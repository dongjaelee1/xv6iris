(* ===================================================================== *)
(* UkShRedirTok.v -- gettoken's '>' ARM, lane SH-REDIR                     *)
(* (design/app-file.md SS5.1, deliverable 1).                              *)
(*                                                                        *)
(* [UkShParseTok.wp_kshp_gtk_disp] walks gettoken's eight-arm switch under *)
(* [ushp_no_symbols], which leaves TWO arms live (the NUL arm and the      *)
(* default) and REFUTES the six symbol arms and the '>' arm.  A redirect   *)
(* line has a '>' in it, so that premise is false for it and the '>' arm   *)
(* has to be WALKED.  This file is that arm and nothing else:              *)
(*                                                                        *)
(*   0x356  lbu   a5,0(s1)      the byte at the cursor -- '>' = 62         *)
(*   0x35a  sext.w s5,a5        ret = *s                                   *)
(*   0x35e  li    a4,60                                                    *)
(*   0x362  bltu  a4,a5,0x3ca   62 > 60: OUT OF LINE                       *)
(*   0x3ca  li    a4,62                                                    *)
(*   0x3ce  bne   a5,a4,0x3e4   it IS '>': fall through                    *)
(*   0x3d2  lbu   a4,1(s1)      THE '>>' LOOKAHEAD                         *)
(*   0x3d6  li    a5,62                                                    *)
(*   0x3da  beq   a4,a5,0x42a   not '>>': fall through                     *)
(*   0x3de  c.addi s1,s1,1      s++                                        *)
(*   0x3e0  c.mv  s5,a5         ret = '>'                                  *)
(*   0x3e2  c.j   0x388         into gettoken's SHARED tail                *)
(*                                                                        *)
(* IT LANDS ON 0x388, which is exactly where                               *)
(* [UkShParseTok.wp_kshp_gtk_disp]'s NUL arm lands, so the tail (the [eq]  *)
(* write, the trailing blank scan, the epilogue) is the same code in both  *)
(* and a whole-gettoken lemma for the redirect shape is this lemma plus    *)
(* that tail.  The '>>' arm (0x42a, [ret = '+']) is REFUTED here from the  *)
(* premise that the byte after the '>' is not another one -- design SS5.1's *)
(* canonical redirect is a single '>' with one blank on each side.          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseLex.
Require Import UkShParseTok.
Require Import UkShRedirLex.
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

Section UkShRedirTok.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).

  Lemma wp_kshp_gtk_disp_gt (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (S k < len)%nat ->
    f k = Z_to_bv 8 62 ->
    f (S k) <> Z_to_bv 8 62 ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    mc !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k) ->
    shp_code γt -∗
    ustr γd dq s0 len f -∗
    urun N h mc (mword_of_int 0x356) (2 + nn) -∗
    (ustr γd dq s0 len f -∗
       ∀ (h' : CpuId) (mc' : regfile),
         ⌜ forall t : mword 5, Regidx t <> Regidx a4_idx ->
             Regidx t <> Regidx a5_idx -> Regidx t <> Regidx s5_idx ->
             Regidx t <> Regidx s1_idx ->
             mc' !!! Regidx t = mc !!! Regidx t ⌝ -∗
         ⌜ mc' !!! Regidx s5_idx = mword_of_int 62 ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat (S k)) ⌝ -∗
         urun N h' mc' (mword_of_int 0x388) (2 + nn) -∗
         mWP (Loop : expr riscv_lang)) -∗
    mWP (Loop : expr riscv_lang).
  Proof using .
    intros Hk Hfk Hfk1 Hs0 Hs64 Hs1.
    iIntros "#Hcode Hstr Hrun Hcont".
    assert (Hbu : bv_unsigned (f k) = 62)
      by (rewrite Hfk; vm_compute; reflexivity).
    (* ---- 0x356  lbu a5,0(s1) ---- *)
    iDestruct (ustr_byte γd dq s0 len f k ltac:(lia) with "Hstr")
      as "[Hb Hcl]".
    iApply (wp_uk_lbu N h mc (mword_of_int 0x356)
              (mword_of_int 0 : mword 12) s1_idx a5_idx dq
              (s0 + Z.of_nat k) (f k) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1 (uint_moi (s0 + Z.of_nat k)
                                  ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb Hrun").
    { iApply (uis_shp_356 with "Hcode"). }
    iIntros "Hb". iDestruct ("Hcl" with "Hb") as "Hstr".
    rewrite (ushp_pc_step 0x356 4). iIntros (h1) "Hrun".
    set (n1 := <[Regidx a5_idx
                 := regval_into_reg (zero_extend' 64 ((f k) : mword 8)
                                     : mword 64)]> mc).
    assert (Hn1 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    n1 !!! Regidx t = mc !!! Regidx t)
      by (intros t Ht; exact (upd_ne mc (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Ha5_1 : n1 !!! Regidx a5_idx = mword_of_int 62).
    { rewrite (upd_eq mc (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 ((f k) : mword 8)
                                   : mword 64))).
      rewrite (zext8_moi (f k)) Hbu. reflexivity. }
    assert (Hs1_1 : n1 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1).
    (* ---- 0x35a  sext.w s5,a5 ---- *)
    iApply (wp_uk_addiw N h1 n1 (mword_of_int 0x35a)
              (mword_of_int 0 : mword 12) a5_idx s5_idx
              (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry;
                    exact (ushp_sextw_byte 62 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shp_35a with "Hcode"). }
    rewrite (ushp_pc_step 0x35a 4). iIntros (h2) "Hrun".
    set (n2 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n1).
    assert (Hn2 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    n2 !!! Regidx t = n1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n1 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Ha5_2 : n2 !!! Regidx a5_idx = mword_of_int 62)
      by (rewrite (Hn2 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_1).
    assert (Hs1_2 : n2 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn2 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_1).
    (* ---- 0x35e  li a4,60 ---- *)
    iApply (wp_uk_li N h2 n2 (mword_of_int 0x35e)
              (mword_of_int 60 : mword 12) a4_idx (mword_of_int 60) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_35e with "Hcode"). }
    rewrite (ushp_pc_step 0x35e 4). iIntros (h3) "Hrun".
    set (n3 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 60 : mword 64)]> n2).
    assert (Hn3 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n3 !!! Regidx t = n2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n2 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_3 : n3 !!! Regidx a4_idx = mword_of_int 60)
      by exact (upd_eq n2 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 60 : mword 64))).
    assert (Ha5_3 : n3 !!! Regidx a5_idx = mword_of_int 62)
      by (rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_2).
    assert (Hs1_3 : n3 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn3 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_2).
    (* ---- 0x362  bltu a4,a5,0x3ca -- TAKEN: 60 < 62 ---- *)
    iApply (wp_uk_btype N h3 n3 (mword_of_int 0x362)
              (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU true
              (mword_of_int 0x3ca) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_3 Ha5_3;
                    rewrite (moi_lt_u 60 62 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_362 with "Hcode"). }
    iIntros (h4) "Hrun".
    (* ---- 0x3ca  li a4,62 ---- *)
    iApply (wp_uk_li N h4 n3 (mword_of_int 0x3ca)
              (mword_of_int 62 : mword 12) a4_idx (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3ca with "Hcode"). }
    rewrite (ushp_pc_step 0x3ca 4). iIntros (h5) "Hrun".
    set (n4 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n3).
    assert (Hn4 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n4 !!! Regidx t = n3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n3 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_4 : n4 !!! Regidx a4_idx = mword_of_int 62)
      by exact (upd_eq n3 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    assert (Ha5_4 : n4 !!! Regidx a5_idx = mword_of_int 62)
      by (rewrite (Hn4 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_3).
    assert (Hs1_4 : n4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn4 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_3).
    (* ---- 0x3ce  bne a5,a4,0x3e4 -- NOT taken: the byte IS '>' ---- *)
    iApply (wp_uk_btype N h5 n4 (mword_of_int 0x3ce)
              (mword_of_int 22 : mword 13) a4_idx a5_idx BNE false
              (mword_of_int 0x3e4) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_4 Ha5_4;
                    rewrite (ushp_moi_neq 62 62 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_3ce with "Hcode"). }
    rewrite (ushp_pc_step 0x3ce 4). iIntros (h6) "Hrun".
    (* ---- 0x3d2  lbu a4,1(s1) -- THE '>>' LOOKAHEAD ---- *)
    iDestruct (ustr_byte γd dq s0 len f (S k) ltac:(lia) with "Hstr")
      as "[Hb1 Hcl1]".
    iApply (wp_uk_lbu N h6 n4 (mword_of_int 0x3d2)
              (mword_of_int 1 : mword 12) s1_idx a4_idx dq
              (s0 + Z.of_nat (S k)) (f (S k)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(rewrite Hs1_4 (uint_moi (s0 + Z.of_nat k)
                                    ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_i12; lia)
              ltac:(vm_compute; discriminate)
              with "[] Hb1 Hrun").
    { iApply (uis_shp_3d2 with "Hcode"). }
    iIntros "Hb1". iDestruct ("Hcl1" with "Hb1") as "Hstr".
    rewrite (ushp_pc_step 0x3d2 4). iIntros (h7) "Hrun".
    set (n5 := <[Regidx a4_idx
                 := regval_into_reg (zero_extend' 64 ((f (S k)) : mword 8)
                                     : mword 64)]> n4).
    assert (Hn5 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n5 !!! Regidx t = n4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n4 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_5 : n5 !!! Regidx a4_idx
                    = mword_of_int (bv_unsigned (f (S k)))).
    { rewrite (upd_eq n4 (Regidx a4_idx)
                 (regval_into_reg (zero_extend' 64 ((f (S k)) : mword 8)
                                   : mword 64))).
      exact (zext8_moi (f (S k))). }
    assert (Hs1_5 : n5 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn5 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_4).
    (* ---- 0x3d6  li a5,62 ---- *)
    iApply (wp_uk_li N h7 n5 (mword_of_int 0x3d6)
              (mword_of_int 62 : mword 12) a5_idx (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3d6 with "Hcode"). }
    rewrite (ushp_pc_step 0x3d6 4). iIntros (h8) "Hrun".
    set (n6 := <[Regidx a5_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n5).
    assert (Hn6 : forall t : mword 5, Regidx t <> Regidx a5_idx ->
                    n6 !!! Regidx t = n5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n5 (Regidx a5_idx) (Regidx t) _ Ht)).
    assert (Ha5_6 : n6 !!! Regidx a5_idx = mword_of_int 62)
      by exact (upd_eq n5 (Regidx a5_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    assert (Ha4_6 : n6 !!! Regidx a4_idx
                    = mword_of_int (bv_unsigned (f (S k))))
      by (rewrite (Hn6 a4_idx ltac:(vm_compute; discriminate)); exact Ha4_5).
    assert (Hs1_6 : n6 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn6 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_5).
    (* ---- 0x3da  beq a4,a5,0x42a -- NOT taken: this is not '>>' ---- *)
    assert (Hne1 : bv_unsigned (f (S k)) <> 62).
    { intro He. apply Hfk1. apply bv_eq. rewrite He.
      vm_compute. reflexivity. }
    pose proof (ushp_byte_rng (f (S k))) as Hrng1.
    iApply (wp_uk_btype N h8 n6 (mword_of_int 0x3da)
              (mword_of_int 80 : mword 13) a5_idx a4_idx BEQ false
              (mword_of_int 0x42a) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_6 Ha5_6;
                    rewrite (moi_eq_vec (bv_unsigned (f (S k))) 62
                               ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    symmetry; apply Z.eqb_neq; exact Hne1)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_3da with "Hcode"). }
    rewrite (ushp_pc_step 0x3da 4). iIntros (h9) "Hrun".
    (* ---- 0x3de  c.addi s1,s1,1 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h9 n6 (mword_of_int 0x3de)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S k))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_6 E1 moi_add;
                    replace (s0 + Z.of_nat (S k)) with (s0 + Z.of_nat k + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3de with "Hcode"). }
    rewrite (ushp_pc_step 0x3de 2). iIntros (hA) "Hrun".
    set (n7 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat (S k))
                                     : mword 64)]> n6).
    assert (Hn7 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    n7 !!! Regidx t = n6 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n6 (Regidx s1_idx) (Regidx t) _ Ht)).
    assert (Hs1_7 : n7 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S k)))
      by exact (upd_eq n6 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (s0 + Z.of_nat (S k))
                                    : mword 64))).
    assert (Ha5_7 : n7 !!! Regidx a5_idx = mword_of_int 62)
      by (rewrite (Hn7 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_6).
    (* ---- 0x3e0  c.mv s5,a5 -- ret = '>' ---- *)
    iApply (wp_uk_cmv N hA n7 (mword_of_int 0x3e0) s5_idx a5_idx
              (mword_of_int 62) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_7; symmetry; exact (ushp_mv_val 62))
              with "[] Hrun").
    { iApply (uis_shp_3e0 with "Hcode"). }
    rewrite (ushp_pc_step 0x3e0 2). iIntros (hB) "Hrun".
    set (n8 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 62 : mword 64)]> n7).
    assert (Hn8 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    n8 !!! Regidx t = n7 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n7 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Hs5_8 : n8 !!! Regidx s5_idx = mword_of_int 62)
      by exact (upd_eq n7 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int 62 : mword 64))).
    assert (Hs1_8 : n8 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S k)))
      by (rewrite (Hn8 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_7).
    (* ---- 0x3e2  c.j 0x388 -- into gettoken's shared tail ---- *)
    iApply (wp_uk_cj N hB n8 (mword_of_int 0x3e2)
              (mword_of_int 2003 : mword 11) (mword_of_int 0x388) (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3e2 with "Hcode"). }
    iIntros (hC) "Hrun".
    iApply ("Hcont" with "Hstr [] [] [] Hrun").
    - iPureIntro. intros t Ht4 Ht5 Hts5 Hts1.
      rewrite (Hn8 t Hts5) (Hn7 t Hts1) (Hn6 t Ht5) (Hn5 t Ht4)
              (Hn4 t Ht4) (Hn3 t Ht4) (Hn2 t Hts5).
      exact (Hn1 t Ht5).
    - iPureIntro. exact Hs5_8.
    - iPureIntro. exact Hs1_8.
  Qed.

End UkShRedirTok.
