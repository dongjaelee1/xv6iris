(* ===================================================================== *)
(* UkShPipeTok.v -- gettoken AT EITHER SYMBOL BYTE, lane SH-PARSE-PIPE    *)
(* (design/app-pipe.md SS5.1, the parser paragraph).                       *)
(*                                                                        *)
(* [UkShRedirGtk.wp_kshp_gettoken_sym] is gettoken at                     *)
(* [UkShParseSym.ushs_gt_ok] -- every symbol byte in the line is a '>'    *)
(* that is neither last nor doubled -- and a pipe line falsifies it        *)
(* ([UkShPipeLex.ushq_demo_not_nosym]'s sibling reason: the byte at the    *)
(* pipe is a '|', not a '>').  This file is gettoken at the WEAKEST        *)
(* premise its switch needs, which covers both lines at once:             *)
(*                                                                        *)
(*   [UkShPipeLex.ushq_sym_ok len f] -- every symbol byte is a '|' or a    *)
(*   '>' with the '>>' lookahead refuted                                  *)
(*                                                                        *)
(* and [UkShPipeLex.ushq_sym_ok_gt] shows the landed premise implies it,   *)
(* so [wp_kshp_gettoken_syms] SUBSUMES the landed walk rather than         *)
(* sitting beside it (the landed statement is not moved -- the bar         *)
(* forbids it -- so the two coexist and a future lane can retire one).     *)
(*                                                                        *)
(* IT IS THREE LEMMAS, and the middle one is the finding.                  *)
(*                                                                        *)
(* (1) [wp_kshp_gtk_disp_bar] -- gettoken's '|' arm, TEN instructions:    *)
(*                                                                        *)
(*       0x356  lbu    a5,0(s1)     the byte at the cursor -- '|' = 124   *)
(*       0x35a  sext.w s5,a5        ret = *s                              *)
(*       0x35e  li     a4,60                                             *)
(*       0x362  bltu   a4,a5,0x3ca  124 > 60: OUT OF LINE                 *)
(*       0x3ca  li     a4,62                                             *)
(*       0x3ce  bne    a5,a4,0x3e4  it is not '>'                         *)
(*       0x3e4  li     a4,124                                            *)
(*       0x3e8  beq    a5,a4,0x386  it IS '|'                             *)
(*       0x386  c.addi s1,s1,1      s++  (the arm '|(){};<' all share)     *)
(*            ->  0x388             gettoken's SHARED tail                *)
(*                                                                        *)
(*     There is NO LOOKAHEAD: sh's [gettoken] has a '>>' case and no      *)
(*     '||' case, so this arm needs neither the byte after the '|' nor     *)
(*     [S k < len] -- where [UkShRedirTok.wp_kshp_gtk_disp_gt] needs       *)
(*     both.  0x386 is the join of the SIX one-byte symbol arms           *)
(*     ('|', '(', ')', ';', '&', '<'), and it falls through into 0x388,    *)
(*     which is where the '>' arm and the NUL arm land too.                *)
(*                                                                        *)
(* (2) [wp_kshp_gtk_disp_sym] -- the two symbol arms UNIFIED.  Both land   *)
(*     on 0x388 with the cursor advanced by exactly one and s5 holding    *)
(*     THE BYTE ITSELF, so one statement covers them with the byte left   *)
(*     as [bv_unsigned (f k)]; the '>>' side condition survives only as    *)
(*     the right disjunct of its premise.  That is what makes (3) the      *)
(*     landed proof with ONE call changed instead of a second copy of      *)
(*     the whole function.                                                *)
(*                                                                        *)
(* (3) [wp_kshp_gettoken_syms] -- gettoken end to end at [ushq_sym_ok],   *)
(*     a THREE-WAY case on the byte at the blank-scanned cursor exactly    *)
(*     as the landed walk is (NUL / symbol / ordinary), with the symbol    *)
(*     arm now (2) rather than the '>'-only walk.  Its answer is the       *)
(*     landed [UkShParseSym.ushs_gettok_res] / [_end] / [_fin], which are  *)
(*     already symbol-GENERIC -- the answer at a symbol is the byte and    *)
(*     the cursor moves by one -- so nothing in the postcondition moved.   *)
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
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShParseTok.
Require Import UkShRedirLex.
Require Import UkShRedirTok.

Require Import UexecSG.
Require Import UkShRedirGtk.
Require Import UkShPipeLex.

Section UkShPipeTok.
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

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).

  (* ---- what the earlier files define, at this file's ghost names ---- *)
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation wp_kshp_fp := (UkShParse.wp_kshp_fp N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).
  Local Notation ushp_cell := (UkShParseTok.ushp_cell N).
  Local Notation wp_kshp_gtk_388 := (UkShParseTok.wp_kshp_gtk_388 N).
  Local Notation wp_kshp_gtk_424 := (UkShParseTok.wp_kshp_gtk_424 N).
  Local Notation wp_kshp_gtk_fin := (UkShParseTok.wp_kshp_gtk_fin N).
  Local Notation wp_kshp_gtk_qst := (UkShParseTok.wp_kshp_gtk_qst N).
  Local Notation wp_kshp_tok_scan := (UkShParseTok.wp_kshp_tok_scan N).
  Local Notation wp_kshp_ws_enter := (UkShParseTok.wp_kshp_ws_enter N).
  Local Notation wp_kshp_gtk_disp_gt := (UkShRedirTok.wp_kshp_gtk_disp_gt N).
  Local Notation wp_kshp_gtk_disp_ns := (UkShRedirGtk.wp_kshp_gtk_disp_ns N).

  (* ===================================================================== *)
  (* (1) gettoken's '|' ARM                                                *)
  (* ===================================================================== *)

  Lemma wp_kshp_gtk_disp_bar (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (k < len)%nat ->
    f k = ushq_bar ->
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
         ⌜ mc' !!! Regidx s5_idx = mword_of_int 124 ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat (S k)) ⌝ -∗
         urun N h' mc' (mword_of_int 0x388) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Hk Hfk Hs0 Hs64 Hs1.
    iIntros "#Hcode Hstr Hrun Hcont".
    assert (Hbu : bv_unsigned (f k) = 124)
      by (rewrite Hfk; exact ushq_bar_val).
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
    assert (Ha5_1 : n1 !!! Regidx a5_idx = mword_of_int 124).
    { rewrite (upd_eq mc (Regidx a5_idx)
                 (regval_into_reg (zero_extend' 64 ((f k) : mword 8)
                                   : mword 64))).
      rewrite (zext8_moi (f k)) Hbu. reflexivity. }
    assert (Hs1_1 : n1 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1).
    (* ---- 0x35a  sext.w s5,a5  --  ret = *s ---- *)
    iApply (wp_uk_addiw N h1 n1 (mword_of_int 0x35a)
              (mword_of_int 0 : mword 12) a5_idx s5_idx
              (mword_of_int 124) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5_1; symmetry;
                    exact (ushp_sextw_byte 124 ltac:(lia)))
              with "[] Hrun").
    { iApply (uis_shp_35a with "Hcode"). }
    rewrite (ushp_pc_step 0x35a 4). iIntros (h2) "Hrun".
    set (n2 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 124 : mword 64)]> n1).
    assert (Hn2 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    n2 !!! Regidx t = n1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n1 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Ha5_2 : n2 !!! Regidx a5_idx = mword_of_int 124)
      by (rewrite (Hn2 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_1).
    assert (Hs1_2 : n2 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn2 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_1).
    assert (Hs5_2 : n2 !!! Regidx s5_idx = mword_of_int 124)
      by exact (upd_eq n1 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int 124 : mword 64))).
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
    assert (Ha5_3 : n3 !!! Regidx a5_idx = mword_of_int 124)
      by (rewrite (Hn3 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_2).
    assert (Hs1_3 : n3 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn3 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_2).
    assert (Hs5_3 : n3 !!! Regidx s5_idx = mword_of_int 124)
      by (rewrite (Hn3 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_2).
    (* ---- 0x362  bltu a4,a5,0x3ca -- TAKEN: 60 < 124 ---- *)
    iApply (wp_uk_btype N h3 n3 (mword_of_int 0x362)
              (mword_of_int 104 : mword 13) a5_idx a4_idx BLTU true
              (mword_of_int 0x3ca) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_3 Ha5_3;
                    rewrite (moi_lt_u 60 124 ltac:(unfold Z64; lia)
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
    assert (Ha5_4 : n4 !!! Regidx a5_idx = mword_of_int 124)
      by (rewrite (Hn4 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_3).
    assert (Hs1_4 : n4 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn4 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_3).
    assert (Hs5_4 : n4 !!! Regidx s5_idx = mword_of_int 124)
      by (rewrite (Hn4 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_3).
    (* ---- 0x3ce  bne a5,a4,0x3e4 -- TAKEN: the byte is not '>' ---- *)
    iApply (wp_uk_btype N h5 n4 (mword_of_int 0x3ce)
              (mword_of_int 22 : mword 13) a4_idx a5_idx BNE true
              (mword_of_int 0x3e4) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_4 Ha5_4;
                    rewrite (ushp_moi_neq 124 62 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3ce with "Hcode"). }
    iIntros (h6) "Hrun".
    (* ---- 0x3e4  li a4,124 ---- *)
    iApply (wp_uk_li N h6 n4 (mword_of_int 0x3e4)
              (mword_of_int 124 : mword 12) a4_idx (mword_of_int 124)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3e4 with "Hcode"). }
    rewrite (ushp_pc_step 0x3e4 4). iIntros (h7) "Hrun".
    set (n5 := <[Regidx a4_idx
                 := regval_into_reg (mword_of_int 124 : mword 64)]> n4).
    assert (Hn5 : forall t : mword 5, Regidx t <> Regidx a4_idx ->
                    n5 !!! Regidx t = n4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n4 (Regidx a4_idx) (Regidx t) _ Ht)).
    assert (Ha4_5 : n5 !!! Regidx a4_idx = mword_of_int 124)
      by exact (upd_eq n4 (Regidx a4_idx)
                  (regval_into_reg (mword_of_int 124 : mword 64))).
    assert (Ha5_5 : n5 !!! Regidx a5_idx = mword_of_int 124)
      by (rewrite (Hn5 a5_idx ltac:(vm_compute; discriminate)); exact Ha5_4).
    assert (Hs1_5 : n5 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat k))
      by (rewrite (Hn5 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_4).
    assert (Hs5_5 : n5 !!! Regidx s5_idx = mword_of_int 124)
      by (rewrite (Hn5 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_4).
    (* ---- 0x3e8  beq a5,a4,0x386 -- TAKEN: it IS '|' ---- *)
    iApply (wp_uk_btype N h7 n5 (mword_of_int 0x3e8)
              (mword_of_int 8094 : mword 13) a4_idx a5_idx BEQ true
              (mword_of_int 0x386) (2 + nn)
              ltac:(cbn [uv_btaken]; rewrite Ha4_5 Ha5_5;
                    rewrite (moi_eq_vec 124 124 ltac:(unfold Z64; lia)
                               ltac:(unfold Z64; lia));
                    reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3e8 with "Hcode"). }
    iIntros (h8) "Hrun".
    (* ---- 0x386  c.addi s1,s1,1  --  s++, and fall into 0x388 ---- *)
    assert (E1 : (sign_extend' 64 (mword_of_int 1 : mword 6) : mword 64)
                 = mword_of_int 1)
      by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_uk_caddi N h8 n5 (mword_of_int 0x386)
              (mword_of_int 1 : mword 6) s1_idx
              (mword_of_int (s0 + Z.of_nat (S k))) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_5 E1 moi_add;
                    replace (s0 + Z.of_nat (S k)) with (s0 + Z.of_nat k + 1)
                      by lia;
                    reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_386 with "Hcode"). }
    rewrite (ushp_pc_step 0x386 2). iIntros (h9) "Hrun".
    set (n6 := <[Regidx s1_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat (S k))
                                     : mword 64)]> n5).
    assert (Hn6 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    n6 !!! Regidx t = n5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne n5 (Regidx s1_idx) (Regidx t) _ Ht)).
    assert (Hs1_6 : n6 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat (S k)))
      by exact (upd_eq n5 (Regidx s1_idx)
                  (regval_into_reg (mword_of_int (s0 + Z.of_nat (S k))
                                    : mword 64))).
    assert (Hs5_6 : n6 !!! Regidx s5_idx = mword_of_int 124)
      by (rewrite (Hn6 s5_idx ltac:(vm_compute; discriminate)); exact Hs5_5).
    iApply ("Hcont" with "Hstr [] [] [] Hrun").
    - iPureIntro. intros t Ht4 Ht5 Hts5 Hts1.
      rewrite (Hn6 t Hts1) (Hn5 t Ht4) (Hn4 t Ht4) (Hn3 t Ht4) (Hn2 t Hts5).
      exact (Hn1 t Ht5).
    - iPureIntro. exact Hs5_6.
    - iPureIntro. exact Hs1_6.
  Qed.


  (* ===================================================================== *)
  (* (2) THE TWO SYMBOL ARMS, UNIFIED                                      *)
  (*                                                                      *)
  (* Both land on 0x388 with s1 advanced by one and s5 = the byte itself,  *)
  (* so the statement leaves the byte as [bv_unsigned (f k)] and the '>>'  *)
  (* lookahead survives only inside the premise's right disjunct.          *)
  (* ===================================================================== *)

  Lemma wp_kshp_gtk_disp_sym (dq : dfrac) (s0 : Z) (len k : nat)
      (f : nat -> bv 8) (nn : nat) (h : CpuId) (mc : regfile) :
    (k < len)%nat ->
    (f k = ushq_bar
     \/ (f k = ushs_gt /\ (S k < len)%nat /\ f (S k) <> ushs_gt)) ->
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
         ⌜ mc' !!! Regidx s5_idx
             = mword_of_int (bv_unsigned (f k)) ⌝ -∗
         ⌜ mc' !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat (S k)) ⌝ -∗
         urun N h' mc' (mword_of_int 0x388) (2 + nn) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Hk Hdisj Hs0 Hs64 Hs1.
    iIntros "#Hcode Hstr Hrun Hcont".
    destruct Hdisj as [ Hbar | (Hgt & Hk1 & Hnd) ].
    - assert (Hbu : bv_unsigned (f k) = 124)
        by (rewrite Hbar; exact ushq_bar_val).
      iApply (wp_kshp_gtk_disp_bar dq s0 len k f nn h mc Hk Hbar Hs0 Hs64 Hs1
                with "Hcode Hstr Hrun").
      iIntros "Hstr" (h' mc') "%Hpres %Hs5 %Hs1' Hrun".
      iApply ("Hcont" with "Hstr [] [] [] Hrun").
      + iPureIntro. exact Hpres.
      + iPureIntro. rewrite Hbu. exact Hs5.
      + iPureIntro. exact Hs1'.
    - assert (Hbu : bv_unsigned (f k) = 62)
        by (rewrite Hgt; exact ushs_gt_val).
      iApply (wp_kshp_gtk_disp_gt dq s0 len k f nn h mc Hk1 Hgt Hnd
                Hs0 Hs64 Hs1 with "Hcode Hstr Hrun").
      iIntros "Hstr" (h' mc') "%Hpres %Hs5 %Hs1' Hrun".
      iApply ("Hcont" with "Hstr [] [] [] Hrun").
      + iPureIntro. exact Hpres.
      + iPureIntro. rewrite Hbu. exact Hs5.
      + iPureIntro. exact Hs1'.
  Qed.


  (* ===================================================================== *)
  (* (3) gettoken, THE WHOLE FUNCTION, AT EITHER SYMBOL                    *)
  (* ===================================================================== *)

  Lemma wp_kshp_gettoken_syms (h : CpuId) (m : regfile) (dq dw dv : dfrac)
      (ps qp eqp s0 : Z) (len off : nat) (f : nat -> bv 8)
      (w0 wq weq : mword 64) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    m !!! Regidx a2_idx = mword_of_int qp ->
    m !!! Regidx a3_idx = mword_of_int eqp ->
    (off <= len)%nat ->
    w0 = mword_of_int (s0 + Z.of_nat off) ->
    ushq_sym_ok len f ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    uword γd ps w0 -∗
    ushp_cell qp wq -∗
    ushp_cell eqp weq -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    urun N h m (mword_of_int ShSyms.gettoken) (8 + (2 + nn)) -∗
    (uword γd ps
       (mword_of_int
          (s0 + Z.of_nat
                  (ushs_gettok_fin len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ushp_cell qp
       (mword_of_int (s0 + Z.of_nat (off + ushp_skipws (len - off) off f))) -∗
     ushp_cell eqp
       (mword_of_int
          (s0 + Z.of_nat
                  (ushs_gettok_end len f
                     (off + ushp_skipws (len - off) off f)))) -∗
     ustr γd dq s0 len f -∗
     ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
     ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       ∀ (h' : CpuId) (m' : regfile),
         ⌜ ucallee_saved m m' ⌝ -∗
         ⌜ m' !!! Regidx a0_idx
             = mword_of_int
                 (ushs_gettok_res len f
                    (off + ushp_skipws (len - off) off f)) ⌝ -∗
         urun N h' m' (ret_pc (m !!! Regidx ra_idx))
           (8 + (2 + nn)) -∗
         WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Ha0 Ha1 Ha2 Ha3 Hoffle Hw0 Hsymok Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode Hcur Hq Heq Hstr Hws Hsy Hrun Hcont".
    rewrite shpp_gettoken.
    iDestruct (urun_stack with "Hrun") as %[Hal8 Hroom].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    assert (Hlo : 64 <= uint sp0) by lia.
    assert (Hr0 : 0 <= uint sp0 < Z64).
    { rewrite uint_unsigned. pose proof (bv_unsigned_in_range 64 sp0) as Hr.
      assert (Em : bv_modulus 64 = Z64) by (vm_compute; reflexivity).
      rewrite Em in Hr. exact Hr. }
    set (kk := (off + ushp_skipws (len - off) off f)%nat).
    assert (Hkk : (kk <= len)%nat).
    { unfold kk. pose proof (ushp_skipws_le (len - off) off f). lia. }
    (* ---- 0x310  c.addi16sp sp,sp,-64 -- THE PUSH ---- *)
    iApply (wp_uk_caddi16sp_dn N h m (mword_of_int 0x310)
              (mword_of_int 60 : mword 6) 8 (2 + nn)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_310 with "Hcode"). }
    rewrite (ushp_pc_step 0x310 2). iIntros "Hstk" (h1) "Hrun".
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 8))).
    assert (Hspu : uint spn = uint sp0 - 64).
    { unfold spn. rewrite !uint_unsigned.
      replace (- (8 * Z.of_nat 8)) with (-64) by lia.
      exact (uv_avi_neg sp0 64 ltac:(lia)
               ltac:(rewrite <- uint_unsigned; lia)). }
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    assert (Hsp1 : m1 !!! Regidx csp_rs1 = spn)
      by exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)).
    assert (Hm1 : forall t : mword 5, Regidx t <> Regidx csp_rs1 ->
                    m1 !!! Regidx t = m !!! Regidx t)
      by (intros t Ht; exact (upd_ne m (Regidx csp_rs1) (Regidx t) _ Ht)).
    set (spl := (mword_of_int (uint sp0 - 64) : mword 64)).
    assert (Hsplu : uint spl = uint sp0 - 64)
      by (unfold spl; apply uint_moi; lia).
    iDestruct (ushp_frame_split sp0 spl 0
                 [(ra_idx, mword_of_int 7 : mword 6);
                  (s0_idx, mword_of_int 6 : mword 6);
                  (s1_idx, mword_of_int 5 : mword 6);
                  (s2_idx, mword_of_int 4 : mword 6);
                  (s3_idx, mword_of_int 3 : mword 6);
                  (s4_idx, mword_of_int 2 : mword 6);
                  (s5_idx, mword_of_int 1 : mword 6);
                  (s6_idx, mword_of_int 0 : mword 6)]
                 ltac:(cbn [length]; lia) with "Hstk") as "[Hsl Hloc]".
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | 5%nat => m !!! Regidx s4_idx
                   | 6%nat => m !!! Regidx s5_idx
                   | _ => m !!! Regidx s6_idx end).
    (* ---- 0x312..0x320  the eight spills ---- *)
    iApply (wp_kshp_spill spn (2 + nn)
              [(ra_idx, mword_of_int 7 : mword 6);
               (s0_idx, mword_of_int 6 : mword 6);
               (s1_idx, mword_of_int 5 : mword 6);
               (s2_idx, mword_of_int 4 : mword 6);
               (s3_idx, mword_of_int 3 : mword 6);
               (s4_idx, mword_of_int 2 : mword 6);
               (s5_idx, mword_of_int 1 : mword 6);
               (s6_idx, mword_of_int 0 : mword 6)]
              (fun i : nat => match i with
                              | 0%nat => 0x312 | 1%nat => 0x314
                              | 2%nat => 0x316 | 3%nat => 0x318
                              | 4%nat => 0x31a | 5%nat => 0x31c
                              | 6%nat => 0x31e | 7%nat => 0x320
                              | _ => 0x322 end)
              (fun i : nat => uint sp0 - 8 * (Z.of_nat i + 1))
              vals h1 m1 Hsp1
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| [| [| i ]]]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ rewrite Hspu; vm_compute uoff_sdsp; lia
                     | split;
                       [ exact (ushp_slot_al (uint sp0) _ Hal8)
                       | unfold vals; cbn;
                         refine (eq_sym (Hm1 _ _));
                         vm_compute; discriminate ] ]))
              with "[] Hsl Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_312 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_314 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_316 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_318 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_31e with "Hcode") | ].
      iSplit; [ iApply (uis_shp_320 with "Hcode") | done ]. }
    iIntros "Hsl" (h2) "Hrun". cbn [length].
    (* ---- 0x322  c.addi4spn s0,sp,64 ---- *)
    iApply (wp_kshp_fp h2 m1 0x322 (mword_of_int 16 : mword 8) (2 + nn)
              with "[] Hrun").
    { iApply (uis_shp_322 with "Hcode"). }
    iIntros (h3 v322) "Hrun".
    set (m2 := <[Regidx s0_idx := regval_into_reg v322]> m1).
    assert (Hm2 : forall t : mword 5, Regidx t <> Regidx s0_idx ->
                    m2 !!! Regidx t = m1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m1 (Regidx s0_idx) (Regidx t) _ Ht)).
    (* ---- 0x324  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv N h3 m2 (mword_of_int 0x324) s4_idx a0_idx
              (mword_of_int ps) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_324 with "Hcode"). }
    rewrite (ushp_pc_step 0x324 2). iIntros (h4) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall t : mword 5, Regidx t <> Regidx s4_idx ->
                    m3 !!! Regidx t = m2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m2 (Regidx s4_idx) (Regidx t) _ Ht)).
    (* ---- 0x326  c.mv s2,a1 ---- *)
    iApply (wp_uk_cmv N h4 m3 (mword_of_int 0x326) s2_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_326 with "Hcode"). }
    rewrite (ushp_pc_step 0x326 2). iIntros (h5) "Hrun".
    set (m4 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                     : mword 64)]> m3).
    assert (Hm4 : forall t : mword 5, Regidx t <> Regidx s2_idx ->
                    m4 !!! Regidx t = m3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m3 (Regidx s2_idx) (Regidx t) _ Ht)).
    (* ---- 0x328  c.mv s5,a2 ---- *)
    iApply (wp_uk_cmv N h5 m4 (mword_of_int 0x328) s5_idx a2_idx
              (mword_of_int qp) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm4 a2_idx ltac:(vm_compute; discriminate))
                      (Hm3 a2_idx ltac:(vm_compute; discriminate))
                      (Hm2 a2_idx ltac:(vm_compute; discriminate))
                      (Hm1 a2_idx ltac:(vm_compute; discriminate)) Ha2;
                    symmetry; exact (ushp_mv_val qp))
              with "[] Hrun").
    { iApply (uis_shp_328 with "Hcode"). }
    rewrite (ushp_pc_step 0x328 2). iIntros (h6) "Hrun".
    set (m5 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int qp : mword 64)]> m4).
    assert (Hm5 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    m5 !!! Regidx t = m4 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m4 (Regidx s5_idx) (Regidx t) _ Ht)).
    (* ---- 0x32a  c.mv s6,a3 ---- *)
    iApply (wp_uk_cmv N h6 m5 (mword_of_int 0x32a) s6_idx a3_idx
              (mword_of_int eqp) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm5 a3_idx ltac:(vm_compute; discriminate))
                      (Hm4 a3_idx ltac:(vm_compute; discriminate))
                      (Hm3 a3_idx ltac:(vm_compute; discriminate))
                      (Hm2 a3_idx ltac:(vm_compute; discriminate))
                      (Hm1 a3_idx ltac:(vm_compute; discriminate)) Ha3;
                    symmetry; exact (ushp_mv_val eqp))
              with "[] Hrun").
    { iApply (uis_shp_32a with "Hcode"). }
    rewrite (ushp_pc_step 0x32a 2). iIntros (h7) "Hrun".
    set (m6 := <[Regidx s6_idx
                 := regval_into_reg (mword_of_int eqp : mword 64)]> m5).
    assert (Hm6 : forall t : mword 5, Regidx t <> Regidx s6_idx ->
                    m6 !!! Regidx t = m5 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m5 (Regidx s6_idx) (Regidx t) _ Ht)).
    assert (Ha0_6 : m6 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm6 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    (* ---- 0x32c  c.ld s1,0(a0) -- the cursor ---- *)
    iApply (wp_uk_cld N h7 m6 (mword_of_int 0x32c)
              (mword_of_int 0 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 1 : mword 3) a0_idx s1_idx ps w0 (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_6 (uint_moi ps ltac:(unfold Z64 in *; lia));
                    vm_compute uoff_c8; lia)
              Hps8 ltac:(vm_compute; discriminate)
              with "[] Hcur Hrun").
    { iApply (uis_shp_32c with "Hcode"). }
    iIntros "Hcur". rewrite (ushp_pc_step 0x32c 2). iIntros (h8) "Hrun".
    set (m7 := <[Regidx s1_idx := regval_into_reg w0]> m6).
    assert (Hm7 : forall t : mword 5, Regidx t <> Regidx s1_idx ->
                    m7 !!! Regidx t = m6 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m6 (Regidx s1_idx) (Regidx t) _ Ht)).
    (* ---- 0x32e  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc N h8 m7 (mword_of_int 0x32e)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x232e)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_32e with "Hcode"). }
    rewrite (ushp_pc_step 0x32e 4). iIntros (h9) "Hrun".
    set (m8 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x232e : mword 64)]> m7).
    assert (Hm8 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m8 !!! Regidx t = m7 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m7 (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x332  addi s3,s3,-806  -- s3 = &whitespace ---- *)
    iApply (wp_uk_addi N h9 m8 (mword_of_int 0x332)
              (mword_of_int 3290 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq m7 (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x232e
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_332 with "Hcode"). }
    rewrite (ushp_pc_step 0x332 4). iIntros (h10) "Hrun".
    set (m9 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> m8).
    assert (Hm9 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    m9 !!! Regidx t = m8 !!! Regidx t)
      by (intros t Ht; exact (upd_ne m8 (Regidx s3_idx) (Regidx t) _ Ht)).
    (* the register file the leading scan starts from *)
    assert (Hs1_9 : m9 !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat off)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s1_idx ltac:(vm_compute; discriminate)).
      rewrite (upd_eq m6 (Regidx s1_idx) (regval_into_reg w0)). exact Hw0. }
    assert (Hs2_9 : m9 !!! Regidx s2_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s2_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s2_idx)
               (regval_into_reg (mword_of_int (s0 + Z.of_nat len)
                                 : mword 64))). }
    assert (Hs3_9 : m9 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq m8 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    assert (Ha1_9 : m9 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm2 a1_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    assert (Hs4_9 : m9 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hm9 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm5 s4_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs5_9 : m9 !!! Regidx s5_idx = mword_of_int qp).
    { rewrite (Hm9 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s5_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm6 s5_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m4 (Regidx s5_idx)
               (regval_into_reg (mword_of_int qp : mword 64))). }
    assert (Hs6_9 : m9 !!! Regidx s6_idx = mword_of_int eqp).
    { rewrite (Hm9 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm8 s6_idx ltac:(vm_compute; discriminate)).
      rewrite (Hm7 s6_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m5 (Regidx s6_idx)
               (regval_into_reg (mword_of_int eqp : mword 64))). }
    assert (Hsp9 : m9 !!! Regidx csp_rs1 = spn).
    { rewrite (Hm9 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm8 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm7 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm6 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm5 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm4 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm3 csp_rs1 ltac:(vm_compute; discriminate)).
      rewrite (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact Hsp1. }
    assert (Hkeep9 : forall t : mword 5,
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              m9 !!! Regidx t = m !!! Regidx t).
    { intros t H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (Hm9 t H19) (Hm8 t H19) (Hm7 t H9) (Hm6 t H22) (Hm5 t H21)
              (Hm4 t H18) (Hm3 t H20) (Hm2 t H8). exact (Hm1 t H2). }
    (* ---- 0x336..0x34c  the LEADING whitespace scan ---- *)
    iApply (wp_kshp_ws_enter 0x336 a1_idx (mword_of_int 1858 : mword 21)
              dq dw s0 len off f nn h10 m9
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              Hoffle Hs0 Hs64 Hs1_9 Hs2_9 Hs3_9 Ha1_9
              with "[] [] [] [] [] [] [] [] Hcode Hstr Hws Hrun").
    { iApply (uis_shp_336 with "Hcode"). }
    { iApply (uis_shp_33a with "Hcode"). }
    { iApply (uis_shp_33e with "Hcode"). }
    { iApply (uis_shp_340 with "Hcode"). }
    { iApply (uis_shp_344 with "Hcode"). }
    { iApply (uis_shp_346 with "Hcode"). }
    { iApply (uis_shp_348 with "Hcode"). }
    { iApply (uis_shp_34c with "Hcode"). }
    iIntros "Hstr Hws" (h11 mA) "%HpresA %Hs1A Hrun".
    assert (Hkkd : (off + ushp_skipws (len - off) off f)%nat = kk)
      by reflexivity.
    rewrite Hkkd in Hs1A.
    assert (Hs2_A : mA !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresA s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs2_9).
    assert (Hs4_A : mA !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresA s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs4_9).
    assert (Hs5_A : mA !!! Regidx s5_idx = mword_of_int qp)
      by (rewrite (HpresA s5_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs5_9).
    assert (Hs6_A : mA !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresA s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hs6_9).
    assert (Hsp_A : mA !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresA csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)); exact Hsp9).
    (* ---- 0x34e..0x352  [if(q) *q = s] ---- *)
    iApply (wp_kshp_gtk_qst s0 qp kk wq nn h11 mA Hs0
              ltac:(unfold Z64 in *; lia) Hs1A Hs5_A with "Hcode Hq Hrun").
    iIntros "Hq" (h12) "Hrun".
    (* ---- 0x356..0x386 (and 0x3ca..0x3e8)  THE SWITCH ---- *)
    (* THREE ARMS, and the byte at the blank-scanned cursor decides which.
       The SYMBOL arm is [wp_kshp_gtk_disp_sym] -- the '|' walk and lane
       SH-REDIR's '>' walk under one statement, because both land on 0x388
       with the cursor advanced by one and s5 holding the byte -- and is
       taken OUT OF LINE first; the other two are the landed dichotomy,
       driven through [UkShRedirGtk.wp_kshp_gtk_disp_ns] -- the same walk as
       [UkShParseTok.wp_kshp_gtk_disp] at the premise it actually uses. *)
    destruct (andb (bool_decide (kk < len)%nat) (ushp_is_sym (f kk)))
      eqn:Egt.
    { (* ---- THE SYMBOL ARM, either byte ---- *)
      apply andb_true_iff in Egt as [ Ekkb Esym ].
      apply bool_decide_eq_true in Ekkb.
      pose proof (Hsymok kk Ekkb Esym) as Hdisj.
      assert (Hres : ushs_gettok_res len f kk = bv_unsigned (f kk)).
      { unfold ushs_gettok_res.
        rewrite (bool_decide_eq_true_2 _ Ekkb) Esym. reflexivity. }
      assert (Hend : ushs_gettok_end len f kk = S kk).
      { unfold ushs_gettok_end.
        rewrite (bool_decide_eq_true_2 _ Ekkb) Esym. reflexivity. }
      assert (Hfin : ushs_gettok_fin len f kk
                     = (S kk + ushp_skipws (len - S kk) (S kk) f)%nat)
        by (unfold ushs_gettok_fin; rewrite Hend; reflexivity).
      iApply (wp_kshp_gtk_disp_sym dq s0 len kk f nn h12 mA
                Ekkb Hdisj Hs0 Hs64 Hs1A with "Hcode Hstr Hrun").
      iIntros "Hstr" (h13 mG) "%HpresG %Hs5G %Hs1G Hrun".
      assert (Hs2_G : mG !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
        by (rewrite (HpresG s2_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs2_A).
      assert (Hs4_G : mG !!! Regidx s4_idx = mword_of_int ps)
        by (rewrite (HpresG s4_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs4_A).
      assert (Hs6_G : mG !!! Regidx s6_idx = mword_of_int eqp)
        by (rewrite (HpresG s6_idx ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hs6_A).
      assert (Hsp_G : mG !!! Regidx csp_rs1 = spn)
        by (rewrite (HpresG csp_rs1 ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)
                       ltac:(vm_compute; discriminate)); exact Hsp_A).
      assert (HkeepG : forall t : mword 5, ucallee_saved_idx t = true ->
                Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
                Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
                Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
                Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
                mG !!! Regidx t = m !!! Regidx t).
      { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
        rewrite (HpresG t (ushp_cs_ne t a4_idx Ht
                             ltac:(vm_compute; reflexivity))
                   (ushp_cs_ne t a5_idx Ht ltac:(vm_compute; reflexivity))
                   H21 H9).
        rewrite (HpresA t Ht H9).
        exact (Hkeep9 t H2 H8 H9 H18 H19 H20 H21 H22). }
      (* ---- 0x388: [if(eq) *eq = s], then the trailing blank scan ---- *)
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len (S kk) f weq nn h13 mG
                ltac:(lia) Hs0 Hs64 Hs1G Hs2_G Hs6_G
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h14 mC) "%HpresC %Hs1C Hrun".
      iApply (wp_kshp_gtk_fin m sp0 spl vals ps (bv_unsigned (f kk))
                (s0 + Z.of_nat (S kk + ushp_skipws (len - S kk) (S kk) f))
                w0 nn
                h14 mC Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
                eq_refl eq_refl
                ltac:(rewrite (HpresC csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hsp_G)
                ltac:(rewrite (HpresC s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4_G)
                Hs1C
                ltac:(rewrite (HpresC s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs5G)
                ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                      rewrite (HpresC t Ht H9 H19);
                      exact (HkeepG t Ht H2 H8 H9 H18 H19 H20 H21 H22))
                with "Hcode Hcur Hsl Hloc Hrun").
      iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
      rewrite Hfin Hend Hres.
      iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
      - iPureIntro. exact Hcs.
      - iPureIntro. exact Hafin. }
    (* ---- the byte at the cursor is NOT a symbol: the landed dichotomy -- *)
    assert (Hnsk : (kk < len)%nat -> ushp_is_sym (f kk) = false).
    { intro Hk. rewrite (bool_decide_eq_true_2 _ Hk) in Egt.
      cbn [andb] in Egt. exact Egt. }
    iApply (wp_kshp_gtk_disp_ns dq s0 len kk f nn h12 mA
              Hkk Hnsk Hs0 Hs64 Hs1A with "Hcode Hstr Hrun").
    iIntros "Hstr" (h13 mB) "%HpresB %Hs5B Hrun".
    assert (Hs1_B : mB !!! Regidx s1_idx = mword_of_int (s0 + Z.of_nat kk))
      by (rewrite (HpresB s1_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs1A).
    assert (Hs2_B : mB !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresB s2_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs2_A).
    assert (Hs4_B : mB !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresB s4_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs4_A).
    assert (Hs6_B : mB !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresB s6_idx ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs6_A).
    assert (Hsp_B : mB !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresB csp_rs1 ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp_A).
    assert (HkeepB : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              mB !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (HpresB t (ushp_cs_ne t a4_idx Ht
                           ltac:(vm_compute; reflexivity))
                 (ushp_cs_ne t a5_idx Ht ltac:(vm_compute; reflexivity))
                 H21).
      rewrite (HpresA t Ht H9).
      exact (Hkeep9 t H2 H8 H9 H18 H19 H20 H21 H22). }
    destruct (lt_dec kk len) as [ Hklt | Hkge ].
    2: { (* THE NUL ARM: the cursor is at [es] and gettoken returns 0 ---- *)
      rewrite (bool_decide_eq_false_2 (kk < len)%nat Hkge).
      assert (Hkeq : kk = len) by lia.
      assert (Hend : ushs_gettok_end len f kk = len).
      { unfold ushs_gettok_end.
        rewrite (bool_decide_eq_false_2 (kk < len)%nat Hkge). exact Hkeq. }
      assert (Hfin : ushs_gettok_fin len f kk = len).
      { unfold ushs_gettok_fin. rewrite Hend.
        assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
        rewrite (ushp_skipws_zero len f). lia. }
      assert (Hres : ushs_gettok_res len f kk = 0).
      { unfold ushs_gettok_res.
        rewrite (bool_decide_eq_false_2 (kk < len)%nat Hkge). reflexivity. }
      rewrite Hkeq in Hs1_B.
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len len f weq nn h13 mB
                ltac:(lia) Hs0 Hs64 Hs1_B Hs2_B Hs6_B
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h14 mC) "%HpresC %Hs1C Hrun".
      assert (Hz : (len - len)%nat = 0%nat) by lia.
      rewrite Hz (ushp_skipws_zero len f) in Hs1C.
      assert (Hlen0 : (len + 0)%nat = len) by lia.
      rewrite Hlen0 in Hs1C.
      iApply (wp_kshp_gtk_fin m sp0 spl vals ps 0 (s0 + Z.of_nat len) w0 nn
                h14 mC Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
                eq_refl eq_refl
                ltac:(rewrite (HpresC csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hsp_B)
                ltac:(rewrite (HpresC s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4_B)
                Hs1C
                ltac:(rewrite (HpresC s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact (Hs5B ltac:(lia)))
                ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                      rewrite (HpresC t Ht H9 H19);
                      exact (HkeepB t Ht H2 H8 H9 H18 H19 H20 H21 H22))
                with "Hcode Hcur Hsl Hloc Hrun").
      iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
      rewrite <- Hkkd. rewrite Hkkd.
      rewrite Hfin Hend Hres.
      iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
      - iPureIntro. exact Hcs.
      - iPureIntro. exact Hafin. }
    (* THE DEFAULT ARM: an ordinary token ---- *)
    rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt).
    assert (Hres : ushs_gettok_res len f kk = 97).
    { unfold ushs_gettok_res.
      rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt) (Hnsk Hklt).
      reflexivity. }
    assert (Hendd : ushs_gettok_end len f kk
                    = (kk + ushp_toklen (len - kk) kk f)%nat).
    { unfold ushs_gettok_end.
      rewrite (bool_decide_eq_true_2 (kk < len)%nat Hklt) (Hnsk Hklt).
      reflexivity. }
    (* ---- 0x3ec  auipc s3,0x2 ---- *)
    iApply (wp_uk_auipc N h13 mB (mword_of_int 0x3ec)
              (mword_of_int 2 : mword 20) s3_idx (mword_of_int 0x23ec)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3ec with "Hcode"). }
    rewrite (ushp_pc_step 0x3ec 4). iIntros (h14) "Hrun".
    set (d1 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int 0x23ec : mword 64)]> mB).
    assert (Hd1 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    d1 !!! Regidx t = mB !!! Regidx t)
      by (intros t Ht; exact (upd_ne mB (Regidx s3_idx) (Regidx t) _ Ht)).
    (* ---- 0x3f0  addi s3,s3,-996 ---- *)
    iApply (wp_uk_addi N h14 d1 (mword_of_int 0x3f0)
              (mword_of_int 3100 : mword 12) s3_idx s3_idx
              (mword_of_int ushp_whitespace) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq mB (Regidx s3_idx)
                               (regval_into_reg (mword_of_int 0x23ec
                                                 : mword 64)));
                    unfold ushp_whitespace;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f0 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f0 4). iIntros (h15) "Hrun".
    set (d2 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int ushp_whitespace
                                     : mword 64)]> d1).
    assert (Hd2 : forall t : mword 5, Regidx t <> Regidx s3_idx ->
                    d2 !!! Regidx t = d1 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d1 (Regidx s3_idx) (Regidx t) _ Ht)).
    assert (Hs3_d2 : d2 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by exact (upd_eq d1 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int ushp_whitespace : mword 64))).
    (* ---- 0x3f4  auipc s5,0x2 ---- *)
    iApply (wp_uk_auipc N h15 d2 (mword_of_int 0x3f4)
              (mword_of_int 2 : mword 20) s5_idx (mword_of_int 0x23f4)
              (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f4 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f4 4). iIntros (h16) "Hrun".
    set (d3 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int 0x23f4 : mword 64)]> d2).
    assert (Hd3 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    d3 !!! Regidx t = d2 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d2 (Regidx s5_idx) (Regidx t) _ Ht)).
    (* ---- 0x3f8  addi s5,s5,-1012  -- s5 = &symbols ---- *)
    iApply (wp_uk_addi N h16 d3 (mword_of_int 0x3f8)
              (mword_of_int 3084 : mword 12) s5_idx s5_idx
              (mword_of_int ushp_symbols) (2 + nn)
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (upd_eq d2 (Regidx s5_idx)
                               (regval_into_reg (mword_of_int 0x23f4
                                                 : mword 64)));
                    unfold ushp_symbols;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_3f8 with "Hcode"). }
    rewrite (ushp_pc_step 0x3f8 4). iIntros (h17) "Hrun".
    set (d4 := <[Regidx s5_idx
                 := regval_into_reg (mword_of_int ushp_symbols
                                     : mword 64)]> d3).
    assert (Hd4 : forall t : mword 5, Regidx t <> Regidx s5_idx ->
                    d4 !!! Regidx t = d3 !!! Regidx t)
      by (intros t Ht; exact (upd_ne d3 (Regidx s5_idx) (Regidx t) _ Ht)).
    assert (Hs5_d4 : d4 !!! Regidx s5_idx = mword_of_int ushp_symbols)
      by exact (upd_eq d3 (Regidx s5_idx)
                  (regval_into_reg (mword_of_int ushp_symbols : mword 64))).
    assert (Hs1_d4 : d4 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat kk))
      by (rewrite (Hd4 s1_idx ltac:(vm_compute; discriminate))
                  (Hd3 s1_idx ltac:(vm_compute; discriminate))
                  (Hd2 s1_idx ltac:(vm_compute; discriminate))
                  (Hd1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_B).
    assert (Hs2_d4 : d4 !!! Regidx s2_idx
                     = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (Hd4 s2_idx ltac:(vm_compute; discriminate))
                  (Hd3 s2_idx ltac:(vm_compute; discriminate))
                  (Hd2 s2_idx ltac:(vm_compute; discriminate))
                  (Hd1 s2_idx ltac:(vm_compute; discriminate)); exact Hs2_B).
    assert (Hs3_d4 : d4 !!! Regidx s3_idx = mword_of_int ushp_whitespace)
      by (rewrite (Hd4 s3_idx ltac:(vm_compute; discriminate))
                  (Hd3 s3_idx ltac:(vm_compute; discriminate)); exact Hs3_d2).
    assert (Hs4_d4 : d4 !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (Hd4 s4_idx ltac:(vm_compute; discriminate))
                  (Hd3 s4_idx ltac:(vm_compute; discriminate))
                  (Hd2 s4_idx ltac:(vm_compute; discriminate))
                  (Hd1 s4_idx ltac:(vm_compute; discriminate)); exact Hs4_B).
    assert (Hs6_d4 : d4 !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (Hd4 s6_idx ltac:(vm_compute; discriminate))
                  (Hd3 s6_idx ltac:(vm_compute; discriminate))
                  (Hd2 s6_idx ltac:(vm_compute; discriminate))
                  (Hd1 s6_idx ltac:(vm_compute; discriminate)); exact Hs6_B).
    assert (Hsp_d4 : d4 !!! Regidx csp_rs1 = spn)
      by (rewrite (Hd4 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd3 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd2 csp_rs1 ltac:(vm_compute; discriminate))
                  (Hd1 csp_rs1 ltac:(vm_compute; discriminate)); exact Hsp_B).
    assert (Hkeep_d4 : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              d4 !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (Hd4 t H21) (Hd3 t H21) (Hd2 t H19) (Hd1 t H19).
      exact (HkeepB t Ht H2 H8 H9 H18 H19 H20 H21 H22). }
    (* ---- 0x3fc  bgeu s1,s2,0x43e -- refuted: the cursor is inside ---- *)
    assert (Htk : false = uv_btaken BGEU (d4 !!! Regidx s1_idx)
                            (d4 !!! Regidx s2_idx)).
    { cbn [uv_btaken]. rewrite Hs1_d4 Hs2_d4.
      rewrite (moi_ge_u (s0 + Z.of_nat kk) (s0 + Z.of_nat len)
                 ltac:(unfold Z64 in *; lia) ltac:(unfold Z64 in *; lia)).
      symmetry. rewrite Z.geb_leb. apply Z.leb_gt. lia. }
    iApply (wp_uk_btype N h17 d4 (mword_of_int 0x3fc)
              (mword_of_int 66 : mword 13) s2_idx s1_idx BGEU false
              (mword_of_int 0x43e) (2 + nn)
              Htk
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shp_3fc with "Hcode"). }
    rewrite (ushp_pc_step 0x3fc 4). iIntros (h18) "Hrun".
    (* ---- 0x400..0x41a  THE TOKEN-BODY SCAN ---- *)
    iApply (wp_kshp_tok_scan dq dw dv s0 len f nn (len - kk)%nat kk h18 d4
              eq_refl Hklt Hs0 Hs64 Hs1_d4 Hs2_d4 Hs3_d4 Hs5_d4
              with "Hcode Hstr Hws Hsy Hrun").
    iIntros "Hstr Hws Hsy" (h19 mE) "%HpresE %Hs1E %Hs5E Hrun".
    set (ee := ushs_gettok_end len f kk).
    assert (Heed : (kk + ushp_toklen (len - kk) kk f)%nat = ee)
      by (unfold ee; rewrite Hendd; reflexivity).
    rewrite Heed in Hs1E.
    assert (Heele : (ee <= len)%nat).
    { rewrite <- Heed. pose proof (ushp_toklen_le (len - kk) kk f). lia. }
    assert (Hexit : ushp_tok_exit len f kk
                    = if bool_decide (ee < len)%nat then 0x388 else 0x424)
      by (unfold ushp_tok_exit; rewrite Heed; reflexivity).
    rewrite Hexit.
    assert (Hs2_E : mE !!! Regidx s2_idx = mword_of_int (s0 + Z.of_nat len))
      by (rewrite (HpresE s2_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs2_d4).
    assert (Hs4_E : mE !!! Regidx s4_idx = mword_of_int ps)
      by (rewrite (HpresE s4_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs4_d4).
    assert (Hs6_E : mE !!! Regidx s6_idx = mword_of_int eqp)
      by (rewrite (HpresE s6_idx ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hs6_d4).
    assert (Hsp_E : mE !!! Regidx csp_rs1 = spn)
      by (rewrite (HpresE csp_rs1 ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; discriminate)
                     ltac:(vm_compute; discriminate)); exact Hsp_d4).
    assert (Hkeep_E : forall t : mword 5, ucallee_saved_idx t = true ->
              Regidx t <> Regidx csp_rs1 -> Regidx t <> Regidx s0_idx ->
              Regidx t <> Regidx s1_idx -> Regidx t <> Regidx s2_idx ->
              Regidx t <> Regidx s3_idx -> Regidx t <> Regidx s4_idx ->
              Regidx t <> Regidx s5_idx -> Regidx t <> Regidx s6_idx ->
              mE !!! Regidx t = m !!! Regidx t).
    { intros t Ht H2 H8 H9 H18 H19 H20 H21 H22.
      rewrite (HpresE t Ht H9 H21).
      exact (Hkeep_d4 t Ht H2 H8 H9 H18 H19 H20 H21 H22). }
    destruct (bool_decide (ee < len)%nat) eqn:Eee.
    { (* the token was ended by a byte: 0x388, then the trailing scan *)
      apply bool_decide_eq_true in Eee.
      iApply (wp_kshp_gtk_388 dq dw s0 eqp len ee f weq nn h19 mE
                ltac:(lia) Hs0 Hs64 Hs1E Hs2_E Hs6_E
                with "Hcode Heq Hstr Hws Hrun").
      iIntros "Heq Hstr Hws" (h20 mF) "%HpresF %Hs1F Hrun".
      assert (Hfin : ushs_gettok_fin len f kk
                     = (ee + ushp_skipws (len - ee) ee f)%nat)
        by (unfold ushs_gettok_fin; rewrite Hendd Heed; reflexivity).
      iApply (wp_kshp_gtk_fin m sp0 spl vals ps 97
                (s0 + Z.of_nat (ee + ushp_skipws (len - ee) ee f)) w0 nn
                h20 mF Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
                eq_refl eq_refl
                ltac:(rewrite (HpresF csp_rs1 ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hsp_E)
                ltac:(rewrite (HpresF s4_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs4_E)
                Hs1F
                ltac:(rewrite (HpresF s5_idx ltac:(vm_compute; reflexivity)
                                 ltac:(vm_compute; discriminate)
                                 ltac:(vm_compute; discriminate));
                      exact Hs5E)
                ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                      rewrite (HpresF t Ht H9 H19);
                      exact (Hkeep_E t Ht H2 H8 H9 H18 H19 H20 H21 H22))
                with "Hcode Hcur Hsl Hloc Hrun").
      iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
      rewrite Hfin Hres.
      iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
      - iPureIntro. exact Hcs.
      - iPureIntro. exact Hafin. }
    (* the token ran to [es]: 0x424, and the trailing scan is empty *)
    apply bool_decide_eq_false in Eee.
    assert (Heeq : ee = len) by lia.
    rewrite Heeq in Hs1E.
    assert (Hfin : ushs_gettok_fin len f kk = len).
    { assert (H1 : ushs_gettok_fin len f kk
                   = (ee + ushp_skipws (len - ee) ee f)%nat)
        by (unfold ushs_gettok_fin; rewrite Hendd Heed; reflexivity).
      rewrite H1 Heeq.
      assert (Hz : (len - len)%nat = 0%nat) by lia. rewrite Hz.
      rewrite (ushp_skipws_zero len f). lia. }
    iApply (wp_kshp_gtk_424 dq dw s0 eqp len f weq nn h19 mE
              Hs0 Hs64 Hs1E Hs2_E Hs6_E with "Hcode Heq Hstr Hws Hrun").
    iIntros "Heq Hstr Hws" (h20 mF) "%HpresF %Hs1F Hrun".
    iApply (wp_kshp_gtk_fin m sp0 spl vals ps 97 (s0 + Z.of_nat len) w0 nn
              h20 mF Hal8 Hlo ltac:(lia) Hsplu Hps0 Hps8 Hpssz
              eq_refl eq_refl
              ltac:(rewrite (HpresF csp_rs1 ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hsp_E)
              ltac:(rewrite (HpresF s4_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs4_E)
              Hs1F
              ltac:(rewrite (HpresF s5_idx ltac:(vm_compute; reflexivity)
                               ltac:(vm_compute; discriminate)
                               ltac:(vm_compute; discriminate));
                    exact Hs5E)
              ltac:(intros t Ht H2 H8 H9 H18 H19 H20 H21 H22;
                    rewrite (HpresF t Ht H9 H19);
                    exact (Hkeep_E t Ht H2 H8 H9 H18 H19 H20 H21 H22))
              with "Hcode Hcur Hsl Hloc Hrun").
    iIntros "Hcur" (hf mf) "%Hcs %Hafin Hrun".
    rewrite Hfin Hres Heeq.
    iApply ("Hcont" with "Hcur Hq Heq Hstr Hws Hsy [] [] Hrun").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Hafin.
  Qed.


End UkShPipeTok.
