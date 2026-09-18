(* ===================================================================== *)
(* UkShPipeRound.v -- THE CHILD WALK AT THE PIPE SHAPE, lane              *)
(* SH-PIPE-ROUND item A (design/app-pipe.md SS5.1).                        *)
(*                                                                        *)
(* [UkShRedirSeam.wp_kshm_child_redir] is the mould, one line shape over:  *)
(* sh's forked child enters at 0x9c0 with the line in s1, calls            *)
(* [parsecmd] and then [runcmd].  What differs is which parser theorem     *)
(* and which [runcmd] arm run:                                            *)
(*                                                                        *)
(*   0x9c0  c.mv a0,s1        the line                                     *)
(*   0x9c2  jal  ra,parsecmd  -> [UkShPipeCm.wp_kshp_parsecmd_bar]:        *)
(*                              the PIPE node over two EXEC nodes          *)
(*   0x9c6  jal  ra,runcmd    -> [UkShPipe.wp_kshr_pipe_arm]:              *)
(*                              pipe(2), two fork1s, six closes, two waits *)
(*                                                                        *)
(* and between them the seam [UkShPipeSeam.ush_cmd_of_ushp_pipe], whose    *)
(* two [ushq_cut_ok] premises are SS1 of this file.                         *)
(*                                                                        *)
(* WHY THE PARSER THEOREM IS NOT THE ONE USED.  [UkShPipeCm.                *)
(* wp_kshp_parser_pipe] closes the three nodes into one [ushp_tree] with   *)
(* [UkShPipeParse.ushp_pipe_close]; the SEAM wants them SEPARATE (it       *)
(* reads the node's own three fields and converts each subtree with        *)
(* [UkShMain.ush_cmd_of_ushp_gen]).  So this walk goes through             *)
(* [wp_kshp_parsecmd_bar], the theorem one step below it, exactly as the   *)
(* redirect seam goes through [UkShRedirPc.wp_kshp_parsecmd_gt].           *)
(*                                                                        *)
(* WHAT THE ARM FORCES ON THE WALK, and it is a finding for the round:     *)
(* [wp_kshr_pipe_arm] takes the exit payload FREE ([(⊢ ukn_pay N (-1))],   *)
(* a Prop), where [UkShRedir.wp_kshr_redir_arm_at] takes the pair          *)
(* [□ (Cr -∗ ukn_pay N (-1))] / [Cr].  A resource the caller brings can    *)
(* still travel -- through the arm's own SPLIT wand, into exactly one of   *)
(* [RcL]/[RcR]/[Rk] -- and that is what [Cr] does here; but the free       *)
(* payload itself is a real premise of the arm and this walk inherits it.  *)
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
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm.
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import PipeNames.
Require Import UserCwd.
Require Import UserChildren.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseCmd.
Require Import UkShLoop.
Require Import UkShMain.
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShRedirSeam.   (* [ushs_toks_below] -- the truncation *)
Require Import UkShPipe.        (* the runcmd arm *)
Require Import UkShPipeLex.
Require Import UkShPipeParse.
Require Import UkShPipeSeam.
Require Import UkShPipeCm.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UexecSG.
Require Import UexecRet.
Local Open Scope Z_scope.
Import Defs.

Section UkShPipeRound.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).

  (* the three allocator links a pipe line's parse spends (design SS5.1 as
     landed: two [execcmd]s and one [pipecmd]); UM1 -> UM2 is a section
     hypothesis of [UkShPipeCm] and therefore one here too *)
  Context (UM0 UM1 UM2 UM3 : iProp Σ).
  Hypothesis ushq_malloc_ok12 : ushp_malloc_ty UM1 UM2.

  (* ===================================================================== *)
  (* §1 THE CUT, AND THE SEAM'S TWO PREMISES.                               *)
  (*                                                                        *)
  (* [nulterminate]'s PIPE row zeroes the end index of every argument       *)
  (* token of the LEFT command and then the end index of the right          *)
  (* command's single word, on ONE buffer -- which is exactly the redirect  *)
  (* cut [UkShRedirPc.ushs_nulcut args len f ge] (the outer fold over a     *)
  (* one-element list IS [ushp_setb]).  So the two shapes share one         *)
  (* definition and only the INDEX BOUNDS differ.                           *)
  (* ===================================================================== *)

  Definition ushq_cut (args : list (nat * nat)) (len : nat)
      (f : nat -> bv 8) (ge : nat) : nat -> bv 8 :=
    UkShParseCmd.ushp_nulfold [(0%nat, ge)]
      (UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f)).

  (* what [wp_kshp_parsecmd_bar] hands back IS this cut *)
  Lemma ushq_cut_eq (args : list (nat * nat)) (len : nat) (f : nat -> bv 8)
      (gp ge : nat) :
    UkShParseCmd.ushp_nulfold [(S (S gp), ge)]
      (UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f))
    = ushq_cut args len f ge.
  Proof using . reflexivity. Qed.

  Lemma ushq_cut_off (args : list (nat * nat)) (len : nat) (f : nat -> bv 8)
      (ge j : nat) :
    j <> ge ->
    ushq_cut args len f ge j
    = UkShParseCmd.ushp_nulfold args (UkShParseCmd.ushp_ext len f) j.
  Proof using .
    intro Hj. rewrite /ushq_cut. cbn [UkShParseCmd.ushp_nulfold snd].
    rewrite /UkShParseCmd.ushp_setb.
    rewrite (proj2 (Nat.eqb_neq j ge) Hj). reflexivity.
  Qed.

  (* the LEFT command's tokens, read on the line TRUNCATED at the '|' --
     [UkShRedirSeam]'s route, at the pipe shape's own symbol fact *)
  Lemma ushq_args_below (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (args : list (nat * nat)) :
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
      (fst tk < snd tk)%nat /\ (snd tk <= gp)%nat.
  Proof using .
    intros Hpq Htoks i tk Hi.
    assert (Hgl : (gp < len)%nat) by exact (ushq_pipe_lt len f gp ge Hpq).
    destruct (ushp_tokens_in gp f 0%nat args
                (UkShRedirSeam.ushs_toks_below len gp f 0%nat args
                   ltac:(lia) ltac:(lia) Htoks) ltac:(lia) i tk Hi)
      as [ Hlo Hhi ].
    split; lia.
  Qed.

  Lemma ushq_args_gap (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (args : list (nat * nat)) :
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    forall (i : nat) (tk : nat * nat), args !! i = Some tk ->
    forall (q : nat) (t : nat * nat), args !! q = Some t ->
    forall x : nat, (fst tk <= x < snd tk)%nat -> x <> snd t.
  Proof using .
    intros Hpq Htoks.
    assert (Hgl : (gp < len)%nat) by exact (ushq_pipe_lt len f gp ge Hpq).
    exact (UkShMain.ushp_tokens_gap gp f 0%nat args
             (ushq_pipe_nosym_below len f gp ge Hpq)
             (UkShRedirSeam.ushs_toks_below len gp f 0%nat args
                ltac:(lia) ltac:(lia) Htoks)
             ltac:(lia)).
  Qed.

  (* SEAM PREMISE 1: the LEFT command's token list, at the cut *)
  Lemma ushq_cut_ok_left (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (args : list (nat * nat)) :
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    UkShPipeSeam.ushq_cut_ok len (ushq_cut args len f ge) args.
  Proof using .
    intros Hpq Htoks Hnn.
    pose proof Hpq as HQ.
    destruct HQ as (Hone & Hgp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
    assert (Hgl : (gp < len)%nat) by exact (ushq_pipe_lt len f gp ge Hpq).
    split_and!.
    - intros i tk Hi.
      destruct (ushq_args_below len f gp ge args Hpq Htoks i tk Hi) as [H1 H2].
      split; lia.
    - intros i tk Hi.
      destruct (ushq_args_below len f gp ge args Hpq Htoks i tk Hi) as [H1 H2].
      rewrite (ushq_cut_off args len f ge (snd tk) ltac:(lia)).
      exact (UkShParseCmd.ushp_nulfold_hit args
               (UkShParseCmd.ushp_ext len f) i tk Hi).
    - intros i tk Hi j Hj.
      destruct (ushq_args_below len f gp ge args Hpq Htoks i tk Hi) as [H1 H2].
      rewrite (ushq_cut_off args len f ge (fst tk + j)%nat ltac:(lia)).
      rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
                 (fst tk + j)%nat
                 ltac:(intros q t Hq;
                       exact (ushq_args_gap len f gp ge args Hpq Htoks
                                i tk Hi q t Hq (fst tk + j)%nat ltac:(lia)))).
      rewrite /UkShParseCmd.ushp_ext
        (bool_decide_eq_true_2 ((fst tk + j) < len)%nat ltac:(lia)).
      apply Hnn. lia.
  Qed.

  (* SEAM PREMISE 2: the RIGHT command's ONE word, at the same cut *)
  Lemma ushq_cut_ok_right (len : nat) (f : nat -> bv 8) (gp ge : nat)
      (args : list (nat * nat)) :
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    UkShPipeSeam.ushq_cut_ok len (ushq_cut args len f ge)
      [(S (S gp), ge)].
  Proof using .
    intros Hpq Htoks Hnn.
    pose proof Hpq as HQ.
    destruct HQ as (Hone & Hgp0 & Hb1 & Hb2 & Hlo & Hhi & Hfw & Htail).
    split_and!.
    - intros i tk Hi.
      destruct i as [| i ]; cbn [lookup list_lookup] in Hi;
        [ injection Hi as <-; cbn [fst snd]; lia | ].
      rewrite lookup_nil in Hi. discriminate.
    - intros i tk Hi.
      destruct i as [| i ]; cbn [lookup list_lookup] in Hi;
        [ injection Hi as <- | rewrite lookup_nil in Hi; discriminate ].
      cbn [snd]. rewrite /ushq_cut.
      cbn [UkShParseCmd.ushp_nulfold snd].
      rewrite /UkShParseCmd.ushp_setb Nat.eqb_refl. reflexivity.
    - intros i tk Hi j Hj.
      destruct i as [| i ]; cbn [lookup list_lookup] in Hi;
        [ injection Hi as <- | rewrite lookup_nil in Hi; discriminate ].
      cbn [fst snd] in Hj |- *.
      rewrite (ushq_cut_off args len f ge (S (S gp) + j)%nat ltac:(lia)).
      rewrite (UkShMain.ushp_nulfold_miss args (UkShParseCmd.ushp_ext len f)
                 (S (S gp) + j)%nat
                 ltac:(intros q t Hq;
                       destruct (ushq_args_below len f gp ge args Hpq Htoks
                                   q t Hq) as [ _ Hhi' ]; lia)).
      rewrite /UkShParseCmd.ushp_ext
        (bool_decide_eq_true_2 ((S (S gp) + j) < len)%nat ltac:(lia)).
      apply Hnn. lia.
  Qed.

  (* ===================================================================== *)
  (* §2 THE CHILD, at the pipe shape.                                       *)
  (* ===================================================================== *)
  Lemma wp_kshm_child_pipe
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp ge : nat)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr : iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    (⊢ ukn_pay N (-1)) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    usz γs szv -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UserChildren.uch γch Sc -∗
    UM0 -∗
    Cr -∗
    □ (app_taint -∗ Qc (-1)) -∗
    (* the arm's own split, with the walk's leftovers ([UM3], [Cr]) free to
       ride into whichever of the three it likes *)
    (∀ γp : pipe_names, UM3 -∗ Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ Rk γp)) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (* ---- THE LEFT CHILD: fd 1 is the pipe's WRITE end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) args)) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[1%nat := FdOpen false true (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcL γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    (* ---- THE RIGHT CHILD: fd 0 is the pipe's READ end ---- *)
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0 (ushq_cut args len f ge) [(S (S gp), ge)])) -∗
       usz (ukn_s N') szv -∗
       UserFd.ustd (ukn_fd N')
         (<[0%nat := FdOpen true false (FdPipe γp)]> ld) -∗
       UserCwd.ucwd (ukn_cwd N') cwdv -∗
       UserChildren.uch (ukn_ch N') (∅ : gset gname) -∗
       UkShPipe.ush_cldep (FdOpen true false (FdPipe γp)) -∗
       UkShPipe.ush_cldep (FdOpen false true (FdPipe γp)) -∗
       RcR γp -∗
       urun N' h' m' (mword_of_int ShSyms.runcmd)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    (* ---- THE PARENT, at 0xea ---- *)
    (∀ (h' : CpuId) (m' : regfile) (γp : pipe_names)
       (r1 r2 rw1 rw2 : mword 64) (S1 S2 S3 S4 : gset gname),
       UkShPipe.ush_fork_ans Sc S1 (RcL γp) Qc r1 -∗
       UkShPipe.ush_fork_ans S1 S2 (RcR γp) Qc r2 -∗
       uwait_ans rw1 S2 S3 -∗
       uwait_ans rw2 S3 S4 -∗
       UserChildren.uch γch S4 -∗
       ush_jtab γt -∗
       usz γs szv -∗
       UserFd.ustd γfd ld -∗
       UserCwd.ucwd γcwd cwdv -∗
       Rk γp -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hpq Htoks Hpos Htlen Hs0 Hs64 Hs38
           HQc Hpx Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1.
    (* the payload is free, so every parser walk's exit premise is free *)
    assert (HpxC : ⊢ □ (Cr -∗ ukn_pay N (-1))).
    { iIntros "!> _". iApply Hpx. }
    iIntros "#Hdp #Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hsz Hstd Hcwd Hch
             HM Hcr #Hkw Hsplit Hpipe Hrun HcL HcR Hpar".
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    iDestruct (ustr_len with "Hline") as %Hlen31.
    iPoseProof HpxC as "#Hpxw".
    (* ---- 0x9c0  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x9c0) a0_idx s1_idx
              (add_vec zero_reg (m !!! Regidx s1_idx))
              (68 + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) eq_refl with "[] Hrun").
    { iApply (uis_shk_9c0 with "Hcode"). }
    assert (E9c0 : add_vec_int (mword_of_int 0x9c0 : mword 64) 2
                   = mword_of_int 0x9c2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E9c0. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a0_idx
                 := regval_into_reg (add_vec zero_reg (m !!! Regidx s1_idx))]> m).
    assert (Ha0_1 : m1 !!! Regidx a0_idx = (mword_of_int s0 : mword 64)).
    { rewrite /m1 (upd_eq m (Regidx a0_idx) _).
      rewrite Hs1. apply bv_eq. rewrite add_vec_unsigned.
      unfold bv_wrap. cbn [bv_unsigned]. rewrite Z.add_0_l.
      rewrite Z.mod_small; [ reflexivity | ].
      pose proof (bv_unsigned_in_range _ (mword_of_int s0 : mword 64)) as Hr.
      assert (Hm : bv_modulus (MachineWord.Z_idx 64) = 18446744073709551616%Z)
        by (vm_compute; reflexivity).
      rewrite Hm in Hr. exact Hr. }
    (* ---- 0x9c2  jal ra,parsecmd ---- *)
    iApply (wp_uk_jal N h1 m1 (mword_of_int 0x9c2)
              (mword_of_int 2096812 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.parsecmd) (mword_of_int 0x9c6)
              (68 + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9c2 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx (mword_of_int 1 : mword 5)
                 := regval_into_reg (mword_of_int 0x9c6 : mword 64)]> m1).
    assert (Ha0_2 : m2 !!! Regidx a0_idx = (mword_of_int s0 : mword 64))
      by (rewrite /m2 (upd_ne m1 (Regidx (mword_of_int 1 : mword 5))
                         (Regidx a0_idx) _ ltac:(vm_compute; discriminate));
          exact Ha0_1).
    assert (Hra_2 : ret_pc (m2 !!! Regidx (mword_of_int 1 : mword 5))
                    = (mword_of_int 0x9c6 : mword 64))
      by (rewrite /m2 (upd_eq m1 (Regidx (mword_of_int 1 : mword 5)) _);
          apply bv_eq; vm_compute; reflexivity).
    (* ---- parsecmd, at the PIPE shape ---- *)
    iApply (UkShPipeCm.wp_kshp_parsecmd_bar N UM0 UM1 UM2 UM3
              ushq_malloc_ok12 h2 m2 dw dv s0 len f args gp ge
              (8 + (UkShDiag.ush_Dg + n))
              Hm01 Hm23 Ha0_2 Hpq Htoks Hpos Htlen Hs0 Hs64
              with "Hpcode Hpro Hline Hws Hsy HM Hpxw Hcr Hrun").
    iIntros (p pl pr) "Hpnode Hnodel Hnoder Hbytes Hws Hsy".
    iIntros (h3 m3) "%Hcs3 %Ha0_3 HM3 Hcr Hrun".
    rewrite Hra_2.
    (* ---- 0x9c6  jal ra,runcmd ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x9c6)
              (mword_of_int 2094792 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.runcmd) (mword_of_int 0x9ca)
              (68 + (8 + (UkShDiag.ush_Dg + n)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_9c6 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx (mword_of_int 1 : mword 5)
                 := regval_into_reg (mword_of_int 0x9ca : mword 64)]> m3).
    assert (Ha0_4 : m4 !!! Regidx a0_idx = (mword_of_int p : mword 64))
      by (rewrite /m4 (upd_ne m3 (Regidx (mword_of_int 1 : mword 5))
                         (Regidx a0_idx) _ ltac:(vm_compute; discriminate));
          exact Ha0_3).
    (* ---- THE SEAM, at the PIPE node ---- *)
    iMod (UkShMain.ubytes_persist γd s0 (S len) (ushq_cut args len f ge)
            with "Hbytes") as "#Hbytesq".
    iMod (UkShPipeSeam.ush_cmd_of_ushp_pipe N h4 m4
            (mword_of_int ShSyms.runcmd)
            (68 + (8 + (UkShDiag.ush_Dg + n)))
            s0 p pl pr len (ushq_cut args len f ge) args [(S (S gp), ge)]
            (ushq_cut_ok_left len f gp ge args Hpq Htoks Hnn0)
            (ushq_cut_ok_right len f gp ge args Hpq Htoks Hnn0)
            Hlen31 Hs0 Hs38
            with "Hrun Hpnode Hnodel Hnoder Hbytesq") as "(Hrun & #Htree)".
    (* ---- runcmd's PIPE arm ---- *)
    replace (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (68 + n))))%nat by lia.
    iApply (UkShPipe.wp_kshr_pipe_arm Hpsok_free N
              (UExec (ush_args s0 (ushq_cut args len f ge) args))
              (UExec (ush_args s0 (ushq_cut args len f ge) [(S (S gp), ge)]))
              h4 m4 p szv cwdv ld st0 st1 Sc (68 + n)%nat
              R RcL RcR Rk Qc
              HQc Hpx Ha0_4 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1
              with "Hdp Hcode Hjt Htree Hsz Hstd Hcwd Hch Hkw
                    [Hsplit HM3 Hcr] Hpipe Hrun HcL HcR Hpar").
    iIntros (γp) "HR". iApply ("Hsplit" $! γp with "HM3 Hcr HR").
  Qed.

End UkShPipeRound.
