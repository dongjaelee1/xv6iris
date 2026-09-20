(* ===================================================================== *)
(*  UShPipeChild.v -- THE PIPELINE LINE'S CHILD, PAID (lane              *)
(*  SH-PIPE-ROUND-3, item 1; design claude-notes/design/app-pipe.md      *)
(*  SS4.3c).                                                             *)
(*                                                                       *)
(*  [UkShPipeRound.wp_kshm_child_pipe] is sh's runcmd child at the pipe  *)
(*  line -- 0x9c0, [parsecmd], the seam, and [runcmd]'s PIPE arm -- and  *)
(*  it inherits two things from the FREE arm it ends on                   *)
(*  ([UkShPipe.wp_kshr_pipe_arm]): the free write law [UkSh.sh_deps],     *)
(*  which a verified shell holds only under the taint, and the free exit  *)
(*  payload [(|- ukn_pay N (-1))].  A ROUND whose console block the wire  *)
(*  accounts for holds neither (SH-PIPE-ROUND-2, refutation 2).           *)
(*                                                                       *)
(*  This file is the PAID twin, and it costs NO new walk: lane            *)
(*  PIPE-ARM-PAID left [UkShPipePaid.wp_kshr_pipe_arm_paid] -- the same   *)
(*  arm with its three [panic] tails paid at the era's credential -- so   *)
(*  what is here is [wp_kshm_child_pipe]'s walk ending on THAT.  It is    *)
(*  [UkShRedirChild.wp_kshm_child_file_redir] one line shape over: no     *)
(*  [UkSh.sh_deps] anywhere, every exit paid by a law into the payload,   *)
(*  and the lend [Cr] carried whole across the parse.                     *)
(*                                                                       *)
(*  WHAT IS NOT HERE, and why (see the lane report, STOP 1).  The brief's *)
(*  item 2 -- [UShPipeRound.sh_pipe_child_law] proved -- is NOT in this   *)
(*  file: the round's EXIT cannot be built out of the landed pieces.      *)
(*  [PipeBoth.pblk2_exit] files the round's code at the PROMPT's first    *)
(*  byte and leaves [PipeLinksLine.pwc_sp_t], i.e. [Wcf I 1]; sh's        *)
(*  runcmd child hands back [UkShFork.ushf_wq I = Wcf I 3 \/ Wcf I 0]     *)
(*  and the prompt is written by the MAIN loop, one process later.  The   *)
(*  mismatch is mechanised in [iris/UShPipeExit.v]                        *)
(*  ([pipe_open_not_line], [pipe_blk2_not_line]).                         *)
(*                                                                       *)
(*  TWO NOTES ON THE STATEMENT BELOW.                                     *)
(*                                                                       *)
(*   - THE ALLOCATOR'S LEFTOVER [UM3] IS DROPPED.  The free walk's split  *)
(*     took it ([forall gp, UM3 -* Cr -* R gp -* ...]) so a caller could  *)
(*     route it; the paid arm's split is fixed at [forall gp, Cr -* R gp  *)
(*     -* RcL gp * (RcR gp * (Rk gp * Cx gp))] -- the arm chooses whether *)
(*     [Cr] pays the [pipe(2)] tail or is split at the forks, so no       *)
(*     caller may split it up front -- and there is no slot for [UM3].    *)
(*     The child exits at the end of the round and the round wants        *)
(*     nothing of the heap, so the walk simply drops it.                  *)
(*   - [shk_rodata] is not a new premise: it is [UkSh.ush_jtab_ro] of the *)
(*     jump table the walk already holds.                                 *)
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
Require Import UkShRedirSeam.
Require Import UkShPipe.
Require Import UkShPipePaid.    (* the PAID arm *)
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import UkShPipeLex.
Require Import UkShPipeParse.
Require Import UkShPipeSeam.
Require Import UkShPipeCm.
Require Import UkShPipeRound.   (* the free walk, the cut and the line shape *)
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UexecSG.
Require Import UexecRet.
Local Open Scope Z_scope.
Import Defs.

Section UShPipeChild.
  (* [UkShPipeRound.v]'s binder list verbatim. *)
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

  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).

  Context (UM0 UM1 UM2 UM3 : iProp Σ).
  Hypothesis ushq_malloc_ok12 : ushp_malloc_ty UM1 UM2.

  (* =================================================================== *)
  (*  S1  THE PAID CHILD, at the pipe shape                               *)
  (* =================================================================== *)
  Lemma wp_kshm_child_pipe_paid
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp ge : nat)
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr Bp : iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (* fd 2 IS THE CONSOLE: a PAID write names the row it goes out on *)
    UkSh.ush_fd2p ld ->
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
    (* the lend pays the parse's own exits, whole (no [ukn_pay] for free) *)
    □ (Cr -∗ ukn_pay N (-1)) -∗
    (* the arm's own split -- the arm chooses between the [pipe(2)] tail
       and the forks, so nothing is split before it *)
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    (* ---- THE THREE DIAGNOSTICS, PAID ---- *)
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
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
    (* ---- THE PARENT, at 0xea, with the forks' borrowed credential ---- *)
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
       Cx γp -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hpq Htoks Hpos Htlen Hs0 Hs64 Hs38
           HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2.
    iIntros "#Hcode #Hjt #Hpcode #Hpro Hline Hws Hsy Hsz Hstd Hcwd Hch
             HM Hcr #Hkw #Hpxw Hsplit Hpipe #Hlawp #Hbp #Hlawf #Hbx Hrun
             HcL HcR Hpar".
    iDestruct (UkSh.ush_jtab_ro γt with "Hjt") as "#Hro".
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    iDestruct (ustr_len with "Hline") as %Hlen31.
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
    (* ---- parsecmd, at the PIPE shape: the lend crosses it whole ---- *)
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
    (* THE ALLOCATOR'S LEFTOVER IS DROPPED (see the header). *)
    iClear "Hbytesq". clear Ha0_3.
    (* ---- runcmd's PIPE arm, PAID ---- *)
    replace (68 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (68 + n))))%nat by lia.
    iApply (UkShPipePaid.wp_kshr_pipe_arm_paid Hpsok_free N
              (UExec (ush_args s0 (ushq_cut args len f ge) args))
              (UExec (ush_args s0 (ushq_cut args len f ge) [(S (S gp), ge)]))
              h4 m4 p szv cwdv ld st0 st1 Sc (68 + n)%nat
              R RcL RcR Rk Cx Bx Qc Cr Bp
              HQc Ha0_4 Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2
              with "Hcode Hro Hjt Htree Hsz Hstd Hcwd Hch Hkw Hcr Hsplit
                    Hpipe Hlawp Hbp Hlawf Hbx Hrun HcL HcR Hpar").
  Qed.

  (* =================================================================== *)
  (*  S2  ...AND AT THE LINE                                              *)
  (*                                                                     *)
  (*  [UkShPipeRound.wp_kshm_child_pipe_line]'s twin: the buffer at [s0]  *)
  (*  holds `echo w1 ... wn | cat\n' and the two children come out at     *)
  (*  [runcmd]'s entry with the pipe's two ends at fd 1 and fd 0.         *)
  (* =================================================================== *)
  Corollary wp_kshm_child_pipe_paid_line
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 szv cwdv : Z) (len : nat) (f : nat -> bv 8)
      (ws : list (list (bv 8)))
      (ld : list fdstate) (st0 st1 : fdstate) (Sc : gset gname) (n : nat)
      (R RcL RcR Rk Cx Bx : pipe_names -> iProp Σ) (Qc : Z -> iProp Σ)
      (Cr Bp : iProp Σ) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    UkShPipeRound.ushq_line_at ws f 0%nat len ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    (forall x y : Z, Qc x = Qc y) ->
    ld !! 0%nat = Some st0 -> ld !! 1%nat = Some st1 ->
    st0 <> FdClosed -> st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : pipe_names),
       st0 <> FdOpen rb wb (FdPipe gn)) ->
    (forall (rb wb : bool) (gn : pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
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
    □ (Cr -∗ ukn_pay N (-1)) -∗
    (∀ γp : pipe_names, Cr -∗ R γp -∗ RcL γp ∗ (RcR γp ∗ (Rk γp ∗ Cx γp))) -∗
    UkShPipe.ush_pipe_call N ld R -∗
    UkShDiag.ush_execfail_law_at (wl_line PipeDisc.dg_pipe) 5%nat Cr Bp -∗
    □ (UserFd.ustd γfd ld -∗ Bp -∗ ukn_pay N (-1)) -∗
    □ (∀ γp : pipe_names,
         UkShDiag.ush_execfail_law_at EchoDisc.alt_panic 5%nat
           (Cx γp) (Bx γp)) -∗
    □ (∀ γp : pipe_names,
         UserFd.ustd γfd ld -∗ Bx γp -∗ ukn_pay N (-1)) -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0
                   (ushq_cut (wl_toks ws) len f
                      (length (wl_body ws) + 3 + 3)%nat) (wl_toks ws))) -∗
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
    (∀ (N' : uk_names Σ) (h' : CpuId) (m' : regfile) (γ' : gname)
       (γp : pipe_names) (q : Z),
       ⌜ ukn_pay N' = Qc ⌝ -∗
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       my_pay γ' Qc -∗
       shk_code (ukn_t N') -∗
       ush_jtab (ukn_t N') -∗
       ush_cmd (ukn_d N') q
         (UExec (ush_args s0
                   (ushq_cut (wl_toks ws) len f
                      (length (wl_body ws) + 3 + 3)%nat)
                   [((length (wl_body ws) + 3)%nat,
                     (length (wl_body ws) + 3 + 3)%nat)])) -∗
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
       Cx γp -∗
       urun N h' m' (mword_of_int 0xea)
         (2 + (UkShDiag.ush_Dg + (68 + n))) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpay Hpsok_free ushq_malloc_ok12.
    intros Hm01 Hm23 Hs1 Hline Hs0 Hs64 Hs38 HQc Hl0 Hl1 Hne0 Hne1
           Hnp0 Hnp1 Hfd2.
    pose proof (UkShPipeRound.ushq_line_is_of_at ws f 0%nat len Hline) as Hli.
    destruct (UkShPipeLex.ush_line_toks_holds_pipe ws UkShPipeLex.ushq_cat f
                0%nat len Hli) as (Hq & Ht & Hpos & Htlen & _).
    assert (Ef : (fun j : nat => f (0 + j)%nat) = f) by reflexivity.
    rewrite Ef in Hq, Ht.
    rewrite UkShPipeLex.ushq_cat_len in Hq.
    assert (Ege : (length (wl_body ws) + 3)%nat
                  = S (S (length (wl_body ws) + 1))) by lia.
    rewrite Ege in Hq |- *.
    exact (wp_kshm_child_pipe_paid h m dw dv s0 szv cwdv len f (wl_toks ws)
             (length (wl_body ws) + 1)%nat
             (S (S (length (wl_body ws) + 1)) + 3)%nat
             ld st0 st1 Sc n R RcL RcR Rk Cx Bx Qc Cr Bp
             Hm01 Hm23 Hs1 Hq Ht Hpos Htlen Hs0 Hs64 Hs38
             HQc Hl0 Hl1 Hne0 Hne1 Hnp0 Hnp1 Hfd2).
  Qed.

End UShPipeChild.
