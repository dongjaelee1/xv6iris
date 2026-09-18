(* ===================================================================== *)
(*  UEchoPipe.v -- ECHO'S ENTRY AT fd 1 = A PIPE WRITE END               *)
(*  (design/app-pipe.md SS5.2, lane ECHO-PIPE.)                           *)
(*                                                                       *)
(*  [UEchoOut.v] is echo's entry at fd 1 = the CONSOLE and [UEchoFile.v]  *)
(*  its (skeleton) twin at fd 1 = a file; this is the twin at fd 1 = the  *)
(*  WRITE END OF A PIPE.  echo's code walk is UNTOUCHED ([UkEcho.v]):     *)
(*  the four [kecho_w] obligations are the same, discharged at a LEDGER   *)
(*  slot whose row is [FdOpen rb true (FdPipe gp)] instead of the console *)
(*  device, through [UkWritePipe]'s ledger-slot deposit                   *)
(*  ([UkRun.udepwf_std], lane PIPE-STD) and [PipeProto]'s payment         *)
(*  ([pipe_wpay_of_inv] at the running cursor, lane PIPE-PROTO).          *)
(*                                                                       *)
(*  WHAT ECHO PRINTS ON THE CONSOLE AT A PIPE: nothing ([UEchoFile]'s     *)
(*  finding, verbatim).  The era's console credential -- and the side     *)
(*  token the forking shell lent -- cross this entry UNTOUCHED and are    *)
(*  handed back at the exit; they appear here as [Wq] and [side_L], so    *)
(*  this file takes no link and no stage.                                *)
(*                                                                       *)
(*  ------------------------------------------------------------------- *)
(*  THE ONE WALL, and it is this lane's finding (see [ep_derail] below).  *)
(*                                                                       *)
(*  [pipe_wpost] lets a write STOP SHORT for two reasons a mapped source  *)
(*  cannot refute: the writer was killed, and the READ END IS SHUT        *)
(*  ([ps_ro s = false], the [PExecR] world).  Both hand the cursor back   *)
(*  at [c + k] with [k < n] -- and from there echo's NEXT write is        *)
(*  UNPAYABLE.  echo ignores write's return and goes on to the next       *)
(*  chunk, whose bytes are the line's at offset [c + n]; a [pipe_wlink]   *)
(*  built from [PipeProto.pipe_inv] must re-establish (P1)                *)
(*  [ps_ws s `prefix_of` L], and appending [L !!! (c+n+j)] to             *)
(*  [take (c+k) L] is not a prefix of [L] unless [k = n].  The payment    *)
(*  [pipe_wpay] is [chain \/ app_taint] and echo holds neither.           *)
(*                                                                       *)
(*  So the protocol AS LANDED has no continuation for a derailed writer,  *)
(*  and this file names exactly the missing capability -- [ep_derail],    *)
(*  [once the line and the pipe have diverged, a further write is still   *)
(*  payable and leaves you diverged] -- as a premise of the entry, IN     *)
(*  THE ENTRY'S OWN [Pay] so that the gap is visible at the statement.    *)
(*  It is not derivable from [pipe_inv]: the two ways to discharge it are *)
(*  in the lane's Findings block (a DERAIL arm on (P1), or a read-end     *)
(*  liveness observation in the body).  Everything else here is proved.   *)
(*                                                                       *)
(*  WHAT THE EXIT PAYLOAD SAYS, in consequence: [ep_ok pn L (length L)] --*)
(*  either the cursor at the line's end (which IS [the line is in],       *)
(*  [pws_lb pn L], design SS4.2's [PRan] arm) or the HALT: some cursor     *)
(*  [c <= length L], or the taint.  [PipeProto.pipe_payL] has arms only   *)
(*  for the two ENDS of that range ([pws_lb pn L] and [wtok pn]); see     *)
(*  [ep_exit_payL] below and the Findings block.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import VcGen.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import ExecEntry.               (* [image_entry] -- the exec channel *)
Require Import SpecKexec.               (* [kexec_image_ok] *)
Require Import SpecSysExec.             (* [exec_args_of] *)
Require Import UkRun UkRunSys.
Require Import UexecExecInst.           (* THE INSTANCES: [uexecSG_xv6] etc. *)
Require Import SpecSysRead.             (* [sys_rw_count] *)
Require Import SpecFilewrite.           (* [filewrite_extra] *)
Require Import PipeInvDefs.
Require Import PipeQueue.               (* [pipe_wpay], [pipe_wpost], ... *)
Require Import PipeReg.                 (* [pipe_reg] *)
Require Import PipeProto.               (* THE PROTOCOL *)
Require Import UkWriteLeaf.
Require Import UkReadRows.              (* [std_fd_st_of_key] *)
Require Import UkWritePipe.             (* the ledger-slot pipe deposit *)
Require Import UkAbi.
Require Import UserHeap.
Require Import UCodeEcho.
Require Import UkEcho.
Require Import UEchoKernel.
Require Import LineWords.
Require Import EchoDisc.
Require Import UEchoOut.                (* THE MOULD: [out_argv_at] etc. *)
Require Import ElfUser.                 (* [echo_elf] *)
Require Import UkShEcho.                (* [echo_argv_bytes] *)
Require Import UShEcho.                 (* [echo_node_img], the room bound *)
Require Import UShEchoOut.              (* [echo_out_argv_of_image] *)
Require Import CtxIdDefs.
Require User.EchoSyms.
Local Open Scope Z_scope.
Import Defs.

Section UEchoPipe.
  (* [UEchoOut.v]'s binder list MINUS the link/stage record (echo prints no
     console byte at a pipe) PLUS the protocol's ghosts.  NO [uexecSG]
     section variable, for [UEchoOut]'s reason: this file reads row 16's
     CONCRETE arm, so the instance must be the ambient xv6 one. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!pipeProtoG Σ}.
  Context `{PS : uprogSG Σ}.

  (* THE ERA'S CONSOLE CREDENTIAL, OPAQUE -- [UEchoFile]'s [Wq].  echo
     writes no console byte at a pipe, so whatever the fork lent
     ([UkShFork.ushf_wq]'s left arm) crosses this entry untouched. *)
  Context (Wq : iProp Σ).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  S1  THE CURSOR, THE HALT, AND THE PROTOCOL'S MISSING ARM            *)
  (* =================================================================== *)

  (* WHERE ECHO IS: the write permit at [c] and the history's lower bound
     at the line's first [c] bytes.  It IS [PipeProto.pipe_wQ pn L c 0]
     read at an absolute cursor, which is what makes the four writes
     compose ([pipe_wQ pn L c k = ep_cur pn L (c + k)], definitionally). *)
  Definition ep_cur (pn : pnames) (L : list (bv 8)) (c : nat) : iProp Σ :=
    (wcur pn c ∗ pws_lb pn (take c L))%I.

  (* THE HALT: the line and the pipe have diverged (a write stopped short
     because the writer was killed or the read end was shut), or the
     application is tainted.  Nothing about the pipe's contents is claimed
     -- which is exactly design SS4.2's [PExecR] world, where the console
     shows the right child's diagnostic and the pipe is irrelevant. *)
  Definition ep_stuck (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    (∃ c : nat, ⌜(c <= length L)%nat⌝ ∗ ep_cur pn L c)%I.

  Definition ep_halt (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    (ep_stuck pn L ∨ app_taint)%I.

  (* WHAT HOLDS BETWEEN TWO OF ECHO'S WRITES. *)
  Definition ep_ok (pn : pnames) (L : list (bv 8)) (c : nat) : iProp Σ :=
    (ep_cur pn L c ∨ ep_halt pn L)%I.

  (* ------------------------------------------------------------------- *)
  (*  THE PROTOCOL'S MISSING ARM (this lane's finding; see the header).    *)
  (*                                                                     *)
  (*  A derailed writer can pay NOTHING: [pipe_wpay] is [chain \/ taint], *)
  (*  the chain's links must re-establish (P1) and the bytes no longer    *)
  (*  continue the pipe's contents.  This is the one capability that      *)
  (*  closes echo's walk, stated at the smallest shape that does it: from *)
  (*  a halted cursor, any write of any run is payable and leaves you     *)
  (*  halted.  It is PERSISTENT (a [box]) because echo needs it at every  *)
  (*  one of its four calls.                                             *)
  (*                                                                     *)
  (*  IT IS NOT DERIVABLE FROM [pipe_inv] AS LANDED, and it is not        *)
  (*  vacuous either: a (P1) with a DERAIL arm supplies it in one step.   *)
  (* ------------------------------------------------------------------- *)
  Definition ep_derail (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      : iProp Σ :=
    (□ ∀ (M : gmap Z (bv 8)) (ua : mword 64) (n : nat),
        ep_stuck pn L -∗
        pipe_wpay (pn_queue γp) M ua
          (fun _ : nat => ep_halt pn L)
          (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) n)%I.

  Global Instance ep_derail_persistent pn γp L : Persistent (ep_derail pn γp L).
  Proof using . rewrite /ep_derail. apply _. Qed.

  (* WHAT CROSSES THE ENTRY UNTOUCHED: the side token the runcmd child lent
     its LEFT child (design SS4.2, as amended) and the era's console
     credential. *)
  Definition ep_frame (pn : pnames) : iProp Σ := (side_L pn ∗ Wq)%I.

  Definition ep_car (pn : pnames) (L : list (bv 8)) (c : nat) : iProp Σ :=
    (ep_frame pn ∗ ep_ok pn L c)%I.

  (* THE EXIT PAYLOAD: the frame back, and the cursor at the line's end --
     or the halt. *)
  Definition ep_exit (pn : pnames) (L : list (bv 8)) : iProp Σ :=
    ep_car pn L (length L).

  (* THE LEND [ExecEntry.image_entry]'s [Pay] slot carries: the protocol's
     handle, the missing arm, the frame, and the write permit at ZERO with
     the empty lower bound (design SS5.2's [Pay], with [ep_derail] added). *)
  Definition ep_pay (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      : iProp Σ :=
    (pipe_inv pn γp L ∗ ep_derail pn γp L ∗ ep_frame pn
     ∗ wcur pn 0%nat ∗ pws_lb pn [])%I.

  Lemma ep_car_of_pay (pn : pnames) (γp : pipe_names) (L : list (bv 8)) :
    ep_pay pn γp L -∗
    pipe_inv pn γp L ∗ ep_derail pn γp L ∗ ep_car pn L 0%nat.
  Proof using .
    rewrite /ep_pay /ep_car /ep_ok /ep_cur.
    iIntros "(#Hinv & #Hd & Hfr & Hw & Hlb)".
    iFrame "Hinv Hd Hfr". iLeft. rewrite take_0. iFrame "Hw Hlb".
  Qed.

  (* ...AND WHAT SH CAN READ OFF THE EXIT.  The good arm is
     [PipeProto.pipe_payL]'s left one -- "the line is in".  The HALT is NOT
     [pipe_payL]'s right arm unless the cursor never moved: [pipe_payL] has
     [pws_lb pn L \/ wtok pn], the two ENDS of the range, and a write that
     stopped in the middle is neither.  That is the lane's second finding. *)
  Lemma ep_exit_payL (pn : pnames) (L : list (bv 8)) :
    ep_exit pn L -∗
    side_L pn ∗ Wq
    ∗ (pws_lb pn L
       ∨ (∃ c : nat, ⌜(c <= length L)%nat⌝ ∗ wcur pn c ∗ pws_lb pn (take c L))
       ∨ app_taint).
  Proof using .
    rewrite /ep_exit /ep_car /ep_frame /ep_ok /ep_cur /ep_halt /ep_stuck.
    iIntros "[[$ $] [[_ Hlb] | [H | #Ht]]]".
    - rewrite take_ge; [ | lia ]. by iLeft.
    - iRight. by iLeft.
    - iRight. by iRight.
  Qed.

  (* =================================================================== *)
  (*  S2  WHAT A WRITE'S POST LEAVES                                      *)
  (* =================================================================== *)

  (* EVERY ARM leaves [ep_ok] at the cursor the call was asked to reach.
     The COPYIN FAULT is refuted by the caller's own mapped source run
     ([UkRunSys.usrc_ok]'s second conjunct, which the write stub hands
     back), so the arm that answers the count answers the WHOLE count; the
     two that remain -- the kill shot and the shut read end -- are the
     halt. *)
  Lemma ep_post_ok (Pt : uptd) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (M : gmap Z (bv 8)) (ua : mword 64) (c n : nat)
      (Rk : iProp Σ) (r : mword 64) :
    (c + n <= length L)%nat ->
    (forall j : nat, (j < n)%nat ->
       UserPtTree.uva_rmapped Pt (uint (add_vec_int ua (Z.of_nat j)))) ->
    pipe_wpost Pt (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c)
      Rk n r -∗
    ep_ok pn L (c + n).
  Proof using .
    intros Hle Hmap. iIntros "H".
    iDestruct (pipe_wpost_cursor with "H") as "[H | [#Ht _]]"; last first.
    { rewrite /ep_ok /ep_halt. iRight. by iRight. }
    iDestruct "H" as (k) "[%Hk H]".
    rewrite /ep_ok /ep_halt /ep_stuck /ep_cur /pipe_wQ /pipe_wQe.
    iDestruct "H" as "[(_ & %Hs & HQ) | [(_ & %Hlt & _ & HQ) | Hobs]]".
    - assert (Hkn : k = n).
      { destruct Hs as [Hkn | Hnm]; [ exact Hkn | ].
        destruct (decide (k = n)) as [Hkn | Hne]; [ exact Hkn | ].
        exfalso. apply Hnm. apply Hmap. lia. }
      subst k. iLeft. iExact "HQ".
    - iRight. iLeft. iExists (c + k)%nat.
      iSplitR; [ iPureIntro; lia | ]. iExact "HQ".
    - iDestruct "Hobs" as "(_ & %Hlt & Hobs)".
      iDestruct "Hobs" as (s) "[_ HQ]".
      iRight. iLeft. iExists (c + k)%nat.
      iSplitR; [ iPureIntro; lia | ]. iExact "HQ".
  Qed.

  (* ...AND A WRITE PAID FROM THE HALT LEAVES THE HALT. *)
  Lemma ep_post_halt (Pt : uptd) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (M : gmap Z (bv 8)) (ua : mword 64) (n : nat)
      (Rk : iProp Σ) (r : mword 64) :
    pipe_wpost Pt (pn_queue γp) M ua
      (fun _ : nat => ep_halt pn L)
      (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) Rk n r -∗
    ep_halt pn L.
  Proof using .
    iIntros "H".
    iDestruct (pipe_wpost_cursor with "H") as "[H | [#Ht _]]"; last first.
    { rewrite /ep_halt. by iRight. }
    iDestruct "H" as (k) "[_ H]".
    iDestruct "H" as "[(_ & _ & $) | [(_ & _ & _ & $) | Hobs]]".
    iDestruct "Hobs" as "(_ & _ & Hobs)".
    iDestruct "Hobs" as (s) "[_ $]".
  Qed.

  (* the payment a HALTED echo makes -- the missing arm at the taint arm's
     side too, where it is free *)
  Lemma ep_pay_halt (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (M : gmap Z (bv 8)) (ua : mword 64) (n : nat) :
    ep_derail pn γp L -∗ ep_halt pn L -∗
    pipe_wpay (pn_queue γp) M ua
      (fun _ : nat => ep_halt pn L)
      (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) n.
  Proof using .
    iIntros "#Hd [Hst | #Ht]".
    - iApply ("Hd" $! M ua n with "Hst").
    - iApply (pipe_wpay_taint with "Ht").
  Qed.

  (* =================================================================== *)
  (*  S3  ONE OF ECHO'S FOUR WRITES, AT fd 1 = THE PIPE'S WRITE END       *)
  (*                                                                     *)
  (*  [UEchoOut.kecho_w_of_link_data_at] / [_txt_at] one row over: where  *)
  (*  the console member spends the era's write link, this one spends the  *)
  (*  protocol's write chain, built at the running cursor by              *)
  (*  [PipeProto.pipe_wpay_of_inv] over the heap the call runs at.  The    *)
  (*  M-premise ([UEchoFile]'s wrapper, and the one thing PIPE-PROTO left  *)
  (*  this lane) is discharged from the caller's own source run --        *)
  (*  [UkRunSys.uheap_ubytes_wat] for argv's strings,                     *)
  (*  [UserHeap.uheap_text] for the two .rodata literals.                 *)
  (* =================================================================== *)

  (* THE ARGV CALLS: the source run is in the DATA half. *)
  Lemma ep_w_data (N : uk_names Σ) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (l : list fdstate) (rb : bool)
      (c : nat) (ua : Z) (nb : nat) (fb : nat -> bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdPipe γp)) ->
    (c + nb <= length L)%nat ->
    (forall j : nat, (j < nb)%nat -> L !!! (c + j)%nat = fb j) ->
    pipe_inv pn γp L -∗
    ep_derail pn γp L -∗
    ustr (ukn_d N) DfracDiscarded ua nb fb -∗
    kecho_w N (mword_of_int ua) nb
      (UserFd.ustd (ukn_fd N) l ∗ ep_car pn L c)
      (UserFd.ustd (ukn_fd N) l ∗ ep_car pn L (c + nb)).
  Proof.
    intros Hl1 Hle Hbytes.
    iIntros "#Hinv #Hder #Hstr" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd [Hfr Hok]] Hrun Hcont".
    iDestruct (urun_ustr_bnd N h m _ avail DfracDiscarded ua nb fb
                 with "Hrun Hstr") as %[Hlo Hhi].
    change (2 ^ 38) with 274877906944 in Hhi.
    assert (Hua : uint (m !!! Regidx a1_idx) = ua)
      by (rewrite Ha1; apply uint_moi; unfold Z64; lia).
    iDestruct (ustr_len with "Hstr") as %Hlen31.
    iAssert (ubytesq (ukn_d N) DfracDiscarded
               (uint (m !!! Regidx a1_idx)) nb fb) as "#Hbs".
    { rewrite Hua. by iDestruct "Hstr" as "(_ & _ & $ & _)". }
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat nb) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 1%nat)
      by (rewrite Ham0; vm_compute; reflexivity).
    pose proof (echo_count_is nb Hlen31) as Hcz.
    assert (Hcnt : sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx) = Z.of_nat nb)
      by (rewrite Ham2; exact Hcz).
    assert (Hrow : bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat 1%nat)
      by (rewrite Ha0; vm_compute; reflexivity).
    assert (Htn : Z.to_nat (sys_rw_count (m !!! Regidx a2_idx)) = nb)
      by (rewrite Ha2 Hcz; lia).
    iDestruct "Hok" as "[Hcur | Hhalt]".
    - (* ---- ON THE LINE: the protocol's chain at the cursor ---- *)
      iApply (wp_kecho_write_chain N h m avail
                (write_pipe_fam (pipe_wQ pn L c) (pipe_wQe pn L c) (ukn_pay N))
                l DfracDiscarded nb fb with "Hcode Hrun [Hcur] Hstd Hbs").
      { iApply (udepwf_std_write_pipe N
                  (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                  (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2)
                  l 1%nat rb γp (pipe_wQ pn L c) (pipe_wQe pn L c) nb
                  Hi0 ltac:(unfold NSTD; lia) Hl1 Hcnt).
        iIntros (M pm sz) "Hheap".
        iDestruct (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                     DfracDiscarded (m !!! Regidx a1_idx) nb fb
                     with "Hheap Hbs") as %HM.
        assert (HM2 : forall k : nat, (k < nb)%nat ->
                  M !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat k))
                  = Some (L !!! (c + k)%nat)).
        { intros k Hk. rewrite (Hbytes k Hk). exact (HM k Hk). }
        iFrame "Hheap". rewrite Ham1.
        iDestruct "Hcur" as "[Hw Hlb]".
        iApply (pipe_wpay_of_inv pn γp L M (m !!! Regidx a1_idx) c nb Hle HM2
                  with "Hinv Hw Hlb"). }
      iIntros (h' ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hbs' Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_pipe_fam (pipe_wQ pn L c) (pipe_wQe pn L c)
                      (ukn_pay N))
                   W (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                   (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                   ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as (Pt) "(%Hpmp & %Hwfp & %Hlzp & Hextra)".
      iDestruct (uwrite_pipe_extra (uvis_gen W) Pt
                   (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) rb γp
                   (sys_rw_count (m !!! Regidx a2_idx)) (uvis_M W)
                   (m !!! Regidx a1_idx) (pipe_wQ pn L c) (pipe_wQe pn L c) ret
                   (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l 1%nat
                      (FdOpen rb true (FdPipe γp)) Hrow
                      ltac:(unfold NSTD; lia) Htk Hl1)
                   with "Hextra") as "Hwp".
      rewrite Htn.
      iDestruct (ep_post_ok Pt pn γp L (uvis_M W) (m !!! Regidx a1_idx) c nb
                   (ChildTok.kill_shot (uvis_gen W)) ret Hle
                   ltac:(intros j Hj; exact (Hnf Pt j Hwfp Hpmp (Hlzp Hlz) Hj))
                   with "Hwp") as "Hok".
      iApply ("Hcont" $! h' ret with "[Hstd Hfr Hok] Hrun").
      iFrame "Hstd Hfr". iExact "Hok".
    - (* ---- HALTED: the missing arm pays, and the halt survives ---- *)
      iApply (wp_kecho_write_chain N h m avail
                (write_pipe_fam (fun _ : nat => ep_halt pn L)
                   (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) (ukn_pay N))
                l DfracDiscarded nb fb with "Hcode Hrun [Hhalt] Hstd Hbs").
      { iApply (udepwf_std_write_pipe N
                  (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                  (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2)
                  l 1%nat rb γp (fun _ : nat => ep_halt pn L)
                  (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) nb
                  Hi0 ltac:(unfold NSTD; lia) Hl1 Hcnt).
        iIntros (M pm sz) "Hheap". iFrame "Hheap". rewrite Ham1.
        iApply (ep_pay_halt pn γp L M (m !!! Regidx a1_idx) nb
                  with "Hder Hhalt"). }
      iIntros (h' ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hbs' Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_pipe_fam (fun _ : nat => ep_halt pn L)
                      (fun (_ : nat) (_ : pipe_st) => ep_halt pn L)
                      (ukn_pay N))
                   W (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                   (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                   ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as (Pt) "(%Hpmp & %Hwfp & %Hlzp & Hextra)".
      iDestruct (uwrite_pipe_extra (uvis_gen W) Pt
                   (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) rb γp
                   (sys_rw_count (m !!! Regidx a2_idx)) (uvis_M W)
                   (m !!! Regidx a1_idx) (fun _ : nat => ep_halt pn L)
                   (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) ret
                   (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l 1%nat
                      (FdOpen rb true (FdPipe γp)) Hrow
                      ltac:(unfold NSTD; lia) Htk Hl1)
                   with "Hextra") as "Hwp".
      rewrite Htn.
      iDestruct (ep_post_halt Pt pn γp L (uvis_M W) (m !!! Regidx a1_idx) nb
                   (ChildTok.kill_shot (uvis_gen W)) ret with "Hwp") as "Hh".
      iApply ("Hcont" $! h' ret with "[Hstd Hfr Hh] Hrun").
      iFrame "Hstd Hfr". rewrite /ep_ok. iRight. iExact "Hh".
  Qed.

  (* THE TWO LITERAL CALLS, at one byte each: echo's separator and its
     newline are .rodata -- X and NOT W, filed under the TEXT gname, and no
     [ubytesq] of them exists ([UEchoOut]'s finding), so the stub is the
     TEXT one and the M-premise comes off [UserHeap.uheap_text]. *)
  Lemma ep_w_txt (N : uk_names Σ) (pn : pnames) (γp : pipe_names)
      (L : list (bv 8)) (l : list fdstate) (rb : bool)
      (c : nat) (ua : Z) (b : bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdPipe γp)) ->
    (c + 1 <= length L)%nat ->
    L !!! c = b ->
    0 <= ua < 2 ^ 38 ->
    pipe_inv pn γp L -∗
    ep_derail pn γp L -∗
    utext (ukn_t N) ua b -∗
    kecho_w N (mword_of_int ua) 1%nat
      (UserFd.ustd (ukn_fd N) l ∗ ep_car pn L c)
      (UserFd.ustd (ukn_fd N) l ∗ ep_car pn L (c + 1)).
  Proof.
    intros Hl1 Hle Hbyte Hrange.
    change (2 ^ 38) with 274877906944 in Hrange.
    iIntros "#Hinv #Hder #Hb" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd [Hfr Hok]] Hrun Hcont".
    assert (Hua : uint (m !!! Regidx a1_idx) = ua)
      by (rewrite Ha1; apply uint_moi; unfold Z64; lia).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 1%nat)
      by (rewrite Ham0; vm_compute; reflexivity).
    pose proof (echo_count_is 1%nat ltac:(cbn; lia)) as Hcz.
    assert (Hcnt : sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx) = Z.of_nat 1%nat)
      by (rewrite Ham2; exact Hcz).
    assert (Hrow : bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat 1%nat)
      by (rewrite Ha0; vm_compute; reflexivity).
    assert (Htn : Z.to_nat (sys_rw_count (m !!! Regidx a2_idx)) = 1%nat)
      by (rewrite Ha2 Hcz; lia).
    iAssert ([∗ list] j ∈ seq 0 1,
               utext (ukn_t N) (uint (m !!! Regidx a1_idx) + Z.of_nat j)%Z
                 ((fun _ : nat => b) j))%I as "#Hbs".
    { cbn [seq]. rewrite big_sepL_singleton Hua Z.add_0_r. iExact "Hb". }
    iDestruct "Hok" as "[Hcur | Hhalt]".
    - (* ---- ON THE LINE ---- *)
      iApply (wp_kecho_write_chain_txt N h m avail
                (write_pipe_fam (pipe_wQ pn L c) (pipe_wQe pn L c) (ukn_pay N))
                l 1%nat (fun _ : nat => b) with "Hcode Hrun [Hcur] Hstd Hbs").
      { iApply (udepwf_std_write_pipe N
                  (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                  (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2)
                  l 1%nat rb γp (pipe_wQ pn L c) (pipe_wQe pn L c) 1%nat
                  Hi0 ltac:(unfold NSTD; lia) Hl1 Hcnt).
        iIntros (M pm sz) "Hheap".
        iDestruct (uheap_text (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ua b
                     with "Hheap Hb") as %(HM & _ & _).
        assert (HM2 : forall k : nat, (k < 1)%nat ->
                  M !! uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat k))
                  = Some (L !!! (c + k)%nat)).
        { intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k.
          rewrite Nat.add_0_r Hbyte.
          change (Z.of_nat 0%nat) with 0%Z. rewrite avi0 Hua. exact HM. }
        iFrame "Hheap". rewrite Ham1.
        iDestruct "Hcur" as "[Hw Hlb]".
        iApply (pipe_wpay_of_inv pn γp L M (m !!! Regidx a1_idx) c 1%nat Hle
                  HM2 with "Hinv Hw Hlb"). }
      iIntros (h' ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_pipe_fam (pipe_wQ pn L c) (pipe_wQe pn L c)
                      (ukn_pay N))
                   W (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                   (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                   ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as (Pt) "(%Hpmp & %Hwfp & %Hlzp & Hextra)".
      iDestruct (uwrite_pipe_extra (uvis_gen W) Pt
                   (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) rb γp
                   (sys_rw_count (m !!! Regidx a2_idx)) (uvis_M W)
                   (m !!! Regidx a1_idx) (pipe_wQ pn L c) (pipe_wQe pn L c) ret
                   (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l 1%nat
                      (FdOpen rb true (FdPipe γp)) Hrow
                      ltac:(unfold NSTD; lia) Htk Hl1)
                   with "Hextra") as "Hwp".
      rewrite Htn.
      iDestruct (ep_post_ok Pt pn γp L (uvis_M W) (m !!! Regidx a1_idx) c 1%nat
                   (ChildTok.kill_shot (uvis_gen W)) ret Hle
                   ltac:(intros j Hj; exact (Hnf Pt j Hwfp Hpmp (Hlzp Hlz) Hj))
                   with "Hwp") as "Hok".
      iApply ("Hcont" $! h' ret with "[Hstd Hfr Hok] Hrun").
      iFrame "Hstd Hfr". iExact "Hok".
    - (* ---- HALTED ---- *)
      iApply (wp_kecho_write_chain_txt N h m avail
                (write_pipe_fam (fun _ : nat => ep_halt pn L)
                   (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) (ukn_pay N))
                l 1%nat (fun _ : nat => b) with "Hcode Hrun [Hhalt] Hstd Hbs").
      { iApply (udepwf_std_write_pipe N
                  (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                  (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2)
                  l 1%nat rb γp (fun _ : nat => ep_halt pn L)
                  (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) 1%nat
                  Hi0 ltac:(unfold NSTD; lia) Hl1 Hcnt).
        iIntros (M pm sz) "Hheap". iFrame "Hheap". rewrite Ham1.
        iApply (ep_pay_halt pn γp L M (m !!! Regidx a1_idx) 1%nat
                  with "Hder Hhalt"). }
      iIntros (h' ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_pipe_fam (fun _ : nat => ep_halt pn L)
                      (fun (_ : nat) (_ : pipe_st) => ep_halt pn L)
                      (ukn_pay N))
                   W (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                   (m !!! Regidx a2_idx) (uvis_fd W) (uvis_M W)
                   ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as (Pt) "(%Hpmp & %Hwfp & %Hlzp & Hextra)".
      iDestruct (uwrite_pipe_extra (uvis_gen W) Pt
                   (fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W)) rb γp
                   (sys_rw_count (m !!! Regidx a2_idx)) (uvis_M W)
                   (m !!! Regidx a1_idx) (fun _ : nat => ep_halt pn L)
                   (fun (_ : nat) (_ : pipe_st) => ep_halt pn L) ret
                   (std_fd_st_of_key (m !!! Regidx a0_idx) (uvis_fd W) l 1%nat
                      (FdOpen rb true (FdPipe γp)) Hrow
                      ltac:(unfold NSTD; lia) Htk Hl1)
                   with "Hextra") as "Hwp".
      rewrite Htn.
      iDestruct (ep_post_halt Pt pn γp L (uvis_M W) (m !!! Regidx a1_idx) 1%nat
                   (ChildTok.kill_shot (uvis_gen W)) ret with "Hwp") as "Hh".
      iApply ("Hcont" $! h' ret with "[Hstd Hfr Hh] Hrun").
      iFrame "Hstd Hfr". rewrite /ep_ok. iRight. iExact "Hh".
  Qed.

End UEchoPipe.
