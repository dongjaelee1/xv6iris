(* ===================================================================== *)
(* UShLine.v -- SH-LINE 2b PHASE 2: SH'S CONSOLE READ, SUPPLIED.          *)
(*                                                                        *)
(* [UConsLine.ush_read_recv_leaf] is the read leaf sh's [gets] wants: the  *)
(* one that KEEPS the kernel's receipt, so the shell learns that the byte  *)
(* it was handed is the next one after the byte it was handed last.  Two   *)
(* things have to happen for that leaf to exist, and both need the         *)
(* CONCRETE deposit bundle ([UexecExecInst]'s instance of                  *)
(* [UexecSG.uexecSG]) in scope -- which is why this file is here and not   *)
(* beside [UkSh.v] or [UShKernel.v], where the class is abstract           *)
(* (SH-LINE 2b phase 1's finding).                                        *)
(*                                                                        *)
(*  S1  THE FAMILY.  read's deposit and read's post are read at the SAME   *)
(*      [UexecSG.sfam], so a program that wants to be told something about *)
(*      its window has to NAME the family it deposited.  [xfam_rd] is      *)
(*      [UexecExecInst.xfam]'s point at two fields: the process's own exit *)
(*      payload ([kf_xpay], which [UkRun.udepwf_std]'s pure row demands)   *)
(*      and [rf_ret] -- WHAT THE CALLER ASKS TO BE TOLD.                   *)
(*                                                                        *)
(*  S2/S3  THE ACCESS LEMMA AND THE DISCHARGE ARE GONE (lane ECHO-OUT    *)
(*      part 5).  [ush_read_sup] built read(5)'s console deposit out of    *)
(*      the reader lease and the boundary's INPUT LICENCE, and             *)
(*      [ush_read_recv_leaf_holds] discharged [UkSh.ush_read_recv_leaf]    *)
(*      from the two.  At the echo application's REAL input claim          *)
(*      ([EchoOut.ein]) the flat [WpUart.in_licence] is FALSE -- the       *)
(*      claim's non-taint arms pin the delivered sequence and its count,   *)
(*      so moving [dl] needs the READER's half of [EchoOut.dl_cnt], which  *)
(*      the lease does not carry yet.  The leaf is therefore OWED, at the  *)
(*      statement [ush_read_recv_leaf_holds] used to prove, from           *)
(*      [UInitBootAdequacy]'s [Hsh_owed] through                           *)
(*      [UInitBoot.echo_Hinit_boot]; lane IO-LEAF pays it.  Section S2     *)
(*      below carries the full argument.                                   *)
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
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes ObsTrace.
Require Import RegFile.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required --
   naming a class without its defining module in scope introduces a FRESH
   Type variable and the kernel's [uexecSG] instance becomes invisible to
   resolution ([UInitSh.v]'s header). *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.           (* [perm_of] / [lazy_free] *)
Require Import ProcPtOwn.          (* [uptd] / [ud_um] / [proc_pt_wf] *)
Require Import UserPtTree.         (* [uva_wmapped] *)
Require Import UserCwd UserChildren.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import VcGen.              (* [trunc32] *)
Require Import PieceFam.
Require Import FsTree.
Require Import ChildTok.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import SpecArgfd.          (* [fd_st_of_key] *)
Require Import SpecFileread.       (* [fileread_in] / [console_receipt] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import AppCfg AppInv.      (* [app_sup] *)
Require Import FsCfg.
Require Import FsAbsDefs.
Require Import ConsoleInv.         (* [cons_acc] / [cons_out] / [CONSOLE] *)
Require Import WpUart.             (* [cons_read_pay]: E5's console I/O
                                      boundary (lane CONS-IO) *)
Require Import UartNames.          (* [cons_names] *)
Require Import UserConsole.        (* [upos] / [ucons_pay] *)
Require Import UkSh.               (* [ush_narrow_count_le] *)
Require Import UConsLine.          (* [ush_read_recv_leaf] / [ush_std_cons] *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section UShLine.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s header): no local
     [Context {SG}] / [Context {PS}], and NO separate [uartGhostG] either
     -- [Xv6G.xv6_uart] is the one path from the bundle to the console
     ring's cameras, and it is what makes the program's spelling of the
     reader token and the ring's own ONE proposition
     ([UserConsole.ucons_reader_eq]). *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  S1  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* [UexecExecInst.xfam] at the two fields read's rows look at, and the
     trivial ones everywhere else: a deposit is read at ONE number
     ([UexecExecInst.xv6_sbundle] is a match on it), so the rest of the
     record is inert.  [UInitConsK.xfam_mknod] is the mold. *)
  Definition xfam_rd (Q : Z -> iProp Σ) (Rd : nat -> nat -> iProp Σ) : xfam :=
    {| xf_P     := fun _ _ => True%I;
       xf_Pmiss := fun _ _ => True%I;
       xf_Fo    := pfam_triv (fun _ _ _ => True%I);
       xf_Rs    := True%I;
       rf_F     := pfam_triv (fun _ _ _ _ => True%I);
       cf_P     := fun _ _ => True%I;
       cf_Pmiss := fun _ _ => True%I;
       cf_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_P     := fun _ _ => True%I;
       of_Pmiss := fun _ _ => True%I;
       of_Farm  := pfam_triv (fun _ _ => True%I);
       of_Fun   := pfam_triv (fun _ _ => True%I);
       of_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       of_Fo    := pfam_triv (fun _ _ _ => True%I);
       of_Ft    := pfam_triv (fun _ _ _ => True%I);
       wf_Q     := fun _ => True%I;
       nf_P     := fun _ _ => True%I;
       nf_Pmiss := fun _ _ => True%I;
       nf_Farm  := pfam_triv (fun _ _ => True%I);
       nf_Fun   := pfam_triv (fun _ _ => True%I);
       nf_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       nf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_P     := fun _ _ => True%I;
       uf_Pmiss := fun _ _ => True%I;
       uf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       uf_Ftgt  := pfam_triv (fun _ _ => True%I);
       uf_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       uf_Fmiss := pfam_triv (fun _ _ _ => True%I);
       lf_Ftgt  := pfam_triv (fun _ _ _ => True%I);
       lf_Fent  := pfam_triv (fun _ _ _ _ => True%I);
       lf_Funt  := pfam_triv (fun _ _ => True%I);
       df_P     := fun _ _ => True%I;
       df_Pmiss := fun _ _ => True%I;
       df_Farm  := pfam_triv (fun _ _ => True%I);
       df_Fdots := pfam_triv (fun _ _ _ _ => True%I);
       df_Fun   := pfam_triv (fun _ _ => True%I);
       df_Fok   := pfam_triv (fun _ _ _ _ => True%I);
       df_Fex   := pfam_triv (fun _ _ _ _ => True%I);
       kf_pay   := fun _ => True%I;
       (* a program that forks lends nothing at this record (lane
          FORK-REFUND): [UexecSG.sfork_lend] is [emp]. *)
       kf_lend  := emp%I;
       kf_xpay  := Q;
       rf_ret   := Rd;
       (* sh says nothing about the input's boundary account yet: the real
          [read_link] arrives with SH-LINE R2/R3 (lane CONS-IO, milestone
          B, and the coordinator's ruling (5)). *)
       rf_in    := fun _ => True%I |}.

  (* WHAT SH ASKS TO BE TOLD.  A lease holder's choice: the window it was
     handed begins at ITS OWN position and its half of the pair comes back
     at the new one -- or the ring's marker moved behind its back
     ([ConsoleInv.cons_out]'s second disjunct), which for a constraining
     application is the taint, and then the number means nothing any more.
     THE TWO DISJUNCTS ARE NOT THE CALLER'S CHOICE: which one it gets is
     decided by whether a tokenless reader popped while the call slept. *)
  Definition ush_rd_ret (γp : gname) (T : iProp Σ) (n : nat)
      : nat -> nat -> iProp Σ :=
    (* ...AND THE LEASE COMES BACK WITH THE POSITION (lane KILL-PAY,
       K4(a)).  The reader token no longer rides in the run's payload row
       -- that row is a WAND from the kill credential now -- so it goes
       down into the call in the program's own hand and comes back here.
       The TAINTED arm hands back only the position:
       [UserConsole.ucons_pay_taint] rebuilds the payload from [T]. *)
    fun cur dc =>
      ((⌜cur = n⌝ ∗ upos γp (n + dc)%nat
          ∗ ucons_pay fsc_cons γp T (-1))
       ∨ (T ∗ ∃ n' : nat, upos γp n'))%I.

  (* AT THE CLASS'S OWN FAMILY TYPE, not at [xfam] ([UConsOpen.v]'s note):
     the ecall leaves take [UexecSG.sfam], and an [xfam]-typed argument is
     checked before the instance evar is resolved and so does not
     convert. *)
  Definition ush_read_fam (γp : gname) (T : iProp Σ) (n : nat)
      (Q : Z -> iProp Σ) : sfam :=
    xfam_rd Q (ush_rd_ret γp T n).

  (* =================================================================== *)
  (*  S1b  THE TWO KEY-LEVEL ROWS, IN THE PROCESS'S DIRECTION             *)
  (*                                                                      *)
  (*  [UexecExecInst] states the deposit's ELIM and the post's INTRO --    *)
  (*  the DISPATCHER's two directions.  A process needs the other two, at  *)
  (*  readings it can name, so each takes the key's own projections as     *)
  (*  pure premises.  [UConsOpen]'s two are the mold; the proofs are the   *)
  (*  same three lines, the match at one literal.                          *)
  (* =================================================================== *)
  Local Ltac xv6_skip :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [Hc | _]; [ exfalso; by vm_compute in Hc | ]
    end.
  Local Ltac xv6_take :=
    match goal with
    | |- context [ @decide (?a = ?b) _ ] =>
        let Hc := fresh "Hc" in
        destruct (decide (a = b)) as [_ | Hc]; [ | exfalso; by apply Hc ]
    end.

  Lemma sbundle_at_read_intro_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 : mword 64) (sts : list fdstate) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 -> uvis_fd W = sts ->
    fileread_in (fd_st_of_key v0 sts) (rf_F f) (rf_ret f) (rf_in f) True%I -∗
    sbundle_at X USYS_read f W.
  Proof.
    intros H0 Hfd. iIntros "H".
    (* the REWRITE GOES FIRST, against the lemma's own variables
       ([UConsOpen.sbundle_at_open_intro_at]'s note) *)
    rewrite -H0 -Hfd.
    rewrite /sbundle_at /= /xv6_sbundle /xk_a.
    xv6_skip. xv6_take. iExact "H".
  Qed.

  Lemma spost_at_read_elim_at (X : uvis -d> iPropO Σ) (f : xfam) (W : uvis)
      (v0 v1 v2 : mword 64) (sts : list fdstate)
      (r : mword 64) (M' : gmap Z (bv 8)) (fdv' : list fdstate)
      (cw' : Z) (cs' : gset gname) :
    tf_w (uvis_tf W) (tf_arg_idx 0) = v0 ->
    tf_w (uvis_tf W) (tf_arg_idx 1) = v1 ->
    tf_w (uvis_tf W) (tf_arg_idx 2) = v2 ->
    uvis_fd W = sts ->
    spost_at X USYS_read f W r M' fdv' cw' cs' -∗
    (* THE ANSWER'S RANGE COMES OUT WITH THE RECEIPT (lane CONS-ROWS, B3):
       row 5 carries [SpecFileread.fileread_ret] at the key's own count, and
       a process that has not tied [r] to its request can spend neither of
       the receipt's control-flow rows. *)
    ⌜fileread_ret (sys_rw_count v2) r⌝ ∗
    ∃ P : uptd,
      ⌜perm_of (ud_um P) (uvis_sz W) = uvis_perm W⌝ ∗
      ⌜proc_pt_wf P⌝ ∗
      ⌜uvis_lazy W = false -> lazy_free (ud_um P) (uvis_sz W)⌝ ∗
      fileread_extra_core (uvis_gen W) P (fd_st_of_key v0 sts) (sys_rw_count v2)
        (rf_F f) (rf_ret f) (rf_in f) r M' v1.
  Proof.
    intros H0 H1 H2 Hfd. iIntros "H".
    rewrite -H0 -H1 -H2 -Hfd.
    rewrite /spost_at /= /xv6_spost /xk_a.
    xv6_take. iExact "H".
  Qed.

  (* THE DESCRIPTOR THE CALL RAN ON, out of the caller's own ledger: the
     arm [SpecFileread.fileread_in] takes is selected by the KEY's table,
     and what a program holds is the low [NSTD] slots of it. *)
  Lemma ush_fd_st_console (v0 : mword 64) (fdv l : list fdstate) (wr : bool) :
    bv_signed (trunc32 v0) = 0 ->
    take NSTD fdv = l ->
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    fd_st_of_key v0 fdv = FdOpen true wr (FdDevice CONSOLE).
  Proof.
    intros H0 Htake Hl0. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= 0 < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; unfold NOFILE; lia ].
    rewrite <- Htake in Hl0.
    rewrite lookup_take in Hl0; [ | unfold NSTD; lia ].
    change (Z.to_nat 0) with 0%nat. rewrite Hl0. reflexivity.
  Qed.

  (* =================================================================== *)
  (*  S2  THE ACCESS LEMMA IS GONE (lane ECHO-OUT part 5).                *)
  (*                                                                      *)
  (*  [ush_read_sup] built read(5)'s CONSOLE deposit out of the reader     *)
  (*  lease and the boundary's INPUT LICENCE, and [ush_read_recv_leaf_     *)
  (*  holds] below it discharged [UkSh.ush_read_recv_leaf] from the two.   *)
  (*  BOTH ARE DELETED, and the reason is that the second half of that     *)
  (*  payment stopped being free.  [SpecFileread.fileread_in]'s console    *)
  (*  arm is [ConsoleInv.cons_acc … ∗ WpUart.cons_read_pay (S gen_id)      *)
  (*  Rin]: the ring's own payment, which the lease pays, BESIDE the       *)
  (*  application's delivered-sequence link.  While the application's      *)
  (*  input claim was [emp] the link was free ([WpUart.in_licence] at      *)
  (*  [RiscvPtsto.in_res_triv]) and this file took that licence as a       *)
  (*  Coq-level premise; at the echo application's REAL claim              *)
  (*  ([EchoOut.ein]) the flat licence is FALSE -- the claim's two         *)
  (*  non-taint arms carry [⌜(dl ++ ws) `prefix_of` echoed pops⌝] and the  *)
  (*  delivered count [EchoOut.dl_cnt v (1/2) (length dl)], so an          *)
  (*  arbitrary window is refuted and moving [dl] at all needs the         *)
  (*  READER's other half of that ghost.  Only the taint arm is free,      *)
  (*  which is exactly what [App.Happ_in_sup] says, and the payload's      *)
  (*  LEASE arm ([UserConsole.ucons_pay]) carries no taint.                *)
  (*                                                                      *)
  (*  SO THE LEAF IS OWED, NOT PROVED: it is a Coq-level premise of        *)
  (*  [UInitBoot.echo_Hinit_boot] and the third conjunct of                *)
  (*  [UInitBootAdequacy]'s [Hsh_owed], on [UkSh.sh_deps]'s mould, and     *)
  (*  lane IO-LEAF discharges it -- it puts [EchoOut.era_pin] and the      *)
  (*  reader's [dl_cnt] half on sh's lease and runs the leaf through       *)
  (*  [EchoOut.echo_read_link], whose [WpUart.read_link] hands over        *)
  (*  [⌜ConsLog.read_ok pops dl ws⌝].                                      *)
  (*  WHAT SURVIVES HERE is everything that never touched the licence:     *)
  (*  the read family, the two [sbundle] adapters, the two [fd_st]         *)
  (*  readings, [ush_count_is_cap], and the SHUT arm's deposit             *)
  (*  ([ush_read_sup_closed]).                                            *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  S3  THE DISCHARGE (header)                                          *)
  (* =================================================================== *)
  (* THE KERNEL'S COUNT IS THE CALLER'S REQUEST (lane CONS-ROWS).  The
     trapframe's argument 2 reaches file.c as a 32-bit INT
     ([SpecSysRead.sys_rw_count]) while the leaf names the request as a
     [nat] read off the same word unsigned; the two agree exactly below the
     sign boundary, which is [UConsLine.ush_read_recv_leaf]'s
     [Z.of_nat cap < 2 ^ 31] premise.  Above it the kernel really is
     answering a different request, so this is a bridge and not a
     formality. *)
  Lemma ush_count_is_cap (w : mword 64) (cap : nat) :
    uint w = Z.of_nat cap -> (Z.of_nat cap < 2 ^ 31)%Z ->
    sys_rw_count w = Z.of_nat cap.
  Proof.
    intros Hu Hlt. rewrite uint_unsigned in Hu.
    change (2 ^ 31)%Z with 2147483648%Z in Hlt.
    rewrite /sys_rw_count. unfold bv_signed.
    rewrite trunc32_subrange subrange_31_0_unsigned Hu.
    rewrite (Z.mod_small (Z.of_nat cap) 4294967296); [| lia].
    assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
    rewrite bv_swrap_small; [ reflexivity | rewrite Hhm; lia ].
  Qed.
  (* THE DESCRIPTOR THE CALL RAN ON, at the row's OTHER arm: a SHUT fd 0.
     [SpecFileread.fileread_in]'s [FdClosed] arm asks for nothing and
     [fileread_extra_core]'s says [r = -1] (lane CLOSED-READ) -- so the
     shell's read leaf answers on both arms of [UkSh.ush_fd0p] and [gets]
     does not have to case split on which table it was handed. *)
  Lemma ush_fd_st_closed (v0 : mword 64) (fdv l : list fdstate) :
    bv_signed (trunc32 v0) = 0 ->
    take NSTD fdv = l ->
    l !! 0%nat = Some FdClosed ->
    fd_st_of_key v0 fdv = FdClosed.
  Proof.
    intros H0 Htake Hl0. rewrite /fd_st_of_key H0.
    destruct (decide (0 <= 0 < Z.of_nat NOFILE)) as [_ | Hc];
      [ | exfalso; apply Hc; unfold NOFILE; lia ].
    rewrite <- Htake in Hl0.
    rewrite lookup_take in Hl0; [ | unfold NSTD; lia ].
    change (Z.to_nat 0) with 0%nat. rewrite Hl0. reflexivity.
  Qed.

  (* ...AND THE SUPPLY AT THAT ARM, which costs nothing at all: the shut
     descriptor's bundle is [P -∗ P], so the call spends no token and the
     caller keeps the position it came in with. *)
  Lemma ush_read_sup_closed (N : uk_names Σ) (γp : gname) (T : iProp Σ)
      (m : regfile) (pc : mword 64) (l : list fdstate) (n : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    l !! 0%nat = Some FdClosed ->
    ⊢ udepwf_std N m pc USYS_read (ush_read_fam γp T n (ukn_pay N)) l.
  Proof.
    intros Ha0 Hl0.
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro_at uslot
              (ush_read_fam γp T n (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              (m !!! Regidx a0_idx) fdv
              (tf_of_arg0 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false)).
    rewrite (ush_fd_st_closed (m !!! Regidx a0_idx) fdv l Ha0 Htake Hl0).
    rewrite /fileread_in. iIntros "HP". iExact "HP".
  Qed.

  (* =================================================================== *)
  (*  THE DISCHARGE OF [UkSh.ush_read_leaf] IS GONE TOO -- see S2 above.   *)
  (*  [ush_read_recv_leaf_holds] WAS that proof, and its console arm ran   *)
  (*  on [ush_read_sup]; both went with the licence.  The statement it     *)
  (*  proved is now OWED, verbatim:                                       *)
  (*                                                                      *)
  (*    forall (γp : gname) (N : uk_names Σ) (l : list fdstate),           *)
  (*      ukn_pay N = ucons_pay FsCfg.fsc_cons γp T ->                     *)
  (*      ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp T            *)
  (*          FsCfg.fsc_cons l                                            *)
  (*                                                                      *)
  (*  which is [UInitSh.init_cons_sup_of_sh_slot]'s own premise, threaded  *)
  (*  from [UInitBootAdequacy]'s [Hsh_owed] through                        *)
  (*  [UInitBoot.echo_Hinit_boot].                                        *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  S4  R3'S TARGET, AND THE ONE THING STILL BETWEEN IT AND A LEMMA.    *)
  (*                                                                      *)
  (*  What the top theorem still names is                                 *)
  (*                                                                      *)
  (*    Hsh_owed ... -> ... /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)      *)
  (*                                                                      *)
  (*  and [UInitSh.sh_pay_rest Rsh] is                                    *)
  (*                                                                      *)
  (*    ∀ (γp : gname) (N : uk_names Σ),                                  *)
  (*      UkSh.ush_rest (PS := uprogSG_free) N γp                         *)
  (*        (Rsh (ukn_t N) (ukn_d N) (ukn_s N))                           *)
  (*                                                                      *)
  (*  THE [Rsh] SH'S STATE FIXES is [UInitSh.sh_Rsh] (lane SH-STATE,       *)
  (*  LANDED).  [UInitSh.sh_pay_state] produces it out of [usz γs           *)
  (*  (uvis_sz W')] and the writable data below the frame, and what a turn  *)
  (*  of the command loop carries is [UkShLoop.ushl_R N sz] -- so           *)
  (*                                                                      *)
  (*    sh_Rsh := fun _ γd γs => UkShLoop.ushl_dat γd ∗                     *)
  (*                usz γs (kexec_sz ElfUser.sh_elf)                        *)
  (*                                                                      *)
  (*  -- the break at a CONSTANT, not under an existential: the wand's key  *)
  (*  premise [UShKernel.sh_pay_key] pins [uvis_sz W' = kexec_sz sh_elf],   *)
  (*  so the three bounds [UkShFork.ushf_rest_of_body] asks of it           *)
  (*  ([8344 <= sz], [pgroundup sz = sz], [usz_ok (sz + 65536)]) are CLOSED *)
  (*  computations at [0x5000] and R3 has strictly less to do.             *)
  (*                                                                      *)
  (*  THE RECORD'S OWN THREE ARE NO LONGER IN THE WAY (lane SH-LINE 2b,    *)
  (*  (b), LANDED).  [UkSh.ush_rest] takes [⌜ukn_const N⌝], [shk_code γt]  *)
  (*  and [UkSh.ush_jtab γt] inside its own [□], [wp_ksh_loop] pays them   *)
  (*  down the chain, and [UShKernel.sh_uexec_slot] pays them at the entry *)
  (*  off the key's text ([UkSh.ush_jtab_of_rodata] is the new step).  So  *)
  (*  a [∀] over every record is provable now, which it was not.           *)
  (*                                                                      *)
  (*  WHAT STAYS NAMED, and who owns it:                                  *)
  (*      [UkSh.sh_deps]                 -- [Hsh_owed]'s own conjunct,     *)
  (*                                        write(16), E5's.               *)
  (*      (nothing for the allocator: lane SELF-KILL's step 5 gave the     *)
  (*       malloc contract its failure arm and deleted                      *)
  (*       [ushm_sbrk_never_fails]; what is left there is the Coq-level     *)
  (*       [⊢ UkRun.ukn_pay N (-1)], free at the forked child's record.)    *)
  (*      [UkRun.uxsup] / E4's pinned [UkShEcho.sh_exec_sup_echo]          *)
  (*                                     -- the exec supply, built from    *)
  (*                                        the application invariant and  *)
  (*                                        /echo's pin at                 *)
  (*                                        [echo_Hinit_boot].             *)
  (*      [UkSh.ush_gen_slot N T]        -- E2's, off                      *)
  (*                                        [AppEcho.echo_sup_of_taint].   *)
  (*      [UkShLoop.ush_line_lexable]    -- discharged in tree by E4's     *)
  (*                                        [UkShEcho.ush_line_toks_holds] *)
  (*                                        and composed away by R3.       *)
  (*                                                                      *)
  (*  So R3's lemma reads                                                 *)
  (*                                                                      *)
  (*    Lemma sh_rest_holds                                               *)
  (*        (T : iProp Σ) `{!Persistent T} :                              *)
  (*      (⊢ UkSh.sh_deps (PS := uprogSG_free)) ->                        *)
  (*      (∀ N, ⊢ UkSh.ush_gen_slot (PS := uprogSG_free) N T) ->           *)
  (*      (∀ N, ⊢ UkRun.uxsup (PS := uprogSG_free)) ->                     *)
  (*      ⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh                            *)
  (*                                                                      *)
  (*  IT IS STILL NOT IN THE TREE, and what is left is R2 and only R2:     *)
  (*  [ushf_rest_of_body] proves [UkSh.ush_rest_l], the obligation WITH    *)
  (*  the line fact in it, and [sh_pay_rest] names [UkSh.ush_rest], the    *)
  (*  one without.  [ush_rest_l_of_rest] goes the wrong way.  The rename   *)
  (*  R2 ends with -- [ush_rest] deleted, [ush_rest_l] renamed to it -- is *)
  (*  what lines the two up, and it needs [wp_ksh_getcmd] to PRODUCE       *)
  (*  [ush_rest_line], which is R2's proof.                                *)
  (*                                                                      *)
  (*  WHAT R2'S PROOF IS STILL MISSING, precisely (reported, not invented  *)
  (*  here).  The producer half is buildable from what is landed: the      *)
  (*  read's answer ([UkSh.ush_read_ans]) hands back a one-byte window at  *)
  (*  the caller's own cursor with its tag, B1 pins [dc = dd] on the       *)
  (*  [r = 1] round and B4 sends the [r = 0] round to                      *)
  (*  [UkSh.ush_swallow_taint], so [UkSh.ush_gets_line] accumulates.  The  *)
  (*  CONSUMER half does not close, and two ingredients are why:           *)
  (*                                                                      *)
  (*    THE LINE BOUNDARY.  [UkSh.ush_line_is] needs the window to be      *)
  (*    [echo_line] AT INDEX 0, and what the discipline gives is           *)
  (*    "[ins h] is a prefix of [echo_line]*" for the whole cycle.  The    *)
  (*    step between them is [UConsLine.ush_disc_line_seg], whose premise  *)
  (*    is [ins h = concat (replicate q echo_line) ++ bs] -- i.e. that the *)
  (*    input BEFORE this gets is a whole number of lines.  Nothing in the *)
  (*    command loop carries that.  It is true (sh's previous [gets]       *)
  (*    stopped at '\n') and it is an INVARIANT of the loop, so what it    *)
  (*    wants is a conjunct of [UkSh.ush_pos] -- a persistent              *)
  (*    [ucons_stored_lb] at the cursor's own length whose bytes are       *)
  (*    [concat (replicate q echo_line)], or the taint -- established at   *)
  (*    init's mint ([UserConsole.upos_alloc], position 0) and preserved   *)
  (*    by a [gets] that ended at '\n'.  Stating it is a design step and   *)
  (*    it is the coordinator's.                                           *)
  (*                                                                      *)
  (*    THE STORED SEQUENCE IS NOT THE INPUT SEQUENCE.  [cons_window]      *)
  (*    speaks of the ring's COMMITTED bytes and [disc_seg] of the input;  *)
  (*    they agree only where nothing was dropped, which is the rate       *)
  (*    discipline's no-overflow argument -- E5's, and this file's own §4  *)
  (*    header already says so.                                            *)
  (*                                                                      *)
  (*    AND THE MINUS-ONE ARM.  A read that answers -1 (killed, or fd 0    *)
  (*    shut) pays neither a window nor the taint, so a [gets] that took   *)
  (*    it can offer [UkSh.ush_rest_line] on neither arm.  Under the       *)
  (*    discipline it cannot happen and lane KILL-PAY will hand the arm    *)
  (*    [□ riscv_kill_cred] -- which for echo IS the taint -- and then it  *)
  (*    goes generic like any other.  Until then it is a third arm.        *)
  (* =================================================================== *)

End UShLine.
