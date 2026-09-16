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
(*      [UInitBoot.echo_Hinit_boot]; lane IO-LEAF pays it (S5-S7 below).   *)
(*      Section S2 below carries the full argument.                        *)
(*                                                                        *)
(*  S5/S6/S7  THE READ SIDE ON THE ERA'S OWN LINK, AND THE LEAF PAID     *)
(*      (lane IO-LEAF, M5).  S5 rebuilds the access lemma at              *)
(*      [EchoLinks.echo_link_rd]: the console deposit's boundary half is  *)
(*      the era's read link at sh's own delivered count now, not the      *)
(*      licence, and the credential it spends comes off SH'S OWN LEASE    *)
(*      ([UserConsole.ucons_pay]'s [Rd], under the same existential as    *)
(*      the cursor).  It also proves the bridge the survey called for:    *)
(*      the byte the call delivered IS [EchoDisc.echo_line] at sh's own   *)
(*      count.  S6 is the LEAF on that deposit, at an answer that carries *)
(*      the era's facts beside the ring's, with the [-1] arm refuted at   *)
(*      the console descriptor by TRAP-ROWS T2.  S7 is the OWED           *)
(*      statement, [ush_read_recv_leaf_holds], discharged -- so the S2/S3 *)
(*      note above is history and [UInitBootAdequacy]'s [Hsh_owed] has    *)
(*      two conjuncts.                                                    *)
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
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UkReadRows.         (* the read leaf's SHARED key-level rows:
                                      [xfam_rd], the intro/elim pair, the two
                                      [fd_st_of_key] readings, the count *)
Require Import UkReadCons.         (* THE NEUTRAL CONSOLE MEMBER of the read
                                      leaf -- this file's leaf is its echo
                                      INSTANCE (lane RD-4) *)
Require Import SpecArgfd.          (* [fd_st_of_key] *)
Require Import SpecFileread.       (* [fileread_in] / [console_receipt] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import AppInv.      (* [app_sup] *)
Require Import FsCfg.
Require Import ConsoleInv.         (* [cons_acc] / [cons_out] / [CONSOLE] *)
Require Import WpUart.             (* [cons_read_pay]: E5's console I/O
                                      boundary (lane CONS-IO) *)
Require Import UartNames.          (* [cons_names] *)
Require Import UserConsole.        (* [upos] / [ucons_pay] *)
Require Import UkSh.               (* [ush_narrow_count_le] *)
Require UkInit.                    (* [init_rd]: the exit family, the pair *)
(* THE ERA'S READ SIDE (lane IO-LEAF, M5).  [EchoOut] is the application's
   CLAIM and [EchoLinks] the program-side law built on it; this file names
   neither the boot record nor its four equations -- the law arrives as a
   premise, exactly as [UkSh.sh_deps] does.  [EchoOut] requires nothing
   above [SpecConsoleintr], so there is no cycle with the U tier. *)
Require Import LogEntryDefs.            (* [log_entry] / [read_ok] *)
Require Import EchoDisc.           (* [echo_line] *)
Require Import EchoOutPure.        (* [E_byte] / [echoed] *)
Require Import EchoOut.            (* [era_pin] / [dl_cnt] / [read_ret] *)
Require Import EchoLinksLine.      (* [ewc_lcred]: the loop's tight family (step 4) *)
Require Import EchoLinks.          (* [echo_links] and its two read
                                      projections *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  THE RING'S TRANSLATION IS THE IDENTITY ON THE LINE (lane IO-LEAF, M5) *)
(*                                                                       *)
(*  What a program reads out of its buffer is [ConsoleInv.cons_xlate] of  *)
(*  the byte the ring stored ([ConsoleInv.cons_window]'s last clause),    *)
(*  and what the era's input claim places in [EchoDisc.echo_line] is the  *)
(*  STORED byte ([EchoOut.ein_read_byte]).  The two are the same byte     *)
(*  exactly because the line carries no carriage return -- 0x0d is the    *)
(*  one byte [cons_xlate] moves, and the seventeen of [echo_line] are     *)
(*  "echo hello world\n".  A closed computation, in the [forallb]-over-   *)
(*  [seq] shape [UkSh.ush_jrow_bytes] uses.                               *)
(* ===================================================================== *)
Lemma echo_line_no_cr (i : nat) :
  (i < length echo_line)%nat ->
  cons_xlate (echo_line !!! i) = echo_line !!! i.
Proof.
  intro Hi. pose proof (echo_line_byte_val_at i Hi) as Hv.
  rewrite /cons_xlate. rewrite decide_False; [reflexivity |].
  intro Hq. apply (f_equal bv_unsigned) in Hq.
  rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
    [lia | by vm_compute].
Qed.

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
  (* the era's own cameras (lane IO-LEAF, M5).  A NARROW class beside the
     bundle, on [UShOut.v]'s and [UInitBanner.v]'s context list: the
     application's ghosts are not [Xv6G.xv6G]'s and binding a second copy
     of a bundle class is what makes the kernel's instance invisible. *)
  Context `{!echoOutG Σ}.

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
  (* [Rin] IS A PARAMETER NOW (lane IO-LEAF, M5): read's console deposit
     carries [WpUart.cons_read_pay (S gen_id) (rf_in f)] beside the ring's
     own payment, and what sh asks to be told about the window it CONSUMED
     is the era's [EchoOut.read_ret] -- not [True], which was only ever
     payable while the application's input claim was [emp]. *)
  (* [xfam_rd] MOVED to [UkReadRows.v] (lane RD-4), beside its inode twin
     [xfam_rdf]: the two ARE the two arms of the read leaf, and neither file
     that needed one could see the other. *)

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
       [UserConsole.ucons_pay_taint] rebuilds the payload from [T].
       ...AND IT COMES BACK IN PIECES, not as [UserConsole.ucons_pay]
       (lane IO-LEAF, M5).  The payload's left arm now carries the
       application's own per-position credential beside the token
       ([ucons_pay]'s [Rd]), and THAT credential is what the BOUNDARY half
       of the deposit returns -- in the receipt, not here.  The two halves
       of read's console arm fire independently, so the lease can only be
       reassembled where both answers are in hand, which is the leaf. *)
    fun cur dc =>
      ((⌜cur = n⌝ ∗ upos γp (n + dc)%nat
          ∗ ucons_reader fsc_cons (n + dc)%nat ∗ upos_a γp (n + dc)%nat)
       ∨ (T ∗ ∃ n' : nat, upos γp n'))%I.

  (* AT THE CLASS'S OWN FAMILY TYPE, not at [xfam] ([UConsOpen.v]'s note):
     the ecall leaves take [UexecSG.sfam], and an [xfam]-typed argument is
     checked before the instance evar is resolved and so does not
     convert. *)
  Definition ush_read_fam_at (γp : gname) (T : iProp Σ) (n : nat)
      (Rin : list (list mobs * bv 8) -> iProp Σ) (Q : Z -> iProp Σ) : sfam :=
    xfam_rd Q (ush_rd_ret γp T n) Rin.

  Definition ush_read_fam (γp : gname) (T : iProp Σ) (n : nat)
      (Q : Z -> iProp Σ) : sfam :=
    ush_read_fam_at γp T n (fun _ => True%I) Q.

  (* =================================================================== *)
  (*  S1b  THE TWO KEY-LEVEL ROWS MOVED (lane RD-4)                       *)
  (*                                                                      *)
  (*  [sbundle_at_read_intro_at] / [spost_at_read_elim_at] were this       *)
  (*  file's copies of the deposit's INTRO and the post's ELIM in the      *)
  (*  process's direction; [UkReadFile.v] carried the same two lemmas word *)
  (*  for word, because neither arm's file could see the other's.  They    *)
  (*  are one pair now, [UkReadRows.sbundle_at_read_intro] /               *)
  (*  [UkReadRows.spost_at_read_elim], and they say nothing about the      *)
  (*  descriptor -- which is exactly why there was only ever one of them.  *)
  (* =================================================================== *)

  (* THE DESCRIPTOR THE CALL RAN ON, out of the caller's own ledger: the
     arm [SpecFileread.fileread_in] takes is selected by the KEY's table,
     and what a program holds is the low [NSTD] slots of it. *)
  Lemma ush_fd_st_console (v0 : mword 64) (fdv l : list fdstate) (wr : bool) :
    bv_signed (trunc32 v0) = 0 ->
    take NSTD fdv = l ->
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    fd_st_of_key v0 fdv = FdOpen true wr (FdDevice CONSOLE).
  Proof.
    intros H0 Htake Hl0.
    exact (std_fd_st_of_key v0 fdv l 0%nat _ H0 ltac:(unfold NSTD; lia)
             Htake Hl0).
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
  Proof. exact (uread_count_is_cap w cap). Qed.
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
    intros H0 Htake Hl0.
    exact (std_fd_st_of_key v0 fdv l 0%nat _ H0 ltac:(unfold NSTD; lia)
             Htake Hl0).
  Qed.

  (* ...AND THE SUPPLY AT THAT ARM, which costs nothing at all: the shut
     descriptor's bundle is [P -∗ P], so the call spends no token and the
     caller keeps the position it came in with. *)
  (* AT ANY [Rin] (lane IO-LEAF, M5): the shut descriptor's arm of
     [SpecFileread.fileread_in] is [P -∗ P] and reads no boundary link at
     all, so the closed arm of the leaf costs the same whether the caller
     asked to be told about its window or not. *)
  Lemma ush_read_sup_closed (N : uk_names Σ) (γp : gname) (T : iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ)
      (m : regfile) (pc : mword 64) (l : list fdstate) (n : nat) :
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    l !! 0%nat = Some FdClosed ->
    ⊢ udepwf_std N m pc USYS_read
        (ush_read_fam_at γp T n Rin (ukn_pay N)) l.
  Proof.
    intros Ha0 Hl0.
    rewrite /udepwf_std. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Htake #Hmpay Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro uslot
              (ush_read_fam_at γp T n Rin (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              (m !!! Regidx a0_idx) fdv
              (tf_of_arg0 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false)).
    rewrite (ush_fd_st_closed (m !!! Regidx a0_idx) fdv l Ha0 Htake Hl0).
    rewrite /fileread_in. iIntros "HP". iExact "HP".
  Qed.

  (* =================================================================== *)
  (*  S5  THE ERA'S READ LINK AS SH'S DEPOSIT (lane IO-LEAF, M5)          *)
  (*                                                                     *)
  (*  S2 says why the flat input licence is FALSE at the echo             *)
  (*  application's real input claim, and what has to replace it: the     *)
  (*  READER's half of [EchoOut.dl_cnt] at sh's own cursor, spent through *)
  (*  [EchoOut.echo_read_link].  This section is the deposit, S6 the leaf *)
  (*  built on it, and the leaf IS the statement lane ECHO-OUT part 5     *)
  (*  left owed -- so [UInitBootAdequacy]'s [Hsh_owed] loses its third    *)
  (*  conjunct with it.                                                   *)
  (*                                                                     *)
  (*  WHERE THE HALF LIVES.  Not in a new conjunct of [UkSh.ush_at]: it   *)
  (*  is inside the CONSOLE LEASE the shell already carries, as the [Rd]  *)
  (*  of [UserConsole.ucons_pay], under the same existential as           *)
  (*  [upos_a].  That is the only place the era's delivered count and the *)
  (*  ring's cursor can be said to be the SAME number -- a holder of      *)
  (*  [upos γp n] pins the existential by [UserConsole.upos_agree] and    *)
  (*  reads the credential at its own [n] -- and it is what makes the     *)
  (*  credential round-trip: /init lends the lease at every fork          *)
  (*  ([uinit_lend]) and reaps it at every wait ([uinit_redeem]), so      *)
  (*  round [k > 0]'s shell is handed one exactly as round 0's is.        *)
  (* =================================================================== *)

  (* THE CREDENTIAL ITSELF -- [UserConsole.ucons_pay]'s [Rd] at the echo
     era.  The era pin is PERSISTENT and travels with the half only to
     name the era's ghosts; what is exclusive is the half. *)
  (* ...AND IT IS AT A LINE BOUNDARY (lane IO-LEAF, M5(3)).  The payload
     is what crosses between processes -- /init lends it at every fork and
     reaps it at every wait -- and what the NEXT shell needs to know about
     the count it is handed is that a LINE starts there: without it the
     first byte its [gets] takes is not the first byte of a line.  It is
     the payload and not the pieces that carries the fact, because the
     pieces are what a shell holds IN THE MIDDLE of a line, where it is
     false ([UkSh.ush_lease] is the mid-line form). *)
  (* THE READER'S RECEIPT RESIDUE (lane IO-LEAF, step 4): what the era's
     read link hands back at a window's far end, beyond the delivered
     count -- the reader's two bounds on the transcript's resolution and
     the WRITER'S cursor bound at the stream those bounds compute
     ([EchoOut.read_ret]'s trailing conjuncts, PROLOGUE-ALTS-3).  It is what
     refutes a credential that still owes the round's banner at a
     boundary the reader is past ([EchoLinks.wr_owed_read_refute]):
     [ush_wb_read_holds] below.  Persistent, so it rides the pieces and the
     lease's read side for free; at the boot it is the era's own turn at
     count 0 ([UInitBoot]). *)
  Definition rd_res (v : era_pins) (n : nat) : iProp Σ :=
    (∃ ps0 cs0 : list nat,
       ⌜rd_stage ps0 cs0 n⌝ ∗ turn_lb v (length (proc_upto ps0 cs0 n))
       ∗ ps_lb v ps0 ∗ cs_lb v cs0)%I.

  Global Instance rd_res_persistent v n : Persistent (rd_res v n).
  Proof. rewrite /rd_res. apply _. Qed.
  Global Instance rd_res_timeless v n : Timeless (rd_res v n).
  Proof. rewrite /rd_res. apply _. Qed.

  Definition ush_rd_pin (γ : echo_gn) (n : nat) : iProp Σ :=
    (⌜UkSh.ush_bnd n⌝
     ∗ ∃ v : era_pins, era_pin γ (S gen_id) v ∗ dl_cnt v (1/2) n
                       ∗ E_lb v n ∗ rd_res v n)%I.

  Global Instance ush_rd_pin_timeless γ n : Timeless (ush_rd_pin γ n).
  Proof. rewrite /ush_rd_pin. apply _. Qed.

  (* ...AND THE EXIT FAMILY (lane IO-LEAF, step 3): what sh's exit payload
     carries per count is the read side above AND the BANNER-OWED
     credential [Wb n] -- init's next round's banner is payable from it --
     which the shell reaches only at its shut-fd-0 exit with fd 2 closed.
     The right arm is AFFINE until step 4 (every other exit assembles the
     payload without a credential); it is spelled ONCE, at
     [UkInit.init_rd], and this is that family at the era's read side. *)
  Definition ush_rd_x (γ : echo_gn) (Wb : nat -> iProp Σ) (n : nat)
      : iProp Σ :=
    UkInit.init_rd (ush_rd_pin γ) Wb n.

  Global Instance ush_rd_x_timeless γ Wb n `{!Timeless (Wb n)} :
    Timeless (ush_rd_x γ Wb n).
  Proof. rewrite /ush_rd_x /UkInit.init_rd /UkInit.init_rd_cred. apply _. Qed.

  (* =================================================================== *)
  (*  THE LEASE, UNBUNDLED (lane IO-LEAF, M5(3); [UkSh]'s [Pm]).          *)
  (*                                                                     *)
  (*  Between a line's first byte and its '\n' the shell's count is at no *)
  (*  boundary, so the payload above cannot be reassembled -- what the    *)
  (*  shell holds there is its PIECES: both halves of the position pair,  *)
  (*  the ring's reader token, and the era's own half of the delivered    *)
  (*  count.  The two laws below are what [UkSh] knows about them.        *)
  (* =================================================================== *)
  (* ...AND THE WRITER'S BOUND AT THE SAME COUNT (lane IO-LEAF, M6a(3)):
     [E_lb v n] is what the era's read link hands back at a window's far
     end, and it is what the WRITE credential needs at the next line
     boundary ([EchoLinks.ewc_read]) -- so it rides with the pieces from
     the read that produced it to the boundary that spends it.  Persistent,
     so it costs the payload nothing to carry ([ush_rd_pin] has it too, at
     the boot end from [EchoOut.eturn]). *)
  Definition ush_mid (γ : echo_gn) (γp : gname) (n : nat) : iProp Σ :=
    (upos γp n ∗ upos_a γp n ∗ ucons_reader fsc_cons n
     ∗ ∃ v : era_pins, era_pin γ (S gen_id) v ∗ dl_cnt v (1/2) n
                       ∗ E_lb v n ∗ rd_res v n)%I.

  (* the payload comes apart into the pieces: the credential slot of the
     exit family is DROPPED (nothing in the loop holds it) *)
  Lemma ush_mid_of_at (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : nat -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ UkSh.ush_at N γp n -∗ UkSh.ush_lease N γp T (ush_mid γ γp) n.
  Proof.
    intro Hpay. rewrite /UkSh.ush_at /UkSh.ush_lease.
    iIntros "[Hpos Hlease]". iEval (rewrite Hpay /ucons_pay) in "Hlease".
    iDestruct "Hlease" as "[Hl | #HT]"; last first.
    { iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
      iExists n. iFrame "Hpos". rewrite Hpay.
      iApply (ucons_pay_taint with "HT"). }
    iDestruct "Hl" as (n') "(Hrd0 & Hpa & Hcred)".
    iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
    iLeft. rewrite /ush_mid. iFrame "Hpos Hpa".
    rewrite /ush_rd_x /UkInit.init_rd /UkInit.init_rd_cred. iDestruct "Hcred" as "[[_ Hcred] _]". iFrame "Hrd0 Hcred".
  Qed.

  (* ...and go back together at a boundary WITH THE BANNER-OWED
     CREDENTIAL: the exit family's own arm (its only one since lane
     EXEC-SEAM, (C)),
     which sh's shut-fd-0 exit assembles when its fd 2 was closed (step
     3; [UkSh.ush_at_of_pm_wb]'s discharge) *)
  Lemma ush_at_of_mid_wb (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : nat -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    UkSh.ush_bnd n ->
    ⊢ ush_mid γ γp n -∗ Wb n -∗ UkSh.ush_at N γp n.
  Proof.
    intros Hpay Hbnd. rewrite /ush_mid /UkSh.ush_at.
    iIntros "(Hpos & Hpa & Hrd0 & Hcred) Hb". iFrame "Hpos". rewrite Hpay.
    iApply (ucons_pay_tok fsc_cons γp T (ush_rd_x γ Wb) n (-1)
              with "Hrd0 Hpa [Hcred Hb]").
    rewrite /ush_rd_x /UkInit.init_rd /UkInit.init_rd_cred /ush_rd_pin.
    iSplitL "Hcred"; [ iSplitR; [ by iPureIntro | iExact "Hcred" ] | ].
    iExact "Hb".
  Qed.

  Lemma ush_at_of_mid_taint (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : nat -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ T -∗ ush_mid γ γp n -∗ UkSh.ush_at N γp n.
  Proof.
    intro Hpay. rewrite /ush_mid /UkSh.ush_at.
    iIntros "#HT (Hpos & _ & _ & _)". iFrame "Hpos". rewrite Hpay.
    iApply (ucons_pay_taint with "HT").
  Qed.

  (* THE WRITE CREDENTIAL'S STEP AT A READ (lane IO-LEAF, M6a(3)).  A line
     read leaves the pieces at [n + 17] carrying the writer's bound there,
     and that bound is exactly what takes the credential the prompt left
     ([EchoLinks.ewc_pr] at [2]) to the next boundary's ([0]):
     [EchoLinks.ewc_read].  The pieces come back untouched -- the bound is
     persistent -- so this is the ONE law [UkSh]'s loop needs about the
     credential beyond the prompt's own ([UkSh.ush_wc_read]). *)
  Lemma ush_mid_wc_read (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (γp : gname) (n : nat) :
    ush_mid γ γp (n + length echo_line)%nat -∗
    EchoLinks.ewc_cred T γ (S gen_id) n 2%nat -∗
    ush_mid γ γp (n + length echo_line)%nat
    ∗ EchoLinks.ewc_cred T γ (S gen_id) (n + length echo_line)%nat 0%nat.
  Proof.
    iIntros "(Hpos & Hpa & Hrd0 & Hcred) Hc".
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
    rewrite /EchoLinks.ewc_cred. iDestruct "Hc" as (v') "[#Hpin' Hc]".
    iDestruct (era_pin_agree with "Hpin Hpin'") as %<-.
    iSplitR "Hc".
    { rewrite /ush_mid. iFrame "Hpos Hpa Hrd0". iExists v. iFrame "Hpin Hdl HE Hres". }
    iExists v. iFrame "Hpin".
    iEval (cbn [EchoLinks.ewc_pr]) in "Hc". cbn [EchoLinks.ewc_pr].
    iApply (EchoLinks.ewc_read T v n with "HE Hc").
  Qed.

  (* ...AND THE SAME AT THE LOOP'S TIGHT FAMILY (step 4;
     [EchoLinksLine.ewc_lcred], what the top instantiates [Wc] at): the read
     leaves the BLOCK-OWED credential at the next boundary (index 3). *)
  Lemma ush_mid_wc_read_t (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (γp : gname) (n : nat) :
    ush_mid γ γp (n + length echo_line)%nat -∗
    EchoLinksLine.ewc_lcred T γ (S gen_id) n 2%nat -∗
    ush_mid γ γp (n + length echo_line)%nat
    ∗ EchoLinksLine.ewc_lcred T γ (S gen_id) (n + length echo_line)%nat 3%nat.
  Proof.
    iIntros "(Hpos & Hpa & Hrd0 & Hcred) Hc".
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
    iSplitR "Hc".
    { rewrite /ush_mid. iFrame "Hpos Hpa Hrd0". iExists v. iFrame "Hpin Hdl HE Hres". }
    iApply (EchoLinksLine.ewc_lcred_read T γ (S gen_id) n v with "Hpin HE Hc").
  Qed.

  (* THE DISCIPLINE LEMMA AT THE PIECES (step 4; [UkSh.ush_wb_read]'s
     discharge).  A shell whose fd 2 is closed printed no prompt, so the
     era still owes the round's banner at boundary [n]
     ([UInitBanner.kinit_ban n], spelled out here); the pieces a whole
     line's read leaves at [n + 17] carry the reader's receipt of that
     line, whose writer-cursor bound is at least the stream through the
     block the line closed -- strictly more than a banner-owed cursor at
     [n] can be ([EchoLinks.wr_owed_read_refute]).  So the credential's
     untainted arm is refuted and what is left is the taint. *)
  Lemma ush_wb_read_holds (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (γp : gname) (n : nat) :
    ush_mid γ γp (n + length echo_line)%nat -∗
    (∃ v : era_pins, era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v n 0%nat) -∗
    ush_mid γ γp (n + length echo_line)%nat ∗ T.
  Proof.
    iIntros "(Hpos & Hpa & Hrd0 & Hcred) Hb".
    iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
    iDestruct "Hb" as (v') "[#Hpin' Hb]".
    iDestruct (era_pin_agree with "Hpin Hpin'") as %<-.
    iSplitR "Hb".
    { rewrite /ush_mid. iFrame "Hpos Hpa Hrd0". iExists v. iFrame "Hpin Hdl HE Hres". }
    rewrite /EchoLinks.ewc_ban.
    iDestruct "Hb" as "[Hl | #HT]"; [ | iExact "HT" ].
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & _)".
    iDestruct "Hres" as (ps0 cs0) "(%Hrd & #Htlb & #Hps0 & #Hcs0)".
    iDestruct (turn_lb_le v (P + 0)%nat _ with "Htn Htlb") as %Hle.
    iDestruct (ps_lb_cmp v ps ps0 with "Hps Hps0") as %Hpsc.
    iDestruct (cs_lb_cmp v cs cs0 with "Hcs Hcs0") as %Hcsc.
    iExFalso. iPureIntro.
    pose proof echo_line_pos as HL.
    exact (EchoLinks.wr_owed_read_refute ps cs ps0 cs0 n P
             (n + length echo_line)%nat
             (or_introl (EchoLinks.wr_ban_pro ps cs n P Hw))
             ltac:(lia) Hrd Hpsc Hcsc ltac:(lia)).
  Qed.

  (* =================================================================== *)
  (*  THE ENTRY LAW (lane IO-LEAF, step 3).  What /init lends its child   *)
  (*  is the RAW lease -- the position's program half and the lease at    *)
  (*  the READ family alone ([ush_rd_pin], the lend family) -- beside the *)
  (*  loop's credential slot at the lent count; the exit payload is at    *)
  (*  the EXIT family ([ush_rd_x]) and is assembled by sh where it leaves. *)
  (*  The lend's token arm pins the count against the program's half     *)
  (*  ([upos_agree]) and the pieces are [ush_mid]; its taint arm is the   *)
  (*  loop's taint arm, with the payload free at the exit family.  The    *)
  (*  boundary fact rides inside [ush_rd_pin], which is what makes it     *)
  (*  round-trip through /init's restart loop.                            *)
  (* =================================================================== *)
  Lemma ush_posb_of_lend (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (N : uk_names Σ) (γp : gname) (Wc : nat -> nat -> iProp Σ)
      (Wb : nat -> iProp Σ) (l : list fdstate) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ upos γp n -∗ ucons_pay fsc_cons γp T (ush_rd_pin γ) (-1) -∗
      (* the lent slot, OR THE TAINT (lane EXEC-SEAM, (C)): /init's lend
         names the taint on its third arm, and a tainted turn is the
         cursor's own right arm *)
      (UkSh.ush_wcp Wc Wb l n 0%nat ∨ T) -∗
      UkSh.ush_posb N γp T Wc Wb (ush_mid γ γp) l 0%nat.
  Proof.
    intro Hpay. rewrite /ucons_pay.
    iIntros "Hpos Hl [Hwc | #HT]"; last first.
    { iApply (UkSh.ush_posb_taint N γp T Wc Wb (ush_mid γ γp) l 0%nat
                with "HT [Hpos]").
      rewrite /UkSh.ush_pos /UkSh.ush_at. iExists n. iFrame "Hpos".
      rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
    iDestruct "Hl" as "[Hl | #HT]"; last first.
    { iApply (UkSh.ush_posb_taint N γp T Wc Wb (ush_mid γ γp) l 0%nat
                with "HT [Hpos]").
      rewrite /UkSh.ush_pos /UkSh.ush_at. iExists n. iFrame "Hpos".
      rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
    iDestruct "Hl" as (n') "(Hrd0 & Hpa & Hcred)".
    iDestruct (upos_agree γp n n' with "Hpos Hpa") as %<-.
    iDestruct "Hcred" as "[%Hbnd Hcred]".
    iApply (UkSh.ush_posb_of_wc N γp T Wc Wb (ush_mid γ γp) l 0%nat n Hbnd
              with "[Hpos Hpa Hrd0 Hcred] Hwc").
    rewrite /ush_mid. iFrame "Hpos Hpa Hrd0 Hcred".
  Qed.

  (* WHAT SH ASKS TO BE TOLD ABOUT THE WINDOW IT CONSUMED.  [EchoOut.
     read_ret] is the era's own answer: the delivered count moved to the
     window's far end, the prefix fact, and the two index laws SH-LINE
     turns into the line.  The RIGHT disjunct is the arm an already
     TAINTED era answers on -- there the reader holds no half of the count
     and the link is free ([EchoLinks.echo_link_rd_taint]), so the answer
     can only be the taint itself.
     ONE definition and not two, because [WpUart.cons_read_pay] quantifies
     the window INSIDE: the program deposits ONE link and is told which
     window it got in the receipt. *)
  Definition ush_rd_in (T : iProp Σ) (γ : echo_gn) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((∃ v : era_pins, era_pin γ (S gen_id) v ∗ E_lb v n ∗ rd_res v n
        ∗ read_ret T (S gen_id) v n ws)
     ∨ T)%I.

  Definition ush_read_fam_era (T : iProp Σ) (γ : echo_gn) (γp : gname)
      (n : nat) (Q : Z -> iProp Σ) : sfam :=
    ush_read_fam_at γp T n (ush_rd_in T γ n) Q.

  (* =================================================================== *)
  (*  THE ACCESS LEMMA, REBUILT ON THE ERA'S LINK.                        *)
  (*                                                                     *)
  (*  Two payments, side by side, exactly as [SpecFileread.fileread_in]'s *)
  (*  console arm asks for them: the RING's ([ConsoleInv.cons_acc]), paid *)
  (*  by the reader lease sh carries, and the BOUNDARY's                  *)
  (*  ([WpUart.cons_read_pay]), which used to be bought outright from     *)
  (*  [WpUart.in_licence] and is now the era's read link at sh's own      *)
  (*  delivered count -- READ OFF THE SAME LEASE.  Both arms of the lease *)
  (*  answer both payments: the token arm pays the ring with the token    *)
  (*  and the boundary with the half beside it, and the taint arm pays    *)
  (*  the ring with [ConsoleInv.cons_dirty_cred] and the boundary with    *)
  (*  [EchoLinks.echo_link_rd_taint].                                     *)
  (* =================================================================== *)
  (* THE PAYMENT ITSELF, WITHOUT THE DEPOSIT AROUND IT (lane RD-4).  The
     neutral console member ([UkReadCons.wp_uk_ecall_read_cons]) takes the
     two payments as they stand, so what this file owes is only the era's
     answer to them; the deposit's wrapping is the member's.  BOTH ARMS OF
     THE LEASE ANSWER BOTH PAYMENTS, and they must be split ONCE: the token
     arm pays the ring with the token and the console history with the half
     beside it, the taint arm pays the ring with
     [ConsoleInv.cons_dirty_cred] and the history with
     [EchoLinks.echo_link_rd_taint]. *)
  Lemma ush_read_pay_era (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (N : uk_names Σ) (γp : gname) (n : nat) :
    (* E2's two readings of the supply *)
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    echo_links T γ -∗
    (* THE LEASE, IN THE PIECES A LINE'S MIDDLE LEAVES IT IN (lane
       IO-LEAF, M5(3)): the payload's own form asserts a LINE BOUNDARY,
       which is false between a line's first byte and its '\n'. *)
    UkSh.ush_lease N γp T (ush_mid γ γp) n -∗
    cons_acc fsc_cons app_sup (ush_rd_ret γp T n)
    ∗ cons_read_pay (S gen_id) (ush_rd_in T γ n).
  Proof.
    intros Hst Hts.
    iIntros "#Hlk HP".
    iDestruct (echo_links_rd with "Hlk") as "#Hrdl".
    iDestruct (echo_links_rd_taint with "Hlk") as "#Hrdt".
    iEval (rewrite /UkSh.ush_lease /ush_mid) in "HP".
    iDestruct "HP" as "[Hl | [#HT Hp]]".
    - (* THE LEASE HOLDER'S ARM: the token, both halves of the position
         pair, and the era's credential beside them, all at ONE number. *)
      iDestruct "Hl" as "(Hpos & Hpa & Hrd0 & Hcred)".
      iDestruct "Hcred" as (v) "(#Hpin & Hdl & #HE & #Hres)".
      iSplitR "Hdl"; last first.
      { (* THE CONSOLE HISTORY'S HALF: the era's read link at sh's own
           count, which is ONE answer to [WpUart.read_link]'s atomic
           update -- ConsLog's [EvRead] event. *)
        iIntros (ws).
        iApply ("Hrdl" $! (S gen_id) v n ws with "Hpin Hdl").
        iIntros "Hret". rewrite /ush_rd_in. iLeft. iExists v.
        iFrame "Hpin HE Hres Hret". }
      iEval (rewrite ucons_reader_eq) in "Hrd0".
      iApply (cons_acc_reader fsc_cons app_sup n with "Hrd0 [Hpos Hpa]").
      iIntros (cur dc) "Hout". rewrite /cons_out.
      iDestruct "Hout" as "[Hrd' [%Hcur | #Hdirty]]".
      + (* nobody read behind its back: the window is at its own position,
           and BOTH halves move ([upos_update]) *)
        subst cur.
        iMod (upos_update γp n (n + dc)%nat with "Hpos Hpa") as "[Hpos Hpa]".
        iModIntro. rewrite /ush_rd_ret. iLeft.
        iSplitR; [ done | ]. iFrame "Hpos Hpa".
        rewrite ucons_reader_eq. iExact "Hrd'".
      + (* a tokenless reader popped while the call slept *)
        iAssert T as "#HT"; [ iApply Hst; iExact "Hdirty" | ].
        iModIntro. iClear "Hrd'".
        rewrite /ush_rd_ret. iRight. iFrame "HT".
        iExists n. iExact "Hpos".
    - (* THE TAINTED ARM: the lease holds no token and no credential;
         both payments are free ([AppEcho.echo_sup_of_taint] read
         forwards, and [EchoLinks.echo_link_rd_taint]). *)
      iEval (rewrite /UkSh.ush_pos /UkSh.ush_at) in "Hp".
      iDestruct "Hp" as (n') "[Hpos _]".
      iSplitL "Hpos".
      + iApply (cons_acc_cred fsc_cons app_sup with "[] [Hpos]").
        * rewrite /cons_dirty_cred. iModIntro. iApply Hts. iExact "HT".
        * iIntros (cur dc). iModIntro.
          rewrite /ush_rd_ret. iRight. iFrame "HT". iExists n'.
          iExact "Hpos".
      + iIntros (ws). iApply ("Hrdt" $! (S gen_id) ws with "HT").
        iIntros "#HT'". rewrite /ush_rd_in. iRight. iExact "HT'".
  Qed.

  (* ...AND THE DEPOSIT, at its exact former statement: the neutral
     supplier at the era's own [Rd] and [Rin].  [UkReadCons.read_cons_fam]
     and [ush_read_fam_era] are the same record ([UkReadRows.xfam_rd] at
     those two), which is the whole content of "sh's read is an INSTANCE of
     the console member". *)
  Lemma ush_read_sup_era (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (N : uk_names Σ) (γp : gname)
      (m : regfile) (pc : mword 64) (l : list fdstate) (n : nat) (wr : bool) :
    (* the descriptor is fd 0, and fd 0 is the console *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE)) ->
    (* E2's two readings of the supply *)
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    echo_links T γ -∗
    UkSh.ush_lease N γp T (ush_mid γ γp) n -∗
    udepwf_std N m pc USYS_read (ush_read_fam_era T γ γp n (ukn_pay N)) l.
  Proof.
    intros Ha0 Hl0 Hst Hts.
    iIntros "#Hlk HP".
    iDestruct (ush_read_pay_era γ T N γp n Hst Hts with "Hlk HP")
      as "[Hacc Hlink]".
    iApply (udepwf_std_read_cons N m pc l 0%nat wr
              (ush_rd_ret γp T n) (ush_rd_in T γ n)
              Ha0 ltac:(unfold NSTD; lia) Hl0 with "Hacc Hlink").
  Qed.

  (* =================================================================== *)
  (*  THE BYTE THE READ DELIVERED IS THE LINE'S, AT SH'S OWN COUNT        *)
  (*  (the survey's §4(a)/(b), as a lemma).                               *)
  (*                                                                     *)
  (*  Three rows of one receipt meet here.  The WINDOW row                *)
  (*  ([ConsoleInv.cons_window]) says the [j]th byte the call DELIVERED   *)
  (*  is the ring's stored entry at [cur + j] and the caller's buffer     *)
  (*  byte is its translation.  The BOUNDARY row says the window the call *)
  (*  CONSUMED is that same stored run read at the bound                  *)
  (*  [ConsoleInv.cons_swallow] extends to, so the two agree wherever a   *)
  (*  byte was delivered.  And [EchoOut.ein_read_byte] places that byte   *)
  (*  in [EchoDisc.echo_line] BY THE READER'S OWN DELIVERED COUNT, which  *)
  (*  [EchoOut.read_ret] pins to [n].                                     *)
  (*                                                                     *)
  (*  STATED AT INDEX 0 AND NOT AT EVERY [j], because that is the only    *)
  (*  index the era's law reaches: [ein_read_byte] is at the count the    *)
  (*  window STARTS at, and sh's [gets] reads at [cap = 1] precisely so   *)
  (*  that the byte it copies is that one ([UkSh.v]'s §3).                *)
  (* =================================================================== *)
  Lemma ush_rd_byte_of_rows
      (sl sl' ws dl : list (list mobs * bv 8)) (hs : list (list mobs))
      (pops : list LogEntryDefs.log_entry)
      (n dd dc : nat) (g : nat -> bv 8) :
    (0 < dd)%nat -> (dd <= dc)%nat ->
    cons_window sl n dd g hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (n + j)%nat) ->
    E_byte (seg_of (echoed pops)) ->
    (dl ++ ws) `prefix_of` echoed pops ->
    length dl = n ->
    g 0%nat = echo_line !!! (n `mod` length echo_line)%nat.
  Proof.
    intros Hdd Hdc Hwin Hpre Hws HE Hpr Hdl.
    destruct Hwin as (_ & _ & Hwj).
    destruct (Hwj 0%nat Hdd) as (h & b & Hsl & _ & _ & Hg).
    assert (Hsl' : sl' !! (n + 0)%nat = Some (h, b))
      by (eapply prefix_lookup_Some; [ exact Hsl | exact Hpre ]).
    assert (Hw0 : ws !! 0%nat = Some (h, b))
      by (rewrite (Hws 0%nat ltac:(lia)); exact Hsl').
    pose proof (ein_read_byte pops dl ws n (h, b) HE Hpr Hdl Hw0) as Hb.
    cbn [snd] in Hb.
    rewrite Hg Hb.
    apply echo_line_no_cr.
    apply Nat.mod_upper_bound. pose proof echo_line_pos. lia.
  Qed.

  (* =================================================================== *)
  (*  S6  THE LEAF (lane IO-LEAF, M5)                                     *)
  (*                                                                     *)
  (*  [UkSh.ush_read_recv_leaf] itself, at the ENRICHED answer: the three *)
  (*  arms the landed one has, and on the window arm the era's own facts  *)
  (*  beside them.  Those facts are all PERSISTENT -- the delivered byte  *)
  (*  placed in [EchoDisc.echo_line] by sh's own count, and the era's two *)
  (*  bounds at the window's far end -- so the enriched answer WEAKENS to *)
  (*  the landed one for free ([ush_read_ans_of_era]) and the owed        *)
  (*  statement is one line below.  The era's delivered-count half is NOT *)
  (*  among them: it goes back into the LEASE, which is where the next    *)
  (*  read will look for it.                                             *)
  (*                                                                     *)
  (*  THE [-1] ARM IS REFUTED at an open readable console descriptor by   *)
  (*  TRAP-ROWS T2 ([UexecRet.uexec_live_ok]'s read clause), and that is  *)
  (*  what makes the credential's round trip possible at all: the         *)
  (*  receipt's [-1] arm hands back no window, and the boundary link the  *)
  (*  deposit carried goes with it.  At a SHUT fd 0 the deposit carries   *)
  (*  no link ([SpecFileread.fileread_in]'s [FdClosed] arm is [P -∗ P]),  *)
  (*  so the lease comes straight back and the [-1] arm is the answer.    *)
  (* =================================================================== *)
  Definition ush_rd_era_win (T : iProp Σ) (γ : echo_gn) (n dd dc : nat)
      (g : nat -> bv 8) : iProp Σ :=
    (T
     ∨ (⌜(0 < dd)%nat ->
          g 0%nat = echo_line !!! (n `mod` length echo_line)%nat⌝
        ∗ (⌜dc = 0%nat⌝
           ∨ ∃ (v : era_pins) (cs0 ps0 : list nat),
               era_pin γ (S gen_id) v ∗ cs_lb v cs0 ∗ ps_lb v ps0
               ∗ E_lb v (n + dc)%nat
               ∗ ⌜((n + dc) `div` length echo_line
                   <= S (length cs0))%nat⌝)))%I.

  Global Instance ush_rd_era_win_persistent T γ n dd dc g `{!Persistent T} :
    Persistent (ush_rd_era_win T γ n dd dc g).
  Proof. rewrite /ush_rd_era_win. apply _. Qed.

  Definition ush_read_ans_era (T : iProp Σ) (γ : echo_gn)
      (N : uk_names Σ) (γp : gname) (cnm : cons_names) (l : list fdstate)
      (r : mword 64) (cap n : nat) (g : nat -> bv 8) : iProp Σ :=
    ((∃ (dd dc : nat) (hs : list (list mobs))
        (sl : list (list mobs * bv 8)),
        ⌜ Z.of_nat dd = bv_unsigned r ⌝ ∗
        ⌜ (dd <= cap)%nat ⌝ ∗
        ⌜ dd = cap -> dc = dd ⌝ ∗
        ⌜ dd = 0%nat -> (0 < cap)%nat -> dc = (dd + 1)%nat ⌝ ∗
        ⌜ cons_chain sl ⌝ ∗
        ucons_stored_lb cnm sl ∗
        ([∗ list] hh ∈ hs, riscv_rx_tag hh) ∗
        ⌜ cons_window sl n dd g hs ⌝ ∗
        ucons_swallow cnm False sl dd dc ∗
        ush_rd_era_win T γ n dd dc g ∗
        ⌜ UkSh.ush_fd0c l ⌝ ∗
        ush_mid γ γp (n + dc)%nat)
     ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝
        ∗ ⌜ l !! 0%nat = Some FdClosed ⌝ ∗ ush_mid γ γp n)
     ∨ (T ∗ UkSh.ush_pos N γp))%I.

  (* THE ERA'S FACTS ARE PERSISTENT, so dropping them costs nothing -- and
     what is left is exactly [UkSh]'s answer, whose own byte row is the
     one the era's window arm carries.  WHERE THE WINDOW IS TAINTED the
     answer moves to [UkSh]'s taint arm: [UkSh] states its byte row
     unconditionally, so a window with no reading of its byte is not a
     window at that tier. *)
  Lemma ush_read_ans_of_era (T : iProp Σ) (γ : echo_gn) `{!Persistent T}
      (Wb : nat -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (cnm : cons_names) (l : list fdstate)
      (r : mword 64) (cap n : nat) (g : nat -> bv 8) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ush_read_ans_era T γ N γp cnm l r cap n g -∗
    UkSh.ush_read_ans N γp T (ush_mid γ γp) cnm l r cap n g.
  Proof.
    intro Hpay.
    rewrite /ush_read_ans_era /UkSh.ush_read_ans.
    iIntros "[Hw | [Hm | Ht]]";
      [ | iRight; iLeft; iExact "Hm" | iRight; iRight; iExact "Ht" ].
    iDestruct "Hw" as (dd dc hs sl)
      "(%H1 & %H2 & %H3 & %H4 & %H5 & #H6 & #H7 & %H8 & #H9 & #Hwin
        & %Hfdc & Hp)".
    rewrite /ush_rd_era_win.
    iDestruct "Hwin" as "[#HT | [%Hby _]]".
    { iRight. iRight. iFrame "HT". rewrite /UkSh.ush_pos.
      iExists (n + dc)%nat.
      iApply (ush_at_of_mid_taint γ T Wb N γp (n + dc)%nat Hpay with "HT Hp"). }
    iLeft. iExists dd, dc, hs, sl.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitR; [ by iPureIntro | ].
    iSplitR; [ iExact "H6" | ]. iSplitR; [ iExact "H7" | ].
    iSplitR; [ by iPureIntro | ]. iSplitR; [ iExact "H9" | ].
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iExact "Hp".
  Qed.

  Lemma ush_read_recv_era (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (Wb : nat -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate)
      (h : CpuId) (m : regfile) (pc : mword 64) (a : Z) (k cap n : nat)
      (f : nat -> bv 8) (avail : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    usysno m = USYS_read ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 0 ->
    uint (m !!! Regidx a1_idx) = a ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (Z.of_nat cap < 2 ^ 31)%Z ->
    UkSh.ush_fd0p l ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    echo_links T γ -∗
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    ubytes (ukn_d N) a k f -∗
    ustd (ukn_fd N) l -∗
    UkSh.ush_lease N γp T (ush_mid γ γp) n -∗
    urun (PS := uprogSG_free) N h m pc avail -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ustd (ukn_fd N) l -∗
       ush_read_ans_era T γ N γp fsc_cons l r cap n g -∗
       ubytes (ukn_d N) a k g -∗
       urun (PS := uprogSG_free) N h'
         (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hpay Hst Hts Hn Ha0 Ha1 Ha2 Hcapk Hcap31 Hfd0 Hal.
    iIntros "#Hlk #Hi Hbuf Hstd Hpos Hrun Hcont".
    subst a.
    pose proof (UkSh.ush_narrow_count_le (m !!! Regidx a2_idx) cap Ha2) as Hbnd.
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap)
      by exact (ush_count_is_cap (m !!! Regidx a2_idx) cap Ha2 Hcap31).
    change (2 ^ 31)%Z with 2147483648%Z in Hcap31.
    (* THE LEASE, OUT OF THE PROGRAM'S OWN HAND, IN PIECES (lane IO-LEAF,
       M5(3)): mid-line the era's credential is at no boundary, so what
       the walk carries is [UkSh.ush_lease] and not the payload. *)
    destruct Hfd0 as [[wr Hl0] | Hcl].
    - (* ================= fd 0 IS THE CONSOLE ================= *)
      (* THE ECHO TAILORING IS A WRAPPER NOW (lane RD-4).  The walk, the
         refutation of the [-1] arm at an open readable console descriptor,
         the receipt's two GUARDED rows (the per-byte ledger's linearity
         and [ConsoleInv.cons_swallow]'s copy-out fault) and the window's
         assembly are all the NEUTRAL console member's
         ([UkReadCons.wp_uk_ecall_read_cons]) -- none of them was ever
         about an application.  What is left here is the era's own reading
         of the input segment the call consumed, which is what [Rin] is
         for. *)
      assert (Hfdc : UkSh.ush_fd0c l) by (exists wr; exact Hl0).
      iDestruct (ush_read_pay_era γ T N γp n Hst Hts with "Hlk Hpos")
        as "[Hacc Hlink]".
      iApply (wp_uk_ecall_read_cons (PS := uprogSG_free) N h m pc
                (uint (m !!! Regidx a1_idx)) k cap f avail l 0%nat wr
                (ush_rd_ret γp T n) (ush_rd_in T γ n)
                Hn Ha0 ltac:(unfold NSTD; lia) Hl0 eq_refl Ha2 Hcapk Hcap31
                Hal with "Hi Hrun Hstd Hbuf Hacc Hlink").
      iIntros (h' r d g) "%Hd %Hgf Hstd Hans Hbuf Hrun".
      iDestruct "Hans" as (dd dc cur hs)
        "(%Hdr & %Hddcap & %Hb1 & %Hb4 & #Htags & Hrd & Hwin)".
      rewrite /ush_rd_ret.
      iDestruct "Hrd" as "[(%Hcur & Hp & Hrdt & Hpa) | [#HT Hp]]"; last first.
      { (* the caller's own [Rd] came back tainted *)
        iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /ush_read_ans_era /UkSh.ush_pos /UkSh.ush_at.
        iRight. iRight. iFrame "HT".
        iDestruct "Hp" as (n') "Hp". iExists n'. iFrame "Hp".
        rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
      subst cur.
      iDestruct "Hwin" as "[Hw | #Hdirty]"; last first.
      { (* a tokenless reader popped while the call slept *)
        iAssert T as "#HT"; [ iApply Hst; iExact "Hdirty" | ].
        iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /ush_read_ans_era /UkSh.ush_pos /UkSh.ush_at.
        iRight. iRight. iFrame "HT". iExists (n + dc)%nat. iFrame "Hp".
        rewrite Hpay. iApply (ucons_pay_taint with "HT"). }
      rewrite /uread_cons_win.
      iDestruct "Hw" as (sl) "(%Hch & #Hlb & %Hwinf & #Hsw & %Hddc & Hbnd)".
      iDestruct "Hbnd" as (sl2 ws)
        "(#Hlb2 & %Hpre2 & %Hlen2 & %Hlws & %Hwsj & Hrin)".
      (* THE BOUNDARY'S ANSWER, and THE PIECES KEPT TOGETHER (lane
         IO-LEAF, M5(3)): the era's credential at the window's far end
         goes back beside the token and both halves of the position pair,
         but NOT into the payload -- the far end is in the middle of a
         line, where the payload's own boundary row is false. *)
      iAssert ((ush_rd_era_win T γ n dd dc g ∗ ush_mid γ γp (n + dc)%nat)
               ∨ (T ∗ UkSh.ush_pos N γp))%I
        with "[Hrin Hrdt Hpa Hp]" as "Hera".
      { rewrite /ush_rd_era_win /ush_rd_in.
        iDestruct "Hrin" as "[Hret | #HT]"; last first.
        { iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
          iExists (n + dc)%nat. iFrame "Hp". rewrite Hpay.
          iApply (ucons_pay_taint with "HT"). }
        iDestruct "Hret" as (v) "(#Hpin & #HE0 & #Hres0 & Hret)".
        rewrite /read_ret.
        iDestruct "Hret" as "[[#HT _] | [Hdlr Hfacts]]".
        { iRight. iFrame "HT". rewrite /UkSh.ush_pos /UkSh.ush_at.
          iExists (n + dc)%nat. iFrame "Hp". rewrite Hpay.
          iApply (ucons_pay_taint with "HT"). }
        iDestruct "Hfacts" as (pops dl)
          "(%Hrok & %Hdl & %Hpref & %Hidx & %Hbyte & Hrest)".
        iEval (rewrite Hlws) in "Hdlr".
        (* THE WRITER'S BOUND AT THE FAR END: off the receipt where a byte
           was delivered, and the one the lease went in with where the
           window was empty (the count did not move). *)
        iDestruct "Hrest" as "#Hrest".
        iAssert (E_lb v (n + dc)%nat) as "#HEn".
        { iDestruct "Hrest" as "[%Hws0 | Hbb]".
          - assert (Hdc0 : dc = 0%nat)
              by (rewrite <- Hlws, Hws0; reflexivity).
            rewrite Hdc0 Nat.add_0_r. iExact "HE0".
          - iDestruct "Hbb" as (cs0 ps0) "(_ & _ & HE & _)".
            iEval (rewrite Hlws) in "HE". iExact "HE". }
        (* ...AND THE RECEIPT'S RESIDUE AT THE FAR END (step 4): off the
           receipt where a byte was delivered, the one the lease went in
           with where the window was empty *)
        iAssert (rd_res v (n + dc)%nat) as "#Hresn".
        { iDestruct "Hrest" as "[%Hws0 | Hbb]".
          - assert (Hdc0 : dc = 0%nat)
              by (rewrite <- Hlws, Hws0; reflexivity).
            rewrite Hdc0 Nat.add_0_r. iExact "Hres0".
          - iDestruct "Hbb" as (cs0 ps0) "(#Hcs & #Hps & _ & _ & #Htlb & %Hrds)".
            rewrite /rd_res. iExists ps0, cs0.
            iEval (rewrite Hlws) in "Htlb". iFrame "Htlb Hps Hcs".
            iPureIntro. rewrite <- Hlws. exact Hrds. }
        iLeft. iSplitR "Hdlr Hrdt Hpa Hp"; last first.
        { rewrite /ush_mid. iFrame "Hp Hpa Hrdt".
          iExists v. iFrame "Hpin Hdlr HEn Hresn". }
        iRight. iSplitR.
        { iPureIntro. intro Hdd0.
          exact (ush_rd_byte_of_rows sl sl2 ws dl hs pops n dd dc g
                   Hdd0 Hddc Hwinf Hpre2 Hwsj Hbyte Hpref Hdl). }
        iDestruct "Hrest" as "[%Hws0 | Hbb]".
        { iLeft. iPureIntro. rewrite <- Hlws, Hws0. reflexivity. }
        iRight. iDestruct "Hbb" as (cs0 ps0) "(#Hcs & #Hps & #HE & %Hbd & _)".
        iExists v, cs0, ps0. iFrame "Hpin Hcs Hps".
        iEval (rewrite Hlws) in "HE". iFrame "HE".
        iPureIntro. rewrite <- Hlws. exact Hbd. }
      iDestruct "Hera" as "[[#Hera Hmid] | [#HT Hp']]"; last first.
      { iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hp'] Hbuf Hrun");
          [ exact Hd | exact Hgf | ].
        rewrite /ush_read_ans_era. iRight. iRight. iFrame "HT Hp'". }
      iApply ("Hcont" $! h' r d g
                with "[%] [%] Hstd [Hmid] Hbuf Hrun");
        [ exact Hd | exact Hgf | ].
      rewrite /ush_read_ans_era. iLeft.
      iExists dd, dc, hs, sl.
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ iPureIntro; exact Hddcap | ].
      iSplitR; [ iPureIntro; exact Hb1 | ].
      iSplitR; [ iPureIntro; exact Hb4 | ].
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ iExact "Hlb" | ].
      iSplitR; [ iExact "Htags" | ].
      iSplitR; [ iPureIntro; exact Hwinf | ].
      iSplitR; [ iExact "Hsw" | ].
      iSplitR; [ iExact "Hera" | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hmid".
    - (* ================= fd 0 IS SHUT ================= *)
      iDestruct (ush_read_sup_closed N γp T (ush_rd_in T γ n) m pc l n
                   Ha0 Hcl) as "Hsb".
      iApply (wp_uk_ecall_read_recv (PS := uprogSG_free) N h m pc
                (bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0
                            : mword 32))
                k f avail (ush_read_fam_era T γ γp n (ukn_pay N)) l
                Hn eq_refl ltac:(lia) Hal
                with "Hi Hrun Hsb Hstd Hbuf").
      iIntros (h' r d g W M' fdv' cw' cs')
        "%Hd %Hgf %Hlin %HM %Hnf %Harg0 %Harg1 %Harg2 %Htake %Hlz %Hlive
         Hstd Hpost Hrun Hbuf".
      iDestruct (spost_at_read_elim uslot
                   (ush_read_fam_era T γ γp n (ukn_pay N)) W
                   (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                   (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                   Harg0 Harg1 Harg2 eq_refl with "Hpost")
        as "[%Hfrret Hpost']".
      iDestruct "Hpost'" as (P) "(%Hperm & %Hwf & %Hlazy & Hrec)".
      iEval (rewrite (ush_fd_st_closed (m !!! Regidx a0_idx) (uvis_fd W) l
                        Ha0 Htake Hcl) /fileread_extra_core) in "Hrec".
      iDestruct "Hrec" as "%Hm1".
      iApply ("Hcont" $! h' r d g
                with "[%] [%] Hstd [Hpos] Hbuf Hrun");
        [ lia | exact Hgf | ].
      rewrite /ush_read_ans_era /UkSh.ush_lease.
      iDestruct "Hpos" as "[Hmid | [#HT Hp]]";
        [ | iRight; iRight; iFrame "HT Hp" ].
      iRight. iLeft.
      iSplitR; [ by iPureIntro | ].
      iSplitR; [ by iPureIntro | ]. iExact "Hmid".
  Qed.

  (* =================================================================== *)
  (*  S7  THE OWED STATEMENT, DISCHARGED.                                 *)
  (*                                                                     *)
  (*  This is [UShLine.ush_read_recv_leaf_holds] back, at the same        *)
  (*  statement lane ECHO-OUT part 5 deleted it at, with the flat input   *)
  (*  licence replaced by the era's read link and the credential read off *)
  (*  sh's own lease.  [UInitBootAdequacy]'s [Hsh_owed] loses its third   *)
  (*  conjunct with it.                                                   *)
  (*                                                                     *)
  (*  [echo_links] is a COQ-LEVEL premise for the licence's own reason:   *)
  (*  the result is a Coq-level [⊢], and the discharge site               *)
  (*  ([UInitBoot.echo_Hinit_boot]) is where the record's four equations  *)
  (*  are, which is where [EchoLinks.echo_links_holds] proves it.         *)
  (* =================================================================== *)
  Lemma ush_read_recv_leaf_holds (γ : echo_gn) (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (Wb : nat -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    (⊢ app_sup -∗ T) ->
    (⊢ T -∗ app_sup) ->
    (⊢ echo_links T γ) ->
    (* AT THE FREE INSTANCE, NAMED (durable-notes, the two-instances
       wedge): [UkRun.urun] carries [udep], so the leaf is PS-indexed, and
       the one that consumes it -- sh's entry -- is at
       [UexecExecInst.uprogSG_free] while ambient resolution here would
       find [uprogSG_gen].  The two are not convertible. *)
    ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp T
        (ush_mid γ γp) fsc_cons l.
  Proof.
    intros Hpay Hst Hts Hlk.
    iAssert (echo_links T γ) as "#Hlk"; [ iApply Hlk | ].
    rewrite /UkSh.ush_read_recv_leaf.
    iIntros (h m pc a k cap n f avail)
      "%Hn %Ha0 %Ha1 %Ha2 %Hcapk %Hcap31 %Hfd0 %Hal #Hi Hbuf Hstd Hpos Hrun
       Hcont".
    iApply (ush_read_recv_era γ T Wb N γp l h m pc a k cap n f avail
              Hpay Hst Hts Hn Ha0 Ha1 Ha2 Hcapk Hcap31 Hfd0 Hal
              with "Hlk Hi Hbuf Hstd Hpos Hrun [Hcont]").
    iIntros (h' r d g) "%Hd %Hgf Hstd Hans Hbuf Hrun".
    iApply ("Hcont" $! h' r d g with "[%] [%] Hstd [Hans] Hbuf Hrun");
      [ exact Hd | exact Hgf | ].
    iApply (ush_read_ans_of_era T γ Wb N γp fsc_cons l r cap n g Hpay
              with "Hans").
  Qed.


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
