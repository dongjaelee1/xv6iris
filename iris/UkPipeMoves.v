(* ===================================================================== *)
(* UkPipeMoves.v -- THE DESCRIPTOR MOVES A PIPE ROW MAKES AT THE STANDARD *)
(* SLOTS (design/app-pipe.md SS5.1/SS5.4; lane PIPE-STD, item 3).           *)
(*                                                                        *)
(* sh's PIPE arm moves pipe rows THROUGH THE LEDGER: after [close(1)] it  *)
(* [dup]s the write end into slot 1, after [close(0)] the read end into   *)
(* slot 0, and it closes the two handles the [pipe] call gave it.  Lane   *)
(* PIPE-STD's brief asked whether any of the five landed leaves that move *)
(* a descriptor PINS the moved row (or the table) to be pipe-free, and    *)
(* if one does, to add the pipe-typed twin.                               *)
(*                                                                        *)
(* THE ANSWER IS THAT NONE OF THEM DOES, so there is no twin to add and   *)
(* no pin to lift.  Read at the statements:                               *)
(*                                                                        *)
(*  - [UkRunSys.wp_uk_ecall_dup] takes [st <> FdClosed] and               *)
(*    [ukn_held N = ∅] and NOTHING about the row's type; the table row it *)
(*    re-establishes is [UkRun.urun_rows_dup], whose own premise is only  *)
(*    [fdv !! k = Some st] -- a COPY of a row the table already had is    *)
(*    paid by whatever paid that row ([urun_nopipe_dup]: either the       *)
(*    pure arm, where the source row's pipe-freedom comes off the table's *)
(*    own, or the taint).  So a pipe row dups like any other, and the     *)
(*    test below is the evidence.                                        *)
(*  - [wp_uk_ecall_dup_untracked] likewise, through                       *)
(*    [UkRun.urun_rows_copy], which has no premise at all.                *)
(*  - [wp_uk_ecall_dup_closed] is about a source slot the ledger says is   *)
(*    CLOSED (it refutes the success arm), so no row moves.                *)
(*  - [wp_uk_ecall_close] and [wp_uk_ecall_close_std] take the close      *)
(*    payment as [UkRun.udepw_cl N m pc st], which is INDEXED BY THE      *)
(*    STATE: its left arm is “st is not a pipe end” and its right arm is  *)
(*    a deposit at 21 ([udepw_cl_of_udepw]) -- which is exactly where a   *)
(*    pipe row's close link (lane PIPE-REG's registry) goes in.  The      *)
(*    [fdst_nopipe] the two proofs do use is [fdst_nopipe_closed], about  *)
(*    the [FdClosed] they INSTALL, never about the row they remove.       *)
(*                                                                        *)
(* WHAT DOES PIN, and it is not one of the five: sh's own wrappers        *)
(* [UkSh.wp_ksh_close] / [wp_ksh_cstub] and [UkShRedir.wp_kshx_close_std] *)
(* carry the PURE premise “st is not a pipe end” and spend it on          *)
(* [UkRun.udepw_cl_nonpipe].  That pin is LOAD-BEARING (it is the whole   *)
(* of how those leaves mint their close deposit), so per this lane's STOP *)
(* rule it is not lifted here; lane SH-PIPE, whose brief takes the six    *)
(* closes of the PIPE arm through the GENERIC leaves with the registry's  *)
(* deposits, needs the generic ones and not the wrappers for [close(p[0])] *)
(* and [close(p[1])].  [close(1)]/[close(0)] shut CONSOLE rows and the    *)
(* wrappers serve them unchanged.                                        *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import PipeNames.          (* [pipe_names] *)
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.
Require Import ProcGeom.           (* [NOFILE] / [NSTD] *)
Require Import UsysMemOk.         (* [USYS_close] / [USYS_dup] *)
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import CtxIdDefs.
Local Open Scope Z_scope.
Import Defs.

Section UkPipeMoves.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).

  (* =================================================================== *)
  (*  1.  THE CLAIM ABOVE THE STANDARD STREAMS IS A HANDLE                *)
  (* =================================================================== *)
  (* [UserFd.ufd_own] is the disjunction the two dup leaves take and give
     back; [ufd_own_hi] is the way in and this is the way OUT at a
     descriptor the caller knows is not a standard stream.  It is what
     turns dup's “your source comes back” into “your HANDLE comes back”,
     which is what a program holding a pipe end has. *)
  Lemma ufd_of_own_hi (γf : gname) (l : list fdstate) (fd : nat)
      (st : fdstate) :
    (NSTD <= fd)%nat -> ufd_own γf l fd st -∗ ufd γf fd st.
  Proof using .
    iIntros (Hge) "[[%Hlt _] | $]". exfalso. lia.
  Qed.

  (* =================================================================== *)
  (*  2.  THE LEDGER ARITHMETIC OF [close(k); dup(p)]                      *)
  (* =================================================================== *)
  (* Both moves sh's PIPE arm makes are this one fact at [k = 1] (echo's
     write end) and [k = 0] (cat's read end): a ledger of three OPEN
     console rows with slot [k] shut has [k] as its lowest closed slot, so
     the next allocation is DETERMINED and lands there
     ([UserFd.ualloc_std]).  Computation, at the console row the boot
     ledger actually holds. *)
  Definition ucons (mj : Z) : fdstate := FdOpen true true (FdDevice mj).

  Lemma lowest_closed_std1 (mj : Z) :
    fd_lowest_closed [ucons mj; FdClosed; ucons mj] = Some 1%nat.
  Proof using . reflexivity. Qed.

  Lemma lowest_closed_std0 (mj : Z) :
    fd_lowest_closed [FdClosed; ucons mj; ucons mj] = Some 0%nat.
  Proof using . reflexivity. Qed.

  (* =================================================================== *)
  (*  3.  THE CONSUMER TEST: close(1); dup(p[1]) INSTALLS THE WRITE END    *)
  (*      IN SLOT 1                                                       *)
  (* =================================================================== *)
  (* The brief's test, at the leaves.  A program holds the boot ledger
     ([c; c; c], three console rows) and a HANDLE on a pipe's write end
     above the standard streams -- which is exactly what [pipe(2)] hands
     back at a full ledger ([UkReadPipe.wp_uk_pipe_read_end]) -- and it
     runs sh's two instructions: [close(1)], then [dup] of the handle.
     The ledger arrives at [c; W; c]: the pipe's write end IS fd 1, which
     is what [UkWritePipe.wp_uk_ecall_write_pipe_std] then writes through
     and what echo's entry claims.

     THE RELOAD OF a0 IS A PREMISE and not part of the test: close's
     return value lands in a0, so a program has to put [p[1]] back there
     with its own instructions before the second ecall, and those
     instructions are sh's code (lane SH-PIPE).  The premise says only
     “whatever they are, they take the run from where close left it to
     where dup starts” -- durable-notes' trick of making a CALL a premise
     -- so the test is about the two DESCRIPTOR MOVES and nothing else.

     NOTHING IN IT IS PIPE-SPECIFIC except the row, which is the point:
     the two leaves are applied at a [FdPipe] state with no extra premise
     and no twin. *)
  Lemma wp_uk_close1_dup_pipe_std (N : uk_names Σ) (h : CpuId)
      (m m2 : regfile) (pc pc2 : mword 64) (mj : Z) (γp : pipe_names)
      (rb : bool) (fdp : nat) (avail : nat) :
    (* ---- close(1) ---- *)
    usysno m = USYS_close ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = 1%Z ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    (* ---- dup(p[1]), at the register file the program's own instructions
       built ---- *)
    usysno m2 = USYS_dup ->
    bv_signed (trunc32 (m2 !!! Regidx a0_idx)) = Z.of_nat fdp ->
    (* [ukn_held N = ∅] IS GONE (lane PIPE-NEG1, porting the campaign over
       upstream's OFF-LINK-2 L6): [UkRunSys.wp_uk_ecall_dup] pins only
       [st <> FdClosed] now, the parked discipline and the record field
       [UkRun.ukn_held] having left the tree. *)
    is_aligned_vaddr (Virtaddr (add_vec_int pc2 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    uinstr_is (ukn_t N) pc2 false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m2 pc2 USYS_dup -∗
    (* THE LEDGER: three open console rows *)
    ustd (ukn_fd N) [ucons mj; ucons mj; ucons mj] -∗
    (* ...AND A HANDLE ON THIS PIPE'S WRITE END, above them *)
    ufd (ukn_fd N) fdp (FdOpen rb true (FdPipe γp)) -∗
    (* the program's own reload of a0 between the two ecalls *)
    (∀ (h1 : CpuId) (r : mword 64),
       urun N h1 (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       (∀ h2 : CpuId,
          urun N h2 m2 pc2 avail -∗ WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang)) -∗
    (∀ (h3 : CpuId) (r2 : mword 64),
       (* dup answered 1: the slot was DETERMINED by the caller's own
          ledger, so the failure arm (“the table was full”) is refuted by
          computation *)
       ⌜r2 = (mword_of_int 1 : mword 64)⌝ -∗
       (* THE WRITE END IS FD 1 *)
       ustd (ukn_fd N)
         [ucons mj; FdOpen rb true (FdPipe γp); ucons mj] -∗
       (* ...and the handle comes home untouched: dup does not disturb its
          source, and the slot the copy landed in was not the source's *)
       ufd (ukn_fd N) fdp (FdOpen rb true (FdPipe γp)) -∗
       urun N h3 (<[Regidx a0_idx := r2]> m2) (add_vec_int pc2 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using .
    intros Hn1 Ha01 Hal1 Hn2 Ha02 Hal2.
    iIntros "#Hi1 #Hi2 Hrun Hdep Hstd Hh Hload Hcont".
    (* the handle is not a standard stream, which is what brings it back as
       a handle after the dup *)
    iDestruct (ufd_ge (ukn_fd N) fdp (FdOpen rb true (FdPipe γp))
                 with "Hh") as %Hge.
    (* ---- close(1), at the ledger's own slot ---- *)
    iApply (wp_uk_ecall_close_std N h m pc
              [ucons mj; ucons mj; ucons mj] 1%nat (ucons mj) avail
              Hn1 Ha01 ltac:(unfold NSTD; lia) eq_refl
              ltac:(discriminate) Hal1
              with "Hi1 Hrun [] Hstd").
    { iApply (udepw_cl_nonpipe N m pc (ucons mj)).
      intros rb' wb' gp'. discriminate. }
    iIntros (h1 r) "_ Hstd Hrun".
    (* ---- the program's own reload of a0 ---- *)
    iApply ("Hload" $! h1 r with "Hrun").
    iIntros (h2) "Hrun".
    (* ---- dup(p[1]), AT A PIPE ROW: no premise about the row's type ---- *)
    iApply (wp_uk_ecall_dup N h2 m2 pc2
              [ucons mj; FdClosed; ucons mj] fdp
              (FdOpen rb true (FdPipe γp)) avail
              Hn2 Ha02 ltac:(discriminate) Hal2
              with "Hi2 Hrun Hdep Hstd [Hh]").
    { iApply (ufd_own_hi (ukn_fd N) [ucons mj; FdClosed; ucons mj] fdp
                (FdOpen rb true (FdPipe γp)) with "Hh"). }
    iIntros (h3 r2) "[Hok | [%Hbad _]] Hrun".
    - iDestruct "Hok" as (fd1) "([%Hr2 %Hlt] & Halloc & Hown)".
      iDestruct (ualloc_std (ukn_fd N) [ucons mj; FdClosed; ucons mj]
                   fd1 1%nat (FdOpen rb true (FdPipe γp))
                   (lowest_closed_std1 mj) with "Halloc") as "[%Hfd1 Hstd]".
      subst fd1.
      iDestruct (ufd_of_own_hi (ukn_fd N)
                   (ustd_after [ucons mj; FdClosed; ucons mj]
                      (FdOpen rb true (FdPipe γp))) fdp
                   (FdOpen rb true (FdPipe γp)) Hge with "Hown") as "Hh".
      iApply ("Hcont" $! h3 r2 with "[%] [Hstd] Hh Hrun").
      + rewrite Hr2. reflexivity.
      + iExact "Hstd".
    - (* REFUTED BY COMPUTATION: slot 1 is closed, so the table is not
         full and dup cannot have answered -1. *)
      exfalso. destruct Hbad as [_ Hnone].
      rewrite (lowest_closed_std1 mj) in Hnone. discriminate Hnone.
  Qed.

End UkPipeMoves.
