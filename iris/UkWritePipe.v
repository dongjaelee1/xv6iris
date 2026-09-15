(* ===================================================================== *)
(* UkWritePipe.v -- THE PIPE ARM OF THE GENERIC WRITE LEAF.               *)
(*                                                                        *)
(* RD-5 predicted this file's shape from the read side and was right about *)
(* the payment and WRONG, in the program's favour of honesty, about the    *)
(* post: it expected "a supplier from [emp], a pure [filewrite_ret] post,  *)
(* and the same two owed kernel-side rows".  The payment is indeed [emp].  *)
(* THE POST IS EMPTIER THAN THAT, and the reason is not the pipe at all:   *)
(*                                                                        *)
(*   ROW 16 CARRIES NO RETURN BLANKET.  [UexecExecInst.xv6_spost]'s read   *)
(*   row is [⌜SpecFileread.fileread_ret (sys_rw_count (xk_a W 2)) r⌝]      *)
(*   BESIDE [fileread_extra_core] -- which is why RD-5's pipe READ member  *)
(*   could state [PipeInvDefs.pipe_rw_ret] at the caller's own count even  *)
(*   though the pipe arm of the receipt is [emp].  The WRITE row is        *)
(*   deliberately "[filewrite_extra] at the same key, WITHOUT              *)
(*   [filewrite_ret], the round carrying [UsysMemOk.usys_fd_ok] instead"   *)
(*   (that file's own note).  At an inode or a console descriptor nothing  *)
(*   is lost -- [SpecFilewrite.write_arms_at_ret] and                      *)
(*   [write_cons_arms_ret] recover the blanket FROM the arm -- but at a    *)
(*   PIPE the arm is [emp], so there is nothing to recover it from.        *)
(*                                                                        *)
(* So a U-tier pipe write learns NOTHING about its return value: not the   *)
(* count, not even that it is [-1] or in range.  That is the honest        *)
(* strength, and it is stated below.  THE ROW IS OWED AND IT IS ONE LINE   *)
(* KERNEL-SIDE: row 16's post gains the conjunct row 5 already has.  It is *)
(* an edit to [UexecExecInst.xv6_spost]'s 16 arm plus                      *)
(* [UkWriteLeaf.spost_at_write_elim_at]'s conclusion and every row-16      *)
(* consumer's post shape -- a wide cone for a one-line row, which is why   *)
(* this lane records it rather than takes it.                              *)
(*                                                                        *)
(* WHAT IS TRUE HERE, AND IT IS NOT NOTHING.  The member is the            *)
(* REACHABILITY statement for the write end: a program holding             *)
(* [ufd b (FdOpen false true FdPipe)] -- the handle                        *)
(* [UkReadPipe.wp_uk_pipe_read_end] hands back from [sys_pipe]'s own join  *)
(* -- can make the call, PAY NOTHING for it, and keep its handle and its   *)
(* source run.  Compare the two other members: the file arm costs one      *)
(* chunk chain, the console arm one output chain, the pipe arm nothing at  *)
(* all, which is design/user-read.md section 1's "the payment is a         *)
(* resource the PROGRAM owns and understands" at its limit case, exactly   *)
(* as [UkReadPipe.udepwf_st_read_pipe] is on the read side.                *)
(*                                                                        *)
(* AND THE TWO ROWS RD-5 LEFT OWED ARE STILL OWED, unchanged and for the   *)
(* same reason ([PipeInvDefs.pipe_names]' four gnames are all about the    *)
(* ENDS; the ring's contents are existential inside the pipe's own         *)
(* spinlock): there is no byte-queue ghost, so "the bytes the writer       *)
(* pushed are the reader's next bytes" is not statable at any tier today.  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
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
Require Import UserHeap.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith.
Require Import ProcGeom.           (* [NOFILE] / [tf_arg_idx] *)
Require Import VcGen.              (* [trunc32] *)
Require Import PieceFam.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UkReadRows.         (* [udepwf_st] / [ufd_key_agree] *)
Require Import UkWriteLeaf.        (* row 16's family and its two key rows *)
Require Import SpecArgfd.          (* [fd_st_of_key] *)
Require Import SpecFilewrite.      (* [filewrite_in] / [filewrite_extra] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section UkWritePipe.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY -- the other two members', at the trivial cursor      *)
  (* =================================================================== *)
  (* Row 16's ONE family field is [wf_Q], and there is no chain here for a
     cursor to be the cursor OF, so it is the unit.  No family argument and
     no payment argument: there is nothing for a caller to choose. *)
  Definition write_pipe_fam (Xp : Z -> iProp Σ) : sfam :=
    xfam_wr (fun _ => True%I) Xp.

  (* =================================================================== *)
  (*  2.  THE DEPOSIT'S SUPPLIER, PROVED FROM NOTHING                      *)
  (* =================================================================== *)
  (* [SpecFilewrite.filewrite_in] at [FdOpen _ true FdPipe] is the [_ => P]
     arm: it takes NOTHING.  (The [P] the kernel threads through is [True]
     at this leaf, so what is left is the unit.)  A pipe write costs its
     caller nothing beyond its own handle. *)
  Lemma udepwf_st_write_pipe (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (rb : bool) :
    ⊢ udepwf_st N m pc 16 (write_pipe_fam (ukn_pay N))
        (FdOpen rb true FdPipe).
  Proof.
    rewrite /udepwf_st. iSplitR; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Hkey _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_write_intro_at uslot (write_pipe_fam (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
              (m !!! Regidx a2_idx) fdv M
              (tf_of_arg0 m pc) (tf_of_arg1 m pc) (tf_of_arg2 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false)
              eq_refl).
    rewrite Hkey. cbn [write_pipe_fam xfam_wr wf_Q].
    rewrite /filewrite_in /=. done.
  Qed.

  (* =================================================================== *)
  (*  3.  THE MEMBER                                                      *)
  (* =================================================================== *)
  (* [UkRunSys.wp_uk_ecall_write_at]'s walk at the pipe handle, taken
     DIRECTLY rather than through [UkWriteFile.wp_uk_ecall_write_file] for
     [UkReadPipe]'s reason: a pipe end is a descriptor a program was GIVEN
     by [sys_pipe] rather than one any ledger can reach, so the reading is
     the handle's ([UkReadRows.ufd_key_agree]) -- the file arm's route, for
     the file arm's reason -- and the walk's [D]/[K] fit it with nothing
     added.

     WHAT COMES BACK is the handle and the run, and NOTHING about [r]: see
     the header.  The run comes back because 16 writes no user byte, and
     that is worth having -- it is what lets a program loop over a buffer
     it keeps. *)
  Lemma wp_uk_ecall_write_pipe (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (fd : nat) (rb : bool)
      (dq : dfrac) (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    (* THE HANDLE, and it is the WHOLE payment *)
    UserFd.ufd (ukn_fd N) fd (FdOpen rb true FdPipe) -∗
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (∀ (h' : CpuId) (r : mword 64),
       UserFd.ufd (ukn_fd N) fd (FdOpen rb true FdPipe) -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hufdh Hbuf Hcont".
    iPoseProof (udepwf_st_write_pipe N m pc rb) as "Hsb".
    iApply (wp_uk_ecall_write_at N h m pc avail (write_pipe_fam (ukn_pay N))
              (UserFd.ufd (ukn_fd N) fd (FdOpen rb true FdPipe))
              (ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f)
              (fun fdv => fd_st_of_key (m !!! Regidx a0_idx) fdv
                          = FdOpen rb true FdPipe)
              nb f Hn Hal4
              (ufd_key_agree N fd (FdOpen rb true FdPipe)
                 (m !!! Regidx a0_idx) Hfdv Hfdlt)
              (fun M pmv sz =>
                 usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz dq
                   (m !!! Regidx a1_idx) nb f)
              with "Hi Hrun [Hsb] Hufdh Hbuf").
    { rewrite /udepwf_st /udepwf_K. iExact "Hsb". }
    iIntros (h' r W cw' cs')
      "%Hk0 %Hk1 %Hk2 %Hkey %Hlz %Hsrc Hufdh Hbuf Hpost Hrun".
    (* THE ARM TELLS NOTHING ([filewrite_extra] at [FdOpen _ true FdPipe] is
       [emp]) and the row carries no blanket, so the post is dropped. *)
    iApply ("Hcont" $! h' r with "Hufdh Hbuf Hrun").
  Qed.

  (* ...AND AT THE STATE [sys_pipe] ACTUALLY HANDS BACK.  RD-5's
     [UkReadPipe.wp_uk_pipe_read_end] reads the pipe leaf's post one step
     into the two members' own premises and gives out
     [ufd a (FdOpen true false FdPipe)] and
     [ufd b (FdOpen false true FdPipe)]; this is the second of those at the
     write member's premise, which is the join the brief asked to be
     checked rather than assumed. *)
  Lemma wp_uk_pipe_write_end (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (fd : nat)
      (dq : dfrac) (nb : nat) (f : nat -> bv 8) :
    usysno m = 16 ->
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen false true FdPipe) -∗
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
    (∀ (h' : CpuId) (r : mword 64),
       UserFd.ufd (ukn_fd N) fd (FdOpen false true FdPipe) -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb f -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hfdv Hfdlt Hal4.
    iIntros "#Hi Hrun Hufdh Hbuf Hcont".
    iApply (wp_uk_ecall_write_pipe N h m pc avail fd false dq nb f
              Hn Hfdv Hfdlt Hal4 with "Hi Hrun Hufdh Hbuf Hcont").
  Qed.

End UkWritePipe.
