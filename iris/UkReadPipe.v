(* ===================================================================== *)
(* UkReadPipe.v -- THE PIPE ARM OF THE GENERIC READ LEAF.                  *)
(*                                                                        *)
(* design/user-read.md section 3's PIPE row, on RD-4's shape: supplier ->  *)
(* content post -> leaf, the walk taken from                               *)
(* [UkRunSys.wp_uk_ecall_read_at] (the ONE read walk, parametric in the    *)
(* descriptor resource [D] and the pure reading [K] of the key's table)    *)
(* and the deposit an instance of [UkRunSys.udepwf_K].                     *)
(*                                                                        *)
(* WHAT THE SURVEY FOUND, AND IT DECIDES THIS FILE.  Section 3 asks for    *)
(* "an AU on the pipe's byte queue at the read end" and a content post     *)
(* "delivered bytes = a prefix of the queue, queue advanced".  RD-4's      *)
(* console finding was that the payment was ALREADY an AU one level below  *)
(* the merged claim; the pipe's answer is the opposite, and it is not a    *)
(* gap in the U tier:                                                      *)
(*                                                                        *)
(*   THERE IS NO BYTE-QUEUE GHOST TO STATE AN AU ON.  [PipeInvDefs]'s      *)
(*   [pipe_names] carries FOUR gnames and every one of them is about the   *)
(*   ENDS -- [pn_read]/[pn_write] are the two reference fractions and      *)
(*   [pn_mread]/[pn_mwrite] the two open marks.  The ring's contents are   *)
(*   the [bs] existentially bound inside [pipe_res_at], i.e. inside the    *)
(*   payload of the pipe's own SPINLOCK, and the queue coupling that would *)
(*   say which of those 512 bytes are live is not imposed: what IS imposed *)
(*   is the pure counter bound [pipe_count_ok nr nw], and                  *)
(*   design/pipe.md says of it, in terms, "Nothing consumes it yet -- the  *)
(*   CONTENTS of the live window stay existential; it and [pipe_data]'s    *)
(*   tracked byte list are the hooks a future contents-indexed refinement  *)
(*   builds on."  [SpecPiperead]'s own contract says the same thing at the *)
(*   function tier: "[bs] is what came out of the pipe, which no contract  *)
(*   at this tier can name".                                               *)
(*                                                                        *)
(*   SO THE KERNEL'S READ CONTRACT AT A PIPE DESCRIPTOR IS A NO-OP ON BOTH *)
(*   SIDES, and this is landed definition, not an omission to be repaired  *)
(*   from above: [SpecFileread.fileread_in] at [FdOpen true _ FdPipe] is   *)
(*   the [_ => P] arm (it takes NOTHING), and                              *)
(*   [SpecFileread.fileread_extra_core] at the same state is [emp] (it     *)
(*   tells NOTHING).  Section 3's Pipe row is therefore, TODAY, exactly    *)
(*   its "Dev (other)" row -- "the base weak form (bytes exist, tail       *)
(*   pinned) -- honest, since the device model gives nothing to name".     *)
(*                                                                        *)
(* WHAT THIS FILE THEREFORE IS.  The pipe member at its honest strength,   *)
(* which is worth landing for three reasons and is worth no more than      *)
(* that:                                                                   *)
(*                                                                        *)
(*  - THE PAYMENT SIDE IS FINISHED, not weak.  A pipe read costs its       *)
(*    caller NOTHING beyond its own handle ([udepwf_st_read_pipe] below is *)
(*    proved from [emp]), which is section 1's "the per-arm payment is a   *)
(*    resource the PROGRAM owns and understands" at its limit case.  When  *)
(*    a queue ghost lands, this supplier gains an argument and nothing     *)
(*    else about the file moves.                                           *)
(*  - THE ARM DISPATCH WORKS AT THE PIPE HANDLE.  The one walk's [D]/[K]   *)
(*    parametrization fits a pipe end with nothing added: a pipe end is a  *)
(*    descriptor a program was GIVEN (by [sys_pipe]) rather than one the   *)
(*    ledger can reach, so the reading is [UkReadRows.ufd_fd_st_of_key]'s  *)
(*    -- the same route the file arm takes, and for the same reason.       *)
(*  - AND WHAT THE PROGRAM IS TOLD IS STATED RATHER THAN LOST:             *)
(*    [uread_pipe_ans] below is [PipeInvDefs.pipe_rw_ret] read at the      *)
(*    caller's own [nat] count.  -1 is NOT refuted here and that is        *)
(*    correct: [UexecRet.uexec_live_ok] refutes it only at the console,    *)
(*    and piperead really does answer -1 (killed while asleep, or the very *)
(*    first copyout faulted).                                              *)
(*                                                                        *)
(* THE EOF ROW IS OWED, and it is owed one level down.  Section 3's "EOF:  *)
(* writer end closed and queue empty -> r = 0" is a fact about the pipe's  *)
(* OPEN MARKS ([pipe_endstate]) and its counters, both of which live under *)
(* the pipe's lock; [fileread_extra_core]'s [emp] is where it would have   *)
(* to come through, and it does not.  No U-tier statement can mint it.     *)
(*                                                                        *)
(* ...AND SO IS THE COUNT/WINDOW JOIN, which is the sharper of the two     *)
(* owed rows and is the exact analogue of [UsysMemOk]'s SS2c.  The walk    *)
(* hands out a window length [d] (the bytes [usys_mem_ok] says the call    *)
(* wrote) and the post hands out a return value [r]; at the INODE arm      *)
(* [FsAbsReadFire.read_post_ok] ties them ([Z.of_nat d = bv_unsigned r])   *)
(* and at the CONSOLE arm [SpecFileread.console_receipt] does, but at the  *)
(* pipe arm NOTHING does -- so a program reading a pipe cannot conclude    *)
(* that the bytes of its buffer ABOVE the returned count are unchanged.    *)
(* That is a kernel-side row ([fileread_extra_core]'s pipe arm), not a     *)
(* U-tier one; the continuation below therefore hands [d] and [r] over     *)
(* separately and claims no equation between them.                         *)
(*                                                                        *)
(* ON [UkReadFile]: this file takes two ARM-INDEPENDENT names from it,     *)
(* [udepwf_st] (the STATE-fixed deposit, which is [UkRunSys.udepwf_K] at   *)
(* the handle reading) and [ufd_key_agree] (that reading, taken where both *)
(* halves are in one hand).  Neither says anything about files -- the      *)
(* "file" leaf is really the HANDLE leaf -- and their proper home is       *)
(* [UkReadRows.v] beside the two [fd_st_of_key] readings that are already  *)
(* there.  They are not moved here for RD-1's operational reason: an edit  *)
(* to [UkReadRows.v] invalidates [UShLine.vo] and with it the whole echo   *)
(* chain above it, for a move with no proof content.  Recorded as owed.    *)
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
Require Import FdSlots.             (* [fdstate] / [fd_lowest_closed] *)
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import PipeInvDefs.         (* [pipe_rw_ret] -- what read answers here *)
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith.
Require Import ProcGeom.            (* [NOFILE] / [NSTD] / [tf_arg_idx] *)
Require Import VcGen.               (* [trunc32] *)
Require Import PieceFam.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.       (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UkReadRows.          (* the shared key-level rows *)
Require Import UkReadFile.          (* [udepwf_st] / [ufd_key_agree] -- the
                                       ARM-INDEPENDENT handle deposit, see
                                       the header's last paragraph *)
Require Import SpecArgfd.           (* [fd_st_of_key] *)
Require Import SpecFileread.        (* [fileread_in] / [fileread_ret] *)
Require Import SpecSysRead.         (* [sys_rw_count] *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

Section UkReadPipe.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* THE PROGRAM'S SUPPLY CLASS IS GENERALIZED and not resolved here, for
     [UkReadCons.v]'s reason (RD-4): the kernel's own instance is
     [UexecExecInst.uprogSG_gen] and a program whose numbers are free runs
     at [uprogSG_free]; the two are NOT convertible, so a leaf that fixes
     one cannot be applied by a program at the other. *)
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  1.  THE FAMILY                                                      *)
  (* =================================================================== *)
  (* THE CHOICE IS IMMATERIAL HERE, AND THAT IS THE FINDING.  The two
     family records are the two ARMS ([UkReadRows.v]'s header):
     [xfam_rd] names [rf_ret]/[rf_in] (what the CONSOLE caller asks to be
     told) and [xfam_rdf] names [rf_F] (the INODE caller's observation
     receipt).  The pipe arm of [SpecFileread.fileread_in] and of
     [fileread_extra_core] reads NONE of the three, so any record with the
     right exit payload serves; it is spelled as [xfam_rd] at the trivial
     readings, which is "a caller that asks to be told nothing" -- the
     shape the row will keep when a queue ghost gives it something to ask
     for. *)
  Definition read_pipe_fam (Q : Z -> iProp Σ) : sfam :=
    xfam_rd Q (fun _ _ => True%I) (fun _ => True%I).

  (* =================================================================== *)
  (*  2.  THE DEPOSIT'S SUPPLIER: NOTHING AT ALL                          *)
  (* =================================================================== *)
  (* The whole price of a pipe read, and it is [emp].  Compare the file
     arm ([UkReadFile.udepwf_st_read_file]: one observation commit) and the
     console arm ([UkReadCons.udepwf_std_read_cons]: the ring's payment and
     one AU on the console history).  A pipe read's arm of
     [SpecFileread.fileread_in] is the [_ => P] one, so the supplier hands
     the caller's exit payload straight back and owes nothing beside it. *)
  Lemma udepwf_st_read_pipe (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (wb : bool) :
    ⊢ udepwf_st N m pc USYS_read (read_pipe_fam (ukn_pay N))
        (FdOpen true wb FdPipe).
  Proof.
    rewrite /udepwf_st. iSplit; [ iPureIntro; reflexivity | ].
    iIntros (M pm sz fdv cw gn cs pidv) "%Hkey _ Hheap Hufd".
    iFrame "Hheap Hufd".
    iApply (sbundle_at_read_intro uslot (read_pipe_fam (ukn_pay N))
              (uvis_of_run m pc M pm sz fdv cw gn cs pidv false)
              (m !!! Regidx a0_idx) fdv
              (tf_of_arg0 m pc)
              (uvis_of_run_fd m pc M pm sz fdv cw gn cs pidv false)).
    rewrite Hkey. rewrite /fileread_in /=. by iIntros "$".
  Qed.

  (* =================================================================== *)
  (*  3.  THE CONTENT POST                                                *)
  (* =================================================================== *)
  (* ...WHICH IS PURE, and that is the whole of section 3's Pipe row as the
     tree supports it today (the header).  It is
     [PipeInvDefs.pipe_rw_ret] -- piperead's and pipewrite's shared return
     convention -- read at the caller's own [nat] request, which is the
     form a program that asked for [cap] bytes wants: either the call
     failed, or it delivered a count no larger than the request. *)
  Definition uread_pipe_ans (cap : nat) (r : mword 64) : Prop :=
    r = (mword_of_int (-1) : mword 64)
    \/ exists d : nat, r = (mword_of_int (Z.of_nat d) : mword 64)
                       /\ (d <= cap)%nat.

  Lemma uread_pipe_ans_of_ret (cap : nat) (r : mword 64) :
    fileread_ret (Z.of_nat cap) r -> uread_pipe_ans cap r.
  Proof.
    rewrite /fileread_ret /pipe_rw_ret /uread_pipe_ans.
    intros [Hm1 | (i & Hi & Hb)]; [ by left | right ].
    assert (Hmax : Z.max 0 (Z.of_nat cap) = Z.of_nat cap) by lia.
    rewrite Hmax in Hb.
    exists (Z.to_nat i). split; [ rewrite Z2Nat.id; [ exact Hi | lia ] | lia ].
  Qed.

  (* =================================================================== *)
  (*  4.  THE LEAF                                                        *)
  (* =================================================================== *)
  (* [UkRunSys.wp_uk_ecall_read_at]'s walk at the PIPE arm.  The three
     differences from the console member are all in the descriptor, exactly
     as they are for the file member: the deposit is fixed at the STATE the
     caller's handle names rather than at the low [NSTD] ledger, what goes
     down and comes back is one [UserFd.ufd] rather than the whole ledger,
     and what the caller is told about the key is the arm itself.

     NO PAYMENT ARGUMENT, and no family argument either: there is nothing
     for a caller to choose (section 2 above).  The buffer's tail is pinned
     above the WINDOW LENGTH [d] and NOT above the returned count -- the
     join between them is the owed row in the header. *)
  Lemma wp_uk_ecall_read_pipe (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (k cap : nat) (f : nat -> bv 8) (avail : nat)
      (fd : nat) (wb : bool) :
    usysno m = USYS_read ->
    (* THE DESCRIPTOR IS THE ONE THE HANDLE NAMES; a0 carries it as a C
       [int], so the reading is the signed low word *)
    bv_signed (trunc32 (m !!! Regidx a0_idx)) = Z.of_nat fd ->
    (fd < NOFILE)%nat ->
    uint (m !!! Regidx a2_idx) = Z.of_nat cap ->
    (cap <= k)%nat ->
    (* the kernel answers the SIGNED 32-bit count, so the request the caller
       made is the request file.c read only below the sign boundary *)
    (Z.of_nat cap < 2 ^ 31)%Z ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserFd.ufd (ukn_fd N) fd (FdOpen true wb FdPipe) -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k f -∗
    (∀ (h' : CpuId) (r : mword 64) (d : nat) (g : nat -> bv 8),
       ⌜ (d <= cap)%nat ⌝ -∗
       ⌜ forall j : nat, (d <= j < k)%nat -> g j = f j ⌝ -∗
       ⌜ uread_pipe_ans cap r ⌝ -∗
       UserFd.ufd (ukn_fd N) fd (FdOpen true wb FdPipe) -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a1_idx)) k g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Ha0 Hfdlt Ha2 Hcapk Hcap31 Hal.
    iIntros "#Hi Hrun Hufdh Hbuf Hcont".
    assert (Hcnt : sys_rw_count (m !!! Regidx a2_idx) = Z.of_nat cap)
      by exact (uread_count_is_cap (m !!! Regidx a2_idx) cap Ha2 Hcap31).
    assert (Hcw : bv_signed (subrange_vec_dec (m !!! Regidx a2_idx) 31 0
                             : mword 32) = Z.of_nat cap).
    { rewrite /sys_rw_count trunc32_subrange in Hcnt. exact Hcnt. }
    iPoseProof (udepwf_st_read_pipe N m pc wb) as "Hsb".
    iApply (wp_uk_ecall_read_at N h m pc (Z.of_nat cap) k f avail
              (read_pipe_fam (ukn_pay N))
              (UserFd.ufd (ukn_fd N) fd (FdOpen true wb FdPipe))
              (fun fdv => fd_st_of_key (m !!! Regidx a0_idx) fdv
                          = FdOpen true wb FdPipe)
              Hn Hcw ltac:(rewrite Nat2Z.id; exact Hcapk) Hal
              (ufd_key_agree N fd (FdOpen true wb FdPipe)
                 (m !!! Regidx a0_idx) Ha0 Hfdlt)
              with "Hi Hrun [Hsb] Hufdh Hbuf").
    { rewrite /udepwf_st /udepwf_K. iExact "Hsb". }
    iIntros (h' r d g W M' fdv' cw' cs')
      "%Hd %Hgf %Hlin %Himg %Hnf %H0 %H1 %H2 %Hkey %Hlz %Hlive
       Hufdh Hpost Hrun Hbuf".
    iDestruct (spost_at_read_elim uslot (read_pipe_fam (ukn_pay N)) W
                 (m !!! Regidx a0_idx) (m !!! Regidx a1_idx)
                 (m !!! Regidx a2_idx) (uvis_fd W) r M' fdv' cw' cs'
                 H0 H1 H2 eq_refl with "Hpost")
      as "[%Hret _]".
    (* THE ARM TELLS NOTHING ([fileread_extra_core] at [FdOpen true _
       FdPipe] is [emp]), so the post's only content is its RETURN row --
       which is the one the pipe's two functions share. *)
    rewrite Hcnt in Hret.
    rewrite Nat2Z.id in Hd.
    iApply ("Hcont" $! h' r d g with "[%] [%] [%] Hufdh Hrun Hbuf");
      [ exact Hd | exact Hgf | exact (uread_pipe_ans_of_ret cap r Hret) ].
  Qed.

  (* =================================================================== *)
  (*  5.  THE CONSUMER TEST -- THE SEAM AT sys_pipe                        *)
  (* =================================================================== *)
  (* WHAT THE TEST CAN BE, and why it is this.  The test the lane owes is
     "a program holding the read end learns the writer's bytes across the
     two ends"; the content half of that is not derivable at any tier today
     (the header), and neither is a one-process write-then-read, for the
     same reason and no other -- a pipe read's post is [emp].  What IS
     derivable, and what actually has to hold for the member above to be
     reachable by a real program, is the SEAM: the two descriptors
     [sys_pipe] hands back are handles at exactly the two states the read
     and write members case on.  [UsysMemOk.usys_pipe_ok]'s join is what
     makes the bytes in the caller's [int fd[2]] name those slots, and
     [UkRunSys.wp_uk_ecall_pipe] already spends it; this lemma is that
     leaf's post read one step further, into the two members' own premises.

     THE SECOND CALL IS NOT IN THE TEST, and cannot be: the descriptor
     arrives in the caller's BUFFER and a program has to load it into a0
     with its own instructions before the read's ecall.  So the two ends
     are handed over at the first call's continuation, where a program
     proof picks them up. *)

  (* the ledger does not move when every standard slot is open: pipe's two
     allocations both land above [NSTD], so each [ustd_after] is the
     identity. *)
  Lemma ustd_after_none (l : list fdstate) (st : fdstate) :
    fd_lowest_closed l = None -> ustd_after l st = l.
  Proof. intros H. rewrite /ustd_after H. reflexivity. Qed.

  (* the join's U-tier reading, at a ledger with no free standard slot --
     which is where any program that has not just closed a standard stream
     is, and the only case in which pipe's two arms are HANDLES rather than
     ledger writes. *)
  Lemma upipe_ends_handles (N : uk_names Σ) (l : list fdstate) (a b : nat) :
    fd_lowest_closed l = None ->
    ualloc_at (ukn_fd N) l a (FdOpen true false FdPipe) -∗
    ualloc_at (ukn_fd N) (ustd_after l (FdOpen true false FdPipe)) b
      (FdOpen false true FdPipe) -∗
    UserFd.ufd (ukn_fd N) a (FdOpen true false FdPipe) ∗
    UserFd.ufd (ukn_fd N) b (FdOpen false true FdPipe).
  Proof.
    intros Hnone.
    rewrite (ustd_after_none l (FdOpen true false FdPipe) Hnone).
    rewrite /ualloc_at Hnone.
    iIntros "[_ Ha] [_ Hb]". iFrame "Ha Hb".
  Qed.

  Lemma wp_uk_pipe_read_end (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (l : list fdstate) (f : nat -> bv 8) (avail : nat) :
    usysno m = USYS_pipe ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    fd_lowest_closed l = None ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    udepw N m pc USYS_pipe -∗
    ustd (ukn_fd N) l -∗
    ubytes (ukn_d N) (uint (m !!! Regidx a0_idx)) 8 f -∗
    (∀ (h' : CpuId) (r : mword 64) (g : nat -> bv 8),
       ((∃ a b : nat,
           ⌜ uint r = 0 /\ a <> b /\ (a < NOFILE)%nat /\ (b < NOFILE)%nat
             /\ (forall i : nat, (i < 8)%nat ->
                   g i = if (i <? 4)%nat
                         then nth_byte
                                (trunc32 (mword_of_int (Z.of_nat a)
                                          : mword 64)) i
                         else nth_byte
                                (trunc32 (mword_of_int (Z.of_nat b)
                                          : mword 64)) (i - 4)%nat) ⌝ ∗
           (* THE TWO ENDS, AT THE TWO MEMBERS' OWN PREMISES: [a] is
              [wp_uk_ecall_read_pipe]'s handle and [b] is the write
              member's. *)
           UserFd.ufd (ukn_fd N) a (FdOpen true false FdPipe) ∗
           UserFd.ufd (ukn_fd N) b (FdOpen false true FdPipe) ∗
           ustd (ukn_fd N) l)
        ∨ (⌜ uint r <> 0 ⌝ ∗ ustd (ukn_fd N) l)) -∗
       urun N h' (<[Regidx a0_idx := r]> m) (add_vec_int pc 4) avail -∗
       ubytes (ukn_d N) (uint (m !!! Regidx a0_idx)) 8 g -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hn Hal Hnone.
    iIntros "#Hi Hrun Hsb Hstd Hbuf Hcont".
    iApply (wp_uk_ecall_pipe N h m pc l f avail Hn Hal
              with "Hi Hrun Hsb Hstd Hbuf").
    iIntros (h' r g) "Harm Hrun Hbuf".
    iApply ("Hcont" $! h' r g with "[Harm] Hrun Hbuf").
    iDestruct "Harm" as "[Hok | Hbad]"; [ | iRight; iExact "Hbad" ].
    iDestruct "Hok" as (a b) "(%Hpure & Hra & Hrb & Hstd)".
    iDestruct (upipe_ends_handles N l a b Hnone with "Hra Hrb") as "[Hha Hhb]".
    (* the ledger comes home UNMOVED: both allocations landed above the
       standard streams, so [ustd_after] is the identity at each step *)
    rewrite (ustd_after_none l (FdOpen true false FdPipe) Hnone).
    rewrite (ustd_after_none l (FdOpen false true FdPipe) Hnone).
    iLeft. iExists a, b. iSplitR; [ by iPureIntro | ].
    iFrame "Hha Hhb Hstd".
  Qed.

End UkReadPipe.
