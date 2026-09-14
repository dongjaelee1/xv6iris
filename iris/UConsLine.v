(* ===================================================================== *)
(* UConsLine.v -- SH-LINE'S STATEMENTS: what the shell's line IS.          *)
(*                                                                        *)
(* The lane SH-LINE (app-echo.md, "SH-LINE RULING") makes sh's line buffer *)
(* carry "these are the consecutive next input bytes, at my position, each *)
(* tagged", and discharges [UkShFork.ushf_lexable] from it.  This file is  *)
(* PHASE 1 of that lane: every shape the rewiring has to hit, STATED and   *)
(* typechecked, and nothing rewired yet -- so a reviewer sees the target   *)
(* before the sweep, and the sweep has something to unify against.         *)
(*                                                                        *)
(*   §1  the ledger that knows fd 0 is the console          (design S4)    *)
(*   §2  sh's read leaf, with the receipt kept              (design S5)    *)
(*   §3  the [gets] loop's line invariant                   (design S5)    *)
(*   §4  the two PURE facts that discharge lexability       (design S6)    *)
(*   §5  init's LINEAR exec supply for the child it lends   (design S3)    *)
(*                                                                        *)
(* WHAT PHASE 1 FOUND, and why the rewiring is not in this file:           *)
(*                                                                        *)
(*  (a) THE EXIT PAYLOAD CROSSES exec (lane EXEC-PAY, landed).  A run's    *)
(*      payload [UkRun.ukn_pay N (-1)] lives INSIDE [UkRun.urun] and the   *)
(*      exec'd image's own run needed it, so no program could hand it     *)
(*      over: it was the KERNEL that carried it.  WITHDRAWN by lane        *)
(*      SELF-KILL, P6 -- no run carries a payload at the kill status any   *)
(*      more, [SpecKexec.exec_slot_pre]'s wands take the pay fact alone    *)
(*      and what an exec'd image must OWN crosses as [PinnedExec]'s        *)
(*      linear [Pay].  §5's supply                                         *)
(*      therefore names the POSITION only; the payload arrives at the      *)
(*      constructor wand ([PinnedExec.pex_slot]) from the seam.            *)
(*                                                                        *)
(*  (b) FD 0 IS NOT KNOWN TO BE THE CONSOLE from the leaves init has.      *)
(*      [UkRunSys.wp_uk_ecall_open]'s post existentially quantifies the    *)
(*      descriptor's TYPE ([SpecSysOpen.v:403] says why: it is [FdDevice]  *)
(*      exactly when the path walk observed a T_DEVICE inode), and that    *)
(*      leaf discards the process's post ([UkRunSys.v:785] binds           *)
(*      [spost_at] as [_]).  Switching init's two [dup]s to the tracked    *)
(*      leaf does not fix it: a dup copies whatever state the ledger       *)
(*      already records.  §1's ledger is therefore stated, and what it     *)
(*      needs is a PINNED OPEN bundle at "/console" -- [xv6_sbundle]'s     *)
(*      row 15 and [xv6_spost]'s row 15 already carry an observation       *)
(*      family and a receipt, so the shape exists; the builder and the     *)
(*      pin do not.                                                       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes ObsTrace.
Require Import RegFile.
Require Import UmodeArith.
Require Import UmodeAbi.       (* [ubyte0] -- the NUL [gets] plants *)
Require Import UsysMemOk.
Require Import UserHeap UkRun UkRunSys.
(* the address-space vocabulary the swallowed byte's FAULT arm is refuted
   in ([ush_swallow_nofault]): the permission projection and the lazy
   flag's claim, the page table the read ran at, and the writable-leaf
   predicate a copy-out needs. *)
Require Import UserPerm.       (* [perm_of] / [uperm] / [lazy_free] *)
Require Import ProcPtOwn.      (* [uptd] / [ud_um] / [proc_pt_wf] *)
Require Import UserPtTree.     (* [uva_wmapped] *)
(* THE GHOST-CLASS BINDERS' DEFINING MODULES, each IMPORTED and not merely
   reached transitively: a class named without its module in scope is a
   fresh [gFunctors -> Type] variable and the section's binders then
   resolve nothing (durable-notes, "Typeclasses and ghost-class bundling"). *)
Require Import Xv6Cameras.     (* [uartGhostG]: the console ring's cameras *)
Require Import ChildTok.       (* [ctokG]: the slot's fork arms' capacity *)
Require Import VcGen.          (* [trunc32]: how [argfd] reads a descriptor *)
Require Import FdSlots UserFd ProcGeom.
Require Import UInitFd.      (* [ufd_l0] -- the all-closed low ledger the
                               CLOSED arm of sh's entry is at *)
Require Import UserCwd UserChildren.  (* [ucwd_any] / [uch_any] -- the two
                               ghosts [UkSh.ush_pstate] carries beside the
                               ledger *)
Require Import UexecSlot UexecRet.  (* [uvis] / [uslot] -- the taint's
                               generic slot, [UkRun.urun_gen]'s premise *)
Require Import ConsoleInv.     (* [cons_window] / [cons_chain] / [CONSOLE] *)
Require Import SpecFileread.   (* [fileread_ret]: the answer's range, B3 *)
Require Import UserConsole.    (* [upos] / [ucons_stored_lb] / [ucons_pay] *)
Require Import UCodeInit UkInit.  (* init's catalogs and its exec supply's shape *)
Require Import UkSh.           (* [sh_buf] / [sh_nbuf] *)
Require Import UkShParse.      (* [ushp_no_symbols] / [ushp_tokens] *)
Require Import UkShLoop.       (* [ush_line_lexable] -- the lowest file that
                                  sees both the LINE and the LEXER *)
Require Import AppEcho.        (* [echo_line] / [star_prefix] / [disc_seg] *)
Require Import EchoOut.            (* [echoOutG]: the class [AppEcho]'s claims
                                      and its ledger are stated at (lane
                                      ECHO-OUT part 5).  It CARRIES
                                      [mono_natG], so it is the taint's one
                                      instance here too. *)
Require Import UexecSG.
Require FsImg.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  §4  THE TWO PURE FACTS THAT DISCHARGE LEXABILITY                      *)
(*                                                                        *)
(*  [UkShFork.ushf_lexable] is "every line the user could type lexes",     *)
(*  which is false and is the last thing sh rests on.  What replaces it is *)
(*  these two, applied to the line the RECEIPT says sh read.               *)
(* ===================================================================== *)

(* (1) THE LINE IS A PREFIX OF [echo_line].  Under the discipline the input
   of one power cycle is a prefix of [echo_line]*; a window that begins at
   a LINE BOUNDARY -- which is where sh's previous [gets] stopped, because
   it stopped at a '\n' -- is therefore a prefix of one [echo_line].

   STATED OVER [ins] ALONE, at [EchoDisc.disc_seg] -- the CONTENT half D3
   of the discipline, which is all this lane needs (S6).  The discipline
   itself is stronger since DISC-RATE ([EchoDisc.disc_seg'] adds the owner's
   rate bound D0/D1/D2, which is what excludes the ring overflow), and a
   supplier reaches D3 from it in one step ([EchoDisc.disc_seg'_proj], or
   [disc_proj] to the whole-history [disc_old]).  These statements say
   nothing about which stored bytes were dropped, and do not have to --
   contiguity of the STORED sequence is what [ConsoleInv.cons_window] /
   [cons_chain] carry, and contiguity of the INPUT sequence is E5's
   overflow argument, not this lane's. *)
(* LANE SH-STATE PROVED THESE, AND REPAIRED THE FIRST TWO.  As landed they
   were FALSE: nothing bounded the window to ONE line, and [q = 0] with
   [bs = echo_line ++ echo_line] satisfies the premise while
   [take 34 echo_line] is seventeen bytes long.  What is missing is exactly
   what [gets] guarantees -- it stops at the FIRST '\n', so the only
   newline in what it delivered is its LAST byte -- and that is the premise
   added below.  (The third, [ush_line_full], was true as landed and is
   unchanged.)

   THE PERIODICITY LEMMAS THIS FILE READS -- [mod_sub_self],
   [concat_replicate_lookup], [star_prefix_lookup] -- are general facts
   about [EchoDisc.star_prefix] and now live THERE, beside
   [star_prefix_snoc] (lane ECHO-PURE); they were here only so that proving
   them cost the line statements' own cone and not the discipline's. *)

(* '\n' occurs in [echo_line] ONLY as its last byte -- the fact both (1)
   and (2) turn on, decided at the literal *)
Lemma echo_line_no_early_nl_bool :
  forallb (fun j : nat =>
      negb (bool_decide (echo_line !! j = Some (Z_to_bv 8 10)))) (seq 0 16) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_line_nl_at (k : nat) :
  (k < 17)%nat -> echo_line !! k = Some (Z_to_bv 8 10) -> k = 16%nat.
Proof.
  intros Hk H. destruct (Nat.eq_dec k 16%nat) as [Hk16 | Hne];
    [ exact Hk16 | exfalso ].
  assert (Hin : In k (seq 0 16)) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) echo_line_no_early_nl_bool k Hin) as Hb.
  apply negb_true_iff in Hb. exact (bool_decide_eq_false_1 _ Hb H).
Qed.

Lemma ush_disc_line :
  forall (q : nat) (bs : list (bv 8)),
    star_prefix echo_line (concat (replicate q echo_line) ++ bs) ->
    (* ...AND THE WINDOW HOLDS AT MOST ONE LINE: the only '\n' in it is its
       last byte, which is what [gets] stopping at the first one says. *)
    (forall j : nat, (S j < length bs)%nat -> bs !! j <> Some (Z_to_bv 8 10)) ->
    bs = take (length bs) echo_line.
Proof.
  intros q bs Hsp Hnl.
  pose proof echo_line_length as Hp.
  assert (Hpos : (0 < length echo_line)%nat) by lia.
  assert (HLlen : length (concat (replicate q echo_line))
                  = (q * length echo_line)%nat)
    by apply concat_replicate_length.
  assert (Hpt : forall i : nat, (i < length bs)%nat ->
            bs !! i = echo_line !! (i `mod` 17)%nat).
  { intros i Hi.
    assert (Hi2 : (length (concat (replicate q echo_line)) + i
                   < length (concat (replicate q echo_line) ++ bs))%nat)
      by (rewrite length_app; lia).
    pose proof (star_prefix_lookup echo_line
                  (concat (replicate q echo_line) ++ bs)
                  (length (concat (replicate q echo_line)) + i)
                  Hsp Hpos Hi2) as H.
    rewrite lookup_app_r in H; [ | lia ].
    replace (length (concat (replicate q echo_line)) + i
             - length (concat (replicate q echo_line)))%nat with i in H by lia.
    rewrite H. f_equal. rewrite HLlen Hp.
    transitivity ((i + q * 17) `mod` 17)%nat;
      [ f_equal; lia | apply Nat.Div0.mod_add ]. }
  assert (Hlen : (length bs <= 17)%nat).
  { destruct (Nat.le_gt_cases (length bs) 17%nat) as [Hle | Hgt];
      [ exact Hle | exfalso ].
    assert (H16i : (16 < length bs)%nat) by lia.
    assert (H16 : bs !! 16%nat = Some (Z_to_bv 8 10))
      by (rewrite (Hpt 16%nat H16i); reflexivity).
    assert (H17 : (S 16 < length bs)%nat) by lia.
    exact (Hnl 16%nat H17 H16). }
  apply list_eq. intros i.
  destruct (decide (i < length bs)%nat) as [Hi | Hi].
  - rewrite (Hpt i Hi). rewrite lookup_take; [ | exact Hi ].
    rewrite (Nat.mod_small i 17%nat ltac:(lia)). reflexivity.
  - assert (Hn1 : bs !! i = None) by (apply lookup_ge_None_2; lia).
    assert (Hn2 : take (length bs) echo_line !! i = None)
      by (apply lookup_ge_None_2; rewrite length_take; lia).
    rewrite Hn1 Hn2. reflexivity.
Qed.

(* ...and the same at the shape the call site has it in: the cycle's
   discipline, at a history whose input ends with the window. *)
Lemma ush_disc_line_seg :
  forall (h : list mobs) (q : nat) (bs : list (bv 8)),
    disc_seg h ->
    ins h = concat (replicate q echo_line) ++ bs ->
    (forall j : nat, (S j < length bs)%nat -> bs !! j <> Some (Z_to_bv 8 10)) ->
    bs = take (length bs) echo_line.
Proof.
  intros h q bs Hd Hins Hnl.
  apply (ush_disc_line q bs); [ | exact Hnl ].
  rewrite <- Hins. exact Hd.
Qed.

(* (2) A PREFIX OF [echo_line] THAT ENDS IN '\n' IS [echo_line].  '\n' is
   [echo_line]'s last byte and occurs nowhere else in it, and '\n' is
   exactly what [gets] stops at -- so the two together say the line sh has
   in its buffer IS "echo hello world\n". *)
Lemma ush_line_full :
  forall bs0 : list (bv 8),
    let bs := bs0 ++ [Z_to_bv 8 10] in
    bs = take (length bs) echo_line ->
    bs = echo_line.
Proof.
  intros bs0. cbv zeta. intro Heq.
  pose proof echo_line_length as Hp.
  pose proof (f_equal length Heq) as HL.
  rewrite length_take Hp length_app in HL. cbn [length] in HL.
  assert (Hlast : (bs0 ++ [Z_to_bv 8 10]) !! (length bs0) = Some (Z_to_bv 8 10)).
  { rewrite lookup_app_r; [ | lia ]. rewrite Nat.sub_diag. reflexivity. }
  rewrite Heq in Hlast.
  apply lookup_take_Some in Hlast as [Hlast _].
  pose proof (echo_line_nl_at (length bs0) ltac:(lia) Hlast) as H16.
  rewrite Heq length_app. cbn [length]. rewrite H16.
  apply take_ge. rewrite Hp. lia.
Qed.

(* (3) ...AND THAT LINE LEXES, concretely.  [ushp_no_symbols] keeps
   [gettoken] in its default arm and [ushp_tokens] names the three tokens
   of "echo hello world"; both are decidable at the literal, so the proof
   is [vm_compute]/[reflexivity] and no assumption about user input
   survives.  The length is [length echo_line] = 17 -- the '\n' is
   whitespace, not a terminator, and [gets] plants the NUL past it. *)
Definition ush_echo_tokens : Prop :=
  ushp_no_symbols (length echo_line) (fun j : nat => echo_line !!! j)
  /\ ushp_tokens (length echo_line) (fun j : nat => echo_line !!! j) 0%nat
       [(0, 4); (5, 10); (11, 16)]%nat
  /\ (length [(0, 4); (5, 10); (11, 16)]%nat < 10)%nat.

(* (4) ...AND THE SHAPE THE BUFFER'S LINE IS IN WHEN IT IS DISCIPLINED is
   [UkSh.ush_line_is] -- MOVED DOWN to the program tier (lane SH-LINE 2b,
   L3), because [UkSh.ush_rest_l] is what carries it and that file is below
   this one. *)

(* ...AND THE DISCHARGE ITSELF is [UkShLoop.ush_line_lexable]: it
   quantifies over the ONE line the receipt says sh read, and
   [ush_echo_tokens] above is the closed computation that answers it.
   What stands between the two is that [ushp_no_symbols] and [ushp_tokens]
   read their bytes through a function, so the instance at
   [fun j => f (k + j)] is the instance at [fun j => echo_line !!! j] under
   [UkSh.ush_line_is]'s pointwise equality (E4's
   [UkShEcho.ush_line_toks_holds] is that transport, with the token list
   named).  BOTH NAMES ARE KEPT HERE as abbreviations, so that the
   consumers above this file are unaffected by the move down. *)
Notation ush_line_is := UkSh.ush_line_is.
Notation ush_line_lexable := UkShLoop.ush_line_lexable.

(* ...AND THE READ LEAF'S TWO NAMES, for the same reason and by the same
   rule (lane SH-LINE 2b, R1'): [ush_read_recv_leaf] and the three-armed
   answer it hands back are stated in [UkSh.v] now, because sh's [gets] --
   which is below this file -- is what runs on them.  Kept here as
   abbreviations so the discharge and the files that quote it are
   unaffected by the move. *)
Notation ush_read_recv_leaf := UkSh.ush_read_recv_leaf.
Notation ush_read_ans := UkSh.ush_read_ans.
Notation ush_gets_line := UkSh.ush_gets_line.
Notation ush_swallow_taint := UkSh.ush_swallow_taint.

(* ===================================================================== *)
(*  §4b  THE ^D REFUTATION IS [UkSh]'S NOW (lane SH-LINE 2b, R2).          *)
(*                                                                        *)
(*  [disc_no_ctrl_d] and the four pure steps under it moved DOWN, for the  *)
(*  read leaf's reason: their consumer is sh's [gets], which is below this *)
(*  file, and [UkSh.v] must not import [UConsLine] (durable-notes, the     *)
(*  heavy-import note).  Kept here as an abbreviation.                     *)
(* ===================================================================== *)
Notation disc_no_ctrl_d := UkSh.disc_no_ctrl_d.

Section UConsLine.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* the console ring's two cameras, at the narrow class a program binds
     ([UserConsole.v]'s header) *)
  Context `{!uartGhostG Σ}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* the echo claims' class (lane ECHO-OUT part 5): [AppEcho.echo_taint] and
     everything built over it is stated at [EchoOut.echoOutG] now, not at a
     bare [mono_natG]. *)
  Context `{!echoOutG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).

  (* =================================================================== *)
  (*  §1  THE LEDGER THAT KNOWS ITS FD 0                                  *)
  (*                                                                      *)
  (*  [UkSh.ush_std] is the bare ledger and says nothing about which of    *)
  (*  the three standard streams are open ([UkSh.v:4121-4133]).  What      *)
  (*  sh's read needs is one row: fd 0 is an OPEN, READABLE CONSOLE        *)
  (*  DEVICE, because that row is what selects [SpecFileread.              *)
  (*  fileread_in]'s console arm at [SpecArgfd.fd_st_of_key (xk_a W 0)]    *)
  (*  -- and the console arm is the only one that pays a receipt about     *)
  (*  input bytes.                                                        *)
  (*                                                                      *)
  (*  THE MAJOR IS [ConsoleInv.CONSOLE], not "some device": the arm is     *)
  (*  keyed by a [decide] on the major ([SpecFileread.fileread_extra]'s    *)
  (*  note), and a different major reads a different device.              *)
  (* =================================================================== *)
  Definition ush_std_cons (γfd : gname) (l : list fdstate) : iProp Σ :=
    (ustd γfd l ∗
     ⌜exists wr : bool, l !! 0%nat = Some (FdOpen true wr (FdDevice CONSOLE))⌝)%I.

  (* the bare ledger is what the rest of sh reads: the row is a pure side
     fact, so no lemma between here and the read has to carry it, and
     [UkSh.ush_std] is this one weakened. *)
  Lemma ush_std_cons_ledger (γfd : gname) (l : list fdstate) :
    ush_std_cons γfd l -∗ ustd γfd l.
  Proof. iIntros "[$ _]". Qed.

  (* =================================================================== *)
  (*  §2  SH'S READ LEAF, WITH THE RECEIPT KEPT                           *)
  (*                                                                      *)
  (*  [UkSh.ush_read_leaf] is a Hypothesis of UkSh's section, and it IS    *)
  (*  this leaf now (lane SH-LINE 2b, R1'): the read the shell runs on is  *)
  (*  the one that KEEPS the kernel's receipt.  The statement MOVED DOWN   *)
  (*  to [UkSh.v] for the only reason a statement ever moves down here --  *)
  (*  its consumer is below this file, and [UkSh.v] must not import        *)
  (*  [UConsLine] (durable-notes, the heavy-import note).  Nothing in the  *)
  (*  shape is this file's any more, so what is left is the NAME, so that  *)
  (*  the discharge above ([UShLine.ush_read_recv_leaf_holds]) and the     *)
  (*  files that quote it are unaffected by the move.                      *)
  (*                                                                      *)
  (*  WHAT IT COSTS THE CALLER: its LEDGER (the arm the kernel's row takes *)
  (*  is selected by the KEY's table, and the pure row beside it is        *)
  (*  [UkSh.ush_fd0p] -- so the leaf answers on BOTH of that row's arms    *)
  (*  and [gets] does not case split) and its POSITION                     *)
  (*  ([UserConsole.upos] at the cursor it believes the token stands at).  *)
  (*  What it hands back is one of THREE things, and which one is not the  *)
  (*  caller's choice: the WINDOW, the MINUS ONE (killed, or fd 0 shut --  *)
  (*  lane CLOSED-READ), or the TAINT.  [UkSh.ush_read_ans]'s own header   *)
  (*  is what says which is which.                                        *)
  (*                                                                      *)
  (*  THE SLACK IS GONE (lane CONS-ROWS spent).  The call asks for [cap]   *)
  (*  bytes into a buffer of [k], and [cap <= k] is all that relates them: *)
  (*  the copy-out reason used to need a byte to spare, because            *)
  (*  [ConsoleInv.cons_swallow]'s fault arm is stated at [dst + dd] and a  *)
  (*  verified reader refutes it only where it OWNS the byte               *)
  (*  ([UkRunSys.uk_read_nofault]).  B1 is what makes that byte redundant: *)
  (*  at [dd = cap] the cursor moved by exactly [dd], so the swallow is on *)
  (*  its LEFT arm and there is nothing to refute.  The window's           *)
  (*  [⌜dd <= cap⌝ -∗] guard is gone with it -- the discharge derives the  *)
  (*  bound from row 5's [SpecFileread.fileread_ret] once the [r = -1]     *)
  (*  alternative has been routed to the leaf's own minus-one arm.        *)
  (*                                                                      *)
  (*  THE COUNT IS THE REQUEST, AND [Z.of_nat cap < 2 ^ 31] IS WHAT SAYS   *)
  (*  SO (lane CONS-ROWS).  The kernel's rows are stated at the count the  *)
  (*  trapframe's argument 2 reads as a 32-bit INT                        *)
  (*  ([SpecSysRead.sys_rw_count]), and [uint a2 = Z.of_nat cap] pins that *)
  (*  to [cap] only below the sign boundary -- above it the kernel reads a *)
  (*  different (possibly negative) request and the rows are about that   *)
  (*  one.  A caller asking for a whole 2 GB in one read() gets the weaker *)
  (*  contract; every reader in this tree asks for one byte.              *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §3  THE [gets] LOOP'S LINE INVARIANT IS [UkSh]'S NOW                 *)
  (*      (lane SH-LINE 2b, R2).                                           *)
  (*                                                                       *)
  (*  [ush_gets_line] is what [UkSh.wp_ksh_gets_loop] carries round its     *)
  (*  cycle, so it has to be stated where that walk is.  Moved DOWN for the *)
  (*  read leaf's reason; kept here as an abbreviation.                     *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §3b  THE TWO ROUNDS' READINGS OF THE SWALLOWED BYTE                 *)
  (* =================================================================== *)

  (* THE COPY-OUT FAULT, ELIMINATED (lane SH-LINE 2b, L1; lane LAZY-FLAG's
     deliverable).  [ConsoleInv.cons_swallow]'s reason is "[C('D')] with
     nothing delivered, OR the copy-out faulted at this destination", and
     the second is a statement about the READER's own address space.  A
     verified program refutes it from what it already owns: [ubytes] puts
     the destination in the permission map's writable set, and the lazy
     flag at [false] turns a writable page of the PROJECTION into a real
     user leaf with V, U and W ([UkRunSys.uk_read_nofault]).  What is left
     is the [False]-instantiated arm the leaf above is stated at.

     THE THREE PURE PREMISES ARE ROW 5's THREE CONJUNCTS
     ([UexecExecInst]'s read row, with [UkRunSys.wp_uk_ecall_read_recv]'s
     [⌜uvis_lazy W = false⌝] turning the row's implication into
     [lazy_free]), so the discharge applies this with the [∃ P] in hand. *)
  Lemma ush_swallow_nofault (N : uk_names Σ) (cn : cons_names)
      (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z)
      (dst : mword 64) (k d : nat) (f : nat -> bv 8) (P : uptd)
      (sl : list (list mobs * bv 8)) (dc : nat) :
    (d < k)%nat ->
    ProcPtOwn.proc_pt_wf P ->
    perm_of (ud_um P) sz = pmv ->
    lazy_free (ud_um P) sz ->
    uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗
    ubytes (ukn_d N) (uint dst) k f -∗
    ucons_swallow cn
      (~ UserPtTree.uva_wmapped P (uint (add_vec_int dst (Z.of_nat d))))
      sl d dc -∗
    ucons_swallow cn False sl d dc.
  Proof.
    intros Hdk Hwf Hpm Hlf. iIntros "Hheap Hbs Hsw".
    iDestruct (uk_read_nofault (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz
                 (DfracOwn 1) dst k d f P Hdk Hwf Hpm Hlf
                 with "Hheap Hbs") as %Hmap.
    iApply (ucons_swallow_mono cn _ False sl d dc with "Hsw").
    intro Hno. exact (Hno Hmap).
  Qed.

  (* =================================================================== *)
  (*  §6  THE THREE-ARM LEDGER SH'S ENTRY TAKES -- COLLAPSED (lane          *)
  (*      SH-LINE 2b, L4).                                                  *)
  (*                                                                        *)
  (*  It is [UkSh.ush_std l] beside [UkSh.ush_fd0 T l] now, and the three    *)
  (*  arms are [UkSh.ush_fd0p]'s two plus the taint.  The pure row moved     *)
  (*  DOWN for SH-OPEN's reason: sh's console PREAMBLE reopens a closed      *)
  (*  fd 0, so the row its read runs on is the one the preamble LEFT, and    *)
  (*  the loop head ([UkSh.ush_loop_head]) has to carry it -- which it       *)
  (*  cannot do from a file above [UkSh.v].  §1's [ush_std_cons] is the      *)
  (*  CONSOLE arm, which is what the read leaf above takes.                  *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §7  SH'S PER-TURN STATE, WITH THE POSITION -- LANDED.                 *)
  (*                                                                        *)
  (*  [UkSh.ush_pstate] carries it: the ledger, the cwd, the children set    *)
  (*  and -- LAST -- [UkSh.ush_pos], the program's half of the console       *)
  (*  position pair (SH-LINE phase 2a).  Nothing is left here.               *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §8  THE TAG'S READING -- MOVED DOWN (lane SH-LINE 2b, L4).            *)
  (*                                                                        *)
  (*  It is [UkSh.ush_tag_law T] now, for §10's reason: [UkSh.ush_rest_l]    *)
  (*  is what consumes what the law produces, and that file is below this    *)
  (*  one.  §11's [Pay] below is what carries it across the exec.            *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §9  THE TAINT'S GENERIC CONTINUATION -- MOVED DOWN (lane SH-OPEN).   *)
  (*                                                                      *)
  (*  It is [UkSh.ush_gen_slot] / [UkSh.ush_gen_run] now, because the      *)
  (*  first walk that needs it is sh's CONSOLE PREAMBLE, which is below    *)
  (*  this file: sh's open of "console" is PINNED, so under the taint      *)
  (*  there is no bundle for row 15 and the preamble must be able to stop  *)
  (*  walking sh's code.  The two statements were textually identical;     *)
  (*  this file's copies are gone and its own statements take UkSh's.      *)
  (* =================================================================== *)

  (* =================================================================== *)
  (*  §10  WHAT REPLACES [UkShFork.ushf_lexable]                          *)
  (*                                                                      *)
  (*  [ushf_lexable] is "every line the user could type lexes", which is   *)
  (*  false.  What the command loop hands its body instead is this: for    *)
  (*  the line in the buffer at [k], either the FIRST NUL at or after [k]  *)
  (*  ends a line that is exactly [echo_line] ([ush_line_is], hence        *)
  (*  [ush_line_lexable]), or the taint -- and on the taint the body's     *)
  (*  continuation is §9's.                                               *)
  (*                                                                      *)
  (*  STATED OVER THE FIRST NUL rather than over a given [len] because     *)
  (*  that is what [UkShFork.ushf_first_nul] produces: the body derives    *)
  (*  its own [len] from the loop's "some byte at or after [k] is NUL",    *)
  (*  and the line fact has to hold at the [len] it derived.               *)
  (* =================================================================== *)
  (*  IT IS [UkSh.ush_rest_line T f k] NOW, and it rides as a premise of    *)
  (*  [UkSh.ush_rest_l] -- the obligation [UkShFork.ushf_rest_of_body]       *)
  (*  proves.  Moved DOWN because its consumer is the command loop's body.   *)

  (* =================================================================== *)
  (*  §11  THE LINEAR [Pay] THAT CROSSES THE EXEC                         *)
  (*                                                                      *)
  (*  [PinnedExec.pinned_exec_bundle]'s [Pay] is the ONE linear resource   *)
  (*  an exec'ing process can put in the exec'd image's slot, and this is  *)
  (*  what init puts there for sh: sh's own entry payload                  *)
  (*  ([UInitSh.sh_pay], persistent), the tag's reading (§8, persistent)   *)
  (*  and the POSITION (linear, minted fresh per child just before the     *)
  (*  fork).  The exit payload is NOT here -- it arrives at the            *)
  (*  constructor wand from the kernel's own payment (EXEC-PAY; §5's       *)
  (*  note).                                                              *)
  (*                                                                      *)
  (*  [Pay] is a parameter because [UInitSh.sh_pay] is stated above this   *)
  (*  file's altitude; what this names is the SHAPE the two extra          *)
  (*  conjuncts ride in.                                                   *)
  (*                                                                      *)
  (*  ...AND THE LEASE RIDES HERE TOO (lane KILL-PAY, K4(a)).  sh used to  *)
  (*  be handed the console reader token INSIDE its exit payload, which    *)
  (*  the run carried ([UkRun.urun]'s own row).  That row is GONE (lane    *)
  (*  SELF-KILL, P6), so the payload has nowhere to ride and the token     *)
  (*  crosses on the linear [Pay] beside the                               *)
  (*  position, landing in [UkSh.ush_at].  A THIRD conjunct and not a      *)
  (*  reshaping of the second: the position is what a read's receipt is    *)
  (*  keyed at and the lease is what pays for the read.                    *)
  (* =================================================================== *)
  Definition ush_exec_pay (Pay : iProp Σ) (cn : cons_names) (T : iProp Σ)
      (γp : gname) (n : nat) : iProp Σ :=
    (Pay ∗ ush_tag_law T ∗ upos γp n ∗ ucons_pay cn γp T (-1))%I.


End UConsLine.
