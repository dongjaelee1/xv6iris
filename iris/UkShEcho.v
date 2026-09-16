(* ===================================================================== *)
(* UkShEcho.v -- E4 SH-ECHO, THE u-TIER HALF: sh's forked child at the    *)
(* ONE command the disciplined line spells, and the PINNED exec supply    *)
(* its EXEC arm runs on.                                                  *)
(*                                                                        *)
(* WHY A SECOND RUNCMD.  [UkShRun.wp_kshr_runcmd] is proved by induction  *)
(* over an ARBITRARY [ushcmd], so its EXEC arm needs an exec bundle at an  *)
(* ARBITRARY argv -- which is exactly what no pin can supply, and why it   *)
(* takes [UkRun.uxsup_at], the generic (tainted) supply, at every key.     *)
(* Under the discipline sh's buffer holds ONE line ([UConsLine.           *)
(* ush_line_is]: "echo hello world\n"), so the command is ONE value and    *)
(* the arm can be respecialised at it.  This file states that value and    *)
(* the specialised arm; [UShEcho.v] PAYS the supply out of the echo        *)
(* application's claim that /echo is [ElfUser.echo_elf].                   *)
(*                                                                        *)
(* THE SPLIT IS INIT'S, one level down.  [UkInit.init_exec_sup] is the     *)
(* u-tier DEFINITION of init's pinned supply (a wand from init's own       *)
(* persistent image facts to [UkRun.udepw_at] at ONE working directory)    *)
(* and [UInitSh.init_exec_sup_of_sh_slot] is its payment above the         *)
(* kernel's instance.  [sh_exec_sup_echo] below is the first half at sh,   *)
(* and [UShEcho.sh_exec_sup_of_echo_slot] the second.                      *)
(*                                                                        *)
(* PHASE 1.  Everything a phase-2 proof will have to produce is STATED     *)
(* here, in the vocabulary the walks already speak, and the closed facts   *)
(* about the literal line are PROVED (that is what keeps the statements    *)
(* from being about nothing).  Nothing is [Admitted] and nothing is a      *)
(* placeholder premise: the four obligations below are [Prop]s whose       *)
(* bodies are the lemma statements, on [UConsLine.v]'s mould.              *)
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
Require Import Xv6Cameras.     (* [uartGhostG]: the position pair's cameras *)
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import UserPerm.
Require Import UserHeap UkRun UkRunLeaf UkRunSys.
Require Import UkRunExecRef.  (* [udepw_at_refR] / [wp_uk_ecall_exec_at_cwd_refR]: the exec refund at the supplier's shape (step 4) *)
Require Import UkRunMem.   (* [uoff_c8]: the c.ld offset the 0xce load names *)
Require Import FdSlots UserFd UserCwd UserChildren.
Require Import UCodeShK.
Require Import UCodeShP.
Require Import UkSh.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import LineWords.        (* [wl_line] / [wl_toks] / [wl_off]      *)
Require Import UkShWords.        (* the lexer at an ARBITRARY word list *)
Require Import UkShRun.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShMain.
Require Import UkShFork.
Require Import UConsLine.        (* [ush_line_is]: the buffer IS [echo_line] *)
Require Import EchoDisc.         (* [echo_line], [sb], [nlb] *)
Require Import FsImg.            (* [ROOTINO] -- the cwd the pin resolves at *)
Require Import UexecSG.          (* [uexecSG] / [uprogSG]: the deposit class *)
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UsysMemOk.   (* [USYS_exit] -- the tear-down's bundle row *)
Local Open Scope Z_scope.
Import Defs.

(* a failing tactic in a whole-function WP looks like a hang: Rocq prints
   the entire goal, and a [urun]-altitude goal is enormous (durable-notes,
   "The dev loop"). *)
Set Printing Depth 40.

(* ===================================================================== *)
(* S1  THE LINE'S COMMAND.                                                *)
(*                                                                        *)
(* THE PARSE IS FUNCTIONAL, and it always was: [UkShParseCmd.             *)
(* wp_kshp_parser] takes the token list as a PREMISE                      *)
(* ([UkShParse.ushp_tokens len f 0 toks]) and returns the node at THAT     *)
(* list ([ushp_tree s0 p (UshpExec toks)]), so there is no determinacy     *)
(* lemma to prove about the parser -- the caller names the tokens.  What   *)
(* the disciplined branch owes is therefore that the line LEXES: it        *)
(* carries no symbol byte and its maximal non-blank runs are the token     *)
(* list.  That is [UConsLine.ush_echo_tokens].                             *)
(*                                                                        *)
(* AND THAT IS NOT A PROPERTY OF THESE SEVENTEEN BYTES.  It used to be     *)
(* proved by [vm_compute] at the literal, which is an answer worth exactly *)
(* one command line.  [UkShWords.v] proves it for an ARBITRARY list of     *)
(* words joined by single spaces and closed by a newline, and what is left *)
(* here is the INSTANCE: [echo_ws] names the three words, two closed       *)
(* computations say the literal IS their join and what offsets they land   *)
(* at, and everything else is [UkShWords]' general lemmas applied.         *)
(* ===================================================================== *)

(* THE TOKEN LIST AND THE TWO BOUNDARY ACCESSORS ARE THE WORD LIST'S.
   [EchoDisc.echo_line] IS [LineWords.wl_line EchoDisc.echo_ws], so the
   tokens sh's lexer finds are [wl_toks] of those words, argument [i]
   starts where the join puts word [i], and it is as long as that word.
   Nothing below reads a number off this line. *)
Definition echo_toks : list (nat * nat) := wl_toks echo_ws.

Definition echo_off (i : nat) : nat := wl_off 0%nat echo_ws i.

Definition echo_alen (i : nat) : nat := length (echo_ws !!! i).

(* the one fact about THESE words the lexer's caller needs and the general
   statement cannot give it: there are fewer of them than sh's MAXARGS *)
Lemma echo_toks_lt10 : (length echo_toks < 10)%nat.
Proof. rewrite /echo_toks wl_toks_length. vm_compute. lia. Qed.

(* [echo_ws_wf], [echo_ws_length] and [echo_ws_at] are [EchoDisc]'s, with
   the word list they are about. *)

(* AN ARGUMENT'S BYTES ARE INSIDE THE LINE -- [LineWords.wl_off_lt_line] at
   these words.  A caller that used to bound [echo_off i + j] by case
   analysis over the three offsets gets it from this. *)
Lemma echo_off_lt (i j : nat) :
  (i < length echo_ws)%nat -> (j <= echo_alen i)%nat ->
  (echo_off i + j < length echo_line)%nat.
Proof.
  intros Hi Hj. rewrite /echo_off echo_line_words.
  exact (wl_off_lt_line echo_ws i _ j (echo_ws_at i Hi) Hj).
Qed.

(* ...AND THE TWO NUMBERS THAT ARE NOT ABOUT THE ARGUMENTS.  The first
   word starts at the line's base, which is true of every line
   ([LineWords.wl_off_0]); the COMMAND NAME is four bytes, which stays
   four whatever the arguments are, because the program run is /echo.
   The offsets and lengths of the arguments themselves are gone: nothing
   above reads one any more. *)
Lemma echo_off_0 : echo_off 0%nat = 0%nat.
Proof. by rewrite /echo_off wl_off_0. Qed.

Lemma echo_alen_0 : echo_alen 0%nat = 4%nat.
Proof. by vm_compute. Qed.

Lemma echo_toks_lookup (i : nat) :
  (i < length echo_ws)%nat ->
  echo_toks !! i = Some (echo_off i, (echo_off i + echo_alen i)%nat).
Proof.
  intro Hi. rewrite /echo_toks /echo_off /echo_alen /wl_toks.
  exact (wl_toks_at_lookup echo_ws 0%nat i _ (echo_ws_at i Hi)).
Qed.

(* ---- the line lexes: [UkShWords.v]'s two general lemmas, instantiated - *)

Lemma ush_echo_tokens_holds : UConsLine.ush_echo_tokens.
Proof.
  rewrite /UConsLine.ush_echo_tokens.
  assert (Hlen : length echo_line = length (wl_line echo_ws))
    by (by rewrite echo_line_words).
  assert (Hf : forall j : nat, (j < length echo_line)%nat ->
            echo_line !!! j = wl_line echo_ws !!! j)
    by (intros j _; by rewrite echo_line_words).
  split_and!.
  - exact (wl_no_symbols echo_ws (fun j : nat => echo_line !!! j)
             (length echo_line) echo_ws_wf Hlen Hf).
  - replace [(0, 4); (5, 10); (11, 16)]%nat with echo_toks
      by (rewrite /echo_toks; vm_compute; reflexivity).
    exact (wl_tokens echo_ws (fun j : nat => echo_line !!! j)
             (length echo_line) echo_ws_wf Hlen Hf).
  - simpl. lia.
Qed.

(* ---- the determinacy the DISCIPLINED buffer needs -------------------- *)
(* [ush_echo_tokens] is about [echo_line] read through
   [fun j => echo_line !!! j]; the command loop hands its body the line
   through [fun j => f (k + j)].  [UConsLine.ush_line_is] says the two
   agree pointwise below [len], and [ushp_no_symbols] / [ushp_tokens] read
   their bytes only there -- so this is a TRANSPORT and not a second
   computation.  It is [UConsLine.ush_line_lexable] with the token list
   NAMED, which is what the specialised arm needs and the existential form
   cannot give. *)
Definition ush_line_toks : Prop :=
  forall (f : nat -> bv 8) (k len : nat),
    UConsLine.ush_line_is f k len ->
    len = length echo_line
    /\ ushp_no_symbols len (fun j : nat => f (k + j)%nat)
    /\ ushp_tokens len (fun j : nat => f (k + j)%nat) 0%nat echo_toks.

(* ---- the transport, which is all the determinacy costs --------------- *)
(* The four [ushp_*_ext] lemmas this used to carry say only that the lexer
   reads [f] inside its window and nowhere else -- nothing about echo, and
   nothing about any particular line -- so they live in [UkShWords.v] now,
   beside the general tokenization they exist to move. *)

(* ...and the determinacy itself: ONE transport of the lexing above. *)
Lemma ush_line_toks_holds : ush_line_toks.
Proof.
  intros f k len [Hlen Hf].
  split; [ exact Hlen | ].
  subst len.
  destruct ush_echo_tokens_holds as (Hns & Htk & _).
  assert (Hext : forall j : nat, (j < length echo_line)%nat ->
            echo_line !!! j = f (k + j)%nat)
    by (intros j Hj; symmetry; exact (Hf j Hj)).
  split.
  - exact (ushp_no_symbols_ext (length echo_line) _ _ Hext Hns).
  - exact (ushp_tokens_ext (length echo_line) _ _ Hext 0%nat echo_toks Htk).
Qed.

(* ---- the command, as a VALUE ---------------------------------------- *)
(* [UkShMain.ush_cmd_of_ushp] converts the parser's node into the runner's
   tree at [UExec (UkShMain.ush_args s0 g toks)], where [g] is the line
   AFTER [nulterminate]'s cut ([ushp_nulfold toks (ushp_ext len f)]).  At
   [toks := echo_toks] that value is three [UserHeap.uarg]s and nothing
   else, and this is it. *)
Definition echo_cmd (s0 : Z) (g : nat -> bv 8) : ushcmd :=
  UExec (UkShMain.ush_args s0 g echo_toks).

Lemma echo_cmd_simple (s0 : Z) (g : nat -> bv 8) : ush_simple (echo_cmd s0 g).
Proof. exact I. Qed.

Lemma echo_cmd_ht (s0 : Z) (g : nat -> bv 8) : ush_ht (echo_cmd s0 g) = 1%nat.
Proof. reflexivity. Qed.

Lemma echo_cmd_args_length (s0 : Z) (g : nat -> bv 8) :
  length (UkShMain.ush_args s0 g echo_toks) = length echo_ws.
Proof.
  rewrite UkShMain.ush_args_length /echo_toks. exact (wl_toks_length echo_ws).
Qed.

Lemma echo_cmd_args_lookup (s0 : Z) (g : nat -> bv 8) (i : nat) :
  (i < length echo_ws)%nat ->
  UkShMain.ush_args s0 g echo_toks !! i
  = Some (UArg (s0 + Z.of_nat (echo_off i)) (echo_alen i)
            (fun j : nat => g (echo_off i + j)%nat)).
Proof.
  intro Hi.
  rewrite (UkShMain.ush_args_lookup s0 g echo_toks i
             (echo_off i, (echo_off i + echo_alen i)%nat)
             (echo_toks_lookup i Hi)).
  cbn [fst snd].
  replace (echo_off i + echo_alen i - echo_off i)%nat with (echo_alen i)
    by lia.
  reflexivity.
Qed.

(* ---- the argv BYTES, as a pure premise ------------------------------- *)
(* What the exec at the bottom of the arm needs of the line is not the
   whole of [ush_line_is] but three strings and their NULs: [nulterminate]
   has cut the line at each token's end, so the byte function the tree is
   built over spells "echo\0", "hello\0", "world\0" at the three offsets.
   Stated over the CUT function [g] (the tree's own), because that is the
   one the node's [ustr]s are indexed by. *)
Definition echo_argv_bytes (g : nat -> bv 8) : Prop :=
  (forall (i j : nat), (i < length echo_ws)%nat -> (j < echo_alen i)%nat ->
     g (echo_off i + j)%nat = echo_line !!! (echo_off i + j)%nat)
  /\ (forall i : nat, (i < length echo_ws)%nat ->
        g (echo_off i + echo_alen i)%nat = ubyte0).

(* ...and it holds of the disciplined line's cut.  [ushp_nulfold] writes a
   NUL at each token's END and leaves every other index alone, and the
   three ends [4], [10], [16] are outside all three tokens -- so the
   strings are the line's own bytes and the terminators are the cut's. *)
Definition echo_argv_bytes_of_line : Prop :=
  forall (f : nat -> bv 8) (k len : nat),
    UConsLine.ush_line_is f k len ->
    echo_argv_bytes
      (ushp_nulfold echo_toks (ushp_ext len (fun j : nat => f (k + j)%nat))).

(* ...AND THE CUT IS NOT A PROPERTY OF THESE OFFSETS EITHER.  It used to
   be three stores at 4, 10 and 16, discharged by [reflexivity] at each.
   [UkShWords.wl_cut_in] / [wl_cut_end] say the same thing at an arbitrary
   word list -- inside word [i] the cut is transparent, at its END it is
   the terminator -- so this is two applications and the arithmetic that
   keeps every index inside [ushp_ext]'s window. *)
Lemma echo_argv_bytes_of_line_holds : echo_argv_bytes_of_line.
Proof.
  intros f k len [Hlen Hf].
  split.
  - intros i j Hi Hj.
    pose proof (echo_ws_at i Hi) as Hw.
    assert (Hlt : (wl_off 0%nat echo_ws i + j < len)%nat).
    { rewrite Hlen echo_line_words.
      exact (wl_off_lt_line echo_ws i _ j Hw (Nat.lt_le_incl _ _ Hj)). }
    rewrite /echo_off /echo_toks
      (wl_cut_in echo_ws (fun x : nat => f (k + x)%nat) len i _ j Hw Hj Hlt).
    exact (Hf _ Hlt).
  - intros i Hi.
    pose proof (echo_ws_at i Hi) as Hw.
    rewrite /echo_off /echo_alen /echo_toks.
    exact (wl_cut_end echo_ws (fun x : nat => f (k + x)%nat) len i _ Hw).
Qed.

Section UkShEcho.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  (* the position pair's cameras -- [UkSh.ush_pstate]'s fourth conjunct *)
  Context `{!uartGhostG Σ}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  (* the numbers a verified program admits (lane SUPPLY-SPLIT); a SECTION
     hypothesis exactly as in [UkShRun]/[UkShFork], so no statement below
     names it *)
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.

  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  THE NODE, ADDRESSED.  Three accessors so that no consumer of the     *)
  (*  tree has to fight [UkShMain.ush_args]'s [map] again: argument [i]'s  *)
  (*  pointer word, its string, and the NULL cap.  Everything is           *)
  (*  [DfracDiscarded], so every one of them is free to take.              *)
  (* =================================================================== *)
  Lemma echo_cmd_str (gd : gname) (t s0 : Z) (g : nat -> bv 8) (i : nat) :
    (i < length echo_ws)%nat ->
    ush_cmd gd t (echo_cmd s0 g) -∗
    ⌜ 0 < s0 + Z.of_nat (echo_off i) < 2 ^ 38 ⌝ ∗
    ustr gd DfracDiscarded (s0 + Z.of_nat (echo_off i)) (echo_alen i)
      (fun j : nat => g (echo_off i + j)%nat).
  Proof.
    intro Hi. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(_ & _ & #Hs)".
    iDestruct (big_sepL_lookup _ (UkShMain.ush_args s0 g echo_toks) i _
                 (echo_cmd_args_lookup s0 g i Hi) with "Hs") as "#Hx".
    rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
    iDestruct "Hx" as "[%Hr #Hstr]".
    iSplit; [ iPureIntro; exact Hr | iExact "Hstr" ].
  Qed.

  Lemma echo_cmd_word (gd : gname) (t s0 : Z) (g : nat -> bv 8) (i : nat) :
    (i < length echo_ws)%nat ->
    ush_cmd gd t (echo_cmd s0 g) -∗
    uwordq gd DfracDiscarded (t + 8 + 8 * Z.of_nat i)
      (mword_of_int (s0 + Z.of_nat (echo_off i))).
  Proof.
    intro Hi. iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(#Hv & _ & _)".
    iDestruct (uargv_acc gd (t + 8) (UkShMain.ush_args s0 g echo_toks) i _
                 (echo_cmd_args_lookup s0 g i Hi) with "Hv") as "[[#Hw _] _]".
    cbn [ua_ptr]. iExact "Hw".
  Qed.

  Lemma echo_cmd_cap (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    ush_cmd gd t (echo_cmd s0 g) -∗
    uwordq gd DfracDiscarded (t + 8 + 8 * Z.of_nat (length echo_ws))
      (mword_of_int 0).
  Proof.
    iIntros "#Hc".
    iDestruct (ush_cmd_exec with "Hc") as "(_ & #Hn & _)".
    rewrite /ush_ptr echo_cmd_args_length. iExact "Hn".
  Qed.

  Lemma echo_cmd_addr (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    ush_cmd gd t (echo_cmd s0 g) -∗ ⌜ 0 < t < 2 ^ 38 /\ t mod 8 = 0 ⌝.
  Proof. iIntros "#Hc". iApply (ush_cmd_addr with "Hc"). Qed.

  (* argv[0], in the two shapes runcmd's EXEC arm reads it: the POINTER
     SLOT the [c.ld a0,8(s1)] at 0xce loads, and the STRING the diagnostic
     tail prints.  [UkShRun.ush_argv0] is the generic form; at [echo_cmd]
     the [match] on the vector is already decided. *)
  Lemma echo_cmd_argv0 (gd : gname) (t s0 : Z) (g : nat -> bv 8) :
    ush_cmd gd t (echo_cmd s0 g) -∗
    ush_ptr gd (t + 8) (s0 + Z.of_nat (echo_off 0%nat))
    ∗ ush_str gd (UArg (s0 + Z.of_nat (echo_off 0%nat)) (echo_alen 0%nat)
                    (fun j : nat => g (echo_off 0%nat + j)%nat)).
  Proof.
    iIntros "#Hc". iSplit.
    - iDestruct (echo_cmd_word gd t s0 g 0%nat ltac:(exact echo_ws_pos) with "Hc") as "#Hw".
      assert (E : t + 8 + 8 * Z.of_nat 0%nat = t + 8) by lia.
      iEval (rewrite E) in "Hw".
      rewrite /ush_ptr. iExact "Hw".
    - iDestruct (echo_cmd_str gd t s0 g 0%nat ltac:(exact echo_ws_pos) with "Hc")
        as "[%Hr #Hs]".
      rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
      iSplit; [ iPureIntro; exact Hr | iExact "Hs" ].
  Qed.

  (* =================================================================== *)
  (* S2  THE PINNED EXEC SUPPLY, at sh's own key.                         *)
  (*                                                                      *)
  (* [UkRun.uxsup_at] is the exec bundle at EVERY key; a PINNED bundle is  *)
  (* about a PATH, and a relative path names a file only against the       *)
  (* directory it is resolved from -- so what a pinned supplier can pay is *)
  (* [UkRun.udepw_at] at ONE cwd, and the leaf that takes it is            *)
  (* [UkRunSys.wp_uk_ecall_exec_at_cwd] ([UkInit.wp_kinit_exec] is the     *)
  (* landed call site).  This is init's [init_exec_sup_pos] at sh.         *)
  (*                                                                      *)
  (* WHAT IT IS LENT AND WHAT IT READS.  [udepw_at] hands the supplier the *)
  (* key's two authorities and takes them back: the bundle owes            *)
  (* [SpecSysExec.exec_path_of M pv pl] and                                *)
  (* [SpecSysExec.exec_args_of M av na alen afun], both readings of the    *)
  (* image [M] at the key, and the node is what answers them -- the argv   *)
  (* words at [t+8], the NULL cap, and the three [ustr]s, all              *)
  (* [DfracDiscarded] and so all readable off the lent [UserHeap.uheap].   *)
  (*                                                                      *)
  (* THE CHILD'S PAYLOAD IS TRIVIAL.  The process that execs is the one sh *)
  (* FORKED, and [UkFork.wp_uk_ecall_fork_any]'s child arm gives the       *)
  (* equation ([UkRun.ukn_triv]); so [Q := fun _ => True] throughout and   *)
  (* the taint arm's generic slot is [UexecExecMint.uslot_mint_all] at it. *)
  (* =================================================================== *)
  (* AT THE CHILD'S PAID PAYLOAD (lane IO-LEAF, step 4): the process that
     execs is the one sh FORKED, and its payload is the one sh CHOSE at the
     fork ([UkShFork.ushf_wq] -- the credential after echo's block, or the
     block still owed) -- so [Q] is a parameter, and so is what the child
     was LENT ([Cr], the block credential the paid entry is built on).
     [UShEcho.sh_exec_sup_of_echo_slot] is the one discharge. *)
  Definition sh_exec_sup_echo (Q : Z -> iProp Σ) (Cr : iProp Σ) : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64)
          (s0 t : Z) (g : nat -> bv 8) (ld : list fdstate),
          ⌜ ukn_pay N' = Q ⌝ -∗
          (* argv[0]'s string, which is the PATH exec resolves... *)
          ⌜ m !!! Regidx a0_idx = (mword_of_int s0 : mword 64) ⌝ -∗
          (* ...and [&argv[0]], which is the VECTOR it reads *)
          ⌜ m !!! Regidx a1_idx = (mword_of_int (t + 8) : mword 64) ⌝ -∗
          ⌜ echo_argv_bytes g ⌝ -∗
          (* ...AND THE CHILD'S fd 1 IS THE CONSOLE (step 4): echo's paid
             entry writes on it, and the fact is about the TABLE the exec
             channel carries verbatim -- so the ledger fragment goes in
             here, where the deposit meets the table's authority *)
          ⌜ UkSh.ush_fd1p ld ⌝ -∗
          UserFd.ustd (ukn_fd N') ld -∗
          ush_cmd (ukn_d N') t (echo_cmd s0 g) -∗
          Cr -∗
          (* AT THE REFUND THE SUPPLIER NAMES ([UkRunExecRef.udepw_at_refR]):
             a failed exec hands the ledger fragment and the lend back
             whole, which is what the diagnostic's exit pays with *)
          udepw_at_refR N' m pc FsImg.ROOTINO
            (UserFd.ustd (ukn_fd N') ld ∗ Cr)))%I.

  Global Instance sh_exec_sup_echo_persistent Q Cr :
    Persistent (sh_exec_sup_echo Q Cr).
  Proof. rewrite /sh_exec_sup_echo. apply _. Qed.

  (* THE CWD-INDEXED EXEC STUB.  [UkShRun.wp_kshr_exec] takes the ∀-cwd
     deposit [UkRun.udepw]; a pinned supply cannot pay that (its bundle
     answers at ONE cwd), so the specialised arm needs sh's exec stub at
     the indexed deposit and the program's own half of its working
     directory beside it -- [UkInit.wp_kinit_exec] is the same lemma at
     init's three pcs.  Everything else is [wp_kshr_exec] verbatim: a
     successful exec never comes back, so the only continuation is -1. *)
  Definition wp_kshr_exec_at_cwd (R : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (c : Z) (avail : nat),
      ⊢ shk_code (ukn_t N) -∗
        urun N h m (mword_of_int ShSyms.exec) avail -∗
        UserCwd.ucwd (ukn_cwd N) c -∗
        udepw_at_refR N
          (<[Regidx (mword_of_int 17 : mword 5) := (mword_of_int 7 : mword 64)]> m)
          (mword_of_int 0xcc0) c R -∗
        (∀ h' : CpuId,
           UserCwd.ucwd (ukn_cwd N) c -∗
           (* ...AND THE REFUND (step 4), at the shape the supplier named
              ([UkRunExecRef.wp_uk_ecall_exec_at_cwd_refR]) *)
           R -∗
           urun N h'
             (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                (<[Regidx (mword_of_int 17 : mword 5)
                   := (mword_of_int 7 : mword 64)]> m))
             (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) avail -∗
           WP (Loop : expr riscv_lang)) -∗
        WP (Loop : expr riscv_lang).

  (* =================================================================== *)
  (* THE SPECIALISED EXEC ARM.                                            *)
  (*                                                                      *)
  (* [UkShDiag.wp_kshr_runcmd_final] at [c := echo_cmd s0 g], with the two *)
  (* GENERIC supplies replaced by the pinned one and [UserCwd.ucwd_any]    *)
  (* replaced by the root: [ush_simple (echo_cmd s0 g)] is [I] and         *)
  (* [ush_ht] is 1, so the LIST and BACK arms -- the only consumers of     *)
  (* [UkRun.uxsup] -- are not reached at all, which is why this statement  *)
  (* names no generic supply (S5's grep).                                  *)
  (*                                                                      *)
  (* THE CWD IS A PREMISE.  sh's process state carries                     *)
  (* [UserCwd.ucwd_any] ([UkSh.ush_pstate]), which pins no inum; what this *)
  (* arm needs is [ucwd (ukn_cwd N) ROOTINO], and the fact that sh never   *)
  (* leaves the root is SH-OPEN's ([uvis_cwd W = ROOTINO] at sh's entry,   *)
  (* on its own branch).  Taken as a premise here, and the seam is named   *)
  (* in the report.                                                        *)
  (* =================================================================== *)
  (* AT THE PAID PAYLOAD (step 4): the record is CONSTANT-paid at [Q]
     ([UkRun.ukn_const], sh's choice is status-independent) and holds what
     it was lent; a failed exec's diagnostic exits on the refund. *)
  (* ...AND THE DIAGNOSTIC IS PAID (M4b(2)): a child whose exec FAILED
     writes "exec echo failed" on its fd 2 from the refund ([Cr], the
     block credential it was lent) and exits on what the seventeen bytes
     leave ([Cd], the block written up to its prompt).  The free law
     [UkSh.sh_deps] is no longer a premise: nothing on this walk spends it. *)
  Definition wp_kshr_exec_echo (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
           (t szv s0 : Z) (g : nat -> bv 8) (ld : list fdstate) (n : nat),
      ukn_pay N = Q ->
      m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
      echo_argv_bytes g ->
      UkSh.ush_fd1p ld ->
      UkSh.ush_fd2p ld ->
      ⊢ shk_code (ukn_t N) -∗
        sh_exec_sup_echo Q Cr -∗
        (* the diagnostic's law, and what its end pays at the exit *)
        UkShDiag.ush_execfail_law Cr Cd -∗
        (* ...and the tear-down's close payments (design/pipe.md, "The exit
           path"): the diagnostic's walk ends in exit(1) *)
        UkRun.udepw_law USYS_exit -∗
        □ (Cd -∗ Q (-1)) -∗
        ush_jtab (ukn_t N) -∗
        ush_cmd (ukn_d N) t (echo_cmd s0 g) -∗
        usz (ukn_s N) szv -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        Cr -∗
        urun N h m (mword_of_int ShSyms.runcmd)
          (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
        WP (Loop : expr riscv_lang).

  Lemma wp_kshr_exec_at_cwd_holds (R : iProp Σ) : wp_kshr_exec_at_cwd R.
  Proof.
    intros N Hc h m c avail.
    iIntros "#Hcode Hrun Hcwd Hsbx Hcont".
    assert (Hexec : ShSyms.exec = 0xcbe)
      by (destruct shk_syms_pins
            as (_&_&_&_&_&_&_&_&_&_&_&_&_&H&_); exact H).
    rewrite Hexec.
    iApply (wp_uk_cli N h m (mword_of_int 0xcbe)
              (mword_of_int 7 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_cbe with "Hcode"). }
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64
                        (mword_of_int 7 : mword 6) : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    assert (E0 : add_vec_int (mword_of_int 0xcbe : mword 64) 2
                 = mword_of_int 0xcc0)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite E0 Em. iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m).
    iApply (wp_uk_ecall_exec_at_cwd_refR N h1 m1 (mword_of_int 0xcc0) avail c R
              ltac:(rewrite /m1 /usysno
                      (upd_eq m (Regidx a7_idx) (mword_of_int 7 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hcwd Hsbx").
    { iApply (uis_shk_cc0 with "Hcode"). }
    assert (E1 : add_vec_int (mword_of_int 0xcc0 : mword 64) 4
                 = mword_of_int 0xcc4)
      by (apply bv_eq; vm_compute; reflexivity).
    (* the failed exec's refund goes on to the continuation (step 4) *)
    rewrite E1. iIntros (h2) "Hcwd Hpay Hrun".
    set (m2 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]> m1).
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) _
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 7 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcc4) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cc4 with "Hcode"). }
    iIntros (h3) "Hrun". iApply ("Hcont" $! h3 with "Hcwd Hpay Hrun").
  Qed.

  (* ---- the specialised EXEC arm, PROVED ------------------------------- *)
  Lemma wp_kshr_exec_echo_holds (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) :
    wp_kshr_exec_echo Q Cr Cd.
  Proof.
    intros N Hcc h m t szv s0 g ld n Hpeq Ha0 Hbytes Hfd1 Hfd2.
    (* THE BUNDLE-INTRO HANG (durable-notes, "iIntros #H on a bundle of
       wands"): [iIntros "#H"] on a bundle of [UkRun.udepw_law]s sends the
       [Persistent] search down [udepw]'s wand chain and it does not return
       AT THIS FILE'S ALTITUDE.  [UkSh.sh_deps] used to be introduced
       linearly for that reason and is GONE from this walk (M4b(2): the
       diagnostic goes through the links); [sh_exec_sup_echo] is still
       introduced linearly and its box stripped by an explicit unfold. *)
    iIntros "#Hcode Hexs #Hxl #Hex2 #Hcd #Hjt #Htree Hsz Hstd Hcwd Hch Hcr Hrun".
    rewrite /sh_exec_sup_echo. iDestruct "Hexs" as "#Hexs".
    iDestruct (ush_jtab_ro with "Hjt") as "#Hro".
    iDestruct (echo_cmd_addr with "Htree") as %[Htr Ht8].
    iDestruct (echo_cmd_argv0 with "Htree") as "[#Hw0 #Hstr]".
    iDestruct "Hstr" as "[%Hxr #Hxs]".
    cbn [ua_ptr ua_len ua_bytes] in Hxr.
    (* ---- runcmd's prologue and the jump table ---- *)
    iApply (wp_kshr_entry N (echo_cmd s0 g) h m t
              (2 + (UkShDiag.ush_Dg + n)) Ha0 with "Hcode Hjt Htree Hrun").
    iIntros (h1 m1 sp0) "%Hal8 %Hlo %Hsp1 %Hs0_1 %Hs1_1 %Ha0_1 _ Hrun".
    assert (E8 : (t + 8) mod 8 = 0)
      by (rewrite Zplus_mod Ht8; reflexivity).
    assert (Ece : add_vec_int (mword_of_int 0xce : mword 64) 2
                  = mword_of_int 0xd0)
      by (apply bv_eq; vm_compute; reflexivity).
    (* ---- 0xce  c.ld a0,8(s1) -- argv[0] ---- *)
    iApply (UkShRun.wp_uk_cldq N h1 m1 (mword_of_int 0xce)
              (mword_of_int 1 : mword 5) (mword_of_int 2 : mword 3)
              (mword_of_int 2 : mword 3) a0_idx a0_idx DfracDiscarded
              (t + 8) (mword_of_int (s0 + Z.of_nat (echo_off 0%nat)))
              (2 + (UkShDiag.ush_Dg + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_1 (uint_moi t ltac:(unfold Z64; lia));
                    vm_compute uoff_c8; lia)
              E8 ltac:(vm_compute; discriminate)
              with "[] Hw0 Hrun").
    { iApply (uis_shk_ce with "Hcode"). }
    iIntros "_". rewrite Ece. iIntros (h2) "Hrun".
    set (k1 := <[Regidx a0_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat (echo_off 0%nat))
                       : mword 64)]> m1).
    assert (Hk1 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                    k1 !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx a0_idx) (Regidx q) _ Hq)).
    assert (Hs1_k : k1 !!! Regidx s1_idx = (mword_of_int t : mword 64))
      by (rewrite (Hk1 s1_idx ltac:(vm_compute; discriminate)); exact Hs1_1).
    (* ---- 0xd0  c.beqz a0 -- NOT taken: argv[0] is a string ---- *)
    iApply (wp_uk_cbeqz N h2 k1 (mword_of_int 0xd0)
              (mword_of_int 16 : mword 8) (mword_of_int 2 : mword 3) a0_idx
              false (mword_of_int 0xf0) (2 + (UkShDiag.ush_Dg + n))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite /k1 (upd_eq m1 (Regidx a0_idx)
                                   (mword_of_int
                                      (s0 + Z.of_nat (echo_off 0%nat))
                                    : mword 64));
                    rewrite (moi_eq_zero (s0 + Z.of_nat (echo_off 0%nat))
                               ltac:(unfold Z64; lia));
                    symmetry; apply Z.eqb_neq; lia)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(discriminate)
              with "[] Hrun").
    { iApply (uis_shk_d0 with "Hcode"). }
    assert (Ed0 : add_vec_int (mword_of_int 0xd0 : mword 64) 2
                  = mword_of_int 0xd2)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ed0. iIntros (h3) "Hrun".
    (* ---- 0xd2  addi a1,s1,8 -- &argv[0] ---- *)
    iApply (wp_uk_addi N h3 k1 (mword_of_int 0xd2)
              (mword_of_int 8 : mword 12) s1_idx a1_idx
              (mword_of_int (t + 8)) (2 + (UkShDiag.ush_Dg + n))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_k;
                    assert (Es : (sign_extend' 64
                                    (mword_of_int 8 : mword 12) : mword 64)
                                 = mword_of_int 8)
                      by (apply bv_eq; vm_compute; reflexivity);
                    rewrite Es moi_add; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_d2 with "Hcode"). }
    assert (Ed2 : add_vec_int (mword_of_int 0xd2 : mword 64) 4
                  = mword_of_int 0xd6)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Ed2. iIntros (h4) "Hrun".
    set (k2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int (t + 8)
                                     : mword 64)]> k1).
    (* ---- 0xd6  jal ra,exec ---- *)
    iApply (wp_kshr_jal N h4 k2 0xd6 ShSyms.exec 0xda
              (mword_of_int 3048 : mword 21) (2 + (UkShDiag.ush_Dg + n))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_d6 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (k3 := <[Regidx ra_idx := (mword_of_int 0xda : mword 64)]> k2).
    assert (Hrk3 : ret_pc (k3 !!! Regidx ra_idx)
                   = (mword_of_int 0xda : mword 64))
      by (rewrite /k3 (upd_eq k2 (Regidx ra_idx) _);
          apply bv_eq; vm_compute; reflexivity).
    (* ---- THE PINNED EXEC, at the root ---- *)
    assert (Hka0 : (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
                     !!! Regidx a0_idx
                   = (mword_of_int (s0 + Z.of_nat (echo_off 0%nat))
                      : mword 64)).
    { rewrite (upd_ne k3 (Regidx a7_idx) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /k3 (upd_ne k2 (Regidx ra_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /k2 (upd_ne k1 (Regidx a1_idx) (Regidx a0_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /k1 (upd_eq m1 (Regidx a0_idx) _). reflexivity. }
    assert (Hka1 : (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
                     !!! Regidx a1_idx = (mword_of_int (t + 8) : mword 64)).
    { rewrite (upd_ne k3 (Regidx a7_idx) (Regidx a1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /k3 (upd_ne k2 (Regidx ra_idx) (Regidx a1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /k2 (upd_eq k1 (Regidx a1_idx) _). reflexivity. }
    (* THE DEPOSIT, BUILT FIRST AND FULLY EXPLICITLY.  Leaving the key an
       evar for [iApply] to solve makes the proofmode unify against
       [UkRun.udepw_at]'s whole ∀-chain, which does not terminate at this
       altitude (durable-notes, "A compile that never finishes"). *)
    iAssert (udepw_at_refR N
               (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
               (mword_of_int 0xcc0) FsImg.ROOTINO
               (UserFd.ustd (ukn_fd N) ld ∗ Cr))
      with "[Hstd Hcr]" as "Hdepx".
    { iApply ("Hexs" $! N
                (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)
                (mword_of_int 0xcc0) s0 t g ld
                with "[%] [%] [%] [%] [%] Hstd Htree Hcr").
      - exact Hpeq.
      - (* [echo_off 0] IS 0; the supply names the token's base, the load
           named its offset from the node, and the two are the same [Z]. *)
        assert (Hoff0 : s0 + Z.of_nat (echo_off 0%nat) = s0)
          by (rewrite echo_off_0; lia).
        rewrite <- Hoff0. exact Hka0.
      - exact Hka1.
      - exact Hbytes.
      - exact Hfd1. }
    (* the budget is a [nat] and the cwd a [Z]; [wp_kshr_exec_at_cwd] is a
       [Definition ... : Prop], so its argument scopes are not visible at
       elaboration and the [%nat] has to be written. *)
    iApply (wp_kshr_exec_at_cwd_holds (UserFd.ustd (ukn_fd N) ld ∗ Cr)
              N Hcc h5 k3 FsImg.ROOTINO
              ((2 + (UkShDiag.ush_Dg + n))%nat)
              with "Hcode Hrun Hcwd Hdepx").
    rewrite Hrk3. iIntros (h6) "Hcwd [Hstd Hcr] Hrun".
    (* ---- 0xda: "exec %s failed" -- PAID (M4b(2)): the seventeen bytes
       go out on the refund, and the exit on what they leave ---- *)
    set (k4 := <[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                 (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> k3)).
    assert (Hs1_k4 : uint (k4 !!! Regidx s1_idx) = t).
    { rewrite /k4 (upd_ne _ (Regidx a0_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite (upd_ne k3 (Regidx a7_idx) (Regidx s1_idx) _
                 ltac:(vm_compute; discriminate)).
      rewrite /k3 (upd_ne k2 (Regidx ra_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite /k2 (upd_ne k1 (Regidx a1_idx) (Regidx s1_idx) _
                     ltac:(vm_compute; discriminate)).
      rewrite Hs1_k. apply uint_moi. unfold Z64. lia. }
    replace (2 + (UkShDiag.ush_Dg + n))%nat
      with (UkShDiag.ush_Dg + (2 + n))%nat by lia.
    iApply (UkShDiag.wp_kshd_execfail_paid N Cr Cd ld h6 k4 (2 + n)
              (UArg (s0 + Z.of_nat (echo_off 0%nat)) (echo_alen 0%nat)
                 (fun j : nat => g (echo_off 0%nat + j)%nat))
              Hfd2 ltac:(rewrite Hs1_k4; exact Ht8) ltac:(reflexivity)
              ltac:(intros j Hj; cbn [ua_bytes];
                    rewrite (proj1 Hbytes 0%nat j ltac:(exact echo_ws_pos) Hj);
                    rewrite echo_off_0 Nat.add_0_l; reflexivity)
              with "Hxl Hcode Hro [] [] Hstd Hcr [] Hex2 Hrun").
    { rewrite Hs1_k4. cbn [ua_ptr]. iExact "Hw0". }
    { rewrite /ush_str. cbn [ua_ptr ua_len ua_bytes].
      iSplitR; [ iPureIntro; exact Hxr | iExact "Hxs" ]. }
    { iIntros "_ Hc". rewrite <- Hpeq. iApply ("Hcd" with "Hc"). }
  Qed.

  (* =================================================================== *)
  (* THE DISPATCH, in [UkShMain.wp_kshm_child]'s place.                   *)
  (*                                                                      *)
  (* [wp_kshm_child_alloc] is already parametric in the token list, so the *)
  (* specialisation is at [toks := echo_toks]; what CHANGES is the supply  *)
  (* it hands the runner (pinned, not [UkRun.uxsup]) and the cwd.  The     *)
  (* two premises the generic lemma takes about the line                   *)
  (* ([ushp_no_symbols], [ushp_tokens]) are replaced by the ONE fact the   *)
  (* disciplined branch has -- [UConsLine.ush_line_is] -- through          *)
  (* [ush_line_toks] above.                                                *)
  (*                                                                      *)
  (* THE TAINTED BRANCH IS THE GENERIC ONE and does not appear here:       *)
  (* under the taint sh's line is unknown, the parse is whatever it is,    *)
  (* and [UkShMain.wp_kshm_child_alloc] runs on [UkRun.uxsup] exactly as   *)
  (* it does today.  The disjunction is [UConsLine.ush_rest_line]'s, and   *)
  (* the case split belongs to the body that holds it (SH-LINE 2b).        *)
  (* =================================================================== *)
  Definition wp_kshm_child_echo (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) : Prop :=
    forall (N : uk_names Σ) (Hc : ukn_const N)
           (h : CpuId) (m : regfile) (dw dv : dfrac)
           (s0 : Z) (len : nat) (f : nat -> bv 8) (sz : Z)
           (ld : list fdstate) (n : nat),
      ukn_pay N = Q ->
      m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
      UConsLine.ush_line_is f 0%nat len ->
      0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
      8344 <= sz ->
      UserPtTree.pgroundup sz = sz ->
      usz_ok (sz + 65536) ->
      UkSh.ush_fd1p ld ->
      UkSh.ush_fd2p ld ->
      (* NO FREE WRITE LAW (M4b(2)): the paid child's walk spends it
         nowhere *)
      ⊢ shk_code (ukn_t N) -∗
        sh_exec_sup_echo Q Cr -∗
        (* what the lend pays where the parser's walk DIES (the null store
           at [memset]) -- and the diagnostic's law and what its end pays
           where the exec FAILED (M4b(2)) *)
        □ (Cr -∗ Q (-1)) -∗
        UkShDiag.ush_execfail_law Cr Cd -∗
        (* ...and the tear-down's close payments (design/pipe.md, "The exit
           path"): both dead ends of this walk end in exit(1) *)
        UkRun.udepw_law USYS_exit -∗
        □ (Cd -∗ Q (-1)) -∗
        shp_code (ukn_t N) -∗ shp_rodata (ukn_t N) -∗ ush_jtab (ukn_t N) -∗
        ustr (ukn_d N) (DfracOwn 1) s0 len f -∗
        ustr (ukn_d N) dw ushp_whitespace 5 ushp_ws_f -∗
        ustr (ukn_d N) dv ushp_symbols 7 ushp_sym_f -∗
        UserFd.ustd (ukn_fd N) ld -∗
        UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
        UserChildren.uch_any (ukn_ch N) -∗
        UkShMalloc.ushm_fresh N sz -∗
        Cr -∗
        urun N h m (mword_of_int 0x9c0)
          (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
        WP (Loop : expr riscv_lang).

  Lemma wp_kshm_child_echo_holds (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) :
    wp_kshm_child_echo Q Cr Cd.
  Proof.
    intros N Hc h m dw dv s0 len f sz ld n
      Hpeq Hs1 Hline Hs0 Hs64 Hs38 Hszlo Hszal Hszok Hfd1 Hfd2.
    (* the ONE line the discipline admits, as the parser's own premises *)
    destruct (ush_line_toks_holds f 0%nat len Hline) as (_ & Hns0 & Htoks0).
    assert (Hns : ushp_no_symbols len f) by exact Hns0.
    assert (Htoks : ushp_tokens len f 0%nat echo_toks) by exact Htoks0.
    pose proof echo_toks_lt10 as Htlen.
    assert (Hbytes : echo_argv_bytes
              (ushp_nulfold echo_toks (ushp_ext len f)))
      by exact (echo_argv_bytes_of_line_holds f 0%nat len Hline).
    (* the pinned supply LINEARLY, as in [wp_kshr_exec_echo_holds]: it is
       spent exactly once, at the arm below, and introducing it with [#]
       does not return here.  No [UkSh.sh_deps] anywhere on this walk
       (M4b(2)). *)
    iIntros "#Hcode Hexs #Hcq #Hxl #Hex2 #Hcd #Hpcode #Hpro #Hjt Hline Hws Hsy Hstd
             Hcwd Hch HM Hcr Hrun".
    (* the line's own bytes are non-NUL, which is what makes each token a
       string once the cut lands *)
    iDestruct (ustr_nonul with "Hline") as %Hnn0.
    iDestruct (ustr_len with "Hline") as %Hlen31.
    (* ---- 0x9c0  c.mv a0,s1 ---- *)
    iApply (wp_uk_cmv N h m (mword_of_int 0x9c0) a0_idx s1_idx
              (add_vec zero_reg (m !!! Regidx s1_idx))
              (60 + (8 + (UkShDiag.ush_Dg + n)))
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
    assert (Hs1_1 : m1 !!! Regidx s1_idx = (mword_of_int s0 : mword 64))
      by (rewrite /m1 (upd_ne m (Regidx a0_idx) (Regidx s1_idx) _
                         ltac:(vm_compute; discriminate)); exact Hs1).
    (* ---- 0x9c2  jal ra,parsecmd ---- *)
    iApply (wp_uk_jal N h1 m1 (mword_of_int 0x9c2)
              (mword_of_int 2096812 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.parsecmd) (mword_of_int 0x9c6)
              (60 + (8 + (UkShDiag.ush_Dg + n)))
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
    (* ---- parsecmd ---- *)
    (* the exit payload goes down the parser's walk (lane IO-LEAF, M3c):
       [malloc] can return NULL and the store through it kills this
       process.  This walk still has it for free. *)
    (* the exit resource down the parser's walk is the LEND (step 4): the
       law [Hcq] pays the exit where the walk dies, and the lend comes back
       on the arm where the allocation succeeded, for the exec below *)
    iAssert (□ (Cr -∗ ukn_pay N (-1)))%I as "#Hpxw".
    { iIntros "!> Hc". rewrite Hpeq. iApply ("Hcq" with "Hc"). }
    iApply (UkShParseCmd.wp_kshp_parser N (UkShMalloc.ushm_fresh N sz)
              (usz (ukn_s N) (sz + 65536))
              (UkShMalloc.ushm_malloc_ok_holds N Hpsok_free sz
                 Hszlo Hszal Hszok)
              h2 m2 dw dv s0 len f echo_toks
              (8 + (UkShDiag.ush_Dg + n))
              Ha0_2 Hns Htoks Htlen Hs0 Hs64
              with "Hpcode Hpro Hline Hws Hsy HM Hpxw Hex2 Hcr Hrun").
    iIntros (p) "%Hparses Hnode Hline %Hcut Hws Hsy".
    iIntros (h3 m3) "%Hcs3 %Ha0_3 Hsz Hcr Hrun".
    rewrite Hra_2.
    (* ---- 0x9c6  jal ra,runcmd ---- *)
    iApply (wp_uk_jal N h3 m3 (mword_of_int 0x9c6)
              (mword_of_int 2094792 : mword 21) (mword_of_int 1 : mword 5)
              (mword_of_int ShSyms.runcmd) (mword_of_int 0x9ca)
              (60 + (8 + (UkShDiag.ush_Dg + n)))
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
    (* ---- THE SEAM: the node the parser built is the tree runcmd walks ---- *)
    iMod (UkShMain.ush_cmd_of_ushp N h4 m4 (mword_of_int ShSyms.runcmd)
            (60 + (8 + (UkShDiag.ush_Dg + n))) s0 p len f echo_toks
            Htoks Hns Hnn0 Hlen31 Hs0 Hs38
            with "Hrun Hnode Hline") as "(Hrun & #Htree)".
    (* ---- THE PINNED EXEC ARM, at the ONE command the line spells ---- *)
    (* [echo_cmd] is a [UExec], so [ush_ht] is 1 and the budget is the
       generic arm's at [c := echo_cmd s0 g]; the LIST and BACK arms -- the
       only consumers of [UkRun.uxsup] -- are not reached, which is why no
       generic supply appears anywhere in this walk. *)
    replace (60 + (8 + (UkShDiag.ush_Dg + n)))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (60 + n))))%nat by lia.
    iApply (wp_kshr_exec_echo_holds Q Cr Cd N _ h4 m4 p (sz + 65536) s0
              (ushp_nulfold echo_toks (ushp_ext len f)) ld ((60 + n)%nat)
              Hpeq Ha0_4 Hbytes Hfd1 Hfd2
              with "Hcode Hexs Hxl Hex2 Hcd Hjt Htree Hsz Hstd Hcwd Hch Hcr Hrun").
  Qed.

  (* =================================================================== *)
  (* S3b THE BODY'S CHILD LAW, DISCHARGED (lane IO-LEAF, step 4).         *)
  (*                                                                      *)
  (* [UkShFork.ushf_child_law] is the dispatch above at the payload sh's   *)
  (* fork chose -- [ushf_wq np], the credential after echo's block or the  *)
  (* block still owed -- and the lend [Wc np 3], for every boundary [np].  *)
  (* The exec supply at that payload is the one thing it needs, and it is  *)
  (* the application's to give ([UShEcho.sh_exec_sup_of_echo_slot]).       *)
  (* =================================================================== *)
  Definition sh_exec_sup_echo_wq (Wc : nat -> nat -> iProp Σ) : iProp Σ :=
    (□ (∀ np : nat,
          sh_exec_sup_echo (fun _ : Z => UkShFork.ushf_wq Wc np) (Wc np 3%nat)))%I.

  Global Instance sh_exec_sup_echo_wq_persistent Wc :
    Persistent (sh_exec_sup_echo_wq Wc).
  Proof. rewrite /sh_exec_sup_echo_wq. apply _. Qed.

  (* ...and the diagnostic's law at the same two ends (M4b(2)): from the
     block owed to the block written up to its prompt, at every boundary *)
  Definition ush_execfail_law_wq (Wc : nat -> nat -> iProp Σ) : iProp Σ :=
    (□ (∀ np : nat, UkShDiag.ush_execfail_law (Wc np 3%nat) (Wc np 0%nat)))%I.

  Global Instance ush_execfail_law_wq_persistent Wc :
    Persistent (ush_execfail_law_wq Wc).
  Proof. rewrite /ush_execfail_law_wq. apply _. Qed.

  Lemma ushf_child_law_holds (Wc : nat -> nat -> iProp Σ) :
    ush_execfail_law_wq Wc -∗
    sh_exec_sup_echo_wq Wc -∗ UkShFork.ushf_child_law Wc.
  Proof.
    iIntros "#Hxl #Hsup". rewrite /UkShFork.ushf_child_law.
    iIntros "!>" (N' h m dw dv s0 len g sz ld n np)
      "%Hpeq %Hs1 %Hline %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok %Hrows
       #Hcode #Hpcode #Hpro #Hjt Hline Hws Hsy Hstd Hcwd Hch HM Hcr Hrun".
    pose proof (ukn_const_of_eq N' _ Hpeq (fun x y => eq_refl)) as Hc.
    iApply (wp_kshm_child_echo_holds (fun _ : Z => UkShFork.ushf_wq Wc np)
              (Wc np 3%nat) (Wc np 0%nat) N' Hc h m dw dv s0 len g sz ld n
              Hpeq Hs1 Hline Hs0 Hs64 Hs38 Hszlo Hszal Hszok
              (proj1 (proj2 Hrows)) (proj2 (proj2 Hrows))
              with "Hcode [] [] [] [] Hpcode Hpro Hjt Hline Hws Hsy Hstd Hcwd Hch
                    HM Hcr Hrun").
    - iApply ("Hsup" $! np).
    - (* a child that died at the null store exits on the block it was
         lent *)
      iIntros "!> Hc". rewrite /UkShFork.ushf_wq. iLeft. iExact "Hc".
    - iApply ("Hxl" $! np).
    - (* a failed exec's child exits on the block written up to its prompt *)
      iIntros "!> Hc". rewrite /UkShFork.ushf_wq. iRight. iExact "Hc".
  Qed.

  (* =================================================================== *)
  (* S4  THE PARENT.                                                      *)
  (*                                                                      *)
  (* For [echo_cmd] the parent's round is the LANDED one:                  *)
  (* [UkShFork.wp_kshf_fork]'s parent arm reaps with [wait((int * )0)] --  *)
  (* [UkShRun.wp_kshr_wait], whose answer [ret] is UNCONSTRAINED and whose *)
  (* only moving resource is the index-free [UserChildren.uch_any] -- and  *)
  (* re-enters the loop head with exactly what it carried in.  So the      *)
  (* round's invariant carries NOTHING about the child: not its payload    *)
  (* (the child runs at [fun _ => True]), not its exit status, not a byte  *)
  (* of what echo wrote.  The five conjuncts below ARE the invariant, and  *)
  (* the ONE thing E4 adds to it is the cwd index: the next round's child  *)
  (* must exec on the pin too, so [UserCwd.ucwd_any] in                    *)
  (* [UkSh.ush_pstate] becomes [ucwd (ukn_cwd N) ROOTINO] here.            *)
  (* =================================================================== *)
  (* [T] IS A PARAMETER (lane IO-LEAF, M5(3)): the fourth conjunct is the
     cursor AT A LINE BOUNDARY now, whose other arm is the taint. *)
  (* ...AND THE PID ROW BESIDE THE CHILDREN SET (step 4), and the cwd
     PINNED at the root in [UkSh.ush_pstate] itself now (SH-LINE R3(2)):
     the index below is kept for E4's round, and is the root. *)
  Definition ush_pstate_at (N : uk_names Σ) (gp : gname) (T : iProp Σ)
      (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ) (Pm : nat -> iProp Σ)
      (l : list fdstate) (c : Z) : iProp Σ :=
    (UkSh.ush_std N l ∗ UserCwd.ucwd (ukn_cwd N) c
     (* the two identity conjuncts are PINNED now (lane EXEC-SEAM), as
        [UkSh.ush_pstate]'s are: no children at the head, not <init> *)
     ∗ UserChildren.uch (ukn_ch N) ∅
     ∗ UkSh.ush_pid N
     ∗ UkSh.ush_posb N gp T Wc Wb Pm l 0%nat)%I.

  Lemma ush_pstate_of_at (N : uk_names Σ) (gp : gname) (T : iProp Σ)
      (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ) (Pm : nat -> iProp Σ)
      (l : list fdstate) :
    ush_pstate_at N gp T Wc Wb Pm l FsImg.ROOTINO -∗
    UkSh.ush_pstate N gp T Wc Wb Pm l.
  Proof.
    rewrite /ush_pstate_at /UkSh.ush_pstate.
    iIntros "(Hstd & Hcwd & Hch & Hpid & Hpos)". iFrame "Hstd Hcwd Hch Hpid Hpos".
  Qed.

  (* WHAT CROSSES THE ROUND, named once: the loop head's own resources are
     [UkShLoop.ushl_head]'s and are not re-stated; these are the four the
     fork arm threads through both processes' entry and back out of the
     parent's ([UkShFork.wp_kshf_fork]). *)
  Definition ush_echo_round_carry (N : uk_names Σ) (gp : gname)
      (T : iProp Σ) (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
      (Pm : nat -> iProp Σ) (l : list fdstate) (sz : Z)
      (f : nat -> bv 8) : iProp Σ :=
    (ush_pstate_at N gp T Wc Wb Pm l FsImg.ROOTINO
     ∗ UkShLoop.ushl_dat (ukn_d N) ∗ usz (ukn_s N) sz
     ∗ ubytes (ukn_d N) UkSh.sh_buf UkSh.sh_nbuf f)%I.

End UkShEcho.
