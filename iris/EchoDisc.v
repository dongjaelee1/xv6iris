(* EchoDisc.v -- THE ECHO APPLICATION'S CONSOLE DISCIPLINE AND OUTPUT CLAIM,
   as PURE COMBINATORICS over the observation trace.  No Iris, no ghosts: a
   [list mobs] goes in and a [Prop] comes out, so the statements here can be
   read -- and refuted -- without opening the logic.

   Design of record: claude-notes/projects/app-echo.md, "E5 -- THE OUTPUT
   SIDE" (O1-O3 as ruled by the owner; O5's allocation-failure
   alternatives; "TWO UARTS") and "E3 -- THE INPUT LINE" (R4, the
   per-character ruling); the pre-mortem review
   review-echo-plan-2026-09-12.md, findings 7, 8 and 12.

   THE THEOREM IS ABOUT THE CONSOLE UART ONLY.  The board has two 16550s
   and the kernel drives both: the CONSOLE ([DevModel.Uart0]) carries the
   processes' output and [consoleintr]'s echo of what the user types, and
   nothing else -- [printk] and [panic] write the OTHER port
   ([DevModel.Uart1]), whose output is unconstrained and which this file
   never reads.  So the console wire is PURE SESSION OUTPUT: what a user
   sees is exactly what init, sh, echo and the echo-back produced, in the
   order the transmitter accepted it.  (Before the second port existed the
   kernel's ten boot messages were interleaved into the same wire, byte for
   byte, and the discipline had to wait for the last of them before it
   could read anything; all of that is gone.)

   WHY THE DISCIPLINE IS A RATE BOUND.  [AppEcho.disc] used to be
   [star_prefix echo_line] of the cycle's INPUT BYTES ALONE -- a predicate
   that says nothing about WHEN a byte was typed.  Review finding 7 is that
   the theorem is FALSE at that discipline: the console ring holds 128
   unconsumed bytes and [consoleintr] DROPS the next one silently, so an
   adversary who types a screenful before sh's first read breaks the
   correspondence between the stored sequence and the input sequence, and
   nothing downstream can repair it.  The owner's ruling (app-echo.md, O3)
   is a rate bound stated on the raw wire:

     D1  a line's first byte only after the "$ " prompt has appeared.
     D2  every later byte of a line only after the previous byte's echo.
     D3  the input bytes are a prefix of [echo_line]^* -- the LANDED
         predicate, kept verbatim as [disc_seg].

   D1 AND D2 ARE ONE CONDITION, POSITIONAL.  Section 5 states, at every
   input position i, that the expected transcript for the first i input
   bytes is already a prefix of the wire ([disc_pt]).  That transcript
   ENDS in exactly the byte D2 asks for when i is mid-line, and in exactly
   the "$ " D1 asks for when i is at a line boundary (at i = 0 it is init's
   banner and sh's first prompt), so the one condition implies both.  It is
   also the SIMULATION INVARIANT the output proof wants: [good_out] bounds
   the wire from the other side, and at an input point the two bounds meet
   and the wire is pinned exactly.

   WHAT IS NOT HERE.  [Hphi] -- the theorem's obligation at [echo_phi] --
   is NOT proved by this file, nor by the lane that wrote it; see the note
   at [AppEcho.echo_phi].  This file is the STATEMENT. *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [obs_wire Uart0], [cycles_of], [trace_shape] *)
Require Import RiscvPtsto.       (* [string_bytes] *)
Require Import LineWords.        (* the line as a list of WORDS *)
(* ssreflect's [rewrite] (the [/def] fold, the multi-rule form) is what this
   file's proofs are written in; a pure file does not get it from the
   proofmode the way its neighbours do, so it is imported by name. *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  BYTES FROM STRINGS                                                 *)
(* ====================================================================== *)

(* the kernel's own string->bytes reader, NUL-free.  Every literal below is
   transcribed from the source it comes from and from nothing else: a
   message that is wrong here makes the claim say something the machine
   does not do, and no build step would notice. *)
Definition sb (s : string) : list (bv 8) := string_bytes s.

Definition nlb : list (bv 8) := [Z_to_bv 8 10%Z].

(* ====================================================================== *)
(*  1.  THE INPUT LINE AND D3 (the landed predicate, verbatim)             *)
(* ====================================================================== *)

(* THE CONSOLE LINE THE DISCIPLINE ADMITS, as the three WORDS it is --
   the command name and its two arguments -- joined by single spaces and
   closed by the newline [gets] stops at and keeps ([LineWords.wl_line]).
   These are the bytes the user types, and ALSO their echoes, because
   [consoleintr] echoes a stored byte unchanged and rewrites only '\r'
   (to '\n'); the line ends in '\n' (byte 10), not '\r', so echo is the
   IDENTITY on it.

   IT IS SPELLED AS WORDS AND NOT AS SEVENTEEN BYTES because that is the
   structure everything above actually reads it through: sh's lexer finds
   the words ([UkShWords.wl_tokens]), exec pushes them, and echo prints
   them back.  A fact stated at the byte list is worth one command line;
   the same fact at [wl_line] is worth every disciplined one. *)
Definition echo_ws : list (list (bv 8)) :=
  [ sb "echo"%string; sb "hello"%string; sb "world"%string ].

Definition echo_line : list (bv 8) := wl_line echo_ws.

(* THE ONE SANCTIONED UNFOLDING.  Past the [Opaque] below the tree reads
   the line through its lemmas and never through its bytes -- which is
   both what makes a general line possible and what stops an [rewrite
   !length_app] from silently turning [length echo_line] into the arity
   of a join. *)
Lemma echo_line_words : echo_line = wl_line echo_ws.
Proof. reflexivity. Qed.

Lemma echo_line_length : length echo_line = 17.
Proof. vm_compute. reflexivity. Qed.

(* ...and the ONE thing most of the tree needs of that length: no line is
   empty, because every line carries its newline.  Not a fact about these
   three words ([LineWords.wl_line_pos]). *)
Lemma echo_line_pos : 0 < length echo_line.
Proof. rewrite echo_line_words. exact (wl_line_pos echo_ws). Qed.

(* the same line, read off the string it is: a transcription check *)
Lemma echo_line_string : echo_line = sb "echo hello world"%string ++ nlb.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* the words are words: nonempty and alphanumeric.  Decidable, so this is
   the ONE check that says which line the application is about. *)
Lemma echo_ws_wf : wl_wf echo_ws.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma echo_ws_length : length echo_ws = 3%nat.
Proof. reflexivity. Qed.

(* THE TWO BOUNDS A CALLER OWES, named where the word list is: the line
   has a command name to run, and it has fewer words than sh's MAXARGS.
   Both are decidable at any given line and become premises once the word
   list is a parameter. *)
Lemma echo_ws_pos : (0 < length echo_ws)%nat.
Proof. rewrite echo_ws_length. lia. Qed.

Lemma echo_ws_lt10 : (length echo_ws < 10)%nat.
Proof. rewrite echo_ws_length. lia. Qed.

(* a word of the line, read back through [!!] so that [LineWords]' lemmas
   -- every one of which is keyed on [ws !! i = Some w] -- apply *)
Lemma echo_ws_at (i : nat) :
  (i < length echo_ws)%nat -> echo_ws !! i = Some (echo_ws !!! i).
Proof.
  intro Hi. destruct (lookup_lt_is_Some_2 echo_ws i Hi) as [w Hw].
  by rewrite Hw list_lookup_total_alt Hw.
Qed.

(* ---- EVERY BYTE OF THE LINE, NUMERICALLY ----------------------------- *)
(* The console-side proofs each have to refute one byte -- the carriage
   return [consoleintr] rewrites, the three erase characters, the
   end-of-file byte, the NUL [gets] plants past the line.  Each used to be
   a case analysis over seventeen literals.  All of them come off this one
   reading ([LineWords.wl_line_byte_val]) by [lia]. *)
Lemma echo_line_byte_val (b : bv 8) :
  b ∈ echo_line ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof.
  rewrite echo_line_words. exact (wl_line_byte_val echo_ws b echo_ws_wf).
Qed.

Lemma echo_line_byte_val_at (j : nat) :
  (j < length echo_line)%nat ->
  bv_unsigned (echo_line !!! j) = 10%Z
  \/ bv_unsigned (echo_line !!! j) = 32%Z
  \/ (48 <= bv_unsigned (echo_line !!! j) <= 57)%Z
  \/ (65 <= bv_unsigned (echo_line !!! j) <= 90)%Z
  \/ (97 <= bv_unsigned (echo_line !!! j) <= 122)%Z.
Proof.
  intro Hj. apply echo_line_byte_val.
  destruct (lookup_lt_is_Some_2 echo_line j Hj) as [b Hb].
  rewrite list_lookup_total_alt Hb. cbn [default from_option].
  exact (elem_of_list_lookup_2 echo_line j b Hb).
Qed.

(* THE THREE ROWS THE SHELL'S OWN WALK SPENDS, each off the reading above
   together with the newline's position: the only newline is the LAST
   byte, no byte is a carriage return, and no byte is the NUL [gets]
   plants past the line -- which is what turns "the first NUL at or after
   0" into the line's length. *)
Lemma echo_line_byte_ncr (j : nat) :
  (j < length echo_line)%nat -> bv_unsigned (echo_line !!! j) <> 13%Z.
Proof. intro Hj. pose proof (echo_line_byte_val_at j Hj). lia. Qed.

Lemma echo_line_byte_nonzero (j : nat) :
  (j < length echo_line)%nat -> bv_unsigned (echo_line !!! j) <> 0%Z.
Proof. intro Hj. pose proof (echo_line_byte_val_at j Hj). lia. Qed.

(* ...AND ITS POSITIONAL HALF: the only newline is the last byte, which is
   what [gets] stopping at the first one says about the buffer it read. *)
Lemma echo_line_nl_last (k : nat) :
  echo_line !! k = Some (Z_to_bv 8 10%Z) -> k = (length echo_line - 1)%nat.
Proof.
  rewrite echo_line_words. intro Hk.
  rewrite (wl_line_nl_last echo_ws k echo_ws_wf Hk) wl_line_length. lia.
Qed.

Lemma echo_line_nl_at_end :
  echo_line !! (length echo_line - 1)%nat = Some (Z_to_bv 8 10%Z).
Proof.
  rewrite echo_line_words wl_line_length.
  replace (length (wl_body echo_ws) + 1 - 1)%nat
    with (length (wl_body echo_ws)) by lia.
  exact (wl_line_nl_at echo_ws).
Qed.

Lemma echo_line_byte_nl (j : nat) :
  (j < length echo_line)%nat ->
  bv_unsigned (echo_line !!! j) = 10%Z -> j = (length echo_line - 1)%nat.
Proof.
  intros Hj He. apply echo_line_nl_last.
  destruct (lookup_lt_is_Some_2 echo_line j Hj) as [b Hb].
  rewrite Hb. f_equal.
  rewrite <- (list_lookup_total_correct echo_line j b Hb).
  apply bv_eq. rewrite He. by vm_compute.
Qed.

Lemma echo_line_nl_val :
  bv_unsigned (echo_line !!! (length echo_line - 1)%nat) = 10%Z.
Proof.
  rewrite (list_lookup_total_correct echo_line (length echo_line - 1)%nat
             (Z_to_bv 8 10%Z) echo_line_nl_at_end).
  by vm_compute.
Qed.

Global Opaque echo_line.

(* the INPUT bytes of an observation list, in order -- the CONSOLE's; an
   input on the other port is not the user's and is invisible here *)
Definition ins (h : list mobs) : list (bv 8) :=
  omap (fun e => match e with ObsUartIn Uart0 b => Some b | _ => None end) h.

Lemma ins_app (h k : list mobs) : ins (h ++ k) = ins h ++ ins k.
Proof. by rewrite /ins omap_app. Qed.

Lemma ins_in (b : bv 8) : ins [ObsUartIn Uart0 b] = [b].
Proof. reflexivity. Qed.
Lemma ins_out (b : bv 8) : ins [ObsUartOut Uart0 b] = [].
Proof. reflexivity. Qed.

(* [l] IS A PREFIX OF [pat]^*, spelled so that it is decidable by one
   list equality and prefix-closed by one [take]: the first [length l]
   letters of [pat] repeated [length l] times are the first [length l]
   letters of [pat]^w whenever [pat] is nonempty. *)
Definition star_prefix (pat l : list (bv 8)) : Prop :=
  l = take (length l) (concat (replicate (length l) pat)).

Global Instance star_prefix_dec pat l : Decision (star_prefix pat l).
Proof. rewrite /star_prefix. apply _. Defined.

Lemma star_prefix_nil pat : star_prefix pat [].
Proof. reflexivity. Qed.

Lemma concat_replicate_S {A} (n : nat) (pat : list A) :
  concat (replicate (S n) pat) = concat (replicate n pat) ++ pat.
Proof. by rewrite replicate_S_end concat_app /= app_nil_r. Qed.

Lemma concat_replicate_length {A} (n : nat) (pat : list A) :
  length (concat (replicate n pat)) = n * length pat.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite concat_replicate_S length_app IH. lia.
Qed.

(* the one law the rx step needs: breaking the discipline is forever. *)
Lemma star_prefix_snoc pat l b :
  0 < length pat ->
  star_prefix pat (l ++ [b]) -> star_prefix pat l.
Proof.
  rewrite /star_prefix. intros Hpat Hsnoc.
  apply (f_equal (take (length l))) in Hsnoc.
  rewrite take_app_length take_take in Hsnoc.
  rewrite length_app /= in Hsnoc.
  rewrite Nat.min_l in Hsnoc; [|lia].
  rewrite Nat.add_1_r concat_replicate_S in Hsnoc.
  rewrite take_app_le in Hsnoc; [exact Hsnoc|].
  rewrite concat_replicate_length. nia.
Qed.

(* ...and its iterate: [star_prefix] is prefix-closed outright, which is
   what carries the discipline down to every earlier history. *)
Lemma star_prefix_prefix (pat l l' : list (bv 8)) :
  0 < length pat -> l' `prefix_of` l -> star_prefix pat l -> star_prefix pat l'.
Proof.
  intros Hp [z ->]. induction z as [|b z IH] using rev_ind; intros Hs.
  - by rewrite app_nil_r in Hs.
  - apply IH. rewrite app_assoc in Hs. exact (star_prefix_snoc _ _ _ Hp Hs).
Qed.

(* THE PERIODICITY OF A STAR PREFIX, byte by byte.  These three were proved
   in [UConsLine.v] (lane SH-STATE) so that they would cost the line
   statements' cone and not the discipline's; they are general facts about
   [star_prefix] and their standing relocation ask is here, beside
   [star_prefix_snoc], where lane ECHO-PURE put them. *)
Lemma mod_sub_self (i p : nat) : (p <= i)%nat -> ((i - p) `mod` p = i `mod` p)%nat.
Proof.
  intro H. transitivity (((i - p) + 1 * p) `mod` p)%nat.
  - symmetry. apply Nat.Div0.mod_add.
  - f_equal. lia.
Qed.

Lemma concat_replicate_lookup {A} (N : nat) (pat : list A) (i : nat) :
  (i < N * length pat)%nat ->
  concat (replicate N pat) !! i = pat !! (i `mod` length pat)%nat.
Proof.
  revert i. induction N as [| N IH]; intros i Hi; [ cbn in Hi; lia | ].
  rewrite replicate_S. cbn [concat].
  destruct (decide (i < length pat)%nat) as [Hlt | Hge].
  - rewrite lookup_app_l; [ | exact Hlt ].
    rewrite (Nat.mod_small i (length pat) Hlt). reflexivity.
  - rewrite lookup_app_r; [ | lia ].
    rewrite IH; [ | cbn [Nat.mul] in Hi; lia ].
    rewrite (mod_sub_self i (length pat) ltac:(lia)). reflexivity.
Qed.

(* a star prefix IS the periodic word, byte by byte *)
Lemma star_prefix_lookup (pat l : list (bv 8)) (i : nat) :
  star_prefix pat l -> (0 < length pat)%nat -> (i < length l)%nat ->
  l !! i = pat !! (i `mod` length pat)%nat.
Proof.
  intros Hs Hp Hi.
  pose proof (f_equal (fun z : list (bv 8) => z !! i) Hs) as Hl. cbn beta in Hl.
  rewrite Hl. rewrite lookup_take; [ | exact Hi ].
  apply concat_replicate_lookup. nia.
Qed.

(* D3: one power cycle's input keeps the CONTENT discipline.  This is the
   whole of the LANDED [AppEcho.disc_seg]; [UConsLine]'s line statements
   are written at it and are unchanged (section 5's projection). *)
Definition disc_seg (seg : list mobs) : Prop := star_prefix echo_line (ins seg).

Global Instance disc_seg_dec seg : Decision (disc_seg seg).
Proof. rewrite /disc_seg. apply _. Defined.

Lemma disc_seg_nil : disc_seg [].
Proof. exact (star_prefix_nil _). Qed.

Lemma disc_seg_out (seg : list mobs) (b : bv 8) :
  disc_seg (seg ++ [ObsUartOut Uart0 b]) <-> disc_seg seg.
Proof. rewrite /disc_seg ins_app ins_out app_nil_r. done. Qed.

Lemma disc_seg_prefix (seg' seg : list mobs) :
  seg' `prefix_of` seg -> disc_seg seg -> disc_seg seg'.
Proof.
  intros [k ->] Hd. rewrite /disc_seg ins_app in Hd.
  eapply star_prefix_prefix; [exact echo_line_pos| |exact Hd]. by eexists.
Qed.

(* THE LANDED WHOLE-HISTORY PREDICATE, kept under its own name: everything
   already proved against it still means what it meant, and section 5's
   [disc_proj] is the one step from the new discipline to it. *)
Definition disc_old (h : list mobs) : Prop := Forall disc_seg (cycles_of h).

Global Instance disc_old_dec h : Decision (disc_old h).
Proof. rewrite /disc_old. apply _. Qed.

(* ====================================================================== *)
(*  2.  THE EXPECTED SESSION (R3, with O5's alternatives)                  *)
(* ====================================================================== *)

(* ---- 2a.  THE PROLOGUE, AND ITS ALTERNATIVES ---- *)

(* user/init.c:27, user/sh.c:137, user/init.c:35 and user/init.c:30 -- the
   four literals the console's opening is made of.  Every one is a console
   write ([printf] to fd 1, [fprintf] to fd 2, on descriptors init opened on
   "console"), so every one reaches THIS wire. *)
Definition u_banner   : list (bv 8) := sb "init: starting sh"%string ++ nlb.
Definition u_prompt   : list (bv 8) := sb "$ "%string.
Definition u_execfail : list (bv 8) := sb "init: exec sh failed"%string ++ nlb.
Definition u_forkfail : list (bv 8) := sb "init: fork failed"%string ++ nlb.

(* THE GOOD PROLOGUE, kept under its own name and byte for byte what it was:
   init's banner, then sh's first prompt. *)
Definition u_prologue : list (bv 8) :=
  sb "init: starting sh"%string ++ nlb ++ sb "$ "%string.

(* THE PROLOGUE ALTERNATIVES, RULED BY THE OWNER (2026-09-16: "allow these
   errors in the top-level trace theorem"; 2026-09-14: "the banner is
   optional ... a trace without a banner in a given era has to be possible
   anyway").  A prologue round is a SEQUENCE OF LETTERS, each a console
   write of init's or the shell's, and the round's transcript is the
   concatenation of their bytes:
     0  "$ "                       sh runs: the session begins.  ENDS the
                                   round.
     1  "init: exec sh failed\n"   the child could not exec (user/init.c:35);
                                   it exits, init's wait reaps it and the
                                   outer loop runs AGAIN.  CONTINUES.
     2  "init: fork failed\n"      init could not fork (user/init.c:30); it
                                   exits and kexit panics (kernel/proc.c:339)
                                   on the OTHER port, so no PROCESS ever
                                   writes this wire again.  ENDS the round.
     3  "init: starting sh\n"      init's banner (user/init.c:27), printed at
                                   the head of every turn of its outer loop
                                   WHEN ITS CONSOLE IS OPEN.  CONTINUES.
   THE BANNER IS A LETTER AND NOT A PREFIX OF THE OTHERS because init's
   console open can fail (the kernel's open contract admits a full file
   table) while the shell's own opens succeed: init then prints nothing at
   all and the round is "$ " alone -- the resolution [[0]] -- where a
   round with the banner is [[3; 0]].  The good run is [[3; 0]]; one exec
   failure and a restart is [[3; 1; 3; 0]]; the fork failure is [[3; 2]].

   WHY THE LETTERS ARE FILED ONE AT A TIME.  A writer's knowledge of the
   round is a persistent LOWER BOUND of the resolution ([EchoOut.ps_lb]),
   and a lower bound is worth exactly the bytes of the letters it names
   ([pro_of_mono]): an open round predicts NOTHING beyond them.  An
   alternative whose transcript RETRACTED a default (a "prompt without the
   banner" filed against a round that predicted the banner) would make a
   stale bound predict bytes the wire will never carry, and then no link
   stated at a lower bound could be proved.  So the banner is what init
   files when it writes its first banner byte, and nothing is predicted
   before that.

   Their first bytes are '$', 'i', 'i', 'i' -- NOT pairwise distinct, so
   [line_alts_head_det]'s one-byte reading does not carry over; what they
   are is PAIRWISE PREFIX-FREE (the three diagnostics part at byte 6,
   "init: e" / "init: f" / "init: s"), and that whole-block reading is
   what pins the resolution off the wire ([pro_of_prefix_free]).  A later
   ruling changes this ONE list.

   NOT HERE: "init: wait returned an error\n" (user/init.c:47).  That arm is
   REFUTED and not admitted -- kwait returns -1 only for a caller with no
   children or a killed one, and init holds the shell's generation. *)
Definition pro_alts : list (list (bv 8)) :=
  [ u_prompt; u_execfail; u_forkfail; u_banner ].

Lemma pro_alts_length : length pro_alts = 4.
Proof. reflexivity. Qed.

(* the letters that CONTINUE a round: the exec failure and the banner *)
Definition pro_cont (a : nat) : Prop := a = 1%nat \/ a = 3%nat.

Global Instance pro_cont_dec a : Decision (pro_cont a).
Proof. rewrite /pro_cont. apply _. Defined.

(* THE PROLOGUE FOR A RESOLUTION [ps]: the letters' bytes, in order, up to
   and including the first letter that ENDS the round; what follows it
   belongs to the next round.  OUT OF LETTERS the prologue is what has been
   filed and nothing more, so [pro_of] is MONOTONE under append
   ([pro_of_snoc]) -- which is exactly what a writer's mono_list LOWER
   BOUND of [ps] is worth -- and a COMPLETE prologue is one whose [ps] has
   an ending letter ([pro_done]).  [pro_of] reads exactly ONE round: it
   discards the tail at the first ending letter, so the r-th round's
   prologue is [pro_of (pro_from r ps)]. *)
Definition pro_more (a : nat) (t : list (bv 8)) : list (bv 8) :=
  if decide (pro_cont a) then t else [].

Fixpoint pro_of (ps : list nat) : list (bv 8) :=
  match ps with
  | [] => []
  | a :: ps' => pro_alts !!! a ++ pro_more a (pro_of ps')
  end.

Definition pro_done (ps : list nat) : Prop := Exists (fun a => ~ pro_cont a) ps.

Global Instance pro_done_dec ps : Decision (pro_done ps).
Proof. rewrite /pro_done. apply _. Defined.

(* drop ONE round, and [r] of them *)
Fixpoint pro_tail (ps : list nat) : list nat :=
  match ps with
  | [] => []
  | a :: ps' => if decide (pro_cont a) then pro_tail ps' else ps'
  end.

Fixpoint pro_from (r : nat) (ps : list nat) : list nat :=
  match r with
  | 0%nat => ps
  | S r' => pro_from r' (pro_tail ps)
  end.

(* how many rounds [ps] has SETTLED: one per ending letter *)
Fixpoint pro_rounds (ps : list nat) : nat :=
  match ps with
  | [] => 0%nat
  | a :: ps' => ((if decide (pro_cont a) then 0 else 1) + pro_rounds ps')%nat
  end.

(* one failed sub-round of the restart loop, in wire bytes: banner + the
   exec diagnostic *)
Definition pro_round : nat := (length u_banner + length u_execfail)%nat.

(* [j] FAILED SUB-ROUNDS: banner, exec failure, banner, exec failure, ...
   -- the open round init's restart head stands in *)
Definition pro_fail (j : nat) : list nat := concat (replicate j [3%nat; 1%nat]).

Lemma pro_more_cont (a : nat) (t : list (bv 8)) : pro_cont a -> pro_more a t = t.
Proof. intros H. rewrite /pro_more. by rewrite decide_True. Qed.

Lemma pro_more_1 (t : list (bv 8)) : pro_more 1%nat t = t.
Proof. apply pro_more_cont. by left. Qed.

Lemma pro_more_3 (t : list (bv 8)) : pro_more 3%nat t = t.
Proof. apply pro_more_cont. by right. Qed.

Lemma pro_more_ne (a : nat) (t : list (bv 8)) : ~ pro_cont a -> pro_more a t = [].
Proof. intros H. rewrite /pro_more. by rewrite decide_False. Qed.

Lemma pro_cont_ne (a : nat) : a <> 1%nat -> a <> 3%nat -> ~ pro_cont a.
Proof. intros H1 H3 [H | H]; [exact (H1 H) | exact (H3 H)]. Qed.

Lemma u_banner_pos : (0 < length u_banner)%nat.
Proof. vm_compute. lia. Qed.

Lemma pro_of_nil : pro_of [] = [].
Proof. reflexivity. Qed.

Lemma pro_of_cons (a : nat) (ps : list nat) :
  pro_of (a :: ps) = pro_alts !!! a ++ pro_more a (pro_of ps).
Proof. reflexivity. Qed.

Lemma pro_of_good : pro_of [3%nat; 0%nat] = u_prologue.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ...and the banner-less good run, the ruling's own case *)
Lemma pro_of_good_noban : pro_of [0%nat] = u_prompt.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* every letter is at least two bytes *)
Lemma pro_alts_nonnil (a : nat) : (a < length pro_alts)%nat -> pro_alts !!! a <> [].
Proof.
  rewrite pro_alts_length. intros Ha.
  destruct a as [|[|[|[|a]]]]; try lia; vm_compute; discriminate.
Qed.

Lemma pro_of_pos (ps : list nat) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> ps <> [] ->
  (0 < length (pro_of ps))%nat.
Proof.
  intros HF Hne. destruct ps as [| a ps]; [done |].
  rewrite Forall_cons in HF. destruct HF as [Ha _].
  cbn [pro_of]. rewrite length_app.
  destruct (pro_alts !!! a) as [| z zs] eqn:Hz;
    [ exfalso; exact (pro_alts_nonnil a Ha Hz) | cbn; lia ].
Qed.

(* the letters of an OPEN round all continue it *)
Lemma pro_open_cont (ps : list nat) : ~ pro_done ps -> Forall pro_cont ps.
Proof.
  induction ps as [| c ps IH]; intros Hnd; [done |].
  rewrite Forall_cons. split.
  - destruct (decide (pro_cont c)) as [? | Hne]; [done |].
    exfalso. apply Hnd. rewrite /pro_done. by apply Exists_cons; left.
  - apply IH. intros H. apply Hnd. rewrite /pro_done Exists_cons. by right.
Qed.

(* ...so [pro_of] is a HOMOMORPHISM on it: filing anything after an open
   round appends the bytes *)
Lemma pro_of_open_app (ps z : list nat) :
  ~ pro_done ps -> pro_of (ps ++ z) = pro_of ps ++ pro_of z.
Proof.
  intros Hnd. pose proof (pro_open_cont ps Hnd) as HF. clear Hnd.
  induction ps as [| c ps IH]; [done |].
  rewrite Forall_cons in HF. destruct HF as [Hc HF].
  cbn [app pro_of]. rewrite !(pro_more_cont c _ Hc).
  rewrite (IH HF). by rewrite app_assoc.
Qed.

Lemma pro_of_singleton (a : nat) : pro_of [a] = pro_alts !!! a.
Proof.
  cbn [pro_of]. rewrite /pro_more. case_decide; by rewrite app_nil_r.
Qed.

(* ---- [pro_of] is monotone in the resolution ---- *)

Lemma pro_of_snoc ps a : pro_of ps `prefix_of` pro_of (ps ++ [a]).
Proof.
  induction ps as [| c ps IH]; cbn [pro_of app].
  - apply prefix_nil.
  - destruct (decide (pro_cont c)) as [Hc | Hc].
    + rewrite !(pro_more_cont c _ Hc). by apply prefix_app.
    + rewrite !(pro_more_ne c _ Hc). reflexivity.
Qed.

Lemma pro_of_mono ps ps' : ps `prefix_of` ps' -> pro_of ps `prefix_of` pro_of ps'.
Proof.
  intros [z ->]. induction z as [| a z IH] using rev_ind.
  - rewrite app_nil_r. reflexivity.
  - rewrite app_assoc. etrans; [exact IH | apply pro_of_snoc].
Qed.

Lemma pro_of_done_ext ps ps' :
  ps `prefix_of` ps' -> pro_done ps -> pro_of ps = pro_of ps'.
Proof.
  intros [z ->]. induction ps as [| a ps IH]; intros Hd.
  - by apply Exists_nil in Hd.
  - rewrite /pro_done Exists_cons in Hd.
    cbn [app pro_of]. destruct (decide (pro_cont a)) as [Ha | Ha].
    + rewrite !(pro_more_cont a _ Ha).
      destruct Hd as [Hne | Hd]; [done |]. by rewrite (IH Hd).
    + by rewrite !(pro_more_ne a _ Ha).
Qed.

Lemma pro_tail_mono ps ps' : ps `prefix_of` ps' -> pro_tail ps `prefix_of` pro_tail ps'.
Proof.
  intros [z ->]. induction ps as [| a ps IH]; cbn [app pro_tail].
  - apply prefix_nil.
  - case_decide; [exact IH | by eexists].
Qed.

Lemma pro_from_mono r ps ps' :
  ps `prefix_of` ps' -> pro_from r ps `prefix_of` pro_from r ps'.
Proof.
  revert ps ps'. induction r as [| r IH]; intros ps ps' Hp; [exact Hp |].
  cbn [pro_from]. by apply IH, pro_tail_mono.
Qed.

Lemma pro_of_from_mono r ps ps' :
  ps `prefix_of` ps' -> pro_of (pro_from r ps) `prefix_of` pro_of (pro_from r ps').
Proof. intros Hp. by apply pro_of_mono, pro_from_mono. Qed.

Lemma pro_tail_Forall (P : nat -> Prop) ps : Forall P ps -> Forall P (pro_tail ps).
Proof.
  induction ps as [| a ps IH]; cbn [pro_tail]; [done |].
  rewrite Forall_cons. intros [Ha Hps]. case_decide; [by apply IH | exact Hps].
Qed.

(* a settled round stays settled under extension *)
Lemma pro_done_mono ps ps' : ps `prefix_of` ps' -> pro_done ps -> pro_done ps'.
Proof. intros [z ->] Hd. rewrite /pro_done Exists_app. by left. Qed.

(* ---- how many rounds a resolution has settled ---- *)

Lemma pro_rounds_tail ps : pro_rounds (pro_tail ps) = (pro_rounds ps - 1)%nat.
Proof.
  induction ps as [| a ps IH]; cbn [pro_tail pro_rounds]; [done |].
  case_decide as Ha; [rewrite IH |]; lia.
Qed.

Lemma pro_done_rounds ps : pro_done ps <-> (0 < pro_rounds ps)%nat.
Proof.
  rewrite /pro_done. induction ps as [| a ps IH]; cbn [pro_rounds].
  - split; [by intros ?%Exists_nil | lia].
  - rewrite Exists_cons IH. case_decide as Ha.
    + split; [intros [H | H]; [by destruct (H Ha) | lia] | intros H; right; lia].
    + split; [intros _; lia | intros _; by left].
Qed.

Lemma pro_from_done r ps : pro_done (pro_from r ps) <-> (r < pro_rounds ps)%nat.
Proof.
  revert ps. induction r as [| r IH]; intros ps; cbn [pro_from].
  - rewrite pro_done_rounds. lia.
  - rewrite IH pro_rounds_tail. lia.
Qed.

Lemma pro_rounds_app ps ps' :
  pro_rounds (ps ++ ps') = (pro_rounds ps + pro_rounds ps')%nat.
Proof.
  induction ps as [| a ps IH]; cbn [app pro_rounds]; [done |].
  rewrite IH. case_decide; lia.
Qed.

Lemma pro_rounds_replicate_0 d : pro_rounds (replicate d 0%nat) = d.
Proof.
  induction d as [| d IH]; cbn [replicate pro_rounds]; [done |].
  rewrite IH. case_decide as H; [| lia]. exfalso. by destruct H.
Qed.

(* an open round's letters count no round, and the ending letter after
   them counts one *)
Lemma pro_rounds_open (g : list nat) : Forall pro_cont g -> pro_rounds g = 0%nat.
Proof.
  induction g as [| a g IH]; [done |].
  rewrite Forall_cons. intros [Ha Hg]. cbn [pro_rounds].
  rewrite decide_True; [| exact Ha]. by rewrite IH.
Qed.

Lemma pro_rounds_group (g : list nat) (t : nat) (z : list nat) :
  Forall pro_cont g -> ~ pro_cont t ->
  pro_rounds (g ++ [t] ++ z) = S (pro_rounds z).
Proof.
  intros Hg Ht. rewrite !pro_rounds_app (pro_rounds_open g Hg).
  cbn [pro_rounds]. rewrite decide_False; [lia | exact Ht].
Qed.

Lemma pro_of_from_done_ext r ps ps' :
  ps `prefix_of` ps' -> (r < pro_rounds ps)%nat ->
  pro_of (pro_from r ps) = pro_of (pro_from r ps').
Proof.
  intros Hp Hr. apply pro_of_done_ext; [by apply pro_from_mono |].
  by apply pro_from_done.
Qed.

(* ---- the four letters are PAIRWISE PREFIX-FREE ---- *)

Lemma pro_alts_prefix_det (a b : nat) :
  (a < length pro_alts)%nat -> (b < length pro_alts)%nat ->
  pro_alts !!! a `prefix_of` pro_alts !!! b -> a = b.
Proof.
  rewrite pro_alts_length. intros Ha Hb.
  destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; try lia;
    try reflexivity;
    intros H; exfalso; revert H; apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* THE WHOLE-BLOCK READING that replaces [line_alts_head_det]'s one-byte
   one: two resolutions below ONE wire have the SAME prologue, and a settled
   one below any forces the other settled too.  This is the ONE fact the
   reconciliation of the discipline's witness with the claim's spends. *)
Lemma pro_of_prefix_free (ps ps' : list nat) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  Forall (fun a => (a < length pro_alts)%nat) ps' -> pro_done ps' ->
  pro_of ps' `prefix_of` pro_of ps -> pro_done ps /\ pro_of ps' = pro_of ps.
Proof.
  revert ps. induction ps' as [| a' t' IH]; intros ps HF HF' Hd Hp.
  { by apply Exists_nil in Hd. }
  rewrite Forall_cons in HF'. destruct HF' as [Ha' HF'].
  rewrite /pro_done Exists_cons in Hd.
  destruct ps as [| a t].
  { exfalso. cbn [pro_of] in Hp.
    apply prefix_nil_inv, app_eq_nil in Hp as [Hnil _].
    exact (pro_alts_nonnil a' Ha' Hnil). }
  rewrite Forall_cons in HF. destruct HF as [Ha HF].
  cbn [pro_of] in Hp |- *.
  assert (Hcmp : pro_alts !!! a' `prefix_of` pro_alts !!! a
                 \/ pro_alts !!! a `prefix_of` pro_alts !!! a').
  { eapply prefix_weak_total;
      [ etrans; [apply prefix_app_r; reflexivity | exact Hp]
      | apply prefix_app_r; reflexivity ]. }
  assert (Haa : a' = a).
  { destruct Hcmp as [Hc | Hc];
      [ by apply pro_alts_prefix_det | symmetry; by apply pro_alts_prefix_det ]. }
  subst a'. apply prefix_app_inv in Hp.
  destruct (decide (pro_cont a)) as [Hc | Hc].
  - rewrite !(pro_more_cont a _ Hc) in Hp |- *.
    destruct Hd as [Hne | Hd]; [done |].
    destruct (IH t HF HF' Hd Hp) as [Hdt Heq].
    split; [by apply Exists_cons; right | by rewrite Heq].
  - rewrite !(pro_more_ne a _ Hc) in Hp |- *.
    split; [by apply Exists_cons; left | reflexivity].
Qed.

(* AN UNSETTLED PROLOGUE ENDS AT A LETTER BOUNDARY, so the byte any longer
   prologue has just past it is the first byte of one of the four letters
   -- and none of those is [echo_line]'s.  This is what refutes "the
   stage's prologue is still open while a disciplined byte arrives". *)
Lemma lookup_app_shift {A} (u v : list A) (n : nat) :
  (u ++ v) !! (length u + n)%nat = v !! n.
Proof.
  rewrite lookup_app_r; [| lia].
  by replace (length u + n - length u)%nat with n by lia.
Qed.

Lemma pro_alts_head_ne_echo (a : nat) (b : bv 8) :
  (a < length pro_alts)%nat -> pro_alts !!! a !! 0%nat = Some b ->
  echo_line !! 0%nat = Some b -> False.
Proof.
  rewrite pro_alts_length. intros Ha Hb Hc.
  destruct a as [|[|[|[|a]]]]; try lia; vm_compute in Hb; injection Hb as Hb;
    subst b; vm_compute in Hc; injection Hc as Hc; discriminate.
Qed.

Lemma pro_of_not_done_next (P P' : list nat) (b : bv 8) :
  Forall (fun a => (a < length pro_alts)%nat) P' ->
  ~ pro_done P ->
  pro_of P `prefix_of` pro_of P' ->
  pro_of P' !! length (pro_of P) = Some b ->
  exists a, (a < length pro_alts)%nat /\ pro_alts !!! a !! 0%nat = Some b.
Proof.
  revert P'. induction P as [| c P IH]; intros P' HF' Hnd Hpre Hlk.
  - destruct P' as [| a t'].
    { exfalso. cbn [pro_of] in Hlk. discriminate. }
    rewrite Forall_cons in HF'. destruct HF' as [Ha HF'].
    exists a. split; [exact Ha |].
    cbn [pro_of length] in Hlk.
    rewrite lookup_app_l in Hlk; [exact Hlk |].
    destruct (pro_alts !!! a) as [| z zs] eqn:Hz;
      [ exfalso; exact (pro_alts_nonnil a Ha Hz) | cbn; lia ].
  - assert (Hc1 : pro_cont c).
    { destruct (decide (pro_cont c)) as [? | Hne]; [done |].
      exfalso. apply Hnd. rewrite /pro_done. by apply Exists_cons; left. }
    assert (HndP : ~ pro_done P).
    { intros H. apply Hnd. rewrite /pro_done Exists_cons. by right. }
    destruct P' as [| a t'].
    { exfalso. cbn [pro_of] in Hpre. rewrite (pro_more_cont c _ Hc1) in Hpre.
      apply prefix_nil_inv, app_eq_nil in Hpre as [Hnil _].
      assert (Hcb : (c < length pro_alts)%nat)
        by (destruct Hc1 as [-> | ->]; rewrite pro_alts_length; lia).
      exact (pro_alts_nonnil c Hcb Hnil). }
    rewrite Forall_cons in HF'. destruct HF' as [Ha HF'].
    cbn [pro_of] in Hpre, Hlk. rewrite (pro_more_cont c _ Hc1) in Hpre, Hlk.
    assert (Hcb : (c < length pro_alts)%nat)
      by (destruct Hc1 as [-> | ->]; rewrite pro_alts_length; lia).
    assert (Haa : a = c).
    { destruct (prefix_weak_total (pro_alts !!! c) (pro_alts !!! a)
                  (pro_alts !!! a ++ pro_more a (pro_of t'))
                  ltac:(etrans; [apply prefix_app_r; reflexivity | exact Hpre])
                  ltac:(apply prefix_app_r; reflexivity)) as [H | H].
      - symmetry. apply pro_alts_prefix_det; [exact Hcb | exact Ha | exact H].
      - apply pro_alts_prefix_det; [exact Ha | exact Hcb | exact H]. }
    subst a. rewrite (pro_more_cont c _ Hc1) in Hpre, Hlk.
    apply prefix_app_inv in Hpre.
    apply (IH t' HF' HndP Hpre).
    rewrite (length_app (pro_alts !!! c) (pro_of P)) in Hlk.
    rewrite (lookup_app_shift (pro_alts !!! c)) in Hlk.
    exact Hlk.
Qed.

(* ---- 2b.  THE LINE ALTERNATIVES AND THE BLOCK ---- *)

(* O5, RULED BY THE OWNER (2026-09-12): allocation failure PRINTS, and what
   it prints is valid output.  After a complete line's '\n' echo the
   continuation is ONE OF
     0  "hello world\n$ "                 the good one: echo ran
     1  "exec echo failed\n$ "            sh's child could not exec
                                          (user/sh.c:80); it exits 0
     2  "$ "                              the child died before printing
     3  "fork\n"                          sh's fork1 panicked
                                          (user/sh.c:194; panic prints
                                          "%s\n" to fd 2 and exits 1), so
                                          init reaps the SHELL and its outer
                                          loop starts a NEW ROUND -- whose
                                          exec or fork can fail exactly as
                                          round 0's can, which is why the
                                          restart is a fresh PROLOGUE and
                                          not part of this literal
   Alternatives 0, 1 and 2 end in "$ "; ALTERNATIVE 3 DOES NOT -- the
   prologue [alt_blk] appends after it supplies the prompt, or the fork
   diagnostic instead.  Their FIRST bytes are 'h', 'e', '$', 'f' --
   pairwise distinct, which is what makes the LINE choice readable off one
   byte of the wire ([line_alts_head_det]).  A later ruling changes this
   ONE list. *)
(* ECHO'S OUTPUT IS THE LINE MINUS ITS COMMAND NAME.  echo prints its
   arguments joined by single spaces and closed by a newline -- which is
   exactly what [gets] read, with the first word dropped.  So the good
   alternative is not a second literal transcribed beside [echo_line]: it
   is [wl_line] of the line's tail, and then the prompt sh writes once it
   has reaped.  A transcription error here cannot make the two disagree,
   because there is only one of them. *)
Definition echo_line_out : list (bv 8) := wl_line (drop 1 echo_ws).

Lemma echo_line_out_string : echo_line_out = sb "hello world"%string ++ nlb.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma echo_line_out_length : length echo_line_out = 12%nat.
Proof. vm_compute. reflexivity. Qed.

Definition line_alts : list (list (bv 8)) :=
  [ echo_line_out ++ sb "$ "%string;
    sb "exec echo failed"%string ++ nlb ++ sb "$ "%string;
    sb "$ "%string;
    sb "fork"%string ++ nlb ].

Lemma line_alts_0 : line_alts !!! 0%nat = echo_line_out ++ sb "$ "%string.
Proof. reflexivity. Qed.

(* ---- WHERE ECHO'S OUTPUT PUTS EACH WORD ------------------------------ *)
(* Argument [i] of the line is word [i - 1] of the TAIL, because echo does
   not print the command name.  These four are the whole of the cursor a
   write chain over the words walks: where a word starts, what follows it
   while another word remains, and what follows the last one. *)
Definition echo_ocur (i : nat) : nat := wl_off 0%nat (drop 1 echo_ws) (i - 1).

Lemma echo_ws_drop (i : nat) :
  (1 <= i)%nat -> drop 1 echo_ws !! (i - 1)%nat = echo_ws !! i.
Proof.
  intro Hi. rewrite lookup_drop. f_equal. lia.
Qed.

(* the alternative opens with the output, and the prompt is past it *)
Lemma echo_alt0_out (p : nat) :
  (p < length echo_line_out)%nat ->
  line_alts !!! 0%nat !! p = echo_line_out !! p.
Proof.
  intro Hp. rewrite line_alts_0.
  exact (lookup_app_l echo_line_out (sb "$ "%string) p Hp).
Qed.

Lemma echo_ocur_S (i : nat) (w : list (bv 8)) :
  (1 <= i)%nat -> echo_ws !! i = Some w ->
  echo_ocur (S i) = S (echo_ocur i + length w)%nat.
Proof.
  intros Hi Hw. rewrite /echo_ocur.
  replace (S i - 1)%nat with (S (i - 1)) by lia.
  exact (wl_off_S_at (drop 1 echo_ws) 0%nat (i - 1)%nat w
           ltac:(rewrite echo_ws_drop; [exact Hw | exact Hi])).
Qed.

Lemma echo_ocur_lt (i : nat) (w : list (bv 8)) (j : nat) :
  (1 <= i)%nat -> echo_ws !! i = Some w -> (j <= length w)%nat ->
  (echo_ocur i + j < length echo_line_out)%nat.
Proof.
  intros Hi Hw Hj. rewrite /echo_ocur /echo_line_out.
  exact (wl_off_lt_line (drop 1 echo_ws) (i - 1)%nat w j
           ltac:(rewrite echo_ws_drop; [exact Hw | exact Hi]) Hj).
Qed.

(* a separator follows a word while another argument remains... *)
Lemma echo_out_sep (i : nat) (w : list (bv 8)) :
  (1 <= i)%nat -> echo_ws !! i = Some w -> (S i < length echo_ws)%nat ->
  line_alts !!! 0%nat !! (echo_ocur i + length w)%nat = Some wl_sp.
Proof.
  intros Hi Hw Hlt.
  assert (Hd : drop 1 echo_ws !! (i - 1)%nat = Some w)
    by (rewrite echo_ws_drop; [exact Hw | exact Hi]).
  rewrite (echo_alt0_out (echo_ocur i + length w)%nat
             (echo_ocur_lt i w (length w) Hi Hw ltac:(lia))).
  rewrite /echo_line_out /echo_ocur.
  apply (wl_line_sep (drop 1 echo_ws) (i - 1)%nat w Hd).
  rewrite length_drop. lia.
Qed.

(* ...and the closing newline follows the last, which is where the output
   ends *)
Lemma echo_out_last (i : nat) (w : list (bv 8)) :
  (1 <= i)%nat -> echo_ws !! i = Some w -> S i = length echo_ws ->
  S (echo_ocur i + length w)%nat = length echo_line_out
  /\ line_alts !!! 0%nat !! (echo_ocur i + length w)%nat = Some wl_nl.
Proof.
  intros Hi Hw Hlast.
  assert (Hd : drop 1 echo_ws !! (i - 1)%nat = Some w)
    by (rewrite echo_ws_drop; [exact Hw | exact Hi]).
  assert (Hend : (echo_ocur i + length w)%nat
                 = length (wl_body (drop 1 echo_ws))).
  { rewrite /echo_ocur.
    rewrite (wl_off_last (drop 1 echo_ws) 0%nat (i - 1)%nat w Hd
               ltac:(rewrite length_drop; lia)).
    lia. }
  split.
  - rewrite Hend /echo_line_out wl_line_length. lia.
  - rewrite (echo_alt0_out (echo_ocur i + length w)%nat
               (echo_ocur_lt i w (length w) Hi Hw ltac:(lia))).
    rewrite /echo_line_out Hend. exact (wl_line_nl_at (drop 1 echo_ws)).
Qed.

(* the alternative is the output and then the prompt, so its length is
   the output's plus two -- not a number *)
Lemma line_alts_0_length :
  length (line_alts !!! 0%nat) = (length echo_line_out + 2)%nat.
Proof. rewrite line_alts_0 length_app. by vm_compute (length (sb "$ "%string)). Qed.

Lemma line_alts_length : length line_alts = 4.
Proof. reflexivity. Qed.

(* how many shells have already died on their own fork panic BEFORE line
   [i] -- so line [i], if it took alternative 3, opens round
   [S (pro_idx cs i)], and the block that closes line [q-1] reads round
   [pro_idx cs q], round 0 at the head of the transcript included. *)
Fixpoint pro_idx (cs : list nat) (i : nat) : nat :=
  match i with
  | 0%nat => 0%nat
  | S i' => (pro_idx cs i' + if decide (cs !!! i' = 3%nat) then 1 else 0)%nat
  end.

Lemma pro_idx_S cs i :
  pro_idx cs (S i)
  = (pro_idx cs i + if decide (cs !!! i = 3%nat) then 1 else 0)%nat.
Proof. reflexivity. Qed.

Lemma pro_idx_S3 cs i : cs !!! i = 3%nat -> pro_idx cs (S i) = S (pro_idx cs i).
Proof. intros H. rewrite pro_idx_S decide_True; [lia | exact H]. Qed.

Lemma pro_idx_Sne cs i : cs !!! i <> 3%nat -> pro_idx cs (S i) = pro_idx cs i.
Proof. intros H. rewrite pro_idx_S decide_False; [lia | exact H]. Qed.

Lemma pro_idx_mono cs i j : (i <= j)%nat -> (pro_idx cs i <= pro_idx cs j)%nat.
Proof.
  intros Hij. induction j as [| j IH].
  - assert (i = 0%nat) by lia. by subst i.
  - destruct (decide (i = S j)) as [-> | Hne]; [done |].
    rewrite pro_idx_S.
    assert (pro_idx cs i <= pro_idx cs j)%nat by (apply IH; lia).
    case_decide; lia.
Qed.

Lemma pro_idx_le cs i : (pro_idx cs i <= i)%nat.
Proof.
  induction i as [| i IH]; [cbn; lia |].
  rewrite pro_idx_S. case_decide; lia.
Qed.

(* ONE COMPLETED LINE'S OUTPUT: the echo of its seventeen bytes, the
   continuation this run took, and -- if that continuation was the shell's
   own fork panic -- the PROLOGUE of the round init then starts.  [cs]
   records the continuation per line and [ps] the prologue choices of the
   whole run, in wire order; out of range both read as alternative 0, which
   keeps [alt_seq] total and its step law unconditional -- the choices are
   pinned by the wire wherever the discipline actually looks at them. *)
Definition alt_cont (ps cs : list nat) (i : nat) : list (bv 8) :=
  line_alts !!! (cs !!! i)
  ++ (if decide (cs !!! i = 3%nat)
      then pro_of (pro_from (S (pro_idx cs i)) ps) else []).

Definition alt_blk (ps cs : list nat) (i : nat) : list (bv 8) :=
  echo_line ++ alt_cont ps cs i.

Definition alt_seq (ps cs : list nat) (q : nat) : list (bv 8) :=
  concat (alt_blk ps cs <$> List.seq 0 q).

Lemma alt_seq_0 ps cs : alt_seq ps cs 0 = [].
Proof. reflexivity. Qed.

Lemma alt_seq_S ps cs q : alt_seq ps cs (S q) = alt_seq ps cs q ++ alt_blk ps cs q.
Proof.
  rewrite /alt_seq List.seq_S fmap_app concat_app Nat.add_0_l /=.
  by rewrite app_nil_r.
Qed.

(* ---- THE LENGTHS, ONCE ----------------------------------------------- *)
(* [length echo_line] is what every consumer divides the session by, and
   an unguarded [rewrite !length_app] unfolds it into the arity of the
   join the line IS -- leaving [lia] with two different atoms.  So the
   three decompositions a consumer needs are proved HERE, with the
   [length_app] instances pinned, and nobody above takes a session apart
   with [length_app] again. *)
Lemma alt_blk_length ps cs q :
  length (alt_blk ps cs q)
  = (length echo_line + length (alt_cont ps cs q))%nat.
Proof. rewrite /alt_blk (length_app echo_line _). reflexivity. Qed.

Lemma alt_seq_S_length ps cs q :
  length (alt_seq ps cs (S q))
  = (length (alt_seq ps cs q) + length echo_line
     + length (alt_cont ps cs q))%nat.
Proof.
  rewrite alt_seq_S (length_app (alt_seq ps cs q) _) alt_blk_length. lia.
Qed.

(* ---- the two extensionality laws the transcript needs ---- *)

Lemma pro_idx_ext cs1 cs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  forall j, (j <= q)%nat -> pro_idx cs1 j = pro_idx cs2 j.
Proof.
  intros Hj j. induction j as [| j IH]; intros Hjq; [done |].
  rewrite !pro_idx_S IH; [| lia]. by rewrite (Hj j ltac:(lia)).
Qed.

Lemma pro_idx_take cs q i : (i <= q)%nat -> pro_idx (take q cs) i = pro_idx cs i.
Proof.
  intros Hi. apply (pro_idx_ext _ _ q); [| lia].
  intros j Hj. rewrite list_lookup_total_alt lookup_take; [| lia].
  by rewrite -list_lookup_total_alt.
Qed.

(* THE CHOICE BYTE EXTENDS AN OPEN ROUND.  [pro_of] of an unresolved
   resolution ends at a letter boundary, so filing the round's next letter
   appends its bytes -- the first of which is the byte the writer is
   putting out. *)
Lemma pro_of_snoc_head (ps : list nat) (a : nat) (b : bv 8) :
  ~ pro_done ps -> pro_alts !!! a !! 0%nat = Some b ->
  (pro_of ps ++ [b]) `prefix_of` pro_of (ps ++ [a]).
Proof.
  intros Hnd Hb. rewrite (pro_of_open_app ps [a] Hnd) pro_of_singleton.
  apply prefix_app.
  destruct (pro_alts !!! a) as [| z zs] eqn:Hz; [discriminate |].
  cbn in Hb. injection Hb as <-. by eexists.
Qed.

(* ...and dropping SETTLED rounds commutes with filing the open one's. *)
Lemma pro_tail_snoc (ps : list nat) (a : nat) :
  (0 < pro_rounds ps)%nat -> pro_tail (ps ++ [a]) = pro_tail ps ++ [a].
Proof.
  induction ps as [| c ps IH]; cbn [pro_rounds pro_tail app]; [lia |].
  case_decide as Hc; [| done]. intros H. by apply IH.
Qed.

Lemma pro_from_snoc_le (r : nat) (ps : list nat) (a : nat) :
  (r <= pro_rounds ps)%nat -> pro_from r (ps ++ [a]) = pro_from r ps ++ [a].
Proof.
  revert ps. induction r as [| r IH]; intros ps Hr; [done |].
  cbn [pro_from]. rewrite pro_tail_snoc; [| lia].
  apply IH. rewrite pro_rounds_tail. lia.
Qed.

(* THE SAME, FOR A WHOLE BLOCK OF CHOICES: once the first [r] rounds have
   settled, dropping them commutes with filing anything at all. *)
Lemma pro_from_app_le (r : nat) (ps z : list nat) :
  (r <= pro_rounds ps)%nat -> pro_from r (ps ++ z) = pro_from r ps ++ z.
Proof.
  intros Hr. induction z as [| a z IH] using rev_ind.
  - by rewrite !app_nil_r.
  - rewrite app_assoc (pro_from_snoc_le r (ps ++ z) a); last first.
    { rewrite pro_rounds_app. lia. }
    rewrite IH. by rewrite -app_assoc.
Qed.

Lemma pro_from_nil (r : nat) : pro_from r [] = [].
Proof. induction r as [| r IH]; [done |]. by cbn [pro_from pro_tail]. Qed.

(* FILING A LETTER AT AN OPEN ROUND LEAVES NOTHING OVER: the round is
   either still open (a continuing letter) or closed by exactly that
   letter, so the resolution never runs ahead of the wire.  ([pro_tail]
   of an open [ps] is [[]], and appending one entry leaves exactly that.) *)
Lemma pro_tail_open_snoc (ps : list nat) (a : nat) :
  ~ pro_done ps -> pro_tail (ps ++ [a]) = [].
Proof.
  induction ps as [| c ps IH]; intros Hnd.
  - cbn [app pro_tail]. by case_decide.
  - assert (Hc1 : pro_cont c).
    { destruct (decide (pro_cont c)) as [? | Hne]; [done |].
      exfalso. apply Hnd. rewrite /pro_done. by apply Exists_cons; left. }
    cbn [app pro_tail]. rewrite decide_True; [| exact Hc1].
    apply IH. intros H. apply Hnd. rewrite /pro_done Exists_cons. by right.
Qed.

(* AN OPEN PROLOGUE GROWS STRICTLY when a letter is filed -- every letter
   is non-empty, so at least its first byte is new.  This is what makes
   the resolution READABLE OFF THE LENGTH of what was written. *)
Lemma pro_of_open_snoc_lt (ps : list nat) (a : nat) :
  ~ pro_done ps -> (a < length pro_alts)%nat ->
  (length (pro_of ps) < length (pro_of (ps ++ [a])))%nat.
Proof.
  intros Hnd Ha.
  destruct (pro_alts !!! a) as [| c bs] eqn:Hz;
    [ exfalso; exact (pro_alts_nonnil a Ha Hz) |].
  assert (Hb : pro_alts !!! a !! 0%nat = Some c) by (by rewrite Hz).
  pose proof (pro_of_snoc_head ps a c Hnd Hb) as Hpre.
  apply prefix_length in Hpre. rewrite (length_app (pro_of ps) [c]) in Hpre.
  cbn [length] in Hpre. lia.
Qed.

(* ...hence an OPEN prologue determines its resolution: nothing can be
   appended without moving the bytes. *)
Lemma pro_of_open_app_inj (ps z : list nat) :
  ~ pro_done ps -> Forall (fun a => (a < length pro_alts)%nat) z ->
  pro_of (ps ++ z) = pro_of ps -> z = [].
Proof.
  intros Hnd HF Heq. destruct z as [| a z]; [done | exfalso].
  rewrite Forall_cons in HF. destruct HF as [Ha _].
  assert (Hp : pro_of (ps ++ [a]) `prefix_of` pro_of (ps ++ a :: z)).
  { apply pro_of_mono. exists z. by rewrite -app_assoc. }
  apply prefix_length in Hp. rewrite Heq in Hp.
  pose proof (pro_of_open_snoc_lt ps a Hnd Ha). lia.
Qed.

(* ...and a settled extension of an open round is STRICTLY longer *)
Lemma pro_of_open_done_lt (ps ps' : list nat) :
  ~ pro_done ps -> pro_done ps' -> ps `prefix_of` ps' ->
  Forall (fun a => (a < length pro_alts)%nat) ps' ->
  (length (pro_of ps) < length (pro_of ps'))%nat.
Proof.
  intros Hnd Hd [z ->] HF.
  destruct z as [| a z].
  { exfalso. rewrite app_nil_r in Hd. exact (Hnd Hd). }
  apply Forall_app in HF as [_ HF]. rewrite Forall_cons in HF.
  destruct HF as [Ha _].
  pose proof (pro_of_open_snoc_lt ps a Hnd Ha) as Hlt.
  assert (Hp : pro_of (ps ++ [a]) `prefix_of` pro_of (ps ++ a :: z)).
  { apply pro_of_mono. exists z. by rewrite -app_assoc. }
  apply prefix_length in Hp. lia.
Qed.

(* THE BANNER OF THE j-TH FAILED SUB-ROUND.  An OPEN prologue with [j]
   failures behind it is [(banner ++ "init: exec sh failed\n")^j], so the
   banner init files next starts at [pro_round * j] -- the ONE arithmetic
   fact init's restart loop needs, at an arbitrary j and with no
   [vm_compute]. *)
Lemma pro_alts_1 : pro_alts !!! 1%nat = u_execfail.
Proof. reflexivity. Qed.

Lemma pro_alts_3 : pro_alts !!! 3%nat = u_banner.
Proof. reflexivity. Qed.

Lemma pro_fail_0 : pro_fail 0 = [].
Proof. reflexivity. Qed.

Lemma pro_fail_S (j : nat) : pro_fail (S j) = pro_fail j ++ [3%nat; 1%nat].
Proof. rewrite /pro_fail. apply concat_replicate_S. Qed.

Lemma pro_fail_cont (j : nat) : Forall pro_cont (pro_fail j).
Proof.
  induction j as [| j IH]; [constructor |].
  rewrite pro_fail_S Forall_app. split; [exact IH |].
  constructor; [by right | constructor; [by left | constructor]].
Qed.

Lemma pro_fail_bound (j : nat) :
  Forall (fun a => (a < length pro_alts)%nat) (pro_fail j).
Proof.
  eapply Forall_impl; [exact (pro_fail_cont j) |].
  intros a [-> | ->]; rewrite pro_alts_length; lia.
Qed.

Lemma pro_done_cont (g : list nat) : Forall pro_cont g -> ~ pro_done g.
Proof.
  intros HF Hd. rewrite /pro_done Exists_exists in Hd.
  destruct Hd as (a & Ha & Hne). apply Hne.
  exact (proj1 (Forall_forall _ _) HF a Ha).
Qed.

Lemma pro_done_fail (j : nat) : ~ pro_done (pro_fail j).
Proof. exact (pro_done_cont _ (pro_fail_cont j)). Qed.

Lemma pro_of_fail_length (j : nat) :
  length (pro_of (pro_fail j)) = (pro_round * j)%nat.
Proof.
  induction j as [| j IH]; [reflexivity |].
  rewrite pro_fail_S (pro_of_open_app _ _ (pro_done_fail j)) length_app IH.
  assert (H31 : length (pro_of [3%nat; 1%nat]) = pro_round).
  { rewrite /pro_round. vm_compute. reflexivity. }
  rewrite H31. lia.
Qed.

Lemma pro_of_fail_banner (j i : nat) (b : bv 8) :
  u_banner !! i = Some b ->
  pro_of (pro_fail j ++ [3%nat]) !! (pro_round * j + i)%nat = Some b.
Proof.
  intros Hb.
  rewrite (pro_of_open_app _ _ (pro_done_fail j)) pro_of_singleton pro_alts_3.
  rewrite -pro_of_fail_length lookup_app_shift. exact Hb.
Qed.

Lemma pro_idx_app_le (cs z : list nat) (q : nat) :
  (q <= length cs)%nat -> pro_idx (cs ++ z) q = pro_idx cs q.
Proof.
  intros Hq. symmetry. apply (pro_idx_ext cs (cs ++ z) q); [| lia].
  intros j Hj. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Lemma alt_seq_ext ps cs1 cs2 q :
  (forall j, (j < q)%nat -> cs1 !!! j = cs2 !!! j) ->
  alt_seq ps cs1 q = alt_seq ps cs2 q.
Proof.
  intros Hj. induction q as [| q IH]; [done |].
  rewrite !alt_seq_S IH; [| intros j Hjq; apply Hj; lia].
  rewrite /alt_blk /alt_cont (Hj q ltac:(lia)).
  by rewrite (pro_idx_ext cs1 cs2 (S q) Hj q ltac:(lia)).
Qed.

(* ...and the one for the PROLOGUES: only the rounds the first [q] lines
   enter are read, which is what makes a lower bound of [ps] worth its
   transcript. *)
Lemma alt_seq_ps_ext ps1 ps2 cs q :
  (forall r, (r <= pro_idx cs q)%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  alt_seq ps1 cs q = alt_seq ps2 cs q.
Proof.
  induction q as [| q IH]; intros Hr; [done |].
  assert (Hle : (pro_idx cs q <= pro_idx cs (S q))%nat)
    by (apply pro_idx_mono; lia).
  rewrite !alt_seq_S IH; [| intros r Hrq; apply Hr; lia].
  rewrite /alt_blk /alt_cont. case_decide as H3; [| done].
  rewrite (Hr (S (pro_idx cs q))); [done |].
  rewrite (pro_idx_S3 cs q H3). lia.
Qed.

(* ---- 2c.  THE SESSION ---- *)

(* THE EXPECTED SESSION TRANSCRIPT for [n] input bytes: the prologue this
   run opened with, then one block per COMPLETED line, then the echo of the
   bytes of the line in progress.  It depends on the input only through its
   LENGTH -- which is what D3 buys: under [disc_seg] the input IS determined
   by its length. *)
Definition sess_n (ps cs : list nat) (n : nat) : list (bv 8) :=
  pro_of ps ++ alt_seq ps cs (n `div` length echo_line)
            ++ take (n `mod` length echo_line) echo_line.

Definition sess (ps cs : list nat) (l : list (bv 8)) : list (bv 8) :=
  sess_n ps cs (length l).

Lemma sess_n_0 ps cs : sess_n ps cs 0 = pro_of ps.
Proof.
  rewrite /sess_n Nat.Div0.div_0_l Nat.Div0.mod_0_l alt_seq_0 take_0.
  by rewrite !app_nil_r.
Qed.

(* ...and the session's own, on the same rule *)
Lemma sess_n_length ps cs n :
  length (sess_n ps cs n)
  = (length (pro_of ps) + length (alt_seq ps cs (n `div` length echo_line))
     + (n `mod` length echo_line) `min` length echo_line)%nat.
Proof.
  rewrite /sess_n (length_app (pro_of ps) _) (length_app (alt_seq ps cs _) _)
    length_take. lia.
Qed.

Lemma sess_n_ps_ext ps1 ps2 cs n :
  (forall r, (r <= pro_idx cs (n `div` length echo_line))%nat ->
     pro_of (pro_from r ps1) = pro_of (pro_from r ps2)) ->
  sess_n ps1 cs n = sess_n ps2 cs n.
Proof.
  intros Hr. rewrite /sess_n (Hr 0%nat ltac:(lia)).
  by rewrite (alt_seq_ps_ext ps1 ps2 cs _ Hr).
Qed.

(* EVERY PROLOGUE THE FIRST [q] LINES ENTER HAS SETTLED: round 0, and one
   more for every line that took alternative 3.  This is the side condition
   the DISCIPLINE and the CLAIM carry; the stage machine carries the weaker
   one (every block strictly below the current stage). *)
Definition pro_ok (ps cs : list nat) (q : nat) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps
  /\ (pro_idx cs q < pro_rounds ps)%nat.

Global Instance pro_ok_dec ps cs q : Decision (pro_ok ps cs q).
Proof. rewrite /pro_ok. apply _. Defined.

Lemma pro_ok_mono ps cs q q' : (q' <= q)%nat -> pro_ok ps cs q -> pro_ok ps cs q'.
Proof.
  intros Hq [HF Hlt]. split; [exact HF |].
  pose proof (pro_idx_mono cs q' q Hq). lia.
Qed.

(* dropping rounds composes, and it eats settled rounds one at a time *)
Lemma pro_from_add a b ps : pro_from a (pro_from b ps) = pro_from (b + a) ps.
Proof.
  revert ps. induction b as [| b IH]; intros ps; [done |].
  cbn [pro_from Nat.add]. apply IH.
Qed.

Lemma pro_rounds_from r ps : pro_rounds (pro_from r ps) = (pro_rounds ps - r)%nat.
Proof.
  revert ps. induction r as [| r IH]; intros ps; [cbn; lia |].
  cbn [pro_from]. rewrite IH pro_rounds_tail. lia.
Qed.

Lemma pro_from_Forall (P : nat -> Prop) r ps :
  Forall P ps -> Forall P (pro_from r ps).
Proof.
  revert ps. induction r as [| r IH]; intros ps HF; [exact HF |].
  cbn [pro_from]. by apply IH, pro_tail_Forall.
Qed.

Lemma pro_idx_S_le cs i : (pro_idx cs (S i) <= S (pro_idx cs i))%nat.
Proof. rewrite pro_idx_S. case_decide; lia. Qed.

(* THE STAGE'S side condition: every block STRICTLY BELOW stage [n] reads a
   round that has settled.  The round the writer is standing in need not
   have -- it settles at that block's choice byte -- which is exactly the
   difference from [pro_ok]. *)
Definition pro_pin (ps cs : list nat) (n : nat) : Prop :=
  forall q, (length echo_line * q < n)%nat -> (pro_idx cs q < pro_rounds ps)%nat.

Lemma pro_pin_at ps cs n k :
  pro_pin ps cs n -> (k < n)%nat ->
  (pro_idx cs (k `div` length echo_line) < pro_rounds ps)%nat.
Proof.
  intros Hp Hk. apply Hp. pose proof echo_line_pos as HL.
  pose proof (Nat.div_mod_eq k (length echo_line)). lia.
Qed.

Lemma pro_pin_idx_le ps cs n :
  pro_pin ps cs n -> (pro_idx cs (n `div` length echo_line) <= pro_rounds ps)%nat.
Proof.
  intros Hp. pose proof echo_line_pos as HL.
  pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm.
  destruct (decide (length echo_line * (n `div` length echo_line) < n)%nat)
    as [Hlt | Hge].
  - pose proof (Hp (n `div` length echo_line)%nat Hlt). lia.
  - destruct (n `div` length echo_line)%nat as [| m'] eqn:Hm.
    + cbn [pro_idx]. lia.
    + assert (Hlt' : (length echo_line * m' < n)%nat) by lia.
      pose proof (Hp m' Hlt'). pose proof (pro_idx_S_le cs m'). lia.
Qed.

Lemma pro_pin_mono ps ps' cs n :
  ps `prefix_of` ps' -> pro_pin ps cs n -> pro_pin ps' cs n.
Proof.
  intros [z ->] Hp q Hq. pose proof (Hp q Hq).
  rewrite pro_rounds_app. lia.
Qed.

(* the bridge [good_out_of_stage] spends: PADDING the resolution with
   terminated rounds turns the stage's condition into the claim's, at any
   line count the padding covers.  It moves no round the stage has read
   ([pro_of_from_done_ext]). *)
Lemma pro_ok_pad ps cs m d :
  Forall (fun x => (x < length pro_alts)%nat) ps -> (m <= d)%nat ->
  pro_ok (ps ++ replicate (S d) 0%nat) cs m.
Proof.
  intros HF Hm. split.
  - apply Forall_app. split; [exact HF |].
    apply Forall_forall. intros x Hx. apply elem_of_replicate in Hx as [-> _].
    rewrite pro_alts_length. lia.
  - rewrite pro_rounds_app pro_rounds_replicate_0.
    pose proof (pro_idx_le cs m). lia.
Qed.

(* the bridge [good_out_of_stage] spends: PADDING the resolution with one
   terminated round turns the stage's condition into the claim's. *)
Lemma pro_pin_ok ps cs n a :
  pro_pin ps cs n -> Forall (fun x => (x < length pro_alts)%nat) ps ->
  ~ pro_cont a -> (a < length pro_alts)%nat ->
  pro_ok (ps ++ [a]) cs (n `div` length echo_line).
Proof.
  intros Hp HF Hne Ha. split.
  - apply Forall_app. split; [exact HF | by apply Forall_singleton].
  - rewrite pro_rounds_app.
    pose proof (pro_pin_idx_le ps cs n Hp).
    assert (Hr : pro_rounds [a] = 1%nat).
    { cbn [pro_rounds]. rewrite decide_False; [lia | exact Hne]. }
    lia.
Qed.

(* R3's relation: [out] is what the session may have emitted for input [l],
   under SOME resolution of the prologue's and the per-line alternatives. *)
Definition expected_rel (l out : list (bv 8)) : Prop :=
  exists ps cs : list nat,
    pro_ok ps cs (length l `div` length echo_line)
    /\ Forall (fun c => c < length line_alts) cs
    /\ out `prefix_of` sess ps cs l.

(* ---- the arithmetic of one more input byte ---- *)

Lemma div_mod_succ (n m : nat) :
  0 < m ->
  (S n `mod` m = 0 /\ S n `div` m = S (n `div` m) /\ n `mod` m = m - 1)
  \/ (S n `mod` m = S (n `mod` m) /\ S n `div` m = n `div` m).
Proof.
  intros Hm.
  pose proof (Nat.div_mod_eq n m) as Hdm.
  pose proof (Nat.mod_upper_bound n m ltac:(lia)) as Hub.
  destruct (decide (S (n `mod` m) = m)) as [Heq|Hne].
  - left.
    assert (HS : S n = (n `div` m + 1) * m) by nia.
    rewrite HS Nat.Div0.mod_mul Nat.div_mul; [|lia].
    split; [done|]. split; [lia|]. lia.
  - right.
    assert (HS : S n = S (n `mod` m) + n `div` m * m) by nia.
    rewrite HS Nat.Div0.mod_add Nat.mod_small; [|lia].
    split; [done|].
    rewrite Nat.div_add; [|lia]. rewrite Nat.div_small; [lia|lia].
Qed.

Lemma prefix_take_le {A} (l : list A) (n m : nat) :
  n <= m -> take n l `prefix_of` take m l.
Proof.
  intros Hnm.
  assert (H : take n l = take n (take m l)).
  { rewrite take_take Nat.min_l; [done|lia]. }
  rewrite H. apply prefix_take.
Qed.

Lemma sess_n_step ps cs n : sess_n ps cs n `prefix_of` sess_n ps cs (S n).
Proof.
  rewrite /sess_n.
  destruct (div_mod_succ n (length echo_line) echo_line_pos)
    as [(Hm & Hd & Hr)|(Hm & Hd)]; rewrite Hm Hd.
  - rewrite alt_seq_S take_0 app_nil_r.
    apply prefix_app, prefix_app.
    rewrite /alt_blk. apply prefix_app_r, prefix_take.
  - apply prefix_app, prefix_app, prefix_take_le. lia.
Qed.

Lemma sess_n_mono ps cs n m : n <= m -> sess_n ps cs n `prefix_of` sess_n ps cs m.
Proof.
  intros Hnm. replace m with (n + (m - n)) by lia.
  generalize (m - n) as d. intros d. clear Hnm m.
  induction d as [|d IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. etrans; [exact IH | apply sess_n_step].
Qed.

(* R3's monotonicity, both ways round.  In the INPUT LENGTH the resolution
   has to be PADDED: a longer input may complete more lines, each of which
   may be a shell that died on its own fork panic and re-entered the
   prologue, so [pro_ok] at the longer length asks for more settled rounds
   than the shorter one supplies.  Padding with terminated rounds changes no
   round the shorter transcript reads ([pro_of_from_done_ext]). *)
Lemma expected_rel_out_mono l out out' :
  out' `prefix_of` out -> expected_rel l out -> expected_rel l out'.
Proof.
  intros Hp (ps & cs & Hok & Hcs & Hout). exists ps, cs.
  split; [exact Hok|]. split; [exact Hcs|]. by etrans.
Qed.

Lemma expected_rel_ins_mono l l' out :
  length l <= length l' -> expected_rel l out -> expected_rel l' out.
Proof.
  intros Hlen (ps & cs & [HF Hlt] & Hcs & Hout).
  set (pad := replicate (length l') 0%nat).
  assert (Hext : forall r, (r < pro_rounds ps)%nat ->
            pro_of (pro_from r (ps ++ pad)) = pro_of (pro_from r ps)).
  { intros r Hr. symmetry.
    apply (pro_of_from_done_ext r ps (ps ++ pad)); [by eexists | exact Hr]. }
  exists (ps ++ pad), cs. split.
  { split.
    - apply Forall_app. split; [exact HF |].
      apply Forall_forall. intros x Hx. apply elem_of_replicate in Hx as [-> _].
      rewrite pro_alts_length. lia.
    - rewrite pro_rounds_app /pad pro_rounds_replicate_0.
      pose proof (pro_idx_le cs (length l' `div` length echo_line)) as H1.
      pose proof (Nat.Div0.div_le_upper_bound (length l') (length echo_line)
                    (length l') ltac:(pose proof echo_line_pos; nia)) as H2.
      lia. }
  split; [exact Hcs |].
  etrans; [exact Hout |]. rewrite /sess.
  rewrite (sess_n_ps_ext ps (ps ++ pad) cs (length l)); last first.
  { intros r Hr. symmetry. apply Hext. lia. }
  by apply sess_n_mono.
Qed.

Lemma expected_rel_ins_prefix l l' out :
  l `prefix_of` l' -> expected_rel l out -> expected_rel l' out.
Proof. intros Hp. apply expected_rel_ins_mono. by apply prefix_length. Qed.

(* ...and the decomposition D3 gives the session: under [star_prefix] the
   input really is [q] whole lines and a prefix of the next, which is why
   [sess_n] may read only the LENGTH of the input. *)
Lemma star_prefix_decomp (l : list (bv 8)) :
  star_prefix echo_line l ->
  l = concat (replicate (length l `div` length echo_line) echo_line)
      ++ take (length l `mod` length echo_line) echo_line.
Proof.
  intros Hsp.
  pose proof echo_line_pos as HL.
  pose proof (Nat.div_mod_eq (length l) (length echo_line)) as Hdm.
  pose proof (Nat.mod_upper_bound (length l) (length echo_line)
                ltac:(lia)) as Hub.
  assert (Hqn : length l `div` length echo_line <= length l).
  { apply Nat.Div0.div_le_upper_bound. nia. }
  assert (Hsplit : replicate (length l) echo_line
                 = replicate (length l `div` length echo_line) echo_line
                   ++ replicate (length l - length l `div` length echo_line)
                        echo_line).
  { rewrite -replicate_add. f_equal. lia. }
  rewrite {1}Hsp Hsplit concat_app take_app.
  rewrite take_ge; [|rewrite concat_replicate_length; nia].
  rewrite concat_replicate_length. f_equal.
  replace (length l - length l `div` length echo_line * length echo_line)
    with (length l `mod` length echo_line) by nia.
  destruct (decide (length l `mod` length echo_line = 0)) as [Hr0|Hr0].
  { by rewrite Hr0 !take_0. }
  destruct (length l - length l `div` length echo_line) as [|d] eqn:Hd.
  { exfalso. nia. }
  rewrite replicate_S concat_cons take_app_le; [done|lia].
Qed.

(* ====================================================================== *)
(*  3.  THE WIRE THE USER HAD SEEN AT EACH INPUT                           *)
(* ====================================================================== *)

(* the wire the user had seen when each input byte was typed: [in_pres seg]
   lists, in order, the prefix of [seg] STRICTLY BEFORE its i-th
   [ObsUartIn Uart0]. *)
Fixpoint in_pres (seg : list mobs) : list (list mobs) :=
  match seg with
  | [] => []
  | ObsUartIn Uart0 b :: seg' => [] :: ((fun p => ObsUartIn Uart0 b :: p) <$> in_pres seg')
  | e :: seg' => (fun p => e :: p) <$> in_pres seg'
  end.

Lemma in_pres_length seg : length (in_pres seg) = length (ins seg).
Proof.
  induction seg as [|e seg IH]; [done|].
  destruct e as [[] ?|[] ?| |]; cbn; rewrite ?length_fmap IH //.
Qed.

(* AN EVENT THAT IS NOT A CONSOLE INPUT IS INVISIBLE TO THE DISCIPLINE.
   The machine has two 16550s and the discipline reads ONE of them -- the
   console's input side and the console's wire -- so an output byte, and
   ANY event of the other port, leaves both [ins] and [in_pres] alone. *)
Definition not_cons_in (e : mobs) : Prop :=
  match e with ObsUartIn Uart0 _ => False | _ => True end.

Lemma ins_snoc_other e : not_cons_in e -> ins [e] = [].
Proof. destruct e as [[] ?|[] ?| |]; cbn; done. Qed.

Lemma in_pres_snoc_other seg e :
  not_cons_in e -> in_pres (seg ++ [e]) = in_pres seg.
Proof.
  intro He. induction seg as [|x seg IH].
  - destruct e as [[] ?|[] ?| |]; cbn in He |- *; done.
  - destruct x as [[] ?|[] ?| |]; cbn; rewrite IH //.
Qed.

Lemma in_pres_out seg i b : in_pres (seg ++ [ObsUartOut i b]) = in_pres seg.
Proof. apply in_pres_snoc_other. by destruct i. Qed.

Lemma in_pres_in seg b : in_pres (seg ++ [ObsUartIn Uart0 b]) = in_pres seg ++ [seg].
Proof.
  induction seg as [|e seg IH]; [done|].
  destruct e as [[] ?|[] ?| |]; cbn; rewrite IH ?fmap_app //.
Qed.

(* ====================================================================== *)
(*  4.  THE DISCIPLINE (R4)                                               *)
(* ====================================================================== *)

(* D1/D2 AT ONE INPUT POSITION.  [p] is the wire before input [i]: the
   expected transcript for the [i] bytes typed so far is already there.
   Mid-line that transcript ends in the echo of byte [i-1] (D2); at a line
   boundary it ends in the "$ " of the previous line's continuation, and at
   [i = 0] it is init's banner and sh's first prompt (D1).

   The wire is the CONSOLE's, and nothing but the session writes it, so the
   transcript is measured from the start of the wire: there is no kernel
   prefix to skip and no partial prologue to name.  WHAT THIS DOES AND DOES
   NOT CLAIM, as fact: a user who types before the prompt -- or before the
   previous byte's echo -- is outside the discipline, and the theorem says
   nothing about that cycle beyond safety.  Under the discipline at most
   one line (seventeen bytes) is ever outstanding in the console ring,
   which holds 128, so [consoleintr] drops nothing. *)
Definition disc_pt (ps cs : list nat) (i : nat) (p : list mobs) : Prop :=
  sess_n ps cs i `prefix_of` obs_wire Uart0 p.

Global Instance disc_pt_dec ps cs i p : Decision (disc_pt ps cs i p).
Proof. rewrite /disc_pt. apply _. Defined.

(* THE PER-CYCLE DISCIPLINE: D3, and at every input byte D1/D2 under ONE
   resolution of the prologue's and the per-line alternatives.  [pro_ok] is
   stated AT THE INPUT and not once for the segment, because that is where
   it is true: it says every prologue the transcript for THESE [i] bytes
   enters has settled, and a segment the user never typed into enters none
   (and must stay disciplined -- [disc_seg'_nil]). *)
Definition disc_seg' (seg : list mobs) : Prop :=
  disc_seg seg
  /\ exists ps cs : list nat,
       length cs = length (ins seg) `div` length echo_line
       /\ Forall (fun c => c < length line_alts) cs
       /\ forall (i : nat) (p : list mobs),
            in_pres seg !! i = Some p ->
            pro_ok ps cs (i `div` length echo_line) /\ disc_pt ps cs i p.

(* ---- decidability: the choice list is bounded, so the search is finite ---- *)

Fixpoint bounded_lists (k n : nat) : list (list nat) :=
  match n with
  | O => [[]]
  | S n' => (fun p => p.1 :: p.2) <$>
              (List.list_prod (List.seq 0 k) (bounded_lists k n'))
  end.

Lemma elem_of_bounded_lists (k n : nat) (cs : list nat) :
  cs ∈ bounded_lists k n <-> length cs = n /\ Forall (fun c => c < k) cs.
Proof.
  revert cs. induction n as [|n IH]; intros cs; cbn.
  - rewrite elem_of_list_singleton. split.
    + intros ->. split; [done|constructor].
    + intros [Hl _]. by apply nil_length_inv.
  - rewrite elem_of_list_fmap. split.
    + intros ([c cs'] & -> & Hp). cbn.
      apply elem_of_list_In in Hp. apply in_prod_iff in Hp as [Hc Hcs].
      apply in_seq in Hc. apply elem_of_list_In in Hcs.
      apply IH in Hcs as [Hl Hf].
      split; [by rewrite /= Hl|]. rewrite Forall_cons. split; [lia|exact Hf].
    + intros [Hl Hf]. destruct cs as [|c cs']; [done|].
      rewrite Forall_cons in Hf. destruct Hf as [Hc Hf].
      exists (c, cs'). split; [done|].
      apply elem_of_list_In, in_prod_iff. split.
      * apply in_seq. lia.
      * apply elem_of_list_In, IH. split; [by injection Hl|exact Hf].
Qed.

Lemma Forall_imap_pair {A} (P : nat -> A -> Prop) (l : list A) :
  Forall (fun ip => P ip.1 ip.2) (imap (fun i x => (i, x)) l)
  <-> forall i x, l !! i = Some x -> P i x.
Proof.
  rewrite Forall_lookup. split.
  - intros HF i x Hx. apply (HF i (i, x)). by rewrite list_lookup_imap Hx.
  - intros HF i [j x] Hj. rewrite list_lookup_imap in Hj.
    destruct (l !! i) as [y|] eqn:E; [|done]. cbn in Hj. simplify_eq.
    by apply HF.
Qed.

(* ---- the PROLOGUE candidates: the CANONICAL resolutions ----
   [bounded_lists 4 L] would be 4^L and would put the literals below out of
   [vm_compute]'s reach.  A settled round IS its letters -- the continuing
   ones, then one ending letter -- and every letter costs at least two wire
   bytes, so both the number of rounds and each round's length are bounded
   by the segment ([pro_canon], [sess_n_pro_len]), and the search is
   finite. *)
Fixpoint cont_lists (n : nat) : list (list nat) :=
  match n with
  | O => [[]]
  | S n' => (fun p => p.1 :: p.2) <$>
              (List.list_prod [1%nat; 3%nat] (cont_lists n'))
  end.

Lemma elem_of_cont_lists (n : nat) (g : list nat) :
  g ∈ cont_lists n <-> length g = n /\ Forall pro_cont g.
Proof.
  revert g. induction n as [|n IH]; intros g; cbn [cont_lists].
  - rewrite elem_of_list_singleton. split.
    + intros ->. split; [done|constructor].
    + intros [Hl _]. by apply nil_length_inv.
  - rewrite elem_of_list_fmap. split.
    + intros ([c g'] & -> & Hp). cbn.
      apply elem_of_list_In in Hp. apply in_prod_iff in Hp as [Hc Hg].
      apply elem_of_list_In in Hg. apply IH in Hg as [Hl Hf].
      split; [by rewrite /= Hl|]. rewrite Forall_cons. split; [| exact Hf].
      apply elem_of_list_In in Hc. rewrite /pro_cont.
      apply elem_of_cons in Hc as [-> | Hc]; [by left |].
      apply elem_of_list_singleton in Hc. by right.
    + intros [Hl Hf]. destruct g as [|c g']; [done|].
      rewrite Forall_cons in Hf. destruct Hf as [Hc Hf].
      exists (c, g'). split; [done|].
      apply elem_of_list_In, in_prod_iff. split.
      * apply elem_of_list_In. destruct Hc as [-> | ->];
          [apply elem_of_list_here | by apply elem_of_list_further, elem_of_list_here].
      * apply elem_of_list_In, IH. split; [by injection Hl|exact Hf].
Qed.

Definition pro_grp_cands (m : nat) : list (list nat) :=
  mjoin ((fun k => mjoin ((fun g => [g ++ [0%nat]; g ++ [2%nat]])
                          <$> cont_lists k)) <$> List.seq 0 (S m)).

Fixpoint pro_cands (rounds m : nat) : list (list nat) :=
  match rounds with
  | 0%nat => [[]]
  | S r => (fun q => q.1 ++ q.2) <$>
             List.list_prod (pro_grp_cands m) (pro_cands r m)
  end.

Lemma elem_of_pro_grp_cands (m : nat) (g : list nat) (t : nat) :
  Forall pro_cont g -> (length g <= m)%nat -> (t = 0%nat \/ t = 2%nat) ->
  (g ++ [t]) ∈ pro_grp_cands m.
Proof.
  intros Hg Hk Ht. rewrite /pro_grp_cands elem_of_list_join.
  exists (mjoin ((fun g => [g ++ [0%nat]; g ++ [2%nat]]) <$> cont_lists (length g))).
  split.
  - rewrite elem_of_list_join. exists [g ++ [0%nat]; g ++ [2%nat]]. split.
    + destruct Ht as [-> | ->];
        [ apply elem_of_list_here | by apply elem_of_list_further, elem_of_list_here ].
    + apply elem_of_list_fmap. exists g. split; [reflexivity |].
      apply elem_of_cont_lists. by split.
  - apply elem_of_list_fmap. exists (length g). split; [reflexivity |].
    apply elem_of_list_In, in_seq. lia.
Qed.

Lemma elem_of_pro_cands_app (R m : nat) (g rest : list nat) :
  g ∈ pro_grp_cands m -> rest ∈ pro_cands R m -> (g ++ rest) ∈ pro_cands (S R) m.
Proof.
  intros Hg Hr. cbn [pro_cands]. apply elem_of_list_fmap.
  exists (g, rest). split; [reflexivity |].
  apply elem_of_list_In, in_prod; by apply elem_of_list_In.
Qed.

Lemma pro_cont_bound (a : nat) : pro_cont a -> (a < length pro_alts)%nat.
Proof. intros [-> | ->]; rewrite pro_alts_length; lia. Qed.

Lemma pro_grp_cands_Forall m g :
  g ∈ pro_grp_cands m -> Forall (fun a => (a < length pro_alts)%nat) g.
Proof.
  rewrite /pro_grp_cands elem_of_list_join. intros (l & Hg & Hl).
  apply elem_of_list_fmap in Hl as (k & -> & _).
  rewrite elem_of_list_join in Hg. destruct Hg as (l2 & Hg & Hl2).
  apply elem_of_list_fmap in Hl2 as (g0 & -> & Hg0).
  apply elem_of_cont_lists in Hg0 as [_ Hc].
  assert (Hrep : Forall (fun a => (a < length pro_alts)%nat) g0).
  { eapply Forall_impl; [exact Hc |]. exact pro_cont_bound. }
  apply elem_of_cons in Hg as [-> | Hg];
    [| apply elem_of_list_singleton in Hg; rewrite Hg];
    (apply Forall_app; split; [exact Hrep |];
     apply Forall_singleton; rewrite pro_alts_length; lia).
Qed.

Lemma pro_cands_Forall R m g :
  g ∈ pro_cands R m -> Forall (fun a => (a < length pro_alts)%nat) g.
Proof.
  revert g. induction R as [| R IH]; intros g Hg; cbn [pro_cands] in Hg.
  - apply elem_of_list_singleton in Hg as ->. constructor.
  - apply elem_of_list_fmap in Hg as ([g1 g2] & -> & Hp). cbn.
    apply elem_of_list_In, in_prod_iff in Hp as [H1 H2].
    apply Forall_app. split.
    + by apply (pro_grp_cands_Forall m), elem_of_list_In.
    + by apply IH, elem_of_list_In.
Qed.

Lemma pro_cands_nonempty (R m : nat) : exists g, g ∈ pro_cands R m.
Proof.
  induction R as [| R IH]; [exists []; by apply elem_of_list_singleton |].
  destruct IH as [g Hg]. exists (([] ++ [0%nat]) ++ g).
  apply elem_of_pro_cands_app; [| exact Hg].
  apply elem_of_pro_grp_cands; [constructor | cbn; lia | by left].
Qed.

(* ---- the canonical form of one round, and of a whole resolution ---- *)

(* a settled resolution starts with a round: continuing letters, then an
   ending one, then the rest *)
Lemma pro_of_first_group (ps : list nat) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> pro_done ps ->
  exists (g : list nat) (t : nat) (z : list nat),
    ps = g ++ [t] ++ z /\ Forall pro_cont g /\ (t = 0%nat \/ t = 2%nat)
    /\ (length g <= length (pro_of ps))%nat.
Proof.
  induction ps as [| a ps IH]; intros HF Hd.
  { by apply Exists_nil in Hd. }
  rewrite Forall_cons in HF. destruct HF as [Ha HF].
  rewrite /pro_done Exists_cons in Hd.
  destruct (decide (pro_cont a)) as [Hc | Hne].
  - destruct Hd as [Hn | Hd]; [done |].
    destruct (IH HF Hd) as (g & t & z & Heq & Hg & Ht & Hk).
    exists (a :: g), t, z. split; [by rewrite Heq |]. split; [by constructor |].
    split; [exact Ht |].
    cbn [pro_of length]. rewrite (pro_more_cont a _ Hc) length_app.
    destruct (pro_alts !!! a) as [| y ys] eqn:Hy;
      [ exfalso; exact (pro_alts_nonnil a Ha Hy) | cbn [length]; lia ].
  - exists [], a, ps. split; [reflexivity |]. split; [constructor |].
    split; [| cbn; lia].
    rewrite pro_alts_length in Ha. rewrite /pro_cont in Hne.
    destruct a as [|[|[|[|a]]]]; [by left | exfalso; apply Hne; by left
                                 | by right | exfalso; apply Hne; by right | lia].
Qed.

Lemma pro_tail_group (g : list nat) (t : nat) (z : list nat) :
  Forall pro_cont g -> ~ pro_cont t -> pro_tail (g ++ [t] ++ z) = z.
Proof.
  intros Hg Ht. induction g as [| a g IH]; cbn [app pro_tail].
  - by rewrite decide_False.
  - rewrite Forall_cons in Hg. destruct Hg as [Ha Hg].
    rewrite decide_True; [| exact Ha]. by apply IH.
Qed.

Lemma pro_of_group_app (g : list nat) (t : nat) (z : list nat) :
  Forall pro_cont g -> ~ pro_cont t ->
  pro_of (g ++ [t] ++ z) = pro_of (g ++ [t]).
Proof.
  intros Hg Ht. induction g as [| a g IH]; cbn [app pro_of].
  - by rewrite !(pro_more_ne t _ Ht).
  - rewrite Forall_cons in Hg. destruct Hg as [Ha Hg].
    by rewrite !(pro_more_cont a _ Ha) IH.
Qed.

Lemma pro_canon (R m : nat) : forall ps : list nat,
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  (forall r, (r < R)%nat -> (r < pro_rounds ps)%nat
             /\ (length (pro_of (pro_from r ps)) <= m)%nat) ->
  exists ps0, ps0 ∈ pro_cands R m
    /\ pro_rounds ps0 = R
    /\ (forall r, (r < R)%nat -> pro_of (pro_from r ps0) = pro_of (pro_from r ps)).
Proof.
  induction R as [| R IH]; intros ps HF Hb.
  { exists []. split; [by apply elem_of_list_singleton |].
    split; [reflexivity |]. intros r Hr. lia. }
  destruct (Hb 0%nat ltac:(lia)) as [Hr0 Hm0]. cbn [pro_from] in Hm0.
  assert (Hd : pro_done ps) by (apply (pro_from_done 0%nat ps); exact Hr0).
  destruct (pro_of_first_group ps HF Hd) as (g & t & z & Heq & Hg & Ht & Hk).
  assert (Htne : ~ pro_cont t) by (destruct Ht as [-> | ->]; intros [H | H]; lia).
  destruct (IH (pro_tail ps) (pro_tail_Forall _ _ HF))
    as (ps1 & Hin1 & Hrd1 & Hag1).
  { intros r Hr. destruct (Hb (S r) ltac:(lia)) as [H1 H2].
    cbn [pro_from] in H2. rewrite pro_rounds_tail. split; [lia | exact H2]. }
  exists ((g ++ [t]) ++ ps1). split.
  { apply elem_of_pro_cands_app; [| exact Hin1].
    apply elem_of_pro_grp_cands; [exact Hg | lia | exact Ht]. }
  split.
  { rewrite -app_assoc pro_rounds_group; [by rewrite Hrd1 | exact Hg | exact Htne]. }
  intros r Hr. destruct r as [| r].
  - cbn [pro_from]. rewrite -app_assoc (pro_of_group_app g t ps1 Hg Htne).
    rewrite Heq (pro_of_group_app g t z Hg Htne). reflexivity.
  - cbn [pro_from]. rewrite -app_assoc (pro_tail_group g t ps1 Hg Htne).
    apply Hag1. lia.
Qed.

(* ---- the bound the discipline itself supplies ---- *)

Lemma in_pres_prefix_all (seg : list mobs) :
  Forall (fun p => p `prefix_of` seg) (in_pres seg).
Proof.
  induction seg as [| e seg IH]; [constructor |].
  destruct e as [[] c | [] c | |]; cbn [in_pres];
    try (apply Forall_fmap; eapply Forall_impl; [exact IH |];
         intros q Hq; rewrite /compose; by apply prefix_cons).
  constructor; [apply prefix_nil |].
  apply Forall_fmap. eapply Forall_impl; [exact IH |].
  intros q Hq. rewrite /compose. by apply prefix_cons.
Qed.

Lemma in_pres_prefix (seg : list mobs) (i : nat) (p : list mobs) :
  in_pres seg !! i = Some p -> p `prefix_of` seg.
Proof. intros Hi. exact (Forall_lookup_1 _ _ _ _ (in_pres_prefix_all seg) Hi). Qed.

Lemma obs_wire_length (i : uart_id) (s : list mobs) :
  (length (obs_wire i s) <= length s)%nat.
Proof.
  induction s as [| e s IH]; [done |].
  destruct e as [j b | j b | |]; cbn [obs_wire length];
    repeat case_decide; cbn [length]; lia.
Qed.

(* EVERY ROUND THE TRANSCRIPT ENTERS IS ON THE WIRE, so the search space is
   bounded by the segment. *)
Lemma alt_seq_pro_len ps cs q r :
  (r <= pro_idx cs q)%nat ->
  (length (pro_of (pro_from r ps))
   <= length (pro_of ps) + length (alt_seq ps cs q))%nat.
Proof.
  revert r. induction q as [| q IH]; intros r Hr.
  - assert (r = 0%nat) by (cbn in Hr; lia). subst r. cbn [pro_from]. lia.
  - rewrite alt_seq_S length_app.
    destruct (decide (r <= pro_idx cs q)%nat) as [Hle | Hgt].
    + pose proof (IH r Hle). lia.
    + assert (H3 : cs !!! q = 3%nat).
      { destruct (decide (cs !!! q = 3%nat)) as [? | Hn]; [done |].
        exfalso. rewrite (pro_idx_Sne cs q Hn) in Hr. lia. }
      rewrite (pro_idx_S3 cs q H3) in Hr.
      assert (Hre : r = S (pro_idx cs q)) by lia.
      rewrite /alt_blk /alt_cont !length_app decide_True; [| exact H3].
      rewrite Hre. lia.
Qed.

Lemma sess_n_pro_len ps cs n r :
  (r <= pro_idx cs (n `div` length echo_line))%nat ->
  (length (pro_of (pro_from r ps)) <= length (sess_n ps cs n))%nat.
Proof.
  intros Hr. rewrite /sess_n
    (length_app (pro_of ps) _) (length_app (alt_seq ps cs _) _).
  pose proof (alt_seq_pro_len ps cs (n `div` length echo_line) r Hr). lia.
Qed.

(* ---- the constructor the literals below spend ---- *)

Definition disc_pt_all (ps cs : list nat) (seg : list mobs) : Prop :=
  Forall (fun ip => pro_ok ps cs (ip.1 `div` length echo_line)
                    /\ disc_pt ps cs ip.1 ip.2)
    (imap (fun i x => (i, x)) (in_pres seg)).

Global Instance disc_pt_all_dec ps cs seg : Decision (disc_pt_all ps cs seg).
Proof. rewrite /disc_pt_all. apply _. Defined.

Lemma disc_seg'_intro (seg : list mobs) (ps cs : list nat) :
  disc_seg seg ->
  length cs = (length (ins seg) `div` length echo_line)%nat ->
  Forall (fun c => (c < length line_alts)%nat) cs ->
  disc_pt_all ps cs seg ->
  disc_seg' seg.
Proof.
  intros Hd Hl Hf Hall. split; [exact Hd |]. exists ps, cs.
  split; [exact Hl |]. split; [exact Hf |]. by apply Forall_imap_pair.
Qed.

(* the intro direction at an EXPLICIT predicate: [apply]'s higher-order
   unification cannot guess [P] out of a conjunction. *)
Lemma Forall_imap_pair_intro {A} (P : nat -> A -> Prop) (l : list A) :
  (forall i x, l !! i = Some x -> P i x) ->
  Forall (fun ip => P ip.1 ip.2) (imap (fun i x => (i, x)) l).
Proof. apply Forall_imap_pair. Qed.

Global Instance disc_seg'_dec seg : Decision (disc_seg' seg).
Proof.
  destruct (decide (disc_seg seg)) as [Hd | Hd]; [| right; by intros [? _]].
  destruct (decide (Exists (fun cs =>
                      Exists (fun ps => disc_pt_all ps cs seg)
                        (pro_cands
                           (S (pro_idx cs
                                 ((length (ins seg) - 1) `div` length echo_line)))
                           (length seg)))
                    (bounded_lists (length line_alts)
                       (length (ins seg) `div` length echo_line)))) as [HE | HE].
  - left. apply Exists_exists in HE as (cs & Hcs & HP).
    apply Exists_exists in HP as (ps & _ & Hall).
    apply elem_of_bounded_lists in Hcs as [Hl Hf].
    by eapply disc_seg'_intro.
  - right. intros [_ (ps & cs & Hl & Hf & Hall)]. apply HE.
    apply Exists_exists. exists cs. split; [by apply elem_of_bounded_lists |].
    apply Exists_exists.
    destruct (decide (length (ins seg) = 0%nat)) as [Hz | Hz].
    { (* no input at all: the clause is vacuous and any candidate serves *)
      destruct (pro_cands_nonempty
                  (S (pro_idx cs
                        ((length (ins seg) - 1) `div` length echo_line)))
                  (length seg)) as [g Hg].
      exists g. split; [exact Hg |]. rewrite /disc_pt_all.
      apply (Forall_imap_pair_intro
               (fun i p => pro_ok g cs (i `div` length echo_line)
                           /\ disc_pt g cs i p)).
      intros i p Hi. exfalso. apply lookup_lt_Some in Hi.
      rewrite in_pres_length in Hi. lia. }
    (* the LAST input bounds every round the transcript enters *)
    destruct (lookup_lt_is_Some_2 (in_pres seg) (length (ins seg) - 1)%nat
                ltac:(rewrite in_pres_length; lia)) as [pl Hlast].
    destruct (Hall _ _ Hlast) as [[HFps Hltl] Hptl].
    destruct (pro_canon
                (S (pro_idx cs ((length (ins seg) - 1) `div` length echo_line)))
                (length seg) ps HFps) as (ps0 & Hin0 & Hrd0 & Hag0).
    { intros r Hr. split; [lia |].
      etrans; [apply (sess_n_pro_len ps cs (length (ins seg) - 1)%nat r); lia |].
      etrans; [apply prefix_length, Hptl |].
      etrans; [apply obs_wire_length |].
      apply prefix_length, (in_pres_prefix seg _ _ Hlast). }
    exists ps0. split; [exact Hin0 |]. rewrite /disc_pt_all.
    apply (Forall_imap_pair_intro
             (fun i p => pro_ok ps0 cs (i `div` length echo_line)
                         /\ disc_pt ps0 cs i p)).
    intros i p Hi.
    destruct (Hall i p Hi) as [[_ Hlti] Hpti].
    assert (Hile : (i `div` length echo_line
                    <= (length (ins seg) - 1) `div` length echo_line)%nat).
    { apply Nat.Div0.div_le_mono.
      apply lookup_lt_Some in Hi. rewrite in_pres_length in Hi. lia. }
    assert (Hidxle : (pro_idx cs (i `div` length echo_line)
                      <= pro_idx cs
                           ((length (ins seg) - 1) `div` length echo_line))%nat)
      by (by apply pro_idx_mono).
    assert (Hsame : sess_n ps0 cs i = sess_n ps cs i).
    { apply sess_n_ps_ext. intros r Hr. apply Hag0. lia. }
    split.
    + rewrite /pro_ok. split; [by eapply pro_cands_Forall |]. lia.
    + rewrite /disc_pt Hsame. exact Hpti.
Defined.

Lemma disc_seg'_nil : disc_seg' [].
Proof.
  split; [exact disc_seg_nil|]. exists [], []. split; [done|].
  split; [constructor|]. intros i p Hi.
  apply lookup_lt_Some in Hi. cbn in Hi. lia.
Qed.

(* THE PROJECTION.  Everything the tree already proves against the landed
   discipline reads off the new one in one step. *)
Lemma disc_seg'_proj seg : disc_seg' seg -> disc_seg seg.
Proof. by intros [? _]. Qed.

(* ANTI-VACUITY AT A LITERAL.  [disc_seg'] is not merely decidable and
   prefix-closed: it is SATISFIED, by the schedule the design names --
   init's banner and sh's prompt on the wire, then the first byte of
   "echo hello world\n".  Everything in it is closed, so [vm_compute]
   answers it, and it is the check that says D1/D2 did not make the
   discipline unsatisfiable. *)
Definition demo_seg : list mobs :=
  ((fun b => ObsUartOut Uart0 b) <$> u_prologue) ++ [ObsUartIn Uart0 (Z_to_bv 8 101%Z)].

Lemma demo_disc_seg' : disc_seg' demo_seg.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 0%nat] []);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* ...AND AT THE FOUR OTHER OPENINGS.  These are the literals that say the
   owner's rulings of 2026-09-16 and 2026-09-14 did not make the discipline
   vacuous: the shell that had to be started twice, the fork that failed,
   the shell that died on its own fork panic after a completed line, and
   the shell whose init printed no banner at all. *)
Definition demo_seg_exec : list mobs :=
  ((fun b => ObsUartOut Uart0 b) <$> pro_of [3%nat; 1%nat; 3%nat; 0%nat])
  ++ [ObsUartIn Uart0 (Z_to_bv 8 101%Z)].

Lemma demo_disc_seg'_exec : disc_seg' demo_seg_exec.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 1%nat; 3%nat; 0%nat] []);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

Definition demo_seg_fork : list mobs :=
  ((fun b => ObsUartOut Uart0 b) <$> pro_of [3%nat; 2%nat])
  ++ [ObsUartIn Uart0 (Z_to_bv 8 101%Z)].

Lemma demo_disc_seg'_fork : disc_seg' demo_seg_fork.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 2%nat] []);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* one whole line typed and echoed, the shell's fork1 panic, and init's
   restart -- the block whose alternative is 3 re-enters the prologue *)
Definition demo_seg_panic : list mobs :=
  ((fun b => ObsUartOut Uart0 b) <$> pro_of [3%nat; 0%nat])
  ++ mjoin ((fun b => [ObsUartIn Uart0 b; ObsUartOut Uart0 b]) <$> echo_line)
  ++ ((fun b => ObsUartOut Uart0 b) <$> (line_alts !!! 3%nat
        ++ pro_of (pro_from 1%nat [3%nat; 0%nat; 3%nat; 0%nat]))).

Lemma demo_disc_seg'_panic : disc_seg' demo_seg_panic.
Proof.
  eapply (disc_seg'_intro _ [3%nat; 0%nat; 3%nat; 0%nat] [3%nat]);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* THE BANNER-LESS OPENING (the ruling of 2026-09-14): init's console open
   failed, it printed nothing, and the shell's "$ " is the round's first
   byte *)
Definition demo_seg_noban : list mobs :=
  ((fun b => ObsUartOut Uart0 b) <$> u_prompt) ++ [ObsUartIn Uart0 (Z_to_bv 8 101%Z)].

Lemma demo_disc_seg'_noban : disc_seg' demo_seg_noban.
Proof.
  eapply (disc_seg'_intro _ [0%nat] []);
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* THE DISCIPLINE, over the WHOLE history (uart-trace.md ruling 1): every
   cycle's input keeps the rate discipline.  [cycles_of h] lists every
   cycle, the open one LAST while the power is on, so the open cycle is
   covered. *)
Definition disc (h : list mobs) : Prop := Forall disc_seg' (cycles_of h).

Global Instance disc_dec h : Decision (disc h).
Proof. rewrite /disc. apply _. Qed.

Lemma disc_nil : disc [].
Proof. constructor. Qed.

Lemma disc_proj h : disc h -> disc_old h.
Proof.
  rewrite /disc /disc_old. intros H. apply Forall_lookup. intros i seg Hi.
  apply disc_seg'_proj. by eapply Forall_lookup_1.
Qed.

(* ---- the three closure laws, at the SAME statements they had ---- *)

Lemma disc_seg'_other (seg : list mobs) (e : mobs) :
  not_cons_in e -> disc_seg' (seg ++ [e]) <-> disc_seg' seg.
Proof.
  intro He.
  assert (Hi : in_pres (seg ++ [e]) = in_pres seg)
    by (by apply in_pres_snoc_other).
  assert (Hn : ins (seg ++ [e]) = ins seg)
    by (rewrite ins_app (ins_snoc_other e He) app_nil_r; reflexivity).
  rewrite /disc_seg' /disc_seg Hi Hn. done.
Qed.

(* ...hence the closure law, at every I/O event the discipline cannot see:
   an output on either port, and an INPUT ON THE OTHER PORT.  The second is
   what a two-UART machine forces -- the environment may type on the
   kernel's port at any moment and the echo claim has to survive it. *)
Lemma disc_other (h : list mobs) (e : mobs) :
  is_io e = true -> not_cons_in e ->
  trace_shape h true ->
  disc (h ++ [e]) <-> disc h.
Proof.
  intros Hio He Hsh.
  destruct (cycles_of_io h [e] Hsh) as (cs & Hc & Hc');
    [by constructor|].
  rewrite /disc Hc Hc' !Forall_app !Forall_singleton
          (disc_seg'_other _ _ He). done.
Qed.

Lemma disc_seg'_out (seg : list mobs) (i : uart_id) (b : bv 8) :
  disc_seg' (seg ++ [ObsUartOut i b]) <-> disc_seg' seg.
Proof. apply disc_seg'_other. by destruct i. Qed.

Lemma disc_out (h : list mobs) (i : uart_id) (b : bv 8) :
  trace_shape h true ->
  disc (h ++ [ObsUartOut i b]) <-> disc h.
Proof. intro Hsh. apply disc_other; [by destruct i|by destruct i|exact Hsh]. Qed.

Lemma disc_power (h : list mobs) (on : bool) :
  disc (h ++ [if on then ObsPowerOff else ObsPowerOn]) <-> disc h.
Proof.
  rewrite /disc. destruct on.
  - by rewrite cycles_of_off.
  - rewrite cycles_of_on Forall_app Forall_singleton.
    split; [by intros [? _] | intros ?; split; [done | exact disc_seg'_nil]].
Qed.

(* an input byte can only have BROKEN the discipline: the witness for the
   shorter history is the longer one's choice list, cut to the lines the
   shorter input completed. *)

Lemma sess_n_take ps cs n q :
  (n `div` length echo_line <= q)%nat -> sess_n ps (take q cs) n = sess_n ps cs n.
Proof.
  intros Hq. rewrite /sess_n. do 2 f_equal.
  apply alt_seq_ext. intros j Hj.
  rewrite list_lookup_total_alt lookup_take; [|lia].
  by rewrite -list_lookup_total_alt.
Qed.

Lemma disc_seg'_in (seg : list mobs) (b : bv 8) :
  disc_seg' (seg ++ [ObsUartIn Uart0 b]) -> disc_seg' seg.
Proof.
  intros [Hd (ps & cs & Hl & Hf & Hall)].
  rewrite /disc_seg ins_app ins_in in Hd.
  rewrite ins_app ins_in length_app /= in Hl.
  split; [exact (star_prefix_snoc _ _ _ echo_line_pos Hd)|].
  exists ps, (take (length (ins seg) `div` length echo_line) cs).
  split.
  { assert (H1 : (length (ins seg) `div` length echo_line
                 <= (length (ins seg) + 1) `div` length echo_line)%nat)
      by (apply Nat.Div0.div_le_mono; lia).
    rewrite length_take Hl Nat.min_l; [done|exact H1]. }
  split; [by apply Forall_take|].
  intros i p Hi.
  assert (Hlt : (i < length (ins seg))%nat).
  { apply lookup_lt_Some in Hi. by rewrite in_pres_length in Hi. }
  assert (Hi' : in_pres (seg ++ [ObsUartIn Uart0 b]) !! i = Some p).
  { rewrite in_pres_in lookup_app_l; [exact Hi|].
    rewrite in_pres_length. lia. }
  destruct (Hall i p Hi') as [Hok Hpt].
  assert (Hqi : (i `div` length echo_line
                 <= length (ins seg) `div` length echo_line)%nat)
    by (apply Nat.Div0.div_le_mono; lia).
  split.
  - rewrite /pro_ok. destruct Hok as [HF Hlt2]. split; [exact HF|].
    by rewrite (pro_idx_take cs _ (i `div` length echo_line) Hqi).
  - rewrite /disc_pt in Hpt |- *. by rewrite sess_n_take.
Qed.

Lemma disc_in (h : list mobs) (b : bv 8) :
  trace_shape h true ->
  disc (h ++ [ObsUartIn Uart0 b]) -> disc h.
Proof.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartIn Uart0 b] Hsh) as (cs & Hc & Hc');
    [by constructor|].
  rewrite /disc Hc Hc' !Forall_app !Forall_singleton.
  intros [Hall Hseg]. split; [exact Hall|]. exact (disc_seg'_in _ _ Hseg).
Qed.

(* THE DISCIPLINE IS PREFIX-CLOSED, at ONE fact and with no [trace_shape]
   premise: [cyc_step] extends the most recent cycle (or starts one) and
   never touches an older one, so dropping the last event either drops a
   whole cycle or shortens the open one -- and [disc_seg'] is closed under
   both.  Every consumer that has to say "the history this log entry was
   taken at is disciplined too" spends this and nothing else. *)
Lemma Forall_rev_iff {A} (P : A -> Prop) (l : list A) :
  Forall P (rev l) <-> Forall P l.
Proof.
  induction l as [|a l IH]; [done|]. cbn.
  rewrite Forall_app Forall_singleton Forall_cons IH. tauto.
Qed.

Lemma disc_snoc (h : list mobs) (e : mobs) : disc (h ++ [e]) -> disc h.
Proof.
  rewrite /disc /cycles_of !Forall_rev_iff cycles_rev_app /=.
  destruct e as [i b|i b| |]; cbn.
  - destruct (cycles_rev h) as [|c cs]; [by intros _|].
    rewrite !Forall_cons. intros [Hseg Hall]. split; [|exact Hall].
    destruct i.
    + exact (disc_seg'_in c b Hseg).
    + apply (disc_seg'_other c (ObsUartIn Uart1 b) I). exact Hseg.
  - destruct (cycles_rev h) as [|c cs]; [by intros _|].
    rewrite !Forall_cons. intros [Hseg Hall]. split; [|exact Hall].
    apply (disc_seg'_out c i b). exact Hseg.
  - rewrite Forall_cons. by intros [_ ?].
  - done.
Qed.

Lemma disc_prefix (h' h : list mobs) : h' `prefix_of` h -> disc h -> disc h'.
Proof.
  intros [k ->]. induction k as [|e k IH] using rev_ind; intros Hd.
  - by rewrite app_nil_r in Hd.
  - apply IH. rewrite app_assoc in Hd. exact (disc_snoc _ _ Hd).
Qed.

(* ====================================================================== *)
(*  5.  THE CLAIM (R5)                                                    *)
(* ====================================================================== *)

(* THE OUTPUT CLAIM for one power cycle: everything that reached the
   console wire is a PREFIX of the transcript this cycle's input calls
   for, under some resolution of the per-line alternatives.  Nothing else
   is on this wire -- the kernel's own messages go to the other port -- so
   there is no interleaving to name and no witness to exhibit: the claim
   is a prefix test on the raw wire. *)
Definition good_out (seg : list mobs) : Prop :=
  expected_rel (ins seg) (obs_wire Uart0 seg).

Lemma good_out_nil : good_out [].
Proof.
  exists [0%nat], []. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* ...and it is not vacuous either: the five schedules the section above
   exhibits -- the good run, one exec failure, the fork failure, the shell
   that died on its own fork panic and was restarted, and the banner-less
   opening -- satisfy it. *)
Lemma demo_good_out : good_out demo_seg.
Proof.
  exists [3%nat; 0%nat], []. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_exec : good_out demo_seg_exec.
Proof.
  exists [3%nat; 1%nat; 3%nat; 0%nat], [].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_fork : good_out demo_seg_fork.
Proof.
  exists [3%nat; 2%nat], []. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_panic : good_out demo_seg_panic.
Proof.
  exists [3%nat; 0%nat; 3%nat; 0%nat], [3%nat].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

Lemma demo_good_out_noban : good_out demo_seg_noban.
Proof.
  exists [0%nat], []. apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* AT AN INPUT POINT THE TWO BOUNDS MEET.  The discipline says the expected
   transcript for the bytes typed so far is a prefix of the wire; the claim
   says the wire is a prefix of the transcript for the same bytes.  So at
   the moment a disciplined byte is typed the wire IS the transcript --
   which is the simulation invariant E5's proof of [Hphi] carries: sh has
   consumed every previous line, the ring holds at most the line in
   progress, and [consoleintr] drops nothing. *)
Lemma disc_pt_good_out_pin (ps cs : list nat) (i : nat) (p : list mobs) :
  length (ins p) = i ->
  disc_pt ps cs i p -> obs_wire Uart0 p `prefix_of` sess ps cs (ins p) ->
  obs_wire Uart0 p = sess_n ps cs i.
Proof.
  intros Hlen Hd Hg. rewrite /disc_pt in Hd. rewrite /sess Hlen in Hg.
  by apply (anti_symm prefix).
Qed.
