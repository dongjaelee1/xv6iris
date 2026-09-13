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

(* the console line the discipline admits: "echo hello world\n" -- the
   bytes the user types, and ALSO their echoes, because [consoleintr]
   echoes a stored byte unchanged and rewrites only '\r' (to '\n').  This
   line ends in '\n' (byte 10), not '\r', so echo is the IDENTITY on it. *)
Definition echo_line : list (bv 8) :=
  Z_to_bv 8 <$> [101; 99; 104; 111; 32; 104; 101; 108; 108; 111; 32;
                 119; 111; 114; 108; 100; 10]%Z.

Lemma echo_line_length : length echo_line = 17.
Proof. reflexivity. Qed.
Lemma echo_line_pos : 0 < length echo_line.
Proof. rewrite echo_line_length. lia. Qed.

(* the same line, read off the string it is: a transcription check *)
Lemma echo_line_string : echo_line = sb "echo hello world"%string ++ nlb.
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

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

(* THE LANDED WHOLE-HISTORY PREDICATE, kept under its own name: everything
   already proved against it still means what it meant, and section 5's
   [disc_proj] is the one step from the new discipline to it. *)
Definition disc_old (h : list mobs) : Prop := Forall disc_seg (cycles_of h).

Global Instance disc_old_dec h : Decision (disc_old h).
Proof. rewrite /disc_old. apply _. Qed.

(* ====================================================================== *)
(*  2.  THE EXPECTED SESSION (R3, with O5's alternatives)                  *)
(* ====================================================================== *)

(* user/init.c:26 and user/sh.c:137 -- init's banner, then sh's prompt.
   Both are console writes ([write(1, ...)] and [write(2, "$ ", 2)] on
   descriptors init opened on "console"), so both reach THIS wire. *)
Definition u_prologue : list (bv 8) :=
  sb "init: starting sh"%string ++ nlb ++ sb "$ "%string.

(* O5, RULED BY THE OWNER (2026-09-12): allocation failure PRINTS, and what
   it prints is valid output.  After a complete line's '\n' echo the
   continuation is ONE OF
     0  "hello world\n$ "                 the good one: echo ran
     1  "exec echo failed\n$ "            sh's child could not exec
                                          (user/sh.c:80); it exits 0
     2  "$ "                              the child died before printing
     3  "fork\ninit: starting sh\n$ "     sh's fork1 panicked
                                          (user/sh.c:194; panic prints
                                          "%s\n" to fd 2 and exits 1), so
                                          init reaps and restarts sh
   Every alternative ENDS in "$ ", so D1's "a prompt has appeared" is
   well-defined after any of them; and their FIRST bytes are 'h', 'e', '$',
   'f' -- pairwise distinct, which is what makes the choice readable off
   the wire.  A later ruling changes this ONE list. *)
Definition line_alts : list (list (bv 8)) :=
  [ sb "hello world"%string ++ nlb ++ sb "$ "%string;
    sb "exec echo failed"%string ++ nlb ++ sb "$ "%string;
    sb "$ "%string;
    sb "fork"%string ++ nlb ++ sb "init: starting sh"%string ++ nlb
      ++ sb "$ "%string ].

Lemma line_alts_length : length line_alts = 4.
Proof. reflexivity. Qed.

(* ONE COMPLETED LINE'S OUTPUT: the echo of its seventeen bytes, then the
   continuation this run took.  [cs] records the continuation per line; out
   of range it reads as alternative 0, which keeps [alt_seq] total and its
   step law unconditional -- the choice is pinned by the wire wherever the
   discipline actually looks at it. *)
Definition alt_blk (cs : list nat) (i : nat) : list (bv 8) :=
  echo_line ++ line_alts !!! (cs !!! i).

Definition alt_seq (cs : list nat) (q : nat) : list (bv 8) :=
  concat (alt_blk cs <$> List.seq 0 q).

Lemma alt_seq_0 cs : alt_seq cs 0 = [].
Proof. reflexivity. Qed.

Lemma alt_seq_S cs q : alt_seq cs (S q) = alt_seq cs q ++ alt_blk cs q.
Proof.
  rewrite /alt_seq List.seq_S fmap_app concat_app Nat.add_0_l /=.
  by rewrite app_nil_r.
Qed.

(* THE EXPECTED SESSION TRANSCRIPT for [n] input bytes: init's banner and
   the first prompt, then one block per COMPLETED line, then the echo of
   the bytes of the line in progress.  It depends on the input only through
   its LENGTH -- which is what D3 buys: under [disc_seg] the input IS
   determined by its length. *)
Definition sess_n (cs : list nat) (n : nat) : list (bv 8) :=
  u_prologue ++ alt_seq cs (n `div` length echo_line)
             ++ take (n `mod` length echo_line) echo_line.

Definition sess (cs : list nat) (l : list (bv 8)) : list (bv 8) :=
  sess_n cs (length l).

Lemma sess_n_0 cs : sess_n cs 0 = u_prologue.
Proof.
  by rewrite /sess_n Nat.Div0.div_0_l Nat.Div0.mod_0_l alt_seq_0 take_0
             app_nil_r.
Qed.

(* R3's relation: [out] is what the session may have emitted for input [l],
   under SOME resolution of the per-line alternatives. *)
Definition expected_rel (l out : list (bv 8)) : Prop :=
  exists cs : list nat,
    Forall (fun c => c < length line_alts) cs /\ out `prefix_of` sess cs l.

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

Lemma sess_n_step cs n : sess_n cs n `prefix_of` sess_n cs (S n).
Proof.
  rewrite /sess_n.
  destruct (div_mod_succ n (length echo_line) echo_line_pos)
    as [(Hm & Hd & Hr)|(Hm & Hd)]; rewrite Hm Hd.
  - rewrite alt_seq_S take_0 app_nil_r.
    apply prefix_app, prefix_app.
    rewrite /alt_blk. apply prefix_app_r, prefix_take.
  - apply prefix_app, prefix_app, prefix_take_le. lia.
Qed.

Lemma sess_n_mono cs n m : n <= m -> sess_n cs n `prefix_of` sess_n cs m.
Proof.
  intros Hnm. replace m with (n + (m - n)) by lia.
  generalize (m - n) as d. intros d. clear Hnm m.
  induction d as [|d IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. etrans; [exact IH | apply sess_n_step].
Qed.

(* R3's monotonicity, both ways round *)
Lemma expected_rel_out_mono l out out' :
  out' `prefix_of` out -> expected_rel l out -> expected_rel l out'.
Proof.
  intros Hp (cs & Hcs & Hout). exists cs. split; [exact Hcs|]. by etrans.
Qed.

Lemma expected_rel_ins_mono l l' out :
  length l <= length l' -> expected_rel l out -> expected_rel l' out.
Proof.
  intros Hlen (cs & Hcs & Hout). exists cs. split; [exact Hcs|].
  etrans; [exact Hout|]. rewrite /sess. by apply sess_n_mono.
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
  pose proof echo_line_length as HL.
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
Definition disc_pt (cs : list nat) (i : nat) (p : list mobs) : Prop :=
  sess_n cs i `prefix_of` obs_wire Uart0 p.

Global Instance disc_pt_dec cs i p : Decision (disc_pt cs i p).
Proof. rewrite /disc_pt. apply _. Defined.

(* THE PER-CYCLE DISCIPLINE: D3, and at every input byte D1/D2 under ONE
   resolution of the per-line alternatives. *)
Definition disc_seg' (seg : list mobs) : Prop :=
  disc_seg seg
  /\ exists cs : list nat,
       length cs = length (ins seg) `div` length echo_line
       /\ Forall (fun c => c < length line_alts) cs
       /\ forall (i : nat) (p : list mobs),
            in_pres seg !! i = Some p -> disc_pt cs i p.

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

Global Instance disc_seg'_dec seg : Decision (disc_seg' seg).
Proof.
  rewrite /disc_seg'.
  destruct (decide (disc_seg seg)) as [Hd|Hd]; [|right; by intros [? _]].
  destruct (decide (Exists (fun cs => Forall (fun ip => disc_pt cs ip.1 ip.2)
                                        (imap (fun i x => (i, x)) (in_pres seg)))
             (bounded_lists (length line_alts)
                (length (ins seg) `div` length echo_line)))) as [HE|HE].
  - left. split; [exact Hd|].
    apply Exists_exists in HE as (cs & Hcs & HF).
    apply elem_of_bounded_lists in Hcs as [Hl Hf].
    exists cs. split; [exact Hl|]. split; [exact Hf|].
    by apply Forall_imap_pair.
  - right. intros [_ (cs & Hl & Hf & Hall)]. apply HE.
    apply Exists_exists. exists cs. split.
    + apply elem_of_bounded_lists. by split.
    + by apply Forall_imap_pair.
Defined.

Lemma disc_seg'_nil : disc_seg' [].
Proof.
  split; [exact disc_seg_nil|]. exists []. split; [done|].
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
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

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
Lemma alt_seq_ext cs1 cs2 q :
  (forall j, j < q -> cs1 !!! j = cs2 !!! j) -> alt_seq cs1 q = alt_seq cs2 q.
Proof.
  induction q as [|q IH]; intros Hj; [done|].
  rewrite !alt_seq_S IH; [|intros j Hjq; apply Hj; lia].
  rewrite /alt_blk (Hj q ltac:(lia)) //.
Qed.

Lemma sess_n_take cs n q :
  n `div` length echo_line <= q -> sess_n (take q cs) n = sess_n cs n.
Proof.
  intros Hq. rewrite /sess_n. do 2 f_equal.
  apply alt_seq_ext. intros j Hj.
  rewrite list_lookup_total_alt lookup_take; [|lia].
  by rewrite -list_lookup_total_alt.
Qed.

Lemma disc_seg'_in (seg : list mobs) (b : bv 8) :
  disc_seg' (seg ++ [ObsUartIn Uart0 b]) -> disc_seg' seg.
Proof.
  intros [Hd (cs & Hl & Hf & Hall)].
  rewrite /disc_seg ins_app ins_in in Hd.
  rewrite ins_app ins_in length_app /= in Hl.
  split; [exact (star_prefix_snoc _ _ _ echo_line_pos Hd)|].
  exists (take (length (ins seg) `div` length echo_line) cs).
  split.
  { assert (H1 : length (ins seg) `div` length echo_line
                 <= (length (ins seg) + 1) `div` length echo_line)
      by (apply Nat.Div0.div_le_mono; lia).
    rewrite length_take Hl Nat.min_l; [done|exact H1]. }
  split; [by apply Forall_take|].
  intros i p Hi.
  assert (Hlt : i < length (ins seg)).
  { apply lookup_lt_Some in Hi. by rewrite in_pres_length in Hi. }
  assert (Hi' : in_pres (seg ++ [ObsUartIn Uart0 b]) !! i = Some p).
  { rewrite in_pres_in lookup_app_l; [exact Hi|].
    rewrite in_pres_length. lia. }
  specialize (Hall i p Hi'). rewrite /disc_pt in Hall |- *.
  rewrite sess_n_take; [exact Hall|].
  apply Nat.Div0.div_le_mono. lia.
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
Proof. exists []. split; [constructor|]. apply prefix_nil. Qed.

(* ...and it is not vacuous either: the same schedule [demo_disc_seg']
   admits satisfies it. *)
Lemma demo_good_out : good_out demo_seg.
Proof.
  exists []. split; [constructor|].
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(* AT AN INPUT POINT THE TWO BOUNDS MEET.  The discipline says the expected
   transcript for the bytes typed so far is a prefix of the wire; the claim
   says the wire is a prefix of the transcript for the same bytes.  So at
   the moment a disciplined byte is typed the wire IS the transcript --
   which is the simulation invariant E5's proof of [Hphi] carries: sh has
   consumed every previous line, the ring holds at most the line in
   progress, and [consoleintr] drops nothing. *)
Lemma disc_pt_good_out_pin (cs : list nat) (i : nat) (p : list mobs) :
  length (ins p) = i ->
  disc_pt cs i p -> obs_wire Uart0 p `prefix_of` sess cs (ins p) ->
  obs_wire Uart0 p = sess_n cs i.
Proof.
  intros Hlen Hd Hg. rewrite /disc_pt in Hd. rewrite /sess Hlen in Hg.
  by apply (anti_symm prefix).
Qed.
