(* EchoOutPure.v -- THE PURE HALF OF E5's APPLICATION CLAIM.

   Design of record: claude-notes/projects/app-echo.md, "E5 -- THE CONSOLE
   I/O CLAIM: DESIGN OF RECORD" (the claim's pure conjuncts and the three
   arguments (E), (R), (W)).  This file is Iris-free list algebra over
   [EchoDisc] and [ConsLog], so that the Iris lane (ECHO-OUT) only has to
   APPLY lemmas.

   THE STAGE MACHINE.  The claim's data is the list [E] of ECHOED inputs:
   [E]'s j-th entry is the pair (history, byte) of input j+1, and the
   kernel put [echo_of c] on the wire for it.  The console's accepted
   bytes are then

     acc = D cs E ++ w      with   w `prefix_of` pending cs E

   where [D cs E] is the transcript DUE after E's last echo and
   [pending cs E] is the PROCESS output owed at that stage (init's banner
   and sh's first prompt before any input; the completed line's
   continuation at a line boundary; nothing mid-line -- mid-line a process
   byte is forbidden outright, which is what makes the discipline's rate
   bound bite).  [cs] resolves the per-line alternatives, exactly as in
   [EchoDisc.sess_n].

   THE FOUR FACTS, in the order the Iris claim spends them:
     F1  the stage is below the session   ([D_pending_sess], [D_stage_prefix])
     F2  the next echo is the next input  ([D2_next_input])
     F3  the read window is a slice of E  ([read_window_prefix],
                                           [read_window_line])
     F4  PHI's pure part                  ([good_out_of_stage],
                                           [echo_phi_of_good_out]) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import EchoDisc.
Require Import ConsLog.
(* as in EchoDisc: a pure file does not inherit ssreflect's [rewrite] from
   the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  TWO BORROWED LEMMAS                                                *)
(*                                                                        *)
(*  The periodicity lemmas this file reads ([star_prefix_lookup] and its   *)
(*  two steps) are [EchoDisc]'s since lane ECHO-PURE moved them there.     *)
(*  What is still borrowed is the cycle a history's last input lives in:   *)
(*  it is an [ObsTrace]-level fact and belongs there, but the only copy    *)
(*  today is [UkSh]'s, far above this file.                               *)
(* ====================================================================== *)

(* ...and the cycle a history's last input lives in, copied from
   [UkSh.ush_cycles_snoc_in] for the same reason (that file is above this
   one; the fact is [ObsTrace]'s and belongs there). *)
Lemma epu_elem_of_rev_head {A} (x : A) (l : list A) : x ∈ rev (x :: l).
Proof. cbn. apply elem_of_app. right. by apply elem_of_list_singleton. Qed.

Lemma epu_cycles_snoc_in (h : list mobs) (b : bv 8) :
  exists s0 : list mobs,
    (s0 ++ [ObsUartIn Uart0 b])%list ∈ cycles_of (h ++ [ObsUartIn Uart0 b])%list.
Proof.
  rewrite /cycles_of cycles_rev_app.
  destruct (cycles_rev h) as [| c cs] eqn:Hc.
  - exists []. exact (epu_elem_of_rev_head ([] ++ [ObsUartIn Uart0 b])%list []).
  - exists c. exact (epu_elem_of_rev_head (c ++ [ObsUartIn Uart0 b])%list cs).
Qed.

(* ====================================================================== *)
(*  1.  THE BYTES OF THE LINE                                              *)
(* ====================================================================== *)

(* [echo_of] is the identity off '\r' *)
Lemma echo_of_other (c : bv 8) :
  c <> (mword_of_int 13 : mword 8) -> echo_of c = c.
Proof.
  intro Hne. rewrite /echo_of.
  destruct (eq_vec (c : mword 8) (mword_of_int 13 : mword 8)) eqn:He;
    [ | reflexivity ].
  exfalso. apply Hne. by apply eq_vec_true_iff in He.
Qed.

(* [echo_line] ends in '\n', not '\r', and holds neither '\r', nor any of
   the three erase bytes, nor ^D: decided at the literal, seventeen bytes.
   The third clause is what refutes the READ PATH'S SWALLOW arm (a leading
   ^D pops a byte and delivers nothing); the erase clause refutes the gap
   clause's erase disjunct. *)
Lemma echo_line_bytes_ok (c : bv 8) :
  c ∈ echo_line ->
  c <> (mword_of_int 13 : mword 8) /\ cons_erase c = false
  /\ bv_unsigned c <> 4%Z.
Proof.
  rewrite /echo_line. intros Hc.
  apply elem_of_list_fmap in Hc as (z & -> & Hz).
  repeat (apply elem_of_cons in Hz as [-> | Hz];
          [ split;
            [ intro Hq; apply (f_equal bv_unsigned) in Hq;
              vm_compute in Hq; discriminate Hq
            | split; [ vm_compute; reflexivity
                     | intro Hq; vm_compute in Hq; discriminate Hq ] ] | ]).
  by apply elem_of_nil in Hz.
Qed.

(* THE ECHO OF A LINE BYTE IS THE BYTE ITSELF -- which is why [D]'s
   [echo_of c] and [sess_n]'s [echo_line] byte are the same thing. *)
Lemma echo_of_echo_line (c : bv 8) : c ∈ echo_line -> echo_of c = c.
Proof. intro Hc. apply echo_of_other, (echo_line_bytes_ok c Hc). Qed.

Lemma cons_erase_echo_line (c : bv 8) : c ∈ echo_line -> cons_erase c = false.
Proof. intro Hc. apply (echo_line_bytes_ok c Hc). Qed.

Lemma no_ctrl_d_echo_line (c : bv 8) : c ∈ echo_line -> bv_unsigned c <> 4%Z.
Proof. intro Hc. apply (echo_line_bytes_ok c Hc). Qed.

(* THE BYTE A DISCIPLINED HISTORY ENDS IN is the line byte its POSITION
   calls for -- D3 read at one index. *)
Lemma disc_seg_last_byte (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c ->
  c = echo_line !!! ((length (ins h) - 1) `mod` length echo_line).
Proof.
  intros Hd [h0 ->].
  rewrite /disc_seg ins_app ins_in in Hd. rewrite ins_app ins_in.
  set (k := length (ins h0)).
  assert (Hlk : (ins h0 ++ [c]) !! k = Some c).
  { by rewrite lookup_app_r ?Nat.sub_diag. }
  assert (Hlt : k < length (ins h0 ++ [c]))
    by (rewrite length_app /=; lia).
  pose proof (star_prefix_lookup echo_line (ins h0 ++ [c]) k Hd
                echo_line_pos Hlt) as Hp.
  rewrite Hlk in Hp. rewrite length_app /= Nat.add_sub.
  assert (Hr : k `mod` length echo_line < length echo_line)
    by (apply Nat.mod_upper_bound; pose proof echo_line_length; lia).
  rewrite (list_lookup_total_alt echo_line) -Hp //.
Qed.

Lemma disc_seg_in_echo_line (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> c ∈ echo_line.
Proof.
  intros Hd He. rewrite (disc_seg_last_byte h c Hd He).
  apply elem_of_list_lookup_2 with ((length (ins h) - 1) `mod` length echo_line).
  rewrite -list_lookup_lookup_total_lt //.
  apply Nat.mod_upper_bound. pose proof echo_line_length. lia.
Qed.

(* the refutation the read contract's erase disjunct needs *)
Lemma disc_seg_no_erase (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> cons_erase c = false.
Proof.
  intros Hd He. apply cons_erase_echo_line, (disc_seg_in_echo_line h c Hd He).
Qed.

(* ...and the same for the read path's SWALLOW arm.  The kernel tests
   [cons_xlate b] against 0x04 and [cons_xlate] is the identity off '\r'
   ([UkSh.disc_no_ctrl_d] is that bridge); this is its pure half, which is
   all a file below ConsoleInv can say. *)
Lemma disc_seg_no_ctrl_d (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> bv_unsigned c <> 4%Z.
Proof.
  intros Hd He. apply no_ctrl_d_echo_line, (disc_seg_in_echo_line h c Hd He).
Qed.

Lemma disc_no_erase (h : list mobs) (c : bv 8) :
  disc h -> obs_ends_in Uart0 h c -> cons_erase c = false.
Proof.
  intros Hdisc [h0 ->].
  destruct (epu_cycles_snoc_in h0 c) as (s0 & Hin).
  apply elem_of_list_lookup in Hin as [i Hi].
  pose proof (disc_seg'_proj _ (Forall_lookup_1 _ _ _ _ Hdisc Hi)) as Hseg.
  eapply disc_seg_no_erase; [exact Hseg | apply obs_ends_in_snoc].
Qed.

(* THE OPEN CYCLE OF A DISCIPLINED HISTORY KEEPS D3 -- the one step from
   the whole-history discipline to the segment the claim is stated over. *)
Lemma disc_seg_open_seg (h : list mobs) :
  trace_shape h true -> disc h -> disc_seg (open_seg h).
Proof.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply elem_of_list_lookup in Hin as [i Hi].
  exact (disc_seg'_proj _ (Forall_lookup_1 _ _ _ _ Hd Hi)).
Qed.

(* ...AND THE BYTE COMES WITH IT.  Lane ECHO-OUT stores E's histories as
   CYCLE SEGMENTS (the discipline, [good_out] and [acc] are all per power
   cycle, so [E_index]'s [ins] must count the cycle's inputs and not the
   run's), and this is what turns the shift's [obs_ends_in] at the whole
   history into the one at the segment. *)
Lemma open_seg_ends_in (h : list mobs) (c : bv 8) :
  obs_ends_in Uart0 h c -> obs_ends_in Uart0 (open_seg h) c.
Proof.
  intros [h0 ->].
  rewrite (open_seg_io h0 [ObsUartIn Uart0 c]); [| by repeat constructor].
  apply obs_ends_in_snoc.
Qed.

(* ====================================================================== *)
(*  2.  THE STAGE MACHINE: [pending] AND [D]                               *)
(* ====================================================================== *)

(* THE PROCESS OUTPUT OWED AFTER [n] ECHOED INPUTS.  Before any input it is
   init's banner and sh's first prompt ([u_prologue]); after the '\n' echo
   that completes line [q] it is that line's continuation, indexed exactly
   as [EchoDisc.alt_blk] indexes it ([line_alts !!! (cs !!! (q-1))], with
   [q = n / 17]); mid-line it is nothing.  It reads only [n], because
   [sess_n] does. *)
Definition pending_n (cs : list nat) (n : nat) : list (bv 8) :=
  if decide (n = 0) then u_prologue
  else if decide (n `mod` length echo_line = 0)
       then line_alts !!! (cs !!! (n `div` length echo_line - 1))
       else [].

Definition pending (cs : list nat) (E : list (list mobs * bv 8)) : list (bv 8) :=
  pending_n cs (length E).

(* THE TRANSCRIPT DUE AFTER E's LAST ECHO.  The note's law is a RIGHT
   append ([D cs (E ++ [(h,c)]) = D cs E ++ pending cs E ++ [echo_of c]]),
   but a [Fixpoint] on the right does not reduce under [cbn] on an opaque
   tail and a [Fixpoint] on [length E] cannot see the bytes.  So the
   definition is structural on [E] FROM THE LEFT with the stage index as an
   accumulator: [cbn] reduces it on every [x :: E'], and the note's law is
   [D_app] below, one line off [D_from_app]. *)
Fixpoint D_from (cs : list nat) (k : nat) (E : list (list mobs * bv 8))
  : list (bv 8) :=
  match E with
  | [] => []
  | x :: E' => pending_n cs k ++ [echo_of x.2] ++ D_from cs (S k) E'
  end.

Definition D (cs : list nat) (E : list (list mobs * bv 8)) : list (bv 8) :=
  D_from cs 0 E.

Lemma D_nil cs : D cs [] = [].
Proof. reflexivity. Qed.

Lemma pending_nil cs : pending cs [] = u_prologue.
Proof. reflexivity. Qed.

Lemma D_from_app cs k E1 E2 :
  D_from cs k (E1 ++ E2) = D_from cs k E1 ++ D_from cs (k + length E1) E2.
Proof.
  revert k. induction E1 as [|x E1 IH]; intros k; cbn.
  - by rewrite Nat.add_0_r.
  - rewrite IH -!app_assoc.
    replace (S k + length E1) with (k + S (length E1)) by lia.
    reflexivity.
Qed.

(* THE NOTE'S LAW, verbatim *)
Lemma D_app cs E x :
  D cs (E ++ [x]) = D cs E ++ pending cs E ++ [echo_of x.2].
Proof.
  rewrite /D /pending D_from_app /=. by rewrite ?app_nil_r.
Qed.

(* ====================================================================== *)
(*  3.  WHAT THE CLAIM SAYS ABOUT [E]                                      *)
(* ====================================================================== *)

(* E's INDEX LAW, as the design states it: E's j-th entry is input j+1, and
   its byte is the one its history ends in. *)
Definition E_index (E : list (list mobs * bv 8)) : Prop :=
  forall (j : nat) (x : list mobs * bv 8),
    E !! j = Some x -> obs_ends_in Uart0 x.1 x.2 /\ length (ins x.1) = S j.

(* E's CONTENT LAW: E's j-th byte is the line byte position j calls for.
   THIS IS THE HYPOTHESIS F1 TURNS ON and the note does not list it: [D]
   records the bytes actually echoed and [sess_n] records [echo_line]'s, so
   without it [D cs E] and [sess_n cs (length E)] are unrelated.  It is not
   a new assumption -- it is D3 read at one index ([E_byte_of_disc]) -- but
   it has to be NAMED, because F1 is stated at stages where the discipline
   itself is not in scope. *)
Definition E_byte (E : list (list mobs * bv 8)) : Prop :=
  forall (j : nat) (x : list mobs * bv 8),
    E !! j = Some x -> x.2 = echo_line !!! (j `mod` length echo_line).

Lemma E_byte_of_disc (E : list (list mobs * bv 8)) :
  E_index E ->
  (forall j x, E !! j = Some x -> disc_seg x.1) ->
  E_byte E.
Proof.
  intros Hidx Hd j x Hx.
  destruct (Hidx j x Hx) as [Hends Hlen].
  rewrite (disc_seg_last_byte x.1 x.2 (Hd j x Hx) Hends) Hlen.
  by rewrite Nat.sub_succ Nat.sub_0_r.
Qed.

(* ...and the form [D] consumes *)
Lemma E_byte_echo (E : list (list mobs * bv 8)) (j : nat) (x : list mobs * bv 8) :
  E_byte E -> E !! j = Some x ->
  echo_of x.2 = echo_line !!! (j `mod` length echo_line).
Proof.
  intros HE Hx. rewrite (HE j x Hx). apply echo_of_echo_line.
  apply elem_of_list_lookup_2 with (j `mod` length echo_line).
  rewrite -list_lookup_lookup_total_lt //.
  apply Nat.mod_upper_bound. pose proof echo_line_length. lia.
Qed.

Lemma E_byte_take (E : list (list mobs * bv 8)) (n : nat) :
  E_byte E -> E_byte (take n E).
Proof.
  intros HE j x Hx. apply lookup_take_Some in Hx as [Hx _]. by apply HE.
Qed.

Lemma E_index_take (E : list (list mobs * bv 8)) (n : nat) :
  E_index E -> E_index (take n E).
Proof.
  intros HE j x Hx. apply lookup_take_Some in Hx as [Hx _]. by apply HE.
Qed.

(* ====================================================================== *)
(*  4.  F1 -- THE STAGE IS BELOW THE SESSION                               *)
(* ====================================================================== *)

(* [sess_n] grows by at least one byte per input.  This is what refutes
   "the input got ahead of the echo" in F2, and [EchoDisc.sess_n_mono] is
   only the non-strict half. *)
Lemma sess_n_length_step cs n :
  length (sess_n cs n) < length (sess_n cs (S n)).
Proof.
  rewrite /sess_n !length_app !length_take.
  pose proof echo_line_length as HL.
  destruct (div_mod_succ n (length echo_line) echo_line_pos)
    as [(Hm & Hd & Hr)|(Hm & Hd)]; rewrite Hm Hd.
  - rewrite alt_seq_S length_app /alt_blk length_app.
    pose proof (Nat.mod_upper_bound n (length echo_line) ltac:(lia)).
    lia.
  - pose proof (Nat.mod_upper_bound n (length echo_line) ltac:(lia)).
    lia.
Qed.

Lemma sess_n_length_lt cs n m :
  n < m -> length (sess_n cs n) < length (sess_n cs m).
Proof.
  intros Hnm. induction Hnm as [|m Hnm IH].
  - apply sess_n_length_step.
  - etrans; [exact IH | apply sess_n_length_step].
Qed.

(* F1, THE BOUNDARY EQUATION.  Stated at EVERY stage, not only at a line
   boundary: mid-line [pending] is empty and the equation is the statement
   that the echoes so far ARE the line's prefix.  The note asks for it at
   [length E = 17 q]; that is the instance the claim spends, but the
   induction needs the general one anyway. *)
Lemma E_byte_app_l (E : list (list mobs * bv 8)) (x : list mobs * bv 8) :
  E_byte (E ++ [x]) -> E_byte E.
Proof.
  intros HE j y Hy. apply HE. rewrite lookup_app_l; [exact Hy|].
  by eapply lookup_lt_Some.
Qed.

Lemma D_pending_sess (cs : list nat) (E : list (list mobs * bv 8)) :
  E_byte E -> D cs E ++ pending cs E = sess_n cs (length E).
Proof.
  induction E as [|x E IH] using rev_ind; intros HE.
  - by rewrite D_nil pending_nil /= sess_n_0.
  - pose proof echo_line_length as HL.
    pose proof (E_byte_echo (E ++ [x]) (length E) x HE
                  ltac:(rewrite lookup_app_r;
                        [ by rewrite Nat.sub_diag | lia ])) as Hb.
    pose proof (Nat.mod_upper_bound (length E) (length echo_line)
                  ltac:(lia)) as Hub.
    set (n := length E) in *.
    assert (Hlen : length (E ++ [x]) = S n) by (rewrite length_app /=; lia).
    (* the byte the echo adds is [echo_line]'s next *)
    assert (Htk : take (n `mod` length echo_line) echo_line
                    ++ [echo_line !!! (n `mod` length echo_line)]
                  = take (S (n `mod` length echo_line)) echo_line).
    { rewrite (take_S_r echo_line _ (echo_line !!! (n `mod` length echo_line)));
        [done|]. by rewrite -list_lookup_lookup_total_lt. }
    assert (HtkK : forall K : list (bv 8),
              take (n `mod` length echo_line) echo_line
                ++ [echo_line !!! (n `mod` length echo_line)] ++ K
              = take (S (n `mod` length echo_line)) echo_line ++ K).
    { intros K. by rewrite app_assoc Htk. }
    rewrite D_app (app_assoc (D cs E) (pending cs E) [echo_of x.2]).
    rewrite (IH (E_byte_app_l _ _ HE)) Hb /pending Hlen.
    destruct (div_mod_succ n (length echo_line) echo_line_pos)
      as [(Hm & Hd & Hr)|(Hm & Hd)].
    + (* a line just completed: the echo closes [echo_line] and the
         continuation of line [n / 17] is what is owed next *)
      assert (Hp : pending_n cs (S n)
                   = line_alts !!! (cs !!! (n `div` length echo_line))).
      { rewrite /pending_n. case_decide as H1; [exfalso; lia|].
        case_decide as H2; [|exfalso; exact (H2 Hm)].
        by rewrite Hd Nat.sub_succ Nat.sub_0_r. }
      rewrite Hp /sess_n Hm Hd alt_seq_S /alt_blk take_0 app_nil_r -!app_assoc.
      rewrite HtkK Hr.
      replace (S (length echo_line - 1)) with (length echo_line) by lia.
      by rewrite take_ge; [|lia].
    + (* mid-line: nothing is owed, and the echo extends the take *)
      assert (Hp : pending_n cs (S n) = []).
      { rewrite /pending_n. case_decide as H1; [exfalso; lia|].
        case_decide as H2; [exfalso; rewrite Hm in H2; lia|done]. }
      rewrite Hp /sess_n Hm Hd app_nil_r -!app_assoc. by rewrite Htk.
Qed.

(* F1, AS THE CLAIM USES IT *)
Lemma D_stage_prefix (cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) :
  E_byte E -> w `prefix_of` pending cs E ->
  (D cs E ++ w) `prefix_of` sess_n cs (length E).
Proof.
  intros HE Hw. rewrite -(D_pending_sess cs E HE).
  by apply prefix_app, Hw.
Qed.

(* the third side condition the note lists, [sess_n cs n ⊑ sess_n cs m] for
   [n <= m], IS [EchoDisc.sess_n_mono] and is not restated here. *)

(* ====================================================================== *)
(*  5.  F2 -- THE NEXT ECHO IS THE NEXT INPUT                              *)
(* ====================================================================== *)

(* TWO PREFIX-COMPARABLE HISTORIES THAT END IN THE SAME INPUT NUMBER ARE
   EQUAL.  The note asks for this by name; it is what turns "the byte is
   already logged" into a contradiction with the log-order fact. *)
Lemma ins_hist_agree (h1 h2 : list mobs) (c1 c2 : bv 8) :
  h1 `prefix_of` h2 ->
  obs_ends_in Uart0 h1 c1 -> obs_ends_in Uart0 h2 c2 ->
  length (ins h1) = length (ins h2) -> h1 = h2.
Proof.
  intros [k ->] He1 He2 Hlen.
  rewrite ins_app length_app in Hlen.
  assert (Hk : ins k = []) by (apply nil_length_inv; lia).
  destruct k as [|e k _] using rev_ind; [by rewrite app_nil_r|].
  exfalso. destruct He2 as [h0 Hh0].
  rewrite app_assoc in Hh0.
  apply app_inj_tail in Hh0 as [_ ->].
  rewrite ins_app ins_in in Hk. by apply app_eq_nil in Hk as [_ ?].
Qed.

(* F2.  The wire is abstract ([W]) so that the Iris lane may instantiate it
   with [obs_wire Uart0 (open_seg h)] or with [obs_wire Uart0 h]; the two
   hypotheses about it are the discipline's LOWER bound at this input
   ([EchoDisc.disc_pt cs (m-1)], D1/D2) and the claim's UPPER bound.

   HYPOTHESES THE NOTE DOES NOT LIST: [E_byte E] (F1 turns on it), and
   [Hnew] -- the new input's history strictly extends every logged one.
   [Hnew] is the kernel's own log-order fact (the design: "the kernel
   proves [h] is strictly above every history already in [pops]"), and
   without it nothing refutes [m <= length E]: an adversary log that
   records the SAME input twice satisfies every other hypothesis. *)
Lemma prefix_app_cancel {A} (k a b : list A) :
  (k ++ a) `prefix_of` (k ++ b) -> a `prefix_of` b.
Proof.
  intros [z Hz]. exists z. rewrite -app_assoc in Hz. by apply app_inv_head in Hz.
Qed.

Lemma hist_ext_irrefl (h : list mobs) : hist_ext h h -> False.
Proof. intros [_ Hl]. lia. Qed.

Lemma D2_next_input (cs : list nat) (E : list (list mobs * bv 8))
      (w W : list (bv 8)) (h : list mobs) (c : bv 8) (m : nat) :
  E_byte E -> E_index E ->
  (forall x, x ∈ E -> hist_ext x.1 h) ->
  obs_ends_in Uart0 h c ->
  length (ins h) = m ->
  w `prefix_of` pending cs E ->
  sess_n cs (m - 1) `prefix_of` W ->
  W `prefix_of` (D cs E ++ w) ->
  m = S (length E) /\ w = pending cs E.
Proof.
  intros HEb HEi Hnew Hends Hm Hw Hlow Hup.
  assert (Hm1 : 1 <= m).
  { destruct Hends as [h0 ->]. rewrite -Hm ins_app ins_in length_app /=. lia. }
  (* the discipline's lower bound and the claim's upper bound meet *)
  assert (Hboth : sess_n cs (m - 1) `prefix_of` sess_n cs (length E)).
  { etrans; [exact Hlow|]. etrans; [exact Hup|]. by apply D_stage_prefix. }
  (* the input cannot have got AHEAD of the echo: [sess_n] grows per input *)
  assert (Hle : m - 1 <= length E).
  { destruct (decide (m - 1 <= length E)) as [?|Hgt]; [done|exfalso].
    apply prefix_length in Hboth.
    pose proof (sess_n_length_lt cs (length E) (m - 1) ltac:(lia)). lia. }
  (* ...nor can it be one the log already has: the histories would agree *)
  assert (Heq : m - 1 = length E).
  { destruct (decide (m - 1 = length E)) as [?|Hne]; [done|exfalso].
    assert (Hlt : m - 1 < length E) by lia.
    destruct (lookup_lt_is_Some_2 E (m - 1) Hlt) as [x Hx].
    destruct (HEi (m - 1) x Hx) as [Hxe Hxlen].
    assert (Hxin : x ∈ E) by (by eapply elem_of_list_lookup_2).
    destruct (Hnew x Hxin) as [Hpre Hlen'].
    assert (Hsame : x.1 = h).
    { eapply ins_hist_agree; [exact Hpre|exact Hxe|exact Hends|]. lia. }
    rewrite Hsame in Hlen'. lia. }
  split; [lia|].
  apply (anti_symm prefix); [exact Hw|].
  eapply (prefix_app_cancel (D cs E)).
  rewrite (D_pending_sess cs E HEb) -Heq.
  etrans; [exact Hlow|exact Hup].
Qed.

(* ====================================================================== *)
(*  6.  F3 -- THE READ WINDOW IS A SLICE OF [E]                            *)
(* ====================================================================== *)

(* the entries a read may hand out: the ECHOED ones, in log order *)
Definition echoed (pops : list log_entry) : list (list mobs * bv 8) :=
  (fun e => (le_hist e, le_byte e)) <$> filter log_echoed pops.

Lemma echoed_lookup (pops : list log_entry) (j : nat) (x : list mobs * bv 8) :
  echoed pops !! j = Some x ->
  exists e, e ∈ pops /\ log_echoed e /\ (le_hist e, le_byte e) = x.
Proof.
  rewrite /echoed list_lookup_fmap fmap_Some.
  intros (e & He & ->). exists e. split; [|split; [|reflexivity]].
  - apply elem_of_list_lookup_2 in He. by apply elem_of_list_filter in He as [_ ?].
  - apply elem_of_list_lookup_2 in He. by apply elem_of_list_filter in He as [? _].
Qed.

Lemma echoed_elem (pops : list log_entry) (e : log_entry) :
  e ∈ pops -> log_echoed e -> (le_hist e, le_byte e) ∈ echoed pops.
Proof.
  intros Hin Hec. rewrite /echoed. apply elem_of_list_fmap.
  exists e. split; [reflexivity|]. by apply elem_of_list_filter.
Qed.

(* A FILTER KEEPS A STRICT ORDER ON THE INDICES.  The general step behind
   "[echoed pops] is history-ordered because [pops] is". *)
Lemma epu_filter_cons_T {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (a : A) (l : list A) : P a -> filter P (a :: l) = a :: filter P l.
Proof. intro Hp. rewrite filter_cons. case_decide; [done|contradiction]. Qed.

Lemma epu_filter_cons_F {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (a : A) (l : list A) : ~ P a -> filter P (a :: l) = filter P l.
Proof. intro Hp. rewrite filter_cons. case_decide; [contradiction|done]. Qed.

Lemma filter_strict_order {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (R : A -> A -> Prop) (l : list A) :
  (forall i j x y, i < j -> l !! i = Some x -> l !! j = Some y -> R x y) ->
  (forall i j x y, i < j -> filter P l !! i = Some x ->
                   filter P l !! j = Some y -> R x y).
Proof.
  induction l as [|a l IH]; intros Hl i j x y Hij Hx Hy.
  { rewrite filter_nil in Hx. by rewrite lookup_nil in Hx. }
  assert (Hl' : forall i j x y, i < j -> l !! i = Some x -> l !! j = Some y -> R x y).
  { intros i' j' x' y' Hij' Hx' Hy'. by eapply (Hl (S i') (S j')); [lia| |]. }
  destruct (decide (P a)) as [Hpa|Hpa].
  - rewrite (epu_filter_cons_T P a l Hpa) in Hx, Hy.
    destruct i as [|i].
    + cbn in Hx. simplify_eq.
      destruct j as [|j]; [lia|]. cbn in Hy.
      assert (Hin : y ∈ l).
      { apply elem_of_list_lookup_2 in Hy.
        by apply elem_of_list_filter in Hy as [_ ?]. }
      apply elem_of_list_lookup in Hin as [n Hn].
      by eapply (Hl 0%nat (S n)); [lia| |].
    + destruct j as [|j]; [lia|]. cbn in Hx, Hy.
      apply (IH Hl' i j x y); [lia|exact Hx|exact Hy].
  - rewrite (epu_filter_cons_F P a l Hpa) in Hx, Hy.
    by eapply IH; [exact Hl'|exact Hij| |].
Qed.

Lemma echoed_order (pops : list log_entry) (i j : nat)
      (x y : list mobs * bv 8) :
  log_ok pops -> i < j ->
  echoed pops !! i = Some x -> echoed pops !! j = Some y ->
  hist_ext x.1 y.1.
Proof.
  intros Hlog Hij Hx Hy.
  rewrite /echoed list_lookup_fmap fmap_Some in Hx.
  destruct Hx as (e1 & He1 & ->).
  rewrite /echoed list_lookup_fmap fmap_Some in Hy.
  destruct Hy as (e2 & He2 & ->). cbn.
  eapply (filter_strict_order log_echoed
            (fun a b => hist_ext (le_hist a) (le_hist b)) pops);
    [ |exact Hij|exact He1|exact He2].
  intros i' j' a b Hij' Ha Hb. by eapply log_ok_lt.
Qed.

(* ---- what refutes an entry in a gap ---- *)

Lemma hist_ext_nil_of_ends (h : list mobs) (c : bv 8) :
  obs_ends_in Uart0 h c -> hist_ext [] h.
Proof.
  intros [h0 ->]. split; [apply prefix_nil|]. rewrite length_app /=. lia.
Qed.

Lemma echoed_elem_inv (pops : list log_entry) (y : list mobs * bv 8) :
  y ∈ echoed pops ->
  exists e, e ∈ pops /\ log_echoed e /\ (le_hist e, le_byte e) = y.
Proof.
  rewrite /echoed. intros Hy. apply elem_of_list_fmap in Hy as (e & -> & He).
  apply elem_of_list_filter in He as [Hec Hin]. by exists e.
Qed.

(* NO LOGGED BYTE IS AN ERASE CHARACTER, under the discipline -- which
   kills the gap clause's second disjunct outright *)
Lemma pops_no_erase (pops : list log_entry) :
  log_ok pops -> (forall e, e ∈ pops -> disc_seg (le_hist e)) ->
  forall e, e ∈ pops -> cons_erase (le_byte e) = false.
Proof.
  intros [Hends _] Hdisc e He.
  eapply disc_seg_no_erase; [by apply Hdisc|by apply (proj1 (Hends e He))].
Qed.

(* ...so NO ECHOED ENTRY LIES STRICTLY INSIDE A GAP *)
(* ...SO NO ECHOED ENTRY LIES STRICTLY INSIDE A GAP.  The premise is the ONE
   consequence of the discipline this argument uses -- [pops_no_erase] is its
   producer -- and not the discipline itself: lane ECHO-OUT's claim carries
   the discipline of each entry's CYCLE SEGMENT, from which the whole
   history's [disc_seg] does not follow, while the no-erase fact does
   ([disc_seg_no_erase] at the segment). *)
Lemma no_echoed_between (pops : list log_entry) (h1 h2 : list mobs)
      (y : list mobs * bv 8) :
  log_ok pops -> (forall e, e ∈ pops -> cons_erase (le_byte e) = false) ->
  gap_ok pops h1 h2 ->
  y ∈ echoed pops -> hist_ext h1 y.1 -> hist_ext y.1 h2 -> False.
Proof.
  intros Hlog Hnoer Hgap Hy H1 H2.
  destruct (echoed_elem_inv pops y Hy) as (e & Hein & Hech & Heq).
  assert (Hh : le_hist e = y.1) by (by rewrite -Heq).
  destruct Hgap as [Hleft|(e' & He'in & _ & _ & Herase)].
  - apply (log_echoed_nonnil e Hech). apply (Hleft e Hein); by rewrite Hh.
  - rewrite (Hnoer e' He'in) in Herase. discriminate.
Qed.

(* F3(a): THE CONSUMED INPUTS ARE AN INITIAL SEGMENT OF THE ECHOED ONES.

   [ws] is the window the read path CONSUMED, not the window it delivered:
   the kernel has two exits that pop a byte and hand it to nobody (a
   leading ^D, and a copy-out fault), so the delivered bytes are a PREFIX
   of [ws] of some length [d].  F3(a) is about the consumed window, which
   is the one [read_ok] speaks of; the swallow is refuted separately (^D is
   not a byte of [echo_line]: [disc_seg_no_ctrl_d]) and enters F3(c) as the
   named hypothesis [d = length ws].

   THE LOG-TO-[E] IDENTIFICATION LIVES HERE AND ONLY HERE.  F1 and F2 are
   stated over an abstract [E] on purpose: the kernel appends the log entry
   AFTER the echo's out_links, so between the two the claim's [E] is one
   entry AHEAD of [echoed pops] and no lemma may assume they agree.

   HYPOTHESES THE NOTE DOES NOT LIST.  (1) The no-erase fact is needed for
   EVERY entry of [pops], not only for [ws]'s: the gap clause's erase
   disjunct names an arbitrary LOG entry, which need not have been consumed,
   and the only thing that refutes it is that a disciplined input byte is a
   byte of [echo_line] and no erase byte is.  It is the DISCIPLINE'S
   consequence and not the discipline ([pops_no_erase] is the producer, and
   [disc_seg_no_erase] is it at a cycle segment, which is the form lane
   ECHO-OUT's claim carries).  (2) [log_ok pops]
   is what makes [echoed pops] history-ordered, so that "no log entry
   strictly between two consecutive consumed ones" is a statement about
   INDICES.  Both hold on the Iris side -- [disc] is prefix-closed, so
   every history in the log is disciplined once the current one is -- but
   neither is in the note's list. *)
Lemma read_window_prefix (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) :
  log_ok pops ->
  read_ok pops dl ws ->
  (forall e, e ∈ pops -> cons_erase (le_byte e) = false) ->
  dl `prefix_of` echoed pops ->
  (dl ++ ws) `prefix_of` echoed pops.
Proof.
  intros Hlog (Hin & Hchain & Hgap0 & Hgap) Hnoer Hdl.
  (* the consumed list agrees with [echoed pops] index by index, by strong
     induction on the index (the bound [N] is the induction's measure) *)
  assert (Hpt : forall N k, k < N -> k < length (dl ++ ws) ->
                  echoed pops !! k = (dl ++ ws) !! k).
  { induction N as [|N IHN]; intros k HkN Hk; [lia|].
    destruct ((dl ++ ws) !! k) as [p|] eqn:Hp;
      [|exfalso; apply lookup_ge_None_1 in Hp; lia].
    destruct (decide (k < length dl)) as [Hkl|Hkl].
    { (* below [dl]: [dl] is already an initial segment *)
      destruct Hdl as [z Hz]. rewrite Hz.
      rewrite lookup_app_l; last exact Hkl.
      rewrite lookup_app_l in Hp; last exact Hkl. exact Hp. }
    (* at or above [dl]: [p] is an entry of [ws], hence an echoed entry *)
    assert (Hpin : p ∈ ws).
    { rewrite lookup_app_r in Hp; [|lia]. by eapply elem_of_list_lookup_2. }
    destruct (Hin p Hpin) as (ep & Hepin & Hepeq & Hepech).
    assert (HpE : p ∈ echoed pops).
    { rewrite -Hepeq. by apply echoed_elem. }
    apply elem_of_list_lookup in HpE as [n Hn].
    assert (Hnk : n = k).
    { destruct (decide (n < k)) as [Hlt|Hge].
      - (* the same entry twice in the consumed list: the chain forbids it *)
        exfalso. rewrite (IHN n ltac:(lia) ltac:(lia)) in Hn.
        destruct p as [hp cp].
        eapply hist_ext_irrefl, (hist_chain_lt _ n k); [exact Hchain|lia| |];
          [exact Hn|exact Hp].
      - destruct (decide (k < n)) as [Hlt|?]; [|lia]. exfalso.
        (* an echoed entry sits strictly inside the gap the read left *)
        assert (Hy : is_Some (echoed pops !! k)).
        { apply lookup_lt_is_Some. apply lookup_lt_Some in Hn. lia. }
        destruct Hy as [y Hy].
        assert (Hyp : hist_ext y.1 p.1)
          by (eapply echoed_order; [exact Hlog|exact Hlt|exact Hy|exact Hn]).
        assert (HyE : y ∈ echoed pops) by (by eapply elem_of_list_lookup_2).
        destruct k as [|k'].
        + destruct p as [hp cp].
          eapply (no_echoed_between pops [] hp y);
            [exact Hlog|exact Hnoer|by eapply Hgap0|exact HyE| |exact Hyp].
          destruct (echoed_elem_inv pops y HyE) as (ey & Heyin & _ & Heyeq).
          rewrite -Heyeq /=.
          eapply hist_ext_nil_of_ends.
          by apply (proj1 (proj1 Hlog ey Heyin)).
        + assert (Hp' : is_Some ((dl ++ ws) !! k')) by (apply lookup_lt_is_Some; lia).
          destruct Hp' as [p' Hp'].
          assert (HE' : echoed pops !! k' = Some p')
            by (rewrite (IHN k' ltac:(lia) ltac:(lia)); exact Hp').
          destruct p as [hp cp]. destruct p' as [hp' cp'].
          eapply (no_echoed_between pops hp' hp y);
            [exact Hlog|exact Hnoer|by eapply Hgap|exact HyE| |exact Hyp].
          apply (echoed_order pops k' (S k') (hp', cp') y);
            [exact Hlog|lia|exact HE'|exact Hy]. }
    by rewrite Hnk in Hn. }
  (* pointwise agreement over the whole consumed list IS the prefix *)
  assert (Hle : length (dl ++ ws) <= length (echoed pops)).
  { destruct (decide (length (dl ++ ws) = 0)) as [H0|Hne]; [lia|].
    destruct ((dl ++ ws) !! (length (dl ++ ws) - 1)) as [p|] eqn:Hp;
      [|apply lookup_ge_None_1 in Hp; lia].
    pose proof (Hpt (length (dl ++ ws)) (length (dl ++ ws) - 1)
                  ltac:(lia) ltac:(lia)) as Hq.
    rewrite Hp in Hq. apply lookup_lt_Some in Hq. lia. }
  assert (Heq : take (length (dl ++ ws)) (echoed pops) = dl ++ ws).
  { apply list_eq. intros k.
    destruct (decide (k < length (dl ++ ws))) as [Hk|Hk].
    - rewrite lookup_take; [|exact Hk]. by eapply (Hpt (S k)); [lia|].
    - rewrite lookup_take_ge; [|lia]. symmetry. apply lookup_ge_None_2. lia. }
  exists (drop (length (dl ++ ws)) (echoed pops)).
  by rewrite -{1}(take_drop (length (dl ++ ws)) (echoed pops)) Heq.
Qed.

(* F3(b): A SEVENTEEN-BYTE CONSUMED WINDOW AT A LINE BOUNDARY IS THE LINE.
   Stated over an abstract [E] so that ECHO-OUT may chain it off F3(a) with
   [E := echoed pops], or off the claim's own [E] when the two agree. *)
Lemma read_window_line (E : list (list mobs * bv 8))
      (dl ws : list (list mobs * bv 8)) (q : nat) :
  E_byte E ->
  (dl ++ ws) `prefix_of` E ->
  length dl = length echo_line * q ->
  length ws = length echo_line ->
  snd <$> ws = echo_line.
Proof.
  intros HE Hp Hdl Hws.
  pose proof echo_line_length as HL.
  apply list_eq. intros k.
  destruct (decide (k < length echo_line)) as [Hk|Hk].
  - destruct (lookup_lt_is_Some_2 ws k ltac:(lia)) as [x Hwk].
    rewrite list_lookup_fmap Hwk /=.
    assert (Hak : (dl ++ ws) !! (length dl + k) = Some x).
    { rewrite lookup_app_r; [|lia].
      by replace (length dl + k - length dl) with k by lia. }
    assert (HEk : E !! (length dl + k) = Some x).
    { destruct Hp as [z ->]. rewrite lookup_app_l; [exact Hak|].
      by eapply lookup_lt_Some. }
    assert (Hmod : (length dl + k) `mod` length echo_line = k).
    { rewrite Hdl.
      replace (length echo_line * q + k) with (k + q * length echo_line) by lia.
      rewrite Nat.Div0.mod_add. by apply Nat.mod_small. }
    rewrite (HE _ _ HEk) Hmod.
    by rewrite (list_lookup_lookup_total_lt echo_line k Hk).
  - rewrite list_lookup_fmap (lookup_ge_None_2 ws k ltac:(lia)) /=.
    symmetry. apply lookup_ge_None_2. lia.
Qed.

(* F3(c): ...AND THAT IS WHAT THE PROCESS GOT, once no byte was swallowed.
   [d] is the number of bytes the read actually delivered; [Hd] is the "no
   swallow" fact, which the application pays with [disc_seg_no_ctrl_d] (the
   ^D exit) and with the copy-out fault's own refutation. *)
Lemma read_delivered_line (E : list (list mobs * bv 8))
      (dl ws : list (list mobs * bv 8)) (q d : nat) :
  E_byte E ->
  (dl ++ ws) `prefix_of` E ->
  length dl = length echo_line * q ->
  length ws = length echo_line ->
  d = length ws ->
  snd <$> take d ws = echo_line.
Proof.
  intros HE Hp Hdl Hws Hd.
  rewrite Hd take_ge; [|lia].
  by eapply read_window_line.
Qed.

(* ====================================================================== *)
(*  7.  F4 -- PHI's PURE PART                                              *)
(* ====================================================================== *)

(* THE CLAIM GIVES [good_out] AT THE SEGMENT.  [Forall (< length line_alts)
   cs] is needed HERE and not in F1 -- [expected_rel] quantifies over a
   BOUNDED choice list, while [D] and [sess_n] index [cs] with the same
   total [!!!] and agree out of range.  [length cs = length E / 17] is not
   needed at all, for the same reason. *)
Lemma good_out_of_stage (cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) (seg : list mobs) :
  Forall (fun i => i < length line_alts) cs ->
  E_byte E ->
  w `prefix_of` pending cs E ->
  obs_wire Uart0 seg `prefix_of` (D cs E ++ w) ->
  length E <= length (ins seg) ->
  good_out seg.
Proof.
  intros Hcs HE Hw Hwire Hlen.
  exists cs. split; [exact Hcs|].
  rewrite /sess. etrans; [exact Hwire|].
  etrans; [exact (D_stage_prefix cs E w HE Hw)|].
  by apply sess_n_mono.
Qed.

(* [AppEcho.echo_phi g h] is [Forall (fun seg => disc_seg' seg -> good_out
   seg) (cycles_of h)] -- the GUARDED form, not [Forall good_out ...] -- so
   PHI's pure part is a weakening and nothing more.  (Stated here rather
   than cited, because [AppEcho] is above this file and this lane may not
   import it; the body is copied, not the name.) *)
Lemma echo_phi_of_good_out (h : list mobs) :
  Forall good_out (cycles_of h) ->
  Forall (fun seg => disc_seg' seg -> good_out seg) (cycles_of h).
Proof. rewrite !Forall_forall. intros H seg Hin _. by apply H. Qed.

(* ====================================================================== *)
(*  8.  THE CHOICES ARE READABLE OFF THE WIRE                              *)
(*                                                                        *)
(*  Lane ECHO-OUT needs D2's LOWER bound at the CLAIM's choice list, and   *)
(*  the discipline supplies it at ITS OWN existential witness              *)
(*  ([EchoDisc.disc_seg'] is [∃ cs, ... disc_pt cs i p]).  The two lists   *)
(*  are different objects, and F2 is stated at one list on purpose: it     *)
(*  compares [sess_n cs (m-1)] with [sess_n cs (length E)] by LENGTH, and  *)
(*  across two lists that comparison is simply false -- the alternatives   *)
(*  have different lengths, so [sess_n cs' 34] can be shorter than         *)
(*  [sess_n cs 17].                                                        *)
(*                                                                        *)
(*  What rescues it is the note's own remark about [line_alts] (EchoDisc,  *)
(*  the O5 ruling): the four alternatives begin with 'h', 'e', '$', 'f',   *)
(*  PAIRWISE DISTINCT, so the resolution is readable off the wire.  Hence  *)
(*  two session transcripts that are prefix-comparable AGREE, and the      *)
(*  discipline's witness may be replaced by the claim's wherever both are  *)
(*  below one wire.  That is [sess_n_prefix_det].                          *)
(* ====================================================================== *)

Lemma line_alts_nonnil (a : nat) :
  a < length line_alts -> line_alts !!! a <> [].
Proof.
  rewrite line_alts_length. intros Ha.
  destruct a as [|[|[|[|a]]]]; try lia; vm_compute; discriminate.
Qed.

Lemma line_alts_head_det (a b : nat) :
  a < length line_alts -> b < length line_alts ->
  line_alts !!! a !! 0 = line_alts !!! b !! 0 -> a = b.
Proof.
  rewrite line_alts_length. intros Ha Hb.
  destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; try lia;
    try reflexivity; intros H; vm_compute in H; discriminate.
Qed.

(* out of range [!!!] reads [0], which IS in range, so this is the honest
   hypothesis and it follows from the [Forall] both sides carry *)
Definition cs_ok (cs : list nat) : Prop :=
  forall i, cs !!! i < length line_alts.

Lemma cs_ok_of_Forall cs :
  Forall (fun x => x < length line_alts) cs -> cs_ok cs.
Proof.
  intros HF i. destruct (decide (i < length cs)) as [Hi|Hi].
  - destruct (lookup_lt_is_Some_2 cs i Hi) as [x Hx].
    rewrite (list_lookup_total_correct cs i x Hx).
    exact (Forall_lookup_1 _ _ _ _ HF Hx).
  - rewrite list_lookup_total_alt (lookup_ge_None_2 cs i ltac:(lia)) /=.
    pose proof line_alts_length. lia.
Qed.

Lemma lookup_total_drop {A} `{!Inhabited A} (n i : nat) (l : list A) :
  drop n l !!! i = l !!! (n + i).
Proof. by rewrite !list_lookup_total_alt lookup_drop. Qed.

Lemma cs_ok_drop cs n : cs_ok cs -> cs_ok (drop n cs).
Proof. intros H i. rewrite lookup_total_drop. apply H. Qed.

Lemma alt_blk_drop cs n i : alt_blk (drop n cs) i = alt_blk cs (n + i).
Proof. rewrite /alt_blk. by rewrite lookup_total_drop. Qed.

Lemma alt_seq_cons cs q :
  alt_seq cs (S q) = alt_blk cs 0 ++ alt_seq (drop 1 cs) q.
Proof.
  rewrite /alt_seq.
  replace (List.seq 0 (S q)) with (0 :: List.seq 1 q) by reflexivity.
  rewrite fmap_cons concat_cons. f_equal.
  rewrite -List.seq_shift -list_fmap_compose.
  f_equal. apply list_fmap_ext.
  intros i x Hx. rewrite /compose. by rewrite (alt_blk_drop cs 1 x).
Qed.

Lemma alt_blk_length cs i : 0 < length (alt_blk cs i).
Proof.
  rewrite /alt_blk length_app. pose proof echo_line_length. lia.
Qed.

(* THE STEP: two block sequences below one wire have the same blocks. *)
Lemma alt_seq_prefix_det (q' : nat) :
  forall (cs cs' : list nat) (q : nat) (t' t : list (bv 8)),
    cs_ok cs -> cs_ok cs' ->
    t' `prefix_of` echo_line -> t `prefix_of` echo_line ->
    (alt_seq cs' q' ++ t') `prefix_of` (alt_seq cs q ++ t) ->
    q' <= q /\ alt_seq cs' q' = alt_seq cs q'.
Proof.
  induction q' as [| n IH]; intros cs cs' q t' t Hcs Hcs' Ht' Ht Hpre.
  { split; [lia | reflexivity]. }
  pose proof echo_line_length as HL.
  assert (Hp' : 0 < length (line_alts !!! (cs' !!! 0%nat))).
  { destruct (line_alts !!! (cs' !!! 0%nat)) as [| z zs] eqn:Hz;
      [ exfalso; exact (line_alts_nonnil _ (Hcs' 0%nat) Hz) | cbn; lia ]. }
  destruct q as [| p].
  { exfalso.
    rewrite alt_seq_0 app_nil_l alt_seq_cons -app_assoc in Hpre.
    apply prefix_length in Hpre. apply prefix_length in Ht.
    rewrite /alt_blk !length_app in Hpre. lia. }
  rewrite alt_seq_cons -app_assoc in Hpre.
  rewrite (alt_seq_cons cs p) -app_assoc in Hpre.
  rewrite /alt_blk -!app_assoc in Hpre.
  apply prefix_app_cancel in Hpre.
  (* the alternatives' first bytes agree, so the choices do *)
  assert (Hhd : cs' !!! 0%nat = cs !!! 0%nat).
  { apply line_alts_head_det; [apply Hcs' | apply Hcs |].
    assert (Hp : 0 < length (line_alts !!! (cs !!! 0%nat))).
    { destruct (line_alts !!! (cs !!! 0%nat)) as [| z zs] eqn:Hz;
        [ exfalso; exact (line_alts_nonnil _ (Hcs 0%nat) Hz) | cbn; lia ]. }
    destruct (lookup_lt_is_Some_2 (line_alts !!! (cs' !!! 0%nat)) 0 Hp')
      as [z Hz].
    assert (Hz1 : (line_alts !!! (cs' !!! 0%nat)
                    ++ (alt_seq (drop 1 cs') n ++ t')) !! 0 = Some z)
      by (rewrite lookup_app_l; [exact Hz | lia]).
    assert (Hz2 : (line_alts !!! (cs !!! 0%nat)
                    ++ (alt_seq (drop 1 cs) p ++ t)) !! 0 = Some z)
      by (eapply prefix_lookup_Some; [exact Hz1 | exact Hpre]).
    rewrite lookup_app_l in Hz2; [| lia].
    by rewrite Hz Hz2. }
  rewrite Hhd in Hpre. apply prefix_app_cancel in Hpre.
  destruct (IH (drop 1 cs) (drop 1 cs') p t' t
              (cs_ok_drop _ _ Hcs) (cs_ok_drop _ _ Hcs') Ht' Ht Hpre)
    as [Hle Heq].
  split; [lia |].
  rewrite alt_seq_cons (alt_seq_cons cs n) Heq /alt_blk Hhd. reflexivity.
Qed.

(* ...AND THE SESSION TRANSCRIPTS THEMSELVES.  This is what lets lane
   ECHO-OUT feed [D2_next_input] the discipline's bound at the CLAIM's
   choice list. *)
Lemma div_lt_of_div_lt (i j p : nat) :
  0 < p -> i `div` p < j `div` p -> i < j.
Proof.
  intros Hp Hlt.
  pose proof (Nat.div_mod_eq i p) as Hi.
  pose proof (Nat.div_mod_eq j p) as Hj.
  pose proof (Nat.mod_upper_bound i p ltac:(lia)) as Hm.
  assert (Hs : p * S (i `div` p) <= p * (j `div` p))
    by (apply Nat.mul_le_mono_l; lia).
  rewrite Nat.mul_succ_r in Hs. lia.
Qed.

Lemma sess_n_prefix_det (cs cs' : list nat) (i j : nat) :
  Forall (fun x => x < length line_alts) cs ->
  Forall (fun x => x < length line_alts) cs' ->
  sess_n cs' i `prefix_of` sess_n cs j ->
  i <= j /\ sess_n cs' i = sess_n cs i.
Proof.
  intros Hcs Hcs' Hpre.
  pose proof (cs_ok_of_Forall _ Hcs) as Hok.
  pose proof (cs_ok_of_Forall _ Hcs') as Hok'.
  pose proof echo_line_length as HL.
  (* [sess_n] is [u_prologue ++ (blocks ++ partial line)]: cancel the
     prologue and compare the block sequences *)
  rewrite /sess_n in Hpre. apply prefix_app_cancel in Hpre.
  assert (Ht' : take (i `mod` length echo_line) echo_line `prefix_of` echo_line)
    by apply prefix_take.
  assert (Ht : take (j `mod` length echo_line) echo_line `prefix_of` echo_line)
    by apply prefix_take.
  destruct (alt_seq_prefix_det (i `div` length echo_line) cs cs'
              (j `div` length echo_line) _ _ Hok Hok' Ht' Ht Hpre)
    as [Hqle Hqeq].
  assert (Hsess : sess_n cs' i = sess_n cs i)
    by (rewrite /sess_n Hqeq; reflexivity).
  split; [| exact Hsess].
  destruct (decide (i `div` length echo_line < j `div` length echo_line))
    as [Hlt | Hnlt].
  - pose proof (div_lt_of_div_lt i j (length echo_line) ltac:(lia) Hlt). lia.
  - assert (Hqe : i `div` length echo_line = j `div` length echo_line) by lia.
    rewrite Hqeq Hqe in Hpre. apply prefix_app_cancel in Hpre.
    apply prefix_length in Hpre. rewrite !length_take in Hpre.
    pose proof (Nat.div_mod_eq i (length echo_line)) as Hi.
    pose proof (Nat.div_mod_eq j (length echo_line)) as Hj.
    pose proof (Nat.mod_upper_bound i (length echo_line) ltac:(lia)).
    pose proof (Nat.mod_upper_bound j (length echo_line) ltac:(lia)).
    rewrite Hqe in Hi. lia.
Qed.

(* the open cycle's FULL discipline, not only D3 -- [disc_seg_open_seg]'s
   twin, and the one lane ECHO-OUT's echo step spends *)
Lemma disc_seg'_open_seg (h : list mobs) :
  trace_shape h true -> disc h -> disc_seg' (open_seg h).
Proof.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply elem_of_list_lookup in Hin as [i Hi].
  exact (Forall_lookup_1 _ _ _ _ Hd Hi).
Qed.

(* THE DISCIPLINE'S LOWER BOUND AT THE OPEN CYCLE'S LAST INPUT: D1/D2 read
   off [disc_seg'] at one index, which is what F2's [Hlow] is.  The choice
   list is the DISCIPLINE's; [sess_n_prefix_det] is what moves the bound to
   the claim's. *)
Lemma disc_seg'_pt_last (seg : list mobs) (c : bv 8) :
  disc_seg' seg -> obs_ends_in Uart0 seg c ->
  exists cs' : list nat,
    Forall (fun x => x < length line_alts) cs'
    /\ sess_n cs' (length (ins seg) - 1) `prefix_of` obs_wire Uart0 seg.
Proof.
  intros [Hd (cs & Hlen & Hf & Hall)] [seg0 ->].
  exists cs. split; [exact Hf |].
  assert (Hip : in_pres (seg0 ++ [ObsUartIn Uart0 c]) !! (length (ins seg0))
                = Some seg0).
  { rewrite in_pres_in lookup_app_r in_pres_length ?Nat.sub_diag //. }
  specialize (Hall _ _ Hip). rewrite /disc_pt in Hall.
  rewrite ins_app ins_in length_app /=.
  replace (length (ins seg0) + 1 - 1) with (length (ins seg0)) by lia.
  etrans; [exact Hall |]. rewrite obs_wire_app. by eexists.
Qed.

(* [sess_n] is never empty: it begins with the prologue *)
Lemma u_prologue_pos : 0 < length u_prologue.
Proof. vm_compute. lia. Qed.

Lemma sess_n_nonnil (cs : list nat) (n : nat) : sess_n cs n <> [].
Proof.
  rewrite /sess_n. intros H.
  apply (f_equal length) in H. rewrite !length_app /= in H.
  pose proof u_prologue_pos. lia.
Qed.

(* ====================================================================== *)
(*  10.  THE SAME-CYCLE BRIDGE (lane ECHO-OUT, section 7)                  *)
(*                                                                        *)
(*  The claims record their same-cycle facts at their OWN witness history  *)
(*  [ho]; the ledger's drain reads them at the run's history [h], and the  *)
(*  kernel supplies [ho `prefix_of` h] ([App.Htx]) and the era stamp at    *)
(*  both ends.  What is missing is the step from "a prefix, at the same    *)
(*  boot count" to "a prefix of the OPEN SEGMENT" -- and that is exactly   *)
(*  where the boot count earns its keep: a suffix with no PowerOn in it    *)
(*  cannot contain a PowerOff either, because the machine is ON at the     *)
(*  end and only a PowerOn turns it back on.                              *)
(* ====================================================================== *)

Lemma epu_foldl_obs_step_none (h : list mobs) :
  foldl obs_step None h = None.
Proof. induction h as [| e h IH]; [done |]. by cbn. Qed.

Lemma epu_no_power_of_boots (h : list mobs) (st : bool) :
  obs_boots h = 0%nat ->
  foldl obs_step (Some st) h = Some true ->
  st = true /\ Forall (fun e => is_io e = true) h.
Proof.
  revert st. induction h as [| e h IH]; intros st Hb Hf.
  - cbn in Hf. injection Hf as ->. split; [reflexivity | constructor].
  - destruct e as [i b | i b | |]; cbn in Hb.
    + cbn in Hf. destruct st.
      * destruct (IH true Hb Hf) as [_ HF].
        split; [reflexivity | by constructor].
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
    + cbn in Hf. destruct st.
      * destruct (IH true Hb Hf) as [_ HF].
        split; [reflexivity | by constructor].
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
    + (* ObsPowerOn *) lia.
    + (* ObsPowerOff *)
      cbn in Hf. destruct st.
      * destruct (IH false Hb Hf) as [Habs _]. discriminate.
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
Qed.

Lemma open_seg_prefix_boots (h1 h2 : list mobs) :
  h1 `prefix_of` h2 -> obs_boots h1 = obs_boots h2 ->
  trace_shape h2 true -> open_seg h1 `prefix_of` open_seg h2.
Proof.
  intros [k ->] Hb Hsh.
  assert (Hk : obs_boots k = 0%nat)
    by (rewrite obs_boots_app in Hb; lia).
  rewrite /trace_shape foldl_app in Hsh.
  destruct (foldl obs_step (Some false) h1) as [st |] eqn:Hst; last first.
  { rewrite epu_foldl_obs_step_none in Hsh. discriminate. }
  destruct (epu_no_power_of_boots k st Hk Hsh) as [_ HF].
  rewrite (open_seg_io h1 k HF). by eexists.
Qed.

Lemma ins_prefix_of (s1 s2 : list mobs) :
  s1 `prefix_of` s2 -> ins s1 `prefix_of` ins s2.
Proof. intros [z ->]. rewrite ins_app. by eexists. Qed.
