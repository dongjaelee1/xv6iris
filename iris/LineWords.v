(* ===================================================================== *)
(* LineWords.v -- A CONSOLE LINE AS A LIST OF WORDS.                      *)
(*                                                                        *)
(* The vocabulary, and nothing that needs a lexer: a line is a list of     *)
(* WORDS joined by single spaces and closed by a newline, [wl_line], and   *)
(* word [i] of it sits at [wl_off] and is named by token [i] of            *)
(* [wl_toks].  That is the shape of line a disciplined console session     *)
(* types, and every statement about such a line reads it through these     *)
(* four definitions rather than through its bytes.                         *)
(*                                                                        *)
(* WHAT SH'S LEXER MAKES OF IT is [UkShWords.v], which sits above          *)
(* [UkShParse]; this file depends on nothing but stdpp, so the discipline  *)
(* ([EchoDisc.v]) can spell its line with it.                              *)
(*                                                                        *)
(* THE CUT.  A line is not a uniform join: the FIRST word has no separator *)
(* before it and the LAST has the newline rather than a space after it.    *)
(* So the body is [wl_body (w :: r) = w ++ wl_tail r] with [wl_tail        *)
(* (w :: r) = ' ' :: wl_body (w :: r)], and every induction over a line    *)
(* runs on [wl_tail] -- whose offset always points AT a blank.  The first  *)
(* word is then the only special case.                                     *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import list bitvector.definitions.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ===================================================================== *)
(*  S1  THE TWO BLANKS A DISCIPLINED LINE USES                            *)
(* ===================================================================== *)

Definition wl_sp : bv 8 := Z_to_bv 8 32%Z.   (* ' '  -- the ONE separator *)
Definition wl_nl : bv 8 := Z_to_bv 8 10%Z.   (* '\n' -- what [gets] keeps *)

(* their numeric readings, so that a proof refuting a byte reasons with
   [lia] and never with [vm_compute] inside a [Prop] *)
Lemma wl_sp_val : bv_unsigned wl_sp = 32%Z.
Proof. by vm_compute. Qed.
Lemma wl_nl_val : bv_unsigned wl_nl = 10%Z.
Proof. by vm_compute. Qed.

(* ===================================================================== *)
(*  S2  THE LINE                                                          *)
(* ===================================================================== *)

(* the separator-led tail: every word after the first is ONE space and the
   word.  [wl_tail (w :: r) = ' ' :: wl_body (w :: r)] is the equation
   every induction over a line turns on. *)
Fixpoint wl_tail (ws : list (list (bv 8))) : list (bv 8) :=
  match ws with
  | [] => []
  | w :: r => wl_sp :: (w ++ wl_tail r)
  end.

Definition wl_body (ws : list (list (bv 8))) : list (bv 8) :=
  match ws with
  | [] => []
  | w :: r => w ++ wl_tail r
  end.

(* ...and the LINE is the body plus the newline [gets] stops at and keeps *)
Definition wl_line (ws : list (list (bv 8))) : list (bv 8) :=
  wl_body ws ++ [wl_nl].

Lemma wl_tail_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  wl_tail (w :: r) = wl_sp :: wl_body (w :: r).
Proof. reflexivity. Qed.

Lemma wl_body_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  wl_body (w :: r) = w ++ wl_tail r.
Proof. reflexivity. Qed.

Lemma wl_line_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  wl_line (w :: r) = w ++ (wl_tail r ++ [wl_nl]).
Proof. rewrite /wl_line wl_body_cons -app_assoc. reflexivity. Qed.

Lemma wl_line_nil : wl_line [] = [wl_nl].
Proof. reflexivity. Qed.

Lemma wl_line_length (ws : list (list (bv 8))) :
  length (wl_line ws) = length (wl_body ws) + 1.
Proof. rewrite /wl_line length_app. cbn [length]. reflexivity. Qed.

(* every line has its newline, so no line is empty -- which is what the
   discipline's [star_prefix] and every division by the line's length
   need, and all either of them needs *)
Lemma wl_line_pos (ws : list (list (bv 8))) : 0 < length (wl_line ws).
Proof. rewrite wl_line_length. lia. Qed.

(* a nonempty tail is a separator and the rest of the body *)
Lemma wl_tail_length_cons (r : list (list (bv 8))) :
  r <> [] -> length (wl_tail r) = S (length (wl_body r)).
Proof. destruct r as [| w0 r0]; [done |]. intros _. reflexivity. Qed.

(* ===================================================================== *)
(*  S3  WHAT A WORD MAY CARRY                                             *)
(*                                                                        *)
(*  ALPHANUMERIC, and nonempty.  Stated POSITIVELY, as the admissible set  *)
(*  rather than as a list of things to avoid, because everything the line  *)
(*  must avoid is then a consequence proved once: sh's five blanks and     *)
(*  seven metacharacters ([UkShWords.wl_alnum_plain]), the console's       *)
(*  carriage return, its three erase characters, its end-of-file byte and  *)
(*  the NUL -- all of them from [wl_line_byte_val] below.  A literal line  *)
(*  used to answer each of those by case analysis over its own bytes.      *)
(* ===================================================================== *)

Definition wl_alnum (b : bv 8) : Prop :=
  (48 <= bv_unsigned b <= 57)%Z        (* 0-9 *)
  \/ (65 <= bv_unsigned b <= 90)%Z     (* A-Z *)
  \/ (97 <= bv_unsigned b <= 122)%Z.   (* a-z *)

Global Instance wl_alnum_dec b : Decision (wl_alnum b).
Proof. rewrite /wl_alnum. apply _. Defined.

Definition wl_word (w : list (bv 8)) : Prop :=
  w <> [] /\ Forall wl_alnum w.

Global Instance wl_word_dec w : Decision (wl_word w).
Proof. rewrite /wl_word. apply _. Defined.

Definition wl_wf (ws : list (list (bv 8))) : Prop := Forall wl_word ws.

Global Instance wl_wf_dec ws : Decision (wl_wf ws).
Proof. rewrite /wl_wf. apply _. Defined.

Lemma wl_wf_cons (w : list (bv 8)) (r : list (list (bv 8))) :
  wl_wf (w :: r) -> wl_word w /\ wl_wf r.
Proof. rewrite /wl_wf. apply Forall_cons_1. Qed.

Lemma wl_word_pos (w : list (bv 8)) : wl_word w -> 0 < length w.
Proof. intros [Hne _]. destruct w as [| b w']; [done | cbn; lia]. Qed.

(* ---- every byte of the line, and which ones they are ------------------ *)

Definition wl_body_byte (b : bv 8) : Prop := wl_alnum b \/ b = wl_sp.

Lemma wl_alnum_body (w : list (bv 8)) :
  Forall wl_alnum w -> Forall wl_body_byte w.
Proof.
  induction w as [| b w' IH]; intro Hw; [constructor |].
  destruct (Forall_cons_1 _ _ _ Hw) as [Hb Hw'].
  constructor; [by left | exact (IH Hw')].
Qed.

Lemma wl_tail_bytes (ws : list (list (bv 8))) :
  wl_wf ws -> Forall wl_body_byte (wl_tail ws).
Proof.
  induction ws as [| w r IH]; intro Hwf; cbn [wl_tail]; [constructor |].
  destruct (wl_wf_cons w r Hwf) as [[_ Hw] Hr].
  constructor; [by right |].
  apply Forall_app. split; [exact (wl_alnum_body w Hw) | exact (IH Hr)].
Qed.

Lemma wl_body_bytes (ws : list (list (bv 8))) :
  wl_wf ws -> Forall wl_body_byte (wl_body ws).
Proof.
  intro Hwf. destruct ws as [| w r]; cbn [wl_body]; [constructor |].
  destruct (wl_wf_cons w r Hwf) as [[_ Hw] Hr].
  apply Forall_app.
  split; [exact (wl_alnum_body w Hw) | exact (wl_tail_bytes r Hr)].
Qed.

(* THE ONE BYTE-LEVEL FACT EVERY CONSUMER SPENDS: a numeric reading of
   every byte the line can carry.  A caller that has to refute one
   particular byte -- '\r', ^U, backspace, DEL, ^D, NUL -- gets it from
   this by [lia] and never by looking at a literal. *)
Lemma wl_line_byte_val (ws : list (list (bv 8))) (b : bv 8) :
  wl_wf ws -> b ∈ wl_line ws ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof.
  intros Hwf Hb. rewrite /wl_line in Hb.
  apply elem_of_app in Hb as [Hb | Hb].
  - apply elem_of_list_lookup_1 in Hb as [i Hi].
    destruct (Forall_lookup_1 _ _ _ _ (wl_body_bytes ws Hwf) Hi)
      as [[H | [H | H]] | ->].
    + right. right. by left.
    + right. right. right. by left.
    + right. right. right. by right.
    + right. left. exact wl_sp_val.
  - apply elem_of_list_singleton in Hb as ->. left. exact wl_nl_val.
Qed.

(* ...AND ITS POSITIONAL HALF: the ONLY newline is the last byte, which is
   what [gets] stopping at the first one says about the buffer it read. *)
Lemma wl_line_nl_last (ws : list (list (bv 8))) (k : nat) :
  wl_wf ws -> wl_line ws !! k = Some wl_nl -> k = length (wl_body ws).
Proof.
  intros Hwf Hk.
  destruct (decide (k < length (wl_body ws))) as [Hlt | Hge].
  - exfalso. rewrite /wl_line (lookup_app_l _ _ k Hlt) in Hk.
    destruct (Forall_lookup_1 _ _ _ _ (wl_body_bytes ws Hwf) Hk)
      as [Ha | Hsp].
    + rewrite /wl_alnum wl_nl_val in Ha. lia.
    + apply (f_equal bv_unsigned) in Hsp.
      rewrite wl_nl_val wl_sp_val in Hsp. lia.
  - apply lookup_lt_Some in Hk. rewrite wl_line_length in Hk. lia.
Qed.

(* ===================================================================== *)
(*  S4  WHERE THE WORDS SIT                                               *)
(* ===================================================================== *)

(* word [i] of a line whose body starts at [off] begins here.  Recursive
   on the word list (not on [i]), so it is the same recursion the token
   list and the [wl_tail] induction run on. *)
Fixpoint wl_off (off : nat) (ws : list (list (bv 8))) (i : nat) : nat :=
  match ws with
  | [] => off
  | w :: r =>
      match i with
      | O => off
      | S i' => wl_off (S (off + length w)) r i'
      end
  end.

(* ...and the token list [UkShParse.ushp_tokens] names: one [(start, end)]
   per word, the next word's start ONE blank past the previous end. *)
Fixpoint wl_toks_at (off : nat) (ws : list (list (bv 8)))
  : list (nat * nat) :=
  match ws with
  | [] => []
  | w :: r => (off, off + length w) :: wl_toks_at (S (off + length w)) r
  end.

Definition wl_toks (ws : list (list (bv 8))) : list (nat * nat) :=
  wl_toks_at 0 ws.

Lemma wl_off_0 (off : nat) (ws : list (list (bv 8))) : wl_off off ws 0 = off.
Proof. by destruct ws. Qed.

Lemma wl_off_ge (ws : list (list (bv 8))) :
  forall off i : nat, off <= wl_off off ws i.
Proof.
  induction ws as [| w r IH]; intros off i; cbn; [lia |].
  destruct i as [| i']; [lia |].
  pose proof (IH (S (off + length w)) i'). lia.
Qed.

Lemma wl_toks_at_length (ws : list (list (bv 8))) :
  forall off : nat, length (wl_toks_at off ws) = length ws.
Proof.
  induction ws as [| w r IH]; intro off; cbn; [reflexivity |].
  by rewrite IH.
Qed.

Lemma wl_toks_length (ws : list (list (bv 8))) :
  length (wl_toks ws) = length ws.
Proof. apply wl_toks_at_length. Qed.

Lemma wl_toks_at_lookup (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)),
    ws !! i = Some w ->
    wl_toks_at off ws !! i
    = Some (wl_off off ws i, wl_off off ws i + length w).
Proof.
  induction ws as [| w0 r IH]; intros off i w Hi; [by destruct i |].
  destruct i as [| i']; cbn in Hi |- *.
  - by injection Hi as <-.
  - exact (IH (S (off + length w0)) i' w Hi).
Qed.

(* every token of a list laid out from [p] lies at or past [p] -- the one
   fact the cut's non-interference argument spends *)
Lemma wl_toks_at_ge (ws : list (list (bv 8))) :
  forall (p : nat) (tk : nat * nat),
    tk ∈ wl_toks_at p ws -> p <= fst tk /\ p <= snd tk.
Proof.
  induction ws as [| w r IH]; intros p tk Htk; cbn in Htk.
  - by apply elem_of_nil in Htk.
  - apply elem_of_cons in Htk as [-> | Htk]; cbn; [lia |].
    pose proof (IH (S (p + length w)) tk Htk). lia.
Qed.

(* ...and no word runs past the body's end, so every index a word names is
   inside the line *)
Lemma wl_off_le_body (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)) (j : nat),
    ws !! i = Some w -> j <= length w ->
    wl_off off ws i + j <= off + length (wl_body ws).
Proof.
  induction ws as [| w0 r IH]; intros off i w j Hi Hj; [by destruct i |].
  rewrite wl_body_cons length_app.
  destruct i as [| i']; cbn [wl_off] in *.
  - injection Hi as <-. lia.
  - assert (Hrne : r <> []).
    { intro Hnil. rewrite Hnil in Hi. by destruct i'. }
    pose proof (IH (S (off + length w0)) i' w j Hi Hj) as Hle.
    rewrite (wl_tail_length_cons r Hrne). lia.
Qed.

Lemma wl_off_lt_line (ws : list (list (bv 8))) (i : nat) (w : list (bv 8))
    (j : nat) :
  ws !! i = Some w -> j <= length w ->
  wl_off 0 ws i + j < length (wl_line ws).
Proof.
  intros Hi Hj. rewrite wl_line_length.
  pose proof (wl_off_le_body ws 0 i w j Hi Hj). lia.
Qed.

(* ===================================================================== *)
(*  S4  READING THE LINE                                                  *)
(*                                                                        *)
(*  Three [!!!] laws, so the byte bookkeeping over a join is rewriting and *)
(*  not a fresh [lia] each time.                                          *)
(* ===================================================================== *)

Lemma wl_lta_app_l {A} `{Inhabited A} (u v : list A) (j : nat) :
  j < length u -> (u ++ v) !!! j = u !!! j.
Proof.
  intro Hj. rewrite !list_lookup_total_alt (lookup_app_l u v j Hj).
  reflexivity.
Qed.

Lemma wl_lta_app_r {A} `{Inhabited A} (u v : list A) (j : nat) :
  (u ++ v) !!! (length u + j) = v !!! j.
Proof.
  rewrite !list_lookup_total_alt
    (lookup_app_r u v (length u + j) ltac:(lia)).
  by replace (length u + j - length u) with j by lia.
Qed.

Lemma wl_lta_cons_S {A} `{Inhabited A} (x : A) (l : list A) (j : nat) :
  (x :: l) !!! S j = l !!! j.
Proof. reflexivity. Qed.

(* WORD [i]'S BYTES ARE THE LINE'S, at the offset the join puts them --
   so a statement about the line's byte at [wl_off ws i + j] is a
   statement about the word, which is what lets a caller stop naming the
   line's bytes at all.  Proved with the already-joined PREFIX explicit,
   because that is what the induction consumes. *)
Lemma wl_line_word_pre (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)) (j : nat) (pre : list (bv 8)),
    ws !! i = Some w -> j < length w -> off = length pre ->
    (pre ++ wl_body ws ++ [wl_nl]) !!! (wl_off off ws i + j) = w !!! j.
Proof.
  induction ws as [| w0 r IH]; intros off i w j pre Hi Hj Hoff;
    [by destruct i |].
  destruct i as [| i']; cbn [wl_off].
  - cbn in Hi. injection Hi as Heq. subst w0.
    rewrite wl_body_cons -!app_assoc Hoff.
    rewrite (wl_lta_app_r pre (w ++ wl_tail r ++ [wl_nl]) j).
    exact (wl_lta_app_l w _ j Hj).
  - assert (Hrne : r <> []).
    { intro Hnil. rewrite Hnil in Hi. by destruct i'. }
    assert (Hsplit : pre ++ wl_body (w0 :: r) ++ [wl_nl]
                     = (pre ++ w0 ++ [wl_sp]) ++ wl_body r ++ [wl_nl]).
    { destruct r as [| w1 r1]; [exfalso; by apply Hrne |].
      rewrite wl_body_cons wl_tail_cons.
      change (wl_sp :: wl_body (w1 :: r1))
        with ([wl_sp] ++ wl_body (w1 :: r1)).
      by rewrite -!app_assoc. }
    rewrite Hsplit.
    exact (IH (S (off + length w0)) i' w j (pre ++ w0 ++ [wl_sp])
             Hi Hj ltac:(rewrite !length_app; cbn [length]; lia)).
Qed.

(* THE NEXT WORD STARTS ONE BLANK PAST THIS ONE'S END -- the recurrence
   every cursor that walks the line spends, and the reason a write chain
   over the words needs no offset arithmetic of its own. *)
Lemma wl_off_S_at (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)),
    ws !! i = Some w -> wl_off off ws (S i) = S (wl_off off ws i + length w).
Proof.
  induction ws as [| w0 r IH]; intros off i w Hi; [by destruct i |].
  destruct i as [| i'].
  - cbn in Hi. injection Hi as Heq. subst w0.
    cbn [wl_off]. by rewrite wl_off_0.
  - cbn [wl_off]. exact (IH (S (off + length w0)) i' w Hi).
Qed.

(* ...AND WHAT SITS THERE: a separator while another word follows, and the
   closing newline once none does. *)
(* a lookup at the junction of a three-way join, with the index EXPLICIT:
   an [ltac:(lia)] inside [lookup_app_r] sees the index as an evar and
   fails (durable-notes, "Inline [ltac:] and evar-typed holes"). *)
Lemma wl_lookup_mid {A} (u m v : list A) (x : A) (j : nat) :
  j = length u + length m ->
  (u ++ m ++ x :: v) !! j = Some x.
Proof.
  intros ->.
  rewrite (lookup_app_r u (m ++ x :: v) (length u + length m) ltac:(lia)).
  replace (length u + length m - length u) with (length m) by lia.
  rewrite (lookup_app_r m (x :: v) (length m) ltac:(lia)) Nat.sub_diag.
  reflexivity.
Qed.

Lemma wl_line_sep_pre (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)) (pre : list (bv 8)),
    ws !! i = Some w -> (S i < length ws)%nat -> off = length pre ->
    (pre ++ wl_body ws ++ [wl_nl]) !! (wl_off off ws i + length w)
    = Some wl_sp.
Proof.
  induction ws as [| w0 r IH]; intros off i w pre Hi Hlen Hoff;
    [by destruct i |].
  destruct i as [| i'].
  - cbn in Hi. injection Hi as Heq. subst w0.
    destruct r as [| w1 r1]; [cbn [length] in Hlen; lia |].
    assert (Hshape : wl_body (w :: w1 :: r1) ++ [wl_nl]
                     = w ++ wl_sp :: (wl_body (w1 :: r1) ++ [wl_nl])).
    { rewrite wl_body_cons wl_tail_cons. symmetry.
      exact (app_assoc w (wl_sp :: wl_body (w1 :: r1)) [wl_nl]). }
    rewrite wl_off_0 Hoff Hshape.
    exact (wl_lookup_mid pre w (wl_body (w1 :: r1) ++ [wl_nl]) wl_sp
             (length pre + length w) eq_refl).
  - assert (Hrne : r <> []).
    { intro Hnil. rewrite Hnil in Hi. by destruct i'. }
    assert (Hsplit : pre ++ wl_body (w0 :: r) ++ [wl_nl]
                     = (pre ++ w0 ++ [wl_sp]) ++ wl_body r ++ [wl_nl]).
    { destruct r as [| w1 r1]; [exfalso; by apply Hrne |].
      rewrite wl_body_cons wl_tail_cons.
      change (wl_sp :: wl_body (w1 :: r1))
        with ([wl_sp] ++ wl_body (w1 :: r1)).
      by rewrite -!app_assoc. }
    cbn [wl_off]. rewrite Hsplit.
    exact (IH (S (off + length w0)) i' w (pre ++ w0 ++ [wl_sp]) Hi
             ltac:(cbn [length] in Hlen; lia)
             ltac:(rewrite !length_app; cbn [length]; lia)).
Qed.

Lemma wl_line_sep (ws : list (list (bv 8))) (i : nat) (w : list (bv 8)) :
  ws !! i = Some w -> (S i < length ws)%nat ->
  wl_line ws !! (wl_off 0 ws i + length w) = Some wl_sp.
Proof.
  intros Hi Hlen.
  exact (wl_line_sep_pre ws 0 i w [] Hi Hlen eq_refl).
Qed.

(* the LAST word's end IS the body's end, which is where the newline is *)
Lemma wl_off_last (ws : list (list (bv 8))) :
  forall (off i : nat) (w : list (bv 8)),
    ws !! i = Some w -> S i = length ws ->
    wl_off off ws i + length w = off + length (wl_body ws).
Proof.
  induction ws as [| w0 r IH]; intros off i w Hi Hlen; [by destruct i |].
  destruct i as [| i'].
  - cbn in Hi. injection Hi as Heq. subst w0.
    destruct r as [| w1 r1]; [| cbn [length] in Hlen; lia].
    rewrite wl_off_0 wl_body_cons. cbn [wl_tail]. rewrite app_nil_r. lia.
  - assert (Hrne : r <> []).
    { intro Hnil. rewrite Hnil in Hi. by destruct i'. }
    cbn [wl_off].
    rewrite (IH (S (off + length w0)) i' w Hi
               ltac:(cbn [length] in Hlen; lia)).
    rewrite wl_body_cons length_app (wl_tail_length_cons r Hrne). lia.
Qed.

Lemma wl_line_nl_at (ws : list (list (bv 8))) :
  wl_line ws !! length (wl_body ws) = Some wl_nl.
Proof.
  rewrite /wl_line
    (lookup_app_r (wl_body ws) [wl_nl] (length (wl_body ws)) ltac:(lia))
    Nat.sub_diag.
  reflexivity.
Qed.

Lemma wl_line_word (ws : list (list (bv 8))) (i : nat) (w : list (bv 8))
    (j : nat) :
  ws !! i = Some w -> j < length w ->
  wl_line ws !!! (wl_off 0 ws i + j) = w !!! j.
Proof.
  intros Hi Hj.
  exact (wl_line_word_pre ws 0 i w j [] Hi Hj eq_refl).
Qed.

(* ===================================================================== *)
(*  S5  THE LINE IS PARSEABLE: what was typed is a function of the wire   *)
(* ===================================================================== *)

(* A claim of the shape "whatever you type, echo prints it back" only says
   something if the observer can tell WHAT was typed.  The wire carries the
   console's echo of the line and then whatever ran; the line ends at the
   first newline, and inside it each word ends at the first blank.  Both
   readings are the same fact -- a WORD is alphanumeric and a SEPARATOR is
   not -- so both are this one lemma.

   Stated as a SPLITTING law rather than as injectivity of [wl_line]: the
   consumer is a wire with a remainder after the line, and it needs the
   remainder to match too. *)
Lemma wl_split_pred (P : bv 8 -> Prop) (u1 t1 u2 t2 : list (bv 8)) :
  Forall P u1 -> Forall P u2 ->
  (forall b, head t1 = Some b -> ~ P b) ->
  (forall b, head t2 = Some b -> ~ P b) ->
  u1 ++ t1 = u2 ++ t2 -> u1 = u2 /\ t1 = t2.
Proof.
  revert u2. induction u1 as [| a u1' IH]; intros u2 H1 H2 Ht1 Ht2 Heq.
  - destruct u2 as [| b u2']; [by split |].
    exfalso. cbn in Heq.
    destruct (Forall_cons_1 _ _ _ H2) as [Hb _].
    exact (Ht1 b ltac:(by rewrite Heq) Hb).
  - destruct u2 as [| b u2'].
    + exfalso. cbn in Heq.
      destruct (Forall_cons_1 _ _ _ H1) as [Ha _].
      exact (Ht2 a ltac:(by rewrite -Heq) Ha).
    + cbn in Heq. injection Heq as Hab Hrest. subst b.
      destruct (Forall_cons_1 _ _ _ H1) as [_ H1'].
      destruct (Forall_cons_1 _ _ _ H2) as [_ H2'].
      destruct (IH u2' H1' H2' Ht1 Ht2 Hrest) as [-> ->]. by split.
Qed.

(* the two bytes that are not word bytes, which is what makes the split
   land where it does *)
Lemma wl_alnum_not_sp : ~ wl_alnum wl_sp.
Proof. rewrite /wl_alnum wl_sp_val. lia. Qed.

Lemma wl_body_byte_not_nl : ~ wl_body_byte wl_nl.
Proof.
  rewrite /wl_body_byte /wl_alnum wl_nl_val. intros [H | H]; [lia |].
  apply (f_equal bv_unsigned) in H. rewrite wl_nl_val wl_sp_val in H. lia.
Qed.

(* a tail either is empty or opens on the blank [wl_tail] puts there, so
   it never opens on a word byte *)
Lemma wl_tail_head_not_alnum (ws : list (list (bv 8))) (b : bv 8) :
  head (wl_tail ws) = Some b -> ~ wl_alnum b.
Proof.
  destruct ws as [| w r]; cbn [wl_tail]; [done |].
  intros [= <-]. exact wl_alnum_not_sp.
Qed.

Lemma wl_nl_head_not_body (t : list (bv 8)) (b : bv 8) :
  head (wl_nl :: t) = Some b -> ~ wl_body_byte b.
Proof. intros [= <-]. exact wl_body_byte_not_nl. Qed.

Lemma wl_tail_inj (ws1 ws2 : list (list (bv 8))) :
  wl_wf ws1 -> wl_wf ws2 -> wl_tail ws1 = wl_tail ws2 -> ws1 = ws2.
Proof.
  revert ws2. induction ws1 as [| w1 r1 IH]; intros ws2 Hw1 Hw2 Heq.
  - by destruct ws2 as [| w2 r2]; [| cbn in Heq].
  - destruct ws2 as [| w2 r2]; [by cbn in Heq |].
    cbn [wl_tail] in Heq. injection Heq as Heq.
    destruct (wl_wf_cons w1 r1 Hw1) as [[_ Ha1] Hr1].
    destruct (wl_wf_cons w2 r2 Hw2) as [[_ Ha2] Hr2].
    destruct (wl_split_pred wl_alnum w1 (wl_tail r1) w2 (wl_tail r2)
                Ha1 Ha2 (wl_tail_head_not_alnum r1)
                (wl_tail_head_not_alnum r2) Heq) as [-> Hr].
    by rewrite (IH r2 Hr1 Hr2 Hr).
Qed.

Lemma wl_body_inj (ws1 ws2 : list (list (bv 8))) :
  wl_wf ws1 -> wl_wf ws2 -> wl_body ws1 = wl_body ws2 -> ws1 = ws2.
Proof.
  intros Hw1 Hw2 Heq.
  destruct ws1 as [| w1 r1]; destruct ws2 as [| w2 r2]; [done | | |].
  - exfalso. destruct (wl_wf_cons w2 r2 Hw2) as [Hwd2 _].
    pose proof (wl_word_pos w2 Hwd2).
    apply (f_equal length) in Heq. rewrite wl_body_cons length_app in Heq.
    cbn in Heq. lia.
  - exfalso. destruct (wl_wf_cons w1 r1 Hw1) as [Hwd1 _].
    pose proof (wl_word_pos w1 Hwd1).
    apply (f_equal length) in Heq. rewrite wl_body_cons length_app in Heq.
    cbn in Heq. lia.
  - rewrite !wl_body_cons in Heq.
    destruct (wl_wf_cons w1 r1 Hw1) as [[_ Ha1] Hr1].
    destruct (wl_wf_cons w2 r2 Hw2) as [[_ Ha2] Hr2].
    destruct (wl_split_pred wl_alnum w1 (wl_tail r1) w2 (wl_tail r2)
                Ha1 Ha2 (wl_tail_head_not_alnum r1)
                (wl_tail_head_not_alnum r2) Heq) as [-> Hr].
    by rewrite (wl_tail_inj r1 r2 Hr1 Hr2 Hr).
Qed.

(* THE READING THE WIRE GIVES.  Two lines followed by two remainders make
   the same wire only if they are the same line AND the same remainder --
   so a session's rounds can each carry their OWN word list and the
   observer still knows which one each round typed. *)
Lemma wl_line_det (ws1 ws2 : list (list (bv 8))) (t1 t2 : list (bv 8)) :
  wl_wf ws1 -> wl_wf ws2 ->
  wl_line ws1 ++ t1 = wl_line ws2 ++ t2 -> ws1 = ws2 /\ t1 = t2.
Proof.
  intros Hw1 Hw2 Heq.
  rewrite /wl_line -!app_assoc /= in Heq.
  destruct (wl_split_pred wl_body_byte
              (wl_body ws1) (wl_nl :: t1) (wl_body ws2) (wl_nl :: t2)
              (wl_body_bytes ws1 Hw1) (wl_body_bytes ws2 Hw2)
              (wl_nl_head_not_body t1) (wl_nl_head_not_body t2) Heq)
    as [Hb Ht].
  split; [exact (wl_body_inj ws1 ws2 Hw1 Hw2 Hb) | by injection Ht].
Qed.

(* the plain injectivity, for a consumer that has no remainder *)
Lemma wl_line_inj (ws1 ws2 : list (list (bv 8))) :
  wl_wf ws1 -> wl_wf ws2 -> wl_line ws1 = wl_line ws2 -> ws1 = ws2.
Proof.
  intros Hw1 Hw2 Heq.
  destruct (wl_line_det ws1 ws2 [] [] Hw1 Hw2 ltac:(by rewrite !Heq))
    as [H _].
  exact H.
Qed.

(* THE FORM THE DISCIPLINE SPENDS.  A session claim compares what the
   model says the wire holds against a PREFIX of the real wire, so the
   reading has to survive a prefix: the line is still determined, and the
   remainder is still comparable.  It is [wl_line_det] with the prefix's
   witness folded into the first remainder. *)
Lemma wl_line_prefix_det (ws1 ws2 : list (list (bv 8)))
    (t1 t2 : list (bv 8)) :
  wl_wf ws1 -> wl_wf ws2 ->
  wl_line ws1 ++ t1 `prefix_of` wl_line ws2 ++ t2 ->
  ws1 = ws2 /\ t1 `prefix_of` t2.
Proof.
  intros Hw1 Hw2 [k Hk]. rewrite -app_assoc in Hk.
  destruct (wl_line_det ws1 ws2 (t1 ++ k) t2 Hw1 Hw2 (eq_sym Hk))
    as [-> Ht].
  split; [reflexivity | by exists k].
Qed.

(* ...and the bare one: a line that is a prefix of a WIRE opening with a
   line is that line.  This is what says the observer reads the typed
   words off the wire without knowing them in advance. *)
Lemma wl_line_of_wire (ws1 ws2 : list (list (bv 8))) (t : list (bv 8)) :
  wl_wf ws1 -> wl_wf ws2 ->
  wl_line ws1 `prefix_of` wl_line ws2 ++ t -> ws1 = ws2.
Proof.
  intros Hw1 Hw2 Hp.
  destruct (wl_line_prefix_det ws1 ws2 [] t Hw1 Hw2
              ltac:(by rewrite app_nil_r)) as [H _].
  exact H.
Qed.

(* ANTI-VACUITY: the encoding is not degenerate -- the blank is load
   bearing, so one two-letter word and two one-letter words are different
   lines, and the reading above tells them apart. *)
Definition wl_demo_a : bv 8 := Z_to_bv 8 97%Z.
Definition wl_demo_b : bv 8 := Z_to_bv 8 98%Z.

Lemma wl_demo_wf1 : wl_wf [[wl_demo_a; wl_demo_b]].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_demo_wf2 : wl_wf [[wl_demo_a]; [wl_demo_b]].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_demo_distinct :
  wl_line [[wl_demo_a; wl_demo_b]] <> wl_line [[wl_demo_a]; [wl_demo_b]].
Proof. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ===================================================================== *)
(*  S6  A SESSION'S INPUT: A SEQUENCE OF LINES, EACH ITS OWN             *)
(* ===================================================================== *)

(* What a console session types is not one line repeated: it is a SEQUENCE
   of lines, each with its own words.  [wl_lines] is that input, and the
   laws below are what a discipline spends instead of dividing the wire by
   a fixed line length -- which is only meaningful when every round is the
   same size. *)
Definition wl_lines (wss : list (list (list (bv 8)))) : list (bv 8) :=
  concat (wl_line <$> wss).

Definition wl_seq_wf (wss : list (list (list (bv 8)))) : Prop :=
  Forall wl_wf wss.

Lemma wl_lines_nil : wl_lines [] = [].
Proof. reflexivity. Qed.

Lemma wl_lines_cons (ws : list (list (bv 8)))
    (r : list (list (list (bv 8)))) :
  wl_lines (ws :: r) = wl_line ws ++ wl_lines r.
Proof. reflexivity. Qed.

Lemma wl_lines_app (u v : list (list (list (bv 8)))) :
  wl_lines (u ++ v) = wl_lines u ++ wl_lines v.
Proof. by rewrite /wl_lines fmap_app concat_app. Qed.

Lemma wl_seq_wf_cons (ws : list (list (bv 8)))
    (r : list (list (list (bv 8)))) :
  wl_seq_wf (ws :: r) -> wl_wf ws /\ wl_seq_wf r.
Proof. rewrite /wl_seq_wf. apply Forall_cons_1. Qed.

(* every line carries its newline, so a nonempty sequence is nonempty *)
Lemma wl_lines_pos (ws : list (list (bv 8)))
    (r : list (list (list (bv 8)))) :
  0 < length (wl_lines (ws :: r)).
Proof.
  rewrite wl_lines_cons length_app. pose proof (wl_line_pos ws). lia.
Qed.

(* THE LAW THAT REPLACES THE DIVISION.  With one fixed line, which round a
   wire position falls in is [position / line length].  With a line per
   round that quotient is meaningless -- and it does not need replacing by
   another formula, because the ROUNDS THEMSELVES are already determined:
   a session whose input is a prefix of another's typed a prefix of the
   same lines.  So the round decomposition is read off the wire, never
   computed from a length. *)
Lemma wl_lines_prefix_det (wss1 wss2 : list (list (list (bv 8)))) :
  wl_seq_wf wss1 -> wl_seq_wf wss2 ->
  wl_lines wss1 `prefix_of` wl_lines wss2 -> wss1 `prefix_of` wss2.
Proof.
  revert wss2. induction wss1 as [| w1 r1 IH]; intros wss2 H1 H2 Hp.
  - apply prefix_nil.
  - destruct wss2 as [| w2 r2].
    + exfalso. rewrite wl_lines_nil in Hp.
      pose proof (prefix_length _ _ Hp) as Hl.
      pose proof (wl_lines_pos w1 r1) as Hpos.
      change (length (@nil (bv 8))) with 0%nat in Hl. lia.
    + destruct (wl_seq_wf_cons w1 r1 H1) as [Hw1 Hr1].
      destruct (wl_seq_wf_cons w2 r2 H2) as [Hw2 Hr2].
      rewrite !wl_lines_cons in Hp.
      destruct (wl_line_prefix_det w1 w2 (wl_lines r1) (wl_lines r2)
                  Hw1 Hw2 Hp) as [-> Hrest].
      apply prefix_cons, (IH r2 Hr1 Hr2 Hrest).
Qed.

Lemma wl_lines_inj (wss1 wss2 : list (list (list (bv 8)))) :
  wl_seq_wf wss1 -> wl_seq_wf wss2 ->
  wl_lines wss1 = wl_lines wss2 -> wss1 = wss2.
Proof.
  intros H1 H2 Heq.
  apply (anti_symm prefix);
    [ apply (wl_lines_prefix_det _ _ H1 H2); by rewrite Heq
    | apply (wl_lines_prefix_det _ _ H2 H1); by rewrite Heq ].
Qed.
