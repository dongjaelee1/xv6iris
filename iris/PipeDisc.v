(* PipeDisc.v -- THE PIPELINE APPLICATION'S PURE MODEL: the lines the user
   may type ([echo w1 .. wn] and [echo w1 .. wn | cat]), the alternative
   each round may take, and the console transcript the session calls for.
   Iris-free, over [EchoDisc]/[LineWords], so the claim can be read -- and
   refuted -- without opening the logic.

   Design of record: claude-notes/design/app-pipe.md section 1.  Worklist
   claude-notes/projects/app-pipe.md, lane PIPE-MODEL.

   WHAT THIS FILE IS.  [EchoDisc] models a session in which every round is
   one echo line.  Here a round is one of TWO line shapes, and the pipeline
   shape's round is run by THREE processes (the shell's runcmd child, echo
   at the pipe's write end and cat at its read end), so its console
   continuation has alternatives the echo line has not: the two exec
   diagnostics, EVERY BYTE-WISE INTERLEAVING of the two when both execs
   fail, and sh's own [pipe]/[fork] panics in the runcmd child.  Nothing
   survives the round -- a pipe dies with its era -- so the session
   function threads NO state and is [EchoDisc.sess] with a richer
   alternative type ([sessp]), read through an injective [nat] encoding so
   that the stage's [cs_auth]/[cs_lb] machinery is reused verbatim.
   Upstream's [FileDisc] is the shape this file copies, file section for
   file section; it is NOT imported (the two models share no statement).

   THE OBSERVER STILL CANNOT SEE WHICH ALTERNATIVE RAN, and does not need
   to: at [echo fork | cat] the good run prints "fork\n$ ", which is also
   what sh's [fork1] panic in the runcmd child prints.  So the determinacy
   theorem [sessp_prefix_det] -- the twin of [EchoOutPure.sess_prefix_det],
   which is what the stage spends -- concludes an equality of BYTES and
   never of indices.  Its engine is one observation, not a table: every
   alternative's own output is a '$'-free run followed by the prompt,
   except the echo line's alternative 3 (the MAIN loop's [fork1] panic),
   which kills the shell and re-enters init's prologue.

   WHERE THIS FILE DEPARTS FROM design section 1, each departure reported
   in claude-notes/projects/app-pipe.md under Findings:

   - [parse_pline] inverts [line_body] (the body [LineWords.bodies_of]
     cuts), NOT [line_bytes] (which carries the closing newline the cut
     has already stripped).  The brief's
     [parse_pline (line_body (line_bytes l)) = Some l] is not even
     well-typed; the law that holds is [parse_pline_body] below, and
     [line_bytes l = line_body l ++ [wl_nl]] is kept as its own equation.
     This is [FileDisc]'s first departure, verbatim.
   - [palt_ok] admits NO prologue-re-entering alternative at an [LPipe]
     line ([palt_ok_pipe_no_panic] below), while design section 1's own
     prose says "[LPipe] lines reach [alt_panic] exactly as [LEcho] lines
     do".  The model as written is therefore INCOMPLETE at a reachable
     behaviour of the machine -- sh's MAIN-loop [fork1] failing on the
     round whose line is a pipeline line.  Landed as designed and
     reported; the one-line fix is [palt_ok (LPipe _) (PEcho 3) := True].
   - [pcont_shape] gives only "a '$'-free run, then the prompt".
     [FileDisc.cont_shape]'s stronger shape -- the run's ONLY newline, if
     any, is its last byte -- is FALSE at [PBoth sel]
     ([pcont_both_no_nl_shape] below): a merge of the two diagnostics
     carries TWO newlines.  The stronger shape is landed for the [LEcho]
     lines alone ([pcont_shape_nl]), which is exactly where the
     determinacy proof needs it, because a panic alternative forces an
     [LEcho] line ([palt_panic_LEcho]).
   - [merge]'s inverse law wants a STOPPING merge, not a skipping one:
     with "a [true] at an exhausted [d1] consumes the selector and
     produces nothing" the law [merge_take] is false (see the comment at
     [merge]).  Landed stopping, which makes [merge_take] and hence
     [merge_prefix] unconditional.
   - [pipe_phi] takes the history alone, as [FileDisc.file_phi] does; the
     [gstate] argument [AppEcho.echo_phi] carries is the record's, and
     lane PIPE-STAGE adds it. *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [obs_wire Uart0], [cycles_of] *)
Require Import LineWords.        (* the word line and the parser *)
Require Import EchoDisc.         (* the console discipline this one extends *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  SMALL LIST AND PREFIX FACTS                                        *)
(*                                                                        *)
(*  [FileDisc] section 0's list, re-proved under its own names so that     *)
(*  neither model imports the other.                                       *)
(* ====================================================================== *)

Lemma pd_prefix_lookup {A} (u v : list A) (i : A) (n : nat) :
  u `prefix_of` v -> u !! n = Some i -> v !! n = Some i.
Proof using. intros Hp Hu. exact (prefix_lookup_Some u v n i Hu Hp). Qed.

Lemma pd_Forall_drop {A} (P : A -> Prop) (n : nat) (l : list A) :
  Forall P l -> Forall P (drop n l).
Proof using.
  intro HF. apply Forall_forall. intros x Hx.
  apply elem_of_list_lookup in Hx as [i Hi]. rewrite lookup_drop in Hi.
  exact (Forall_lookup_1 _ _ _ _ HF Hi).
Qed.

Lemma pd_lookup_total_drop {A} `{!Inhabited A} (n i : nat) (l : list A) :
  drop n l !!! i = l !!! (n + i).
Proof using. by rewrite !list_lookup_total_alt lookup_drop. Qed.

Lemma pd_take_S {A} `{!Inhabited A} (n : nat) (l : list A) :
  (S n <= length l)%nat -> take (S n) l = l !!! 0%nat :: take n (drop 1 l).
Proof using.
  destruct l as [| a l]; [cbn [length]; lia |].
  intros _. cbn [take drop]. by rewrite list_lookup_total_alt /=.
Qed.

Lemma pd_lta_take_eq {A} `{!Inhabited A} (l l' : list A) (q j : nat) :
  take q l' = take q l -> (j < q)%nat -> l' !!! j = l !!! j.
Proof using.
  intros Heq Hj.
  assert (H1 : l' !! j = take q l' !! j)
    by (symmetry; rewrite lookup_take; [done | lia]).
  assert (H2 : l !! j = take q l !! j)
    by (symmetry; rewrite lookup_take; [done | lia]).
  by rewrite !list_lookup_total_alt H1 H2 Heq.
Qed.

Lemma pd_app4 {A} (a c s t : list A) (n : A) :
  ((a ++ n :: c) ++ s) ++ t = a ++ n :: (c ++ (s ++ t)).
Proof using. by rewrite -!app_assoc. Qed.

Lemma pd_cmp_at {A} (l1 l2 : list A) (i : nat) (x y : A) :
  (l1 `prefix_of` l2 \/ l2 `prefix_of` l1) ->
  l1 !! i = Some x -> l2 !! i = Some y -> x = y.
Proof using.
  intros [Hp | Hp] H1 H2.
  - rewrite (pd_prefix_lookup _ _ _ _ Hp H1) in H2. by injection H2.
  - rewrite (pd_prefix_lookup _ _ _ _ Hp H2) in H1. by injection H1.
Qed.

Lemma pd_prefix_eq {A} (u v : list A) :
  u `prefix_of` v -> (length v <= length u)%nat -> u = v.
Proof using.
  intros [k ->] Hl. rewrite length_app in Hl.
  assert (Hk : k = []) by (destruct k; [reflexivity | cbn [length] in Hl; lia]).
  subst k. by rewrite app_nil_r.
Qed.

(* ====================================================================== *)
(*  1.  THE LINES THE USER MAY TYPE                                        *)
(* ====================================================================== *)

(* sh's lexer sees '|' as a symbol token; the pipeline is CANONICAL -- one
   blank each side, and the right-hand command is the single word [cat]
   with NO argument, so cat reads its standard input.  That is the shape
   the sh walk (design section 5.1) is stated at. *)
Definition suf_pipecat : list (bv 8) := sb " | cat"%string.

Inductive pline :=
  | LEcho (ws : list (list (bv 8)))
  | LPipe (ws : list (list (bv 8))).

Global Instance pline_eq_dec : EqDecision pline.
Proof using. solve_decision. Defined.
Global Instance pline_inhabited : Inhabited pline := populate (LEcho []).

Definition pline_ws (l : pline) : list (list (bv 8)) :=
  match l with LEcho ws => ws | LPipe ws => ws end.

(* THE BODY the console cut keeps, and the LINE the user typed: the body
   and the newline [gets] stops at.  [line_bytes (LEcho ws)] is
   [LineWords.wl_line ws] on the nose. *)
Definition line_body (l : pline) : list (bv 8) :=
  match l with
  | LEcho ws => wl_body ws
  | LPipe ws => wl_body ws ++ suf_pipecat
  end.

Definition line_bytes (l : pline) : list (bv 8) := line_body l ++ [wl_nl].

Lemma line_bytes_echo ws : line_bytes (LEcho ws) = wl_line ws.
Proof using. reflexivity. Qed.

Lemma line_bytes_body l : line_bytes l = line_body l ++ [wl_nl].
Proof using. reflexivity. Qed.

Definition pline_ok (l : pline) : Prop :=
  match l with
  | LEcho ws => line_ok ws
  | LPipe ws => line_ok ws /\ (length (line_bytes (LPipe ws)) < line_max)%nat
  end.

Global Instance pline_ok_dec l : Decision (pline_ok l).
Proof using. destruct l; rewrite /pline_ok; apply _. Defined.

Lemma pline_ok_ws l : pline_ok l -> line_ok (pline_ws l).
Proof using. destruct l as [ws | ws]; [exact id | by intros [H _]]. Qed.

(* ---- the pipe symbol, and the bytes a line body may carry ------------ *)

Definition wl_bar : bv 8 := Z_to_bv 8 124%Z.

(* the partial line the user is in the middle of.  '|' is not a
   [wl_body_byte] and the line [echo hi | cat] passes through the input
   [echo hi |], so the pipeline application's D3 admits it. *)
Definition pbody_byte (b : bv 8) : Prop := wl_body_byte b \/ b = wl_bar.

Global Instance pbody_byte_dec b : Decision (pbody_byte b).
Proof using. rewrite /pbody_byte. apply _. Defined.

Lemma pbody_byte_of_body b : wl_body_byte b -> pbody_byte b.
Proof using. by left. Qed.

Lemma suf_pipecat_len : length suf_pipecat = 6%nat.
Proof using. by vm_compute. Qed.

Lemma suf_pipecat_bytes : Forall pbody_byte suf_pipecat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma wl_bar_not_body : ~ wl_body_byte wl_bar.
Proof using.
  rewrite /wl_body_byte /wl_alnum /wl_bar. intros [H | H].
  - assert (Hv : bv_unsigned (Z_to_bv 8 124%Z) = 124%Z) by (by vm_compute). lia.
  - apply (f_equal bv_unsigned) in H. rewrite wl_sp_val in H.
    assert (Hv : bv_unsigned (Z_to_bv 8 124%Z) = 124%Z) by (by vm_compute). lia.
Qed.

Lemma suf_pipecat_bar : wl_bar ∈ suf_pipecat.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- THE PARSER ------------------------------------------------------ *)

Definition strip_pipecat (b : list (bv 8)) : option (list (bv 8)) :=
  if decide (suf_pipecat `suffix_of` b)
  then Some (take (length b - length suf_pipecat) b) else None.

Lemma strip_pipecat_app c : strip_pipecat (c ++ suf_pipecat) = Some c.
Proof using.
  rewrite /strip_pipecat decide_True; [| by exists c].
  rewrite length_app.
  replace (length c + length suf_pipecat - length suf_pipecat)%nat
    with (length c) by lia.
  by rewrite take_app_length.
Qed.

Lemma strip_pipecat_Some b c : strip_pipecat b = Some c -> b = c ++ suf_pipecat.
Proof using.
  intros Hc. destruct (decide (suf_pipecat `suffix_of` b)) as [[k ->] | Hn].
  - rewrite (strip_pipecat_app k) in Hc. by injection Hc as <-.
  - rewrite /strip_pipecat decide_False in Hc; [discriminate | exact Hn].
Qed.

Lemma strip_pipecat_None b c : strip_pipecat b = None -> b <> c ++ suf_pipecat.
Proof using. intros H ->. by rewrite strip_pipecat_app in H. Qed.

(* THE PARSE of one body.  It answers [Some] only for an ADMISSIBLE line,
   so [is_Some (parse_pline b)] IS the content half of the discipline at
   that body; and what it answers determines the body
   ([line_body_parse]). *)
Definition parse_pline (b : list (bv 8)) : option pline :=
  match strip_pipecat b with
  | Some c =>
      if decide (body_ok c /\ (S (length b) < line_max)%nat)
      then Some (LPipe (wl_words c)) else None
  | None => if decide (body_ok b) then Some (LEcho (wl_words b)) else None
  end.

Definition pline_of (b : list (bv 8)) : pline :=
  default inhabitant (parse_pline b).

(* the lines of a body list, in order *)
Definition plines_of (I : list (bv 8)) : list pline := pline_of <$> bodies_of I.

Lemma parse_pline_ok b l : parse_pline b = Some l -> pline_ok l.
Proof using.
  rewrite /parse_pline. destruct (strip_pipecat b) as [c |] eqn:Hs.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [[Hbody Hok] Hlen]. rewrite /pline_ok. split.
    + exact Hok.
    + pose proof (strip_pipecat_Some b c Hs) as Hbc.
      rewrite Hbc length_app in Hlen.
      rewrite /line_bytes /line_body !length_app Hbody.
      cbn [length] in Hlen |- *. lia.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [Hbody Hok]. exact Hok.
Qed.

Lemma line_body_parse b l : parse_pline b = Some l -> b = line_body l.
Proof using.
  rewrite /parse_pline. destruct (strip_pipecat b) as [c |] eqn:Hs.
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [[Hbody _] _]. rewrite /line_body Hbody.
    exact (strip_pipecat_Some b c Hs).
  - case_decide as Hb; [| discriminate]. intros [= <-].
    destruct Hb as [Hbody _]. by rewrite /line_body Hbody.
Qed.

(* ...AND THE LINE'S OWN BYTES, which is the form the shell's read link
   hands back: what the user typed is the body plus its newline. *)
Lemma line_bytes_parse b l :
  parse_pline b = Some l -> line_bytes l = b ++ [wl_nl].
Proof using. intro H. by rewrite /line_bytes -(line_body_parse b l H). Qed.

(* ---- ...AND ITS INVERSE ---------------------------------------------- *)

Lemma body_no_pipecat ws (c : list (bv 8)) :
  line_ok ws -> wl_body ws <> c ++ suf_pipecat.
Proof using.
  intros Hok Heq.
  pose proof (wl_body_bytes ws (line_ok_wf _ Hok)) as Hfb.
  rewrite Heq in Hfb. apply Forall_app in Hfb as [_ Hsuf].
  exact (wl_bar_not_body
           (proj1 (Forall_forall _ _) Hsuf wl_bar suf_pipecat_bar)).
Qed.

Lemma parse_pline_body l : pline_ok l -> parse_pline (line_body l) = Some l.
Proof using.
  destruct l as [ws | ws].
  - (* LEcho *)
    intro Hok. rewrite /line_body /parse_pline.
    destruct (strip_pipecat (wl_body ws)) as [c |] eqn:Hs.
    { exfalso. exact (body_no_pipecat ws c Hok (strip_pipecat_Some _ _ Hs)). }
    rewrite decide_True; last first.
    { rewrite /body_ok (wl_words_body ws (line_ok_wf _ Hok)).
      split; [reflexivity | exact Hok]. }
    by rewrite (wl_words_body ws (line_ok_wf _ Hok)).
  - (* LPipe *)
    intros [Hok Hlen]. rewrite /line_body /parse_pline.
    rewrite strip_pipecat_app decide_True; last first.
    { split.
      - rewrite /body_ok (wl_words_body ws (line_ok_wf _ Hok)).
        split; [reflexivity | exact Hok].
      - rewrite /line_bytes /line_body !length_app in Hlen.
        cbn [length] in Hlen. rewrite length_app. lia. }
    by rewrite (wl_words_body ws (line_ok_wf _ Hok)).
Qed.

Lemma pline_of_body l : pline_ok l -> pline_of (line_body l) = l.
Proof using. intro H. by rewrite /pline_of (parse_pline_body l H). Qed.

(* ---- D3 FOR THE PIPELINE APPLICATION --------------------------------- *)

Definition pbody_ok (b : list (bv 8)) : Prop := is_Some (parse_pline b).

Global Instance pbody_ok_dec b : Decision (pbody_ok b).
Proof using. rewrite /pbody_ok. apply _. Defined.

Lemma pbody_ok_line b :
  pbody_ok b -> pline_ok (pline_of b) /\ b = line_body (pline_of b).
Proof using.
  intros [l Hl]. rewrite /pline_of Hl /=.
  split; [exact (parse_pline_ok b l Hl) | exact (line_body_parse b l Hl)].
Qed.

Lemma pbody_ok_of l : pline_ok l -> pbody_ok (line_body l).
Proof using. intro H. exists l. exact (parse_pline_body l H). Qed.

Lemma pbody_ok_bytes b : pbody_ok b -> Forall pbody_byte b.
Proof using.
  intro Hb. destruct (pbody_ok_line b Hb) as [Hok Heq]. rewrite Heq.
  destruct (pline_of b) as [ws | ws]; rewrite /line_body.
  - apply Forall_impl with (P := wl_body_byte);
      [exact (wl_body_bytes ws (line_ok_wf _ Hok)) | exact pbody_byte_of_body].
  - apply Forall_app. split; [| exact suf_pipecat_bytes].
    destruct Hok as [Hok _].
    apply Forall_impl with (P := wl_body_byte);
      [exact (wl_body_bytes ws (line_ok_wf _ Hok)) | exact pbody_byte_of_body].
Qed.

Lemma pbody_ok_short b : pbody_ok b -> (S (length b) < line_max)%nat.
Proof using.
  intro Hb. destruct (pbody_ok_line b Hb) as [Hok Heq]. rewrite Heq.
  destruct (pline_of b) as [ws | ws].
  - pose proof (line_ok_len ws Hok) as Hl.
    rewrite wl_line_length in Hl. rewrite /line_body. lia.
  - destruct Hok as [_ Hl].
    rewrite /line_bytes /line_body length_app in Hl. cbn [length] in Hl.
    rewrite /line_body. lia.
Qed.

(* D3: every COMPLETE body parses to an admissible line, and the partial
   line is body bytes -- '|' included -- short enough that its newline
   still fits [getcmd]'s buffer. *)
Definition disc_input_p (I : list (bv 8)) : Prop :=
  Forall pbody_ok (bodies_of I)
  /\ Forall pbody_byte (rest_of I)
  /\ (S (length (rest_of I)) < line_max)%nat.

Global Instance disc_input_p_dec I : Decision (disc_input_p I).
Proof using. rewrite /disc_input_p. apply _. Defined.

Lemma disc_input_p_nil : disc_input_p [].
Proof using.
  rewrite /disc_input_p bodies_of_nil rest_of_nil /line_max.
  split; [constructor |]. split; [constructor | cbn [length]; lia].
Qed.

Lemma disc_input_p_snoc I b : disc_input_p (I ++ [b]) -> disc_input_p I.
Proof using.
  intros (Hb & Hr & Hs). destruct (decide (b = wl_nl)) as [-> | Hne].
  - rewrite bodies_of_snoc_nl in Hb.
    apply Forall_app in Hb as [Hb1 Hb2]. rewrite Forall_singleton in Hb2.
    split; [exact Hb1 |]. split; [exact (pbody_ok_bytes _ Hb2) |].
    exact (pbody_ok_short _ Hb2).
  - rewrite (bodies_of_snoc_other I b Hne) in Hb.
    rewrite (rest_of_snoc_other I b Hne) in Hr, Hs.
    apply Forall_app in Hr as [Hr1 _].
    split; [exact Hb |]. split; [exact Hr1 |].
    rewrite (length_app (rest_of I) [b]) in Hs. cbn [length] in Hs. lia.
Qed.

Lemma disc_input_p_prefix I I' :
  I `prefix_of` I' -> disc_input_p I' -> disc_input_p I.
Proof using.
  intros [k ->]. induction k as [| b k IH] using rev_ind; intro Hd.
  - by rewrite app_nil_r in Hd.
  - apply IH. rewrite app_assoc in Hd. exact (disc_input_p_snoc _ _ Hd).
Qed.

Lemma disc_input_p_body I i b :
  disc_input_p I -> bodies_of I !! i = Some b -> pbody_ok b.
Proof using. intros (Hb & _ & _) Hi. exact (Forall_lookup_1 _ _ _ _ Hb Hi). Qed.

Lemma disc_input_p_line I i b :
  disc_input_p I -> bodies_of I !! i = Some b ->
  pline_ok (pline_of b) /\ b = line_body (pline_of b).
Proof using.
  intros Hd Hi. exact (pbody_ok_line b (disc_input_p_body I i b Hd Hi)).
Qed.

Lemma disc_input_p_rest_short I :
  disc_input_p I -> (S (length (rest_of I)) < line_max)%nat.
Proof using. by intros (_ & _ & H). Qed.

Lemma disc_input_p_at I i :
  disc_input_p I -> (i < nlines I)%nat ->
  pline_ok (pline_of (bodies_of I !!! i))
  /\ bodies_of I !!! i = line_body (pline_of (bodies_of I !!! i)).
Proof using.
  intros Hd Hi. rewrite /nlines in Hi.
  destruct (lookup_lt_is_Some_2 (bodies_of I) i Hi) as [b Hb].
  rewrite (list_lookup_total_correct _ _ _ Hb).
  exact (pbody_ok_line b (disc_input_p_body I i b Hd Hb)).
Qed.

(* ---- AN ECHO-DISCIPLINED INPUT IS PIPE-DISCIPLINED -------------------- *)
(* [EchoDisc]'s lines are this model's [LEcho] lines, so nothing about the
   echo application's discipline is weakened or restated. *)

Lemma parse_pline_echo b : body_ok b -> parse_pline b = Some (LEcho (wl_words b)).
Proof using.
  intro Hb. rewrite /parse_pline.
  destruct (strip_pipecat b) as [c |] eqn:Hs.
  { exfalso. pose proof (strip_pipecat_Some b c Hs) as Hbc.
    pose proof (body_ok_bytes b Hb) as Hfb.
    rewrite Hbc in Hfb. apply Forall_app in Hfb as [_ Hsuf].
    exact (wl_bar_not_body
             (proj1 (Forall_forall _ _) Hsuf wl_bar suf_pipecat_bar)). }
  rewrite decide_True; [reflexivity | exact Hb].
Qed.

Lemma pline_of_echo b : body_ok b -> pline_of b = LEcho (wl_words b).
Proof using. intro H. by rewrite /pline_of (parse_pline_echo b H). Qed.

Lemma pbody_ok_of_body b : body_ok b -> pbody_ok b.
Proof using.
  intro H. exists (LEcho (wl_words b)). exact (parse_pline_echo b H).
Qed.

Lemma disc_input_p_of_disc_input I : disc_input I -> disc_input_p I.
Proof using.
  intros (Hb & Hr & Hs). split.
  { apply Forall_impl with (P := body_ok); [exact Hb | exact pbody_ok_of_body]. }
  split; [| exact Hs].
  apply Forall_impl with (P := wl_body_byte);
    [exact Hr | exact pbody_byte_of_body].
Qed.

(* ====================================================================== *)
(*  2.  THE DIAGNOSTICS, AND THE MERGE OF TWO OF THEM                      *)
(* ====================================================================== *)

(* SH'S DIAGNOSTICS ARE WORD LINES, as [EchoDisc.dg_exec] is.  The two exec
   diagnostics are ONE [fprintf(2, "exec %s failed\n", argv[0])]
   (user/sh.c:80) at the two commands of the pipeline; the two panics are
   [panic("pipe")] (user/sh.c:47) and [panic("fork")] (user/sh.c:194),
   whose printer is [fprintf(2, "%s\n", s)] (user/sh.c:181).  Stating them
   in the word vocabulary is what makes their collision with an echoed
   line a statement the parse settles. *)
Definition dg_exec_cat : list (list (bv 8)) :=
  [ sb "exec"%string; sb "cat"%string; sb "failed"%string ].
Definition dg_pipe : list (list (bv 8)) := [ sb "pipe"%string ].

Lemma dg_exec_cat_line :
  wl_line dg_exec_cat = sb "exec cat failed"%string ++ nlb.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma dg_pipe_line : wl_line dg_pipe = sb "pipe"%string ++ nlb.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* THE TWO DIAGNOSTICS THAT CAN COLLIDE ON THE WIRE, as raw bytes: the
   left child's (echo could not be exec'd) and the right child's (cat
   could not be).  [dg_execL] is [EchoDisc.dg_exec]'s line on the nose,
   which is why an [LEcho] round and an [LPipe] round print the SAME bytes
   when their left exec fails. *)
Definition dg_execL : list (bv 8) := wl_line dg_exec.
Definition dg_execR : list (bv 8) := wl_line dg_exec_cat.

Lemma dg_execL_string : dg_execL = sb "exec echo failed"%string ++ nlb.
Proof using. exact dg_exec_line. Qed.

Lemma dg_execR_string : dg_execR = sb "exec cat failed"%string ++ nlb.
Proof using. exact dg_exec_cat_line. Qed.

Lemma dg_execL_len : length dg_execL = 17%nat.
Proof using. by vm_compute. Qed.

Lemma dg_execR_len : length dg_execR = 16%nat.
Proof using. by vm_compute. Qed.

(* ---- THE ROUND'S FOUR CONSTANT CONTINUATIONS ------------------------- *)

Definition alt_execL : list (bv 8) := dg_execL ++ u_prompt.
Definition alt_execR : list (bv 8) := dg_execR ++ u_prompt.
Definition alt_pipe  : list (bv 8) := wl_line dg_pipe ++ u_prompt.
Definition alt_forkc : list (bv 8) := wl_line dg_fork ++ u_prompt.

(* [alt_execL] IS the echo application's exec alternative: one [fprintf],
   one format, one argument. *)
Lemma alt_execL_echo : alt_execL = alt_execfail.
Proof using. reflexivity. Qed.

Lemma alt_execL_string :
  alt_execL = sb "exec echo failed"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma alt_execR_string :
  alt_execR = sb "exec cat failed"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma alt_pipe_string :
  alt_pipe = sb "pipe"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* THE RUNCMD CHILD'S FORK PANIC ENDS IN THE PROMPT and the MAIN LOOP'S
   DOES NOT.  [panic] in the runcmd child exits the CHILD, the parent
   shell's [wait(0)] returns and it prints the next prompt
   ([alt_forkc]); the main loop's own [fork1] kills the SHELL, init reaps
   it and re-enters the prologue ([EchoDisc.alt_panic], with no prompt).
   The two are the same four bytes followed by different things, which is
   exactly why the model needs both. *)
Lemma alt_forkc_panic : alt_forkc = alt_panic ++ u_prompt.
Proof using. reflexivity. Qed.

Lemma alt_forkc_string :
  alt_forkc = sb "fork"%string ++ nlb ++ sb "$ "%string.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* ---- '$' IS THE ONE BYTE ONLY THE PROMPT CARRIES --------------------- *)

Definition nodollar (b : bv 8) : Prop := bv_unsigned b <> 36%Z.

Global Instance nodollar_dec b : Decision (nodollar b).
Proof using. rewrite /nodollar. apply _. Defined.

Lemma body_byte_nodollar b : wl_body_byte b -> nodollar b.
Proof using.
  rewrite /wl_body_byte /wl_alnum /nodollar. intros [[H | [H | H]] | ->].
  - lia.
  - lia.
  - lia.
  - rewrite wl_sp_val. lia.
Qed.

Lemma nl_nodollar : nodollar wl_nl.
Proof using. rewrite /nodollar wl_nl_val. lia. Qed.

(* '$' is not a byte of any word line, and a word line's ONE newline is
   its last byte.  Both readings come off [LineWords] at once. *)
Lemma pd_wl_line_shape ws :
  wl_wf ws ->
  Forall nodollar (wl_line ws)
  /\ exists v, wl_nl ∉ v /\ wl_line ws = v ++ [wl_nl].
Proof using.
  intro Hwf. split.
  - apply Forall_forall. intros b Hb.
    pose proof (wl_line_byte_val ws b Hwf Hb) as Hv. rewrite /nodollar. lia.
  - exists (wl_body ws). split; [exact (wl_body_nonl ws Hwf) | reflexivity].
Qed.

Lemma pd_wl_line_shape' ws :
  wl_wf ws ->
  Forall nodollar (wl_line ws)
  /\ (wl_nl ∉ wl_line ws
      \/ exists v, wl_nl ∉ v /\ wl_line ws = v ++ [wl_nl]).
Proof using.
  intro H. destruct (pd_wl_line_shape ws H) as [H1 H2].
  split; [exact H1 | by right].
Qed.

(* ---- THE MERGE: TWO WRITERS ON ONE WIRE ------------------------------ *)

(* HOW MANY BYTES OF THE LEFT DIAGNOSTIC AN INTERLEAVING SELECTS *)
Fixpoint count_true (sel : list bool) : nat :=
  match sel with
  | [] => 0%nat
  | true :: s => S (count_true s)
  | false :: s => count_true s
  end.

Lemma count_true_le sel : (count_true sel <= length sel)%nat.
Proof using.
  induction sel as [| [|] s IH]; cbn [count_true length]; lia.
Qed.

Lemma count_true_app s1 s2 :
  count_true (s1 ++ s2) = (count_true s1 + count_true s2)%nat.
Proof using.
  induction s1 as [| [|] s IH]; cbn [app count_true]; lia.
Qed.

Lemma count_true_replicate_true n : count_true (replicate n true) = n.
Proof using. induction n as [| n IH]; cbn [replicate count_true]; lia. Qed.

Lemma count_true_replicate_false n : count_true (replicate n false) = 0%nat.
Proof using. induction n as [| n IH]; cbn [replicate count_true]; lia. Qed.

(* THE INTERLEAVING [sel] PUTS ON THE WIRE, one byte per selector entry:
   [true] takes the next byte of [d1], [false] the next byte of [d2].

   IT STOPS AT AN EXHAUSTED SIDE and does not skip.  The skipping variant
   ("a [true] at an empty [d1] consumes the selector and produces
   nothing") makes [merge_take] FALSE -- at [sel = [true; false]],
   [d1 = []], [d2 = [x]] it gives [merge sel d1 d2 = [x]] while
   [merge (take 1 sel) d1 d2 = []], so a prefix of a merge would not be a
   merge of a prefix of the selector, and [merge_prefix] (which design
   section 4.3 spends) would need side conditions.  Stopping makes both
   laws UNCONDITIONAL, and at every [sel] the model admits ([palt_ok]'s
   length and count conditions) the two definitions agree. *)
Fixpoint merge (sel : list bool) (d1 d2 : list (bv 8)) : list (bv 8) :=
  match sel with
  | [] => []
  | true :: s =>
      match d1 with [] => [] | b :: d1' => b :: merge s d1' d2 end
  | false :: s =>
      match d2 with [] => [] | b :: d2' => b :: merge s d1 d2' end
  end.

Lemma merge_nil_sel d1 d2 : merge [] d1 d2 = [].
Proof using. reflexivity. Qed.

Lemma merge_true_cons s b d1 d2 :
  merge (true :: s) (b :: d1) d2 = b :: merge s d1 d2.
Proof using. reflexivity. Qed.

Lemma merge_false_cons s d1 b d2 :
  merge (false :: s) d1 (b :: d2) = b :: merge s d1 d2.
Proof using. reflexivity. Qed.

Lemma merge_true_nil s d2 : merge (true :: s) [] d2 = [].
Proof using. reflexivity. Qed.

Lemma merge_false_nil s d1 : merge (false :: s) d1 [] = [].
Proof using. reflexivity. Qed.

(* the merge is as long as the selector, once both sides have the bytes *)
Lemma merge_length sel d1 d2 :
  (count_true sel <= length d1)%nat ->
  (length sel - count_true sel <= length d2)%nat ->
  length (merge sel d1 d2) = length sel.
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 H1 H2; [done | |].
  - pose proof (count_true_le s) as Hcl.
    cbn [count_true length] in H1, H2.
    destruct d1 as [| b d1']; [cbn [length] in H1; lia |].
    rewrite merge_true_cons. cbn [length]. rewrite IH; [lia | |];
      cbn [length] in H1 |- *; lia.
  - pose proof (count_true_le s) as Hcl.
    cbn [count_true length] in H1, H2.
    destruct d2 as [| b d2']; [cbn [length] in H2; lia |].
    rewrite merge_false_cons. cbn [length]. rewrite IH; [lia | |];
      cbn [length] in H2 |- *; lia.
Qed.

(* A PREFIX OF A MERGE IS A MERGE OF A PREFIX OF THE SELECTOR.  This is
   the engine of the inverse law, and it is unconditional. *)
Lemma merge_take sel d1 d2 k :
  take k (merge sel d1 d2) = merge (take k sel) d1 d2.
Proof using.
  revert d1 d2 k. induction sel as [| [|] s IH]; intros d1 d2 k.
  - by rewrite !take_nil.
  - destruct k as [| k']; [by rewrite !take_0 |].
    destruct d1 as [| b d1']; [by cbn |].
    cbn. by rewrite IH.
  - destruct k as [| k']; [by rewrite !take_0 |].
    destruct d2 as [| b d2']; [by cbn |].
    cbn. by rewrite IH.
Qed.

(* ...and the merge reads only as much of each side as the selector asks
   for, which turns a prefix of the selector into a pair of cursors *)
Lemma merge_take_lr sel d1 d2 c1 c2 :
  (count_true sel <= c1)%nat -> (length sel - count_true sel <= c2)%nat ->
  merge sel (take c1 d1) (take c2 d2) = merge sel d1 d2.
Proof using.
  revert d1 d2 c1 c2. induction sel as [| [|] s IH]; intros d1 d2 c1 c2 H1 H2;
    [done | |].
  - pose proof (count_true_le s) as Hcl.
    cbn [count_true length] in H1, H2.
    destruct c1 as [| c1']; [lia |].
    destruct d1 as [| b d1']; [by rewrite take_nil |].
    rewrite (_ : take (S c1') (b :: d1') = b :: take c1' d1');
      [| reflexivity].
    rewrite !merge_true_cons. f_equal. apply IH; lia.
  - pose proof (count_true_le s) as Hcl.
    cbn [count_true length] in H1, H2.
    destruct c2 as [| c2']; [lia |].
    destruct d2 as [| b d2']; [by rewrite take_nil |].
    rewrite (_ : take (S c2') (b :: d2') = b :: take c2' d2');
      [| reflexivity].
    rewrite !merge_false_cons. f_equal. apply IH; lia.
Qed.

(* DESIGN SECTION 4.3'S LAW: a prefix of a merge is a merge of prefixes --
   the two writers' cursors are [c1] and [c2] and the interleaving so far
   is [sel'], a prefix of the round's. *)
Lemma merge_prefix_take (sel : list bool) (d1 d2 : list (bv 8)) (k : nat) :
  take k (merge sel d1 d2)
  = merge (take k sel) (take (count_true (take k sel)) d1)
          (take (length (take k sel) - count_true (take k sel))%nat d2).
Proof using.
  rewrite merge_take. symmetry. apply merge_take_lr; lia.
Qed.

Lemma merge_prefix (sel : list bool) (d1 d2 p : list (bv 8)) :
  p `prefix_of` merge sel d1 d2 ->
  exists (sel' : list bool) (c1 c2 : nat),
    p = merge sel' (take c1 d1) (take c2 d2) /\ sel' `prefix_of` sel.
Proof using.
  intros [z Hz].
  exists (take (length p) sel), (count_true (take (length p) sel)),
         (length (take (length p) sel)
          - count_true (take (length p) sel))%nat.
  split; [| apply prefix_take].
  rewrite -merge_prefix_take Hz. by rewrite take_app_length.
Qed.

(* NEITHER DIAGNOSTIC CARRIES A '$', so no interleaving of them does --
   which is what puts every [PBoth] round under the same reading as every
   other non-panic round (section 4). *)
Lemma merge_nodollar sel d1 d2 :
  Forall nodollar d1 -> Forall nodollar d2 ->
  Forall nodollar (merge sel d1 d2).
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 H1 H2;
    [constructor | |].
  - destruct d1 as [| b d1']; [by constructor |].
    apply Forall_cons_1 in H1 as [Hb H1].
    rewrite merge_true_cons. apply Forall_cons. split; [exact Hb | by apply IH].
  - destruct d2 as [| b d2']; [by constructor |].
    apply Forall_cons_1 in H2 as [Hb H2].
    rewrite merge_false_cons. apply Forall_cons. split; [exact Hb | by apply IH].
Qed.

Lemma dg_execL_nodollar : Forall nodollar dg_execL.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma dg_execR_nodollar : Forall nodollar dg_execR.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

Lemma merge_no_dollar sel : Forall nodollar (merge sel dg_execL dg_execR).
Proof using.
  apply merge_nodollar; [exact dg_execL_nodollar | exact dg_execR_nodollar].
Qed.

(* the first byte of a merge is the first byte of one of the two sides --
   the one reading the negative witness (section 8) spends *)
Lemma merge_head sel d1 d2 (b : bv 8) :
  merge sel d1 d2 !! 0%nat = Some b ->
  d1 !! 0%nat = Some b \/ d2 !! 0%nat = Some b.
Proof using.
  destruct sel as [| [|] s]; [discriminate | |].
  - destruct d1 as [| c d1']; [discriminate |].
    rewrite merge_true_cons. cbn. intros [= <-]. by left.
  - destruct d2 as [| c d2']; [discriminate |].
    rewrite merge_false_cons. cbn. intros [= <-]. by right.
Qed.

(* ====================================================================== *)
(*  3.  THE ROUND'S ALTERNATIVES                                           *)
(* ====================================================================== *)

(* ONE ALTERNATIVE DECIDES A ROUND: what the console shows.  [PEcho] is the
   echo application's four, unchanged; the rest are the pipeline line's,
   and design section 1 is the table:

     PEcho a     the echo application's four ([EchoDisc.line_alts_of])
     PRan        wl_line (drop 1 ws) ++ "$ "       the line, then the prompt
     PExecL      "exec echo failed\n$ "            left exec failed; cat
                                                   printed nothing (EOF at
                                                   an empty pipe)
     PExecR      "exec cat failed\n$ "             right exec failed; echo's
                                                   bytes went into the pipe
                                                   and stayed there
     PBoth sel   merge sel dg_execL dg_execR ++ "$ "
                                                   both failed; [sel] is the
                                                   byte-wise interleaving
     PPipe       "pipe\n$ "                        pipe(2) failed; sh's panic
                                                   in the runcmd CHILD
     PFork       "fork\n$ "                        a fork1 failed in the
                                                   runcmd child (either one)
     PSilent     "$ "                              a child died before
                                                   printing

   [PPipe] AND [PFork] END IN THE PROMPT, not in a fresh prologue: [runcmd]
   runs in the shell's forked child, so [panic] there exits the CHILD, the
   parent's [wait(0)] returns and it prints the next prompt.  The MAIN
   loop's own [fork1] panic -- which does kill the shell and re-enter
   init's prologue -- is [EchoDisc]'s alternative 3, i.e. [PEcho 3]. *)
Inductive palt :=
  | PEcho (a : nat)
  | PRan
  | PExecL
  | PExecR
  | PBoth (sel : list bool)
  | PPipe
  | PFork
  | PSilent.

Global Instance palt_eq_dec : EqDecision palt.
Proof using. solve_decision. Defined.
Global Instance palt_inhabited : Inhabited palt := populate (PEcho 0%nat).

(* THE ENCODING the stage's [cs_auth]/[cs_lb] machinery carries: an
   injective [nat] code, and the echo application's four are THEIR OWN
   INDEX, so an echo line's rounds are LITERALLY today's ([sessp_sess]).
   [PBoth sel] is encoded WITH [sel] -- one alternative per interleaving --
   so the transcript stays a function of [(ps, cs, I)]. *)
Definition palt_code (a : palt) : nat :=
  match a with
  | PEcho k => if decide (k < 4)%nat then k else (10 + 3 * (k - 4))%nat
  | PRan => 4%nat | PExecL => 5%nat | PExecR => 6%nat
  | PPipe => 7%nat | PFork => 8%nat | PSilent => 9%nat
  | PBoth sel => (11 + 3 * encode_nat sel)%nat
  end.

Definition palt_of (n : nat) : palt :=
  if decide (n < 4)%nat then PEcho n
  else if decide (n = 4%nat) then PRan
  else if decide (n = 5%nat) then PExecL
  else if decide (n = 6%nat) then PExecR
  else if decide (n = 7%nat) then PPipe
  else if decide (n = 8%nat) then PFork
  else if decide (n = 9%nat) then PSilent
  else if decide (Nat.modulo n 3 = 2%nat)
       then PBoth (default [] (decode_nat (Nat.div (n - 11) 3)))
       else PEcho (4 + Nat.div (n - 10) 3)%nat.

Lemma pd_mod3_add (a m : nat) : Nat.modulo (a + 3 * m) 3 = Nat.modulo a 3.
Proof using.
  replace (a + 3 * m)%nat with (a + m * 3)%nat by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma pd_div3_mul (m : nat) : Nat.div (3 * m) 3 = m.
Proof using.
  replace (3 * m)%nat with (m * 3)%nat by lia.
  rewrite Nat.div_mul; [reflexivity | lia].
Qed.

Lemma palt_of_code a : palt_of (palt_code a) = a.
Proof using.
  destruct a as [k | | | | sel | | |]; try (by vm_compute).
  - (* PEcho: its own index below 4, and out of every other code's way
       above it *)
    rewrite /palt_code. case_decide as Hk.
    + rewrite /palt_of decide_True; [reflexivity | exact Hk].
    + assert (Hm : Nat.modulo (10 + 3 * (k - 4)) 3 = 1%nat)
        by (rewrite pd_mod3_add; by vm_compute).
      rewrite /palt_of.
      do 7 (case_decide; [exfalso; lia |]).
      case_decide; [exfalso; congruence |].
      replace (10 + 3 * (k - 4) - 10)%nat with (3 * (k - 4))%nat by lia.
      rewrite pd_div3_mul. f_equal. lia.
  - (* PBoth: the interleaving through the countable encoding *)
    assert (Hm : Nat.modulo (11 + 3 * encode_nat sel) 3 = 2%nat)
      by (rewrite pd_mod3_add; by vm_compute).
    rewrite /palt_code /palt_of.
    do 7 (case_decide; [exfalso; lia |]).
    case_decide; [| exfalso; congruence].
    replace (11 + 3 * encode_nat sel - 11)%nat with (3 * encode_nat sel)%nat
      by lia.
    rewrite pd_div3_mul decode_encode_nat. reflexivity.
Qed.

(* ...hence the code is INJECTIVE, which is all the stage asks of it *)
Lemma palt_code_inj (a b : palt) : palt_code a = palt_code b -> a = b.
Proof using.
  intro H. by rewrite -(palt_of_code a) -(palt_of_code b) H.
Qed.

Lemma palt_of_lt4 n : (n < 4)%nat -> palt_of n = PEcho n.
Proof using. intro H. rewrite /palt_of decide_True; [reflexivity | exact H]. Qed.

Lemma palt_code_echo_lt4 k : (k < 4)%nat -> palt_code (PEcho k) = k.
Proof using.
  intro H. rewrite /palt_code decide_True; [reflexivity | exact H].
Qed.

(* THE PROLOGUE-RE-ENTERING ALTERNATIVE: the MAIN loop's [fork1] panicked,
   init reaped the SHELL and its outer loop opened a NEW prologue round.
   [PPipe] and [PFork] are NOT of this kind -- they panic in the runcmd
   child and the shell lives. *)
Definition palt_panic (a : palt) : bool :=
  match a with PEcho k => bool_decide (k = 3%nat) | _ => false end.

(* WHICH ALTERNATIVES A LINE SHAPE ADMITS, and [sel]'s shape: an
   interleaving names one byte per byte of the two diagnostics, and
   [count_true] many of them come from the left one. *)
Definition palt_ok (l : pline) (a : palt) : Prop :=
  match l with
  | LEcho _ => match a with PEcho k => (k < 4)%nat | _ => False end
  | LPipe _ =>
      match a with
      | PBoth sel =>
          length sel = (length dg_execL + length dg_execR)%nat
          /\ count_true sel = length dg_execL
      | PRan | PExecL | PExecR | PPipe | PFork | PSilent => True
      | PEcho _ => False
      end
  end.

Global Instance palt_ok_dec l a : Decision (palt_ok l a).
Proof using. destruct l, a; rewrite /palt_ok; apply _. Defined.

(* ---- THE HOLE IN DESIGN SECTION 1, STATED ---------------------------- *)

(* NO ALTERNATIVE A PIPELINE LINE ADMITS RE-ENTERS THE PROLOGUE.  Design
   section 1's prose says the echo application's [alt_panic] arm -- sh's
   MAIN-loop [fork1] failing, which kills the shell -- "is unchanged and
   [LPipe] lines reach it exactly as [LEcho] lines do (it is decided
   before the line is parsed)".  Its [palt] table says otherwise: [PEcho]
   is "LEcho lines only".  This lemma is the statement of the gap: the
   machine can put [alt_panic] and then a FRESH PROLOGUE on the wire in a
   round whose typed line is a pipeline line, and nothing this model
   admits at such a line prints that -- [PFork]'s continuation is
   [alt_panic ++ u_prompt], which differs from [alt_panic ++ pro_of _] at
   byte 5 whenever the prologue re-entered is init's banner.  The one-line
   repair is [palt_ok (LPipe _) (PEcho 3) := True]; it is NOT applied here,
   because a lane does not change the designer's definitions. *)
Lemma palt_ok_pipe_no_panic (ws : list (list (bv 8))) (a : palt) :
  palt_ok (LPipe ws) a -> palt_panic a = false.
Proof using. destruct a; by intros ?. Qed.

(* ...and the converse reading the determinacy proof spends: a panic
   alternative forces an ECHO line. *)
Lemma palt_panic_LEcho (l : pline) (a : palt) :
  palt_ok l a -> palt_panic a = true -> exists ws, l = LEcho ws.
Proof using.
  destruct l as [ws | ws]; intros Ha Hp; [by exists ws |].
  by rewrite (palt_ok_pipe_no_panic ws a Ha) in Hp.
Qed.

Lemma palt_ok_echo_lt4 ws c : palt_ok (LEcho ws) (palt_of c) -> (c < 4)%nat.
Proof using.
  rewrite /palt_of. case_decide as H4; [by intros _ |].
  do 6 (case_decide; [by intros [] |]).
  case_decide; [by intros [] | rewrite /palt_ok; lia].
Qed.

Lemma palt_panic_echo c :
  (c < 4)%nat -> palt_panic (palt_of c) = bool_decide (c = 3%nat).
Proof using. intro H. by rewrite (palt_of_lt4 c H). Qed.

(* ---- THE CONSOLE CONTINUATION OF A ROUND ----------------------------- *)

(* At [PEcho] it is [EchoDisc.line_alts_of] verbatim; at [PRan] it is
   [EchoDisc.line_alts_of]'s GOOD alternative, because cat copies. *)
Definition pcont (l : pline) (a : palt) : list (bv 8) :=
  match a with
  | PEcho k => line_alts_of (pline_ws l) !!! k
  | PRan => wl_line (drop 1 (pline_ws l)) ++ u_prompt
  | PExecL => alt_execL
  | PExecR => alt_execR
  | PBoth sel => merge sel dg_execL dg_execR ++ u_prompt
  | PPipe => alt_pipe
  | PFork => alt_forkc
  | PSilent => u_prompt
  end.

(* THE CHEAPNESS OF THE CLAIM, in one equation: a pipeline round that ran
   prints exactly what the echo line prints. *)
Lemma pcont_PRan_alt0 l : pcont l PRan = line_alts_of (pline_ws l) !!! 0%nat.
Proof using. reflexivity. Qed.

Lemma pcont_panic l a : palt_panic a = true -> pcont l a = alt_panic.
Proof using.
  destruct a; try discriminate.
  rewrite /palt_panic. intro Hk. apply bool_decide_eq_true in Hk as ->.
  exact (line_alts_of_3 (pline_ws l)).
Qed.

(* THE ENGINE OF THE DETERMINACY ARGUMENT: a non-panic alternative prints
   a '$'-free run and then sh's prompt.  There is no third shape, at
   either line.  (Design section 1 asked whether EVERY continuation
   satisfies the shape: every one but [PEcho 3] does -- [PPipe] and
   [PFork] end in the prompt too -- and [PEcho 3] is the one the prologue
   follows.) *)
Lemma pcont_shape (l : pline) (a : palt) :
  pline_ok l -> palt_ok l a -> palt_panic a = false ->
  exists u, pcont l a = u ++ u_prompt /\ Forall nodollar u.
Proof using.
  intros Hl Ha Hp.
  assert (Hex : wl_wf dg_exec)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hec : wl_wf dg_exec_cat)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hpi : wl_wf dg_pipe)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hfk : wl_wf dg_fork)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hpr : exists u : list (bv 8), u_prompt = u ++ u_prompt
                  /\ Forall nodollar u).
  { exists []. split; [reflexivity | constructor]. }
  destruct a; rewrite /pcont.
  - (* PEcho: the echo application's four, minus the panic one *)
    rewrite /palt_panic in Hp. apply bool_decide_eq_false in Hp.
    rewrite /palt_ok in Ha. destruct l as [ws | ws]; [| done].
    destruct a as [| [| [| [| a]]]]; [| | | done | exfalso; lia].
    + exists (wl_line (drop 1 ws)). rewrite line_alts_of_0.
      split; [reflexivity |].
      apply (pd_wl_line_shape (drop 1 ws)).
      apply pd_Forall_drop, (line_ok_wf _ Hl).
    + exists (wl_line dg_exec). rewrite line_alts_of_1 /alt_execfail.
      split; [reflexivity |]. apply (pd_wl_line_shape dg_exec Hex).
    + rewrite line_alts_of_2 /alt_prompt. exact Hpr.
  - (* PRan: the line, minus the command name, then the prompt *)
    exists (wl_line (drop 1 (pline_ws l))). split; [reflexivity |].
    apply (pd_wl_line_shape (drop 1 (pline_ws l))).
    apply pd_Forall_drop, (line_ok_wf _ (pline_ok_ws l Hl)).
  - exists dg_execL. rewrite /alt_execL. split; [reflexivity |].
    rewrite /dg_execL. apply (pd_wl_line_shape dg_exec Hex).
  - exists dg_execR. rewrite /alt_execR. split; [reflexivity |].
    rewrite /dg_execR. apply (pd_wl_line_shape dg_exec_cat Hec).
  - exists (merge sel dg_execL dg_execR). split; [reflexivity |].
    exact (merge_no_dollar sel).
  - exists (wl_line dg_pipe). rewrite /alt_pipe. split; [reflexivity |].
    apply (pd_wl_line_shape dg_pipe Hpi).
  - exists (wl_line dg_fork). rewrite /alt_forkc. split; [reflexivity |].
    apply (pd_wl_line_shape dg_fork Hfk).
  - exact Hpr.
Qed.

(* ...AND, AT AN ECHO LINE, THE STRONGER SHAPE: the run's only newline, if
   any, is its LAST byte.  [FileDisc.cont_shape] gives that at every
   alternative; HERE IT IS FALSE at [PBoth]
   ([pcont_both_no_nl_shape] below), so it is stated where it is true --
   which is exactly where the determinacy proof needs it, because the
   comparison that spends it puts a panic alternative on one side, and a
   panic alternative forces an echo line ([palt_panic_LEcho]). *)
Lemma pcont_shape_nl (ws : list (list (bv 8))) (a : palt) :
  pline_ok (LEcho ws) -> palt_ok (LEcho ws) a -> palt_panic a = false ->
  exists u, pcont (LEcho ws) a = u ++ u_prompt
            /\ Forall nodollar u
            /\ (wl_nl ∉ u \/ exists v, wl_nl ∉ v /\ u = v ++ [wl_nl]).
Proof using.
  intros Hl Ha Hp.
  assert (Hex : wl_wf dg_exec)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  rewrite /palt_panic in Hp.
  rewrite /palt_ok in Ha. destruct a as [k | | | | | | |]; [| done..].
  apply bool_decide_eq_false in Hp.
  rewrite /pcont /pline_ws.
  destruct k as [| [| [| [| k]]]]; [| | | done | exfalso; lia].
  - exists (wl_line (drop 1 ws)). rewrite line_alts_of_0.
    split; [reflexivity |].
    apply (pd_wl_line_shape' (drop 1 ws)).
    apply pd_Forall_drop, (line_ok_wf _ Hl).
  - exists (wl_line dg_exec). rewrite line_alts_of_1 /alt_execfail.
    split; [reflexivity |]. exact (pd_wl_line_shape' dg_exec Hex).
  - exists []. rewrite line_alts_of_2 /alt_prompt.
    split; [reflexivity |]. split; [constructor |].
    left. apply not_elem_of_nil.
Qed.

(* ---- WHY THE STRONGER SHAPE IS FALSE AT [PBoth] ---------------------- *)

(* the interleaving that prints the left diagnostic and then the right one *)
Definition sel_LR : list bool :=
  replicate (length dg_execL) true ++ replicate (length dg_execR) false.

Lemma sel_LR_ok ws : palt_ok (LPipe ws) (PBoth sel_LR).
Proof using.
  rewrite /palt_ok /sel_LR. split.
  - rewrite length_app !length_replicate. reflexivity.
  - rewrite count_true_app count_true_replicate_true
            count_true_replicate_false. lia.
Qed.

Lemma merge_sel_LR : merge sel_LR dg_execL dg_execR = dg_execL ++ dg_execR.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* TWO NEWLINES, so the run is neither newline-free nor closed by its one
   newline: [FileDisc.cont_shape]'s disjunct is refuted at this [sel]. *)
Lemma pcont_both_no_nl_shape :
  ~ (wl_nl ∉ (dg_execL ++ dg_execR)
     \/ exists v, wl_nl ∉ v /\ dg_execL ++ dg_execR = v ++ [wl_nl]).
Proof using.
  assert (Hin : wl_nl ∈ dg_execL ++ dg_execR)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hat : (dg_execL ++ dg_execR) !! 16%nat = Some wl_nl)
    by (apply (bool_decide_unpack _); vm_compute; exact I).
  assert (Hlen : length (dg_execL ++ dg_execR) = 33%nat)
    by (by vm_compute).
  intros [Hno | (v & Hv & Heq)]; [by destruct (Hno Hin) |].
  assert (Hvl : length v = 32%nat)
    by (apply (f_equal length) in Heq;
        rewrite Hlen length_app in Heq; cbn [length] in Heq; lia).
  rewrite Heq in Hat.
  rewrite (lookup_app_l v [wl_nl] 16%nat ltac:(lia)) in Hat.
  exact (Hv (elem_of_list_lookup_2 v 16%nat wl_nl Hat)).
Qed.
