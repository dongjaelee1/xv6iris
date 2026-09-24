(* PipeBothPure.v -- THE `PBoth` BLOCK, PURE: the running selector, the
   bytes it has put on the wire, the stage reading that admits a block
   whose alternative is NOT YET FILED, and the one place a `PBoth` code is
   built.

   Design of record: claude-notes/design/app-pipe.md sections 4.3 and 4.3b,
   lane PIPE-2W, deliverables 2 (the family's pure shapes) and 3 (the pure
   readings).  Nothing here is Iris; nothing here is edited from a landed
   file: [PipeOutPure]'s [pending_at_p] and its whole cone stay byte for
   byte what they were, and the both-arm is a SECOND reading beside them
   ([pboth_at] below), used by the claim's second arm only.

   WHAT THE BLOCK IS.  Both children of sh's runcmd print
   [fprintf(2, "exec %s failed\n", argv[0])] one byte per [write(2)], so
   the wire shows SOME interleaving of [PipeDisc.dg_execL] (17 bytes) and
   [PipeDisc.dg_execR] (16).  The model's alternative is
   [PipeDisc.PBoth sel] and its continuation is
   [pmerge sel dg_execL dg_execR ++ u_prompt]; the running block is the
   same [pmerge] at the selector SO FAR ([pend_both] below), which is a
   prefix of it ([pend_both_mono]).

   THE ONE THING THAT MAKES THE ROUND DIFFERENT FROM EVERY OTHER ROUND in
   the echo/file/pipe stages: the round's entry in [cs] CANNOT be filed at
   the block's first byte, because [sel] is decided byte by byte by two
   concurrent writers and a [mono_list] entry is immutable.  So during the
   block the choice list is ONE SHORT ([pboth_at]'s third conjunct) and the
   block's bytes are read off the selector instead of off [cs] -- and the
   alternative is filed at the PROMPT, which is the only moment at which
   the code exists ([wr_both_exit]).

   WHY A LEDGER IS NEEDED AT ALL, at the statement: [pend_both] is NOT
   INJECTIVE ([pend_both_not_inj] below, a [vm_compute] witness), because
   the two diagnostics share the prefix "exec ".  So the running selector
   cannot be read back off the block's bytes, and a claim that carried only
   "the block so far is SOME merge prefix" could not tell a writer which
   byte comes next.  That is the whole reason design section 4.3b's second
   ledger exists, and it is proved here rather than asserted. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import PipeOutPure.
(* as in PipeDisc / PipeOutPure: a pure file does not inherit ssreflect's
   [rewrite] from the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  1.  THE RUNNING SELECTOR AND ITS BLOCK                                 *)
(* ====================================================================== *)

(* the block the two writers have put on the wire under the selector so far *)
Definition pend_both (sel : list bool) : list (bv 8) :=
  pmerge sel dg_execL dg_execR.

(* how long a COMPLETE selector is: one bit per byte of the two
   diagnostics.  [palt_ok (LPipe ws) (PBoth sel)] is exactly
   [length sel = psel_len /\ count_true sel = length dg_execL]. *)
Definition psel_len : nat := (length dg_execL + length dg_execR)%nat.

Lemma psel_len_val : psel_len = 33%nat.
Proof using. rewrite /psel_len dg_execL_len dg_execR_len. reflexivity. Qed.

(* A RUNNING SELECTOR is one neither side has overdrawn. *)
Definition sel_wf (sel : list bool) : Prop :=
  (count_true sel <= length dg_execL)%nat
  /\ (length sel - count_true sel <= length dg_execR)%nat.

Lemma sel_wf_nil : sel_wf [].
Proof using. rewrite /sel_wf. cbn [count_true length]. lia. Qed.

Lemma sel_wf_prefix (sel sel' : list bool) :
  sel `prefix_of` sel' -> sel_wf sel' -> sel_wf sel.
Proof using.
  intros [z ->] [H1 H2]. rewrite count_true_app length_app in H1, H2.
  pose proof (count_true_le z). rewrite /sel_wf. lia.
Qed.

Lemma pend_both_nil : pend_both [] = [].
Proof using. rewrite /pend_both. apply pmerge_nil_sel. Qed.

Lemma pend_both_length (sel : list bool) :
  sel_wf sel -> length (pend_both sel) = length sel.
Proof using. intros [H1 H2]. by apply pmerge_length. Qed.

(* A PREFIX OF THE SELECTOR IS A PREFIX OF THE BLOCK -- design section
   4.3's [pmerge_prefix] read forwards, which is what makes the running
   block a prefix of the alternative that is filed at the prompt. *)
Lemma pend_both_take (sel : list bool) (k : nat) :
  take k (pend_both sel) = pend_both (take k sel).
Proof using. rewrite /pend_both. apply pmerge_take. Qed.

Lemma pend_both_mono (sel sel' : list bool) :
  sel `prefix_of` sel' -> pend_both sel `prefix_of` pend_both sel'.
Proof using.
  intros Hp.
  assert (Hs : take (length sel) sel' = sel)
    by (destruct Hp as [z ->]; by rewrite take_app_length).
  assert (H2 : pend_both sel = take (length sel) (pend_both sel'))
    by (rewrite pend_both_take Hs; reflexivity).
  rewrite H2. apply prefix_take.
Qed.

(* THE TWO BYTE STEPS.  They are GUARDED, and the guard is not an
   artefact: [pmerge] STOPS at the exhausted side (PIPE-MODEL's ruling,
   which is what makes [pmerge_prefix] unconditional), so once a selector
   has overdrawn one diagnostic every later bit adds NOTHING and the step
   is false.  The guard is exactly [sel_wf] at the two sides, which is what
   the writers' cursors carry anyway. *)
Lemma pmerge_snoc_true (sel : list bool) (d1 d2 : list (bv 8)) :
  (count_true sel <= length d1)%nat ->
  (length sel - count_true sel <= length d2)%nat ->
  pmerge (sel ++ [true]) d1 d2
  = pmerge sel d1 d2 ++ take 1 (drop (count_true sel) d1).
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 H1 H2.
  - cbn [app count_true]. rewrite pmerge_nil_sel app_nil_l drop_0.
    destruct d1 as [| b d1']; [reflexivity |].
    rewrite pmerge_true_cons pmerge_nil_sel. reflexivity.
  - cbn [app count_true] in H1, H2 |- *. destruct d1 as [| b d1'].
    + exfalso. cbn [length] in H1. lia.
    + rewrite !pmerge_true_cons. cbn [app]. f_equal. apply IH;
        [cbn [length] in H1; lia | cbn [length] in H2; lia].
  - cbn [app count_true length] in H1, H2 |- *. destruct d2 as [| b d2'].
    + exfalso. pose proof (count_true_le s). cbn [length] in H2. lia.
    + rewrite !pmerge_false_cons. cbn [app]. f_equal. apply IH;
        [exact H1 | pose proof (count_true_le s); cbn [length] in H2; lia].
Qed.

Lemma pmerge_snoc_false (sel : list bool) (d1 d2 : list (bv 8)) :
  (count_true sel <= length d1)%nat ->
  (length sel - count_true sel <= length d2)%nat ->
  pmerge (sel ++ [false]) d1 d2
  = pmerge sel d1 d2 ++ take 1 (drop (length sel - count_true sel)%nat d2).
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 H1 H2.
  - cbn [app length count_true]. rewrite Nat.sub_0_r.
    rewrite pmerge_nil_sel app_nil_l drop_0.
    destruct d2 as [| b d2']; [reflexivity |].
    rewrite pmerge_false_cons pmerge_nil_sel. reflexivity.
  - cbn [app count_true length] in H1, H2 |- *. destruct d1 as [| b d1'].
    + exfalso. cbn [length] in H1. lia.
    + rewrite !pmerge_true_cons. cbn [app]. f_equal.
      replace (S (length s) - S (count_true s))%nat
        with (length s - count_true s)%nat by lia.
      apply IH; [cbn [length] in H1; lia | lia].
  - cbn [app count_true length] in H1, H2 |- *. destruct d2 as [| b d2'].
    + exfalso. pose proof (count_true_le s). cbn [length] in H2. lia.
    + rewrite !pmerge_false_cons. cbn [app]. f_equal.
      replace (S (length s) - count_true s)%nat
        with (S (length s - count_true s))%nat
        by (pose proof (count_true_le s); lia).
      cbn [drop]. apply IH;
        [exact H1 | pose proof (count_true_le s); cbn [length] in H2; lia].
Qed.

Lemma pop_take1_drop_lookup {A} (l : list A) (i : nat) (x : A) :
  l !! i = Some x -> take 1 (drop i l) = [x].
Proof using.
  intros Hx.
  assert (Hd : drop i l !! 0%nat = Some x)
    by (rewrite lookup_drop Nat.add_0_r; exact Hx).
  destruct (drop i l) as [| y z]; [by rewrite lookup_nil in Hd |].
  cbn [lookup list_lookup] in Hd. injection Hd as <-. reflexivity.
Qed.

(* THE LEFT WRITER'S BYTE: [dg_execL !!! c1] at [c1 = count_true sel]. *)
Lemma pend_both_true (sel : list bool) (b : bv 8) :
  sel_wf sel ->
  dg_execL !! count_true sel = Some b ->
  pend_both (sel ++ [true]) = pend_both sel ++ [b].
Proof using.
  intros [H1 H2] Hb. rewrite /pend_both (pmerge_snoc_true sel _ _ H1 H2).
  by rewrite (pop_take1_drop_lookup dg_execL (count_true sel) b Hb).
Qed.

(* ...AND THE RIGHT WRITER'S, at [c2 = length sel - count_true sel]. *)
Lemma pend_both_false (sel : list bool) (b : bv 8) :
  sel_wf sel ->
  dg_execR !! (length sel - count_true sel)%nat = Some b ->
  pend_both (sel ++ [false]) = pend_both sel ++ [b].
Proof using.
  intros [H1 H2] Hb. rewrite /pend_both (pmerge_snoc_false sel _ _ H1 H2).
  by rewrite (pop_take1_drop_lookup dg_execR _ b Hb).
Qed.

(* NO BYTE OF A RUNNING BLOCK IS A '$' -- the fact that keeps an
   in-progress merge from ever looking like a COMPLETED round's block, and
   hence the fact that leaves [PipeDisc.sessp_prefix_det] (which compares
   completed rounds' codes) untouched by this whole file. *)
Lemma pend_both_nodollar (sel : list bool) : Forall nodollar (pend_both sel).
Proof using. rewrite /pend_both. apply pmerge_no_dollar. Qed.

(* A RUNNING SELECTOR ALWAYS COMPLETES: the block in progress is a prefix
   of a block the line ADMITS, which is what the claim's second arm hands
   to [good_out_p]. *)
Lemma sel_complete (sel : list bool) :
  sel_wf sel ->
  exists selF : list bool,
    sel `prefix_of` selF
    /\ length selF = psel_len
    /\ count_true selF = length dg_execL.
Proof using.
  intros [H1 H2]. pose proof (count_true_le sel) as Hle.
  rewrite dg_execL_len in H1. rewrite dg_execR_len in H2.
  exists (sel ++ replicate (17 - count_true sel) true
              ++ replicate (16 - (length sel - count_true sel)) false).
  split; [by eexists |].
  (* the two lengths are NUMBERS before any [length_app] runs: [dg_execL]
     is a [wl_line], so [length_app] would otherwise unfold
     [length dg_execL] into a sum whose association no longer matches the
     hypotheses' opaque [length dg_execL] *)
  rewrite /psel_len dg_execL_len dg_execR_len.
  rewrite !count_true_app !length_app !length_replicate
          count_true_replicate_true count_true_replicate_false.
  split; lia.
Qed.

(* ====================================================================== *)
(*  1a. WHY THE LEDGER EXISTS: [pend_both] IS NOT INJECTIVE               *)
(*                                                                        *)
(*  Both diagnostics open with the five bytes of `exec ', so the block     *)
(*  `exec e' is the merge of the LEFT one's first six bytes AND of one     *)
(*  left byte after the RIGHT one's first five -- two splits whose next    *)
(*  left byte differs (`c' of `echo' against `x' of `exec').  A claim that *)
(*  knew only that the block so far is SOME merge prefix could therefore   *)
(*  not decide which byte a writer at cursor [c1] is allowed to append,    *)
(*  which is exactly the hole design section 4.3b's second ledger fills.   *)
(* ====================================================================== *)

Definition sel_six_L : list bool := replicate 6 true.
Definition sel_six_R : list bool := [false; false; false; false; false; true].

Lemma pend_both_six_eq : pend_both sel_six_L = pend_both sel_six_R.
Proof using. vm_compute. reflexivity. Qed.

Lemma pend_both_six_len :
  length sel_six_L = 6%nat /\ length sel_six_R = 6%nat.
Proof using. by vm_compute. Qed.

Lemma pend_both_six_split :
  count_true sel_six_L = 6%nat /\ count_true sel_six_R = 1%nat.
Proof using. by vm_compute. Qed.

Lemma pend_both_not_inj :
  exists sel sel' : list bool,
    sel_wf sel /\ sel_wf sel'
    /\ pend_both sel = pend_both sel'
    /\ length sel = length sel'
    /\ dg_execL !!! count_true sel <> dg_execL !!! count_true sel'.
Proof using.
  exists sel_six_L, sel_six_R. split_and!.
  - rewrite /sel_wf /sel_six_L dg_execL_len dg_execR_len.
    rewrite count_true_replicate_true length_replicate. lia.
  - rewrite /sel_wf /sel_six_R dg_execL_len dg_execR_len.
    cbn [count_true length]. lia.
  - exact pend_both_six_eq.
  - by vm_compute.
  - rewrite /sel_six_L /sel_six_R. intro Hq.
    apply (f_equal bv_unsigned) in Hq. vm_compute in Hq. discriminate.
Qed.

(* ====================================================================== *)
(*  2.  THE STAGE READING THAT ADMITS AN UNFILED BLOCK                     *)
(* ====================================================================== *)

(* the round in progress is a PIPELINE line -- the only shape whose
   alternatives include [PBoth] *)
Definition pboth_line (I : list (bv 8)) : Prop :=
  exists ws, pline_of (bodies_of I !!! (nlines I - 1)%nat) = LPipe ws.

(* THE BOTH STATE.  [cs] is ONE SHORT (the round's alternative is not
   filed) and the block written so far is the running merge.  At
   [sel = []] this IS the ordinary block boundary ([pend_both [] = []]),
   which is what makes the entry into the arm at the block's first byte a
   step and not a jump. *)
Definition pboth_at (cs : list nat) (I : list (bv 8)) (w : list (bv 8))
    (sel : list bool) : Prop :=
  I <> []
  /\ rest_of I = []
  /\ length cs = (nlines I - 1)%nat
  /\ pboth_line I
  /\ sel_wf sel
  /\ w = pend_both sel.

Lemma pboth_at_nlines (cs : list nat) (I : list (bv 8)) (w : list (bv 8))
    (sel : list bool) :
  pboth_at cs I w sel -> (1 <= nlines I)%nat.
Proof using.
  intros (Hne & Hr & _ & _ & _ & _). exact (nlines_pos_of_rest_nil I Hne Hr).
Qed.

Lemma pboth_at_w_len (cs : list nat) (I : list (bv 8)) (w : list (bv 8))
    (sel : list bool) :
  pboth_at cs I w sel -> length w = length sel.
Proof using.
  intros (_ & _ & _ & _ & Hwf & ->). by apply pend_both_length.
Qed.

(* THE ROUND'S CODE, BUILT: the ONE place in the tree where a [PBoth] code
   is ever made.  [palt_ok] comes out of the selector's length and its
   count of trues, both of which the writers' cursors carry. *)
Lemma palt_ok_both (ws : list (list (bv 8))) (sel : list bool) :
  length sel = psel_len -> count_true sel = length dg_execL ->
  palt_ok (LPipe ws) (PBoth sel).
Proof using. intros Hl Hc. rewrite /palt_ok /psel_len in Hl |- *. by split. Qed.

Lemma pcont_both (ws : list (list (bv 8))) (sel : list bool) :
  pcont (LPipe ws) (PBoth sel) = pend_both sel ++ u_prompt.
Proof using. reflexivity. Qed.

(* the filed entry read back: [palt_at (cs ++ [palt_code (PBoth sel)])] at
   the round's own index *)
Lemma palt_at_filed (cs : list nat) (i : nat) (a : palt) :
  length cs = i -> palt_at (cs ++ [palt_code a]) i = a.
Proof using.
  intros <-. rewrite /palt_at list_lookup_total_alt lookup_app_r; [| lia].
  rewrite Nat.sub_diag. exact (palt_of_code a).
Qed.

(* ...and at a RAW code, which is what the round's four exits file *)
Lemma palt_at_snoc (cs : list nat) (i : nat) (a : nat) :
  length cs = i -> palt_at (cs ++ [a]) i = palt_of a.
Proof using.
  intros <-. rewrite /palt_at list_lookup_total_alt lookup_app_r; [| lia].
  by rewrite Nat.sub_diag.
Qed.

(* the pending reading AT THE FILED ENTRY is the alternative's continuation:
   the block the running merge is a prefix of *)
Lemma pending_at_p_filed (ps cs : list nat) (I : list (bv 8))
    (ws : list (list (bv 8))) (sel : list bool) :
  I <> [] -> rest_of I = [] ->
  length cs = (nlines I - 1)%nat ->
  pline_of (bodies_of I !!! (nlines I - 1)%nat) = LPipe ws ->
  pending_at_p ps (cs ++ [palt_code (PBoth sel)]) I
  = pend_both sel ++ u_prompt.
Proof using.
  intros Hne Hr Hq Hl. rewrite /pending_at_p.
  rewrite decide_False; [| exact Hne]. rewrite decide_True; [| exact Hr].
  rewrite /alt_cont_p (palt_at_filed cs (nlines I - 1)%nat (PBoth sel) Hq).
  rewrite Hl. cbn [palt_panic]. by rewrite app_nil_r.
Qed.

(* ====================================================================== *)
(*  3.  F4 AT THE BOTH ARM -- the claim's conclusion from an UNFILED block *)
(*                                                                        *)
(*  [PipeOutPure.good_out_p_of_stage] APPLIED, with the round's own entry  *)
(*  supplied as the WITNESS the theorem's existential wants: the block in  *)
(*  progress is a prefix of the alternative [PBoth selF], and [selF] is    *)
(*  any completion of the running selector ([sel_complete]).  So the       *)
(*  console claim holds at every byte of the merged diagnostic, WITHOUT    *)
(*  the round's code ever being filed.                                     *)
(* ====================================================================== *)

Lemma good_out_p_of_stage_both (ps cs : list nat)
    (E : list (list mobs * bv 8)) (w : list (bv 8)) (sel : list bool)
    (seg : list mobs) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  alts_pre_p (ins seg) cs ->
  E_disc_p E ->
  pro_pin_p ps cs (snd <$> E) ->
  pboth_at cs (snd <$> E) w sel ->
  obs_wire Uart0 seg `prefix_of` (D_p ps cs E ++ w) ->
  (snd <$> E) `prefix_of` ins seg ->
  good_out_p seg.
Proof using.
  intros Hps Hao HE Hpin Hboth Hwire Hinp.
  pose proof Hboth as (Hne & Hr & Hq & (ws & Hline) & Hwf & Hw).
  pose proof (nlines_pos_of_rest_nil _ Hne Hr) as Hpos.
  destruct (sel_complete sel Hwf) as (selF & HselF & HlenF & HcntF).
  set (a := palt_code (PBoth selF)).
  set (cs' := (cs ++ [a])%list).
  assert (Hcsp : cs `prefix_of` cs') by (rewrite /cs'; by eexists).
  assert (Hlen' : length cs' = nlines (snd <$> E))
    by (rewrite /cs' length_app Hq; cbn [length]; lia).
  (* the line at the round's index is the same line in the longer input *)
  assert (Hnl : (nlines (snd <$> E) <= nlines (ins seg))%nat)
    by (by apply nlines_prefix).
  assert (Hbod : bodies_of (ins seg) !!! (nlines (snd <$> E) - 1)%nat
                 = bodies_of (snd <$> E) !!! (nlines (snd <$> E) - 1)%nat).
  { destruct (bodies_of_prefix (snd <$> E) (ins seg) Hinp) as [z Hz].
    rewrite Hz !list_lookup_total_alt lookup_app_l;
      [reflexivity | rewrite /nlines in Hpos |- *; lia]. }
  (* the round's entry is admissible at the line *)
  assert (Hok : palt_ok (pline_of (bodies_of (ins seg) !!! length cs))
                  (palt_of a)).
  { rewrite Hq Hbod Hline /a (palt_of_code (PBoth selF)).
    exact (palt_ok_both ws selF HlenF HcntF). }
  assert (Hao' : alts_pre_p (ins seg) cs').
  { apply (alts_pre_p_snoc (ins seg) cs a Hao); [| exact Hok].
    rewrite Hq. rewrite /nlines in Hpos, Hnl |- *. lia. }
  (* the new entry is below every prologue index the stage reads *)
  assert (Hpin' : pro_pin_p ps cs' (snd <$> E)).
  { intros qq Hqq. rewrite /cs' pro_idx_p_app_le; [by apply Hpin |].
    rewrite (pop_nstarted_rest_nil _ Hr) in Hqq. rewrite Hq. lia. }
  (* ...so the transcript BEFORE this round does not move *)
  assert (HD : D_p ps cs' E = D_p ps cs E).
  { symmetry. apply (D_p_cs_prefix ps ps cs cs' E);
      [reflexivity | exact Hcsp | exact Hpin |].
    rewrite (pop_nlines_removelast _ Hr) Hq. lia. }
  apply (good_out_p_of_stage ps cs' E w seg Hps Hao').
  - rewrite (pop_nlines_removelast _ Hr) Hlen'. lia.
  - left. lia.
  - exact HE.
  - exact Hpin'.
  - rewrite /pending_p (pending_at_p_filed ps cs (snd <$> E) ws selF
                          Hne Hr Hq Hline).
    rewrite Hw. etrans; [exact (pend_both_mono sel selF HselF) |].
    by eexists.
  - by rewrite HD.
  - exact Hinp.
Qed.

(* ====================================================================== *)
(*  4.  THE FAMILY'S PURE SHAPE AND ITS THREE MOVES                        *)
(*                                                                        *)
(*  [PipeLinksLine]'s [wr_blk_t_p] one round over: what the two children   *)
(*  share while the block is unfiled, at TWO cursors instead of one.  The  *)
(*  Iris family of design section 4.3b ([pwc_both]) is this predicate with *)
(*  [turn], the three lower bounds and the selector's ledger beside it.    *)
(* ====================================================================== *)

Definition wr_both_p (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (sel : list bool) (c1 c2 : nat) : Prop :=
  I <> []
  /\ rest_of I = []
  /\ length cs = (nlines I - 1)%nat
  /\ pboth_line I
  /\ pro_pin_p ps cs I
  /\ P = length (proc_before_p ps cs I)
  /\ length sel = (c1 + c2)%nat
  /\ count_true sel = c1
  /\ (c1 <= length dg_execL)%nat
  /\ (c2 <= length dg_execR)%nat.

Lemma wr_both_p_sel_wf (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (sel : list bool) (c1 c2 : nat) :
  wr_both_p ps cs I P sel c1 c2 -> sel_wf sel.
Proof using.
  intros (_ & _ & _ & _ & _ & _ & Hl & Hc & H1 & H2). rewrite /sel_wf Hl Hc.
  split; lia.
Qed.

(* the shape the claim's arm reads, from the family's *)
Lemma wr_both_p_pboth_at (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (sel : list bool) (c1 c2 : nat) :
  wr_both_p ps cs I P sel c1 c2 -> pboth_at cs I (pend_both sel) sel.
Proof using.
  intros Hw. pose proof Hw as (Hne & Hr & Hq & Hl & _).
  rewrite /pboth_at. split_and!;
    [exact Hne | exact Hr | exact Hq | exact Hl
     | exact (wr_both_p_sel_wf _ _ _ _ _ _ _ Hw) | reflexivity].
Qed.

(* THE ENTRY: the round's block credential at its FIRST byte is the family
   at the empty selector, and the block it has written is empty. *)
Lemma wr_both_p_entry (ps cs : list nat) (I : list (bv 8)) :
  I <> [] -> rest_of I = [] ->
  length cs = (nlines I - 1)%nat ->
  pboth_line I ->
  pro_pin_p ps cs I ->
  wr_both_p ps cs I (length (proc_before_p ps cs I)) [] 0%nat 0%nat
  /\ pend_both [] = [].
Proof using.
  intros Hne Hr Hq Hl Hpin. split; [| exact pend_both_nil].
  rewrite /wr_both_p. split_and!; try done; cbn [count_true length]; lia.
Qed.

(* THE LEFT STEP: one byte of [dg_execL] at the left cursor, the selector
   one bit longer, the wire one byte longer -- and the byte is the block's
   LAST, at wire position [P + c1 + c2]. *)
Lemma wr_both_step_L (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (sel : list bool) (c1 c2 : nat) (b : bv 8) :
  wr_both_p ps cs I P sel c1 c2 ->
  dg_execL !! c1 = Some b ->
  wr_both_p ps cs I P (sel ++ [true]) (S c1) c2
  /\ pend_both (sel ++ [true]) = pend_both sel ++ [b]
  /\ length (pend_both (sel ++ [true])) = S (c1 + c2)%nat.
Proof using.
  intros Hw Hb. pose proof Hw as (Hne & Hr & Hq & Hl & Hpin & HP & Hlen & Hcnt
                                  & H1 & H2).
  pose proof (lookup_lt_Some _ _ _ Hb) as Hlt.
  assert (Hstep : pend_both (sel ++ [true]) = pend_both sel ++ [b]).
  { apply (pend_both_true sel b (wr_both_p_sel_wf _ _ _ _ _ _ _ Hw)).
    by rewrite Hcnt. }
  assert (Hw' : wr_both_p ps cs I P (sel ++ [true]) (S c1) c2).
  { rewrite /wr_both_p. split_and!;
      first [ done
            | rewrite length_app Hlen; cbn [length]; lia
            | rewrite count_true_app Hcnt; cbn [count_true]; lia
            | lia ]. }
  split_and!; [exact Hw' | exact Hstep |].
  rewrite (pend_both_length _ (wr_both_p_sel_wf _ _ _ _ _ _ _ Hw'))
          length_app Hlen. cbn [length]. lia.
Qed.

(* ...AND THE RIGHT STEP, at [dg_execR] and the right cursor. *)
Lemma wr_both_step_R (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (sel : list bool) (c1 c2 : nat) (b : bv 8) :
  wr_both_p ps cs I P sel c1 c2 ->
  dg_execR !! c2 = Some b ->
  wr_both_p ps cs I P (sel ++ [false]) c1 (S c2)
  /\ pend_both (sel ++ [false]) = pend_both sel ++ [b]
  /\ length (pend_both (sel ++ [false])) = S (c1 + c2)%nat.
Proof using.
  intros Hw Hb. pose proof Hw as (Hne & Hr & Hq & Hl & Hpin & HP & Hlen & Hcnt
                                  & H1 & H2).
  pose proof (lookup_lt_Some _ _ _ Hb) as Hlt.
  assert (Hstep : pend_both (sel ++ [false]) = pend_both sel ++ [b]).
  { apply (pend_both_false sel b (wr_both_p_sel_wf _ _ _ _ _ _ _ Hw)).
    by replace (length sel - count_true sel)%nat with c2 by lia. }
  assert (Hw' : wr_both_p ps cs I P (sel ++ [false]) c1 (S c2)).
  { rewrite /wr_both_p. split_and!;
      first [ done
            | rewrite length_app Hlen; cbn [length]; lia
            | rewrite count_true_app Hcnt; cbn [count_true]; lia
            | lia ]. }
  split_and!; [exact Hw' | exact Hstep |].
  rewrite (pend_both_length _ (wr_both_p_sel_wf _ _ _ _ _ _ _ Hw'))
          length_app Hlen. cbn [length]. lia.
Qed.

(* THE EXIT, at the prompt: both cursors at the end, the code BUILT, the
   round's entry filed, and the block the entry owes is the block the two
   writers wrote.  [pcont] of the filed alternative is the wire's bytes
   followed by the prompt, so sh's own two bytes close the block exactly as
   they do at every other alternative. *)
Lemma wr_both_exit (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (sel : list bool) :
  wr_both_p ps cs I P sel (length dg_execL) (length dg_execR) ->
  exists ws : list (list (bv 8)),
    pline_of (bodies_of I !!! (nlines I - 1)%nat) = LPipe ws
    /\ palt_ok (LPipe ws) (PBoth sel)
    /\ pcont (LPipe ws) (PBoth sel) = pend_both sel ++ u_prompt
    /\ pending_at_p ps (cs ++ [palt_code (PBoth sel)]) I
       = pend_both sel ++ u_prompt
    /\ length (pend_both sel) = psel_len.
Proof using.
  intros Hw. pose proof Hw as (Hne & Hr & Hq & (ws & Hline) & Hpin & HP
                               & Hlen & Hcnt & _ & _).
  assert (Hok : palt_ok (LPipe ws) (PBoth sel))
    by (apply palt_ok_both; [rewrite Hlen /psel_len; lia | exact Hcnt]).
  exists ws. split_and!.
  - exact Hline.
  - exact Hok.
  - exact (pcont_both ws sel).
  - exact (pending_at_p_filed ps cs I ws sel Hne Hr Hq Hline).
  - rewrite (pend_both_length _ (wr_both_p_sel_wf _ _ _ _ _ _ _ Hw)) Hlen.
    rewrite /psel_len. lia.
Qed.

(* ====================================================================== *)
(*  4a. THE BYTES A RUN OF THE TWO WRITERS PUTS ON THE WIRE                *)
(*                                                                        *)
(*  The consumer's view: from the block already written under [sel], the   *)
(*  bytes a further run [tail] of the two writers emits, in order.  This   *)
(*  is what an [out_chain] over the merged diagnostic is indexed by.       *)
(* ====================================================================== *)

Fixpoint both_bytes (sel : list bool) (tail : list bool) : list (bv 8) :=
  match tail with
  | [] => []
  | true :: t =>
      dg_execL !!! count_true sel :: both_bytes (sel ++ [true]) t
  | false :: t =>
      dg_execR !!! (length sel - count_true sel)%nat
        :: both_bytes (sel ++ [false]) t
  end.

Lemma both_bytes_length (sel tail : list bool) :
  length (both_bytes sel tail) = length tail.
Proof using.
  revert sel. induction tail as [| [|] t IH]; intros sel; cbn [both_bytes length];
    [reflexivity | by rewrite IH | by rewrite IH].
Qed.

Lemma both_bytes_app (sel tail : list bool) :
  sel_wf (sel ++ tail) ->
  pend_both (sel ++ tail) = pend_both sel ++ both_bytes sel tail.
Proof using.
  revert sel. induction tail as [| [|] t IH]; intros sel Hwf.
  - rewrite app_nil_r. cbn [both_bytes]. by rewrite app_nil_r.
  - (* a LEFT byte *)
    assert (Hwf0 : sel_wf sel)
      by (apply (sel_wf_prefix sel (sel ++ (true :: t))); [by eexists | done]).
    assert (Hlt : (count_true sel < length dg_execL)%nat).
    { destruct Hwf as [H1 _]. rewrite count_true_app in H1.
      cbn [count_true] in H1. lia. }
    destruct (lookup_lt_is_Some_2 dg_execL (count_true sel) Hlt) as [b Hb].
    assert (Hshape : (sel ++ (true :: t)) = ((sel ++ [true]) ++ t))
      by (by rewrite -app_assoc).
    rewrite Hshape in Hwf |- *. rewrite (IH (sel ++ [true]) Hwf).
    rewrite (pend_both_true sel b Hwf0 Hb). cbn [both_bytes].
    rewrite -app_assoc. cbn [app]. do 2 f_equal.
    by rewrite (list_lookup_total_correct dg_execL (count_true sel) b Hb).
  - (* a RIGHT byte *)
    assert (Hwf0 : sel_wf sel)
      by (apply (sel_wf_prefix sel (sel ++ (false :: t))); [by eexists | done]).
    assert (Hlt : (length sel - count_true sel < length dg_execR)%nat).
    { destruct Hwf as [_ H2]. rewrite count_true_app length_app in H2.
      cbn [count_true length] in H2.
      pose proof (count_true_le t). pose proof (count_true_le sel). lia. }
    destruct (lookup_lt_is_Some_2 dg_execR (length sel - count_true sel)%nat
                Hlt) as [b Hb].
    assert (Hshape : (sel ++ (false :: t)) = ((sel ++ [false]) ++ t))
      by (by rewrite -app_assoc).
    rewrite Hshape in Hwf |- *. rewrite (IH (sel ++ [false]) Hwf).
    rewrite (pend_both_false sel b Hwf0 Hb). cbn [both_bytes].
    rewrite -app_assoc. cbn [app]. do 2 f_equal.
    by rewrite (list_lookup_total_correct dg_execR _ b Hb).
Qed.

(* ====================================================================== *)
(*  5.  WHAT A COMPLETED ROUND'S BLOCK CANNOT BE                           *)
(*                                                                        *)
(*  The refutation the claim's ECHO step needs in the both arm, and the    *)
(*  reason [sessp_prefix_det] never has to look at an unfiled round: a     *)
(*  non-panic alternative's continuation ENDS WITH THE PROMPT, whose first *)
(*  byte is '$', and no byte of a running merge is a '$'.  So a round      *)
(*  whose block is still in progress can never be mistaken for one whose   *)
(*  block is complete, at any selector.                                    *)
(* ====================================================================== *)

Lemma nodollar_prompt_head : ~ nodollar (Z_to_bv 8 36%Z).
Proof using.
  rewrite /nodollar. intro Hq. apply Hq.
  by vm_compute.
Qed.

(* EVERY non-panic alternative's continuation ends with the prompt -- read
   off the eight constructors, so a WRITER (who holds [palt_ok] but not
   [pline_ok]) can spend it.  [PipeHooks.pcont_prompt] is the same
   lemma one file up; the claim's steps are BELOW that file and need it
   here. *)
(* ...EXCEPT THE TERMINAL FORK-FAILURE ROUND, whose block is a shuffle
   that may stop anywhere -- and may carry the stray's bytes AFTER the
   prompt.  [palt_isforkS a = false] is the premise every consumer of
   this lemma now carries, and at the claim it is [PipeOut.pblk_open]'s
   own disjunction that supplies it. *)
Lemma pcont_prompt_p (l : pline) (a : palt) :
  palt_ok l a -> palt_panic a = false -> palt_isforkS a = false ->
  exists u : list (bv 8), pcont l a = u ++ u_prompt.
Proof using.
  intros Hok Hp Hf.
  destruct a as [k | | | | sel | | sel |]; rewrite /pcont; [| | | | | | done |].
  - assert (Hk : (k < 3)%nat).
    { rewrite /palt_panic in Hp. apply bool_decide_eq_false in Hp.
      destruct l as [ws | ws]; cbn [palt_ok] in Hok; lia. }
    destruct k as [| [| [| k]]]; [| | | exfalso; lia].
    + exists (wl_line (drop 1 (pline_ws l))). exact (line_alts_of_0 _).
    + exists dg_execL. rewrite (line_alts_of_1 (pline_ws l)).
      by rewrite -alt_execL_echo /alt_execL.
    + exists []. rewrite (line_alts_of_2 (pline_ws l)). by rewrite app_nil_l.
  - exists (wl_line (drop 1 (pline_ws l))). reflexivity.
  - exists dg_execL. reflexivity.
  - exists dg_execR. reflexivity.
  - exists (pmerge sel dg_execL dg_execR). reflexivity.
  - exists (wl_line dg_pipe). reflexivity.
  - exists []. by rewrite app_nil_l.
Qed.

(* ...so a `$`-FREE run can never be a whole block: the claim's ECHO step
   refutes an open round with exactly this (the discipline wants the
   round's block, prompt included, on the wire before the next input
   byte). *)
Lemma pcont_not_prefix_nodollar (l : pline) (a : palt) (u : list (bv 8)) :
  palt_ok l a -> palt_panic a = false -> palt_isforkS a = false ->
  Forall nodollar u ->
  ~ (pcont l a `prefix_of` u).
Proof using.
  intros Hok Hp Hf Hnd Hpre.
  destruct (pcont_prompt_p l a Hok Hp Hf) as (z & Hz).
  assert (Hlk : pcont l a !! length z = Some (Z_to_bv 8 36%Z)).
  { rewrite Hz lookup_app_r; [| lia].
    rewrite Nat.sub_diag. exact u_prompt_head. }
  pose proof (prefix_lookup_Some _ _ _ _ Hlk Hpre) as Hlk'.
  exact (nodollar_prompt_head (Forall_lookup_1 _ _ _ _ Hnd Hlk')).
Qed.

Lemma pcont_ne_nodollar (l : pline) (a : palt) (u : list (bv 8)) :
  palt_ok l a -> palt_panic a = false -> palt_isforkS a = false ->
  Forall nodollar u ->
  u <> pcont l a.
Proof using.
  intros Hok Hp Hf Hnd Heq.
  apply (pcont_not_prefix_nodollar l a u Hok Hp Hf Hnd).
  rewrite Heq. reflexivity.
Qed.

Lemma pcont_not_prefix_pend_both (l : pline) (a : palt) (sel : list bool) :
  pline_ok l -> palt_ok l a -> palt_panic a = false ->
  palt_isforkS a = false ->
  ~ (pcont l a `prefix_of` pend_both sel).
Proof using.
  intros Hl Ha Hp Hf Hpre.
  destruct (pcont_shape l a Hl Ha Hp Hf) as (u & Hu & _).
  assert (Hlk : pcont l a !! length u = Some (Z_to_bv 8 36%Z)).
  { rewrite Hu lookup_app_r; [| lia].
    rewrite Nat.sub_diag. exact u_prompt_head. }
  pose proof (prefix_lookup_Some _ _ _ _ Hlk Hpre) as Hlk'.
  exact (nodollar_prompt_head
           (Forall_lookup_1 _ _ _ _ (pend_both_nodollar sel) Hlk')).
Qed.

(* ...and therefore the running block is NEVER a completed round's block:
   the one-line statement design section 4.3b asks for, that
   [PipeDisc.sessp_prefix_det] (which compares COMPLETED rounds' codes) is
   unaffected by the both arm. *)
Lemma pend_both_ne_pcont (l : pline) (a : palt) (sel : list bool) :
  pline_ok l -> palt_ok l a -> palt_panic a = false ->
  palt_isforkS a = false ->
  pend_both sel <> pcont l a.
Proof using.
  intros Hl Ha Hp Hf Heq.
  apply (pcont_not_prefix_pend_both l a sel Hl Ha Hp Hf).
  rewrite Heq. reflexivity.
Qed.

(* ====================================================================== *)
(*  6.  THE ROUND'S LEND, GENERALISED (coordinator's amendment,           *)
(*      2026-09-19, after SH-PIPE-ROUND-2's [pipe_turn_one_writer])        *)
(*                                                                        *)
(*  [EchoOut.turn] is half a [mono_nat] authority, so ONE console writer   *)
(*  at a time -- and sh's runcmd child forks TWICE without knowing which   *)
(*  child will write the round's block.  So the two-cursor lease is not    *)
(*  the [PBoth] arm's mechanism: it is THE ROUND'S LEND on every arm.      *)
(*  The LEFT child's console bytes are always a prefix of [dg_execL] (it   *)
(*  either execs and writes into the PIPE, or fails and prints its         *)
(*  diagnostic); the RIGHT child's are a prefix of ONE list [R] fixed at   *)
(*  its first byte -- the LINE (cat printing what it read, [PRan]) or      *)
(*  [dg_execR] (its own diagnostic, [PExecR]).  So ALL FOUR block shapes   *)
(*  are [pmerge sel dg_execL R] at the two cursors, and the four           *)
(*  alternatives are four ways of finishing it.                           *)
(* ====================================================================== *)

Definition pend2 (R : list (bv 8)) (sel : list bool) : list (bv 8) :=
  pmerge sel dg_execL R.

Definition sel_wf2 (R : list (bv 8)) (sel : list bool) : Prop :=
  (count_true sel <= length dg_execL)%nat
  /\ (length sel - count_true sel <= length R)%nat.

Lemma pend2_execR (sel : list bool) : pend2 dg_execR sel = pend_both sel.
Proof using. reflexivity. Qed.

Lemma sel_wf2_execR (sel : list bool) : sel_wf2 dg_execR sel <-> sel_wf sel.
Proof using. rewrite /sel_wf2 /sel_wf. done. Qed.

Lemma pend2_nil (R : list (bv 8)) : pend2 R [] = [].
Proof using. rewrite /pend2. apply pmerge_nil_sel. Qed.

Lemma pend2_length (R : list (bv 8)) (sel : list bool) :
  sel_wf2 R sel -> length (pend2 R sel) = length sel.
Proof using. intros [H1 H2]. by apply pmerge_length. Qed.

Lemma sel_wf2_prefix (R : list (bv 8)) (sel sel' : list bool) :
  sel `prefix_of` sel' -> sel_wf2 R sel' -> sel_wf2 R sel.
Proof using.
  intros [z ->] [H1 H2]. rewrite count_true_app length_app in H1, H2.
  pose proof (count_true_le z). rewrite /sel_wf2. lia.
Qed.

Lemma pend2_take (R : list (bv 8)) (sel : list bool) (k : nat) :
  take k (pend2 R sel) = pend2 R (take k sel).
Proof using. rewrite /pend2. apply pmerge_take. Qed.

Lemma pend2_mono (R : list (bv 8)) (sel sel' : list bool) :
  sel `prefix_of` sel' -> pend2 R sel `prefix_of` pend2 R sel'.
Proof using.
  intros Hp.
  assert (Hs : take (length sel) sel' = sel)
    by (destruct Hp as [z ->]; by rewrite take_app_length).
  assert (H2 : pend2 R sel = take (length sel) (pend2 R sel'))
    by (rewrite pend2_take Hs; reflexivity).
  rewrite H2. apply prefix_take.
Qed.

Lemma pend2_true (R : list (bv 8)) (sel : list bool) (b : bv 8) :
  sel_wf2 R sel -> dg_execL !! count_true sel = Some b ->
  pend2 R (sel ++ [true]) = pend2 R sel ++ [b].
Proof using.
  intros [H1 H2] Hb. rewrite /pend2 (pmerge_snoc_true sel _ _ H1 H2).
  by rewrite (pop_take1_drop_lookup dg_execL (count_true sel) b Hb).
Qed.

Lemma pend2_false (R : list (bv 8)) (sel : list bool) (b : bv 8) :
  sel_wf2 R sel -> R !! (length sel - count_true sel)%nat = Some b ->
  pend2 R (sel ++ [false]) = pend2 R sel ++ [b].
Proof using.
  intros [H1 H2] Hb. rewrite /pend2 (pmerge_snoc_false sel _ _ H1 H2).
  by rewrite (pop_take1_drop_lookup R _ b Hb).
Qed.

(* A LONGER SELECTOR WRITES A LONGER BLOCK.  What a round has written so
   far is a prefix of what it will have written when it files, which is
   how a witness for the round's FINAL alternative (which the walk knows,
   [pipe_round_lend_holds]'s [pblk2_code]) serves at every byte on the
   way ([PipeBoth.pblk2_wit_mono]). *)
Lemma pend2_prefix (R : list (bv 8)) (sel sel' : list bool) :
  sel `prefix_of` sel' -> sel_wf2 R sel' ->
  pend2 R sel `prefix_of` pend2 R sel'.
Proof using.
  intros [z ->]. revert sel.
  induction z as [| x z IH] using rev_ind; intros sel Hwf.
  - rewrite app_nil_r. done.
  - rewrite app_assoc in Hwf |- *.
    assert (Hwf1 : sel_wf2 R (sel ++ z))
      by exact (sel_wf2_prefix R (sel ++ z) ((sel ++ z) ++ [x])
                  ltac:(by eexists) Hwf).
    assert (Hstep : exists b : bv 8,
               pend2 R ((sel ++ z) ++ [x]) = pend2 R (sel ++ z) ++ [b]).
    { destruct Hwf as [Ha Hb].
      pose proof (count_true_le (sel ++ z)) as Hcle. destruct x.
      - rewrite count_true_app in Ha. cbn [count_true] in Ha.
        destruct (lookup_lt_is_Some_2 dg_execL (count_true (sel ++ z))
                    ltac:(lia)) as [b Hlk].
        exists b. exact (pend2_true R (sel ++ z) b Hwf1 Hlk).
      - rewrite count_true_app length_app in Hb.
        cbn [count_true length] in Hb.
        destruct (lookup_lt_is_Some_2 R
                    (length (sel ++ z) - count_true (sel ++ z))%nat
                    ltac:(lia)) as [b Hlk].
        exists b. exact (pend2_false R (sel ++ z) b Hwf1 Hlk). }
    destruct Hstep as [b Hb]. rewrite Hb.
    apply prefix_app_r. exact (IH sel Hwf1).
Qed.

(* the bytes a run of the two children emits, at the right child's own
   source *)
Fixpoint both_bytes2 (R : list (bv 8)) (sel : list bool) (tail : list bool)
  : list (bv 8) :=
  match tail with
  | [] => []
  | true :: t =>
      dg_execL !!! count_true sel :: both_bytes2 R (sel ++ [true]) t
  | false :: t =>
      R !!! (length sel - count_true sel)%nat
        :: both_bytes2 R (sel ++ [false]) t
  end.

Lemma both_bytes2_app (R : list (bv 8)) (sel tail : list bool) :
  sel_wf2 R (sel ++ tail) ->
  pend2 R (sel ++ tail) = pend2 R sel ++ both_bytes2 R sel tail.
Proof using.
  revert sel. induction tail as [| [|] t IH]; intros sel Hwf.
  - rewrite app_nil_r. cbn [both_bytes2]. by rewrite app_nil_r.
  - assert (Hwf0 : sel_wf2 R sel)
      by (apply (sel_wf2_prefix R sel (sel ++ (true :: t)));
          [by eexists | done]).
    assert (Hlt : (count_true sel < length dg_execL)%nat).
    { destruct Hwf as [H1 _]. rewrite count_true_app in H1.
      cbn [count_true] in H1. lia. }
    destruct (lookup_lt_is_Some_2 dg_execL (count_true sel) Hlt) as [b Hb].
    assert (Hshape : (sel ++ (true :: t)) = ((sel ++ [true]) ++ t))
      by (by rewrite -app_assoc).
    rewrite Hshape in Hwf |- *. rewrite (IH (sel ++ [true]) Hwf).
    rewrite (pend2_true R sel b Hwf0 Hb). cbn [both_bytes2].
    rewrite -app_assoc. cbn [app]. do 2 f_equal.
    by rewrite (list_lookup_total_correct dg_execL (count_true sel) b Hb).
  - assert (Hwf0 : sel_wf2 R sel)
      by (apply (sel_wf2_prefix R sel (sel ++ (false :: t)));
          [by eexists | done]).
    assert (Hlt : (length sel - count_true sel < length R)%nat).
    { destruct Hwf as [_ H2]. rewrite count_true_app length_app in H2.
      cbn [count_true length] in H2.
      pose proof (count_true_le t). pose proof (count_true_le sel). lia. }
    destruct (lookup_lt_is_Some_2 R (length sel - count_true sel)%nat Hlt)
      as [b Hb].
    assert (Hshape : (sel ++ (false :: t)) = ((sel ++ [false]) ++ t))
      by (by rewrite -app_assoc).
    rewrite Hshape in Hwf |- *. rewrite (IH (sel ++ [false]) Hwf).
    rewrite (pend2_false R sel b Hwf0 Hb). cbn [both_bytes2].
    rewrite -app_assoc. cbn [app]. do 2 f_equal.
    by rewrite (list_lookup_total_correct R _ b Hb).
Qed.

(* ---- THE ROUND'S BLOCK SHAPE, at the two cursors and the right child's
       own source ---- *)

Definition wr_blk2_p (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) : Prop :=
  I <> []
  /\ rest_of I = []
  /\ length cs = (nlines I - 1)%nat
  /\ pboth_line I
  /\ pro_pin_p ps cs I
  /\ P = length (proc_before_p ps cs I)
  /\ length sel = (c1 + c2)%nat
  /\ count_true sel = c1
  /\ (c1 <= length dg_execL)%nat
  /\ (c2 <= length R)%nat.

Lemma wr_blk2_p_sel_wf (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) :
  wr_blk2_p ps cs I P R sel c1 c2 -> sel_wf2 R sel.
Proof using.
  intros (_ & _ & _ & _ & _ & _ & Hl & Hc & H1 & H2). rewrite /sel_wf2 Hl Hc.
  split; lia.
Qed.

Lemma wr_blk2_p_entry (ps cs : list nat) (I : list (bv 8))
    (R : list (bv 8)) :
  I <> [] -> rest_of I = [] ->
  length cs = (nlines I - 1)%nat ->
  pboth_line I ->
  pro_pin_p ps cs I ->
  wr_blk2_p ps cs I (length (proc_before_p ps cs I)) R [] 0%nat 0%nat
  /\ pend2 R [] = [].
Proof using.
  intros Hne Hr Hq Hl Hpin. split; [| exact (pend2_nil R)].
  rewrite /wr_blk2_p. split_and!; try done; cbn [count_true length]; lia.
Qed.

Lemma wr_blk2_step_L (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) (b : bv 8) :
  wr_blk2_p ps cs I P R sel c1 c2 ->
  dg_execL !! c1 = Some b ->
  wr_blk2_p ps cs I P R (sel ++ [true]) (S c1) c2
  /\ pend2 R (sel ++ [true]) = pend2 R sel ++ [b].
Proof using.
  intros Hw Hb. pose proof Hw as (Hne & Hr & Hq & Hl & Hpin & HP & Hlen & Hcnt
                                  & H1 & H2).
  pose proof (lookup_lt_Some _ _ _ Hb) as Hlt.
  assert (Hstep : pend2 R (sel ++ [true]) = pend2 R sel ++ [b]).
  { apply (pend2_true R sel b (wr_blk2_p_sel_wf _ _ _ _ _ _ _ _ Hw)).
    by rewrite Hcnt. }
  split; [| exact Hstep].
  rewrite /wr_blk2_p. split_and!;
    first [ done
          | rewrite length_app Hlen; cbn [length]; lia
          | rewrite count_true_app Hcnt; cbn [count_true]; lia
          | lia ].
Qed.

Lemma wr_blk2_step_R (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) (b : bv 8) :
  wr_blk2_p ps cs I P R sel c1 c2 ->
  R !! c2 = Some b ->
  wr_blk2_p ps cs I P R (sel ++ [false]) c1 (S c2)
  /\ pend2 R (sel ++ [false]) = pend2 R sel ++ [b].
Proof using.
  intros Hw Hb. pose proof Hw as (Hne & Hr & Hq & Hl & Hpin & HP & Hlen & Hcnt
                                  & H1 & H2).
  pose proof (lookup_lt_Some _ _ _ Hb) as Hlt.
  assert (Hstep : pend2 R (sel ++ [false]) = pend2 R sel ++ [b]).
  { apply (pend2_false R sel b (wr_blk2_p_sel_wf _ _ _ _ _ _ _ _ Hw)).
    by replace (length sel - count_true sel)%nat with c2 by lia. }
  split; [| exact Hstep].
  rewrite /wr_blk2_p. split_and!;
    first [ done
          | rewrite length_app Hlen; cbn [length]; lia
          | rewrite count_true_app Hcnt; cbn [count_true]; lia
          | lia ].
Qed.

(* ====================================================================== *)
(*  7.  THE ROUND'S FOUR EXITS, AND F4 AT AN UNFILED BLOCK OF ANY SHAPE    *)
(* ====================================================================== *)

(* the stage reading at the round's own filed entry, for ANY non-panic
   alternative *)
Lemma pending_at_p_filed_gen (ps cs : list nat) (I : list (bv 8))
    (a : nat) :
  I <> [] -> rest_of I = [] ->
  length cs = (nlines I - 1)%nat ->
  palt_panic (palt_of a) = false ->
  pending_at_p ps (cs ++ [a]) I
  = pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat)) (palt_of a).
Proof using.
  intros Hne Hr Hq Hpan. rewrite /pending_at_p.
  rewrite decide_False; [| exact Hne]. rewrite decide_True; [| exact Hr].
  rewrite /alt_cont_p (palt_at_snoc cs (nlines I - 1)%nat a Hq) Hpan.
  by rewrite app_nil_r.
Qed.

(* THE BLOCK IN PROGRESS, of any shape: the round's entry is absent and
   the bytes so far are a prefix of the continuation of an alternative the
   line admits. *)
Definition pblk2_at (cs : list nat) (I : list (bv 8)) (w : list (bv 8))
    (a : nat) : Prop :=
  I <> []
  /\ rest_of I = []
  /\ length cs = (nlines I - 1)%nat
  /\ palt_ok (pline_of (bodies_of I !!! (nlines I - 1)%nat)) (palt_of a)
  /\ palt_panic (palt_of a) = false
  /\ w `prefix_of`
     pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat)) (palt_of a).

(* F4 AT THE ROUND'S LEND: the console claim holds at every byte of a
   block whose alternative has NOT been filed -- the witness the
   theorem's existential wants is the round's own code, appended. *)
Lemma good_out_p_of_stage_blk2 (ps cs : list nat)
    (E : list (list mobs * bv 8)) (w : list (bv 8)) (a : nat)
    (seg : list mobs) :
  Forall (fun x => (x < length pro_alts)%nat) ps ->
  alts_pre_p (ins seg) cs ->
  E_disc_p E ->
  pro_pin_p ps cs (snd <$> E) ->
  pblk2_at cs (snd <$> E) w a ->
  obs_wire Uart0 seg `prefix_of` (D_p ps cs E ++ w) ->
  (snd <$> E) `prefix_of` ins seg ->
  good_out_p seg.
Proof using.
  intros Hps Hao HE Hpin Hblk Hwire Hinp.
  pose proof Hblk as (Hne & Hr & Hq & Hok0 & Hpan & Hpre).
  pose proof (nlines_pos_of_rest_nil _ Hne Hr) as Hpos.
  set (cs' := (cs ++ [a])%list).
  assert (Hcsp : cs `prefix_of` cs') by (rewrite /cs'; by eexists).
  assert (Hlen' : length cs' = nlines (snd <$> E))
    by (rewrite /cs' length_app Hq; cbn [length]; lia).
  assert (Hnl : (nlines (snd <$> E) <= nlines (ins seg))%nat)
    by (by apply nlines_prefix).
  assert (Hbod : bodies_of (ins seg) !!! (nlines (snd <$> E) - 1)%nat
                 = bodies_of (snd <$> E) !!! (nlines (snd <$> E) - 1)%nat).
  { destruct (bodies_of_prefix (snd <$> E) (ins seg) Hinp) as [z Hz].
    rewrite Hz !list_lookup_total_alt lookup_app_l;
      [reflexivity | rewrite /nlines in Hpos |- *; lia]. }
  assert (Hok : palt_ok (pline_of (bodies_of (ins seg) !!! length cs))
                  (palt_of a)) by (rewrite Hq Hbod; exact Hok0).
  assert (Hao' : alts_pre_p (ins seg) cs').
  { apply (alts_pre_p_snoc (ins seg) cs a Hao); [| exact Hok].
    rewrite Hq. rewrite /nlines in Hpos, Hnl |- *. lia. }
  assert (Hpin' : pro_pin_p ps cs' (snd <$> E)).
  { intros qq Hqq. rewrite /cs' pro_idx_p_app_le; [by apply Hpin |].
    rewrite (pop_nstarted_rest_nil _ Hr) in Hqq. rewrite Hq. lia. }
  assert (HD : D_p ps cs' E = D_p ps cs E).
  { symmetry. apply (D_p_cs_prefix ps ps cs cs' E);
      [reflexivity | exact Hcsp | exact Hpin |].
    rewrite (pop_nlines_removelast _ Hr) Hq. lia. }
  apply (good_out_p_of_stage ps cs' E w seg Hps Hao').
  - rewrite (pop_nlines_removelast _ Hr) Hlen'. lia.
  - left. lia.
  - exact HE.
  - exact Hpin'.
  - rewrite /pending_p
      (pending_at_p_filed_gen ps cs (snd <$> E) a Hne Hr Hq Hpan).
    exact Hpre.
  - by rewrite HD.
  - exact Hinp.
Qed.

(* ---- THE FOUR ALTERNATIVES THE ROUND CAN FILE, and the block each of
       them owes.  Every one is [_ ++ u_prompt], which is what makes the
       exit ONE lemma at four instances. ---- *)

Lemma palt_ok_LPipe_ran (ws : list (list (bv 8))) : palt_ok (LPipe ws) PRan.
Proof using. by cbn. Qed.
Lemma palt_ok_LPipe_execL (ws : list (list (bv 8))) :
  palt_ok (LPipe ws) PExecL.
Proof using. by cbn. Qed.
Lemma palt_ok_LPipe_execR (ws : list (list (bv 8))) :
  palt_ok (LPipe ws) PExecR.
Proof using. by cbn. Qed.

Lemma pcont_ran (ws : list (list (bv 8))) :
  pcont (LPipe ws) PRan = wl_line (drop 1 ws) ++ u_prompt.
Proof using. reflexivity. Qed.
Lemma pcont_execL (ws : list (list (bv 8))) :
  pcont (LPipe ws) PExecL = dg_execL ++ u_prompt.
Proof using. reflexivity. Qed.
Lemma pcont_execR (ws : list (list (bv 8))) :
  pcont (LPipe ws) PExecR = dg_execR ++ u_prompt.
Proof using. reflexivity. Qed.

Lemma palt_panic_ran : palt_panic PRan = false.
Proof using. reflexivity. Qed.
Lemma palt_panic_execL : palt_panic PExecL = false.
Proof using. reflexivity. Qed.
Lemma palt_panic_execR : palt_panic PExecR = false.
Proof using. reflexivity. Qed.
Lemma palt_panic_both (sel : list bool) : palt_panic (PBoth sel) = false.
Proof using. reflexivity. Qed.

(* the block the two cursors have written, read as one of the four:
   [c1 = 0] and the right child at its whole source is [PRan] (source =
   the line) or [PExecR] (source = the right diagnostic); [c2 = 0] and the
   left child at its whole diagnostic is [PExecL]; both complete is
   [PBoth sel]. *)
Lemma pmerge_all_true (sel : list bool) (d1 d2 : list (bv 8)) :
  count_true sel = length sel -> (length sel <= length d1)%nat ->
  pmerge sel d1 d2 = take (length sel) d1.
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 Hc Hle.
  - by rewrite pmerge_nil_sel.
  - cbn [count_true length] in Hc, Hle |- *.
    destruct d1 as [| b d1']; [cbn [length] in Hle; lia |].
    rewrite pmerge_true_cons. cbn [take]. f_equal.
    apply IH; [lia | cbn [length] in Hle; lia].
  - exfalso. cbn [count_true length] in Hc.
    pose proof (count_true_le s). lia.
Qed.

Lemma pmerge_all_false (sel : list bool) (d1 d2 : list (bv 8)) :
  count_true sel = 0%nat -> (length sel <= length d2)%nat ->
  pmerge sel d1 d2 = take (length sel) d2.
Proof using.
  revert d1 d2. induction sel as [| [|] s IH]; intros d1 d2 Hc Hle.
  - by rewrite pmerge_nil_sel.
  - exfalso. cbn [count_true] in Hc. lia.
  - cbn [count_true length] in Hc, Hle |- *.
    destruct d2 as [| b d2']; [cbn [length] in Hle; lia |].
    rewrite pmerge_false_cons. cbn [take]. f_equal.
    apply IH; [lia | cbn [length] in Hle; lia].
Qed.

(* THE LEFT CHILD ALONE: the block is its whole diagnostic, and the
   alternative is [PExecL]. *)
Lemma pend2_left_only (R : list (bv 8)) (sel : list bool) :
  count_true sel = length dg_execL -> length sel = length dg_execL ->
  pend2 R sel = dg_execL.
Proof using.
  intros Hc Hl. rewrite /pend2 (pmerge_all_true sel dg_execL R);
    [| lia | lia].
  rewrite Hl. apply take_ge. lia.
Qed.

(* THE RIGHT CHILD ALONE: the block is its whole source -- the LINE at
   [PRan], its own diagnostic at [PExecR]. *)
Lemma pend2_right_only (R : list (bv 8)) (sel : list bool) :
  count_true sel = 0%nat -> length sel = length R ->
  pend2 R sel = R.
Proof using.
  intros Hc Hl. rewrite /pend2 (pmerge_all_false sel dg_execL R);
    [| lia | lia].
  rewrite Hl. apply take_ge. lia.
Qed.

(* BOTH COMPLETE: the block is the merge, and the alternative is
   [PBoth sel] -- the ONE place the code is built, out of the selector's
   length and its count of trues. *)
Lemma pend2_both_full (ws : list (list (bv 8))) (sel : list bool) :
  count_true sel = length dg_execL ->
  length sel = (length dg_execL + length dg_execR)%nat ->
  palt_ok (LPipe ws) (PBoth sel)
  /\ pcont (LPipe ws) (PBoth sel) = pend2 dg_execR sel ++ u_prompt.
Proof using.
  intros Hc Hl. split; [by apply palt_ok_both | reflexivity].
Qed.
