(* ===================================================================== *)
(* PipesDiscDec.v -- A DECISION PROCEDURE for the blocks of a pipeline   *)
(* ([PipesDisc.line_blocks]) and the demos run through it (cut C2).       *)
(*                                                                        *)
(*  The runs of a line are FINITE -- every [D] is a prefix of the line's *)
(*  content -- so they are enumerated ([stage_outs], [sfx_runs],          *)
(*  [line_runs], each proved equal to its relation), and a merge is       *)
(*  tested byte by byte ([mergeb], pruning at the first byte no stream    *)
(*  offers).  [line_blocksb_spec] is the reflection the demos spend.      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List String.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel PipeDisc.
Require Import StringBytes ProgTree ProgTreePipes PipesPair PipesDisc.
From stdpp Require Import list.

Local Open Scope nat_scope.

(* ===================================================================== *)
(*  1.  THE ENUMERATIONS                                                  *)
(* ===================================================================== *)

Definition prefixes (L : bytes) : list bytes := (fun k => take k L) <$> seq 0 (S (length L)).

Lemma prefixes_spec D L : D ∈ prefixes L <-> D `prefix_of` L.
Proof using.
  unfold prefixes. rewrite elem_of_list_fmap. split.
  - intros (k & -> & _). apply prefix_take.
  - intros HD. exists (length D). split; [exact (prefix_take_eq D L HD) |].
    apply elem_of_seq. pose proof (prefix_length _ _ HD). lia.
Qed.

(* the program's own outcomes of a stage, past sh's two *)
Definition stage_outs_prog (fc : bytes -> option bytes) (L : bytes) (st : stage) : list st_out :=
  match st with
  | SProd (PrEcho ws) =>
      if decide (L = wl_line (drop 1 ws))
      then MkSO [] None (Some (WrAll L)) :: ((fun D => MkSO [] None (Some (WrHalt D))) <$> prefixes L)
      else []
  | SProd (PrCatF f) =>
      MkSO (cat_dg_open f) None (Some WrNone)
      :: (if decide (fc f = Some L)
          then MkSO [] None (Some (WrAll L))
               :: ((fun D => MkSO cat_dg_write None (Some (WrHalt D))) <$> prefixes L)
          else [])
  | SMid =>
      ((fun D => MkSO [] (Some (RdEof D)) (Some (WrAll D))) <$> prefixes L)
      ++ ((fun D => MkSO cat_dg_write (Some RdGone) (Some (WrHalt D))) <$> prefixes L)
  | SLast => (fun D => MkSO D (Some (RdEof D)) None) <$> prefixes L
  end.

Definition stage_outs (fc : bytes -> option bytes) (L : bytes) (st : stage) : list st_out :=
  MkSO (st_dg_exec st) (st_rd_dead st) (st_wr_dead st)
  :: MkSO [] (st_rd_dead st) (st_wr_dead st)
  :: stage_outs_prog fc L st.

Lemma stage_outs_spec fc L st so : so ∈ stage_outs fc L st <-> stage_out fc L st so.
Proof using.
  split.
  - unfold stage_outs. intros H.
    apply elem_of_cons in H as [-> | H]; [apply so_exec |].
    apply elem_of_cons in H as [-> | H]; [apply so_silent |].
    destruct st as [[ws | f] | |]; cbn [stage_outs_prog] in H.
    + destruct (decide (L = wl_line (drop 1 ws))) as [HL | HL]; [| by apply elem_of_nil in H].
      apply elem_of_cons in H as [-> | H]; [apply so_echo; exact HL |].
      apply elem_of_list_fmap in H as (D & -> & HD).
      apply so_echo_halt; [exact HL | apply prefixes_spec; exact HD].
    + apply elem_of_cons in H as [-> | H]; [apply so_catf_open |].
      destruct (decide (fc f = Some L)) as [HL | HL]; [| by apply elem_of_nil in H].
      apply elem_of_cons in H as [-> | H]; [apply so_catf; exact HL |].
      apply elem_of_list_fmap in H as (D & -> & HD).
      apply so_catf_halt; [exact HL | apply prefixes_spec; exact HD].
    + apply elem_of_app in H as [H | H]; apply elem_of_list_fmap in H as (D & -> & HD).
      * apply so_mid_copy. apply prefixes_spec. exact HD.
      * apply so_mid_halt. apply prefixes_spec. exact HD.
    + apply elem_of_list_fmap in H as (D & -> & HD). apply so_last. apply prefixes_spec. exact HD.
  - unfold stage_outs. intros H.
    destruct H as [st | st | ws HL | ws D HL HD | f Hf | f D Hf HD | f | D HD | D HD | D HD].
    + apply elem_of_cons. left. reflexivity.
    + apply elem_of_cons. right. apply elem_of_cons. left. reflexivity.
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog].
      rewrite decide_True by exact HL. apply elem_of_cons. left. reflexivity.
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog].
      rewrite decide_True by exact HL. apply elem_of_cons. right.
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_cons. right.
      rewrite decide_True by exact Hf. apply elem_of_cons. left. reflexivity.
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_cons. right.
      rewrite decide_True by exact Hf. apply elem_of_cons. right.
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_cons. left. reflexivity.
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_app. left.
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog]. apply elem_of_app. right.
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
    + do 2 (apply elem_of_cons; right). cbn [stage_outs_prog].
      apply elem_of_list_fmap. exists D. split; [reflexivity | apply prefixes_spec; exact HD].
Qed.

Fixpoint sfx_runs (fc : bytes -> option bytes) (L : bytes) (m : nat) (w : wr_out) (wc : bool)
    : list (list bytes) :=
  match m with
  | 0 => []
  | 1 => (fun so => [so_cons so])
           <$> filter (fun so => pipe_pairB L wc w (rd_of so)) (stage_outs fc L SLast)
  | S (S m' as m1) =>
      [dg_pipe_b]
      :: mjoin ((fun so => (fun ss => so_cons so :: ss) <$> sfx_runs fc L m1 (wr_of so) true)
                  <$> filter (fun so => pipe_pairB L wc w (rd_of so)) (stage_outs fc L SMid))
  end.

Lemma sfx_runs_spec fc L m w wc ss : ss ∈ sfx_runs fc L m w wc <-> sfx_run fc L m w wc ss.
Proof using.
  revert w wc ss. induction m as [| m IH]; intros w wc ss.
  - cbn [sfx_runs]. split; [intros H; by apply elem_of_nil in H |].
    intros H. remember 0 as z eqn:Hz in H. revert Hz. destruct H; intros Hz; discriminate Hz.
  - destruct m as [| m'].
    + cbn [sfx_runs]. rewrite elem_of_list_fmap. split.
      * intros (so & -> & Hso). apply elem_of_list_filter in Hso as [Hp Hso].
        apply stage_outs_spec in Hso. apply sr_last; assumption.
      * intros H. remember 1 as z eqn:Hz in H. revert Hz.
        destruct H as [win wc0 so Hso Hp | m0 win wc0 | m0 win wc0 so ss0 Hso Hp Hr];
          intros Hz; [| discriminate Hz | discriminate Hz].
        exists so. split; [reflexivity |].
        apply elem_of_list_filter. split; [exact Hp | apply stage_outs_spec; exact Hso].
    + cbn [sfx_runs]. rewrite elem_of_cons, elem_of_list_join. split.
      * intros [-> | (l & Hss & Hl)]; [apply sr_pipe_fail |].
        apply elem_of_list_fmap in Hl as (so & -> & Hso).
        apply elem_of_list_filter in Hso as [Hp Hso].
        apply elem_of_list_fmap in Hss as (ss' & -> & Hss'). apply IH in Hss'.
        apply stage_outs_spec in Hso. apply sr_node; assumption.
      * intros H. remember (S (S m')) as z eqn:Hz in H. revert Hz.
        destruct H as [win wc0 so Hso Hp | m0 win wc0 | m0 win wc0 so ss0 Hso Hp Hr];
          intros Hz; [discriminate Hz | left; reflexivity |].
        injection Hz as ->. right.
        exists ((fun ss => so_cons so :: ss) <$> sfx_runs fc L (S m') (wr_of so) true). split.
        -- apply elem_of_list_fmap. exists ss0. split; [reflexivity | apply IH; exact Hr].
        -- apply elem_of_list_fmap. exists so. split; [reflexivity |].
           apply elem_of_list_filter. split; [exact Hp | apply stage_outs_spec; exact Hso].
Qed.

Definition line_runs (fc : bytes -> option bytes) (l : pline') : list (list bytes) :=
  match l with
  | LEcho' ws => [[wl_line (drop 1 ws)]; [dg_execL]; [[]]]
  | LPipes p n =>
      (if decide (1 <= n) then [[dg_pipe_b]] else [])
      ++ mjoin ((fun so => (fun ss => so_cons so :: ss)
                             <$> sfx_runs fc (prod_content fc p) n (wr_of so) (prod_cat p))
                  <$> stage_outs fc (prod_content fc p) (SProd p))
  end.

Lemma line_runs_spec fc l ss : ss ∈ line_runs fc l <-> line_run fc l ss.
Proof using.
  destruct l as [ws | p n]; cbn [line_runs].
  - split.
    + intros H. apply elem_of_cons in H as [-> | H]; [apply lr_echo |].
      apply elem_of_cons in H as [-> | H]; [apply lr_echo_exec |].
      apply elem_of_list_singleton in H as ->. apply lr_echo_silent.
    + intros H. remember (LEcho' ws) as l eqn:Hl. revert Hl.
      destruct H as [ws0 | ws0 | ws0 | p n Hn | p n so ss0 Hso Hr]; intros Hl;
        try discriminate Hl; injection Hl as ->.
      * apply elem_of_cons. left. reflexivity.
      * apply elem_of_cons. right. apply elem_of_cons. left. reflexivity.
      * apply elem_of_cons. right. apply elem_of_cons. right. apply elem_of_list_singleton. reflexivity.
  - rewrite elem_of_app, elem_of_list_join. split.
    + intros [H | (l & Hss & Hl)].
      * destruct (decide (1 <= n)) as [Hn | Hn]; [| by apply elem_of_nil in H].
        apply elem_of_list_singleton in H as ->. apply lr_pipe_fail. exact Hn.
      * apply elem_of_list_fmap in Hl as (so & -> & Hso).
        apply elem_of_list_fmap in Hss as (ss' & -> & Hss').
        apply sfx_runs_spec in Hss'. apply stage_outs_spec in Hso. apply lr_node; assumption.
    + intros H. remember (LPipes p n) as l eqn:Hl. revert Hl.
      destruct H as [ws0 | ws0 | ws0 | p0 n0 Hn | p0 n0 so ss0 Hso Hr]; intros Hl;
        try discriminate Hl; injection Hl as -> ->.
      * left. rewrite decide_True by exact Hn. apply elem_of_list_singleton. reflexivity.
      * right. exists ((fun ss => so_cons so :: ss)
                         <$> sfx_runs fc (prod_content fc p) n (wr_of so) (prod_cat p)). split.
        -- apply elem_of_list_fmap. exists ss0. split; [reflexivity | apply sfx_runs_spec; exact Hr].
        -- apply elem_of_list_fmap. exists so. split; [reflexivity | apply stage_outs_spec; exact Hso].
Qed.

(* ===================================================================== *)
(*  2.  THE MERGE TEST                                                    *)
(* ===================================================================== *)

(* every way to take the byte [x] off the head of one of the streams *)
Fixpoint picks (x : bv 8) (ss : list bytes) : list (list bytes) :=
  match ss with
  | [] => []
  | s :: ss' =>
      (match s with y :: s' => if decide (y = x) then [s' :: ss'] else [] | [] => [] end)
      ++ ((fun r => s :: r) <$> picks x ss')
  end.

Lemma picks_spec x ss ss' :
  ss' ∈ picks x ss <-> exists i s, ss !! i = Some (x :: s) /\ ss' = <[i := s]> ss.
Proof using.
  revert ss'. induction ss as [| s ss IH]; intros ss'; cbn [picks].
  - split; [intros H; by apply elem_of_nil in H | intros (i & s & H & _); discriminate H].
  - rewrite elem_of_app. split.
    + intros [H | H].
      * destruct s as [| y s']; [by apply elem_of_nil in H |].
        destruct (decide (y = x)) as [-> | Hne]; [| by apply elem_of_nil in H].
        apply elem_of_list_singleton in H as ->. exists 0, s'. split; reflexivity.
      * apply elem_of_list_fmap in H as (r & -> & Hr). apply IH in Hr as (i & s0 & Hi & ->).
        exists (S i), s0. split; [exact Hi | reflexivity].
    + intros ([| i] & s0 & Hi & ->).
      * left. injection Hi as ->. cbn. rewrite decide_True by reflexivity.
        apply elem_of_list_singleton. reflexivity.
      * right. apply elem_of_list_fmap. exists (<[i := s0]> ss). split; [reflexivity |].
        apply IH. exists i, s0. split; [exact Hi | reflexivity].
Qed.

Fixpoint mergeb (ss : list bytes) (b : bytes) : bool :=
  match b with
  | [] => forallb (fun s => bool_decide (s = [])) ss
  | x :: b' => existsb (fun ss' => mergeb ss' b') (picks x ss)
  end.

Lemma mergeb_spec ss b : mergeb ss b = true <-> merge_all ss b.
Proof using.
  revert ss. induction b as [| x b IH]; intros ss; cbn [mergeb].
  - rewrite forallb_forall. split.
    + intros H. apply ma_done. apply Forall_forall. intros s Hs.
      apply elem_of_list_In in Hs. exact (bool_decide_eq_true_1 _ (H s Hs)).
    + intros Hm s Hs. apply bool_decide_eq_true_2.
      inversion Hm as [ss' HF | ]; subst.
      exact (proj1 (Forall_forall _ _) HF s (proj2 (elem_of_list_In _ _) Hs)).
  - rewrite existsb_exists. split.
    + intros (ss' & Hin & Hm). apply elem_of_list_In, picks_spec in Hin as (i & s & Hi & ->).
      apply (ma_take ss i x s b Hi). apply IH. exact Hm.
    + intros Hm. inversion Hm as [| ss0 i x0 s b0 Hi Hm']; subst.
      exists (<[i := s]> ss). split; [| apply IH; exact Hm'].
      apply elem_of_list_In, picks_spec. exists i, s. split; [exact Hi | reflexivity].
Qed.

Definition line_blocksb (fc : bytes -> option bytes) (l : pline') (b : bytes) : bool :=
  existsb (fun ss => mergeb ss b) (line_runs fc l).

Lemma line_blocksb_spec fc l b : line_blocksb fc l b = true <-> line_blocks fc l b.
Proof using.
  unfold line_blocksb, line_blocks. rewrite existsb_exists. split.
  - intros (ss & Hin & Hm). exists ss.
    split; [apply line_runs_spec, elem_of_list_In; exact Hin | apply mergeb_spec; exact Hm].
  - intros (ss & Hr & Hm). exists ss.
    split; [apply elem_of_list_In, line_runs_spec; exact Hr | apply mergeb_spec; exact Hm].
Qed.

(* ===================================================================== *)
(*  3.  DEMOS                                                             *)
(* ===================================================================== *)

Definition fc0 : bytes -> option bytes := fun _ => None.
Definition nlb' : bytes := [wl_nl].

(* echo foo | cat | cat | cat -- parsed, well formed, admitted *)
Definition l_foo3 : pline' := LPipes (PrEcho [cmd_echo; sb "foo"]) 3.

Example demo_parse_foo3 : pl_parse (sb "echo foo | cat | cat | cat") = Some l_foo3.
Proof using. vm_compute. reflexivity. Qed.

Example demo_foo3_ok : pl_ok l_foo3.
Proof using. apply (bool_decide_unpack _). vm_compute. exact I. Qed.

(* SUCCESS: the line, and nothing else *)
Example demo_foo3_run : line_blocks fc0 l_foo3 (sb "foo" ++ nlb').
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.

Example demo_foo3_lm :
  lm_ok (pipes_lm fc0 adm_echo_safe) l_foo3 (PLRun (sb "foo" ++ nlb'))
  /\ lm_cont (pipes_lm fc0 adm_echo_safe) tt l_foo3 (PLRun (sb "foo" ++ nlb'))
     = sb "foo" ++ nlb' ++ sb "$ ".
Proof using. split; [split; [vm_compute; reflexivity | exact demo_foo3_run] | reflexivity]. Qed.

(* every failure prints no content: a middle cat's exec failure, and two
   of them interleaved *)
Example demo_foo3_exec : line_blocks fc0 l_foo3 dg_execR.
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.

Example demo_foo3_exec2 :
  line_blocks fc0 l_foo3 (sb "execexec cat failed" ++ nlb' ++ sb " cat failed" ++ nlb').
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.

(* NEGATIVE: the line is not someone else's *)
Example demo_foo3_neg : ~ line_blocks fc0 l_foo3 (sb "bar" ++ nlb').
Proof using. intros H. apply line_blocksb_spec in H. vm_compute in H. discriminate H. Qed.

(* NEGATIVE: at [echo foo | cat] content never sits beside a diagnostic
   -- echo's halt is silent, so the corner is absent at n = 1 *)
Definition l_foo1 : pline' := LPipes (PrEcho [cmd_echo; sb "foo"]) 1.

Example demo_foo1_neg_exec : ~ line_blocks fc0 l_foo1 (sb "foo" ++ nlb' ++ dg_execL).
Proof using. intros H. apply line_blocksb_spec in H. vm_compute in H. discriminate H. Qed.

Example demo_foo1_neg_corner : ~ line_blocks fc0 l_foo1 (sb "fo" ++ cat_dg_write).
Proof using. intros H. apply line_blocksb_spec in H. vm_compute in H. discriminate H. Qed.

(* THE CORNER (B), MID-STAGE WRITE ERROR: at [echo foo | cat | cat] a
   middle cat's [cat: write error] beside a prefix of the line the last
   cat printed -- and beside the whole line *)
Definition l_foo2 : pline' := LPipes (PrEcho [cmd_echo; sb "foo"]) 2.

Example demo_foo2_corner : line_blocks fc0 l_foo2 (sb "fo" ++ cat_dg_write).
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.

Example demo_foo2_corner_full : line_blocks fc0 l_foo2 (sb "foo" ++ nlb' ++ cat_dg_write).
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.

(* ...and at three cats the corner lets the first middle cat's exec
   failure through as well (its reader, the halted cat, vouches for
   nothing) *)
Example demo_foo3_corner_exec :
  line_blocks fc0 l_foo3 (sb "foo" ++ nlb' ++ cat_dg_write ++ dg_execR).
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.

(* cat f as the producer, at a content function that has [f] *)
Definition fc1 : bytes -> option bytes :=
  fun f => if decide (f = sb "f") then Some (sb "foo bar" ++ nlb') else None.

Example demo_catf_cat_cat :
  line_blocks fc1 (LPipes (PrCatF (sb "f")) 2) (sb "foo bar" ++ nlb').
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.

Example demo_catf_absent :
  line_blocks fc1 (LPipes (PrCatF (sb "nope")) 2) (cat_dg_open (sb "nope")).
Proof using. apply line_blocksb_spec. vm_compute. reflexivity. Qed.

Example demo_catf_absent_neg :
  ~ line_blocks fc1 (LPipes (PrCatF (sb "nope")) 1) (sb "foo bar" ++ nlb').
Proof using. intros H. apply line_blocksb_spec in H. vm_compute in H. discriminate H. Qed.

(* THE TERMINAL ROUND at three stages: the fork of the node below echo
   fails after its left child (a middle cat) was forked; that stray's exec
   diagnostic lands after the prompt.  It is a coverage-ending block of
   this model and NOT one of the landed model's ([PipeDisc.pmergeable]):
   D4 widens with the stages. *)
Definition term_blk : bytes := dg_fork_b ++ u_prompt ++ dg_execR.

Example demo_term_foo2 : plalt_ok fc0 l_foo2 (PLTerm term_blk).
Proof using.
  split; [discriminate |]. exists term_blk. split; [| reflexivity].
  exists [[]; dg_fork_b], dg_execR, dg_fork_b, dg_execR. split.
  - apply (lt_next fc0 (PrEcho [cmd_echo; sb "foo"]) 2
             (MkSO [] None (Some (WrAll (prod_content fc0 (PrEcho [cmd_echo; sb "foo"])))))).
    + apply so_echo. reflexivity.
    + exact (stt_here fc0 _ 0 _ false _ (so_exec fc0 _ SMid)).
  - split; [apply mergeb_spec; vm_compute; reflexivity |].
    split; [reflexivity |]. apply mergeb_spec. vm_compute. reflexivity.
Qed.

Example demo_term_not_landed : ~ pmergeable term_blk.
Proof using. unfold pmergeable. vm_compute. discriminate. Qed.

Example demo_term_merge : lm_merge (pipes_lm fc0 adm_echo_safe) term_blk.
Proof using. exists l_foo2, term_blk. split; [vm_compute; reflexivity | split; [exact demo_term_foo2 | reflexivity]]. Qed.
