(* PipeDiscDec.v -- [PipeDisc.disc_p] IS DECIDABLE, so the pipeline
   application's ledger can put its taint counter at [decide (disc_p h)].

   Design of record: claude-notes/design/app-pipe.md section 1 and the
   worklist's lane PIPE-DEC; the mould is [FileDiscDec] (lane FILE-DEC,
   "BLOCKER 1": the ledger's counter sits at [decide (disc h)], so the
   discipline must be DECIDABLE and the stage must take no hypothesis).
   [EchoDisc.disc_seg'_dec] decides the echo discipline by a finite search
   over the prologue resolutions ([pro_cands] through [pro_canon]) and the
   per-line choices ([bounded_lists 4]).  TWO things stop that search from
   porting verbatim, and ONE thing [FileDiscDec] had to pay does not
   arise here at all:

   - THE CHOICES ARE NO LONGER BOUNDED BY 4, and the codes are not an
     initial segment of the naturals ([palt_code (PBoth sel)] is
     [11 + 16 * bnum sel]), so [bounded_lists] cannot enumerate them.
     They ARE finite per line: [palt_ok] admits, at an [LPipe] line, the
     six constant alternatives, [PEcho 3], and exactly those [PBoth sel]
     with [length sel = |dg_execL| + |dg_execR|] and
     [count_true sel = |dg_execL|].  [choose n k] enumerates the
     selectors and [palt_cands] the codes.  NOTHING HERE IS EVALUATED:
     [choose 33 17] has [C(33,17) > 10^9] entries and a [PBoth] code
     exceeds [2 ^ 33] ([PipeDisc.palt_code_both_big]), so -- exactly as
     lane PIPE-MODEL-2 reported -- a [PBoth] round can be REASONED about
     and never COMPUTED.  This file only ever needs the membership law
     [elem_of_choose], which is a theorem about the enumerator and does
     not run it; the [Decision] instance is something the ledger CASES
     ON, not something anybody evaluates.
   - THE ENUMERATOR LISTS ONLY CANONICAL CODES [palt_code a].  A witness
     is canonicalised to those by [cs_canon_p], which is sound because
     every consumer of [cs] -- [pro_idx_p], [alt_cont_p], [alt_seq_p],
     [sessp], [pro_ok_p], [disc_pt_p], [alts_ok_p] -- reads it ONLY
     through [palt_at = palt_of o (!!!)], and
     [palt_of (palt_code (palt_of c)) = palt_of c].
   - WHAT DOES NOT ARISE: [FileDiscDec]'s sections 6 and 7 (the boot-state
     canonicalisation -- [infixed], [substrings], [scands],
     [disc_seg_f'_canon]) have NO counterpart.  [FileDisc.disc_f] is
     [exists s, fstate_ok s /\ disc_seg_f' s seg] because the file state is
     threaded across rounds and cycles; a pipe dies with its era (design
     section 0, limit 3), so [PipeDisc.sessp] threads NO state,
     [disc_seg_p'] quantifies over [ps] and [cs] alone, and the decision
     is of [disc_seg_p'] itself.  Hence there is no [disc_seg_p'_canon]
     and no [disc_seg_p'_ex_dec]: the lane's deliverable chain is
     [elem_of_choose] -> [palt_cands] -> [alts_cands_p] -> [cs_canon_p]
     -> [sessp_pro_len] -> [disc_seg_p'_dec] -> [disc_p_dec].  This also
     supersedes, for the whole predicate, [PipeDisc]'s parenthetical
     "[disc_seg_p'] is NOT claimed decidable: the search over the
     resolutions [EchoDisc] can run needs a bound on [sel]" -- the bound
     on [sel] is [palt_ok]'s own two conditions, and [choose] is it. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list list_numbers bitvector.definitions.
Require Import RiscvLang.        (* [mobs] *)
Require Import LineWords.
Require Import EchoDisc.         (* [pro_cands], [pro_canon], [nlines_max] *)
Require Import PipeDisc.
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(* ====================================================================== *)
(*  0.  ONE SMALL LIST FACT                                                *)
(* ====================================================================== *)

(* the out-of-range reading of [!!!] is [0], so a pointwise map that fixes
   [0] commutes with it *)
Lemma pdd_lookup_total_fmap (f : nat -> nat) (l : list nat) (i : nat) :
  f 0%nat = 0%nat -> (f <$> l) !!! i = f (l !!! i).
Proof using.
  intro Hf. rewrite !list_lookup_total_alt list_lookup_fmap.
  destruct (l !! i) as [x |]; cbn; [reflexivity | by rewrite Hf].
Qed.

Ltac pdd_elem :=
  solve [ repeat first [ apply elem_of_list_here | apply elem_of_list_further ] ].

(* ====================================================================== *)
(*  1.  THE INTERLEAVINGS ONE [PBoth] ROUND ADMITS                         *)
(* ====================================================================== *)

(* EVERY SELECTOR OF LENGTH [n] WITH EXACTLY [k] [true]s, by recursion on
   the first entry.  At the one length the model admits this list has
   [C(33,17) > 10^9] entries: it is DEFINED so that the search space is
   finite and its membership law is PROVED, and it is never run. *)
Fixpoint choose (n k : nat) : list (list bool) :=
  match n with
  | 0%nat => if decide (k = 0%nat) then [[]] else []
  | S n' =>
      ((fun s => false :: s) <$> choose n' k)
      ++ (match k with
          | 0%nat => []
          | S k' => (fun s => true :: s) <$> choose n' k'
          end)
  end.

Lemma elem_of_choose (n k : nat) (sel : list bool) :
  sel ∈ choose n k <-> length sel = n /\ count_true sel = k.
Proof using.
  revert k sel. induction n as [| n IH]; intros k sel; cbn [choose].
  - case_decide as Hk.
    + rewrite elem_of_list_singleton. split.
      * intros ->. cbn [length count_true]. split; [reflexivity | lia].
      * intros [Hl _]. by apply nil_length_inv in Hl.
    + rewrite elem_of_nil. split; [done |].
      intros [Hl Hc]. apply nil_length_inv in Hl as ->.
      cbn [count_true] in Hc. lia.
  - rewrite elem_of_app. split.
    + intros [Hin | Hin].
      * apply elem_of_list_fmap in Hin as (s & -> & Hs).
        apply IH in Hs as [Hl Hc]. cbn [length count_true]. split; lia.
      * destruct k as [| k']; [by apply elem_of_nil in Hin |].
        apply elem_of_list_fmap in Hin as (s & -> & Hs).
        apply IH in Hs as [Hl Hc]. cbn [length count_true]. split; lia.
    + intros [Hl Hc]. destruct sel as [| b s]; [cbn [length] in Hl; lia |].
      cbn [length] in Hl. destruct b; cbn [count_true] in Hc.
      * destruct k as [| k']; [lia |]. right.
        apply elem_of_list_fmap. exists s. split; [reflexivity |].
        apply IH. split; lia.
      * left. apply elem_of_list_fmap. exists s. split; [reflexivity |].
        apply IH. split; lia.
Qed.

(* ====================================================================== *)
(*  2.  THE CODES ONE LINE ADMITS                                          *)
(* ====================================================================== *)

Definition palt_fix_cands (l : pline) : list palt :=
  match l with
  | LEcho _ => [PEcho 0%nat; PEcho 1%nat; PEcho 2%nat; PEcho 3%nat]
  | LPipe _ => [PEcho 3%nat; PRan; PExecL; PExecR; PPipe; PFork; PSilent]
  end.

(* the CANONICAL codes of the alternatives one line shape admits: the
   constant ones, and -- at a pipeline line -- one per admitted
   interleaving *)
Definition palt_cands (l : pline) : list nat :=
  (palt_code <$> palt_fix_cands l)
  ++ match l with
     | LEcho _ => []
     | LPipe _ =>
         (fun sel => palt_code (PBoth sel))
           <$> choose (length dg_execL + length dg_execR) (length dg_execL)
     end.

Lemma palt_fix_cands_ok l : Forall (palt_ok l) (palt_fix_cands l).
Proof using.
  destruct l as [ws | ws]; cbn [palt_fix_cands].
  - repeat (constructor; [cbn [palt_ok]; lia |]). constructor.
  - constructor; [reflexivity |].
    repeat (constructor; [exact I |]). constructor.
Qed.

(* COMPLETENESS: every alternative a line admits has its code in the
   list.  This is what keeps the decision procedure from being vacuously
   "no" -- and, with [palt_cands_both_LR] below, what says the [PBoth]
   branch of the enumerator is not empty. *)
Lemma palt_cands_alt l a : palt_ok l a -> palt_code a ∈ palt_cands l.
Proof using.
  intro H. rewrite /palt_cands elem_of_app.
  destruct l as [ws | ws]; destruct a as [k | | | | sel | | |];
    cbn [palt_ok] in H; try done.
  - left. apply elem_of_list_fmap. exists (PEcho k). split; [reflexivity |].
    cbn [palt_fix_cands].
    assert (Hk : k = 0%nat \/ k = 1%nat \/ k = 2%nat \/ k = 3%nat) by lia.
    destruct Hk as [-> | [-> | [-> | ->]]]; pdd_elem.
  - left. apply elem_of_list_fmap. exists (PEcho k). split; [reflexivity |].
    rewrite H. cbn [palt_fix_cands]. pdd_elem.
  - left. apply elem_of_list_fmap. exists PRan. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - left. apply elem_of_list_fmap. exists PExecL. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - left. apply elem_of_list_fmap. exists PExecR. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - right. apply elem_of_list_fmap. exists sel. split; [reflexivity |].
    apply elem_of_choose. exact H.
  - left. apply elem_of_list_fmap. exists PPipe. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - left. apply elem_of_list_fmap. exists PFork. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
  - left. apply elem_of_list_fmap. exists PSilent. split; [reflexivity |].
    cbn [palt_fix_cands]. pdd_elem.
Qed.

(* THE MEMBERSHIP LAW, both ways: the list holds exactly the canonical
   codes of the alternatives the line admits. *)
Lemma elem_of_palt_cands l c :
  c ∈ palt_cands l <-> palt_ok l (palt_of c) /\ c = palt_code (palt_of c).
Proof using.
  split.
  - rewrite /palt_cands elem_of_app. intros [Hin | Hin].
    + apply elem_of_list_fmap in Hin as (a & -> & Ha).
      rewrite !palt_of_code. split; [| reflexivity].
      exact (proj1 (Forall_forall _ _) (palt_fix_cands_ok l) a Ha).
    + destruct l as [ws | ws]; [by apply elem_of_nil in Hin |].
      apply elem_of_list_fmap in Hin as (sel & -> & Hsel).
      rewrite !palt_of_code. split; [| reflexivity].
      cbn [palt_ok]. by apply elem_of_choose.
  - intros [Hok Hc]. rewrite Hc. exact (palt_cands_alt l (palt_of c) Hok).
Qed.

Lemma palt_cands_canon l c :
  palt_ok l (palt_of c) -> palt_code (palt_of c) ∈ palt_cands l.
Proof using. exact (palt_cands_alt l (palt_of c)). Qed.

(* ANTI-VACUITY AT THE ONE BRANCH THAT CANNOT BE COMPUTED.  The
   interleaving that prints the left diagnostic and then the right one is
   in the enumerator -- proved through [palt_cands_alt] and
   [PipeDisc.sel_LR_ok], never by evaluating [choose] or a [PBoth] code
   (both of which are out of reach: [palt_code_both_big]). *)
Lemma palt_cands_both_LR (ws : list (list (bv 8))) :
  palt_code (PBoth sel_LR) ∈ palt_cands (LPipe ws).
Proof using. exact (palt_cands_alt _ _ (sel_LR_ok ws)). Qed.

(* ====================================================================== *)
(*  3.  THE RESOLUTION LISTS, LINE BY LINE                                 *)
(* ====================================================================== *)

Fixpoint alts_cands_p (ls : list pline) : list (list nat) :=
  match ls with
  | [] => [[]]
  | l :: ls' =>
      (fun p => fst p :: snd p)
        <$> List.list_prod (palt_cands l) (alts_cands_p ls')
  end.

Lemma elem_of_alts_cands_p (ls : list pline) (cs : list nat) :
  cs ∈ alts_cands_p ls <-> Forall2 (fun l c => c ∈ palt_cands l) ls cs.
Proof using.
  revert cs. induction ls as [| l ls IH]; intros cs; cbn [alts_cands_p].
  - rewrite elem_of_list_singleton. split.
    + intros ->. constructor.
    + intro H. by apply Forall2_nil_inv_l in H.
  - rewrite elem_of_list_fmap. split.
    + intros ([c cs'] & -> & Hp). cbn [fst snd].
      apply elem_of_list_In, in_prod_iff in Hp as [Hc Hcs].
      apply elem_of_list_In in Hc. apply elem_of_list_In, IH in Hcs.
      by constructor.
    + intro H. apply Forall2_cons_inv_l in H as (c & cs' & Hc & Hcs & ->).
      exists (c, cs'). split; [reflexivity |].
      apply elem_of_list_In, in_prod_iff. split.
      * by apply elem_of_list_In.
      * by apply elem_of_list_In, IH.
Qed.

Lemma alts_cands_p_alts_ok (I : list (bv 8)) (cs : list nat) :
  cs ∈ alts_cands_p (plines_of I) -> alts_ok_p I cs.
Proof using.
  rewrite elem_of_alts_cands_p /alts_ok_p. intro H.
  eapply Forall2_impl; [exact H |]. intros l c Hc.
  exact (proj1 (proj1 (elem_of_palt_cands l c) Hc)).
Qed.

(* ====================================================================== *)
(*  4.  THE CANONICAL RESOLUTION                                           *)
(* ====================================================================== *)

(* EVERY consumer of [cs] reads it through [palt_at], so replacing each
   entry by the canonical code of its own decoding moves nothing.  (The
   route "[palt_ok l (palt_of c)] forces [c = palt_code (palt_of c)]" is
   NOT available: [palt_of] accepts codes that are not [palt_code]'s
   values -- e.g. every [n] with [n mod 16 = 11] decodes to a [PBoth],
   while [palt_code (PBoth sel)] is [11 + 16 * bnum sel] and [bnum] is
   not onto.) *)
Definition pcode_canon (c : nat) : nat := palt_code (palt_of c).

Definition cs_canon_p (cs : list nat) : list nat := pcode_canon <$> cs.

Lemma pcode_canon_0 : pcode_canon 0%nat = 0%nat.
Proof using.
  rewrite /pcode_canon (palt_of_lt4 0%nat ltac:(lia)).
  exact (palt_code_echo_lt4 0%nat ltac:(lia)).
Qed.

Lemma cs_canon_p_at cs i : palt_at (cs_canon_p cs) i = palt_at cs i.
Proof using.
  rewrite /palt_at /cs_canon_p (pdd_lookup_total_fmap _ cs i pcode_canon_0).
  rewrite /pcode_canon. by rewrite palt_of_code.
Qed.

Lemma pro_idx_p_canon cs i : pro_idx_p (cs_canon_p cs) i = pro_idx_p cs i.
Proof using.
  induction i as [| i IH]; [reflexivity |].
  by rewrite !pro_idx_p_S IH cs_canon_p_at.
Qed.

Lemma alt_cont_p_canon ps cs bs i :
  alt_cont_p ps (cs_canon_p cs) bs i = alt_cont_p ps cs bs i.
Proof using.
  by rewrite /alt_cont_p cs_canon_p_at pro_idx_p_canon.
Qed.

Lemma alt_seq_p_canon ps cs bs q :
  alt_seq_p ps (cs_canon_p cs) bs q = alt_seq_p ps cs bs q.
Proof using.
  induction q as [| q IH]; [reflexivity |].
  by rewrite !alt_seq_p_S IH /alt_blk_p alt_cont_p_canon.
Qed.

Lemma sessp_canon ps cs I : sessp ps (cs_canon_p cs) I = sessp ps cs I.
Proof using. by rewrite /sessp alt_seq_p_canon. Qed.

Lemma alts_ok_p_cs_canon (I : list (bv 8)) (cs : list nat) :
  alts_ok_p I cs -> cs_canon_p cs ∈ alts_cands_p (plines_of I).
Proof using.
  rewrite /alts_ok_p elem_of_alts_cands_p /cs_canon_p. intro H.
  apply Forall2_fmap_r. eapply Forall2_impl; [exact H |].
  intros l c Hc. exact (palt_cands_canon l c Hc).
Qed.

Lemma disc_pt_all_p_canon ps cs seg :
  disc_pt_all_p ps cs seg -> disc_pt_all_p ps (cs_canon_p cs) seg.
Proof using.
  rewrite /disc_pt_all_p. intro H. eapply Forall_impl; [exact H |].
  intros p [H1 H2]. split.
  - by rewrite /pro_ok_p pro_idx_p_canon.
  - by rewrite /disc_pt_p sessp_canon.
Qed.

(* ====================================================================== *)
(*  5.  THE PROLOGUE BOUND, AT [pro_idx_p]                                 *)
(* ====================================================================== *)

(* EVERY ROUND THE TRANSCRIPT ENTERS IS ON THE WIRE, so the prologue
   search is bounded by the segment.  [EchoDisc.alt_seq_pro_len]'s
   statement at [palt_panic]; the panic alternative is [PEcho 3] at BOTH
   line shapes ([PipeDisc.palt_ok_pipe_panic]), which is why this is one
   case and not two. *)
Lemma alt_seq_p_pro_len ps cs bs q r :
  (r <= pro_idx_p cs q)%nat ->
  (length (pro_of (pro_from r ps))
   <= length (pro_of ps) + length (alt_seq_p ps cs bs q))%nat.
Proof using.
  revert r. induction q as [| q IH]; intros r Hr.
  - assert (r = 0%nat) by (cbn [pro_idx_p] in Hr; lia). subst r.
    cbn [pro_from]. lia.
  - rewrite alt_seq_p_S length_app.
    destruct (decide (r <= pro_idx_p cs q)%nat) as [Hle | Hgt].
    + pose proof (IH r Hle). lia.
    + assert (Hp : palt_panic (palt_at cs q) = true).
      { destruct (palt_panic (palt_at cs q)) eqn:E; [reflexivity |].
        exfalso. rewrite (pro_idx_p_Sn cs q E) in Hr. lia. }
      rewrite (pro_idx_p_Sp cs q Hp) in Hr.
      assert (Hre : r = S (pro_idx_p cs q)) by lia.
      rewrite /alt_blk_p /alt_cont_p Hp !length_app.
      cbn [length]. rewrite length_app Hre. lia.
Qed.

Lemma sessp_pro_len ps cs I r :
  (r <= pro_idx_p cs (nlines I))%nat ->
  (length (pro_of (pro_from r ps)) <= length (sessp ps cs I))%nat.
Proof using.
  intro Hr. rewrite sessp_length.
  pose proof (alt_seq_p_pro_len ps cs (bodies_of I) (nlines I) r Hr). lia.
Qed.

(* ====================================================================== *)
(*  6.  THE DECISION                                                       *)
(* ====================================================================== *)

(* [EchoDisc.disc_seg'_dec]'s search at the two enumerators: the
   resolutions off the lines ([alts_cands_p], through [cs_canon_p]) and
   the prologues off [pro_cands] (through [pro_canon], applied unchanged
   -- it never mentions [cs]).  NOTHING HERE IS MEANT TO RUN: the
   ledger cases on it. *)
Global Instance disc_seg_p'_dec seg : Decision (disc_seg_p' seg).
Proof using.
  destruct (decide (disc_seg_p seg)) as [Hd | Hd];
    [| right; by intros [? _]].
  destruct (decide (Exists (fun cs =>
      Exists (fun ps => disc_pt_all_p ps cs seg)
        (pro_cands (S (pro_idx_p cs (nlines_max (in_pres seg))))
                   (length seg)))
      (alts_cands_p (plines_of (ins seg))))) as [HE | HE].
  - left. apply Exists_exists in HE as (cs & Hcs & HP).
    apply Exists_exists in HP as (ps & _ & Hall).
    eapply disc_seg_p'_intro;
      [exact Hd | by apply alts_cands_p_alts_ok | exact Hall].
  - right. intros [_ (ps & cs & Hao & Hall)]. apply HE.
    apply Exists_exists. exists (cs_canon_p cs).
    split; [by apply alts_ok_p_cs_canon |].
    rewrite pro_idx_p_canon. apply Exists_exists.
    (* the deepest checked point bounds every round the transcript enters *)
    destruct (decide (in_pres seg = [])) as [Hz | Hz].
    { destruct (pro_cands_nonempty
                  (S (pro_idx_p cs (nlines_max (in_pres seg)))) (length seg))
        as [g Hg].
      exists g. split; [exact Hg |]. rewrite /disc_pt_all_p Hz. constructor. }
    destruct (nlines_max_mem (in_pres seg) Hz) as (pl & Hplin & Hpleq).
    destruct (Hall pl Hplin) as [[HFps Hltl] Hptl].
    assert (Hplp : pl `prefix_of` seg)
      by exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) pl Hplin).
    destruct (pro_canon (S (pro_idx_p cs (nlines_max (in_pres seg))))
                (length seg) ps HFps) as (ps0 & Hin0 & Hrd0 & Hag0).
    { intros r Hr. rewrite -Hpleq in Hr. split; [lia |].
      etrans; [apply (sessp_pro_len ps cs (ins pl) r); lia |].
      etrans; [apply prefix_length, Hptl |].
      etrans; [apply obs_wire_length |].
      exact (prefix_length _ _ Hplp). }
    exists ps0. split; [exact Hin0 |].
    apply disc_pt_all_p_canon.
    rewrite /disc_pt_all_p. apply Forall_forall. intros p Hp.
    destruct (Hall p Hp) as [[_ Hltp] Hptp].
    assert (Hidxle : (pro_idx_p cs (nlines (ins p))
                      <= pro_idx_p cs (nlines_max (in_pres seg)))%nat)
      by (apply pro_idx_p_mono, nlines_max_ge, Hp).
    assert (Hsame : sessp ps0 cs (ins p) = sessp ps cs (ins p)).
    { apply sessp_ps_ext. intros r Hr. apply Hag0. lia. }
    split.
    + rewrite /pro_ok_p. split; [by eapply pro_cands_Forall | lia].
    + by rewrite /disc_pt_p Hsame.
Defined.

(* THE DELIVERABLE.  The pipeline discipline is decidable, so the
   pipeline ledger's taint counter reads [decide (disc_p h)] and lane
   PIPE-STAGE's [AppPipe.v] takes no [Decision] hypothesis. *)
(* OPAQUE ON PURPOSE, as [EchoDisc.disc_dec] and [FileDiscDec.disc_f_dec]
   are: the ledger's counter is [if decide (disc_p h) then 0 else 1] and
   every proof that touches it rewrites with a closure law.  A transparent
   instance would let ssreflect's [rewrite /pipe_led] iota-reduce the
   counter at a literal history and those rewrites would stop matching
   (FILE-DEC's finding, worth not re-discovering). *)
Global Instance disc_p_dec h : Decision (disc_p h).
Proof using. rewrite /disc_p. apply _. Qed.

(* ====================================================================== *)
(*  7.  THE ASSUMPTION CHECK                                              *)
(*                                                                        *)
(*  Iris-free and axiom-free.  All four print exactly Closed under the     *)
(*  global context (checked 2026-09-18 on the lane's mirror):              *)
(*                                                                        *)
(*    Print Assumptions elem_of_choose.                                    *)
(*    Print Assumptions elem_of_palt_cands.                                *)
(*    Print Assumptions disc_seg_p'_dec.                                   *)
(*    Print Assumptions disc_p_dec.                                        *)
(* ====================================================================== *)
