(* AppTree.v -- THE TREE APPLICATION: a process's subtree of the live
   namespace, owned as a CLAIM IN THE APPLICATION INVARIANT.

   Design of record: claude-notes/design/user-tree.md (TL-0), lane TL-2,
   on TL-1's pure layer [TreeView.v].  [AppEcho.v] is the mould: its
   claim [echo_taint ∨ (⌜echo_fs_pure av⌝ ∗ cons_state)] is the WHOLE-FS
   special case of this one, and every shape below -- the taint arm, the
   claim law that hands the claim back, the per-delta step wands, the
   transport, the supply -- is echo's at a per-owner ownership map.

   THE CLAIM (design section 2).  [tree_pred c r av] is TAINTED or: the
   application holds the AUTHORITY of an ownership map [own : gmap gname
   (Z * ttree)] -- generation [g] owns the subtree [t] at the root [root]
   -- the map is WELL FORMED at the view ([TreeView.own_wf]: the view is
   tree-shaped, every root is a directory, the roots are pairwise
   non-nested) and it is EXACT: every entry's recorded tree IS the view's
   subtree at its root ([tree_exact]).  A process holds the map ELEMENT
   [tree_own r g root t = g ↪[r] (root, t)], and reads its own subtree off
   the claim by [ghost_map_lookup] -- the stable form
   design/fs-syscall-specs.md section 2 wanted, as a claim rather than as
   a fraction (design/user-exec.md's EX-2 is the refutation of the
   fraction).

   TWO DEVIATIONS FROM THE DESIGN PAGE'S SKETCH, both simplifications:
   (1) the authority is WHOLE ([ghost_map_auth r 1]) and not a half.  The
       half in the sketch was copied off [AppInv.app_body]'s tie to the
       kernel's map, where the OTHER half is the kernel's; here nobody
       else holds one, and an owner's move is a [ghost_map_update], which
       needs the whole.  (2) the claim's third conjunct is the PURE
       [tree_exact] rather than a [[∗ map]] of pure facts -- the same
       proposition, one [iDestruct] cheaper.

   ============ THE THREE FINDINGS, and what they cost ============

   FINDING 1 (THE SEAM, and the brief's STOP rule).  An OWNER'S OWN MOVE
   CANNOT BE PAID AT THE FIRE, because [AppInv.app_top_update_step]'s --
   and [AppInv.app_step]'s -- step is an UPDATE-FREE wand
   ([app_pred av -∗ app_pred av'], applied under the invariant's later),
   and moving an owner's recorded subtree is a GHOST MAP UPDATE.  There
   is no way around it inside the tree layer:
     - a plain wand can TRANSFER resources but cannot run a frame-
       preserving update, and any change of recorded ghost information is
       one;
     - wrapping the claim in [|==>] makes the wand able to update, but
       then the CLAIM LAW is unprovable: a pure fact cannot be read out
       from under a basic update;
     - a WINDOW (desync at a claim-update before the call, resync at one
       after it, echo's mknod two-phase shape) re-establishes nothing: at
       the resync the owner must prove [subtree av root = Some t_new] at
       the invariant's CURRENT view, which only the party that SEES the
       move -- the step wand -- knows.  Whatever the window records, the
       ambiguity "did my commit fire?" survives it.
   So the owner's moves land here in their TRUE shape, as BASIC UPDATES
   ([tree_move_write], [tree_move_create], [tree_move_unl_ent]): the
   whole tree content is proved (disjointness, [own_wf] preservation, the
   INSIDE and OUTSIDE delta lemmas), and what is left over is ONE shape
   mismatch.  Closing it is an [AppInv] seam and not a tree-layer proof:
   [app_step] would have to be [▷ app_pred av ==∗ ▷ app_pred av'] (and
   [app_top_update] can already take it -- it applies the step inside its
   own fupd), which moves every fire site.  That is TL-3's/an AppInv
   lane's decision, recorded in design/user-tree.md section 6.

   FINDING 2 (exec's (W)).  [PinnedObs.pin_resolves_at] -- what
   [ExecRun.exec_walk_of_pin] and [pobs_walk] take -- pins the walk's
   terminal row as an [anode], LINK COUNT INCLUDED.  The tree claim pins
   a node's CONTENT and not its count (TL-1's ruling: [absnode], nlink
   dropped), so [subtree_resolves_pin_file] yields the row only up to an
   EXISTENTIAL count and the pin is unsuppliable AS STATED.  Nothing in
   the walk needs the count ([pobs_hop] reads only the [arun] conjunct);
   it is the terminal IDENTIFICATION ([pobs_node], [ExecBundle.
   ex_node_id]) that asks for the row on the nose.  So [exec_walk_of_own]
   is NOT landed; what is landed is everything on this side of the seam:
   the claim law in both shapes, and [tree_resolves_abs], the pin's
   content at an existential count, ready for an absnode-level
   [pin_resolves_abs] / [ex_node_id] variant (additive, one definition
   each in [PinnedObs.v] and [ExecRun.v]).

   FINDING 3 (grant).  A parent CANNOT keep a hole-punched subtree: the
   claim is EXACT ("my subtree IS [t]") and [own_wf] wants the roots
   pairwise NON-NESTED, so design section 3's "[t_P] at [root_P] becomes
   [t_P ∖ t_C] plus a new entry" is not expressible over TL-1's
   [subtree].  What IS expressible, and what [tree_grant] below is, is
   the HAND-DOWN: the parent's entry is retired and the child's entry at
   a sub-root of it is born.  A hole-punched partition needs a new PURE
   reading in TL-1 ([subtree_except av root R]) and a disjointness
   theorem at it.

   FINDING 4 (THE ERA'S FIRST DEED HAS NO CHANNEL).  Nobody can mint a
   deed at "/" out of a running claim: the insert needs the new root to
   be NON-NESTED with every existing root, which at "/" means the
   ownership map is EMPTY -- and the claim cannot see that its own map
   is empty (a reader holds no deed, and there is no "the partition is
   empty" credential).  Nor can [Happ_init] hand one over: its
   conclusion has no room beside the claim, and App.v's own note says
   its instance never reaches a boot -- every era founds from the
   TRANSPORT's clone.  So the first deed must ride [App.app_boot], which
   the transport CAN build, because the view is available OUTSIDE the
   later (echo's [cons_inum av] trick decides the arm there): allocate
   the fresh map at [{[ g := (ROOTINO, t) ]}] when [subtree av ROOTINO =
   Some t].  WHAT BLOCKS IT is the OTHER arm: [app_boot] is av-FREE, and
   "this view has no root directory" has no av-free spelling, so the
   disjunction collapses to [emp].  THE FIX, priced: the claim grows one
   conjunct, [⌜adir_at av ROOTINO⌝] (or [is_Some (subtree av ROOTINO)]),
   which every landed leg preserves -- a fresh inum is not the root, a
   write/truncate is at a FILE row, and create's and unlink's entry legs
   leave a directory a directory -- and then the transport's None arm is
   refuted from the claim it was handed.  [tree_init_at] below is the
   mint at a FRESH instance, which is the era-0 shape but not the era's.
   Until that conjunct lands, [app_boot] here is [emp] and the tree
   application's owners are the ones a future [tree_grant] hands down
   from the first.

   WHAT ELSE IS OWED, and to whom:
     - [own_wf_ent] (create's PARENT leg alone) and the
       last-link [own_wf] for [delta_unl_tgt] at a row that is nobody's
       root: TL-1 landed [own_wf_write] / [own_wf_create] (FUSED) /
       [own_wf_arm] / [own_wf_unl_ent] / [own_wf_unl_tgt], so the moves
       below are write, truncate, the fused create, and unlink's entry
       leg -- [own_wf_trunc] is proved HERE, in section 1f', because it
       is [own_wf_write]'s twin line for line and TL-3 wants the move;
       it belongs in TreeView.v and moves there when a TL-1 lane runs.
       The PER-LEG create (its parent leg alone) is a harder one: it
       needs an [aview_tree_wf_ent], whose unique-parenthood conjunct
       wants "nothing else names the armed inum".
     - the unlink TARGET leg at the last link needs "the row is nobody's
       root" -- design section 3's "an owner never unlinks a root" --
       which is a fact about the HIDDEN ownership map that no mover
       holds.  It is payable only as a strengthening of the claim (every
       root is named, or is [ROOTINO]); recorded, not taken.
     - the ledger [app_R] below is a PLACEHOLDER that carries the taint
       counter and never bumps it, so the taint is not mintable and the
       SUPPLY (hence the generic slot) is unobtainable at this record.
       TL-4 gives it echo's shape: the step that reads the discipline is
       where an unpaid move is recorded.

   WHAT IS DELIBERATELY NOT HERE: a theorem.  [Happ_init] at the image's
   view is gated on a pure fact about the mkfs image ([aview_tree_wf]),
   and [Hinit_boot] is the first process's exec bundle -- TL-4's, both.
   The application is a DEFINITION with its obligations as free-standing
   lemmas (durable-notes.md's GAP-premise rule), exactly as [AppEcho]
   leaves its two. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map mono_nat invariants.
Require Import RiscvLang.        (* [mobs] *)
Require Import ObsTrace.         (* [trace_shape], [obs_boots], [ObsPowerOn] *)
Require Import PathElems.        (* [path_elems] *)
Require Import FsTree.           (* [fname], [fs_proper] *)
Require Import FsAbsDefs.        (* [aview], [anode], [absnode], [abs_view] *)
Require Import FsAbsDelta.       (* the landed delta legs *)
Require Import FsImg.            (* [ROOTINO]: the era's root inum, as a [Z] *)
Require Import TreeView.         (* TL-1: [subtree], [own_wf], the deltas *)
Require Import AppInv.           (* [app_sup_raw], [app_xfer_raw] *)
Require ConsLog.               (* [cons_step] / [cons_ev]: the merged console claim's event type *)
Require Import SystemAdequacy.   (* [app_xfer_boot_raw]: [App.Happ_boot] *)
Require Import RiscvPtsto.       (* [app_iface_triv]: the interface a
                                    tree application sets *)
Require Import App.              (* [xv6_app], [MkApp] *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  0.  THE GHOST CLASS                                                   *)
(* ===================================================================== *)

(* ONE class, bundling the two cameras the claim is made of: the taint
   counter (echo's [mono_nat], for the same reason -- a counter that has
   left 0 can never come back, so its lower bound is a permanent,
   persistent fact) and the ownership map. *)
Class treeG (Σ : gFunctors) := TreeG {
  tr_mono_nat : mono_natG Σ;
  tr_own_map  : ghost_mapG Σ gname (Z * ttree);
}.
Global Existing Instance tr_mono_nat.
Global Existing Instance tr_own_map.

Definition treeΣ : gFunctors :=
  #[ mono_natΣ; ghost_mapΣ gname (Z * ttree) ].

Global Instance subG_treeΣ {Σ} : subG treeΣ Σ -> treeG Σ.
Proof. solve_inG. Qed.

(* ===================================================================== *)
(*  1.  THE PURE SIDE: exactness, and what the deltas do to it            *)
(*                                                                       *)
(*  ZERO Iris in this section: it is TL-1's layer, read at the ownership  *)
(*  map the claim carries.  Every step wand below is one of these lemmas  *)
(*  plus [tree_step_gen] / [tree_move_gen].                               *)
(* ===================================================================== *)

(* THE CLAIM'S THIRD CONJUNCT: every entry's recorded tree IS the view's
   subtree at its root. *)
Definition tree_exact (av : aview) (own : gmap gname (Z * ttree)) : Prop :=
  forall (g : gname) (root : Z) (t : ttree),
    own !! g = Some (root, t) -> subtree av root = Some t.

(* ---- 1a'.  THE CLAIM'S FOURTH CONJUNCT: "/" IS A DIRECTORY ---------- *)
(*                                                                       *)
(*  design/user-tree.md section 6, TL-2's FINDING 4, and TL-3's landing   *)
(*  of its price.  The era's FIRST deed has to be minted by the TRANSPORT *)
(*  ([App.app_boot]), which sees the view OUTSIDE the later and can       *)
(*  therefore decide [subtree av ROOTINO]; what it cannot do is answer the *)
(*  OTHER arm, because [app_boot] is av-FREE and "this view has no root   *)
(*  directory" has no av-free spelling.  So the claim carries             *)
(*  [⌜adir_at av ROOTINO⌝] and the transport REFUTES that arm from the    *)
(*  claim it was handed ([tree_xfer_boot_at] below).                      *)
(*                                                                       *)
(*  AND IT IS FREE AT EVERY LEG, because it is the roots conjunct of      *)
(*  [own_wf] at the partition that owns "/" and nothing else: each        *)
(*  preservation below is TL-1's own [own_wf_*] lemma at [root_own].      *)
(*  (Which is also the honest reading of the conjunct: the claim says the *)
(*  era has a root, exactly as an owner's entry says its own root is a    *)
(*  directory.) *)

Definition root_own : gmap gname (Z * ttree) :=
  {[ 1%positive := (FsImg.ROOTINO, MkTTree ∅ 0) ]}.

Lemma own_wf_root (av : aview) :
  aview_tree_wf av -> adir_at av FsImg.ROOTINO -> own_wf av root_own.
Proof.
  intros Hwf Hd. rewrite /root_own. split_and!; [exact Hwf | ..].
  - intros g r t Hg. destruct (decide (g = 1%positive)) as [-> | Hne].
    + rewrite lookup_singleton in Hg. injection Hg as <- <-. exact Hd.
    + rewrite lookup_singleton_ne in Hg; [discriminate | congruence].
  - intros g1 g2 r1 t1 r2 t2 Hne H1 H2. exfalso.
    destruct (decide (g1 = 1%positive)) as [-> | H1e].
    + destruct (decide (g2 = 1%positive)) as [-> | H2e]; [exact (Hne eq_refl) |].
      rewrite lookup_singleton_ne in H2; [discriminate | congruence].
    + rewrite lookup_singleton_ne in H1; [discriminate | congruence].
Qed.

Lemma root_of_own_wf (av : aview) :
  own_wf av root_own -> adir_at av FsImg.ROOTINO.
Proof.
  intros (_ & Hroots & _).
  apply (Hroots 1%positive FsImg.ROOTINO (MkTTree ∅ 0)).
  rewrite /root_own lookup_singleton //.
Qed.

(* the root's reading, which is what the transport actually wants *)
Lemma subtree_root_of_claim (av : aview) :
  adir_at av FsImg.ROOTINO ->
  subtree av FsImg.ROOTINO
  = Some (MkTTree (subtree_nodes av FsImg.ROOTINO) FsImg.ROOTINO).
Proof. exact (subtree_of_dir av FsImg.ROOTINO). Qed.

(* ---- 1a.  the two congruences: a move the PROJECTION does not see ---- *)

Lemma own_wf_cong (av av' : aview) (own : gmap gname (Z * ttree)) :
  tview av' = tview av -> own_wf av own -> own_wf av' own.
Proof.
  intros Hv ((Hu & Hcl) & Hroots & Hnn). split_and!.
  - split.
    + rewrite /aview_uniq_parent Hv. exact Hu.
    + rewrite aview_closed_nstep Hv. by rewrite -aview_closed_nstep.
  - intros g r t Hg. apply adir_at_tview. rewrite Hv.
    apply adir_at_tview. exact (Hroots g r t Hg).
  - intros g g' r t r' t' Hne Hg Hg'. rewrite Hv.
    exact (Hnn g g' r t r' t' Hne Hg Hg').
Qed.

Lemma tree_exact_cong (av av' : aview) (own : gmap gname (Z * ttree)) :
  tview av' = tview av -> tree_exact av own -> tree_exact av' own.
Proof.
  intros Hv Hex g root t Hg. rewrite (subtree_cong av' av root Hv).
  exact (Hex g root t Hg).
Qed.

(* ---- 1b.  DISJOINTNESS, as the movers read it ----------------------- *)

(* THE ONE FACT EVERY OWNER'S MOVE TURNS ON: a node of MY tree is outside
   every other owner's reach.  [TreeView.subtree_disjoint] with the claim's
   own exactness supplying the two subtrees. *)
Lemma tree_disjoint_out (av : aview) (own : gmap gname (Z * ttree))
    (g g' : gname) (root root' d : Z) (t t' : ttree) :
  own_wf av own -> tree_exact av own ->
  own !! g = Some (root, t) -> own !! g' = Some (root', t') -> g <> g' ->
  d ∈ dom (tv_nodes t) -> ~ nreach (tview av) root' d.
Proof.
  intros Hwf Hex Hg Hg' Hne Hd Hr.
  pose proof (Hex g root t Hg) as Ht.
  pose proof (subtree_nodes_eq av root t Ht) as Hnodes.
  assert (Hdom : d ∈ dom av).
  { rewrite Hnodes in Hd. by apply elem_of_dom_subtree_nodes in Hd as [Hd _]. }
  assert (Hin : d ∈ dom (subtree_nodes av root)) by (rewrite -Hnodes; exact Hd).
  assert (Hin' : d ∈ dom (subtree_nodes av root'))
    by (apply elem_of_dom_subtree_nodes; split; assumption).
  pose proof (subtree_disjoint av own g g' root root' t t' Hwf Hne Hg Hg') as Hdis.
  rewrite elem_of_disjoint in Hdis. exact (Hdis d Hin Hin').
Qed.

(* ...and the same at the OWNER'S OWN root: a node it does not have is
   one it does not reach. *)
Lemma tree_not_in_own (av : aview) (root d : Z) (t : ttree) :
  subtree av root = Some t -> d ∈ dom av -> d ∉ dom (tv_nodes t) ->
  ~ nreach (tview av) root d.
Proof.
  intros Ht Hdom Hd Hr. apply Hd.
  rewrite (subtree_nodes_eq av root t Ht).
  apply elem_of_dom_subtree_nodes. split; assumption.
Qed.

(* ---- 1c.  [own_wf] does not read the TREES ------------------------- *)

(* an entry's recorded tree may be replaced at will: every conjunct of
   [own_wf] reads the ROOTS and the view, and nothing else.  (It is what
   makes an owner's move ONE [ghost_map_update] and no [own_wf] work.) *)
Lemma own_wf_retree (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root : Z) (t t' : ttree) :
  own !! g = Some (root, t) -> own_wf av own ->
  own_wf av (<[g := (root, t')]> own).
Proof.
  intros Hg (Hwf & Hroots & Hnn).
  assert (Hlk : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             <[g := (root, t')]> own !! g0 = Some (r0, t0) ->
             exists t1, own !! g0 = Some (r0, t1)).
  { intros g0 r0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
    - rewrite lookup_insert in H0. injection H0 as <- <-. by exists t.
    - rewrite lookup_insert_ne in H0; [| congruence]. by exists t0. }
  split_and!; [exact Hwf | ..].
  - intros g0 r0 t0 H0. destruct (Hlk g0 r0 t0 H0) as (t1 & H1).
    exact (Hroots g0 r0 t1 H1).
  - intros g1 g2 r1 t1 r2 t2 Hne H1 H2.
    destruct (Hlk g1 r1 t1 H1) as (u1 & K1).
    destruct (Hlk g2 r2 t2 H2) as (u2 & K2).
    exact (Hnn g1 g2 r1 u1 r2 u2 Hne K1 K2).
Qed.

(* ---- 1d.  the INVISIBLE legs: nothing in the tree moves ------------- *)

Lemma tree_root_cong (av av' : aview) :
  tview av' = tview av ->
  adir_at av FsImg.ROOTINO -> adir_at av' FsImg.ROOTINO.
Proof.
  intros Hv Hd. apply adir_at_tview. rewrite Hv. by apply adir_at_tview.
Qed.

Lemma tree_pres_cong (av av' : aview) (own : gmap gname (Z * ttree)) :
  tview av' = tview av ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf av' own /\ tree_exact av' own /\ adir_at av' FsImg.ROOTINO.
Proof.
  intros Hv Hwf Hex Hr.
  split_and!; [exact (own_wf_cong av av' own Hv Hwf)
              | exact (tree_exact_cong av av' own Hv Hex)
              | exact (tree_root_cong av av' Hv Hr)].
Qed.

(* ---- 1e.  create's ARM leg: a fresh inum is nobody's ---------------- *)

Lemma tree_pres_arm (av : aview) (own : gmap gname (Z * ttree))
    (i : Z) (c : absnode) :
  av !! i = None -> tabs_leaf (tabs_of c) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_arm i c av) own /\ tree_exact (delta_arm i c av) own
  /\ adir_at (delta_arm i c av) FsImg.ROOTINO.
Proof.
  intros Hi Hleaf Hwf Hex Hr.
  pose proof Hwf as (Hcl & Hroots & _).
  split; [exact (own_wf_arm av own i c Hi Hleaf Hwf) |].
  split; [| apply root_of_own_wf;
             exact (own_wf_arm av root_own i c Hi Hleaf
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g root t Hg.
  assert (Hne : i <> root).
  { intros Heq. rewrite Heq in Hi.
    pose proof (adir_at_dom av root (Hroots g root t Hg)) as Hd.
    apply elem_of_dom in Hd as [a Ha]. congruence. }
  rewrite (subtree_delta_arm_fresh av root i c (proj2 Hcl) Hi Hne).
  exact (Hex g root t Hg).
Qed.

(* ---- 1f.  the OWNER'S OWN legs ------------------------------------- *)

Lemma tree_pres_write (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root i : Z) (t : ttree) (off : nat)
    (new bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  own !! g = Some (root, t) -> i ∈ dom (tv_nodes t) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_write i off new av) (<[g := (root, top_write i off new t)]> own)
  /\ tree_exact (delta_write i off new av)
       (<[g := (root, top_write i off new t)]> own)
  /\ adir_at (delta_write i off new av) FsImg.ROOTINO.
Proof.
  intros Hi Hg Hd Hwf Hex Hr.
  pose proof (Hex g root t Hg) as Ht.
  split.
  { apply (own_wf_retree _ _ g root t); [exact Hg |].
    exact (own_wf_write av own i off new bs0 nl Hi Hwf). }
  split; [| apply root_of_own_wf;
             exact (own_wf_write av root_own i off new bs0 nl Hi
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g0 root0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
  - rewrite lookup_insert in H0. injection H0 as <- <-.
    exact (subtree_delta_write av root i t off new bs0 nl Ht Hi Hd).
  - rewrite lookup_insert_ne in H0; [| congruence].
    rewrite (subtree_delta_write_out av root0 i off new
               (tree_disjoint_out av own g g0 root root0 i t t0
                  Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hd)).
    exact (Hex g0 root0 t0 H0).
Qed.

Lemma tree_pres_create (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root d : Z) (nm : fname) (i : Z) (c : absnode)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  fs_pname nm ->
  av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
  av !! i = None -> tabs_leaf (tabs_of c) ->
  own !! g = Some (root, t) -> d ∈ dom (tv_nodes t) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_create d nm i c av)
    (<[g := (root, top_ins d nm i (tabs_of c) t)]> own)
  /\ tree_exact (delta_create d nm i c av)
       (<[g := (root, top_ins d nm i (tabs_of c) t)]> own)
  /\ adir_at (delta_create d nm i c av) FsImg.ROOTINO.
Proof.
  intros Hnm Hd Hnone Hi Hleaf Hg Hdd Hwf Hex Hr.
  pose proof (Hex g root t Hg) as Ht.
  pose proof Hwf as (Hcl & Hroots & _).
  split.
  { apply (own_wf_retree _ _ g root t); [exact Hg |].
    exact (own_wf_create av own d nm i c e nl Hnm Hd Hi Hleaf Hwf). }
  split; [| apply root_of_own_wf;
             exact (own_wf_create av root_own d nm i c e nl Hnm Hd Hi Hleaf
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g0 root0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
  - rewrite lookup_insert in H0. injection H0 as <- <-.
    exact (subtree_delta_create av root d nm i c t e nl Ht Hnm Hd Hnone Hi
             Hleaf Hdd).
  - rewrite lookup_insert_ne in H0; [| congruence].
    assert (Hfresh : ~ nreach (tview av) root0 i).
    { assert (Hne0 : i <> root0).
      { intros Heq. rewrite Heq in Hi.
        pose proof (adir_at_dom av root0 (Hroots g0 root0 t0 H0)) as Hdm.
        apply elem_of_dom in Hdm as [a Ha]. congruence. }
      exact (nreach_fresh av root0 i (proj2 Hcl) Hi Hne0). }
    rewrite (subtree_delta_create_out av root0 d nm i c
               (tree_disjoint_out av own g g0 root root0 d t t0
                  Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hdd)
               Hfresh).
    exact (Hex g0 root0 t0 H0).
Qed.

Lemma tree_pres_unl_ent (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root d : Z) (nm : fname) (dec : nat)
    (t : ttree) (e : gmap fname Z) (nl : nat) :
  av !! d = Some (MkAnode (ADir e) nl) ->
  own !! g = Some (root, t) -> d ∈ dom (tv_nodes t) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_unl_ent d nm dec av) (<[g := (root, top_unlink d nm t)]> own)
  /\ tree_exact (delta_unl_ent d nm dec av)
       (<[g := (root, top_unlink d nm t)]> own)
  /\ adir_at (delta_unl_ent d nm dec av) FsImg.ROOTINO.
Proof.
  intros Hd Hg Hdd Hwf Hex Hr.
  pose proof (Hex g root t Hg) as Ht.
  split.
  { apply (own_wf_retree _ _ g root t); [exact Hg |].
    exact (own_wf_unl_ent av own d nm dec e nl Hd Hwf). }
  split; [| apply root_of_own_wf;
             exact (own_wf_unl_ent av root_own d nm dec e nl Hd
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g0 root0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
  - rewrite lookup_insert in H0. injection H0 as <- <-.
    exact (subtree_delta_unl_ent av root d nm dec t e nl Ht Hd Hdd).
  - rewrite lookup_insert_ne in H0; [| congruence].
    rewrite (subtree_delta_unl_ent_out av root0 d nm dec
               (tree_disjoint_out av own g g0 root root0 d t t0
                  Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hdd)).
    exact (Hex g0 root0 t0 H0).
Qed.

(* ---- 1f'.  TRUNCATE ------------------------------------------------
   [own_wf_trunc] MOVED to [TreeView.v]'s section 7c (lane TL-3's
   housekeeping), where it belongs and where TL-2's own note said it would
   go: it is [own_wf_write]'s twin line for line and reads no Iris.  Only
   the move below is left here. *)

Lemma tree_pres_trunc (av : aview) (own : gmap gname (Z * ttree))
    (g : gname) (root i : Z) (t : ttree) (bs0 : list (bv 8)) (nl : nat) :
  av !! i = Some (MkAnode (AFile bs0) nl) ->
  own !! g = Some (root, t) -> i ∈ dom (tv_nodes t) ->
  own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
  own_wf (delta_trunc i av) (<[g := (root, top_trunc i t)]> own)
  /\ tree_exact (delta_trunc i av) (<[g := (root, top_trunc i t)]> own)
  /\ adir_at (delta_trunc i av) FsImg.ROOTINO.
Proof.
  intros Hi Hg Hd Hwf Hex Hr.
  pose proof (Hex g root t Hg) as Ht.
  split.
  { apply (own_wf_retree _ _ g root t); [exact Hg |].
    exact (own_wf_trunc av own i bs0 nl Hi Hwf). }
  split; [| apply root_of_own_wf;
             exact (own_wf_trunc av root_own i bs0 nl Hi
                      (own_wf_root av (proj1 Hwf) Hr)) ].
  intros g0 root0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
  - rewrite lookup_insert in H0. injection H0 as <- <-.
    exact (subtree_delta_trunc av root i t bs0 nl Ht Hi Hd).
  - rewrite lookup_insert_ne in H0; [| congruence].
    rewrite (subtree_delta_trunc_out av root0 i
               (tree_disjoint_out av own g g0 root root0 i t t0
                  Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hd)).
    exact (Hex g0 root0 t0 H0).
Qed.

(* ---- 1g.  THE HAND-DOWN (finding 3) --------------------------------- *)

(* the child's root is a directory of the view: it is a DIRECTORY ROW OF
   THE PARENT'S TREE, and the parent's tree is the view's own closure. *)
Lemma tree_sub_dir (av : aview) (root root' : Z) (t : ttree)
    (e : gmap fname Z) :
  subtree av root = Some t -> tv_nodes t !! root' = Some (ADir e) ->
  adir_at av root'.
Proof.
  intros Ht Hr'.
  assert (Hreach : nreach (tview av) root root').
  { apply (subtree_dom_reach av root t root' Ht). apply elem_of_dom. by exists (ADir e). }
  apply adir_at_tview. exists e.
  rewrite (subtree_nodes_eq av root t Ht) /subtree_nodes
    (nclose_lookup_in (tview av) root root' Hreach) in Hr'. exact Hr'.
Qed.

Lemma tree_pres_grant (av : aview) (own : gmap gname (Z * ttree))
    (g g' : gname) (root root' : Z) (t t' : ttree) (e : gmap fname Z) :
  own !! g = Some (root, t) -> own !! g' = None ->
  tv_nodes t !! root' = Some (ADir e) ->
  subtree av root' = Some t' ->
  own_wf av own -> tree_exact av own ->
  own_wf av (<[g' := (root', t')]> (delete g own))
  /\ tree_exact av (<[g' := (root', t')]> (delete g own)).
Proof.
  intros Hg Hg' Hr' Ht' Hwf Hex.
  pose proof (Hex g root t Hg) as Ht.
  pose proof Hwf as (Hwf0 & Hroots & Hnn).
  assert (Hdom' : root' ∈ dom (tv_nodes t))
    by (apply elem_of_dom; by exists (ADir e)).
  assert (Hreach : nreach (tview av) root root')
    by exact (subtree_dom_reach av root t root' Ht Hdom').
  (* the two halves of NON-NESTING at the child's root, and both are
     TL-1's theorem: the child sits inside the parent, so a stranger that
     reached it would share a node with the parent, and a stranger the
     CHILD reached would be one the PARENT reached. *)
  assert (Hout : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g -> own !! g0 = Some (r0, t0) ->
             ~ nreach (tview av) r0 root').
  { intros g0 r0 t0 Hne H0.
    exact (tree_disjoint_out av own g g0 root r0 root' t t0
             Hwf Hex Hg H0 (fun Hc => Hne (eq_sym Hc)) Hdom'). }
  assert (Hout2 : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g -> own !! g0 = Some (r0, t0) ->
             ~ nreach (tview av) root' r0).
  { intros g0 r0 t0 Hne H0 Hc.
    exact (Hnn g g0 root t r0 t0 (fun Hc0 => Hne (eq_sym Hc0)) Hg H0
             (nreach_trans (tview av) root root' r0 Hreach Hc)). }
  assert (Hlk : forall (g0 : gname) (r0 : Z) (t0 : ttree),
             g0 <> g' -> <[g' := (root', t')]> (delete g own) !! g0 = Some (r0, t0) ->
             g0 <> g /\ own !! g0 = Some (r0, t0)).
  { intros g0 r0 t0 Hne H0. rewrite lookup_insert_ne in H0; [| congruence].
    destruct (decide (g0 = g)) as [-> | Hg0].
    - rewrite lookup_delete in H0. discriminate.
    - rewrite lookup_delete_ne in H0; [| congruence].
      split; assumption. }
  split.
  - split_and!; [exact Hwf0 | ..].
    + intros g0 r0 t0 H0. destruct (decide (g0 = g')) as [-> | Hne].
      * rewrite lookup_insert in H0. injection H0 as <- <-.
        exact (tree_sub_dir av root root' t e Ht Hr').
      * destruct (Hlk g0 r0 t0 Hne H0) as (_ & H1).
        exact (Hroots g0 r0 t0 H1).
    + intros g1 g2 r1 t1 r2 t2 Hne H1 H2.
      destruct (decide (g1 = g')) as [-> | Hne1].
      * rewrite lookup_insert in H1. injection H1 as <- <-.
        destruct (Hlk g2 r2 t2 (fun Hc => Hne (eq_sym Hc)) H2) as (Hd2 & K2).
        exact (Hout2 g2 r2 t2 Hd2 K2).
      * destruct (Hlk g1 r1 t1 Hne1 H1) as (Hd1 & K1).
        destruct (decide (g2 = g')) as [-> | Hne2].
        { rewrite lookup_insert in H2. injection H2 as <- <-.
          exact (Hout g1 r1 t1 Hd1 K1). }
        destruct (Hlk g2 r2 t2 Hne2 H2) as (Hd2 & K2).
        exact (Hnn g1 g2 r1 t1 r2 t2 Hne K1 K2).
  - intros g0 r0 t0 H0. destruct (decide (g0 = g')) as [-> | Hne].
    + rewrite lookup_insert in H0. injection H0 as <- <-. exact Ht'.
    + destruct (Hlk g0 r0 t0 Hne H0) as (_ & H1). exact (Hex g0 r0 t0 H1).
Qed.

(* ===================================================================== *)
(*  2.  THE TAINT, THE FIXED PART, THE CLAIM                              *)
(* ===================================================================== *)

Section AppTree.
  Context {Σ : gFunctors} `{!treeG Σ}.

  (* THE FIXED PART: the taint counter's name, born once, echo's
     [echo_fixed] exactly. *)
  Definition tree_fixed : Type := gname.
  Definition tree_names : Type := gname.

  (* THE TAINT: the counter has left 0 and can never come back, so its
     lower bound at 1 is a permanent, persistent fact -- "some move of
     the file system was paid by nobody". *)
  Definition tree_taint (c : tree_fixed) : iProp Σ := mono_nat_lb_own c 1.

  Global Instance tree_taint_persistent c : Persistent (tree_taint c).
  Proof using . rewrite /tree_taint. apply _. Qed.
  Global Instance tree_taint_timeless c : Timeless (tree_taint c).
  Proof using . rewrite /tree_taint. apply _. Qed.

  Definition tree_cl (c : tree_fixed) : iProp Σ := mono_nat_auth_own c 1 0%nat.

  Lemma tree_birth : ⊢ |==> ∃ c : tree_fixed, tree_cl c.
  Proof using .
    iMod (mono_nat_own_alloc 0%nat) as (γ) "[Ha _]".
    iModIntro. iExists γ. iExact "Ha".
  Qed.

  (* the mint TL-4's ledger runs at the first unpaid move *)
  Lemma tree_taint_mint (c : tree_fixed) : tree_cl c ==∗ tree_taint c.
  Proof using .
    iIntros "Ha". rewrite /tree_cl /tree_taint.
    iMod (mono_nat_own_update 1%nat with "Ha") as "[_ #Hlb]"; [lia |].
    by iModIntro.
  Qed.

  (* ---- 2a.  THE CLAIM ------------------------------------------------ *)

  (* THE CLAIM'S BODY.  Three pure conjuncts and the authority: the map is
     well formed at the view, it is exact, and -- TL-3's landing of TL-2's
     finding 4 -- THE ERA HAS A ROOT, [adir_at av ROOTINO], which is what
     gives the era's first deed a channel ([tree_xfer_boot_at]).  Every
     landed leg preserves it for free (section 1a'). *)
  Definition tree_body (r : tree_names) (av : aview) : iProp Σ :=
    (∃ own : gmap gname (Z * ttree),
       ghost_map_auth r 1 own ∗ ⌜own_wf av own⌝ ∗ ⌜tree_exact av own⌝
       ∗ ⌜adir_at av FsImg.ROOTINO⌝)%I.

  Definition tree_pred (c : tree_fixed) (r : tree_names) (av : aview)
      : iProp Σ := (tree_taint c ∨ tree_body r av)%I.

  Global Instance tree_body_timeless r av : Timeless (tree_body r av).
  Proof using . rewrite /tree_body. apply _. Qed.
  Global Instance tree_pred_timeless c r av : Timeless (tree_pred c r av).
  Proof using . rewrite /tree_pred. apply _. Qed.

  Lemma tree_body_intro (r : tree_names) (av : aview)
      (own : gmap gname (Z * ttree)) :
    own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
    ghost_map_auth r 1 own -∗ tree_body r av.
  Proof using .
    intros Hwf Hex Hr. iIntros "Ha". iExists own. iFrame "Ha".
    iSplit; [by iPureIntro |]. iSplit; iPureIntro; assumption.
  Qed.

  (* ---- 2b.  THE DEED, AND THE FROZEN DEED ---------------------------- *)

  (* "I own the subtree [t] at [root]" -- the map element, EXCLUSIVE. *)
  Definition tree_own (r : tree_names) (g : gname) (root : Z) (t : ttree)
      : iProp Σ := (g ↪[r] (root, t))%I.

  (* ...AND ITS FROZEN FORM: the element PERSISTED.  An owner that will
     never move its subtree again may trade the deed for a persistent one
     -- and what it buys is the [□]-shaped claim law below, which is what
     a walk (many hops, each reading the claim) needs and which no linear
     deed can pay.  The trade is one-way by construction: a persisted
     element cannot be updated, so a frozen owner's subtree is frozen for
     the whole application (any move inside it taints). *)
  Definition tree_pin (r : tree_names) (g : gname) (root : Z) (t : ttree)
      : iProp Σ := (g ↪[r]□ (root, t))%I.

  Global Instance tree_pin_persistent r g root t : Persistent (tree_pin r g root t).
  Proof using . rewrite /tree_pin. apply _. Qed.
  Global Instance tree_pin_timeless r g root t : Timeless (tree_pin r g root t).
  Proof using . rewrite /tree_pin. apply _. Qed.

  Lemma tree_freeze (r : tree_names) (g : gname) (root : Z) (t : ttree) :
    tree_own r g root t ==∗ tree_pin r g root t.
  Proof using . rewrite /tree_own /tree_pin. iApply ghost_map_elem_persist. Qed.

  (* two deeds at one generation are two authorities at one key *)
  Lemma tree_own_excl (r : tree_names) (g : gname) (root root' : Z)
      (t t' : ttree) :
    tree_own r g root t -∗ tree_own r g root' t' -∗ False.
  Proof using .
    rewrite /tree_own. iIntros "H1 H2".
    iDestruct (ghost_map_elem_ne with "H1 H2") as %Hne. done.
  Qed.

  (* ---- 2c.  THE SUPPLY AND THE TRANSPORT ----------------------------- *)

  (* echo's [echo_sup_of_taint], verbatim at this claim: a tainted
     application claims nothing, so its claim holds of every view -- which
     is the credential the generic user-execution slot runs on. *)
  Lemma tree_sup_of_taint (c : tree_fixed) (r : tree_names) :
    tree_taint c -∗ app_sup_raw (tree_pred c) r.
  Proof using .
    iIntros "#Ht". rewrite /app_sup_raw. iIntros "!>" (av).
    rewrite /tree_pred. iLeft. iExact "Ht".
  Qed.

  (* THE TRANSPORT ([App.Happ_xfer]): a copy of the claim at FRESH names.
     The copy is born OWNING NOTHING -- the empty partition -- which is
     well formed at any view the original's own [own_wf] says is
     tree-shaped.  Echo's [echo_xfer] shape: the fresh authority is
     allocated OUTSIDE the later (the allocation is an update) and the
     arms are read under ONE later. *)
  Lemma tree_xfer (c : tree_fixed) : ⊢ app_xfer_raw (tree_pred c).
  Proof using .
    rewrite /app_xfer_raw. iIntros "!>" (r av) "H".
    iMod (ghost_map_alloc_empty (K := gname) (V := Z * ttree)) as (r') "Ha".
    iAssert (▷ (tree_pred c r av ∗ tree_pred c r' av))%I with "[H Ha]" as "HH";
      last first.
    { iDestruct "HH" as "[H1 H2]". iModIntro. iFrame "H1". iExists r'.
      iExact "H2". }
    iNext. rewrite /tree_pred.
    iDestruct "H" as "[#Ht | Hb]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct "Hb" as (own) "(Hau & %Hwf & %Hex & %Hr)".
    iSplitL "Hau".
    { iRight. iApply (tree_body_intro r av own Hwf Hex Hr with "Hau"). }
    iRight. iApply (tree_body_intro r' av ∅ _ _ Hr with "Ha").
    Unshelve.
    2: { intros g root t Hg. rewrite lookup_empty in Hg. discriminate. }
    split_and!; [exact (proj1 Hwf) | ..];
      intros g *; rewrite lookup_empty; discriminate.
  Qed.

  (* ...AND THE ERA'S FIRST DEED, WHICH IS WHAT THE ROOT CONJUNCT BUYS
     (design section 6, finding 4).  The clone is born owning "/" -- the
     whole namespace at the era's root -- and the arm that blocked this
     before is REFUTED rather than answered with [emp]: the claim the
     transport was handed says the view HAS a root directory, so
     [subtree av ROOTINO] is a [Some] and the deed is minted at it.

     THE VIEW IS AVAILABLE OUTSIDE THE LATER (echo's [cons_inum av] trick),
     and the claim itself is TIMELESS, so the refutation runs inside the
     transport's own [==∗] with no later in the way. *)
  Lemma tree_xfer_boot_at (c : tree_fixed) :
    ⊢ app_xfer_boot_raw (tree_pred c)
        (fun r' : tree_names =>
           ∃ (g : gname) (t : ttree), tree_own r' g FsImg.ROOTINO t)%I.
  Proof using .
    rewrite /app_xfer_boot_raw. iIntros "!>" (r av) "H".
    (* THE VIEW IS AVAILABLE OUTSIDE THE LATER (echo's [cons_inum av]
       trick), so the clone's entry is allocated AT THE ERA'S OWN ROOT
       SUBTREE -- unconditionally, because the deed is only ever cashed
       through the claim law, whose taint arm covers a tainted era. *)
    set (t0 := MkTTree (subtree_nodes av FsImg.ROOTINO) FsImg.ROOTINO).
    iMod (ghost_map_alloc ({[ 1%positive := (FsImg.ROOTINO, t0) ]}
                            : gmap gname (Z * ttree))) as (r') "[Ha Hel]".
    rewrite big_sepM_singleton.
    iAssert (▷ (tree_pred c r av ∗ tree_pred c r' av))%I with "[H Ha]" as "HH";
      last first.
    { iDestruct "HH" as "[H1 H2]". iModIntro. iFrame "H1". iExists r'.
      iFrame "H2". iExists 1%positive, t0. iExact "Hel". }
    iNext. rewrite /tree_pred.
    iDestruct "H" as "[#Ht | Hb]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct "Hb" as (own) "(Hau & %Hwf & %Hex & %Hr)".
    (* THE ARM THAT BLOCKED THIS is refuted here, from the claim's own
       root conjunct: the era HAS a root directory, so its subtree is a
       [Some] and the clone's single entry is exact at it. *)
    pose proof (subtree_root_of_claim av Hr) as Hsub.
    iSplitL "Hau".
    { iRight. iApply (tree_body_intro r av own Hwf Hex Hr with "Hau"). }
    iRight. iApply (tree_body_intro r' av _ _ _ Hr with "Ha").
    Unshelve.
    2: { intros g0 r0 t1 H0. destruct (decide (g0 = 1%positive)) as [-> | Hne].
         - rewrite lookup_singleton in H0. injection H0 as <- <-. exact Hsub.
         - rewrite lookup_singleton_ne in H0; [discriminate | congruence]. }
    split_and!.
    - exact (proj1 Hwf).
    - intros g0 r0 t1 H0. destruct (decide (g0 = 1%positive)) as [-> | Hne].
      + rewrite lookup_singleton in H0. injection H0 as <- <-. exact Hr.
      + rewrite lookup_singleton_ne in H0; [discriminate | congruence].
    - intros g1 g2 r1 t1 r2 t2 Hne H1 H2. exfalso.
      destruct (decide (g1 = 1%positive)) as [-> | H1e].
      + destruct (decide (g2 = 1%positive)) as [-> | H2e];
          [ exact (Hne eq_refl) | ].
        rewrite lookup_singleton_ne in H2; [discriminate | congruence].
      + rewrite lookup_singleton_ne in H1; [discriminate | congruence].
  Qed.

  (* ===================================================================== *)
  (*  3.  THE CLAIM LAWS                                                    *)
  (* ===================================================================== *)

  (* THE STABLE FORM (design section 2), LINEAR: the deed goes in and
     comes back, and what it buys is the reading of its own subtree at
     the view the claim was read at -- or the taint.  This is
     [AppEcho.echo_cons_abs_law]'s shape and [PinnedObs.pobs_walk_dead]'s
     premise; a fire that opens [AppInv.app_inv] once (every AU commit,
     every claim-update) takes it as it stands. *)
  Lemma tree_claim_law (c : tree_fixed) (r : tree_names) :
    ⊢ □ (∀ (v : aview) (g : gname) (root : Z) (t : ttree),
           tree_own r g root t -∗ tree_pred c r v -∗
           tree_pred c r v ∗ tree_own r g root t ∗
           (⌜subtree v root = Some t⌝ ∨ tree_taint c)).
  Proof using .
    iIntros "!>" (v g root t) "Hg [#HT | Hb]".
    { iSplitR; [by iLeft |]. iFrame "Hg". iRight. iExact "HT". }
    iDestruct "Hb" as (own) "(Ha & %Hwf & %Hex & %Hr)".
    iDestruct (ghost_map_lookup with "Ha Hg") as %Hlk.
    iSplitL "Ha".
    { iRight. iApply (tree_body_intro r v own Hwf Hex Hr with "Ha"). }
    iFrame "Hg". iLeft. iPureIntro. exact (Hex g root t Hlk).
  Qed.

  (* ...AND THE [□] FORM, at a FROZEN deed: this is
     [PinnedObs.pobs_walk]'s and [ExecRun.exec_walk_of_pin]'s premise on
     the nose, at [Pin := fun v => subtree v root = Some t].  It cannot be
     had from a linear deed -- a walk reads the claim once per hop, under
     a [□] -- which is what [tree_freeze] is for. *)
  Lemma tree_pin_law (c : tree_fixed) (r : tree_names) (g : gname)
      (root : Z) (t : ttree) :
    tree_pin r g root t -∗
    □ (∀ v : aview, tree_pred c r v -∗
         tree_pred c r v ∗ (⌜subtree v root = Some t⌝ ∨ tree_taint c)).
  Proof using .
    iIntros "#Hg !>" (v) "[#HT | Hb]".
    { iSplitR; [by iLeft |]. iRight. iExact "HT". }
    iDestruct "Hb" as (own) "(Ha & %Hwf & %Hex & %Hr)".
    iDestruct (ghost_map_lookup with "Ha Hg") as %Hlk.
    iSplitL "Ha".
    { iRight. iApply (tree_body_intro r v own Hwf Hex Hr with "Ha"). }
    iLeft. iPureIntro. exact (Hex g root t Hlk).
  Qed.

  (* THE PIN'S CONTENT (finding 2), as the walk families want it and as
     far as the tree claim can pin it: at every view the claim admits,
     the path's run is the SAME run ([resolve_hops], computed from the
     tree alone), it ends at the SAME inum, and the row there is the
     tree's node -- up to the LINK COUNT, which the application tree does
     not carry.  [PinnedObs.pin_resolves_at] wants the row on the nose;
     an absnode-level variant of it takes this. *)
  Lemma tree_resolves_abs (root d i : Z) (t : ttree) (bs : list (bv 8))
      (pl : list (bv 8)) :
    fs_proper (path_elems pl) ->
    d ∈ dom (tv_nodes t) ->
    resolves_from t d pl = Some (i, AFile bs) ->
    forall av : aview,
      subtree av root = Some t ->
      arun av d (path_elems pl) (resolve_hops t d pl)
      /\ resolve_hops t d pl !!! 0%nat = d
      /\ resolve_hops t d pl !!! length (path_elems pl) = i
      /\ (exists k : nat, av !! i = Some (MkAnode (AFile bs) k)).
  Proof using .
    intros Hp Hd Hres av Ht.
    exact (subtree_resolves_pin_file t d i bs pl Hp Hres av root Ht
             (subtree_dom_reach av root t d Ht Hd)).
  Qed.

  (* ===================================================================== *)
  (*  4.  THE STEP WANDS                                                    *)
  (* ===================================================================== *)

  (* THE ENGINE, and the only Iris in the free steps: a view move that
     preserves the THREE pure conjuncts at EVERY ownership map preserves
     the claim.  [AppInv.app_top_update_step] takes exactly this shape.
     (The third is the root's, TL-3's: section 1a' pays it at every leg out
     of the leg's own [own_wf] lemma.) *)
  Lemma tree_step_gen (c : tree_fixed) (r : tree_names) (av av' : aview) :
    (forall own : gmap gname (Z * ttree),
       own_wf av own -> tree_exact av own -> adir_at av FsImg.ROOTINO ->
       own_wf av' own /\ tree_exact av' own /\ adir_at av' FsImg.ROOTINO) ->
    tree_pred c r av -∗ tree_pred c r av'.
  Proof using .
    intros Hstep. iIntros "[#HT | Hb]"; [by iLeft |].
    iDestruct "Hb" as (own) "(Ha & %Hwf & %Hex & %Hr)".
    destruct (Hstep own Hwf Hex Hr) as (Hwf' & Hex' & Hr').
    iRight. iApply (tree_body_intro r av' own Hwf' Hex' Hr' with "Ha").
  Qed.

  (* ---- 4a.  THE INVISIBLE LEGS: free, and at EVERY owner ------------- *)

  (* mkdir's two interior [dirlink]s.  The tree hides the dots, so these
     move nothing at all -- whoever pays them, whatever anyone owns. *)
  Lemma tree_step_dots (c : tree_fixed) (r : tree_names) (av : aview)
      (i d : Z) :
    tree_pred c r av -∗ tree_pred c r (delta_dots i d av).
  Proof using .
    iApply tree_step_gen. intros own Hwf Hex Hr.
    exact (tree_pres_cong av (delta_dots i d av) own (tview_delta_dots av i d)
             Hwf Hex Hr).
  Qed.

  Lemma tree_step_dot (c : tree_fixed) (r : tree_names) (av : aview) (i : Z) :
    tree_pred c r av -∗ tree_pred c r (delta_dot i av).
  Proof using .
    iApply tree_step_gen. intros own Hwf Hex Hr.
    exact (tree_pres_cong av (delta_dot i av) own (tview_delta_dot av i) Hwf Hex Hr).
  Qed.

  (* link's TARGET leg at a row the view has: a pure count bump *)
  Lemma tree_step_link_tgt (c : tree_fixed) (r : tree_names) (av : aview)
      (i : Z) (a : anode) :
    av !! i = Some a ->
    tree_pred c r av -∗ tree_pred c r (delta_link_tgt i a av).
  Proof using .
    intros Ha. iApply tree_step_gen. intros own Hwf Hex Hr.
    exact (tree_pres_cong av (delta_link_tgt i a av) own
             (tview_delta_link_tgt av i a Ha) Hwf Hex Hr).
  Qed.

  (* unlink's TARGET leg above the last link: a count drop *)
  Lemma tree_step_unl_tgt_live (c : tree_fixed) (r : tree_names) (av : aview)
      (i : Z) (a : anode) :
    av !! i = Some a -> (2 <= an_nlink a)%nat ->
    tree_pred c r av -∗ tree_pred c r (delta_unl_tgt i av).
  Proof using .
    intros Ha Hnl. iApply tree_step_gen. intros own Hwf Hex Hr.
    exact (tree_pres_cong av (delta_unl_tgt i av) own
             (tview_delta_unl_tgt_live av i a Ha Hnl) Hwf Hex Hr).
  Qed.

  (* ---- 4b.  CREATE'S ARM LEG: free, because a fresh inum is nobody's -- *)

  (* the first of create's two legs, and the reason they may be paid in
     either order: no entry dangles ([aview_closed], a conjunct of the
     claim's own [own_wf]), so nothing names the armed inum yet and no
     owner reaches it. *)
  Lemma tree_step_arm (c : tree_fixed) (r : tree_names) (av : aview)
      (i : Z) (n : absnode) :
    av !! i = None -> tabs_leaf (tabs_of n) ->
    tree_pred c r av -∗ tree_pred c r (delta_arm i n av).
  Proof using .
    intros Hi Hleaf. iApply tree_step_gen. intros own Hwf Hex Hr.
    exact (tree_pres_arm av own i n Hi Hleaf Hwf Hex Hr).
  Qed.

  (* ---- 4c.  AN OWNER'S OWN MOVES (finding 1) ------------------------- *)

  (* THE ENGINE for a move INSIDE the mover's own subtree: the deed goes
     in, the recorded tree moves by the tree op, the deed comes back.
     A BASIC UPDATE, and that is the seam: [AppInv.app_step] is a plain
     wand, so this cannot be handed to a fire as it stands.  See the
     header's finding 1. *)
  Lemma tree_move_gen (c : tree_fixed) (r : tree_names) (g : gname)
      (root : Z) (t t' : ttree) (av av' : aview) :
    (forall own : gmap gname (Z * ttree),
       own !! g = Some (root, t) -> own_wf av own -> tree_exact av own ->
       adir_at av FsImg.ROOTINO ->
       own_wf av' (<[g := (root, t')]> own)
       /\ tree_exact av' (<[g := (root, t')]> own)
       /\ adir_at av' FsImg.ROOTINO) ->
    tree_own r g root t -∗ tree_pred c r av ==∗
      tree_pred c r av' ∗ (tree_own r g root t' ∨ tree_taint c).
  Proof using .
    intros Hstep. iIntros "Hg [#HT | Hb]".
    { iModIntro. iSplitR; [by iLeft |]. iRight. iExact "HT". }
    iDestruct "Hb" as (own) "(Ha & %Hwf & %Hex & %Hr)".
    iDestruct (ghost_map_lookup with "Ha Hg") as %Hlk.
    destruct (Hstep own Hlk Hwf Hex Hr) as (Hwf' & Hex' & Hr').
    rewrite /tree_own.
    iMod (ghost_map_update (root, t') with "Ha Hg") as "[Ha Hg]".
    iModIntro. iSplitL "Ha".
    { iRight. iApply (tree_body_intro r av' _ Hwf' Hex' Hr' with "Ha"). }
    iLeft. iExact "Hg".
  Qed.

  (* WRITE: the owner's file's bytes are spliced; every other owner's subtree is
     untouched, by disjointness. *)
  Lemma tree_move_write (c : tree_fixed) (r : tree_names) (g : gname)
      (root i : Z) (t : ttree) (off : nat) (new bs0 : list (bv 8))
      (nl : nat) (av : aview) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    i ∈ dom (tv_nodes t) ->
    tree_own r g root t -∗ tree_pred c r av ==∗
      tree_pred c r (delta_write i off new av) ∗
      (tree_own r g root (top_write i off new t) ∨ tree_taint c).
  Proof using .
    intros Hi Hd. iApply tree_move_gen. intros own Hg Hwf Hex Hr.
    exact (tree_pres_write av own g root i t off new bs0 nl Hi Hg Hd Hwf Hex Hr).
  Qed.

  (* TRUNCATE, on [own_wf_trunc] above *)
  Lemma tree_move_trunc (c : tree_fixed) (r : tree_names) (g : gname)
      (root i : Z) (t : ttree) (bs0 : list (bv 8)) (nl : nat) (av : aview) :
    av !! i = Some (MkAnode (AFile bs0) nl) ->
    i ∈ dom (tv_nodes t) ->
    tree_own r g root t -∗ tree_pred c r av ==∗
      tree_pred c r (delta_trunc i av) ∗
      (tree_own r g root (top_trunc i t) ∨ tree_taint c).
  Proof using .
    intros Hi Hd. iApply tree_move_gen. intros own Hg Hwf Hex Hr.
    exact (tree_pres_trunc av own g root i t bs0 nl Hi Hg Hd Hwf Hex Hr).
  Qed.

  (* CREATE, FUSED (TL-1 landed [own_wf_create] at the fused delta; the
     per-leg parent form waits on an [own_wf_ent]): a fresh leaf is hung
     under a directory of the owner's own tree. *)
  Lemma tree_move_create (c : tree_fixed) (r : tree_names) (g : gname)
      (root d : Z) (nm : fname) (i : Z) (n : absnode) (t : ttree)
      (e : gmap fname Z) (nl : nat) (av : aview) :
    fs_pname nm ->
    av !! d = Some (MkAnode (ADir e) nl) -> e !! nm = None ->
    av !! i = None -> tabs_leaf (tabs_of n) ->
    d ∈ dom (tv_nodes t) ->
    tree_own r g root t -∗ tree_pred c r av ==∗
      tree_pred c r (delta_create d nm i n av) ∗
      (tree_own r g root (top_ins d nm i (tabs_of n) t) ∨ tree_taint c).
  Proof using .
    intros Hnm Hd Hnone Hi Hleaf Hdd. iApply tree_move_gen.
    intros own Hg Hwf Hex Hr.
    exact (tree_pres_create av own g root d nm i n t e nl
             Hnm Hd Hnone Hi Hleaf Hg Hdd Hwf Hex Hr).
  Qed.

  (* UNLINK'S ENTRY LEG: the name goes, and the tree RE-CLOSES (the one op
     that can orphan).  The TARGET leg at the last link is not offered --
     see the header. *)
  Lemma tree_move_unl_ent (c : tree_fixed) (r : tree_names) (g : gname)
      (root d : Z) (nm : fname) (dec : nat) (t : ttree)
      (e : gmap fname Z) (nl : nat) (av : aview) :
    av !! d = Some (MkAnode (ADir e) nl) ->
    d ∈ dom (tv_nodes t) ->
    tree_own r g root t -∗ tree_pred c r av ==∗
      tree_pred c r (delta_unl_ent d nm dec av) ∗
      (tree_own r g root (top_unlink d nm t) ∨ tree_taint c).
  Proof using .
    intros Hd Hdd. iApply tree_move_gen. intros own Hg Hwf Hex Hr.
    exact (tree_pres_unl_ent av own g root d nm dec t e nl Hd Hg Hdd Hwf Hex Hr).
  Qed.

  (* ===================================================================== *)
  (*  5.  THE MINTS: era 0, the boot owner, and the hand-down               *)
  (* ===================================================================== *)

  (* ERA 0 ([App.Happ_init]), at the EMPTY partition: nobody owns
     anything, so all the claim says is that the view is tree-shaped.
     THE PREMISE IS THE GATE: at the theorem's own literal the view is the
     mkfs image's, and [aview_tree_wf] of it is a pure fact about the
     image that TL-4 must compute. *)
  Lemma tree_init (c : tree_fixed) (av : aview) :
    aview_tree_wf av -> adir_at av FsImg.ROOTINO ->
    ⊢ |==> ∃ r : tree_names, tree_pred c r av.
  Proof using .
    intros Hwf Hr. iMod (ghost_map_alloc_empty (K := gname) (V := Z * ttree))
      as (r) "Ha".
    iModIntro. iExists r. iRight.
    iApply (tree_body_intro r av ∅ _ _ Hr with "Ha").
    Unshelve.
    2: { intros g root t Hg. rewrite lookup_empty in Hg. discriminate. }
    split_and!; [exact Hwf | ..]; intros g *; rewrite lookup_empty; discriminate.
  Qed.

  (* ...AND THE ERA'S FIRST OWNER BESIDE IT: the boot process owns the
     whole namespace at the root the image gives it.  (Design section 3's
     "the first process owns / at the mkfs image's tree"; the view is an
     argument, so this is equally the mint at any era.) *)
  Lemma tree_init_at (c : tree_fixed) (av : aview) (g : gname)
      (root : Z) (t : ttree) :
    aview_tree_wf av -> adir_at av FsImg.ROOTINO -> subtree av root = Some t ->
    ⊢ |==> ∃ r : tree_names, tree_pred c r av ∗ tree_own r g root t.
  Proof using .
    intros Hwf Hroot Ht.
    iMod (ghost_map_alloc ({[ g := (root, t) ]} : gmap gname (Z * ttree)))
      as (r) "[Ha Hel]".
    rewrite big_sepM_singleton.
    iModIntro. iExists r. iFrame "Hel". iRight.
    iApply (tree_body_intro r av _ _ _ Hroot with "Ha").
    Unshelve.
    2: { intros g0 r0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
         - rewrite lookup_singleton in H0. injection H0 as <- <-. exact Ht.
         - rewrite lookup_singleton_ne in H0; [discriminate | congruence]. }
    split_and!.
    - exact Hwf.
    - intros g0 r0 t0 H0. destruct (decide (g0 = g)) as [-> | Hne].
      + rewrite lookup_singleton in H0. injection H0 as <- <-.
        by apply subtree_Some_inv in Ht as (Hd & _).
      + rewrite lookup_singleton_ne in H0; [discriminate | congruence].
    - intros g1 g2 r1 t1 r2 t2 Hne H1 H2. exfalso.
      destruct (decide (g1 = g)) as [-> | H1e].
      + destruct (decide (g2 = g)) as [-> | H2e].
        * exact (Hne eq_refl).
        * rewrite lookup_singleton_ne in H2; [discriminate | congruence].
      + rewrite lookup_singleton_ne in H1; [discriminate | congruence].
  Qed.

  (* THE HAND-DOWN (finding 3): an owner retires its entry and a fresh
     generation is born owning a SUB-ROOT of it.  A pure re-partition of
     the ownership map -- no view moves -- so it runs at whatever view the
     invariant is at ([AppInv.app_claim_update]'s shape), and the child's
     non-nesting with every stranger IS TL-1's disjointness theorem. *)
  Lemma tree_grant (c : tree_fixed) (r : tree_names) (g : gname)
      (root root' : Z) (t : ttree) (e : gmap fname Z) (av : aview) :
    tv_nodes t !! root' = Some (ADir e) ->
    tree_own r g root t -∗ tree_pred c r av ==∗
      tree_pred c r av ∗
      ((∃ (g' : gname) (t' : ttree),
          tree_own r g' root' t' ∗ ⌜subtree av root' = Some t'⌝)
       ∨ tree_taint c).
  Proof using .
    intros Hr'. iIntros "Hg [#HT | Hb]".
    { iModIntro. iSplitR; [by iLeft |]. iRight. iExact "HT". }
    iDestruct "Hb" as (own) "(Ha & %Hwf & %Hex & %Hroot)".
    rewrite /tree_own.
    iDestruct (ghost_map_lookup with "Ha Hg") as %Hlk.
    pose proof (Hex g root t Hlk) as Ht.
    pose proof (tree_sub_dir av root root' t e Ht Hr') as Hdir.
    pose proof (subtree_of_dir av root' Hdir) as Ht'.
    set (g' := fresh (dom own)).
    assert (Hfresh : own !! g' = None).
    { apply not_elem_of_dom. rewrite /g'. apply is_fresh. }
    iMod (ghost_map_delete with "Ha Hg") as "Ha".
    iMod (ghost_map_insert g' (root', MkTTree (subtree_nodes av root') root')
            with "Ha") as "[Ha Hg']".
    { rewrite lookup_delete_ne; [exact Hfresh |].
      intros ->. by rewrite Hfresh in Hlk. }
    destruct (tree_pres_grant av own g g' root root'
                t (MkTTree (subtree_nodes av root') root') e
                Hlk Hfresh Hr' Ht' Hwf Hex) as [Hwf' Hex'].
    iModIntro. iSplitL "Ha".
    { iRight. iApply (tree_body_intro r av _ Hwf' Hex' Hroot with "Ha"). }
    iLeft. iExists g', (MkTTree (subtree_nodes av root') root').
    iFrame "Hg'". iPureIntro. exact Ht'.
  Qed.

End AppTree.

(* ===================================================================== *)
(*  6.  THE RECORD                                                        *)
(* ===================================================================== *)

(* THE TREE APPLICATION as an [App.xv6_app]: the claim is [tree_pred], the
   fixed part is the taint counter, and EVERY CONSOLE FIELD IS THE GENERIC
   SLOT'S ([App.app_triv]'s) -- this application claims a file system and
   nothing about the two UARTs.  [app_kill := True]: a kill does not taint
   a tree application (design section 3 -- an owner dying leaves its entry
   orphaned, and nothing moves an orphaned subtree until a parent
   re-grants it).

   THE LEDGER IS A PLACEHOLDER (header, "what is owed"): it carries the
   taint counter's birth so that the counter is not dropped, and it never
   bumps it.  TL-4 replaces it with echo's shape. *)
Section AppTreeRecord.
  Context {Σ : gFunctors} `{!treeG Σ}.

  (* the ledger: the counter, or the taint it has already become *)
  Definition tree_R (c : tree_fixed) (_ : list mobs) : iProp Σ :=
    (tree_cl c ∨ tree_taint c)%I.

  Global Instance tree_R_timeless c h : Timeless (tree_R c h).
  Proof using . rewrite /tree_R /tree_cl /tree_taint. apply _. Qed.

  (* THE ERA'S FIRST DEED, as the boot resource (design section 6, finding
     4, landed by TL-3): the era's first process owns "/" at whatever the
     image's namespace is there -- or the application is already tainted,
     which is the arm a tainted era transports at.  It is av-FREE, which
     is what [App.app_boot] requires and what blocked this before the
     claim grew its root conjunct. *)
  Definition tree_boot (_ : tree_fixed) (_ : nat) (r : tree_names) : iProp Σ :=
    (∃ (g : gname) (t : ttree), tree_own r g FsImg.ROOTINO t)%I.

  Definition app_tree : App.xv6_app Σ :=
    MkApp tree_fixed tree_cl tree_names tree_pred
          tree_boot                          (* app_boot *)
          tree_R                             (* app_R *)
          (* THE CONSOLE INTERFACE (upstream redesign R2/R4): a tree
             application says nothing about a received byte, puts no price
             on a kill and claims nothing of the console *)
          (fun _ => app_iface_triv Σ)        (* app_ifc *)
          (fun _ _ => emp%I)                 (* app_turn *)
          (fun _ _ => True).                 (* app_phi *)

  (* ---- the obligations of [App.xv6_app_adequacy] that are lemmas ---- *)

  Lemma app_tree_birth : ⊢ |==> ∃ c : app_fixed app_tree, app_cl app_tree c.
  Proof using . cbn [app_tree app_fixed app_cl]. iApply tree_birth. Qed.

  Lemma app_tree_Rt (c : app_fixed app_tree) (h : list mobs) :
    Timeless (app_R app_tree c h).
  Proof using . cbn [app_tree app_R]. apply _. Qed.

  Lemma app_tree_tagp (c : app_fixed app_tree) (h : list mobs) :
    Persistent (app_tag app_tree c h).
  Proof using . cbn [app_tree app_tag]. apply _. Qed.

  Lemma app_tree_tagt (c : app_fixed app_tree) (h : list mobs) :
    Timeless (app_tag app_tree c h).
  Proof using . cbn [app_tree app_tag]. apply _. Qed.

  Lemma app_tree_killp (c : app_fixed app_tree) : Persistent (app_kill app_tree c).
  Proof using . cbn [app_tree app_kill]. apply _. Qed.

  Lemma app_tree_killt (c : app_fixed app_tree) : Timeless (app_kill app_tree c).
  Proof using . cbn [app_tree app_kill]. apply _. Qed.

  (* A KILL COSTS THIS APPLICATION NOTHING (design section 3) *)
  Lemma app_tree_kill (c : app_fixed app_tree) (r : app_names app_tree) :
    app_sup_raw (app_pred app_tree c) r ⊢ □ app_kill app_tree c.
  Proof using .
    rewrite /app_kill. cbn [app_tree app_ifc app_iface_triv ai_kill].
    iIntros "_ !>". done.
  Qed.

  (* ONE LICENCE over the console claim (redesign R2): the tree
     application's claim is [emp], so every console event on it is free;
     and its timelessness, vacuous at [emp]. *)
  Lemma app_tree_cons_sup (c : app_fixed app_tree) (r : app_names app_tree) :
    app_sup_raw (app_pred app_tree c) r
      ⊢ □ (∀ (k : nat) (h : list mobs) (H : LogEntryDefs.cons_hist)
             (ev : ConsLog.cons_ev),
             app_cons app_tree c k h H ==∗
             app_cons app_tree c k h (ConsLog.cons_step H ev)).
  Proof using .
    rewrite /app_cons. cbn [app_tree app_ifc app_iface_triv ai_cons].
    rewrite /cons_res_triv. iIntros "_ !>" (k h H ev) "_". by iModIntro.
  Qed.

  Lemma app_tree_R0 (c : app_fixed app_tree) :
    app_cl app_tree c ⊢ |==> app_R app_tree c [].
  Proof using .
    cbn [app_tree app_cl app_R]. rewrite /tree_R. iIntros "H". iModIntro.
    iLeft. iExact "H".
  Qed.

  (* the power step: the ledger rides, and the era's console resources are
     both [emp] *)
  Lemma app_tree_pow (c : app_fixed app_tree) (h : list mobs) (on : bool)
      (dk : Z -> bv 8) :
    trace_shape h on ->
    ⊢ app_R app_tree c h ==∗
      app_R app_tree c (h ++ [if on then ObsPowerOff else ObsPowerOn])%list ∗
      (if on then emp
       else app_cons app_tree c (S (obs_boots h)) []
              (LogEntryDefs.MkCH [] [] [] None) ∗
            app_turn app_tree c (S (obs_boots h))).
  Proof using .
    intros _. rewrite /app_cons.
    cbn [app_tree app_R app_ifc app_iface_triv ai_cons app_turn].
    iIntros "H". iModIntro. iSplitL "H"; [iExact "H" |].
    destruct on; by repeat iSplitR.
  Qed.

  Lemma app_tree_boot (c : app_fixed app_tree) (k : nat) :
    ⊢ app_xfer_boot_raw (app_pred app_tree c) (app_boot app_tree c k).
  Proof using .
    cbn [app_tree app_pred app_boot]. rewrite /tree_boot.
    iApply tree_xfer_boot_at.
  Qed.

End AppTreeRecord.

(* ===================================================================== *)
(*  7.  WHAT THE RECORD STILL OWES ([App.xv6_app_adequacy]'s binders)     *)
(*                                                                       *)
(*  Discharged above, as lemmas at the record's fields: [Hbirth], [HRt],  *)
(*  [al_kill], [al_sup], [HR0], [Hpow], [Happ_boot].               *)
(*                                                                       *)
(*  Trivial at this record's fields and left to the instance site (they   *)
(*  are [app_triv]'s one-liners at [emp] claims -- see                    *)
(*  [App.xv6_app_adequacy_triv_xv6Σ]'s [ltac:] block): [Htx], [Hrx],      *)
(*  [Hphi] (the conclusion is [True]).                                    *)
(*                                                                       *)
(*  OPEN, and TL-4's:                                                     *)
(*    [Happ_init] -- era 0's claim at the IMAGE's view.  [tree_init] is   *)
(*      it, GATED on the pure fact [aview_tree_wf (abs_view (fss_inodes   *)
(*      (img_state …)))]: the mkfs image's namespace has unique proper    *)
(*      parenthood and no dangling entry.  A computation over the image,  *)
(*      on [FsImgCheck]'s mould.                                          *)
(*    [Hinit_boot] -- the first process's exec bundle at "/init", echo's   *)
(*      [UInitSh] construction at this claim; finding 2 is what it needs   *)
(*      first if it is to be a PINNED bundle rather than a tainted one.    *)
(*    ...and the LEDGER: [app_R] here never bumps the counter, so         *)
(*      [tree_taint] is not mintable and [app_sup] is unobtainable.  A    *)
(*      real tree application reads an unpaid move off its own ledger.    *)
(* ===================================================================== *)
