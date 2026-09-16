# Design: the tree layer — subtree ownership as an application claim (TL-0)

Status: DESIGN OF RECORD, 2026-09-17 (Fable), the third of the owner's
three ("ex-3, the wait/kill pair, and the tree-layer campaign").  Lanes
run after RD-7/8.  Companion pages: `fs-syscall-specs.md` (§2's
held-share finding, §4's delta vocabulary, §6's tree sketch — which this
page CORRECTS on one point), `applications.md` + `AppInv.v`'s header
(the claim-over-the-view machinery this page instantiates),
`user-exec.md` §4's EX-2 block (the refutation this page is the
successor of), `fs-friendly.md` / `fs-fragments.md` (a DIFFERENT tree —
see §1).

## 0. The one sentence

A verified program's cross-syscall knowledge of the file system — "I
know what this file is", "my directory has exactly these entries" — is
NOT a ghost share (EX-2: custody of a live inode is total, the read arm
lends only to the locking kernel thread, nothing crosses an ecall) but
a CLAIM IN THE APPLICATION INVARIANT: the application declares which
process owns which subtree of the live view, every fs move is paid
with a step that preserves the partition, and a program reads its own
subtree off the claim exactly as sh reads /echo's bytes off echo's
"fs unmodified" pin.  The pin was the whole-fs special case; this is
the per-process general case.

## 1. Two trees, and which one this is

- **The kernel-boundary tree** (`FsRep.fs_rep γi γfs t`, `FsTree.fstree`,
  `wp_sys_mkdir_friendly`): a reading of the kernel's own inode ghosts
  (`fnode := dinode_at ∗ inode_blocks …`), the F1/F1.5 fragment algebra
  of `fs-fragments.md`, whose job is kernel-INTERNAL — traversing
  tree-broken states, retiring the span axiom.  NOT this campaign.
- **The application tree** (this page, `iris/TreeView.v`): a PURE reading
  of `aview`, the live namespace (`FsAbsDefs.abs_view`, §4's "the view is
  the live namespace"), at a root: `subtree av r : option ttree` (the
  nodes reachable from `r` by PROPER directory entries — dots hidden —
  `None` if `r` is not a directory of the view).  It lives in `app_pred`,
  never in a kernel invariant (the owner's rule: nothing
  application-specific inside a kernel fs invariant).

  **The node type is `FsAbsDefs.absnode`, not `FsTree.fsnode`** (TL-1's
  ruling).  `fsnode` has two arms and reads a DEVICE as `NFile []` — right
  for the kernel tree, wrong here, because a program that mknod's a device
  and opens it must tell its node from an empty file.  Extending `fsnode`
  was declined: it is the type `FsTree.node_of` is total onto, so the arm
  would force a decision inside the KERNEL-boundary reading and touch
  FsTree's cone for an application-tier need — the conflation this section
  exists to prevent.  `absnode` is already `anode` minus `nlink`, so the
  projection is `tnode_of a := an_node a` with the dots deleted from a
  directory's map, and `ttree` is `fstree`'s shape (`MkTTree nodes root`)
  over it.
  **`nlink` is dropped**, and that is load-bearing in both directions: it
  makes `delta_dots`, `delta_dot`, `delta_link_tgt` (at a row the view
  has) and `delta_unl_tgt` (above the last link) INVISIBLE in the tree, so
  an owner pays nothing for mkdir's interior legs; and it means the claim
  pins a node's CONTENT but not its link count, so `PinnedObs.
  pin_resolves_at`'s `anode` row is supplied with the count existentially
  quantified (`TreeView.subtree_resolves_pin`).  At a non-directory the
  projection is the identity, so exec's (W) gets the row on the nose
  (`subtree_resolves_pin_file`).

## 2. The claim, and why the machinery is already there

`AppInv.app_inv` keeps half the map authority beside
`app_pred app_run (abs_view I)`; every view move goes through
`app_top_update_step`, which demands a step wand
`app_pred av -∗ app_pred (<[i:=n']> av)` — paid by the moving process's
deposit (a verified program) or by `app_sup` (the generic slot).  Echo's
instance: `echo_pred := taint ∨ (⌜echo_fs_pure av⌝ ∗ cons_state)`, a
pure predicate on the view plus a taint arm for any move nobody pays.

THE TREE APPLICATION's claim, same shape, indexed by an ownership map:

    tree_pred c r av :=
      taint ∨ ( ghost_map_auth (γown r) (1/2) own
              ∗ ⌜own_wf av own⌝            -- roots are directories in av,
                                            -- pairwise non-nested
              ∗ ∗_{g ↦ (root, t) ∈ own} ⌜subtree av root = t⌝ )

and a process `P` of generation `g` holds the other half of its entry,
`g ↪[γown r] (root_P, t_P)` — "I own subtree `t_P` at `root_P`".  The
two halves agree (`ghost_map` agreement), so `P` reads `subtree av
root_P = t_P` off the claim at any fire point: THAT is the stable form
`fs-syscall-specs.md` §2 wanted, as a claim rather than a fraction.

Why this is sound where a share was not: nothing here claims a
fraction of any kernel ghost.  The claim is a Prop on the view, kept
true by the step discipline; the kernel's custody of every inode is
untouched.

## 3. The step discipline = the exclusivity fact, made a resource

§2 of `fs-syscall-specs.md` said: cross-syscall stability is "an
exclusivity fact the tree layer states and consumes at the whole-system
level".  Here is how it is stated and consumed, with no new kernel
mechanism (xv6 has no namespaces, no chroot — this is a DISCIPLINE the
application declares and its verified programs prove):

- **A verified program moving INSIDE its own subtree** pays the step
  from its deposit: `P`'s syscall delta `δ` (§4's `δ_create`/`δ_link`/
  `δ_unlink`/`δ_write`, at a node `d ∈ subtree av root_P`) updates its
  own entry — `t_P ↦ tree_op δ t_P` (a ghost-map update of both halves,
  which is why the wand is an iProp and not a Prop) — and leaves every
  other entry unchanged by DISJOINTNESS: non-nested roots + UNIQUE PROPER
  PARENTHOOD ⇒ subtrees are node-disjoint ⇒ a move at `d` inside `t_P` is
  outside every `t_Q`.

  **What disjointness actually needs** (TL-1, and this corrects the
  earlier sketch): not acyclicity — `fs_dirs_acyclic` is never used, and
  is neither necessary nor sufficient — and not "directories form a tree"
  alone.  A diamond is acyclic and shares a node: one FILE hard-linked
  under two unrelated directories is in both subtrees, and then an
  owner's write inside its own subtree changes another owner's tree.  The
  premise is `TreeView.aview_uniq_parent`: every node has at most one
  proper in-edge (`nuniq_parent`, a conjunct of `own_wf` through
  `aview_tree_wf`).  With unique parenthood restricted to DIRECTORIES
  (xv6's own invariant, since link refuses a directory and there is no
  rename) the honest theorem is weaker and still true:
  `TreeView.nreach_common_dir` — a node two unrelated owners both reach
  is a hard-linked non-directory, never a directory.
  **Consequence for `sys_link`**: a link whose target is already named
  elsewhere breaks `aview_uniq_parent`.  Inside ONE owner's subtree that
  is harmless for disjointness (the node is in one subtree either way)
  but it is not covered by the landed preservation lemma, so a tree
  application either forbids cross-name links or carries the weaker
  directories-only premise and accepts that files may be shared.  The
  aview twin of the landed acyclicity fact is minted anyway
  (`aview_dirs_acyclic`, tied to `FsTree.fs_dirs_acyclic` by
  `aview_dirs_acyclic_tree`) because §6.2 of `fs-syscall-specs.md`
  promises it; nothing uses it.

  The second conjunct of `aview_tree_wf` is `aview_closed`: NO ENTRY
  DANGLES.  It is what makes a fresh inum unreachable, hence create's arm
  invisible to every subtree — which is why create's two legs may be paid
  in either order.  The premise the
  program needs — "this path resolves inside my subtree" — is a pure
  fact about its path and its cwd/root, discharged by its code proof
  (relative paths from a cwd inside `t_P`; absolute paths under
  `root_P`), the same way echo's discipline is a pure property of its
  code.
- **A move nobody pays** (an unverified process, or a verified one
  outside its subtree) TAINTS — the `app_sup` arm, exactly echo's.  So
  the honest theorem reads: "while every fs move is a verified
  program's own-subtree move, every program's view of its subtree is
  exact; the first unpaid move is recorded as the taint".
- **Grant** at fork/exec: a ghost move with NO view move
  (`app_top_update_same` is not even needed).  CORRECTED BY TL-2
  (§6's finding 3): the parent CANNOT keep `t_P ∖ t_C` — the claim is
  exact and the roots are non-nested, so there is no hole-punched
  reading to keep.  What the landed `tree_grant` does is the HAND-DOWN:
  the parent's entry is retired, the child's entry at a sub-root of it
  is born.  Boot: the
  first process owns `/` at the mkfs image's tree — the tree
  application's `Happ_boot`, echo's `echo_fs_era0` shape.
- **Kill / exit**: an owner dying leaves its entry orphaned; the claim
  still holds (nothing moves an orphaned subtree until a parent
  re-grants it — the parent's `wait` is where the entry comes back).
  A kill does NOT taint a tree application; `app_kill := True` unless
  the application also claims the console.
- **Durability**: `fs-syscall-specs.md` §6 item 4 stands — "my subtree
  is well-formed" is an invariant on the current view, so the durable
  instance (`app_xfer`, the crash slot) inherits it with no new
  machinery; the tree layer adds no durable content.

## 4. What it delivers

1. **The stable corollaries**, one per syscall, as INSTANCES of the
   landed AU forms + claim agreement (§2 "Stable form (derived) … never
   a separate proof against the code"): `open` at a path inside `t_P`
   returns a descriptor on exactly the node `t_P` names; `read` at it
   learns exactly that node's bytes (the R-c content row, now with the
   file KNOWN in advance); `mkdir`/`mknod`/`unlink`/`write` move `t_P`
   by the tree op.  These are `fs-friendly.md`'s three-sentence specs
   ("the path resolves or it does not; on success the tree gains a
   node; nothing else changed") — at the application tier, over `aview`.
2. **Pin-free exec** — EX-2's successor, one lemma: the claim law
   `□ ∀ v, app_pred v -∗ app_pred v ∗ (⌜subtree v root_P = t_P⌝ ∨ T)` is
   `PinnedObs.pobs_walk`'s premise shape at `Pin := subtree · root_P =
   t_P`, so `exec_walk_of_own : g ↪ (root_P, t_P) -∗ ⌜resolves_in t_P
   pl = File f⌝ -∗ exec_walk_of …` is the (W) supplier that needs no
   whole-fs pin.  `ExecBundle.v` needs no change (its (W) premises were
   cut for exactly this, EX-1).
3. **A second application** — the validation this whole cleanup asked
   for: a verified program that creates a directory and a file, execs a
   program that reads it back, at the whole-system theorem, with the fs
   NOT pinned unmodified.

## 5. Honest limits

### 5.0 THE WRITE SIDE'S OPEN DECISION (TL-3, for the owner)

TL-2's finding 1 left ONE shape mismatch, and TL-3's read side is
complete without touching it — so the question is now isolated and is a
DECISION, not a proof.  An owner's own move (`tree_move_write`,
`tree_move_trunc`, `tree_move_create`, `tree_move_unl_ent`) is a BASIC
UPDATE `tree_own ∗ tree_pred av ==∗ tree_pred (δ av) ∗ (tree_own' ∨ T)`;
what a fire can take (`AppInv.app_top_update_step`) is an UPDATE-FREE
wand `app_pred av -∗ app_pred av'`.  Two ways to close it, both outside
the tree layer:

- **(i) THE AppInv SEAM.**  `app_step` becomes
  `▷ app_pred av ==∗ ▷ app_pred av'`.  `AppInv.app_top_update` already
  applies the step INSIDE its own fupd, so the invariant can take it
  with no new machinery; upstream's own fires are what move.  COST:
  every AU fire site that supplies a step (every `app_top_update_step`
  caller) restates it, and the generic slot's `app_sup` arm has to be
  re-derived at the update form.  BUYS: an owner's move is paid where
  the move is SEEN, which is the only place its accuracy is provable;
  every landed `tree_move_*` becomes a fire payment verbatim.
- **(ii) PER-SYSCALL POST-VIEW RECEIPTS.**  Each writing row hands the
  caller a receipt naming the POST view (the row already names the
  observed PRE view; this is one more conjunct), and the owner
  re-establishes its claim in its own `app_claim_update` AFTER the
  call.  COST: a statement change per writing syscall (create/write/
  trunc/unlink), each with its own cone, and the owner pays two claim
  opens per write instead of none.  BUYS: no upstream fire moves, and
  the tree layer's altitude keeps the whole change.

TL-3's WRITE side and TL-4's mutation story wait on this.  Note what
does NOT wait: everything in §4.1 that a reader needs, and pin-free
exec, are landed (§6, TL-3 as-landed) — an application whose verified
programs only READ their subtree is provable today, and an application
that writes is provable the moment either route lands.

### 5.1 The rest

- **`sys_link` is not offered** (DESIGNER'S RULING, 2026-09-17, closing
  TL-1's open item).  A link whose target already has a name breaks
  `aview_uniq_parent`, which is what disjointness rests on (§3), so
  inside the tree application's discipline an owner may not link.  The
  case xv6 programs actually use — a link to a file that is currently
  unnamed-but-live — is not one the live-namespace claim can even see.
  FUTURE RELAXATION: shared files WITHIN ONE owner's subtree are
  harmless for disjointness (the node is in one subtree either way) and
  need only the weaker directories-only premise
  (`nreach_common_dir`) plus a `subtree_delta_link_ent` preservation
  lemma at a target the owner already reaches; the landed `own_wf`
  lemmas do not cover it.
- **An owner never unlinks a root** (TL-1's side condition, stated as
  the step's premise), and TL-2 found that the LAST-LINK target leg
  cannot be paid at all as things stand: "the row is nobody's root" is
  a fact about the ownership map, which no mover holds.  It is payable
  only as a strengthening of the claim (every root is named, or is
  `ROOTINO`); recorded, not taken.
- Exclusivity is declared, not enforced: an unverified process can
  scribble anywhere; the claim taints.  This is xv6, not a capability
  OS, and the theorem says so.
- Unlinked-but-open files and the temp-file idiom stay the fd row's
  business (§4 of `fs-syscall-specs.md`); the tree claim is about the
  live namespace only.
- One application per system (`App.xv6_app` is THE application); a
  tree application composes its verified programs under one record,
  as echo composes init/sh/echo.

## 6. Lanes

- [x] **TL-1 THE PURE LAYER** — LANDED, `iris/TreeView.v` (zero Iris,
  every result `Closed under the global context`).  What is there, and
  what TL-2 builds on:
  - `subtree av r : option ttree` over `tview av` (the projected view),
    computed as a SATURATING closure: `nreach_set` iterates the kid
    expansion `S (size m)` times, which is enough because the iteration
    lives in `{[r]} ∪ dom m` and each round that adds nothing is final.
    Nothing outside §3a of the file unfolds the iteration — everything
    downstream uses `nreach` (∃ a proper path) and its spec, and `nreach`
    is DECIDABLE (`nreach_dec`), which is what makes the δ proofs
    pointwise `map_eq`s.
  - **The one law the whole layer turns on**: `nclose_agree` — two maps
    that agree on what the root reaches have the same subtree.  The
    OUTSIDE half of every δ is one line off it (`subtree_out_row`,
    `subtree_out_row2`).
  - `own_wf` (a section over any `Countable` key: `aview_tree_wf` + roots
    are directories + roots pairwise non-nested) and `subtree_disjoint` /
    `subtree_disjoint_trees`.
  - The δ lemmas, INSIDE and OUTSIDE, over the landed legs: write/trunc
    (`nclose_content_edit`), create — fused (`subtree_delta_create`) AND
    leg by leg, since the fires commit a leg at a time: the arm is
    invisible (`subtree_delta_arm_fresh`, a fresh inum is unreachable)
    and the parent leg is the fresh insert at an armed child
    (`subtree_delta_ent`, `top_ins`) — link's parent leg (`top_link`),
    unlink's entry leg (`top_unlink`, the ONE op that re-closes, because
    it is the only one that can orphan), and the four invisible legs.
    `subtree_delta_*` is the naming.
  - `resolves_from` / `resolves_in` / `resolve_hops` and the equivalence
    with `arun` on the view, both directions, plus the relative form from
    a cwd inside the subtree.  Paths are PROPER (`fs_proper (path_elems
    pl)`): `..` at the root leaves the subtree, which is the one move the
    claim cannot answer — a pure side condition on the program's own
    string.
  - `own_wf` preservation per δ (`own_wf_write`, `own_wf_arm`,
    `own_wf_create`, `own_wf_unl_ent`, `own_wf_unl_tgt`).  Two side conditions fell out
    and are stated where they bite: an owner may not unlink a ROOT (its
    own or anyone's), and the row may only leave when nothing names it
    (`aview_no_edge_to` — the `nlink`-vs-edge-count tie, which the tree
    layer does not carry, and which the entry-leg-first order gives).
- [x] **TL-2 THE APPLICATION** — LANDED, `iris/AppTree.v` (echo audit
  unaffected: a second record, and a leaf nothing imports).  Every
  result `Closed under the global context` — not even funext.  What is
  there, and THREE FINDINGS, two of which are seams the design must
  now rule on:

  **The claim, as landed.**  `tree_pred c r av := tree_taint c ∨
  tree_body r av` with `tree_body r av := ∃ own, ghost_map_auth r 1 own
  ∗ ⌜own_wf av own⌝ ∗ ⌜tree_exact av own⌝`, `tree_exact av own := ∀ g
  root t, own !! g = Some (root,t) → subtree av root = Some t`, and the
  deed `tree_own r g root t := g ↪[r] (root,t)`.  TWO DEVIATIONS from
  §2's sketch, both simplifications: the authority is WHOLE (nobody
  holds the other half, and an owner's move needs the whole), and the
  per-entry conjunct is the pure `tree_exact` rather than a `[∗ map]`
  of pure facts.  The taint is echo's shape (a `mono_nat` lower bound
  at 1 on a counter in the fixed part).

  **FINDING 1 (THE SEAM — an owner's own move cannot be paid at the
  fire).**  `AppInv.app_top_update_step`'s — and `AppInv.app_step`'s —
  step is an UPDATE-FREE wand `app_pred av -∗ app_pred av'`, applied
  under the invariant's later; moving an owner's recorded subtree is a
  ghost-map UPDATE.  Three routes were tried and all fail *for one
  reason*: only the step wand SEES the view move, and it cannot write
  anything down.  (a) a plain wand transfers resources but cannot run a
  frame-preserving update; (b) wrapping the claim in `|==>` makes the
  wand able to update but makes the CLAIM LAW unprovable — no pure fact
  comes out from under a basic update; (c) a WINDOW (desync before the
  call, resync after it — echo's mknod two-phase shape) leaves the
  owner having to prove `subtree av root = Some t_new` at the
  invariant's CURRENT view, which it cannot know; whatever the window
  records, the ambiguity "did my commit fire?" survives it.
  So the owner's moves are landed in their TRUE shape, as BASIC
  UPDATES (`tree_move_write`, `tree_move_create`, `tree_move_unl_ent`,
  over the engine `tree_move_gen`): the whole tree content is proved,
  and what is left over is ONE shape mismatch.  TWO WAYS TO CLOSE IT,
  both outside the tree layer and both owner decisions:
    (i) `app_step` becomes `▷ app_pred av ==∗ ▷ app_pred av'`
        (`app_top_update` can already take it — it applies the step
        inside its own fupd); this moves every AU fire site;
    (ii) the syscall's ROW hands the caller a receipt about the POST
        view, so the owner can re-establish accuracy in its own
        claim-update after the call (a per-syscall statement change,
        TL-3's altitude).
  Until then a tree application's owners move nothing, and what TL-3
  gets is the READ side (below), which is complete.

  **FINDING 2 (exec's (W) — TL-1's nlink gap bites at the
  IDENTIFICATION, not at the walk).**  `PinnedObs.pin_resolves_at` pins
  the terminal row as an `anode`, LINK COUNT INCLUDED; the tree claim
  pins content and not counts, so the pin is unsuppliable AS STATED and
  `exec_walk_of_own` is NOT landed.  Nothing in the walk needs the
  count (`pobs_hop` reads only the `arun` conjunct) — it is
  `pobs_node` / `ExecBundle.ex_node_id` that ask for the row on the
  nose.  What IS landed is everything on this side of the seam: the
  claim law in both shapes, and `tree_resolves_abs` (the pin's content
  at an existential count).  Unblocking it is ONE additive definition
  in `PinnedObs.v` (`pin_resolves_abs`) and one in `ExecRun.v` (an
  `ex_node_id` at the node's CONTENT).

  **FINDING 3 (grant is a HAND-DOWN, not a re-partition).**  §3's
  "`t_P` at `root_P` becomes `t_P ∖ t_C` plus a new entry" is NOT
  expressible over TL-1's `subtree`: the claim is EXACT ("my subtree IS
  `t`") and `own_wf` wants the roots pairwise NON-NESTED, so a parent
  cannot keep a hole-punched tree.  `tree_grant` is the honest move:
  the parent's entry is RETIRED and a fresh generation is born owning a
  sub-root of it (the child's non-nesting with every stranger IS TL-1's
  disjointness theorem).  A hole-punched partition needs a new pure
  reading in TL-1 (`subtree_except av root R`) and a disjointness
  theorem at it — price it before promising fork/exec grants that keep
  the parent.

  **FINDING 4 (the era's first deed has no channel).**  Nobody can mint
  a deed at `/` out of a RUNNING claim: the insert needs the new root to
  be non-nested with every existing root, which at `/` means the
  ownership map is empty — and the claim cannot see that its own map is
  empty.  Nor can `Happ_init` hand one over (its conclusion has no room
  beside the claim, and App.v's own note says its instance never reaches
  a boot: every era founds from the TRANSPORT's clone).  So the first
  deed must ride `App.app_boot`, which the transport CAN build, because
  the view is available OUTSIDE the later (echo's `cons_inum av` trick
  decides the arm there): allocate the fresh map at
  `{[ g := (ROOTINO, t) ]}` when `subtree av ROOTINO = Some t`.  What
  blocks it is the OTHER arm — `app_boot` is av-FREE and "this view has
  no root directory" has no av-free spelling, so the disjunction
  collapses to `emp`.  THE FIX, priced: the claim grows ONE conjunct,
  `⌜adir_at av ROOTINO⌝`, which every landed leg preserves (a fresh inum
  is not the root; write/truncate are at a FILE row; create's and
  unlink's entry legs leave a directory a directory), and the
  transport's None arm is then refuted from the claim it was handed.
  Until it lands, `app_boot` is `emp` and a tree application's owners
  are whoever a `tree_grant` hands down from the first.

  **The claim laws** (what TL-3 consumes).  `tree_claim_law`, LINEAR —
  `□ (∀ v g root t, tree_own r g root t -∗ tree_pred c r v -∗
  tree_pred c r v ∗ tree_own r g root t ∗ (⌜subtree v root = Some t⌝ ∨
  tree_taint c))`, `AppEcho.echo_cons_abs_law`'s shape and
  `PinnedObs.pobs_walk_dead`'s premise, which every single-open fire
  takes as it stands.  A ghost-map deed cannot produce a `□`-shaped law
  (a walk reads the claim once per hop), so the `□` form is at a FROZEN
  deed: `tree_freeze : tree_own ==∗ tree_pin` (the element persisted,
  one-way by construction — a frozen owner can never move that subtree
  again, and any move inside it taints) and `tree_pin_law`, which is
  `pobs_walk`'s / `exec_walk_of_pin`'s premise on the nose.

  **The step wands, as landed** (the `_step` payments an owner's
  deposit makes, `AppInv.app_top_update_step`'s shape exactly, over the
  engine `tree_step_gen : (∀ own, own_wf av own → tree_exact av own →
  own_wf av' own ∧ tree_exact av' own) → tree_pred c r av -∗ tree_pred
  c r av'`):
    - the FOUR INVISIBLE legs, FREE and at every owner, whoever pays
      them: `tree_step_dots`, `tree_step_dot`, `tree_step_link_tgt`
      (at a row the view has), `tree_step_unl_tgt_live` (above the
      last link).  mkdir's interior legs cost an owner nothing.
    - create's ARM leg, FREE: `tree_step_arm` at `av !! i = None` and a
      leaf — no owner reaches a fresh inum, because no entry dangles
      (`aview_closed`, a conjunct of the claim's own `own_wf`).  This
      is why create's two legs may be paid in either order.
    - the OWNER'S legs, as basic updates (finding 1), over the engine
      `tree_move_gen`: `tree_own r g root t -∗ tree_pred c r av ==∗
      tree_pred c r (δ av) ∗ (tree_own r g root (tree_op δ t) ∨
      tree_taint c)`, at write / truncate / the FUSED create /
      unlink's entry leg.
  **`own_wf_trunc` is proved in AppTree.v** (section 1f'), because it is
  `own_wf_write`'s twin line for line and the move is wanted; it belongs
  in TreeView.v and moves there when a TL-1 lane runs.  Still owed:
  `own_wf_ent` (create's PARENT leg alone), which is harder — its
  `aview_tree_wf` twin wants "nothing else names the armed inum" — so
  the create move is offered FUSED only.

  **The mints**: `tree_init` (era 0 at the EMPTY partition — gated on
  the pure `aview_tree_wf av`, which at the theorem's literal is a
  computation over the mkfs image, TL-4's), `tree_init_at` (era 0 with
  the boot owner's entry at a root beside it), `tree_grant` (finding
  3), `tree_xfer` / `tree_xfer_boot` (the transport: the copy is born
  owning NOTHING, which is well formed at any view the original's own
  `own_wf` says is tree-shaped).

  **The record** `app_tree : App.xv6_app Σ`, with `app_kill := True`
  (a kill does not taint a tree application) and every console field
  the generic slot's.  Discharged as lemmas at its fields: `Hbirth`,
  `HRt`, `Htagp`, `Htagt`, `Hkillp`, `Hkillt`, `Happ_kill`, `Houtt`,
  `Happ_out_sup`, `Hinpt`, `Hwint`, `Happ_in_sup`, `HR0`, `Hpow`,
  `Happ_boot`.  Trivial at the instance site (`app_triv`'s one-liners
  at `emp` claims): `Htx`, `Hrx`, `Hphi`.  OPEN for TL-4:
  `Happ_init` (gated as above), `Hinit_boot` (the first process's exec
  bundle), and the LEDGER — `app_R` here carries the taint counter and
  never bumps it, so `tree_taint` is not mintable and `app_sup` is
  unobtainable; a real tree application reads an unpaid move off its
  own ledger, as echo reads a broken input discipline off its.
- [x] **TL-3 THE READ SIDE** — LANDED (branch `tl3-read`): the stable
  corollaries a FROZEN DEED buys, plus the two one-definition unblocks
  TL-2 priced and the root conjunct finding 4 asked for.  Four new
  results files, two landed files grown ADDITIVELY, `AppEcho.v`
  untouched, echo audit unmoved at 14, whole tree green.  The write
  side waits on §5.0 and is NOT touched.

  **The two unblocks (finding 2, closed).**
  - `PinnedObs.v` §10, ADDITIVE (every landed statement unchanged):
    `pin_walks_at` (the walk alone — the start rule, the terminal inum,
    the run — which is all `pobs_hop` ever reads), `pin_resolves_abs`
    (that walk plus "the terminal row is this `absnode` at SOME link
    count"), `pobs_hop_w` / `pobs_walk_w` at the weaker premise, and
    `pobs_node_abs` — `pobs_node` with its conclusion cut to the row's
    CONTENT.  `pin_resolves_at` implies `pin_walks_at`, so the new
    family subsumes rather than competes.
  - `ExecRun.v` §6, ADDITIVE: `ex_node_abs` (`ExecBundle.ex_node_id` at
    the content), `exec_walk_of_abs`, `exec_walk_of_abs_of_walk` (the
    forgetful direction, so the landed pin and taint suppliers feed the
    new rule), `exec_walk_of_abs_pin`, and the bundle chain at the
    content — `exec_slot_of_entry_at_abs` / `sys_exec_slot_of_entry_abs`
    / `exec_bundle_of_abs` / `sbundle_pay_refR_of_exec_abs` /
    `uexec_sup_run_abs` / `wp_uk_ecall_exec_run_abs`.
    **WHY THE CHAIN AND NOT JUST A SUPPLIER** (the lane's one real
    finding): `exec_walk_of` names an `anode`, and a tree claim CANNOT
    pin one — two views the claim admits may differ in the terminal
    row's `nlink` (a hard link OUTSIDE the subtree moves the count and
    leaves the subtree alone), so there is no `nl` at which the landed
    (W) could even be stated.  The count is never SPENT (arm (a) reads
    the image out of `AFile f` and keeps the kernel's own count, arm (b)
    refutes `~ anode_loadable`, which is a fact about `an_node`), so the
    content-level chain is ExecBundle's three lemmas with one premise
    weakened and the same proofs.  `ExecBundle.v` itself is untouched.
  - `TreeExec.v`: **`exec_walk_of_own`** — EX-2's successor, finally:
    ```
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    fs_proper (path_elems pl) -> um_start_of cw pl = d ->
    d ∈ dom (tv_nodes t) -> resolves_from t d pl = Some (i, AFile f) ->
    tree_pin r g root t -∗ app_inv fsc_fs -∗
    exec_walk_of_abs cw (tree_taint c) pl (AFile f)
    ```
    with `exec_walk_of_own_root` at an absolute path under `/`, and the
    consumer test `wp_uk_ecall_exec_own_test`: a process holding a
    frozen deed execs a loadable file of its own subtree at
    `wp_uk_ecall_exec_run_abs`, with `image_entry` and NO whole-fs pin.
  - `TreeObs.v` is the bridge both sides share: `tree_pin_claim_law`
    (the era's record equation turns `tree_pin_law` into the `□` shape
    every pinned bundle takes), `tree_own_claim_law` (the linear twin),
    and the deed's PURE content as a pin — `tree_pin_resolves_gen` at a
    row the projection is the identity on, with `_file`, `_dev`, and the
    absolute/relative start instances.  Two pure facts about `nchain`
    moved into TreeView for it (`nchain_head`, `nchain_last`): a pin's
    first two conjuncts are about the hops list ALONE and must be stated
    with no view in hand.

  **The read-side corollaries** (`UkTreeRead.v`), each an instance of a
  landed member + agreement:
  - `open` — LANDED.  `tree_open_bundle_abs` (PinnedOpen's bundle at the
    content pin), `tree_open_recv_file` (the receipt read at a FILE pin:
    the device and directory arms are REFUTED and the file arm's
    descriptor is `FdInode ino`, the node the owner's tree records at
    that path), `tree_open_sup` (the `udepwf_at` deposit out of the
    deed), `tree_open_fd_tie` (the ledger says WHICH descriptor, the
    receipt says what it is ON, and at the slot the call wrote the two
    spellings agree — UInitConsK's console block at `FdInode`) and
    **`wp_uk_ecall_open_own`** at
    `UkRunSys.wp_uk_ecall_open_recv_img`: three arms and no fourth —
    `r = -1` with the ledger back, `UserFd.ualloc` at
    `FdOpen _ _ (FdInode i γo OffParked)` — which is EXACTLY what the
    read corollary below consumes, so open-then-read composes — or the
    taint with some ledger back.  At `om_create = false` and
    `om_trunc = false`: O_TRUNC is a WRITE.
  - `read` — LANDED.  `tree_read_piece` is the observation commit
    (`FsAbsReadFire.aread_commit_at`) supplied OUT OF THE CLAIM rather
    than out of a held `nview` share — `PinnedObs.pobs_aopen`'s three
    lines at read's commit, and the point EX-2 makes about held shares
    is exactly why it has to be this way.  `read_arms_tree_learn` reads
    the arms, and **`wp_uk_tree_read_learns`** is the cat-with-a-known-
    tree test: a program with a frozen deed and a descriptor on a node
    of its subtree reads and LEARNS that the bytes in its buffer are the
    ones its own tree records.
  - `chdir` — **NOT LANDABLE, recorded** (UkTreeRead §5), for two
    independent reasons.  (i) The U-tier leaf DROPS the receipt: the
    kernel has one (`SpecSysChdir.chdir_receipt`, whose success arm IS
    `cw' = i`) and `UexecExecInst` branch 9 pays it at the U key, but
    `UkRunSys.wp_uk_ecall_chdir` takes the family-free `udepw` and binds
    the post as `_` — exactly where open stood before lane OPEN-PIN; the
    fix is a `wp_uk_ecall_chdir_recv` on `wp_uk_ecall_open_recv`'s
    mould, a kernel-leaf lane.  (ii) DEEPER: chdir's bundle owes the
    walk in the `∀ pl` form (`namei_walk_pre_era`), and a pin answers
    ONE path — at any other path its cursor is false.  So chdir needs
    PinnedObs's own one-path seam first, whatever the claim is.
  - `fstat` — **NOT OFFERED, recorded**: there is no U-tier leaf at all
    (8 goes through the quiet leaf, which drops the post, and is not in
    `UexecExecInst`'s list of numbers that pay one).  The tree HAS the
    answer (`tv_nodes t !! i` carries `AFile bs`, hence the size); there
    is no carrier.
  - A DIRECTORY's entry map is pinned only up to the DOTS (the tree
    hides them), so every corollary that reads dirents needs a
    dots-tolerant identification first.  Files and devices are on the
    nose.

  **The root conjunct (finding 4, closed).**  `tree_body` grew
  `⌜adir_at av ROOTINO⌝`; `tree_step_gen` / `tree_move_gen` carry it as
  a third preserved conjunct and EVERY landed leg pays it in two lines,
  because it is the roots conjunct of `own_wf` at the partition that
  owns `/` and nothing else (`AppTree` §1a': `root_own`, `own_wf_root`,
  `root_of_own_wf`).  `tree_init` / `tree_init_at` gain it as a premise;
  `tree_xfer_boot_at` is the era's first deed — the transport allocates
  the clone's entry at `subtree av ROOTINO` OUTSIDE the later (the view
  is available there) and the no-root arm is REFUTED from the claim it
  was handed, so `app_boot` is no longer `emp`: the record's
  `app_boot := tree_boot`, `∃ g t, tree_own r g ROOTINO t`, discharged
  by `app_tree_boot`.  `Happ_init` / `Hinit_boot` stay TL-4's.

  **Housekeeping**: `own_wf_trunc` MOVED to `TreeView.v` §7c (at the
  section's `gmap K`, as its twins).  `own_wf_ent` is PRICED AND NOT
  TAKEN, with the reason recorded where it belongs (TreeView, end of
  `OwnPres`): `nuniq_parent_ins_fresh` wants the target inum ABSENT,
  which the ARM leg has just made false; the honest premise is
  `aview_no_edge_to av i` and no landed lemma proves unique parenthood
  from it — it needs its own induction, the twin of
  `nuniq_parent_ins_fresh` at a present-but-unnamed row.  So the create
  move stays FUSED, which is what the fires take anyway.

  **Bar**: `Print Assumptions` — `Closed under the global context` on
  every pure and claim-level result (`pobs_node_abs`, `pinned_obs_abs`,
  `exec_walk_of_abs_pin`, `exec_bundle_of_abs`, `exec_walk_of_own`,
  `tree_open_recv_file`, `tree_read_piece`, `read_arms_tree_learn`,
  `tree_xfer_boot_at`, `app_tree_boot`, `own_wf_trunc`); the three WP
  rules and both consumer tests carry the standing platform axioms
  (`resv_matches`, `resv_is_valid`) plus funext and nothing else.
- [ ] **TL-3b THE WRITE SIDE**: blocked on §5.0's decision.
- [ ] **TL-4 THE SECOND APPLICATION**: the end-to-end instance of §4.3
  at `xv6_app_adequacy`, with its own `make audit` line.

## 7. The owner's move — the design of record (2026-09-18, Fable, on the owner's "let's do (i) ourselves")

Designing (i) exactly (§7.1) showed it NECESSARY for a wand-side ghost
update and NOT SUFFICIENT for the tree layer: a step wand's conclusion
is `▷ app_pred av'` and nothing else, so an updated deed made inside
it never reaches the owner.  The fire's commit shape already supplies
the return channel (§7.2): every write-kind commit
(`FsAbsCreateFire.acre_commit_at_gen` and its siblings) is TWO-PHASE —
phase 1 hands out the step; phase 2 runs AFTER the mover, is handed
`I'` with `⌜abs_view I' = δ (abs_view I)⌝` and the fs-top auth half, is
a fancy update at a mask containing `appN`, and produces the caller's
own receipt `Φ`.  That is TL-2's route (ii), pre-existing.  RULING:
the write side lands on §7.2 with NO seam change; §7.1 stays designed
and ready for a claim that genuinely needs a wand-side update.

### 7.1 Seam (i), exactly — designed, not (yet) applied

- `AppInv.app_step i I av' := ∀ n', ⌜abs_view (<[i:=n']> I) = av'⌝ -∗
  ▷ app_pred app_run (abs_view I) ==∗ ▷ app_pred app_run (abs_view (<[i:=n']> I))`
  (one `-∗` → `==∗`).
- `app_top_update`: the step premise likewise; proof: `iMod ("Hstep"
  with "[//] Hp") as "Hp"` (inside its `={E}=∗` after `inv_acc`).
- `app_top_update_step`: statement UNCHANGED (update-free wand), proof
  lifts by `iModIntro`; add `app_top_update_bupd`, the `==∗` twin.
- `app_step_at`: conclusion `==∗`; `app_step_acc`, `app_step_id`: `iModIntro`.
- Statements naming `app_step` (the fire pieces; SpecCreate, SpecSysLink,
  SysOpenDefs, SysUnlinkDefs, SpecFilewrite, SpecSysOpen, ProofFilewrite,
  UexecSG/UexecExecInst): text unchanged.  Proofs that BUILD an
  `app_step` (UInitCons:579-ish, PinnedOpen ×2, UkWriteFile, UkTreeRead,
  AppEcho ×1, AppTree ×3): one `iModIntro` each at the right depth
  (`|==> ▷ …`: `iModIntro` then `iNext`).  Mover callers
  (FsAbs{Create,Write,Link,Unlink,Open,Mknod}Fire): `iApply` of an
  `app_step_at` into `app_top_update`'s slot still typechecks; a site
  that `iDestruct`s the wand's result becomes `iMod`.
- Bar: zero semantic change for every consumer; echo audit at 14.

### 7.2 The two-phase owner move — what TL-3 (write) lands

THE DEED IN HALVES.  `tree_own r g root t := g ↪[γown r]{#1/2} (root, t)`;
the claim's live arm holds the auth (whole) and, per entry, the OTHER
half plus the entry's SLOT:

    slot av g (root, t) :=  ⌜subtree av root = Some t⌝              -- exact
                          ∨ (g ↪{#1/2} (root, t) ∗ ∃ γi, tok γi)   -- in flight

`tok γi` is an exclusive one-shot (`own γi (Excl ())`), FRESH per move
(allocated by the owner in phase 1), so nothing is lost when a move
turns out invisible.  Reading (the stable form) is agreement of the
owner's half with the claim's half + the exact arm; the in-flight arm
is refuted for a READER by the same exactness once the mover finished
(§7.2's phase 2 always restores the exact arm before the fire returns).

THE STEP (update-free, so today's `app_step` takes it verbatim):
    tree_step_move g d δ :
      ⌜d ∈ dom (subtree av root)⌝ → ⌜tree_op δ t ≠ t⌝ →
      g ↪{#1/2} (root,t) ∗ tok γi ∗ tree_pred c r av -∗ tree_pred c r (δ av)
— moves g's slot from exact to in-flight by PARKING the owner's half
and the token (no ghost update); every other entry by
`subtree_disjoint` + the OUTSIDE δ lemma; `own_wf`/`adir_at` by TL-1's
preservation lemmas.  A move with `tree_op δ t = t` (a write of the
same bytes, the invisible legs) takes the FREE step instead — the
owner decides by computation on its own tree.

PHASE 1 (the owner's commit callback, mask E ⊇ ↑appN, before the
mover): open `app_inv`, agree the entry, read `subtree av root = t`,
close; allocate `tok γi`; hand the fire `tree_step_move` with the half
and the token captured.  PHASE 2 (after the mover, given `I'` with
`abs_view I' = δ av` and the auth half): open `app_inv` (the tree
claim is timeless — `▷` strips), agree the entry is still `(root, t)`;
the exact arm is REFUTED (`subtree (δ av) root = tree_op δ t ≠ t`, TL-1's
INSIDE lemma); in the in-flight arm take the half and the token,
update the entry to `(root, tree_op δ t)` (auth + both halves = full),
put one half back, close in the exact arm (`subtree (δ av) root =
tree_op δ t` — the INSIDE lemma again), and return the other half as
the receipt `Φ`.  The receipt reaches the U tier through the kept-post
walk exactly as read's does (`UkReadFile`/`UkTreeRead`'s shape).

THE REFUND ARM: `pf_at AU F = AU ∧ refund` — the owner supplies the
same half and token to both conjuncts, so a syscall that fails before
firing hands them straight back.

EXCLUSIVITY, restated: entering the in-flight arm needs the owner's
half; leaving it needs both halves.  A non-owner's move inside `g`'s
subtree cannot build the step and falls to the taint arm, as §3 says.

### 7.3 Lanes

- [ ] **TL-3W** (Opus): the halves, the slot, `tree_step_move`, the
  two phases as ONE lemma per write-kind member (`tree_move_at` for
  create/mknod/unlink/write over the landed fires), the U-tier
  write-side corollaries (`UkTreeWrite.v`: mkdir/mknod/unlink/write at
  an owned subtree, each an instance of the landed member + this
  page's phases), and the consumer test: make a directory and a file,
  read it back — the second application's core, with no whole-fs pin.
  TL-2's `tree_move_*` bupd lemmas retire into §7.2's shape.
- [ ] **SEAM-I** (deferred; ready): §7.1 as one mechanical lane if a
  consumer appears.
