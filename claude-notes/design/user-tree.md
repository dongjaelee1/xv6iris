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

### 5.0 THE WRITE SIDE'S OPEN DECISION — RULED AND LANDED (see §7/§7.4)

RULED 2026-09-18 in §7: route (ii), the fire's own two-phase commit, with
NO `AppInv` seam.  LANDED by TL-3W, §7.4.  The section below is kept as the
record of what the two routes cost.

#### 5.0 (as it stood)

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
  the step's premise).  TL-2 found that the LAST-LINK target leg could
  not be paid at all — "the row is nobody's root" is a fact about the
  ownership map, which no mover holds.  **HALF LIFTED by TL-3P** (§7.5):
  at a NON-DIRECTORY target it is not about the map at all, because
  `own_wf`'s own roots conjunct says every root is `adir_at`, so a file's
  or a device's row is nobody's root by kind
  (`TreeView.own_wf_unl_tgt_nodir`); and the other premise,
  `aview_no_edge_to`, is PROVED by unlink's own entry leg
  (`aview_no_edge_to_unl_ent`: unique parenthood says the edge just cut
  was the only one), so the tree layer never carries the
  `nlink`-vs-edge-count tie.  The leg is then FREE at every owner
  (`AppTree.tree_step_unl_tgt_last`).  A DIRECTORY's last link —
  `rmdir`-shaped — keeps TL-2's wall.
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
  section's `gmap K`, as its twins).  `own_wf_ent` was PRICED AND NOT
  TAKEN — **TAKEN by TL-3P**, `TreeView.v` §8c; the pricing below is right
  about the PREMISE and wrong about the proof (no induction of its own is
  needed — `nuniq_parent_ins_fresh`'s case analysis goes through with
  freshness replaced by the no-edge fact), and what the leg really wants
  beyond the fresh case is a SECOND credential, "the armed inum is
  nobody's root".  The note as it stood:
  `nuniq_parent_ins_fresh` wants the target inum ABSENT,
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
- [x] **TL-3b / TL-3W THE WRITE SIDE** — LANDED, §7.4: §5.0's decision was
  ruled in §7 (route (ii), no seam change) and the lane landed on it.
- [x] **TL-3P THE PARENT PREFIX** — LANDED, §7.5: the pinned nameiparent
  walk (`iris/TreeWalk.v`, `PinnedObs.v` §11), `own_wf_ent`
  (`TreeView.v` §8), the create and unlink MOVES at a given parent
  (`TreeMove.v` §3b), and unlink's last-link target leg.  The
  create/unlink family is still not payable, and §7.5 names the three
  walls that are left — one of which is NOT the one TL-3W predicted.
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

- [x] **TL-3W** — LANDED (branch `tl3w-move`): `AppTree.v` regrown at
  §7.2, `iris/TreeMove.v` and `iris/UkTreeWrite.v` new, `AppEcho.v` /
  `AppInv.v` untouched, every TL-2/TL-3 statement unchanged, whole tree
  green, echo audit 14.  §7.4 is the as-landed block.
- [x] **TL-3P** — LANDED (branch `tl3p-parent`): §7.5.
- [ ] **SEAM-I** (deferred; ready): §7.1 as one mechanical lane if a
  consumer appears.  TL-3W did NOT need it, which is the ruling
  confirmed: the fire's own phase 2 is the return channel.
- [x] **PARENT-CURSOR** — LANDED as **TL-3K** (branch `tl3k-cursor`):
  §7.5's WALL A fix (i) threaded through the whole cone, and WALL B
  dissolved at any length.  §7.6 is the as-landed block; what the family
  still waits on is WALL C (an ARMED LEDGER, not a receipt) and WALL D
  (the name's properness), both stated there.

### 7.4 TL-3W as landed

**THE CLAIM, REGROWN.**  `tree_body` keeps `own_wf` and
`⌜adir_at av ROOTINO⌝` GLOBAL — both read the ROOTS and never the trees —
and replaces TL-2's global `tree_exact` by a PER-ENTRY SLOT, because an
entry whose owner is mid-move has no exactness at all:

    tree_slot r av g p := g ↪[tn_tk r]{#1/2} p
                          ∗ ( ⌜subtree av p.1 = Some p.2⌝          -- exact
                            ∨ (g ↪[tn_own r] p ∗ ∃ γi, tok γi) )   -- in flight

with `tok γi := own γi (Excl ())` at a new `treeG` field
(`tr_tok : inG Σ (exclR unitO)`, `treeΣ` gains `GFunctor (exclR unitO)`);
`tree_body r av := ∃ own, ghost_map_auth (tn_own r) 1 own ∗
ghost_map_auth (tn_tk r) 1 own ∗ ⌜own_wf⌝ ∗ ⌜adir_at⌝ ∗ [∗ map] g ↦ p ∈ own,
tree_slot r av g p`.

**THE ONE DEVIATION FROM §7.2's LETTER, AND IT IS FORCED.**  §7.2 says
phase 2 "agrees the entry is still `(root, t)`" and does not price that
agreement — but at phase 2 the owner holds NOTHING of its entry, and the
disagreement is not decidable from the claim.  Nor can the owner keep a
fraction of the deed: the in-flight arm has to be refuted by a READER,
including a FROZEN one (`tree_pin_law` must survive at its exact
statement), and `DfracOwn q ⋅ DfracDiscarded` is valid for every `q < 1`
— **only `DfracOwn 1` in the claim refutes a pin**.  So the deed is parked
WHOLE and the owner keeps a MOVE TICKET at a SECOND ghost map carrying the
same map:

    tree_deed r g root t := g ↪[tn_own r] (root, t)      -- parked while in flight
    tree_tkt  r g root t := g ↪[tn_tk  r]{#1/2} (root,t) -- the owner's ticket
    tree_own  r g root t := tree_deed ∗ tree_tkt
    tree_pin  r g root t := both, persisted

`tree_names` is therefore `gname * gname` (`tn_own`/`tn_tk`).  Every landed
statement quantifies `tree_names` opaquely, so `TreeObs.v`, `TreeExec.v` and
`UkTreeRead.v` compile with no edit at all.

**THE READER-WINDOW QUESTION, ANSWERED: THERE IS NO WINDOW.**  A reader
holding any fraction of the deed refutes the in-flight arm by exclusivity
(`tree_body_read` is ONE lemma at an arbitrary `dfrac`, and both claim laws
are instances of it), so `tree_claim_law` and `tree_pin_law` keep their
EXACT statements and their fact does NOT weaken to a disjunction.  The
reason is structural rather than lucky: entering the in-flight arm costs
the whole deed, so an owner that can read is an owner that is not moving,
and a concurrent *other* owner's flight is invisible (slots are per entry).

**`tree_step_gen` SURVIVES AT ITS EXACT STATEMENT**, which is not obvious:
its hypothesis is a `∀ own` gated on `tree_exact av own`, which the slotted
body cannot supply.  It is applied at the SYNCED map
(`own_sync av own`, every recorded tree replaced by the view's own subtree
at that entry's root): exact by construction, same roots — so `own_wf`
transfers both ways — and its exactness at the POST view says precisely
"no owner's root moved", which is what each surviving exact slot needs.
The four free steps and create's arm leg are then unchanged, line for line.

**THE TWO PHASES.**  `tree_step_move_gen` (+ `_write` / `_trunc` /
`_create` / `_unl_ent`) is the update-free step `AppInv.app_step` takes
verbatim: the deed and a fresh token go in, the slot moves exact →
in flight, every other entry rides TL-1's OUTSIDE lemma at the mover's own
exactness (`tree_disjoint_out_at` — the mover's, and no one else's, which
is what makes it usable beside in-flight entries).  `tree_resync` is
phase 2: the ticket identifies the entry, the exact arm is refuted by
`t' ≠ t` (§7.2's `tree_op δ t ≠ t`), the parked deed and token come back,
both maps move to `(root, t')`, the slot closes exact, and the owner gets
`tree_own r g root t'` — the receipt.  `tree_move_refund` is the refund
arm.  **TL-2's `tree_move_*` basic updates are RETIRED** (their content is
the pure layer both phases read).

**THE INVISIBLE ARM IS FREE, AND CHEAPER THAN §7.2 SAID.**  The kernel
picks a write's offset and bytes, so an owner supplying a chain must answer
both cases; but at write and truncate an invisible move leaves the ROW
where it was, so the delta is the IDENTITY on the view
(`delta_write_id` / `delta_trunc_id`) and the free step is a congruence.
The decision is `decide (blk_splice off bs bs0 = bs0)` on the pre-row the
fire itself hands phase 1.

**WHAT A MEMBER SUPPLIES AND GETS BACK** (`TreeMove.v`).  At the write
fire: phase 1 (`tree_claim_read`) opens `app_inv`, agrees the map the
kernel lent, reads `subtree (abs_view I) root = Some t' ∨ taint`, decides
visibility, and hands `app_step i I (delta_write i off bs (abs_view I))`;
phase 2 (`tree_claim_resync`) takes `I'` with the delta equation and
returns the deed at `top_write i off bs t'`.  `tree_awrite_phases` is the
pair for ONE chunk (the FULL and the PARTIAL arm are the same proof — they
differ only in the bytes they claim, never in the delta), and
`tree_awrite_chain` is `FsAbsWriteFire.awrite_chain_unit` with
`AppInv.app_sup` replaced by a DEED, at the cursor

    tree_wq c r g root i t := (∃ t', tree_own r g root t' ∗ ⌜twrote i t t'⌝)
                              ∨ tree_taint c

where `twrote i t t'` is "same root, same nodes away from `i`, and `i` is a
FILE in both".  That relation is the honest post: the kernel picks every
chunk's offset, so the owner cannot name the bytes — see the owed item
below.

**THE U TIER** (`UkTreeWrite.v`).  `tree_write_sup` is
`UkWriteFile.udepwf_st_write_file` with the chain paid by the deed, and
**`wp_uk_tree_write_moves`** is the consumer test: a program owning a
subtree, holding a descriptor on a file of it, writes its bytes, learns
the committed bytes are its own, AND gets its deed back moved.  So THE
RECEIPT TYPE IS NOT PURE-ONLY — the write member's kept-post walk carries
an arbitrary `iProp` (row 16's family field `UexecExecInst.wf_Q`, the
chain's prefix cursor), and a ghost-map half rides it home.  That was the
lane's one predicted wall and it is not a wall.

**WHAT IS NOT LANDED, AND EXACTLY WHY** (`TreeMove.v` §4 carries this in
full).  **SUPERSEDED BY §7.5**: TL-3P closed reasons 1 and 3 and found that
3 was not in fact what blocked the family.  Kept as the record of what
TL-3W saw.  The brief's test was "own → mkdir → create → write →
read-learns"; the first two steps are not landable, for THREE independent
reasons:

1. **create/mknod/mkdir: `own_wf_ent`.**  `FsAbsDelta.cre_pre`'s third
   conjunct is `av !! i = Some (MkAnode c 1)` — at the parent leg's instant
   the child is ALREADY ARMED — so an owner's create move is create's
   PARENT LEG ALONE, whose `own_wf` preservation is exactly the
   `own_wf_ent` §6 records as PRICED AND NOT TAKEN (its `aview_tree_wf`
   twin wants `aview_no_edge_to av i`).  `tree_step_move_create` is landed
   at the FUSED delta, i.e. at a view where the child is ABSENT — the shape
   a fire would have if the two legs were one, and not the shape the kernel
   has.
2. **The child's UNARM leg is unpayable from a claim.**
   `cre_child_unfired` asks for `delta_unarm i`; the row is invisible to
   every subtree only if NOTHING NAMES `i`, and the claim's `own_wf` does
   not say so (`nreach_fresh` wants the row ABSENT, which is false by
   then).  The generic supplier pays it off `app_sup`, which a constraining
   application has not got.  Honest fix: a credential threaded from the ARM
   to the UNARM — a change to `aarm_commit_at`'s receipt, a kernel-tier
   lane.
3. **No pinned parent-prefix walk.**  `open_au_create_at` owes
   `FsAbsEra.ep_start`; `PinnedObs` offers a pinned supplier for `ex_start`
   only.  A parent-prefix twin of `pinned_obs_abs` is additive and is what
   any mkdir/mknod/open-O_CREATE corollary needs first.

   **unlink, and why it shares wall 3 with create.**  The tree-side half of
   unlink's entry leg is landed (`tree_step_move_unl_ent` + `tree_resync`),
   but `uent_commit_at` QUANTIFIES THE PARENT `d` INSIDE, and at a `d`
   inside ANOTHER owner's subtree **there is no step at all** — the delta
   moves that owner's tree and only the holder of THAT deed could pay.  So
   an owner cannot supply the commit until `d` is fixed BEFORE it is handed
   in, which is precisely what a pinned parent-prefix walk would do.  That
   is wall 3 again, so the whole create/unlink write family is one lane
   away on this axis.  **And it is why WRITE goes through and they do
   not**: `awrite_full_at` is INDEXED by the descriptor's own inum, so the
   owner's move is at a node it already names.  (The unlink TARGET leg at
   the last link stays TL-2's own recorded wall; above the last link it is
   free.  Its U-tier leaf is blocked anyway — `UkTreeRead` §5: unlink, like
   chdir, still carries the `∀ pl` walk form a pin cannot answer.)
   **O_TRUNC**: the tree-layer half is done (`tree_step_move_trunc`) and it
   IS inum-indexed, so it is only the open bundle's walk that is missing.

**THE SEAM TO THE READ SIDE IS LANDED TOO** (`TreeMove` §1a):
`resolves_from_twrote` / `twrote_read_back` turn the write's own post into
the read corollary's premises at the same path — no induction, because a
walk reads DIRECTORY entries and a file's `nents` is `None` in both trees,
so `TreeView.npath_nents_cong` closes it in a line.  So the caller of
`wp_uk_tree_write_moves` may `tree_freeze` the deed it gets back and hand
it to `UkTreeRead.wp_uk_tree_read_learns`: **own → open → write → freeze →
read-back, with no whole-fs pin anywhere in the run.**  (The freeze is
one-way, as always: a program that will write again keeps the live deed
and reads through a second open instead.)

**OWED, NAMED, PRICED.**
- **The write post does not name the bytes**, for `UkWriteFile.v`'s own
  reason one tier down: the offset is the descriptor's, which this member's
  program does not hold.  With a HELD offset (`OffGv`'s `uoff`, lane RD-1)
  the chain's cursor could name the splice and the corollary would read "my
  tree records exactly the bytes I sent".  Additive, and the one upgrade
  this member is waiting for.

### 7.5 TL-3P as landed — the parent prefix, and the three walls left

**WHAT LANDED.**  Four files grown ADDITIVELY (`TreeView.v` §8,
`PinnedObs.v` §11, `AppTree.v`, `TreeMove.v` §3b) and one new
(`iris/TreeWalk.v`); `AppEcho.v` / `AppInv.v` untouched, every landed
TL-1/2/3/3W statement unchanged, echo audit unmoved, whole tree green.
Every new result is `Closed under the global context` — not even funext.

- **The pinned parent-prefix walk.**  `PinnedObs` §11 is §10's family over
  `FsAbsEra.np_elems pl = removelast (path_elems pl)`: `pin_pwalks_at`,
  `pin_pdir_at` (the terminal directory's entry map, UP TO THE DOTS — all a
  create/unlink consumer spends, since it asks about its own proper `nm`),
  `pobs_phop` / `pobs_pwalk` → `FsAbsEra.ep_start`, and `pobs_pterm`, the
  terminal cursor read as "this is the pinned parent, or the taint".
  `TreeWalk.tree_pwalk_of_own` is the deed route, `TreeExec`'s shape one
  element short.
  **`ep_hops_from` COSTS NOTHING EXTRA AT ITS LAST HOP**, which is the one
  thing this family was expected to cost: it is `ax_hops_from` over the
  SHORTER list, so its hops are `0 .. L-1` and there is no hop at `L`.
  nameiparent's own read of the parent is not a hop at all — it is the
  syscall's separate COMMIT.  The parent-prefix walk is a strict PREFIX of
  the namei walk and its supplier is §10's with one list swapped.
- **`own_wf_ent`** (`TreeView` §8c), so create's parent leg alone has its
  preservation and `AppTree.tree_step_move_ent` exists.  Two credentials,
  not one: `aview_no_edge_to av i` (proved at the arm by
  `aview_no_edge_to_arm`) and "the armed inum is nobody's root", which
  `own_wf_ent_leaf` pays FREE at a non-directory child and which mkdir's
  directory child still owes.
- **The create and unlink MOVES, in full, at a given parent**
  (`TreeMove.tree_acre_phases` / `tree_uent_phases`): phase 1 parks the
  deed and a fresh token and hands out the very `AppInv.app_step` the fire
  asks for; phase 2 returns the deed at `top_ins` / `top_unlink`.
- **Unlink's last-link target leg**, FREE at every owner at a
  non-directory target — see §5.1.

**WALL A — THE COMMITS QUANTIFY THEIR OWN PARENT.**  This is the lane's
main finding and it CORRECTS §7.4's wall 3.
`FsAbsCreateFire.acre_commit_at_gen` and `SysUnlinkDefs.uent_commit_at`
bind `d` INSIDE, so a supplier owes a step at EVERY directory of every
view: at the mover's own `d` it is paid, at a `d` no owner reaches it is
free, and **at a `d` inside a stranger's subtree there is no step at all**
— the delta moves that owner's recorded tree, only the holder of THAT deed
can park it, and `tree_taint` is not mintable by an owner.  The mover
cannot tell the second case from the third.
§7.4 said a pinned parent-prefix walk would FIX `d` before the commit is
handed in.  **It does not.**  The walk and the commit are separate
conjuncts of the bundle (`unlink_au_pre`, `mknod_au_pre`), and the walk's
terminal cursor surfaces only in the syscall's POST — after every commit
has had to be provable at every `d`.  Two fixes:
  - **(i) THREAD THE CURSOR** (kernel tier, mechanical, and the lane
    RECOMMENDS it) — **TAKEN AND LANDED by TL-3K, §7.6**: give the two commits `P (length (npar_elems pl)) d` as
    a premise beside their `cre_pre`/`unl_pre`.  The prover holds it at the
    fire instant (it is what the ret-0 arm hands back), so the kernel side
    is a restatement rather than a new proof, and the owner then reads
    `d = dpar ∨ taint` off `TreeWalk.tree_pwalk_parent` and pays with the
    landed phases verbatim.  Cone: SysOpenDefs, SpecCreate, SpecSysMknod,
    SpecSysUnlink, SpecSysLink, `FsAbs{Create,Unlink,Link}Fire`,
    FsAbsInvFire's unit dischargers, the `ProofSys{Unlink,Link}*` fire
    sites.
  - **(ii) CONSTRAIN THE CLAIM** (tree tier): make "no stranger reaches
    `d`" a consequence of the claim.  It is TRUE of every reachable tree
    application — the era's first deed is ONE entry and `tree_grant`
    RETIRES the parent as it births the child, so the ownership map never
    grows — but the claim cannot see it.  Price: one more conjunct in
    `tree_body` and a third gname in `tree_names`, i.e. an AppTree regrow
    of TL-3W's size; every landed statement survives because `tree_names`
    is quantified opaquely.

**WALL B — THE WALK WANTS A FROZEN DEED AND THE MOVE WANTS A LIVE ONE.**
(SUPERSEDED BY §7.6: TL-3K dissolved it at EVERY length, not just 0/1 —
the resource rides the CURSOR.  Kept as TL-3P's reading.)
New, and independent of WALL A.  A walk reads the claim ONCE PER HOP, so
`PinnedObs`'s premise is a `□` claim law, and only `tree_pin_law` — a
FROZEN deed — has that shape; a frozen deed can never be parked, so its
owner can never move again.  create and unlink need the walk AND the move
in ONE syscall.  WRITE escaped this because its bundle has no walk
(`awrite_full_at` is inum-indexed); exec/open/read escape it because they
never move.
**THE ONE CASE WHERE IT DOES NOT BITE** — and it is where the second
application starts: a parent prefix of LENGTH ZERO.  At a path naming an
entry of the walk's own start directory (`"/foo"` for an owner of `/`),
`np_elems pl = []`, `ep_hops_from` is the empty big-op and `ep_start` is
the START CURSOR ALONE — a pure fact, no claim law read anywhere
(`UInitCons`'s `mknod("console")` is the landed precedent).  So
`mkdir("/d")` by the owner of `/` is reachable the moment WALL A falls,
while a longer prefix needs a DUPLICABLE READ of a LIVE deed besides.
**AND THE LIMIT IS LENGTH 1, NOT 0** (priced, not taken): `pobs_walk_dead`
already shows the shape of a walk whose claim law is LINEAR — it takes a
resource `K`, spends it at hop 0 and hands it back, and every later hop is
reached only under the taint.  A parent prefix of length ONE has exactly
one hop, so a `pobs_phop`/`pobs_pwalk` pair at that linear law would let a
LIVE deed supply the walk for `open("/d/f", O_CREATE)` too.  Two additive
lemmas, and nothing consumes them until WALL A falls, which is why TL-3P
records rather than lands them.  A prefix of length ≥ 2 genuinely needs the
frozen deed.

**WALL C — THE CREDENTIALS THE LEGS OWE EACH OTHER, and they are ONE
mechanism.**  (CORRECTED BY §7.6: it is ONE mechanism, but NOT a
receipt-carried credential — a receipt cannot carry a fact about a LATER
view.  §7.6 prices the two that work.)  create's parent leg needs the arm's no-edge fact; the
child's UNARM leg needs the same one (§7.4's item (a), unchanged); mkdir's
parent leg needs "the armed inum is nobody's root", which only the arm's
own view has; unlink's last-link target leg needs the entry leg's no-edge
fact — and that one the entry leg PROVES
(`TreeView.aview_no_edge_to_unl_ent`).  So WALL C is ONE kernel-tier
change: a credential carried on the legs' receipts (`aarm_commit_at`'s and
`uent_commit_at`'s `Φ`), serving all four at once.

**WHAT TL-4 INHERITS.**  The read side and the write side of the OWNED
subtree are complete; the create/unlink family is one kernel-tier lane
(WALL A fix (i), plus WALL C's credential for mkdir and the unarm) from
being payable, and its first corollary — `mkdir` at the owner's own root —
does not even need WALL B lifted.  No corollary and no extended test
landed in TL-3P: `UkTreeWrite.wp_uk_tree_write_moves` is unchanged, because
every syscall the extended test would add is behind WALL A.

### 7.6 TL-3K as landed — the cursor threaded, WALL B dissolved, and the two credentials that are left

**WHAT LANDED** (branch `tl3k-cursor`): WALL A's fix (i) in full, as a
kernel-tier RESTATEMENT across the whole create/unlink cone; WALL B's fix,
and it is smaller than §7.5 priced — a LIVE deed supplies the parent-prefix
walk at ANY length, not just at length 0 or 1.  `AppEcho.v` / `AppInv.v`
untouched, every landed TL-1/2/3/3W/3P statement unchanged except for the
two commits' new parameter, whole tree green, echo audit 14.

**WALL A, FIX (i), AS LANDED.**  `FsAbsCreateFire.acre_commit_at_gen` and
`SysUnlinkDefs.uent_commit_at` each gain a cursor parameter
`Pd : Z -> iProp Σ` and, beside `cre_pre` / `unl_pre`, the premise `Pd d`:

    acre_commit_at_gen Γ E cf Pd Farm Φ :=
      ∀ I d i nm ents nl,
        ⌜cre_pre (abs_view I) d nm ents nl i (cf d i)⌝ -∗
        cre_arm_fired Farm i -∗ Pd d -∗
        ghost_map_auth (γtop Γ) (1/2) I ={E}=∗
        ghost_map_auth (γtop Γ) (1/2) I ∗ Pd d ∗ app_step … ∗ (phase 2)

**IT IS READ AND HANDED BACK, IN PHASE 1**, and that is forced: the
caller's `P` is an arbitrary — possibly linear — predicate the kernel may
not duplicate, and the syscall's own POST owes the same cursor
(`cre_ok_arms`, `mknod_post_ok`, `unlink_post_ok` all carry
`P (length (npar_elems pl)) d`).  A supplier that does not care
instantiates `Pd` at anything and returns it unread; the generic
dischargers (`acre_commit_at_gen_unit`, `_pinned`, `uent_commit_at_unit`,
`FsAbsInvFire.fsabs_acre` / `fsabs_uent`) quantify `Pd` freely and their
proofs are unchanged but for framing it.

Three moves make every consumer a restatement:
  - `acre_commit_at_gen_cur` / `uent_commit_at_cur` — the cursor is a
    WEAKENING (a commit that holds at every `d` with no cursor holds a
    fortiori when one is handed in), and `SpecCreate.cre_commits_cur`
    lifts it over the whole four-leg bundle;
  - `acre_commit_at_gen_mono` / `uent_commit_at_mono` — the cursor moves
    along an ISO (both directions, because the commit reads the premise
    AND hands it back);
  - `SysMknodDefs.npar_cur M pv P d := ∀ pl, ⌜arg_path_of M pv pl⌝ -∗
    P (length (npar_elems pl)) d`, with `npar_cur_in` / `_out` off
    `ArgPath.arg_path_of_uniq`.

**THE CURSOR HAS TWO READINGS, AND WHICH ONE A BUNDLE CARRIES IS A FACT
ABOUT THAT BUNDLE'S WALK PREMISE.**  This is the lane's first new finding.
  - At the CREATE tier the path is fixed (`bview plen pfun`), so the
    instance is `P (length (npar_elems pl))` and `wp_create`'s bundle
    names it.
  - At the SYSCALL tier the bundle is stated BEFORE argstr has answered
    and the commits deliberately sit OUTSIDE the walk's path wand (a
    failed argstr must hand them back on the nose), so the instance is
    `npar_cur M pv P` — the same cursor under the same `arg_path_of`
    guard the walk carries, and still a BARE resource, so every failure
    fold keeps its shape.  `mknod_acre_inst` / `open_acre_inst` are the
    one-line moves between the two readings at the path argstr read.
  - **mkdir and unlink CANNOT CARRY A CURSOR AT ALL.**  Their bundles
    still take the raw `∀ pl` one-shot (`npar_walk_pre_era`), so there is
    no ONE path for a cursor to name; their commits are handed in at
    `Pd := fun _ => True` (the landed strength, zero semantic change) and
    lifted to create's cursor-threaded one by the weakening.  **So §7.5's
    "mkdir("/d") by the owner of / is reachable the moment WALL A falls"
    is WRONG**: mkdir waits on a path-fixed `mkdir_au_at` (mknod's
    `mknod_au_at` twin, additive) before WALL A can help it, and unlink
    waits on the same seam `UkTreeRead` §5 already records.

**THE STOP RULE DID NOT FIRE.**  Every fire site holds the cursor at the
fire instant, as §7.5 read it: `ProofCreateAlloc` and `ProofCreateMkdir`
both hold `HPpar : P (length (npar_elems (bview plen pfun))) (bv_unsigned
dind)` across `caf_acre_fire` and still need it afterwards (`cr_ok_of_made`),
which is exactly why the commit must hand the cursor back;
`ProofSysUnlinkW5D` / `W5F` hold theirs across `uf_uent_fire`.

**WALL B IS DISSOLVED, AND AT ANY LENGTH** (`PinnedObs` §11a,
`TreeWalk` §3).  §7.5 priced a linear-law hop PAIR reaching length 1.  The
reason length looked binding was that §8's dead walk THROWS `K` AWAY after
hop 0.  Put `K` ON THE CURSOR instead —

    pobs_P_lin T hops K k d := (⌜d = hops !!! k⌝ ∗ K) ∨ T

— and a hop takes `K` out of its INPUT cursor and puts it back into its
OUTPUT one, so the hop RESOURCE is built from persistent things alone (the
`□` linear law and `app_inv`) and the big-op needs no threading.
`pobs_phop_lin` / `pobs_pwalk_lin` / `pobs_pterm_lin` are the family;
`TreeWalk.tree_pwalk_of_own_live` / `tree_pwalk_parent_live` are the deed
route, out of `TreeObs.tree_own_claim_law` (the LIVE deed's own law), at
**any** parent prefix.  THE PRICE: under the taint (or a miss) the cursor's
right disjunct is `T` and `K` is gone — a tainted owner loses the deed it
put on the walk.

**THE SEAM THE LIVE WALK OPENS, and the one piece a corollary now needs.**
The terminal cursor CARRIES the deed, and the terminal cursor is exactly
what the cursor-threaded commit takes as `Pd d` — but the commit returns
`Pd d` in PHASE 1, while an owner's move PARKS the deed in phase 1 and gets
it back (moved) only in phase 2.  So a deed-carrying cursor wants the
commit to return `Pd d` AT PHASE 2, at the moved deed.  That is one more
kernel-tier restatement of the same shape as this lane's.

**WALL C IS NOT A RECEIPT-CARRIED CREDENTIAL** — the lane's main negative
finding, and it corrects §7.5.  What create's parent leg needs is
`aview_no_edge_to av i` AT ITS OWN VIEW; what the arm proves
(`aview_no_edge_to_arm`) is the same fact at the ARM's view, and between
the two instants the view moves arbitrarily as far as the logic can see.  A
receipt carries a RESOURCE, not a fact about a later view, and "nothing
names `i`" has no monotone reading that survives an arbitrary delta.  The
two honest mechanisms, both lanes of their own:
  - **(C-i) an ARMED LEDGER in the fs invariant** (kernel tier, NOT a
    restatement): `InodeRegion.ftop_body` gains "for every inum whose arm
    permit is out, no proper entry of the view names it".  It is
    MAINTAINED for a structural reason that is already in the design: the
    only way to insert an entry at `i` is the create leg, and that leg
    SPENDS the arm's permit (`cre_arm_fired`, the exclusive one-shot per
    armed inode — `acre_commit_at_gen`'s own note); the arm establishes it
    by freshness (`aview_no_edge_to_fresh`).  Price: one invariant
    conjunct and the three legs' preservation.
  - **(C-ii) an APPLICATION-side armed set** (tree tier): the owner
    records `i` in a ledger inside `tree_body` at the arm's phase 2 and
    reads it back at the parent leg; every step must then preserve it,
    which reproduces the same exclusion argument one tier up.
Unlink's last-link leg is the one case §7.5 is right about, and only
because `aview_no_edge_to_unl_ent` proves the credential at the ENTRY
LEG's own POST view — but the two legs are still separate commits, so it
needs the same channel.

**WALL D, NEW: the create leg does not know its name is proper.**
`TreeMove.tree_acre_phases` asks for `fs_pname nm`, and
`acre_commit_at_gen` quantifies `nm` with nothing said about it.  It is
TRUE at every reachable fire — create's own `dirlookup` returns the FOUND
arm at "." and "..", so `dirlink` is never reached with a dot name — but
the commit's altitude cannot see it.  Cheapest fix: `⌜fs_pname nm⌝` beside
`cre_pre`, discharged at the two fire sites from the path's properness.

**SO, AFTER TL-3K, AN OWNER'S CREATE SUPPLIER IS MISSING EXACTLY TWO OF
`tree_acre_phases`'s PREMISES** — `aview_no_edge_to (abs_view I) i` (WALL
C) and `fs_pname nm` (WALL D).  WALL A delivered the third,
`d ∈ dom (tv_nodes t)`, off `tree_pwalk_parent` (or
`tree_pwalk_parent_live` now).  That is why no corollary and no extended
test landed: `UkTreeWrite.wp_uk_tree_write_moves` is unchanged.
