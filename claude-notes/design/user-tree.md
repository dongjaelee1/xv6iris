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
- [ ] **TL-3 THE STABLE COROLLARIES**: open/read/write/mkdir/unlink at
  an owned subtree, each an instance of a landed member + agreement;
  the `user.tex` §7 figure for the owned-subtree `open`.
- [ ] **TL-4 THE SECOND APPLICATION**: the end-to-end instance of §4.3
  at `xv6_app_adequacy`, with its own `make audit` line.
