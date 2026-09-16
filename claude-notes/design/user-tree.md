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
- **Grant** at fork/exec: a parent re-partitions its entry — `t_P` at
  `root_P` becomes `t_P ∖ t_C` plus a new entry `(root_C, t_C)` for the
  child — a ghost move with NO view move (`app_top_update_same` is not
  even needed: the claim's ∗ re-associates by a pure lemma).  Boot: the
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
    (`nclose_content_edit`), create's arm+parent leg (`top_ins`, the
    fresh-leaf insert), link's parent leg (`top_link`), unlink's entry
    leg (`top_unlink`, the ONE op that re-closes, because it is the only
    one that can orphan), and the four invisible legs.  `subtree_delta_*`
    is the naming.
  - `resolves_from` / `resolves_in` / `resolve_hops` and the equivalence
    with `arun` on the view, both directions, plus the relative form from
    a cwd inside the subtree.  Paths are PROPER (`fs_proper (path_elems
    pl)`): `..` at the root leaves the subtree, which is the one move the
    claim cannot answer — a pure side condition on the program's own
    string.
  - `own_wf` preservation per δ (`own_wf_write`, `own_wf_create`,
    `own_wf_unl_ent`, `own_wf_unl_tgt`).  Two side conditions fell out
    and are stated where they bite: an owner may not unlink a ROOT (its
    own or anyone's), and the row may only leave when nothing names it
    (`aview_no_edge_to` — the `nlink`-vs-edge-count tie, which the tree
    layer does not carry, and which the entry-leg-first order gives).
- [ ] **TL-2 THE APPLICATION** (Opus): `AppTree.v` — the record
  instance with `tree_pred`, the claim law, the step wands per δ for an
  owner's deposit (the `_step` payments), grant at fork/exec, boot at
  `/`; `exec_walk_of_own`.  Echo audit unaffected (a second record, not
  a change to echo's).
- [ ] **TL-3 THE STABLE COROLLARIES**: open/read/write/mkdir/unlink at
  an owned subtree, each an instance of a landed member + agreement;
  the `user.tex` §7 figure for the owned-subtree `open`.
- [ ] **TL-4 THE SECOND APPLICATION**: the end-to-end instance of §4.3
  at `xv6_app_adequacy`, with its own `make audit` line.
