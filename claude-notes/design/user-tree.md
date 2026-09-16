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
- **The application tree** (this page): a PURE reading of `aview`, the
  live namespace (`FsAbsDefs.abs_view`, §4's "the view is the live
  namespace"), at a root: `subtree av r : fstree` (the nodes reachable
  from `r` by directory entries, dots hidden, `fsnode`/`anode` are the
  same shape modulo `nlink` and `ADev`).  It lives in `app_pred`,
  never in a kernel invariant (the owner's rule: nothing
  application-specific inside a kernel fs invariant).

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
  other entry unchanged by DISJOINTNESS: non-nested roots + directories
  form a tree (no directory hard links) ⇒ subtrees are node-disjoint ⇒
  a move at `d` inside `t_P` is outside every `t_Q`.  The premise the
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

- [ ] **TL-1 THE PURE LAYER** (Opus; zero Iris): `subtree`, `own_wf`,
  subtree disjointness from non-nested roots + `fs_dirs_acyclic`, the
  δ lemmas (inside ⇒ tree op; outside ⇒ unchanged) over §4's landed
  `FsAbsDelta` legs, `resolves_in` (path resolution in a tree) ⇔
  `arun` on the view.  All closed lemmas; the whole campaign's proof
  content is here.
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
