# Design: the programs' specs as INTERACTION TREES (proposal, 2026-09-23)

**Status: PROPOSAL, awaiting the owner's ruling.**  Asked by the owner
(2026-09-23): unified specs for the user programs (echo, cat, later grep,
sort, …) so that each program is proved ONCE and its spec serves every
line it can appear in — `echo foo`, `echo foo > f`, `echo foo | cat`,
`cat f`, `cat f | cat`, `cat f > g` — and an evaluation of whether the
landed specs, and [`app-both.md`](app-both.md) §5's endpoint proposal,
are general enough.  This file is that evaluation (§1, §2) and the
proposal it leads to (§3, §4).  Its pure half is built:
`iris/ProgTree.v` (the events, the two programs' trees, an interpreter,
and every line shape above computed by `vm_compute`).  Nothing imports it.

## 0. What a program spec has to do

- ONE theorem per program, stated without naming where its descriptors
  point, so that a line shape (the shell's provisioning of the process's
  descriptor table) is what varies and the program's theorem is not.
- The theorem must determine the process's VISIBLE behaviour at every
  destination: the bytes on the console, in a file, through a pipe —
  including their order across descriptors and the kernel's own
  answers (a failed open, a write into a pipe whose reader has gone).
- It must be readable and RUNNABLE without the logic, the way the line
  models are (`FileDisc`'s `vm_compute` demos), so that a new program's
  spec can be checked against the C before its proof exists.

## 1. What the tree has, read as a spec

Each program's code walk is stated over caller-supplied obligations, one
per syscall the C makes, in continuation-passing style:

- echo (`UkEcho.kecho_pay_all`): a chain of `kecho_w ua nb Ci Co`, one
  per `write`, then the exit payload.
- cat (`UkCatMain.kcat_pay_all`): per path, `kcat_o` (the open) whose
  post is an additive pair — the `-1` arm (`kcat_dg_open`: the
  diagnostic, one `kcat_pay_seq` node per BYTE, since xv6's `fprintf`
  writes byte by byte) or the descriptor arm (`kcat_run0`, one
  persistent ROUND LAW `UkCatCat.kcat_round`: read, then by the count the
  read returned, the write of exactly those bytes, back to the invariant
  or out at EOF) — then `kcat_cl`.

**That IS an interaction tree**, hand-unrolled: the events are the
syscalls, each node's continuation is indexed by the kernel's answer,
and cat's loop is the tree's `iter`.  "Prove the program once" already
holds for the WALK — `UEchoFile`/`UEchoPipe` say "echo's code walk is
untouched" — and fails one level up, for four reasons that are all in the
shape of the nodes:

1. **The nodes are machine-shaped.**  Every obligation is
   `∀ h m avail, ⌜three registers⌝ -∗ code -∗ Ci -∗ urun … -∗
   (∀ h' ret, Co -∗ urun … -∗ mWP Loop) -∗ mWP Loop`.  A destination that
   funds one must run the U-tier syscall leaf itself
   (`UkRunSys.wp_uk_ecall_write_chain_buf`, `UkFileOpen`'s deed leaves,
   `UkReadPipe`'s), against its own resource, inside the program's file
   layout.
2. **The vocabulary is per program.**  `kecho_w` and `kcat_wr` are the
   same write obligation at `echo_code γt`/`EchoSyms.write` versus
   `cat_code γt`/`CatSyms.write`.  So the conversion "the console cursor
   funds a write" is proved once per PROGRAM: `UEchoOut` for echo,
   `UCatKernel.cat_w_of_link` for cat — the same lemma twice.
3. **The bytes are not in the node.**  A write node carries the buffer
   ADDRESS and the count; the bytes reach the payer through resources
   (echo's persistent argv, cat's owned buffer).  The visible event
   "write these bytes on this descriptor" is never literally stated.
4. **The entry is per (program, destination).**  Five entry theorems for
   two programs — `UShEcho.echo_image_entry` (console),
   `UEchoFile.efile_image_entry` (file), `UEchoPipe.ep_image_entry`
   (pipe), `UCatKernel.cat_image_entry` (file), `UShCatPay.
   cat_image_entry_1w` (pipe) — and six destination files (`UEchoOut`,
   `UEchoFile`, `UEchoPipe`, `UCatOut`, `UCatKernel`, `UCatPipe`, ~7.6k
   lines) of which the program-specific half is the conversion of (1)–(3).

So a new line shape today costs a destination file and an entry per
program in it, and a new program costs one per destination it can face.
That is the product the owner is asking to remove.

## 2. app-both §5's endpoints (`Out fd S` / `In fd S`), assessed

**What they get right.**  The program's theorem stated at obligations
built from two laws (`Out fd (bs ++ S') ⊢ write(fd, bs) {|bs| ∗ Out fd S'}`,
`In fd S ⊢ read {c ∗ In fd S'}` with `S = c ++ S'`), the six destination
files becoming instances of the two laws proved once per (syscall,
destination) instead of per program, and chunking free.  For the four
landed line shapes that is enough, and much cheaper than today.

**Where they are not general enough**, each with the line that shows it
(every one is computed in `ProgTree.v`'s demos):

1. **Order across descriptors.**  `cat f g` with `g` absent prints `f`'s
   content on fd 1 and then `cat: cannot open g` on fd 2, and both are
   the console.  `Out 1 S1 ∗ Out 2 S2` says nothing about which comes
   first; the console instance would owe an interleaving that only the
   program's own order decides.  (`demo_cat_f_then_absent`.)
2. **The kernel's answers.**  An open of a PRESENT `f` may return `-1`
   (`FileDisc.RCNoOpen`: `filealloc`/`fdalloc`), a pipe write may return
   `-1` when the reader has exited (`UEchoPipe`'s halt arm).  The
   program's behaviour is therefore a SET of traces, one per answer
   sequence, and a spec with one `S` per descriptor chosen from the file
   system's state needs a second spec per arm ("and if the open fails,
   this instead").  The line models already carry these arms.
3. **Two concurrent writers** on the console (`PipeDisc.PBoth`): §5.6
   concedes a split law is needed and leaves it in the pipe module.
4. **Granularity.**  Chunking is invisible on one stream and visible
   when two processes share a device: the `PBoth` interleaving is
   per byte BECAUSE `fprintf` writes per byte.  A stream spec forgets the
   granularity the model needs.
5. **The rest of the process's footprint** — its exit status, and the
   close of a pipe's write end (which IS the reader's end of file) — has
   no endpoint.

**Verdict.**  `Out`/`In` are the right HANDLER for a linear stream on one
descriptor, which is the common case; they are not the right SPEC.  The
spec has to carry the program's order and branch on the kernel's answers,
and that is exactly what the landed walks already do, in the wrong
vocabulary (§1).

## 3. The proposal: the tree is the spec; the endpoints are its handlers

### 3.1 Events and trees — `iris/ProgTree.v` (built)

    ev : Type → Type      EOpen path mode : ev Z    EClose fd : ev Z
                          ERead fd n : ev rd_ans    EWrite fd bs : ev Z
                          EExit status : ev Empty_set
    itree R  (Ret / Tau / Vis)   bind, iter, trigger      proc := itree Empty_set

Twenty lines, no library (the switch has no itree package, and nothing
here needs bisimulation: a tree is only ever interpreted or paid, never
compared to another).  A program's spec is `prog_tree : list bytes → proc`
— `echo_tree`, `cat_tree` are transcriptions of the C, one node per
syscall.  Two rules decide what is a node:

- **Visibility.**  An event is a syscall whose effect or answer another
  process, the disk or the console can see.  `sbrk`, the trap itself,
  exec's argument copies are `Tau` or absent.  `close` IS an event (a
  pipe's reader sees it); `exit` is (its parent does, and it closes).
- **Granularity is the C's.**  One `EWrite` per `write` call: `fprintf`
  is a run of one-byte writes, echo writes each word and its separator,
  cat writes each chunk it read.  Coalescing is a handler's business
  (§3.4), because it is only sound on a stream nobody else writes.

The interpreter (`run`, `line_plain`/`line_redirect`/`line_pipe`) is the
pure reading of "what happens when": a world (console, files, pipes), a
descriptor table per process — WHICH IS THE LINE SHAPE, and nothing a
tree depends on — and the kernel's good answers.  The demos compute every
line shape of the union application and `demo_echo_is_wl_line` checks the
console projection against the line model's own block.

### 3.2 One theorem per program

Over a PROGRAM INSTANCE (its code resource, its stub addresses — the
`usys.S` stubs are the same three instructions in every binary), define
ONCE:

    ev_obl (e : ev X) (K : X → iProp) : iProp
      the machine-shaped hole of §1(1), one per event constructor, with the
      BYTES in its statement (a write hands the payer the run at the
      address, as [ubytesq]/[utext]; a read hands the buffer and gets it
      back at the answer's bytes)
    tree_pay (t : proc) : iProp
      Tau t'   ↦ ▷ tree_pay t'
      Vis e k  ↦ ev_obl e (λ x, ▷ tree_pay (k x))
      (a guarded fixpoint; every Vis costs machine steps, so the later is
       strippable at the leaf)

and the program's theorem is its ENTRY at the tree:

    image_entry f … Q (tree_pay (prog_tree argv)) uslot

"for any payer of the tree's events, the process is safe and does what
the tree says".  `kecho_pay_all args Ci Cend` IS `tree_pay (echo_tree …)`
unfolded; cat's `□ kcat_round` IS `tree_pay` at `iter` (what the round
law's persistence bought, the `▷` under `Vis` buys).  The five entries of
§1(4) become two, stated at no destination.

### 3.3 Handlers, once per (event, destination)

A handler is what answers `ev_obl` at a destination, with its own state:

    console:  the claim's cursor at the line's alternative (`ck_cur`/`ech`/
              `cch` — a write at the alternative's continuation)
    file:     the deed and the held offset (`FileWrite.file_wq`, `Hold p`)
    pipe:     `PipeProto`'s write and read cursors (`wcur`/`rcur`)

The lemma proved once: a handler that answers every event of `t` pays
`tree_pay t` (Löb over the tree).  The six destination files reduce to
handler facts that name no program — the deed open at `fname_f`, the
kill arm's taint, the ordering at the held offset, the kernel's answer
set per destination (console: always the count; pipe: the count or `-1`
with the reader gone; file: the count or `-1` at a full disk, which the
application refutes).

### 3.4 `Out fd S` / `In fd S` are the STREAM handler

§5's two laws are exactly a handler for a tree whose events on `fd` are
writes in order: `Out fd S` answers `EWrite fd bs` when `bs` is `S`'s
next chunk.  They stay, as the derived layer a line shape provisions
where one process owns one stream (every landed shape but `PBoth`).
The pipe: `pipe()` mints `Out w S ∗ In r S` over the protocol.

### 3.5 The line model's continuation becomes a theorem

`lmodel`'s `lm_cont s l a` is hand-written bytes per alternative.  With
the trees it is DERIVED: the console projection of the interpreted trees
at the alternative's answer sequence and schedule — `demo_echo_is_wl_line`
is the first instance.  The line model, the generic families and the
claim (M1–M3) do not move; the conversion discipline is theirs.

### 3.6 What stays where it is

- Two writers on the console (`PBoth`, `PForkS`) are a SCHEDULE's
  interleaving of two trees' byte writes; the pipe module owns it, as
  today.  The trees make the per-byte granularity it needs literal.
- Liveness (a pipe read that blocks) is outside: the interpreter's
  left-first schedule is one valid schedule for a left output that fits
  the pipe, which the line discipline guarantees.

## 4. Order of work (replaces app-both M4's step list; each cut lands green)

1. `ProgTree.v` — landed as a leaf, with the demos.
2. `UkTree.v` (Iris, at `UkRunSys`): `ev_obl` at a program-instance
   record, `tree_pay`, the handler lemma; `kecho_w`, `kcat_wr`/`kcat_r`/
   `kcat_o`/`kcat_cl` shown equal to the generic holes at their program's
   instance, so the walks do not move.
3. The walks' statements at `tree_pay (echo_tree …)` /
   `tree_pay (cat_tree …)`; the free chains (the vacuity guards) at the
   free handler.
4. The three handlers (console from `GenLinks`/`gcl`'s cursor; file from
   the deed; pipe from the protocol); the six destination files reduced
   to instantiations.
5. The two entries at a handler parameter; the five landed entries as
   corollaries; then the shape modules (M4) and the union (M5) as planned.

The risk is in step 4's console handler at the two-writer arm, which
stays pipe-own; steps 2–3 are a restatement of ~15k lines to a smaller
shape, and nothing above the entries changes statement.

## 5. Refuted, or not taken

- **The itree library** (`coq-itree`, with `paco` and `ExtLib`): not in
  the switch, and nothing needs `eutt`.  The twenty-line definition is
  enough; if a later need for bisimulation arises, the library's `itree`
  is the same type and the trees port.
- **Refinement up to chunking** (one `EWrite` for a whole `fprintf`):
  rejected by §2 item 4 — the interleaving model needs the C's
  granularity.  Coalescing is the stream handler's, where it is sound.
- **A syntactic program language** (an inductive tree with a loop node)
  in place of the coinductive tree: gives the round law directly, but is
  not the standard object and cannot be interpreted as a tree elsewhere;
  the guarded `tree_pay` gives the same round law at `iter`.
