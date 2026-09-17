# Design: the PIPELINE application (`AppPipe`) — `echo … | cat` prints the line

**Design of record, opened 2026-09-17 (Fable, on the owner's "go for the
pipeline application").**  Worklist: [`../projects/app-pipe.md`](../projects/app-pipe.md).
Builds on [`applications.md`](applications.md) (the claim scaffold),
[`pipe.md`](pipe.md) "The byte queue" (the pipe's exact ghost state and its
links), [`user-fd.md`](user-fd.md) (the program's descriptor ledger),
[`user-exec.md`](user-exec.md) (the exec channel `image_entry`),
[`user-proc.md`](user-proc.md) (fork's lend / exit payload, wait) and the
echo application's statement (`iris/EchoDisc.v`, `iris/EchoOut.v`,
`iris/EchoLinks.v`; worklist `../completed/app-echo.md`).  Upstream's FILE
application ([`app-file.md`](app-file.md)) is the mould for the campaign's
SHAPE (a pure model beside `EchoDisc`, a record beside `AppEcho`, an
adequacy file and an audit); this design shares no file with it.

## 0. The target, in one paragraph

The same image, the same /init and /sh.  A user types, at the console,
lines of two shapes: `echo w1 … wn` (the echo application's line, its
claim unchanged) and `echo w1 … wn | cat`.  THE CLAIM: **the console shows
the line** — after `echo hello world | cat` the console prints
`hello world`, then the prompt — with the file system unmodified at every
state (the echo application's invariant, verbatim), and the alternatives
exactly the visible failures: sh's `pipe`/`fork` panics, `exec echo
failed`, `exec cat failed`, both diagnostics interleaved when both execs
fail, and the empty continuation of a child that died before printing.
Nothing but the line and those diagnostics ever reaches the console in a
pipeline round.  It is the FIRST application to hold a pipe: a verified
process creates one, two verified processes hold its two ends across
`fork` and `exec`, and every byte through it is exact ghost state.

**WHAT IT PAYS FOR that nothing in the tree has paid before**, each priced
in its section: a verified program that holds a pipe and is NOT tainted
(§2, the ruling `completed/pipe-queue.md` deferred to "an application that
has to do pipe reasoning"); the pipe's contents as a protocol shared by
three processes (§3); sh's PIPE arm — the last unverified arm of `runcmd`
(§5.1); two console writers at once (§4.3, the one new stage mechanism);
and the pipe's read and write leaves at the STANDARD slots (§5.4).

**THREE HONEST LIMITS, stated up front:**

1. **`echo`'s writes into the pipe can fail invisibly only by the reader
   vanishing.**  `pipewrite` returns `-1` when `readopen == 0`
   (`kernel/pipe.c`), which under the discipline happens only when cat's
   process exited before reading — the `exec cat failed` alternative — and
   echo ignores write's return.  In that alternative the line is not on
   the console anyway, so the model says nothing about the pipe's final
   contents there.  A pipe write never fails for lack of space at a line
   under `line_max < PIPESIZE`, and never partially: `pipewrite` copies one
   byte per iteration and a mapped source refutes the `copyin` fault
   (READ-RELAY's twin, already on `pipe_wchain`'s nodes).
2. **When both execs fail the two diagnostics interleave byte-wise** on the
   console (each `fprintf(2, …)` is one `write` per byte, and the two
   children run concurrently).  The model admits EVERY interleaving
   (§1's `PBoth sel`) and the proof pays it with a two-writer lease (§4.3).
   This is a real behaviour of the machine, not a modelling artefact.
3. **Nothing is said across a power cycle beyond the echo application's
   claim** (the file system keeps its pins; a pipe does not survive a
   boot).  The pipe protocol is per era and dies with it.

## 1. The pure model (`iris/PipeDisc.v`)

Iris-free, over `EchoDisc`/`LineWords`, in `FileDisc.v`'s style (a line
type, an alternative type, a continuation function, a fold), so that the
statement can be read and refuted without the logic.

**Lines.**

    Inductive pline := LEcho (ws) | LPipe (ws).
    line_bytes (LEcho ws) := wl_line ws                        -- "echo a b\n"
    line_bytes (LPipe ws) := wl_body ws ++ " | cat" ++ [wl_nl]  -- "echo a b | cat\n"
    pline_ok (LEcho ws) := EchoDisc.line_ok ws
    pline_ok (LPipe ws) := EchoDisc.line_ok ws /\ length (line_bytes (LPipe ws)) < line_max

`parse_pline : list (bv 8) -> option pline` inverts the body (the newline
stripped, as `LineWords.bodies_of` cuts it), decidable; `disc_input_p` is
prefix-closed the way `disc_input` is, with the partial line's bytes
`pbody_byte := wl_body_byte ∨ '|'`.  sh's lexer sees `|` as a symbol
token; the pipe is canonical (one blank each side; the right command is
the single word `cat`), which is what the sh walk (§5.1) is stated at.
`cat` here is `/cat` with NO argument — cat reads its standard input.

**Rounds and alternatives.**  A round is one typed line; its console
continuation is decided by ONE alternative:

    Inductive palt :=
      | PEcho (a : nat)          -- the echo application's four, unchanged (LEcho lines only)
      | PRan                     -- wl_line (drop 1 ws) ++ "$ "        : the line, then the prompt
      | PExecL                   -- "exec echo failed\n$ "             : left exec failed; cat printed nothing (EOF at an empty pipe)
      | PExecR                   -- "exec cat failed\n$ "              : right exec failed; echo's bytes went into the pipe and stayed there
      | PBoth (sel : list bool)  -- merge sel dg_execL dg_execR ++ "$ " : both failed; sel is the interleaving (length = |dg_execL| + |dg_execR|, true = a byte of the left diagnostic)
      | PPipe                    -- "pipe\n$ "                         : pipe(2) failed; sh's panic in the runcmd child
      | PFork                    -- "fork\n$ "                         : a fork1 failed in the runcmd child (either one)
      | PSilent.                 -- "$ "                               : a child died before printing (argv[0] == 0; unreachable under the discipline, kept as echo's alt 2 is)

    palt_ok (l : pline) (a : palt) : Prop     -- which alternatives a shape admits; PBoth's sel has the right length and count
    pcont (l : pline) (a : palt) : list (bv 8) -- the continuation bytes above (EchoDisc.line_alts_of at PEcho)

Two things to notice, because they are what makes the claim cheap:

- **`PRan`'s continuation is exactly `LEcho`'s good alternative** — the
  same bytes the echo application prints for `echo a b`.  cat copies.
- **`PPipe` and `PFork` are followed by the PROMPT, not by the prologue.**
  `runcmd` runs in the child sh's main loop forked; `panic` there exits
  the CHILD (`user/sh.c:panic` is `fprintf(2, "%s\n", s); exit(1)`), the
  parent's `wait(0)` returns and it prints the next prompt.  The echo
  application's `alt_panic` is the MAIN loop's `fork1` failing, which does
  kill the shell and re-enter the prologue; that arm is unchanged and
  `LPipe` lines reach it exactly as `LEcho` lines do (it is decided before
  the line is parsed).  `PFork` covers BOTH forks: if the second fails the
  first child is already running echo into a pipe whose read end the
  panicking parent closes on exit; nothing reaches the console.

**The session.**  `EchoDisc.sess` with `alt_blk` reading `pcont` through
the parse: `sessp (ps cs : list nat) (I : list (bv 8))`, where `cs !!! i`
indexes `palt` through an injective `nat` encoding (so the stage's
`cs_auth`/`cs_lb` machinery is reused verbatim, as `FileDisc` did) and
`palt_ok` is the decidable range condition where `c < 4` was.  `PBoth`'s
`sel` is PART OF THE ENCODING: one alternative per interleaving, so the
transcript is a function of `(ps, cs, I)` and the determinacy proof
(`sessp_prefix_det`, the twin of `EchoOutPure.sess_prefix_det`) runs on
the same one observation — every non-panic continuation is a `$`-free run
followed by the prompt.  (`merge sel d1 d2` contains no `$`: neither
diagnostic does.)

**The theorem's conclusion** is the echo application's, at the new
session: `pipe_phi h := disc_p h -> forall each cycle, exists ps cs,
pro_ok ps cs _ /\ Forall2 palt_ok (lines_of …) cs /\ obs_wire Uart0 seg
`prefix_of` sessp ps cs (ins seg)` — `EchoDisc.good_out` with `sessp`.
The file-system half of the claim is `echo_phi`'s, unchanged.

Demos by `vm_compute`: the success transcript, `PExecL`, `PBoth` at two
different `sel`s, and one NEGATIVE witness (`echo hello | cat` printing
`goodbye` is refuted) — the vacuity rule of `durable-notes.md`.

## 2. A verified program holds a pipe: the REGISTRY replaces the taint

**THE WALL, as landed.**  `UkRunSys.wp_uk_ecall_pipe` takes
`□ riscv_kill_cred` — the taint — as a premise: "a program that opens a
pipe pays its own tear-down's closes out of the taint".  `UkRun.urun_nopipe
fdv := ⌜fdv_nopipe fdv⌝ ∨ □ riscv_kill_cred` is the run's persistent
reading that pays the exit row (`UexecExecInst.xv6_sbundle_exit_nopipe`
mints `fileclose_cpays` from nothing at a pipe-free table); every verified
program today carries the LEFT arm, and after `pipe(2)` only the right arm
is available.  `completed/pipe-queue.md` "Open, recorded" names this as the
ruling an application with pipes would have to make, and names the second
half too: the exit row is a `[∗ list]` of INDEPENDENT payments, so two rows
on one pipe (sh holds `p[0]` and `p[1]`) cannot both be paid by links built
from one exclusive fragment.

**THE RULING (this design): the pipe's fragment lives in a PER-PIPE
INVARIANT, and what the run carries is the invariant's persistent handle,
one per pipe row.**  Both halves fall at once: a link built from an
invariant handle is buildable any number of times (`□`), so two rows on
one pipe and every dup/fork copy of a row pay from the same handle, and no
program ever holds the fragment.  Concretely (`iris/PipeReg.v`, U tier,
below `UkRun`):

    pipe_reg γp : iProp Σ  :=  □ (∀ w : bool, pipe_cpay (pn_queue γp) w emp)
    -- the exit row's payment for a row on this pipe, at either end, forever

    pipe_row_reg (st : fdstate) : iProp Σ :=
      match st with FdOpen _ _ (FdPipe γp) => pipe_reg γp | _ => emp end

    urun_nopipe fdv  :=  [∗ list] st ∈ fdv, pipe_row_reg st        -- REDEFINED; the name stays

The old arms are the two intro lemmas: `urun_nopipe_intro : fdv_nopipe fdv
-> ⊢ urun_nopipe fdv` (every row's registration is `emp`) and
`urun_nopipe_taint : □ riscv_kill_cred -∗ urun_nopipe fdv`
(`pipe_reg_of_taint`: the taint is a `pipe_cpay` at every end).  The
predicate stays PERSISTENT and TIMELESS, so every site that takes
`urun_nopipe` as an opaque hypothesis (the ~25 `iAssert (urun_nopipe …)`
sites listed in the worklist) compiles unchanged.  What moves:

- **The exit row's mint**: `xv6_sbundle_exit_nopipe` becomes
  `xv6_sbundle_exit_regs : urun_nopipe (uvis_fd W) -∗ |==> ∃ f, ⌜kf_xpay f
  = Q⌝ ∗ xv6_sbundle X USYS_exit f W` — `fileclose_cpays sts` is exactly
  `[∗ list] st ∈ sts, fileclose_cpay st emp`, and `fileclose_cpay st emp` at a
  pipe row IS `pipe_cpay (pn_queue γp) w emp`, one instance of the row's
  `pipe_reg`.  The `_nopipe` lemma stays as a corollary.
- **Preservation**: `UkRun.urun_rows_insert` (close installs `FdClosed`:
  `emp`), dup (copies a row: the registration is persistent), open (a
  non-pipe row), fork (the child's table is the parent's: the same
  `[∗ list]`), exec (the table is kept).  `UsysMemOk.usys_fd_ok_nopipe`
  stays as the pure fact it is; the U-tier lemma beside it is
  `urun_nopipe_step : usys_fd_ok n tf r sts sts' -> n <> USYS_pipe ->
  urun_nopipe sts -∗ urun_nopipe sts'` — every new row of `sts'` is a row
  of `sts` or a non-pipe row (the reading `usys_fd_ok` already gives; the
  proof is `usys_fd_ok_nopipe`'s case split with a resource instead of a
  Prop).
- **The pipe leaf**: `wp_uk_ecall_pipe` drops the `□ riscv_kill_cred`
  premise.  Its post hands the caller `pipe_qfrag (pn_queue γp) pst0` (as
  today) and the run OWED THE REGISTRATION: `(pipe_reg γp -∗ urun N h' m'
  pc' avail')` in place of `urun …`.  The caller allocates whatever
  invariant it likes around the fragment, derives `pipe_reg γp` from its
  handle (§3's `pipe_reg_of_inv`), and redeems the run.  A caller that
  wants the old behaviour redeems with `pipe_reg_of_taint`.  STOP RULE for
  the lane: if the run cannot be split that way (the table lives inside
  `urun`'s existential and the two new rows are named only by the post's
  scans), the fallback is a registrar PREMISE `∀ γp, pipe_qfrag (pn_queue
  γp) pst0 ={⊤}=∗ pipe_reg γp` on the leaf, at the same mask the leaf's
  post runs — report which shape landed.

**VACUITY CHECK, written first** (durable-notes "Vacuity"): `pipe_reg γp`
must NOT be provable from nothing.  It is not — `pipe_cpay` is `pipe_clink
∨ pipe_taint_cred`, a `pipe_clink` needs a `pipe_qauth` step that only the
fragment's holder can make, and the taint is not held under the
discipline.  State it as `pipe_reg_not_free` in the scratch and keep it as
a comment.

## 3. The protocol: one invariant per pipe, three processes

`iris/PipeProto.v`.  The runcmd child (sh) allocates it right after
`pipe(2)`, before `fork1`; echo (fd 1 = the write end) and cat (fd 0 = the
read end) reach it through the exec channel; the runcmd child closes both
its ends through the registry and never opens the invariant again except
at the end of the round (§4.2).

**The ghost state** (`pipeProtoG`): a `mono_list` of bytes `γws` (the
pipe's `ps_ws`, as a lower-bound-able history), an agreement cell
`γeof : option (list (bv 8))` (the reader's EOF snapshot, once), an
exclusive token `wtok γw` (the writer's start token).  The names are one
record `pnames`, persistent once allocated.

**The body**, at the line `L := wl_line (drop 1 ws)` (the bytes echo
writes: `EchoDisc`'s good continuation minus the prompt):

    pipe_body pn γp L : iProp Σ :=
      ∃ s : pipe_st,
        pipe_qfrag (pn_queue γp) s
        ∗ mono_list_auth γws 1 (ps_ws s)
        ∗ ⌜ps_ws s `prefix_of` L⌝                                   -- (P1) only the line goes in
        ∗ (⌜ps_ws s = []⌝ ∨ wtok_spent γw)                           -- (P2) nothing goes in before echo starts
        ∗ (∀ w, ⌜γeof ↦ Some w⌝ -∗ ⌜w = ps_ws s /\ ps_wo s = false⌝)  -- (P3) after EOF the contents are frozen
    pipe_inv pn γp L := inv pipeN (pipe_body pn γp L)

(P3) is stated with the agreement cell's persistent reading; `γeof ↦
None` is the live arm.  `wtok_spent γw` is the persistent "the token went
in" (the token itself sits in the body once spent).

**The links, and why each is buildable from the invariant** (the fupd of
every link runs at `⊤`, the payload held, no invariant open — `pipe.md`):

| who | link | what it does inside, and what it needs |
|---|---|---|
| anyone (registry, §2) | `pipe_clink … w emp` | open, lend the fragment, `pst_close w`: (P1)/(P2) untouched, (P3) holds because `pst_close` leaves `ps_ws` alone and only clears a flag. NO knowledge needed — `pipe_reg_of_inv : pipe_inv pn γp L -∗ pipe_reg γp`. |
| echo, first byte | `pipe_wlink … b _` | spends `wtok γw` into the body (P2's right arm), appends `b` to `γws`; needs (P1): `ps_ws s ++ [b] ⊑ L` — echo's chain node knows `b = L !! j` and, from the `mono_list` lower bound it carries at cursor `j`, `ps_ws s = take j L`… |
| echo, byte `j` | `pipe_wlink … b _` | …which is exactly what a fresh `mono_list_lb γws (take j L)` plus (P1) gives (`ws ⊒ take j L` and `ws ⊑ L` and `|ws| = j` from the previous node's `Qe`/`Q` — the chain's `Q j` carries `⌜length (ps_ws s) = j⌝` as a lower bound is not enough: carry the EXACT length in `Q j` as a `mono_list_lb` of length `j` plus the invariant's `⊑ L`, which pins `ws = take j L`); (P3): the write link is fired ONLY at `ps_wo s = true` (§3.1), and `γeof = Some w` forces `ps_wo s = false`, so the arm is refuted. |
| echo, last byte | the same | additionally hands its chain's `Q` a persistent `mono_list_lb γws L` — "the line is in" — which rides echo's EXIT PAYLOAD back to sh. |
| echo's chain, observation node (`Qe j s`) | `pipe_olink` | fires where the write stops on a shut read end (`ps_ro s = false`): the `PExecR` world; echo's `Qe` records nothing and its exit payload carries the taint-free "I stopped at `j`" — sh does not need it (§4.2). |
| cat, each byte | `pipe_rlink` | dequeues `b = ps_ws s !! ps_rp s`; cat's chain carries its cursor `c = ps_rp s` (its own `Q acc` says `⌜ps_rp s = c + length acc⌝` and `acc = take (length acc) (drop c (ps_ws s))`), so the dequeued bytes ARE `L`'s bytes at `c..` by (P1) — which is what cat's console write at cursor `c` needs (§4.1). |
| cat, observation node (`Qe acc s`) | `pipe_olink` | fires where the ring runs dry.  If `pst_eof s` (empty AND `ps_wo s = false`): cat SETS `γeof := Some (ps_ws s)` — (P3)'s premise becomes true at exactly the state it describes — and takes the persistent `γeof ↦ Some w` out.  If merely empty with `ps_wo s = true`: `piperead` did not return 0 (it sleeps), the node hands the count back and cat's loop turns again; the node records nothing. |
| cat, EOF | — | cat's exit payload carries `γeof ↦ Some w` and `⌜w = the bytes cat printed⌝` (its console cursor at exit is `length w`). |
| sh, after both waits | none (a plain `inv` access) | §4.2. |

### 3.1 One premise on the write link: `ps_wo s = true` (lane PQ-FLAG)

(P3) is preserved by a write link only if no write link fires after EOF —
true of the machine (a `pipewrite` runs on behalf of a process holding a
WRITABLE file on this pipe, so `writeopen ≠ 0`), and the kernel already
has the fact as a resource: `PipeInvDefs.pipe_endstate γp w v` with
`pipe_ref γp w q -∗ ⌜pflag_open v⌝` (`PipeInvDefs.v:589`), and the
coupled arm of `pipe_qres` reads `ps_wo s = pflag_bool wo`.  So
`PipeQueue.pipe_wlink` gains ONE pure premise:

    pipe_wlink γ b Φ := ∀ s, ⌜ps_wo s = true⌝ -∗ pipe_qauth γ s ={⊤}=∗ pipe_qauth γ (pst_write b s) ∗ Φ

and symmetrically `pipe_rlink` gains `⌜ps_ro s = true⌝` (free, for
symmetry and for a future reader-side protocol).  A premise on a link
WEAKENS what its holder must provide, so every `_of_frag` constructor and
every chain lemma goes through by ignoring it; the two fire sites
(`ProofPipewrite`'s `sw` of `nwrite++`, `ProofPiperead`'s of `nread++`)
supply it from the caller's `pipe_ref` through `pipe_endstate`.  If the
fire site does not have the ref in hand at the store (it is the FILE
layer's, `SpecFilewrite`'s pipe arm), the lane threads the one pure fact
down from `filewrite`'s `f->writable` test — report which.

Without 3.1 the protocol has no way to freeze the contents at EOF: the
generic close link (§2) fires at the LAST write-end close, which may be
sh's or the cat child's rather than echo's, and none of them can prove
"the line is in" at that instant.  The snapshot-plus-freeze shape is what
lets sh combine echo's "the line is in" with cat's "I printed exactly the
frozen contents" AFTER the fact (§4.2), without anyone reasoning about
who closed last.

### 3.2 What the protocol does NOT do

It does not track reference counts, does not know which close is last,
and does not care in which order the two children exit.  The kernel's
`pipe_cpost` tells a closer whether it was last; nobody here reads it.

## 4. The console side: the stage, the round, two writers

### 4.1 cat's output is echo's line, at the stage's cursor

The pipeline stage is the echo stage with `sessp` for `sess`: the same
`turn`/`ps_lb`/`cs_lb`/`inp_lb` ghosts, the same five links, instantiated
through upstream's link RECORD (lane LINK-GEN: `EchoLinks` is a record with
echo's instance definitional; `PipeLinks` is a second instance, as
`FileLinks` is).  The round's block for `PRan` is `L ++ "$ "` — the SAME
bytes as an `LEcho` round's — so cat's byte at cursor `c` must be `L !! c`,
which is (P1) at the dequeued byte (§3, cat's `pipe_rlink` row).  cat's
console payment is `UCatOut`'s shape at the pipe stage: `kcat_round`'s law
funded at cursor `c`, the write's chain at `cch … c` over the bytes the
read delivered, out at `c + count`.  The pinned-offset premise upstream's
cat round takes (`Hpin`, the deed's `off0 := p`) is here the READ POINTER:
cat's cursor is `ps_rp s`, and the read link's dequeue is what advances it
— no offset, no held descriptor, no `OffHeld` anywhere.

### 4.2 The round closes at sh, from the two exit payloads

sh's runcmd child, after `wait(0); wait(0)`, holds: echo's payload
(`mono_list_lb γws L`, or the `PExecL`/`PSilent` marker with `wtok γw`
still in hand, or the taint-free `PExecR` marker) and cat's payload
(`γeof ↦ Some w` with cat's console cursor at `length w`, or its
`PExecR`/`PSilent` marker).  It opens `pipe_inv` ONCE:

- `PRan`: (P1) gives `ps_ws s ⊑ L`; echo's lb gives `L ⊑ ps_ws s`; (P3)
  gives `w = ps_ws s`; so `w = L` and cat's cursor is at `length L` — the
  block is complete, and sh's prompt byte is the next expected byte.
- `PExecL`: sh holds `wtok γw`, (P2) forces `ps_ws s = []`, (P3) gives
  `w = []`: cat printed nothing, and the console holds the left child's
  diagnostic (paid by `UShPanic.ush_execfail_law` at the stage, as in the
  echo application) — the block is complete at the diagnostic.
- `PExecR`: the right child's diagnostic is on the console; the pipe's
  contents are irrelevant (limit 1) and nothing is read.
- `PBoth`: §4.3.
- `PPipe`, `PFork`: no protocol was allocated (or one child never
  existed); the diagnostic is sh's own, through `UkShDiag`'s printer.

The prompt credential the runcmd child hands back through ITS exit (to
the main-loop sh) is the echo application's `Wq I` shape — one round, one
block, the alternative filed at the prompt byte exactly as `EchoOut` files
`cs`.

### 4.3 Two writers on the console: the `PBoth` arm

Both children print `exec %s failed\n` through ulib's `putc`, one byte per
`write(2)`, concurrently.  The wire shows SOME interleaving; the model's
alternative is `PBoth sel`.  This is the one new stage mechanism and it is
the LAST lane (PIPE-2W); everything else lands without it, and until it
lands `app_pipe`'s theorem carries the `PBoth` arm as the one NAMED
premise (`pipe_both_law`, the shape `UFileBootAdequacy.file_prog_law` has:
a hypothesis of the theorem, stated exactly, audited as such).

**The shape (to be designed against `EchoOut.v` when the lane is briefed;
the requirement is fixed here).**  A MERGE LEASE `wr_merge γm d1 d2 c1 c2`:
the round's block owed is `merge ? d1 d2 ++ "$ "` with the interleaving
UNDECIDED; writer `i` holds `wcur γm i ci` (linear, one per child, both
lent by the runcmd child at its two forks) and may append `di !! ci`,
advancing its own cursor; the alternative `cs !!! round` is FILED AT THE
PROMPT (both writers have exited, `sel` is whatever the ledger recorded),
which is where `EchoOut` files an alternative today.  The requirement that
decides the design: does the stage pin `cs !!! i` for the round IN
PROGRESS, or only at the block's end?  If in progress, the merge lease
must carry `sel` as a growing prefix beside the two cursors and the
in-progress reading of `sessp` has to be an existential over the merge's
completion.  Either way the pure side is `merge_prefix`: a prefix of a
merge of `(take c1 d1, take c2 d2)` is a merge of those prefixes.

## 5. Programs

### 5.1 sh: the PIPE arm (lanes SH-PARSE-PIPE, SH-PIPE)

`runcmd`'s PIPE arm (`user/sh.c:101-123`; the walk's jump-table row 3 at
`0x13c`, refuted today from `ush_simple`):

    pipe(p) -- panic("pipe") on -1
    fork1() == 0: close(1); dup(p[1]); close(p[0]); close(p[1]); runcmd(left)   -- echo, fd 1 = write end
    fork1() == 0: close(0); dup(p[0]); close(p[0]); close(p[1]); runcmd(right)  -- cat,  fd 0 = read end
    close(p[0]); close(p[1]); wait(0); wait(0); break -> exit(0)

`UkShRun.ush_simple` admits `UPipe (UExec l) (UExec r)` at the top (as
upstream's SH-REDIR admitted `URedir (UExec _) file 0x601 1`), with the
two subtrees EXEC nodes: the walk's induction hypothesis serves both.  The
arm is stated in a NEW file `UkShPipe.v` with its non-code obligations as
CALL PREMISES, SH-REDIR's `ush_open_call` pattern, so it compiles before
§2/§3 land: the `pipe` call as a premise shaped like `wp_uk_ecall_pipe`'s
conclusion at the ledger `[c; c; c]` (three console rows, `p = {3, 4}`);
the two `fork1`s through `wp_kshr_fork1_any` with the lends §4 names
(`Rc`: the invariant handle, the registry, `wtok` to the left child, the
merge cursor to each; `Q`: the exit payloads of §4.2); the six closes
through `wp_uk_ecall_close_std`/`wp_uk_ecall_close` with the pipe rows'
deposits from the registry; the two `dup`s into slots 1 and 0
(`wp_uk_ecall_dup` at a standard slot); the two `wait(0)`s through
`wp_kshr_wait0`.  The `pipe`-failed tail is `panic`'s entry into
`UkShDiag.ush_diag_leaf` (already walked: "panic (from fork1's -1 arm and
from PIPE's pipe failure)").

The parser: `gettoken` already lexes `|` as a symbol; `parsepipe` is
walked at the `>` shape (`UkShRedirCm.wp_kshp_parsepipe_gt`) and must turn
ONCE for ` | cat`; `pipecmd` into the node catalogue; `nulterminate`'s
PIPE row; the parser theorem at the pipe shape; `ushf_lexable` grows the
shape.  Upstream's SH-PARSE/SH-PARSE-2 are the mould, file for file.

### 5.2 echo at a pipe (lane ECHO-PIPE)

`UEchoPipe.v`, the twin of `UEchoOut` (echo at the console) and upstream's
`UEchoFile` (echo at a file): echo's code walk `UkEcho` is untouched; its
four `kecho_w` obligations are discharged at LEDGER SLOT 1 = a pipe write
end, through `UkWritePipe`'s member at the STANDARD slot (§5.4), with
`pipe_wpay` built from `pipe_inv` (§3's echo rows: the chain's `Q j`
carries the `mono_list_lb` of length `j`, its `Qe` the observation), and
the `Pay` of its `image_entry` = the invariant handle + `wtok γw` + the
fd-1-is-this-pipe row + the exit payload's shape (the lb of `L`).  The
console credential crosses this entry UNCHANGED (echo prints nothing on
the console; `UEchoFile`'s finding, verbatim).

### 5.3 cat at a pipe (lane CAT-PIPE)

`UCatPipe.v`, the twin of upstream's `UCatKernel` (cat's round at the file
claim) with the read at fd 0 = a pipe read end: `UkCatMain`'s `argc <= 1`
arm (`cat(0)`) is landed; `UkCatCat.kcat_round` is funded at the pipe
stage with the read row = `UkReadPipe`'s member at the STANDARD slot
(§5.4) and `pipe_rpay` built from `pipe_inv` (§3's cat rows), the write
row = the console at cursor `c` (§4.1).  Its `image_entry`'s `Pay` = the
invariant handle + the console lease for the round + the fd-0 row, exit
payload = `γeof ↦ Some w` beside the lease at cursor `length w`.  cat's
`cannot open` arm is unreachable (no argument); its `read error`/`write
error` tails are the kill arms (the taint) as in upstream's round.

### 5.4 The pipe leaves at the standard slots (lane PIPE-STD)

`UkReadPipe.wp_uk_ecall_read_pipe` and `UkWritePipe.wp_uk_ecall_write_pipe`
take a `UserFd.ufd` HANDLE (`fd < NOFILE`); echo writes fd 1 and cat reads
fd 0, which are LEDGER slots (`UserFd.ustd`, below `NSTD`).  Upstream hit
the same thing for the file write (`UkWriteFile.wp_uk_ecall_write_std`,
OFF-LINK's L5, "~20 lines beside the handle-fixed leaf"): the twins here
are `wp_uk_ecall_write_pipe_std` and `wp_uk_ecall_read_pipe_std`, at
`ustd l` with `l !! 1 = Some (FdOpen _ true (FdPipe γp))` /
`l !! 0 = Some (FdOpen true _ (FdPipe γp))`, proved through
`UkRunSys.wp_uk_ecall_write_at` / `_read_at` at `K fdv := take NSTD fdv = l`
with `UserFd.ustd_agree`, statements otherwise identical.  Also the `dup`
of a pipe row INTO a standard slot and `close` of a standard slot holding
a pipe (with the registry's deposit) — check `wp_uk_ecall_dup*` /
`wp_uk_ecall_close_std` cover a pipe-typed row; if a leaf pins `fdst_nopipe`
on the installed row, that pin comes off here.

### 5.5 The record and the theorem (lanes PIPE-STAGE, PIPE-ADEQUACY)

`iris/AppPipe.v`: `app_pipe` with `app_pred := AppEcho`'s (the file system
unmodified: `echo_pred`), `app_fixed`/`app_names` echo's, `app_R` the
ledger at `sessp`, `app_ifc` the console interface at the pipe links
record; `Hphi` at `pipe_phi`; the eleven laws re-derived (echo's instances
are the mould; upstream's `AppFileRec`/STAGE lanes show which ones are
definitional and which need the new session).  `pipe_fs_pure av :=
echo_fs_pure av /\ era0_cat_pins av` (both landed; the image has cat at
inum 3 — `FsCatPin`).  `iris/UPipeBootAdequacy.v`:
`App.xv6_app_adequacy` at `app_pipe`, closed at the literal image, with
`PipeAssumptions.v` and `make audit-pipe{,-only}` beside the echo, tree and
file audits (bar: ≤ echo's fourteen, plus `pipe_both_law` until PIPE-2W
lands, reported as such).

## 6. Lanes

Wave 1, independent, in parallel (each in its own clone with its own
remote build tree): **PQ-FLAG** (§3.1, kernel/spec), **PIPE-REG** (§2, U
tier), **PIPE-MODEL** (§1, pure), **SH-PARSE-PIPE** (§5.1 parser),
**SH-PIPE** (§5.1 runcmd arm at call premises), **PIPE-STD** (§5.4).
Wave 2, on the protocol: **PIPE-PROTO** (§3; needs PQ-FLAG + PIPE-REG),
then **ECHO-PIPE** and **CAT-PIPE** in parallel (need PIPE-PROTO +
PIPE-STD), **PIPE-STAGE** (§4.1/§5.5 record; needs PIPE-MODEL).  Wave 3:
**SH-PIPE-ROUND** (§4.2, sh's round at the claim; needs everything above),
**PIPE-ADEQUACY**, then **PIPE-2W** (§4.3).  The worklist has the briefs'
deliverables and bars.

## 7. Rejected on the way

- **The program keeps the fragment** (the pipe-queue design's "where the
  fragment lives is the application's business", read literally): two
  rows on one pipe cannot be paid, a dup/fork copy cannot be paid, and the
  fragment would have to cross `exec` — an exclusive resource in
  `image_entry`'s `Pay`, which the taint arm of the exec channel could not
  refund.  §2's invariant is the reading that pays.
- **A write-end reference ledger in the protocol** ("the last closer
  proves the line is in"): the kernel fires a close link ONLY at the last
  close, so non-last closes cannot decrement a ghost count atomically with
  the kernel's refcount, and a last closer cannot tell a stale count from a
  live one.  Coupling the ghost count to `f->ref` would need links at every
  `filedup`, including `kfork`'s per-descriptor copies — a kernel-wide
  change for a fact §3.1 gets from one premise.
- **Ordering the closes so echo's exit is always last**: not controllable
  from sh's code, and not what the C does.
- **Weakening `PRan` to "a prefix of the line"**: provable without §3.1,
  and not the theorem anyone wants.
- **Extending `EchoDisc`/`EchoOut` in place with the new shape**: the echo
  theorem's statement and audit would move under an active upstream
  campaign that builds its own third shape on the same files; a sibling
  model and record is the established pattern (FILE), and the link record
  makes the instance cheap.
