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
      | PEcho (a : nat)          -- the echo application's four, unchanged (LEcho lines; PEcho 3 -- the MAIN-LOOP fork panic, prologue re-entered -- at LPipe lines too, RULED 2026-09-18 after PIPE-MODEL's finding)
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
  the line is parsed) -- so `palt_ok (LPipe _) (PEcho 3)` HOLDS (the first cut
  of `palt_ok` forgot it; PIPE-MODEL found the theorem would have been FALSE).  `PFork` covers BOTH forks: if the second fails the
  first child is already running echo into a pipe whose read end the
  panicking parent closes on exit; nothing reaches the console.

**The session.**  `EchoDisc.sess` with `alt_blk` reading `pcont` through
the parse: `sessp (ps cs : list nat) (I : list (bv 8))`, where `cs !!! i`
indexes `palt` through an injective `nat` encoding (so the stage's
`cs_auth`/`cs_lb` machinery is reused verbatim, as `FileDisc` did; RULED
2026-09-18: the encoding is POSITIONAL/binary -- `sel` read as a binary
numeral with a leading 1 -- because a unary `encode_nat` made a `PBoth`
code ~4^33 and uncomputable) and
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

**AMENDED (SH-PIPE, 2026-09-18): the registration is HANDED OUT, not
owed.**  The pipe leaf's post carries `pipe_reg γp` (or whatever the
program-facing registration is) as an ANSWER conjunct beside the fragment
and the two handles — the caller's `ush_pipe_call` premise is stated at
that shape, so both today's leaf (at the taint) and PIPE-REG's leaf
instantiate it.  "Owed" would force a registrar over a `γp` the caller
does not know yet.  PIPE-REG's as-landed block says which shape it
built; if the leaf hands out a registration the PROGRAM must still fund
(the fragment goes into an invariant the program allocates), the leaf's
own answer is the fragment + `pipe_reg_of_taint`-free form the program
converts.

**VACUITY CHECK, written first** (durable-notes "Vacuity"): `pipe_reg γp`
must NOT be provable from nothing.  It is not — `pipe_cpay` is `pipe_clink
∨ pipe_taint_cred`, a `pipe_clink` needs a `pipe_qauth` step that only the
fragment's holder can make, and the taint is not held under the
discipline.  State it as `pipe_reg_not_free` in the scratch and keep it as
a comment.

**AS LANDED (lane PIPE-REG, 2026-09-18).**  `PipeReg.pipe_reg γp := □ (∀ w,
pipe_cpay (pn_queue γp) w emp)` and `pipe_row_reg` as designed;
`fileclose_cpays_of_regs` pays kexit's whole `[∗ list]` row from the
registrations (closes `pipe-queue.md`'s second open item).  THREE
CORRECTIONS: (1) **the registry cannot be named in `UkRun.v`** — `pipe_row_reg`
names `pipeG` and `UkRun` binds no ghost bundle by design (a new binder =
a `Context` line in ~70 files; putting `pipeG` on `ufdG` = two instance
paths in ~95 files, which wedges) — so the row enters through **`uexecSG`**,
the U tier's one instance record: three new fields `srow_reg : fdstate ->
iProp`, `srow_reg_persistent`, `srow_reg_nopipe`, answered by `pipe_row_reg`
in `uexecSG_xv6`; `urun_nopipe fdv := ([∗ list] st ∈ fdv, srow_reg st) ∨ □
riscv_kill_cred`.  (2) **The taint arm stays** in the definition (the class
has no `riscvGS` parameter and the generic supply holds the credential with
no pipe names); a registered program never touches it.  (3) **The run
cannot be handed back OWED**: `UkRun.urun_close_upd` takes the rows as an
INPUT and produces the run the continuation receives — a debt paid by that
continuation is circular — and `γp` is bound inside the post's existential.
The FALLBACK landed: at the class-generic leaf (`UkRunSys.wp_uk_ecall_pipe`)
the `□ riscv_kill_cred` premise is simply gone and the registrar takes the
POST; at the instance (`UkReadPipe.wp_uk_pipe_read_end`) the premise is
fragment-shaped, `∀ γp, pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗
Rp γp`, and `Rp γp` replaces the fragment in the post (registering CONSUMES
the fragment: one fragment buys one `□` payment, `pipe_cpay_of_frag`).
`pipe_reg` is NOT timeless (a fupd wand under `□`); nothing strips a `▷`
off `urun_nopipe`.  Vacuity mechanised: `pipe_reg_not_free` refutes a
conjured close link against `pipe_queue_agree`.  Beyond the brief:
`xv6_sbundle_close_of_reg` (CLOSE(21) from the registry, at the point
family's payload `True` only).  PIPE-PROTO's `pipe_proto_alloc` must
therefore produce the registration BESIDE the handle — `pipe_qfrag … pst0
={⊤}=∗ ∃ pn, pipe_inv pn γp L ∗ wtok γw ∗ pipe_reg γp` — which is literally
the registrar premise at `Rp γp := ∃ pn, pipe_inv pn γp L ∗ wtok γw`.

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

**AS LANDED (lane PIPE-PROTO, 2026-09-18; `iris/PipeProto.v`, all seven
headline results Closed under the global context).**  Four corrections
to the table above: (1) **a cursor's exactness is an EXCLUSIVE RESOURCE,
not arithmetic** — a `mono_list` lower bound of length `j` plus (P1) gives
only `take j L ⊑ ws ⊑ L`, not `ws = take j L`; what pins it is that echo is
the ONLY writer, said as a permit: `wcur pn j` / `rcur pn c` are halves of
a `ghost_var nat` whose other half sits in the body at `length (ps_ws s)`
/ `ps_rp s`.  They also make the chains compose across echo's several
`write`s and cat's several reads.  (2) `wtok pn` IS `wcur pn 0`, so (P2)
is one agreement (`pipe_body_P2`) and `wtok_spent` is gone.  (3) (P3)
cannot be a wand (the body must be `Timeless`: every link's fupd runs at
`⊤` with no WP step to strip a later) — it is the one-shot's two owned
arms, `eof_pending ∨ ∃ w, eof_shot w ∗ ⌜w = ps_ws s ∧ ps_wo s = false⌝`.
(4) the reader's EOF observation is ONE node (`pipe_olink` is a `∀ s`):
`pipe_rQe … acc s := pipe_rQ … acc ∗ (⌜pst_eof s⌝ -∗ eof_shot pn (take (c +
length acc) L))`, vacuous off EOF.  ALSO: the reader needs a start permit
too — `pipe_proto_alloc : pipe_qfrag … pst0 ={⊤}=∗ ∃ pn, pipe_inv pn γp L ∗
wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn ∗ pipe_reg γp` (five conjuncts
beside the registration; `Rp γp` of the registrar is that quintuple).
`pipe_wpay_of_inv` takes `wcur pn c`, `pws_lb pn (take c L)` and the
M-premise (`M !! (ua+k) = Some (L !!! (c+k))`) — echo reads its own source
run off the heap the call runs at, one line around
`pipe_wpay_of_inv_fupd` in ECHO-PIPE, deliberately outside `PipeProto`.
`pipe_rpay_of_inv` needs only `rcur pn c`; `pipe_rQ pn L c acc := rcur pn
(c + length acc) ∗ ⌜acc = take (length acc) (drop c L)⌝` is what funds
cat's console write at cursor `c`.  sh's round: `pipe_round_reading`, the
symmetric payload `pipe_Qc` with `pipe_Qc_two`.  §3.1's "(P3) does not
need a `ps_ro` premise" is CONFIRMED.  `L` has no landed name (`PipeDisc`
spells it inline as `wl_line (drop 1 (pline_ws l))`).

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

**AS LANDED (lane PQ-FLAG, 2026-09-18).**  The WRITE premise landed as
designed: `SpecPipewrite` gained `w = true` (filewrite's own `f->writable`
test is that boolean, `fw_wbool_of_fall`), and `ProofPipewrite` derives
`ps_wo s = true` at the store from the caller's `pipe_ref` through
`pipe_endstate_holder` and the coupled arm.  `pipe_wlink_of_uncond` is the
sanity lemma (the old unconditional stepper is still a link).  The READ
premise `⌜ps_ro s = true⌝` was REFUTED as "free": `piperead` never loads
`readopen`, so the only route is `w = false` on `SpecPiperead`, and the
file layer cannot supply it — `fileread` learns nothing about `wb` at a
pipe row, because nobody publishes "a pipe file's two ends are
complementary" (true of `pipealloc`, dropped at the store; expressible in
`fdstate_ok`/`file_core_noff`'s pipe arm, no publisher).  Not landed, not
needed: (P3) freezes `ps_ws`, which only a write moves.  A future
reader-side protocol wanting "the read end is open" buys that fact first.

Without 3.1 the protocol has no way to freeze the contents at EOF: the
generic close link (§2) fires at the LAST write-end close, which may be
sh's or the cat child's rather than echo's, and none of them can prove
"the line is in" at that instant.  The snapshot-plus-freeze shape is what
lets sh combine echo's "the line is in" with cat's "I printed exactly the
frozen contents" AFTER the fact (§4.2), without anyone reasoning about
who closed last.

### 3.1b RULED (2026-09-18, after ECHO-PIPE's wall): the write link also fires only with the READ end open

ECHO-PIPE found that echo's four writes do not compose past a SHORT write:
a write's post leaves `∃ k ≤ n, wcur pn (c+k)`, and the next write's chain
builder needs its bytes to be `L`'s at the cursor `c+k+j` while echo's
next buffer holds `L`'s at `c+n+j` — so with `k < n` no chain can be
stated, and `pipe_wpay = chain ∨ app_taint` leaves echo (untainted) with
nothing to pay.  The two reachable causes of `k < n`: the kill shot (the
taint, already paired with `kill_shot` by the trap tail — route (c)), and
the reader gone (`readopen == 0`, the `PExecR` world).  RULED, route (d),
which needs nothing lent: **`pipe_wlink` gains `⌜ps_ro s = true⌝`** beside
PQ-FLAG's `⌜ps_wo s = true⌝` — `pipewrite` tests `pi->readopen == 0` under
the SAME lock hold immediately before each byte's store (`kernel/pipe.c`:
the test, the full-ring sleep that loops back to the test, or the store),
so the fire site has the fact for free from the coupled arm (`ps_ro =
pflag_bool ro`), exactly as the write-open premise.  (PQ-FLAG refuted a
`ps_ro` premise on the READ link — piperead never loads `readopen`; this
is the WRITE link, whose code does.)  With it the protocol gains (P4): a
persistent one-shot `ro_shot` ("the read end was seen shut") that the
writer's OBSERVATION node sets when it fires at `ps_ro s = false`, and the
body's law `ro_shot -∗ ⌜ps_ro s = false⌝` (`ps_ro` is monotone: only
`pst_close false` moves it, one way).  A write link fired AFTER the shot
has `⌜ps_ro s = true⌝` against (P4)'s `false` — vacuous — so a chain
builder past a short write is buildable from `ro_shot` alone: echo's
"derail" is `ro_shot ∨ app_taint`, both of which echo can hold (the shot
from its own short write's observation; the taint from the kill).  Nothing
crosses `fork`/`exec` for it; `ep_derail` is deleted from echo's `Pay`.
Lanes: PQ-FLAG-2 (kernel: the premise, the `_of_frag`/chain lemmas ignore
it), PIPE-PROTO-2 ((P4), `ro_shot`, the observation setting it, the
builder past a short write, `pipe_payL`'s mid-line arm = the shot), then
ECHO-PIPE-2 (drop `ep_derail`).  Also from ECHO-PIPE: the chain builder
used is the non-fupd `pipe_wpay_of_inv` (the ledger-slot deposit takes a
plain wand); echo's `Pay` carries the console credential `Wq` (the only
door) beside `side_L`; `pipe_wpost`'s taint arm can swallow a caller's
exclusive payment (a disjunction) — PipeQueue's header overstates.

**AS LANDED (PIPE-PROTO-2, 2026-09-18).**  (P4) is an owned two-arm
one-shot (`ro_pending ∨ (ro_shot ∗ ⌜ps_ro s = false⌝)`, camera
`csumR (exclR unitO) (agreeR unitO)`), the law `pipe_body_P4` against the
authority; the writer's `pipe_wQe` shoots inside the invariant when the
observation fires at `ps_ro s = false`.  The derailed builder is at ONE
resource: `pipe_wpay_of_inv_after_short : pipe_inv -∗ ro_shot -∗ R -∗
pipe_wpay … (fun _ => R) (fun _ _ => R) n` — a node is additive (`Q j ∧
olink ∧ wlinks`), so its value and observation still have to be paid,
and one `R` serves all; no cursor (carrying `wcur` would make it
UNPROVABLE, not unsound — the derailed writer has lost that knowledge), no
M-premise, no bound.  `pipe_payL`'s third arm `∃ c, wcur pn c ∗ ro_shot`;
`pipe_round_reading` answers `w = L` / `w = []` / `w = take c L` (the
contents from the CURSOR; the shot only separates `PExecR` from `PExecL`).
`pipe_rpost_line` = CAT-PIPE's reader post, general.  STILL OWED (both
sides, one ruling): the KILL cause — the write post's kill arm carries
only `kill_shot`, the read's `-1`-by-kill has no row at a pipe; lane
KILL-TAINT makes both carry `app_taint` beside the shot.

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

**AMENDED (SH-PIPE's finding R-2, 2026-09-18): `wait(0)` cannot tell the
two children apart** — `wp_kshr_fork1` requires the payload to be the same
at every return value, and `uwait_ans`'s reaping arm binds its generation
only up to `γ' ∈ cs ∨ pidv = 1`; the pid-refuting form needs
`UserChildren.upid`, which the fork leaf hands out and `wp_kshr_fork1`
drops.  So the two children's exit payloads are ONE symmetric `Qc`, and
the two sides are told apart by EXCLUSIVE SIDE TOKENS: the runcmd child
mints `side_L` and `side_R` (two `Excl ()` ghosts, or one `ghost_map`
with two keys) after `pipe(2)`, lends `side_L` to the left child and
`side_R` to the right through `RcL`/`RcR`, and `Qc _ := (side_L ∗ left
payload) ∨ (side_R ∗ right payload)` where the left payload is echo's
(`mono_list_lb γws L`, or `wtok γw` back at `PExecL`/`PSilent`, or the
`PExecR` marker) and the right payload is cat's (`γeof ↦ Some w` with the
console cursor at `length w`, or its diagnostic's marker).  Two answers
both taking the left arm would put `side_L` twice in sh's hands — refuted
by exclusivity — so sh holds exactly one of each and §4.2's reading goes
through unchanged.  (If a lane wants the pid route instead, `wp_kshr_fork1`
must be re-cut to keep `upid`; not taken.)

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

**AS LANDED (lanes SH-PIPE and SH-PARSE-PIPE part 1, 2026-09-18).**
`ush_simple` is NOT widened (a structural `Fixpoint`; "at the top" is not
expressible and widening silently strengthens `wp_kshr_runcmd`) — the
scope is the layered `UkShPipe.ush_ptop` (one PIPE level over
`ush_simple`), exactly as SH-REDIR did for `URedir`.  The arm
`UkShPipe.wp_kshr_pipe_arm` walks 0x13c–0x1c2 plus the `panic("pipe")`
tail in THREE processes at these premises: `ush_pipe_call` (the `pipe`
stub's answer `ush_pipe_ans`: the two handles at ABSTRACT slots `a ≠ b`,
`NSTD ≤ a, b < NOFILE` — `p = {3,4}` is NOT derivable, the row scans the
whole table and a ledger pins only the low `NSTD`; the eight bytes; the
ledger unmoved; and the REGISTRATION HANDED OUT as an answer conjunct
`R γp` — not owed: owed would force a registrar over a `γp` not yet known;
`pipe_qfrag` itself cannot be named in a `Uk*` file, it lives in
`spost_at`'s row, so it goes inside `R γp`), the two `fork1`s through
`wp_kshr_fork1` (NOT `_any`, which fixes `Rc := emp`) at lends `RcL RcR`
and ONE payload `Qc` for both children (see §4.2 as amended), the six
closes with the two pipe rows' deposits riding the answer as two
persistent `ush_cldep st := □ ∀ N m pc, udepw_cl N m pc st` (the registry
read literally; the children close at records fork chooses, so per-close
parameters were the wrong shape), pipe-row closes through the generic
`wp_uk_ecall_close` (PIPE-STD: the `wp_ksh_close*` wrappers spend a
load-bearing nopipe premise), sh's `dup` stub (`wp_kshpi_dup`, never
walked before; `ukn_held N = ∅` a premise), the two `wait(0)`s through
`wp_kshpi_wait0` at a NAMED children set relaying `uwait_ans`.  `int p[2]`
costs no stack (`wp_kshr_entry` already hands out `sp0-40`).  Consumer
test `wp_kshr_runcmd_pipe` closes the arm at today's kernel modulo ONE
premise: **the kernel's pipe row does not pin a failing `pipe(2)` to −1**
(`UsysMemOk`'s row says `uint r ≠ 0`; sh's next instruction is `bltz a0`,
so the not-taken-and-nonzero path runs the pipeline on two garbage
descriptors) — `ush_pipe_call_weak_of_leaf` proves the gap is exactly that
conjunct; lane **PIPE-NEG1** adds `r = -1` to the row and its
`ProofSysPipe` discharge (`open`/`dup` rows already say it).  The parser
(SH-PARSE-PIPE part 1): the pipe line LEXES (`ush_line_toks_holds_pipe`,
closed), gettoken's `|` arm, nulterminate's PIPE row, the node
`UkShPipeSeam.ush_cmd_of_ushp_pipe` = `ush_cmd γd p (UPipe (UExec (ush_args
s0 g toksl)) (UExec (ush_args s0 g toksr)))`, the argument loop's exit at
`|`; part 2 owes `parseexec` at the pipe line's two sides (re-statements),
`pipecmd`'s catalog row (`make gen-ucode`) and `parsepipe`'s 13-instruction
turn.  The pipe line makes THREE allocations (two `execcmd`, one
`pipecmd`), within the landed malloc chain.  `ushf_lexable` no longer
exists (deleted upstream, SH-LINE 2b); the line predicate is a third
theorem beside the echo and redirect ones, and the line disjunct in
`UkSh.ush_rest_line` needs a FOURTH arm (SH-PIPE-ROUND).

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

**AS LANDED (lane CAT-PIPE, 2026-09-18) and one RULING.**  `UCatPipe.v`:
cat's round `pcat_round_at` (`kcat_round` funded at fd 0 = the pipe:
the READ POINTER IS THE CONSOLE CURSOR, one permit `rcur`; no offset, no
`Hpin`), the entry `pcat_image_entry` at argv `["cat"]` — CHEAPER than
the file's (no name, no path implication, no cwd; the `cannot open` arm
REFUTED by the node's word count), exit row from the registry, audits
unmoved.  The pipe stage's write link takes cat's byte at cursor `c` from
`⌜acc = take d (drop c L)⌝` alone (no `cs`/`I` lend — STOP 2 did not fire).
Two PipeProto/UkReadPipe shapes were too lossy for a WALK and were
re-proved locally (a reader needs `length acc = d` and the post's image
row; `wp_uk_ecall_read_pipe_std`'s count premise is the whole word where
`kcat_r` pins the low 32 bits — one-line relays owed at the leaf).  **THE
WALL, RULED:** a pipe read's `-1` has three arms; two are refuted (copy-out
fault at the first byte; the sign guard at `cap = 512`); the third, THE
READER'S OWN KILL SHOT, is not — the only row killing a read's `-1`
(`UexecRet.uexec_live_ok`) is stated for `FdDevice 1` alone — and cat
branches on it (`cat: read error`, not in the model).  RULED: it closes
by the NAMED PREMISE `Hktaint : □ (∀ gn, ChildTok.kill_shot gn -∗
app_taint)` ("a kill taints the application", what `applications.md`
already says the kill credential is), stated inside `Hprog` beside
`pipe_both_law`, audited as such; the honest discharge is a kernel lane
**READ-KILL-TAINT** (the pipe twin of `uexec_live_ok`'s read clause =
usertrap's second `killed()` check handing the credential out), queued
after PIPE-2W.  Also: a standalone `ctokG` section variable makes
`ChildTok.kill_shot` a different term from the one the post carries
(resolve through `xv6G`) — durable-notes' two-instance wedge again.

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

### 5.6 RULED (2026-09-18, after PIPE-STAGE's finding): the claim pins /cat

`AppEcho.echo_pred γ r av := echo_taint γ ∨ (⌜echo_fs_pure av⌝ ∗ cons_state
r av)` and `echo_fs_pure` pins /init, /sh and /echo only — so a record at
`app_pred := echo_pred` typechecks but cannot resolve `/cat` from the
claim, and SH-PIPE-ROUND's exec of cat would have nothing to stand on.
RULED, route (a): the pipe claim is echo's SHAPE with the stronger pure
conjunct,

    pipe_pred γ r av := echo_taint γ ∨ (⌜file_fs_pure av⌝ ∗ cons_state r av)
    -- FileFsPure.file_fs_pure av = echo_fs_pure av /\ era0_cat_pins av, upstream's landed predicate, imported

`app_fixed`/`app_names`/`app_boot`/`cons_state` stay echo's.  What it
costs (lane PIPE-CLAIM = PIPE-STAGE part 2): the record's laws re-derived
at `pipe_pred` (mould: `AppEcho`'s proofs; the pure conjunct crosses the
transport as a Prop, `Happ_init` computes `era0_cat_pins` off the image
through `FsCatPin.era0_boot_cat_pins` exactly as `AppFileRec` does), and
the PROGRAM-TIER LAWS at `pipe_pred` — /init's console dance
(`init_cons_laws_at` at a non-echo claim: upstream's INIT-FILE rounds are
the mould, minus the f-state; the one real move, the console `mknod`,
must preserve `era0_cat_pins` — `FileDeltas`' pin-preservation lemmas
cover the legs) and whatever sh's round reads of the claim.  Route (b),
confining the pipeline round to era 0 where `era0_boot_cat_pins` is
free, is rejected: the theorem is about every era.  The design's §0
sentence "the file system unmodified, echo's invariant verbatim" is
corrected to "echo's invariant plus /cat's pin, same shape".

### 5.7 AS LANDED (lanes PIPE-STAGE and PIPE-CLAIM, 2026-09-18)

The stage is `FileOut`'s twin with nothing threaded: `PipeOutPure.v`,
`PipeOut.v`, `PipeLinks.v` compiled UNCHANGED across upstream's 190-commit
merge (one new interface field, `ai_lic` → `pipe_cons_lic`).
`postage = EchoOut.ostage` verbatim, `pturn = eturn` verbatim, the fixed
part is echo's; `sessp_prefix_det2` is `sessp_prefix_det` by `exact` (no
state to disagree about); `rd_stage_le` has no twin — the read exports
the choice list truncated to the window's line count, FileOut's route.
The tag is STAGE's corrected shape (`disc_p` does not imply `disc`).
`pipe_link_inst : LinkRec` is NOT landed — it is a ~2,800-line port
(upstream's `FileLinksLine`/`FileLinkInst` now exist as the mould) and is
SH-PIPE-ROUND's if the round needs the record rather than `pipe_links`.
THE CLAIM (§5.6): `pipe_pred γ r av := echo_taint γ ∨ (⌜file_fs_pure av⌝ ∗
cons_state r av)`, and the whole point of §5.6's costing was wrong in the
cheap direction — `pipe_pred γ r av ⊣⊢ echo_pred γ r av ∗ (echo_taint γ ∨
⌜era0_cat_pins av⌝)`, a persistent instance-free factor that crosses the
transport at the same view for free, so the record's laws are ECHO'S
APPLIED (`AppPipeClaim.pipe_pred_split`), zero new assumptions; the
moving-view legs are one lemma (`pipe_step_of_echo`); /init's whole
console dance holds at `pipe_pred` (`AppPipeCons`: the nine
`init_cons_laws_at` conjuncts incl. `pipe_cat_pins_acc`, the /cat reading;
`UInitConsPipe`: four bundles, the seal, both leaf pairs, sh's two console
arms).  `Hprog = al_programs` at `app_pipe` is the only `Context`
hypothesis left — SH-PIPE-ROUND's.  Lesson: a claim that adds a
persistent instance-free conjunct to another application's costs the split
lemma and nothing else.

### 5.8 RULED (2026-09-18, after SH-PIPE-ROUND's two STOPs): the line type, and the link record

SH-PIPE-ROUND landed the child walk at the pipe shape
(`UkShPipeRound.wp_kshm_child_pipe_line`, three platform assumptions) and
the whole-system theorem `UPipeBootAdequacy.pipe_adequacy_pipeΣ` at the
literal image — CLOSED MODULO ONE PREMISE, `pipe_prog_law` (= `al_programs`
at `app_pipe`, the record's only open field), audit `make audit-pipe-only`
= FOURTEEN, echo's list exactly; `pipeΣ` = echo's functor list.  Two STOPs:

**STOP A — there is no "fourth arm"; there is a missing CONSTRUCTOR.**
Upstream generalised sh's line disjunct over THEIR line type:
`UkSh.ush_rest_line_at (D : FileDisc.uline -> Prop)`, `Hdsc_line : uline_ws
lu = wl_words (rest_of I)`.  `FileDisc.uline = LEcho | LEchoF | LCat` and
`FileDisc.v` is a model file (`parse_line`, `lines_of`, `ralt_ok`, `fsm`,
`cont`), read by `FileOutPure` 25 times.  RULED: **add the constructor
`LPipe (ws)` to `FileDisc.uline`, ADDITIVELY** — `parse_line` UNTOUCHED (so
`lines_of`'s range, `alts_ok`, determinacy and `AppFile`'s conclusion keep
their meaning at every input the FILE theorem quantifies over), `uline_ws
(LPipe ws) := ws ++ [bar; cat]` (the WHOLE body's words, which is what
`Hdsc_line` demands — `PipeDisc.pline_ws` gives the echo words alone and
cannot be reused), every `match`/`destruct` on `uline` in the four landed
FILE files (`FileDisc` 6, `FileDiscDec` 3, `FileOutPure` 4, `FileLinksLine`
13; 5 definitions + 26 proof sites) gains the arm that the FILE model
never reaches (its `parse_line` never produces it: the arms are
`ralt_ok := False`-style dead arms or the obvious constant).  This is the
one place the campaign edits upstream's files; it is purely additive and
the owner is told.  The alternative — generalising `UkSh.ush_line_at` to
its three projections — moves every landed statement naming it.  Then the
pipe line's `D` is `PipeDisc`'s reading of `LPipe` and `ush_rest_line`'s
instance at it is SH-PIPE-ROUND-2's.

**STOP B — the round is stated at the LinkRec INSTANCE.**  `UShRound.v` is
end to end at `FI := FileLinkInst.file_link_inst_at g s0` (`Wcl`/`Wbl`,
the five credential conversions, `lk_exfb`, `lk_rres`, the stage record);
`PipeLinks.v` is the BUNDLE, not the record.  Lane **PIPE-LINK-INST**: the
port of `FileLinksLine.v` (2,081) + `FileLinkInst.v` (760) to the pipe
stage — `pipe_link_inst_at`, with `lk_ab I a := PipeDisc.pcont (the line's
parse) (palt_of a)` needing NO guard (pcont reads no state), `lk_apr` =
`pcont_shape`, the three named alternatives literally `3`/`1`/`2` (echo's,
`reflexivity`), `lk_exfb`/`lk_lcred` at the merged diagnostic.
`pipe_both_law` is NOT a premise of the theorem (it lives inside `Hprog`)
and is stated at the record, so it waits for this lane too.  `al_programs`
at `app_pipe` itself needs no record (STOP C did not fire).

Also from the lane: `wp_kshr_pipe_arm` takes the exit payload FREE
(`⊢ ukn_pay N (-1)`) where the redirect arm takes `□ (Cr -∗ …) ∗ Cr`; the
round runs at the lent credential, so SH-PIPE-ROUND-2 re-cuts the arm at
the pair (a caller-brought linear resource travels through the spatial
split premise already).  `wp_kshp_parsecmd_bar`, not `wp_kshp_parser_pipe`,
is the walk's parser (the seam wants the nodes unclosed).  `S (S gp)` and
`gp + 3` are not convertible — replace at the whole index.

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
