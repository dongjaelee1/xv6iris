# Project: the PIPELINE application — `echo … | cat` prints the line

**STATUS: OPEN (started 2026-09-17, owner: "go for the pipeline
application").**  Design of record: [`../design/app-pipe.md`](../design/app-pipe.md).
Read that first; this file is only what is LEFT, lane by lane, and what
each lane found.

The target: `App.xv6_app_adequacy` at `AppPipe.app_pipe`, closed at the
literal image (`UPipeBootAdequacy.pipe_adequacy_pipeΣ`), with
`make audit-pipe-only` beside the echo, tree and file audits, and the
conclusion `PipeDisc.pipe_phi`.  Until lane PIPE-2W lands, the `PBoth`
arm is the theorem's one named premise (`pipe_both_law`).

## Rules for every lane

- Each lane works in ITS OWN worktree of this tree (`/shared/xv6iris-pipe-<lane>`,
  branch `app-pipe/<lane>` off the SHA the brief names) and builds ONLY
  on the EC2 mirror, in a fully built clone of the same name there,
  through `claude-notes/projects/app-pipe-briefs/ec2-lane.sh <lane>
  check|build|run` (which syncs first).  Never a local `rocq`/`coqc`/
  `make` (the standing order; this machine is the owner's, 8 cores/15 GB).
  Lanes do not share a remote clone, so they do not race each other.
- No landed statement moves unless the lane's brief says so.  `AppEcho.v`,
  `EchoOut.v`, `EchoDisc.v`, `AppInv.v`, `App.v` and every `AppFile*`/
  `UEchoFile`/`UCat*`/`UShCat`/`UShRedir*` file of upstream's FILE campaign
  are READ, not edited.
- Every new result carries `Proof using`; the echo audit stays at 14, the
  tree audit at 13 (the at-boot theorem; "10" was the era-0 obligation alone), the system audit at 13.
- Report back: what landed (file, lemma), what was refuted and why (at
  the STATEMENT: mask, persistence, home across `fork`/`exec`), and the
  one thing the next lane needs first.  A refuted ruling is reported, not
  routed around.
- The coordinator merges to `main` from `main` (`git checkout main` first;
  print `git branch --show-current`), gates on a green `--proofs` of the
  merged tree, and pushes only on the owner's signal.

## Wave 1 — independent of the protocol (run in parallel)

- [ ] **PQ-FLAG** (kernel/spec, design §3.1).  `PipeQueue.pipe_wlink` gains
  the premise `⌜ps_wo s = true⌝`, `pipe_rlink` gains `⌜ps_ro s = true⌝`;
  every `_of_frag` constructor and chain lemma (`pipe_wchain`/`pipe_rchain`
  and their `_cursor`/`_neg`/post lemmas) re-proved by ignoring the
  premise; the two fire sites (`ProofPipewrite` at the `sw` of `nwrite++`,
  `ProofPiperead` at `nread++`) supply it from the caller's `pipe_ref`
  through `PipeInvDefs.pipe_endstate` (`:589`) and the coupled arm's
  `pflag_bool`.  If the ref is not in hand at the store, thread the pure
  fact from `SpecFilewrite`'s `f->writable` arm and report.  Bar: whole
  tree green, no statement outside `PipeQueue`/`Spec*Pipe*`/`Proof*Pipe*`
  moves, audits unmoved.
- [ ] **PIPE-REG** (U tier, design §2).  New `iris/PipeReg.v`: `pipe_reg γp
  := □ (∀ w, pipe_cpay (pn_queue γp) w emp)`, `pipe_row_reg`,
  `pipe_reg_of_taint`, persistence/timelessness; the VACUITY scratch
  `pipe_reg_not_free` first.  `UkRun.urun_nopipe` REDEFINED as `[∗ list] st
  ∈ fdv, pipe_row_reg st` (name kept; `urun_nopipe_intro` from
  `fdv_nopipe`, NEW `urun_nopipe_taint`); `urun_nopipe_step` off
  `usys_fd_ok` at `n <> USYS_pipe`; `urun_rows_insert`/`urun_rows_nopipe`
  restated at the resource.  `UexecExecInst.xv6_sbundle_exit_regs` (the
  exit row from the registry; `_nopipe` kept as a corollary) and its one
  consumer `UexecExecMint:151`.  `UkRunSys.wp_uk_ecall_pipe` drops the
  `□ riscv_kill_cred` premise and hands the run back OWED THE REGISTRATION
  (`pipe_reg γp -∗ urun …` in the post) — STOP RULE in design §2 if the
  run cannot be split; the fallback is a registrar premise.  Bar: every
  `iAssert (UkRun.urun_nopipe …)` site in the tree compiles unchanged (the
  list: UkFork:951, UInitSh:1055/1319, UShEchoPay:149/173/268,
  UexecCond:282/313/365, UShEcho:1347/1361/1437, UShKernel:560/801,
  UEchoKernel:457, UCatKernel:1111/1175, UShCat:869/976/1032/1048,
  UEchoFile:459/502, UInitBoot:1020, UInitTreeExec:373, UEchoOut:855,
  USyncKernel:186, UInitKernel:285/405); whole tree green; audits
  unmoved.
- [x] **PIPE-MODEL** (pure, design §1).  `iris/PipeDisc.v` at §1's
  definitions VERBATIM (a lane that finds a definition wrong REPORTS it,
  it does not fix it): `pline`, `line_bytes`, `pline_ok`, `parse_pline`
  and its inverse laws, `disc_input_p` (prefix-closed, decidable, the snoc
  laws `EchoDisc` has), `palt` with its `nat` encoding (injective; `PBoth
  sel` encoded with `sel`), `palt_ok`, `pcont`, `merge`/`merge_prefix`,
  `sessp`, `good_out_p`, `pipe_phi`; the determinacy `sessp_prefix_det`
  (the twin of `EchoOutPure.sess_prefix_det`, on `pcont_shape`: every
  non-panic continuation is `$`-free then the prompt); the `vm_compute`
  demos §1 lists including the NEGATIVE one.  Bar: `Closed under the
  global context`.
- [ ] **SH-PARSE-PIPE** (U tier, sh's parser, design §5.1).  Mould:
  upstream's SH-PARSE / SH-PARSE-2 findings in `projects/app-file.md`.
  `parsepipe` turns ONCE for ` | cat` (today `wp_kshp_parsepipe_gt` is the
  `>`-shape walk); `pipecmd` into the node catalogue (`ush_cmd` at `UPipe
  (UExec l) (UExec r)`); `nulterminate`'s PIPE row; `parseline`/`parsecmd`
  at the pipe shape; the parser theorem at the pipe shape;
  `UkShFork.ushf_lexable` grows the shape.  NEW files where possible
  (`UkShPipeLex.v`, `UkShPipeParse.v`); the existing simple-line and
  redirect-line theorems unchanged.  Bar: whole tree green.
- [ ] **SH-PIPE** (U tier, sh's `runcmd`, design §5.1).  NEW `iris/UkShPipe.v`:
  `UkShRun.ush_simple` admits `UPipe (UExec l) (UExec r)` at the top; the
  PIPE arm walked with its non-code obligations as CALL PREMISES
  (SH-REDIR's `ush_open_call` pattern): `ush_pipe_call` shaped like
  `wp_uk_ecall_pipe`'s conclusion at the ledger `[c; c; c]` (p = {3, 4}),
  the two `fork1`s through `wp_kshr_fork1_any` with ABSTRACT lends `Rc`
  and payloads `Q` (parameters of the arm's lemma), the six closes
  (`wp_uk_ecall_close_std` at slots 0/1, `wp_uk_ecall_close` at 3/4 with
  the pipe rows' deposits as parameters), the two `dup`s into slots 1
  and 0, the two `wait(0)`s through `wp_kshr_wait0`, the `pipe`-failed
  tail into `UkShDiag.ush_diag_leaf`'s panic entry.  If a dup/close leaf
  pins `fdst_nopipe` on the installed row, REPORT (lane PIPE-STD takes
  it).  Bar: the existing `wp_kshr_runcmd` theorems unchanged; the new
  arm compiles at the abstract premises before PIPE-REG lands.
- [x] **PIPE-STD** (U tier, design §5.4).  `UkReadPipe.wp_uk_ecall_read_pipe_std`
  and `UkWritePipe.wp_uk_ecall_write_pipe_std` at `UserFd.ustd` (slot 0 /
  slot 1), through `UkRunSys.wp_uk_ecall_read_at`/`_write_at` at `K fdv :=
  take NSTD fdv = l` with `UserFd.ustd_agree` (mould: `UkWriteFile.
  wp_uk_ecall_write_std` + `udepwf_std_write_file`, OFF-LINK's L5 block);
  the deposit twins; `dup` of a pipe row INTO a standard slot and `close`
  of a standard slot holding a pipe checked and, if a leaf pins
  `fdst_nopipe`, the pin taken off with its reason.  Bar: statements
  otherwise identical to the handle-fixed leaves; whole tree green.

## Wave 2 — on the protocol

- [ ] **PIPE-PROTO** (design §3; after PQ-FLAG + PIPE-REG).  `iris/PipeProto.v`:
  `pipeProtoG`, `pnames`, `pipe_body`/`pipe_inv` at (P1)–(P3),
  `pipe_reg_of_inv`, the writer's chain builder (`pipe_wpay` from the
  invariant at cursor `j` with `Q j` = the length-`j` lower bound, the
  last node's `mono_list_lb γws L`), the reader's chain builder
  (`pipe_rpay` from the invariant at cursor `c`, the EOF observation
  setting `γeof`), the allocation right after `pipe(2)` (`pipe_proto_alloc :
  pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ ∃ pn, pipe_inv pn γp L ∗ wtok γw`),
  and sh's end-of-round reading (§4.2's four cases as lemmas).  Consumer
  test: a straight-line `pipe → fork → (child writes L) / (child reads to
  EOF) → waits → the reading says the reader saw L`, at the leaves.
- [ ] **ECHO-PIPE** (design §5.2; after PIPE-PROTO + PIPE-STD).
  `iris/UEchoPipe.v`: echo's `image_entry` at fd 1 = a pipe write end.
- [ ] **CAT-PIPE** (design §5.3; after PIPE-PROTO + PIPE-STD).
  `iris/UCatPipe.v`: cat's round and `image_entry` at fd 0 = a pipe read
  end, at the pipe stage's cursor.
- [ ] **PIPE-STAGE** (design §4.1/§5.5; after PIPE-MODEL).  `iris/AppPipe.v`
  and the links record instance `PipeLinks`; `Hphi` at `pipe_phi`; the
  record's laws; `pipe_fs_pure`.  Mould: upstream's STAGE / STAGE-2 /
  FILE-DEC findings and `AppFileRec.v`.

## Wave 3 — the round and the theorem

- [ ] **SH-PIPE-ROUND** (design §4.2): sh's round at the claim — the
  main loop's dispatch on the line's shape (LEcho → the echo round
  unchanged; LPipe → `UkShPipe`'s arm instantiated at PIPE-PROTO's lends
  and payloads, ECHO-PIPE's and CAT-PIPE's entries as the two exec
  supplies), the end-of-round reading, the prompt.
- [ ] **PIPE-ADEQUACY**: `iris/UPipeBootAdequacy.v`, `iris/PipeAssumptions.v`,
  `make audit-pipe{,-only}`; the design page's §0 rewritten as landed;
  `pipe_both_law` reported as the one premise.
- [ ] **PIPE-2W** (design §4.3): the merge lease; `pipe_both_law` discharged;
  the premise removed.

## Findings (append as lanes report)

### PIPE-STD (2026-09-17)

**Verdict in one line: the whole lane landed with no statement outside the
two pipe files moved, and the ONE design fact it found is that no leaf that
moves a descriptor pins a pipe row -- so the pipe-typed dup/close twins
SS5.4 provisioned for do not exist and lane SH-PIPE takes the generic leaves
as they stand.**  Whole `iris` tree green on the lane's remote clone
(`ec2-lane.sh std build`, RC=0, plus a confirming re-run with nothing left
to compile); `make audit-echo-only` UNMOVED at FOURTEEN (the same
`PrimInt63`/`PrimString`/`resv_*`/`functional_extensionality_dep` set);
`Proof using` everywhere; no `Admitted`; commits `53b170ec6`, `e074e4691`.
The audits could not have moved anyway: NOTHING in the tree `Require`s
`UkReadPipe.v`, `UkWritePipe.v` or the new `UkPipeMoves.v` (every other
mention of the two is in a comment), so no audit cone reaches this lane, and
the only edit to pre-existing content was two comment lines.

**WHAT LANDED**

- `iris/UkWritePipe.v` section 4 -- `udepwf_std_write_pipe` (the deposit at
  `UkRun.udepwf_std`, the arm computed from the caller's ledger through
  `UkReadRows.std_fd_st_of_key`) and **`wp_uk_ecall_write_pipe_std`**:
  `usysno m = 16`, `bv_signed (trunc32 (m !!! a0)) = Z.of_nat fd`,
  `(fd < NSTD)%nat`, `l !! fd = Some (FdOpen rb true (FdPipe γp))`,
  `sys_rw_count (m !!! a2) = Z.of_nat nb`, the pc+4 alignment; in:
  `uinstr_is`, `urun`, `UserFd.ustd (ukn_fd N) l`, `ubytesq … nb f` and the
  SAME `pipe_wpay (pn_queue γp) M (m !!! a1) Q Qe nb` wand-over-the-heap;
  out: the same source-image row, the same
  `pipe_wpost Pt (pn_queue γp) Mv (m !!! a1) Q Qe Rk nb r`, the ledger
  unmoved, `ubytesq`, `urun` at `<[a0 := r]> m`.
- `iris/UkReadPipe.v` section 6 -- `udepwf_std_read_pipe` and
  **`wp_uk_ecall_read_pipe_std`**: the same shape at
  `l !! fd = Some (FdOpen true wb (FdPipe γp))`, `(fd < NSTD)%nat`, with
  `pipe_rpay (pn_queue γp) Rp Rpe cap` in and the five pure rows +
  `pipe_rpost_img` + `uread_pipe_ans` out, verbatim the handle leaf's.
  Both proved through `UkRunSys.wp_uk_ecall_write_at` / `_read_at` at
  `K fdv := take NSTD fdv = l` with `UserFd.ustd_agree`, as SS5.4 said; the
  walks' `K` expressed the ledger with nothing to report.
- NEW `iris/UkPipeMoves.v` -- the descriptor moves, with the consumer test
  `wp_uk_close1_dup_pipe_std` (ledger `[c; c; c]` + a handle on a pipe write
  end above the standard streams; `close(1)` then `dup`; ledger `[c; W; c]`,
  handle home, answer 1 -- dup's failure arm refuted by computation), plus
  `ufd_of_own_hi` (out of `UserFd.ufd_own` above `NSTD`) and the two
  ledger-arithmetic facts.  The reload of a0 between the two ecalls is a
  CALL PREMISE: it is sh's own instructions (SH-PIPE), and the test is about
  the moves.
- Prose only (item 4): `UkReadPipe.wp_uk_pipe_read_end`'s taint comment and
  `UkWritePipe.v`'s header now point at design SS2 and say what moves when
  PIPE-REG lands (nothing in either file: the pipe payments and the exit row
  are different rows).

**WHAT WAS REFUTED / WHAT THE DESIGN GOT WRONG** (four, every one read at
the STATEMENT; none of them fatal, and none needed a design ruling)

1. **There is no offset mode to leave free.**  The brief asked for the
   deposit twin "with the offset mode free where the file leaf had it".  The
   file twin quantifies `offmode` because `FdInode` CARRIES one; a pipe row
   is `FdOpen rb wb (FdPipe γp)` and has no offset field, so the freedom at
   the same place is the OTHER MODE FLAG -- `rb` on the write leaf, `wb` on
   the read leaf (which end's descriptor this is says nothing about whether
   it may also be read/written, and neither payment looks).  Both leaves
   quantify it.
2. **The mould's slot pin is gratuitous, and copying it would have cost the
   lane a second statement.**  `UkWriteFile.wp_uk_ecall_write_std` /
   `udepwf_std_write_file` pin `a0 = 1` and `l !! 1`, because echo is their
   only caller.  Nothing in the proof needs it -- the ledger reading
   (`UkReadRows.std_fd_st_of_key`) is uniform in the slot -- and the
   pipeline needs slot 1 (echo's write end) and slot 0 (cat's read end), so
   both new leaves take `fd` with `fd < NSTD` and the ledger's row at it.
   One statement each, not two.  (Upstream's two could be generalised the
   same way for free; not done here, it is outside this lane.)
3. **`UkWriteFile.uwr_fd_st_std` is a DUPLICATE** of the landed
   `UkReadRows.std_fd_st_of_key` -- the same statement up to the index's
   name -- so the brief's "use the mould's `uwr_fd_st_std`" would have
   created a third copy.  Neither new file copies it; both take the
   `UkReadRows` one, which they already imported.  (Retiring
   `uwr_fd_st_std` is a one-line sweep in `UkWriteFile.v`, left for whoever
   next edits that file.)
4. **SS5.4's "if a leaf pins `fdst_nopipe` on the installed row, that pin
   comes off here" describes a pin that does not exist.**  Checked at the
   statements and confirmed by the consumer test: `wp_uk_ecall_dup` takes
   `st <> FdClosed` + `ukn_held N = ∅` and nothing about the type (its table
   row is `UkRun.urun_rows_dup`, premise `fdv !! k = Some st` only -- a COPY
   of a row the table already had is paid by whatever paid that row);
   `_dup_untracked` goes through `urun_rows_copy`, which has no premise;
   `_dup_closed` moves no row; `wp_uk_ecall_close` / `_close_std` take the
   payment as `UkRun.udepw_cl N m pc st`, INDEXED BY THE STATE, whose left
   arm is the pure "not a pipe" and whose right arm is a deposit at 21 --
   which is exactly where PIPE-REG's registry link goes in.  The
   `fdst_nopipe` those two proofs use is `fdst_nopipe_closed`, about the
   `FdClosed` they INSTALL.  So: no twin added, no pin lifted, nothing to
   decide.

**THE ONE THING THE NEXT LANE NEEDS FIRST** (SH-PIPE): **do not route the
PIPE arm's `close(p[0])` / `close(p[1])` through `UkSh.wp_ksh_close`.**  That
wrapper and `UkSh.wp_ksh_cstub` (and `UkShRedir.wp_kshx_close_std`) carry the
PURE premise `forall rb wb gp, st <> FdOpen rb wb (FdPipe gp)` and spend it
on `UkRun.udepw_cl_nonpipe`; the pin is LOAD-BEARING (it is the whole of how
those leaves mint their close deposit), so by this lane's STOP rule it was
not lifted.  A pipe row's close must go through the GENERIC
`UkRunSys.wp_uk_ecall_close` with `udepw_cl_of_udepw` and the registry's
deposit at 21 -- which is what SH-PIPE's brief already says, and which means
sh's three instructions around that ecall have to be re-walked (or
`wp_ksh_cstub` generalised to take `udepw_cl N m1 pc1 st`, a statement
change outside both briefs).  `close(1)` / `close(0)` shut CONSOLE rows and
the wrappers serve them unchanged.

For ECHO-PIPE / CAT-PIPE: the two `_std` leaves are ready and their
statements are above; the slot is a parameter, so echo takes `fd := 1` and
cat `fd := 0`, and the OTHER mode flag is free at both.

### PIPE-MODEL (2026-09-18)

**Landed**: `iris/PipeDisc.v` (2731 lines, new file, row added to
`iris/_CoqProject` after `FileDiscDec.v`), nine sections, every proof with
a `Proof using`, no `Admitted`, whole `iris` tree green, audits unmoved
(nothing imports it).  Branch `app-pipe/pipe-model`, five commits
(`490e2f819`, `75e2d32a4`, `d1c860158`, `edc45260e`, `e90d30b4f`).
`Print Assumptions` = **Closed under the global context** for
`palt_of_code`, `merge_prefix`, `pcont_shape`, `sessp_prefix_det`,
`disc_p_disc`, `demo_p_ran`, `demo_p_both_LR`, `demo_p_bad` (recorded in
the file's §9).

Shape: `FileDisc.v` file-section for file-section, with **no threaded
state** (a pipe dies with its era), so the session laws are
`EchoDisc.sess`'s at the letter.  `FileDisc` is NOT imported.

**WHAT THE DESIGN GOT WRONG.**

1. **`palt_ok` admits no prologue-re-entering alternative at an `LPipe`
   line** — landed as designed, and the gap is stated as
   `palt_ok_pipe_no_panic : palt_ok (LPipe ws) a -> palt_panic a = false`.
   §1's table says `PEcho` is "LEcho lines only"; §1's prose two paragraphs
   later says the echo application's `alt_panic` arm (sh's **main-loop**
   `fork1` failing, which kills the shell and re-enters init's prologue)
   "is unchanged and `LPipe` lines reach it exactly as `LEcho` lines do (it
   is decided before the line is parsed)".  Both cannot hold.  The machine
   CAN panic in the main loop on a round whose typed line is a pipeline
   line, and then the wire shows `fork\n` followed by a FRESH PROLOGUE —
   which no `LPipe` alternative prints (`PFork` prints `fork\n$ `, and the
   two part at byte 5 whenever the re-entered prologue carries the banner).
   **The theorem at the model as written would be FALSE, not vacuous.**
   One-line repair, for the owner: `palt_ok (LPipe _) (PEcho 3) := True`
   (`pcont (LPipe ws) (PEcho 3) = alt_panic` already, and `palt_panic`
   already fires, so `alt_cont_p` appends the prologue with no other
   change; `palt_ok_pipe_no_panic` then goes away and `pcont_shape_nl`
   below has to grow the `LPipe` arm, which it can — see 3).

2. **`PBoth`'s code is not computable**, so the design's "one alternative
   per interleaving, encoded WITH `sel`" cannot be *decided* anywhere.
   `palt_code (PBoth sel) = 11 + 3 * encode_nat sel` reads `encode_nat` as
   a **unary `nat`**, and `palt_ok` forces
   `length sel = |dg_execL| + |dg_execR| = 33`; measured growth is ~4x per
   entry (`encode_nat (replicate 4 true) = 425`,
   `encode_nat (replicate 8 true) = 109225`), so the code is ~`4^33`.
   The model stays sound — nothing in the theorem computes a code and
   `palt_of_code` is a rewrite — and the two `PBoth` demos are proved by
   rewriting with it (`demo_p_both`, one lemma for every interleaving).
   But `alts_ok_p`'s `Decision` instance, and any `vm_compute` witness, is
   unusable at a `PBoth` round.  **Lane PIPE-STAGE / PIPE-2W: take
   `cs : list palt`, or index the interleaving by a binary code, if
   anything downstream has to decide a resolution.**

3. **`pcont_shape` is weaker than `FileDisc.cont_shape`, necessarily.**
   The brief asked "here EVERY continuation may satisfy the shape; if so
   say so".  Answer: for the `'$'`-free-run-then-prompt shape, YES — every
   continuation but `PEcho 3` satisfies it, `PPipe` and `PFork` included,
   and `PEcho 3` is the one the prologue follows.  But `FileDisc`'s
   STRONGER shape (the run's only newline, if any, is its LAST byte) is
   **FALSE at `PBoth sel`**: a merge of the two diagnostics carries TWO
   newlines (`pcont_both_no_nl_shape` refutes it at
   `sel = 17 trues ++ 16 falses`).  Landed as two lemmas: `pcont_shape`
   (nodollar only, every line) and `pcont_shape_nl` (the full shape, echo
   lines only).  That is enough, because a panic alternative forces an echo
   line (`palt_panic_LEcho`) and the only cases of `pcont_pair_det` that
   spend the newline disjunct put a panic on one side.  If repair 1 is
   applied, the `LPipe` arm of `pcont_shape_nl` is `alt_panic`'s own shape
   and goes through unchanged.

4. **`merge` must STOP at an exhausted side, not skip.**  With the skipping
   reading ("a `true` at an empty `d1` consumes the selector and produces
   nothing") `merge_take` is false — at `sel = [true; false]`, `d1 = []`,
   `d2 = [x]` it gives `merge sel d1 d2 = [x]` while
   `merge (take 1 sel) d1 d2 = []` — and §4.3's `merge_prefix` would need
   side conditions.  Landed stopping, which makes `merge_take` and
   `merge_prefix` **unconditional**; at every `sel` the model admits the
   two definitions agree.

5. **`parse_pline` inverts `line_body`, not `line_bytes`.**  The brief's
   `parse_pline (line_body (line_bytes l)) = Some l` is not well-typed, and
   `parse_pline (line_bytes l) = Some l` is false at every `l` (the cut has
   already stripped the newline).  Landed as `parse_pline_body`
   (`pline_ok l -> parse_pline (line_body l) = Some l`), `line_body_parse`
   and `line_bytes_parse` (`parse_pline b = Some l -> line_bytes l = b ++
   [wl_nl]`) — `FileDisc`'s first departure, verbatim.

6. **`pipe_phi` takes the history alone** (`disc_p h -> Forall good_out_p
   (cycles_of h)`), as `FileDisc.file_phi` does; `AppEcho.echo_phi`'s
   `gstate` argument belongs to the record, so lane PIPE-STAGE adds it.

**WHAT WAS NOT REFUTED, and is worth knowing.**  `PRan`'s continuation is
`EchoDisc.line_alts_of ws !!! 0` on the nose (`pcont_PRan_alt0`,
`pd_ran_echo`), and `alt_execL = EchoDisc.alt_execfail` definitionally
(`alt_execL_echo`) — so the claim really is cheap.  At an echo-only input
this model IS the echo model: `sessp_sess`, `pro_ok_p_ok`, `disc_p_disc`
(`disc_p h <-> disc h`).  And the extension is strict, not a renaming:
`demo_p_partial`/`demo_p_full` are pipe-disciplined while
`EchoDisc.disc_input` refutes both (`demo_p_partial_not_echo`,
`demo_p_full_not_echo`).

**Names that moved** (nothing else): `line_body` added beside
`line_bytes` (the parser's fixpoint, `FileDisc` precedent);
`dg_execL`/`dg_execR` for the two diagnostics' BYTES and `dg_exec_cat`,
`dg_pipe` for their word lists; `alt_execL`/`alt_execR`/`alt_pipe`/
`alt_forkc` for the four constant continuations (`alt_forkc` is
`EchoDisc.alt_panic ++ u_prompt`, i.e. the RUNCMD CHILD's panic, which is
NOT `alt_panic`); `pd_*` for the `FileDisc`-section-0 helpers re-proved
under their own names.  `merge`, `count_true`, `merge_prefix`,
`merge_no_dollar`, `palt_code`, `palt_of`, `palt_ok`, `pcont`, `sessp`,
`alt_cont_p`/`alt_blk_p`/`alt_seq_p`, `expected_rel_p`, `good_out_p`,
`disc_p`, `pipe_phi`, `sessp_prefix_det`, `demo_p_bad` are the designer's
names verbatim.  (`merge` shadows stdpp's map `merge`; harmless here, but
PIPE-2W may prefer `pmerge`.)

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  Lane PIPE-STAGE: the
resolution list `cs : list nat` cannot carry a `PBoth` alternative in any
computable form (finding 2).  Decide that before instantiating the stage's
`cs_auth`/`cs_lb` — the choice propagates into `EchoOut`'s ghosts and into
PIPE-2W's merge lease.  And the owner owes a ruling on finding 1 before
`AppPipe`'s theorem is stated, because it is the difference between a true
theorem and a false one.
