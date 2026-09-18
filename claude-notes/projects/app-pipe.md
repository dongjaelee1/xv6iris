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

- [x] **PQ-FLAG** (kernel/spec, design §3.1).  `PipeQueue.pipe_wlink` gains
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
- [x] **PIPE-REG** (U tier, design §2).  New `iris/PipeReg.v`: `pipe_reg γp
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
- [x] **SH-PARSE-PIPE** (U tier, sh's parser, design §5.1).  Mould:
  upstream's SH-PARSE / SH-PARSE-2 findings in `projects/app-file.md`.
  `parsepipe` turns ONCE for ` | cat` (today `wp_kshp_parsepipe_gt` is the
  `>`-shape walk); `pipecmd` into the node catalogue (`ush_cmd` at `UPipe
  (UExec l) (UExec r)`); `nulterminate`'s PIPE row; `parseline`/`parsecmd`
  at the pipe shape; the parser theorem at the pipe shape;
  `UkShFork.ushf_lexable` grows the shape.  NEW files where possible
  (`UkShPipeLex.v`, `UkShPipeParse.v`); the existing simple-line and
  redirect-line theorems unchanged.  Bar: whole tree green.
- [x] **SH-PIPE** (U tier, sh's `runcmd`, design §5.1).  NEW `iris/UkShPipe.v`:
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

- [x] **PIPE-NEG1** (kernel/U-tier spec, SH-PIPE's R-1; after PIPE-REG lands
  so the two edits to `wp_uk_ecall_pipe`'s post do not collide).
  `UsysMemOk.usys_fd_ok`'s pipe row pins the failing return to
  `r = mword_of_int (-1)` (as the open and dup rows do); `ProofSysPipe`'s
  discharge (sys_pipe returns −1 on every failure arm); `wp_uk_ecall_pipe`'s
  failure arm reads `r = -1`; `UkShPipe.ush_pipe_call_weak_of_leaf`
  upgraded to the full `ush_pipe_call`, closing `wp_kshr_runcmd_pipe` at
  today's kernel.  Bar: whole tree green, audits unmoved (the row's cone
  is the whole U tier — one conjunct, no statement but the row moves).
- [x] **PIPE-PROTO** (design §3; after PQ-FLAG + PIPE-REG).  `iris/PipeProto.v`:
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
- [x] **CAT-PIPE** (design §5.3; after PIPE-PROTO + PIPE-STD).
  `iris/UCatPipe.v`: cat's round and `image_entry` at fd 0 = a pipe read
  end, at the pipe stage's cursor.
- [x] **PIPE-DEC** (pure; after PIPE-MODEL-2).  `iris/PipeDiscDec.v` ending
  in `Global Instance disc_p_dec h : Decision (PipeDisc.disc_p h)` — the
  twin of `FileDiscDec` (STAGE's BLOCKER 1: the ledger's counter sits at
  `decide (disc h)`); the `PBoth` candidates enumerated as a THEOREM, never
  computed.  Bar: Closed under the global context; PipeDisc.v unedited.
- [x] **PIPE-STAGE** (design §4.1/§5.5; after PIPE-MODEL).  `iris/AppPipe.v`
  and the links record instance `PipeLinks`; `Hphi` at `pipe_phi`; the
  record's laws; `pipe_fs_pure`.  Mould: upstream's STAGE / STAGE-2 /
  FILE-DEC findings and `AppFileRec.v`.
  LANDED with TWO CARVE-OUTS, both reported in the Findings block:
  the `LinkRec` INSTANCE (`pipe_link_inst`) is a LANE of its own — it needs
  a `PipeLinksLine.v`, the pipe twin of `EchoLinks`+`EchoLinksLine`, which
  upstream's FILE application has not landed either (there is no
  `file_link_inst` in the tree) — and `pipe_fs_pure` is NOT a field of the
  record, which leaves /cat's image unpinned in the claim (owner decision).

- [ ] **PIPE-CLAIM** (= PIPE-STAGE part 2, design §5.6; after the upstream
  merge is green).  `pipe_pred` at `file_fs_pure`; `AppPipe.app_pipe` at
  `app_pred := pipe_pred`; the record's laws re-derived; `pipe_Happ_init`
  with `era0_cat_pins` off the image; the program-tier laws at `pipe_pred`
  (`init_cons_laws_at`, INIT-FILE's mould minus the f-state).  Also: merge
  main (upstream's `StageRec.v`/`FileLinkInst.v`, `app_taint`) into the
  branch first and re-read the mould.
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

### SH-PARSE-PIPE (2026-09-18) — the pipe line's LEXER lands whole and its LEXABILITY is a theorem; what is left of the parser is TWO RE-STATEMENTS, and the one instruction nobody had walked is landed

Branch `app-pipe/sh-parse-pipe`, NINE commits (`d17064949`, `16cc644da`,
`6ed408fc8`, `0a2de5b53`, `9ba83f6a1`, `cb0a796c3`, `9c78e50fa`, this one
and `b5bd56a9f`).  Whole
tree green on the lane's remote tree (`build`, RC=0); FIVE NEW FILES plus
five `iris/_CoqProject` lines and NOT ONE LANDED STATEMENT TOUCHED (the
simple-line and redirect-line theorems are byte-identical, `UkShRun.v` is
unread-only, `make gen-ucode` unrun); no `Admitted`, every result carries
`Proof using`.

**WHAT LANDED.**

- `iris/UkShPipeLex.v` (pure, a leaf) — the line model.  `ushq_bar` and its
  byte facts; `ushq_one` / `ushq_pipe` (the canonical shape: one blank each
  side of the `|`, the right command the run `[S (S p), e)`, blanks to the
  end) with the five scan readings and `ushq_pipe_not_nosym`;
  **`ushq_sym_ok`** (ONE premise for `gettoken` covering BOTH symbol bytes,
  which `UkShParseSym.ushs_gt_ok` implies — `ushq_sym_ok_gt`);
  `ushq_nosym_from len f c` with `ushq_nosym_from_0` (it IS
  `ushp_no_symbols` at `c = 0`, both ways) and the pipe line's two
  instances; `ushq_line_is` (positional, `UkShRedirLine.ushs_line_is`'s
  twin) with `ushq_line_is_pipe`; both token lists; **the lexability
  theorem `ush_line_toks_pipe` / `ush_line_toks_holds_pipe`** and its
  existential form `ush_line_lexable_pipe(_holds)`; the demo at
  `echo hello world | cat` and the NEGATIVE witness.
- `iris/UkShPipeTok.v` — `wp_kshp_gtk_disp_bar` (gettoken's `|` arm, TEN
  instructions), `wp_kshp_gtk_disp_sym` (the two symbol arms under ONE
  statement), `wp_kshp_gettoken_syms` (gettoken end to end at
  `ushq_sym_ok`).
- `iris/UkShPipeParse.v` — `ushp_pipe_node` / `ushp_pipe_close` (the node
  with BOTH children named), `ushp_jrow_pipe`, and
  **`wp_kshp_nulterminate_pipe`** (nulterminate's PIPE row, `user/sh.c:481`).
- `iris/UkShPipeSeam.v` — **`ush_cmd_of_ushp_pipe`** (the node catalogue
  `ush_cmd γd p (UPipe (UExec …) (UExec …))`), `ushq_malloc_le_third`, and
  the seam's vacuity instances `ushq_demo_cut_ok_l` / `_r`.
- `iris/UkShPipeEx.v` — `ushp_T_arg_bar` / `ushp_T_pipe_bar` /
  `ushp_peek_arg_hit` / **`ushp_peek_pipe_hit`** (the fact parsepipe's guard
  turns on), `ushp_peek_res_miss` / `ushp_peek_redir_miss_bar` /
  `ushq_peek_redir_miss_pipe` (the miss the left command's LAST
  `parseredirs` needs), and **`wp_kshp_pex_bar`**, the argument loop's exit
  at the `|`.

**THE TOKEN LIST AND THE NODE, VERBATIM (what SH-PIPE consumes).**  With
`p0 := length (wl_body ws)`, `p := p0 + 1` (the `|`),
`e := p0 + 3 + length right`, `len = e + 1`:

```coq
  (* LEFT: echo's OWN list, terminated at the '|' *)
  ushs_toks len f (p0 + 1) 0 (wl_toks ws)          (* 0 < length < 10 *)
  (* the '|' itself: gettoken answers 124 and leaves the cursor at p0 + 3 *)
  ushs_gettok_res len f p = 124   ushs_gettok_end len f p = S p
  ushs_gettok_fin len f p = S (S p)
  (* RIGHT: one token, terminated at the line's end *)
  ushs_toks len f len (p0 + 3) [(p0 + 3, p0 + 3 + length right)]
  (* the node, out of ONE line and the two EXEC nodes *)
  ush_cmd γd p (UPipe (UExec (ush_args s0 g toksl))
                      (UExec (ush_args s0 g toksr)))
    where g = ushp_nulfold toksr (ushp_nulfold toksl (ushp_ext len f))
```
At `echo hello world | cat`: `len = 23`, `'|'` at 17, left
`[(0,4); (5,10); (11,16)]`, right `[(19,22)]` (all four `vm_compute`d in
the file's §9).

**THE FIVE FINDINGS.**

1. **NOTHING under the shape had to be generalised again.**  The token
   model (`ushs_toks`), the two scan measures and the whole tokenization
   induction (`UShLexRedir.ushs_toks_tail` / `ushs_toks_line`) never
   mention WHICH symbol byte stopped them, so both of the pipe line's
   token lists come off them unchanged: the left command's arguments are
   ECHO'S OWN `LineWords.wl_toks ws` terminated at the `|`
   (SH-LEX-REDIR's ruling 1, verbatim) and the right command's one token
   is the same induction at the line's own newline.  The pipe line's
   lexability therefore costs NO new induction and NO new premise —
   `EchoDisc.line_ok ws` and `wl_word right` are the whole bill, and
   `ush_line_toks_holds_pipe` is `Closed under the global context`.
2. **ONE premise serves gettoken at both symbols, and the landed walk is
   its instance.**  `ushq_sym_ok` ("every symbol byte is a `|`, or a `>`
   with the `>>` lookahead refuted") is implied by `ushs_gt_ok`, so
   `wp_kshp_gettoken_syms` SUBSUMES `UkShRedirGtk.wp_kshp_gettoken_sym`
   rather than sitting beside it (the landed statement was left alone —
   the bar forbids moving it — so a later lane can retire one).  What
   made that cheap is `wp_kshp_gtk_disp_sym`: both symbol arms land on
   0x388 with the cursor advanced by one and s5 holding THE BYTE ITSELF,
   so one statement covers them and the whole-function walk is the landed
   proof with ONE call changed.
3. **The `|` arm is CHEAPER than the `>` arm, and 0x386 is a six-way
   join.**  sh's `gettoken` has a `>>` case and no `||` case, so the `|`
   arm needs neither the byte after the `|` nor `S k < len`; it is
   0x356/0x35a/0x35e/0x362 → 0x3ca/0x3ce → 0x3e4/0x3e8 → **0x386**
   (`c.addi s1,s1,1`, the arm `|`, `(`, `)`, `;`, `&`, `<` all share),
   falling into 0x388 where the `>` arm and the NUL arm land.
4. **THE MALLOC STOP RULE IS ANSWERED, AND THE ANSWER IS NO EXTENSION.**
   A pipe line makes exactly **THREE** constructor calls — `parseexec`
   runs once per side of the `|` and each run calls `execcmd` (168 bytes),
   and `parsepipe`'s turn calls `pipecmd` (24) — and `parseredirs` turns
   zero times, so `redircmd` is NOT on the path and neither are
   `parseblock`/`listcmd`/`backcmd`.  Three does NOT exceed what
   `ushm_fresh`'s landed chain funds: `UkShMalloc.ushm_malloc_le_one` is
   already GENERAL in the free list's remaining count `R`, so the third
   link is three lines (`ushq_malloc_le_third`, in this lane's own file —
   nothing in `UkShMalloc` moved).  `fresh → 4084 → 4072 → 4060`:
   THIRTY-SIX of the chunk's 4096 units.  SH-MALLOC-3's "the parser's
   capability is BOUNDED" bounds the REQUEST (168 bytes), not the number
   of calls.
5. **The argument loop's exit at the `|` is ONE instruction of new code.**
   `while (!peek(ps, es, "|)&;"))` is refuted at every round on a
   symbol-free line, so no landed walk ever takes the TAKEN arm of 0x62c
   — and that arm goes to **0x662**, which is exactly where the loop's
   exhausted-line exit goes (`UkShRedirEx.wp_kshp_pex_end`).  So
   `parseexec`'s argv terminator stores and its whole epilogue are
   already walked, unchanged, and `wp_kshp_pex_bar` is the entire
   difference.

**WHAT THE BRIEF / THE DESIGN GOT WRONG.**

- **Deliverable 3 ("`UkShFork.ushf_lexable` grows the pipe shape") is not
  implementable as stated, and the design page repeats a phrasing upstream
  already refuted.**  `ushf_lexable` IS GONE (deleted by lane SH-LINE 2b,
  `iris/UkShFork.v:1064`: "it said every line the user could type lexes,
  and it is FALSE"), and SH-PARSE proved that widening its replacement
  `UkShLoop.ush_line_lexable` to a DISJUNCTION is refuted
  (`UkShRedirLine.ushs_line_is_nosym`: a line `ush_line_is` describes
  carries no symbol byte at all, so the right disjunct would be vacuous).
  What replaces it is a THIRD line predicate plus a theorem, which is what
  this lane landed (`ushq_line_is`, `ush_line_lexable_pipe_holds`).  It is
  deliberately NOT defined in `UkShLoop` beside `ush_line_lexable` /
  `_redir`: SH-LEX-REDIR §4 shows the disjunct inside `UkSh.ush_rest_line`
  and the three-way case in `UkShFork.ushf_rest_of_body` are ONE coupled
  change with the child WALK, the pipe child walk does not exist, and a
  premise nobody can discharge is gunk.  Note for whoever lands it: that
  disjunct now has to admit a **FOURTH** arm — echo, redirect, cat
  (SH-LEX-REDIR's own last paragraph) and pipe.
- **Design §5.1's "`UkShRun.ush_simple` admits `UPipe (UExec l) (UExec r)`
  at the top" is the same sentence SH-REDIR refuted for `URedir`.**
  `ush_simple` is a structural `Fixpoint`, so "at the top and nowhere
  deeper" is not expressible in it, and widening it in place silently
  strengthens `UkShRun.wp_kshr_runcmd`, whose proof has no ledger to spend
  on the arm.  The landed answer is the LAYERED `UkShRedir.ush_top`
  (`ush_top (URedir c1 _ _ _) := ush_simple c1`), so lane SH-PIPE wants a
  `ush_top`-shaped extension (`ush_top (UPipe l r) := ush_simple l /\
  ush_simple r`), not an edit to `ush_simple`.  This lane did not touch
  `UkShRun.v` (its bar forbids it) and reports it instead.
- The brief's "check `UkShRedirTok`/`UkShLexRedir` for the `>` arm and add
  the `|` arm the same way" is right, and cheaper than it sounds (finding
  3).  Its "count them from the C and report" for malloc is answered by
  finding 4.  `UkShRun.ush_cmd`'s `UPipe` row and `ush_cmd_pipe` already
  existed, as did `UkShParse.ushp_tree`'s and `ushp_cmd`'s PIPE arms —
  only the CONSTRUCTOR-side node (`ushp_pipe_node`, both pointers named,
  SH-PARSE-2's shape fact at two pointers) had to be added.

**THE STOP, WITH THE INSTRUCTION RANGE.**  `parsepipe`'s turning arm is
**0x6c2..0x6e0, THIRTEEN instructions**, and it rejoins the landed walk
(`UkShRedirCm.wp_kshp_parsepipe_gt`) at its own 0x6b0, so the epilogue is
free:

```
  0x6c2 c.li a3,0 ; 0x6c4 c.li a2,0 ; 0x6c6 c.mv a1,s1 ; 0x6c8 c.mv a0,s4
  0x6ca jal 310 <gettoken>      -- consumes the '|'  (wp_kshp_gettoken_syms)
  0x6ce c.mv a1,s1 ; 0x6d0 c.mv a0,s4
  0x6d2 jal 682 <parsepipe>     -- THE RECURSION, on the right command
  0x6d6 c.mv a1,a0 ; 0x6d8 c.mv a0,s3
  0x6da jal 260 <pipecmd>       -- NOT IN ANY CATALOG (skipfunc)
  0x6de c.mv s3,a0 ; 0x6e0 c.j 6b0
```
It needs three things this lane could not do, in this order:

1. **`parseexec` at the pipe line, LEFT** — a RE-STATEMENT, not a new
   walk: `UkShParseExec.wp_kshp_parseexec` / `wp_kshp_pex_loop` (or
   SH-PARSE-2's `UkShRedirEx`/`UkShRedirPex` copies) at
   `ushs_toks len f p 0 args` and `ushq_pipe_nosym_below`, with
   `wp_kshp_pex_bar` closing the last round.  No instruction of it is
   undiscovered (finding 5).  ONE MORE "one line of N": the loop calls
   `parseredirs` after EVERY argument, so its last call sits ON the `|`,
   and `UkShRedirPr.wp_kshp_parseredirs_ns` cannot serve it — that walk's
   premise is "the byte at the cursor is not a symbol", which the `|`
   falsifies, and it spends it in one line through
   `ushs_peek_res_nsym`.  The weakest fact is landed here instead
   (`ushp_peek_res_miss`, the mirror of `UkShRedirLex.ushp_peek_res_hit`
   and strictly more general than `ushs_peek_res_nsym`, with
   `ushq_peek_redir_miss_pipe` its instance), so the re-statement of
   `parseredirs`' zero-turn walk carries no new obligation either.
2. **`parseexec`/`parsepipe` at the pipe line, RIGHT** — the same walks at
   `ushq_nosym_from len f (S (S p))` (`ushq_pipe_nosym_from`), which is
   the "one line of 460" shape SH-PARSE named: every use those walks make
   of `ushp_no_symbols` is at or above their own cursor.
3. **`pipecmd`'s catalog row** — `tools/ucode_shp.txt` carries
   `skipfunc pipecmd`; it becomes `func pipecmd`, `make gen-ucode` is
   re-run and `iris/UCodeShP.v` COMMITTED (`make check-ucode`'s second
   half is `git diff --exit-code`).  Two knock-ons, both measured on
   SH-PARSE's `redircmd` precedent: `shp_syms_pins` gains a conjunct, so
   the ELEVEN `destruct shp_syms_pins as (…)` patterns in
   `iris/UkShParse.v:857-877` each gain one `_` (proof text only, no
   statement moves), and the whole parser cone recompiles.  The
   constructor itself is `UkShRedirCmd.wp_kshp_redircmd`'s walk with five
   field stores instead of seven.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  Item 1 above — the LEFT
`parseexec` — because it is pure re-statement and it is what makes the
turn's first call site exist.  Everything the re-statement needs is
landed: the line model and both token lists (`UkShPipeLex`), gettoken at
the `|` (`wp_kshp_gettoken_syms`), the loop's exit (`wp_kshp_pex_bar`),
the two table hits, the PIPE node, `nulterminate`'s PIPE row, the node
catalogue and the third malloc link.

### PQ-FLAG (2026-09-18)

**LANDED** (`iris/`, branch `app-pipe/pq-flag`, commit `539b48d6`):

- `PipeQueue.pipe_wlink γ b Φ` now reads
  `∀ s, ⌜ps_wo s = true⌝ -∗ pipe_qauth γ s ={⊤}=∗ pipe_qauth γ (pst_write b s) ∗ Φ`.
  Every `_of_frag` constructor, every `pipe_wchain`/`pipe_rchain` lemma
  (`_0`, `_cursor`), every payment/post lemma (`pipe_wpay*`, `pipe_wpost*`,
  `pipe_rpost*`) keeps its statement BYTE-IDENTICAL and goes through by
  introducing and ignoring the premise; `pipe_wlink_mono` passes it on.
- `PipeQueue.pipe_wlink_of_uncond` — the lane's sanity lemma: the
  unconditional stepper (the OLD link) is still a `pipe_wlink`, so no
  holder loses anything.  The converse is false and not stated.
- `SpecPipewrite.wp_pipewrite_sconf_body` gains ONE pure premise, `w = true`
  (between `eb = true` and `locks_below`).  **This is the shape the design
  asked to be reported:** the fire site does NOT read the flag out of the
  code (pipewrite never loads `pi->writeopen`), it reads it out of the
  CALLER'S CREDENTIAL, so the contract has to pin the end it is entered
  with to the write end.  It is not a restriction on the code — filewrite
  reaches the call only past `f->writable`, which IS that boolean.
- `ProofPipewrite`: `pw_wo_open` (new; `w = true` + the payload's
  `pipe_endstate γp true wo` + the caller's `pipe_ref γp w q` ⊢
  `⌜pflag_open wo⌝`, via `PipeInvDefs.pipe_endstate_holder`), derived ONCE
  per loop round right after the payload is destructured; `pw_qres_push`
  and `pw_wlink_apply` gain the pure premise (`pflag_open wo` /
  `ps_wo s = true`), bridged by `pipe_qres`'s coupled arm
  (`ps_wo s = pflag_bool wo`).  `w` is deliberately NOT substituted — the
  script names it in a dozen argument lists.
- `ProofFilewrite`: ONE line — `Hwb : fc_wbool Cf = true` (already asserted
  on the pipe path from `fw_wbool_of_fall`) added to the
  `wp_pipewrite_sconf` argument list.  No statement in the file moves.

No other consumer BUILDS a link value today: `SpecFilewrite`/`SpecFileread`,
`UkWritePipe`/`UkReadPipe` and `UexecExecMint` only pass `pipe_wpay`/
`pipe_rpay` through or pay the taint, so no holder-side `iIntros (%)` was
needed anywhere.

**REFUTED: the read link's `⌜ps_ro s = true⌝` (design §3.1's "free, for
symmetry").  It is not free, and it is not landed.**  Evidence at the
statement:

1. piperead never loads `pi->readopen` (`grep readopen ProofPiperead.v` is
   empty; `pr_res_i`'s leftover fact is about `wo`, not `ro`), so the only
   route to the fact is the caller's `pipe_ref γp false q`, i.e. a
   `w = false` premise on `SpecPiperead` — the mirror of what landed.
2. That premise instantiates at `ProofFileread`'s call site to
   `fc_wbool Cf = false`, and fileread learns NOTHING about
   `fc_wbool Cf`: the file layer picks a pipe's end off `fc_wbool C`
   (`FileInvDefs.file_core_noff`), and read's walk only rules out
   `f->readable = 0` (`SpecFileread.fileread_in_of_pipe` /
   `fileread_extra_of_pipe` both leave `wb` free — they destruct `rb` and
   refute `rb = false`, and say nothing of `wb`).
3. The missing fact is a PIPE FILE'S TWO ENDS ARE COMPLEMENTARY —
   `pipealloc` sets `readable/writable` to `1/0` and `0/1` — which is true
   of the code and dropped at the store.  `fdstate_ok` already pins
   `fc_writable C = (if w then 1 else 0)`, so the fact is expressible; what
   is missing is a publisher.  Two ways in, BOTH outside this lane's brief
   (STOP rule 1):
   - narrow `SpecFileread`'s pipe arm from `FdOpen true _ (FdPipe γp)` to
     `FdOpen true false (FdPipe γp)` (and add `fc_writable C = 0` to
     `fileread_in_of_pipe`/`fileread_extra_of_pipe`) — a NON-pipe `Spec*`
     statement moves, and every U-tier read consumer (row 5, `UkReadPipe`)
     would have to prove its pipe row is a read-end row;
   - or add the complementarity conjunct to `FileInvDefs.file_core_noff`'s
     pipe arm, published by `sys_pipe` — a landed invariant moves.
   Nothing in the pipeline protocol needs it: (P3) freezes `ps_ws`, which
   only a WRITE moves, so the reader's side needs no flag premise.  The
   refutation is recorded in `PipeQueue.v` at `pipe_rlink`.

**WHAT THE DESIGN GOT WRONG.**  §3.1's parenthesis "and symmetrically
`pipe_rlink` gains `⌜ps_ro s = true⌝` (free, for symmetry …)" — it is not
free; see above.  §3.1's "the two fire sites supply it from the caller's
`pipe_ref`" is right for the write site but understates the cost: the
`pipe_ref` in `SpecPipewrite`'s precondition is at a GENERIC end (`ANY end,
ANY positive fraction`, the file's own words), so supplying the premise
means the CONTRACT changes, not just the proof.

**THE ONE THING THE NEXT LANE NEEDS FIRST** (PIPE-PROTO): the write link's
premise is now the state's `ps_wo`, so the (P3) arm of `pipe_body` is
refuted from `γeof ↦ Some w` forcing `ps_wo s = false` — as designed — and
the writer's chain builder must hand `pipe_wlink_of_frag` its fragment
KNOWING nothing extra (the constructor's statement did not change).  Do NOT
plan on a `ps_ro` premise on the read side; the reader's EOF observation
(`pipe_olink`, `pst_eof`) is unaffected, but any reader-side protocol that
wanted "the read end is open" must first pay for the complementarity fact
above.

### SH-PIPE (2026-09-18) — runcmd's PIPE arm landed at call premises; the pipe row's -1 is the one wall

Branch `app-pipe/sh-pipe`, three commits, ONE new file (`iris/UkShPipe.v`,
1 line of `iris/_CoqProject`).  No landed statement moved.

**WHAT LANDED** (`iris/UkShPipe.v`, immediately after `UkShRedir.v`):

- `ush_ptop` — the one-level PIPE relaxation of `UkShRun.ush_simple`,
  layered exactly as `UkShRedir.ush_top` is.  **Deliverable 1 of the brief
  ("`ush_simple` admits `UPipe (UExec l) (UExec r)` at the TOP") is
  REFUTED for SH-REDIR's already-recorded reason**, verbatim: `ush_simple`
  is a structural `Fixpoint`, so "at the top and nowhere deeper" is not
  expressible in it, and widening it in place silently strengthens
  `UkShRun.wp_kshr_runcmd`, whose proof carries no ledger, no children set
  and no fd handles to spend on the arm.  Design §5.1 should say
  `ush_ptop`.  (The arm itself needs no scope predicate at all — it takes
  the tree as `UPipe cl cr` with `ush_simple cl`/`ush_simple cr` beside
  it, as `wp_kshr_redir_arm` takes `URedir c1 file mode 1`.)
- `ush_cldep st` = `□ ∀ N m pc, UkRun.udepw_cl N m pc st` — the close
  deposit at every RECORD and every key (`UkCat.kcat_cldep` with the
  record quantified too, because the arm's three processes close their
  pipe rows at three different gname triples).  `ush_cldep_of_law` builds
  it from `udepw_law 21`.
- `wp_kshpi_close_h` — sh's `close` stub at a TAIL HANDLE through the
  generic `UkRunSys.wp_uk_ecall_close`, per lane PIPE-STD's note.
- `wp_kshpi_dup` — sh's `dup` stub (nothing had walked it).
- `wp_kshpi_wait0` — `wait(0)` at a NAMED children set, relaying
  `UexecRet.uwait_ans`.
- `ush_pipe_ans` / `ush_pipe_call` — pipe(2) as a call premise.
- `ush_fork_ans` — `wp_kshr_fork1`'s answer with `uch` taken out.
- **`wp_kshr_pipe_arm`** — the arm, 31 instructions in three processes,
  0x13c..0x1c2 plus the `panic("pipe")` tail 0x172..0x17a; three
  continuations out (each child at `runcmd`'s own entry pc, the parent at
  0xea).  Statement verbatim in the lane report.
- `wp_kshr_runcmd_pipe` — the CONSUMER TEST: the arm at
  `R = RcL = RcR = Rk := emp`, `Qc := ukn_pay N`, both children closed by
  `UkShDiag.wp_kshr_runcmd_final` and the parent by
  `UkShRun.wp_kshr_exit0` at 0xea.  Its ONLY remaining premise is
  `ush_pipe_call`.
- `wp_kshr_runcmd_ptop` — the same at `ush_ptop c`, dispatching to the
  landed walk at every other shape (this is what makes §1's scope claim
  load-bearing).
- `ush_pipe_ans_weak` / `ush_pipe_call_weak` +
  **`ush_pipe_call_weak_of_leaf`** — the gap, MEASURED: the pipe call with
  its failure arm weakened from `r = -1` to the leaf's own
  `uint r <> 0`, discharged OUTRIGHT from the taint and
  `fd_lowest_closed ld = None`.

**R-1 — THE ONE WALL: `UsysMemOk`'s pipe row does not pin a failing
return to -1, and sh's next instruction is `bltz a0`.**  Evidence at the
statement: `UkRunSys.wp_uk_ecall_pipe`'s post is
`(∃ a b γp, ⌜uint r = 0 /\ …⌝ ∗ …) ∨ (⌜uint r <> 0⌝ ∗ ustd … l)`, and
`usys_fd_ok`'s pipe row is `if decide (uint r = 0) then … else sts' = sts`
— the OPEN and DUP rows beside it both say `r = (mword_of_int (-1))` on
failure, pipe's says nothing.  `uint r <> 0` does not decide
`uv_btaken BLT r zero_reg`, and the not-taken-and-nonzero path runs the
whole pipeline on two garbage descriptors, so it is not walkable.  It
cannot be bridged by a premise either: `∀ r, uint r <> 0 -> r = -1` is
FALSE, and a premise stated over the row is false too (take `r = 1`,
`sts' = sts`), so anything built on either would be vacuous.  **The fix
is one conjunct in `UsysMemOk.usys_fd_ok`'s pipe row plus its
`ProofSysPipe` discharge** — `ush_pipe_call_weak_of_leaf` proves that
everything else the arm asks of the leaf (the two handles, the eight
bytes read back as the two descriptor numbers, the unmoved ledger, the
two persistent close registrations) is payable today.

**R-2 — a `wait(0)` CANNOT TELL sh's TWO CHILDREN APART, so design §4.2's
lend/payload split must be SYMMETRIC.**  Two independent reasons, both at
the statement: (a) `UkShRun.wp_kshr_fork1` requires
`forall x y, Q x = Q y`, so a child's payload cannot depend on its exit
status; (b) the reaping arm of `UexecRet.uwait_ans` binds its own
generation with `γ' ∈ cs \/ pidv = mword_of_int 1`, and the only form
that refutes the second disjunct (`UkShRun.wp_kshr_wait_pid`) needs the
caller's `UserChildren.upid` fragment — which `UkFork.wp_uk_ecall_fork`'s
child arm DOES hand out (`UkFork.v:935`) and which `wp_kshr_fork1` then
DROPS.  So the arm relays the two `ush_fork_ans` and the two `uwait_ans`
unredeemed and one payload `Qc` serves both children.

**WHAT ELSE THE DESIGN GOT WRONG.**

1. **`p = {3, 4}` is not derivable** (design §5.1, and the brief's "the
   eight bytes spell 3, 4").  The row's two slots are
   `fd_least_closed sts a` over the WHOLE table, and a program's ledger
   pins only its low `NSTD` (`UserFd.ustd_agree`), so all a caller learns
   is `NSTD <= a`, `a <> b`, `a, b < NOFILE`.  The arm is stated at
   abstract `a`/`b` and never needs more.
2. **The queue fragment cannot be a conjunct of the call premise.**  It
   lives in the key's own post (`spost_at uslot USYS_pipe`) and only the
   deposit class's INSTANCE can read that row, while every `Uk*` file —
   this one included — is stated over the class.  It goes inside the
   abstract `R γp`, as the file claim goes inside `ush_open_call`'s `K`.
3. **The registration is HANDED OUT, not OWED.**  Design §2 has the leaf
   hand the run back as `pipe_reg γp -∗ urun …`; an arm that had to
   *supply* `R γp` would need a registrar premise over a `γp` it does not
   yet know.  Stated as an answer conjunct instead, BOTH leaves
   instantiate it: today's at `R := fun _ => emp`, PIPE-REG's by having
   its supplier allocate the invariant and redeem the owed run.
4. **The close deposits are not arm parameters.**  `fileclose_cpay`-shaped
   per-close parameters cannot be stated: the children close at records
   fork chooses.  They ride on the call's answer as the two persistent
   `ush_cldep`s, which is design §2's ruling read literally (one
   persistent registration per pipe row, payable any number of times).
5. **`wp_kshr_fork1_any` is the wrong fork wrapper** (the brief names it).
   It fixes `Rc := emp` and `Q := ukn_pay N`, so it can carry neither a
   lend nor a per-child payload; the arm uses `UkShRun.wp_kshr_fork1`,
   which has `Sc`, `Q`, `Rc` and `Pex`.
6. **`wp_kshr_wait0` returns nothing** — it is index-free (`uch_any`) and
   discards the answer, which is right for the LIST arm and useless for a
   round.  Replaced by this file's `wp_kshpi_wait0`.
7. `int p[2]` costs NO extra stack: `wp_kshr_entry` already hands out the
   word at `sp0 - 40`, which is exactly p, inside the 48-byte frame.  The
   arm's budget is the LIST arm's, `6 * ush_ht (UPipe cl cr) + (2 + (ush_Dg + n))`.
8. Three things the brief expected to be missing were already there:
   `UkShRun.forkable_ush_paypipe` (the PIPE arm's fork payload), 
   `UkShRun.ush_pipe_halves`/`ush_bytes_as_word` (§8a), and every
   `uis_shk_*` fact for 0x13c..0x1c2 (`tools/ucode_shk.txt` catalogues all
   of runcmd).  `Local` lemmas in a landed file ARE reachable by qualified
   name (`UkShRun.wp_kshr_wait0`, `UkShRedir.wp_kshx_rcall`), so
   UkShRedir's "three leaves copied, not shared" was avoidable.

**AGREES WITH SH-PARSE-PIPE, independently.**  That lane reached the same
refutation of "widen `ush_simple`" and asked for a layered top-level
predicate; `ush_ptop` is it.  And the arm is stated at an ARBITRARY
`ush_cmd (ukn_d N) t (UPipe cl cr)` with `ush_simple cl` / `ush_simple cr`
beside it, so the node
`UPipe (UExec (ush_args s0 g toksl)) (UExec (ush_args s0 g toksr))` that
`UkShPipeSeam.ush_cmd_of_ushp_pipe` produces is an instance of it with
nothing to restate (`ush_simple (UExec _)` is `True`).

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  For SH-PIPE-ROUND: nothing
from this lane is missing — instantiate `ush_pipe_call` and use
`wp_kshr_pipe_arm` (not `wp_kshr_runcmd_pipe`, which drops everything).
For anyone who wants the arm CLOSED at today's kernel: R-1, the `-1` in
`UsysMemOk`'s pipe row.  For PIPE-REG: `wp_uk_ecall_pipe` should also
hand back the two `ush_cldep`s (or whatever `pipe_reg` becomes), because
that is what the six closes are paid with and the taint is the only
source today.
### PIPE-MODEL-2 (2026-09-18) — the coordinator's two rulings, landed

Commit `27e95d086` on `app-pipe/pipe-model` (after `fd925474d`).  Whole
`iris` tree `RC=0`; thirteen headline results **Closed under the global
context** (`bdec_bnum`, `palt_of_code`, `palt_code_inj`,
`palt_code_both_big`, `pmerge_prefix`, `pcont_shape`, `pcont_shape_nl`,
`sessp_prefix_det`, `disc_p_disc`, `demo_p_ran`, `demo_p_panic`,
`demo_p_both_LR`, `demo_p_bad`; list kept in the file's §9).
`iris/PipeDisc.v` is now 3014 lines, 234 results, no `Admitted`, no
landed `.v` file edited.

**RULING 1 — the main-loop panic at an `LPipe` line: LANDED.**
`palt_ok (LPipe _) (PEcho k) := k = 3` (so exactly `PEcho 3` joins, as
ruled).  What moved, and nothing else:

- **Retired**: `palt_ok_pipe_no_panic`, `palt_panic_LEcho`.
  **New**: `palt_ok_pipe_echo` (the iff), `palt_ok_pipe_panic`, and
  `palt_panic_3 : palt_ok l a -> palt_panic a = true -> a = PEcho 3` —
  the panic alternative is now the *same* alternative at both line
  shapes, so the determinacy proof never asks which shape it is looking
  at.  That is a simplification, not a cost.
- **`pcont_shape_nl` generalised** from `LEcho ws` to every `l`, with the
  newline reading as a **disjunction**: the run's only newline is its
  last byte, **or** the run opens on `'e'`.  The newline half is still
  false at `PBoth` (`pcont_both_no_nl_shape`), and it had to be, so the
  second arm is what carries `PBoth`: `pcont_both_head_e` (an admitted
  interleaving is nonempty — `pmerge_length` at `|sel| = 33` — and its
  first byte is one of the two diagnostics' `'e'`), spent by the new
  `pd_head_ne_panic` (sh's panic line opens on `'f'`; `101 ≠ 102`).  That
  is *cheaper* than the newline argument it replaces.
- **`pcont_pair_det` re-proved**, its two panic-vs-prompt cases no longer
  destructing the line shape.  `alt_seq_p_prefix_det`, `sessp_prefix_det`
  and `disc_p_disc` are **unchanged in statement** and green —
  `disc_p_disc` was never at risk, because it quantifies over `echo_only`
  inputs where every line is an `LEcho` one.
- **`pd_bad_head` grew its `PEcho 3` case** (head `'f'` = 102, still never
  `'g'`), and `demo_p_bad` no longer needs "no `LPipe` alternative
  panics": it passes the whole `if palt_panic … then pro_of … else []`
  tail as the lemma's `Z`, so it is now agnostic.
- **New transcript** `demo_p_panic` (+ `demo_p_panic_disc`): the pipeline
  line typed and echoed, sh's main-loop `fork1` panics, init reaps the
  shell and re-enters the prologue — `ps = [3;0;3;0]`, `cs = [3]`, the
  exact wire the old table refused.  `demo_p_panic_ne_forkc` shows it is
  **not** the runcmd child's panic (`alt_forkc`), which is the whole
  content of the hole the ruling closed.

**RULING 2 — the `PBoth` code: LANDED positional/binary, and the
computability goal is UNREACHABLE (reported, with timings and a proof).**

- `bnum : list bool -> nat` reads `sel` as a binary numeral with a
  **leading 1** (lsb first, so leading `false`s survive); `bdigits`/`bdec`
  decode by division on a fuel bounded by `bnum_gt_length`; `bdec_bnum`
  is the round trip.  `palt_code` is ten small tags (0..9: the echo four
  and the six constant pipeline alternatives) and then two progressions
  mod 16 — `PEcho k≥4` at `10 + 16*(k-4)`, `PBoth sel` at
  `11 + 16 * bnum sel`; `palt_of` divides.  `encode_nat`/`decode_nat` are
  gone from the file, and `cs : list nat` is untouched, so PIPE-STAGE
  reuses `EchoOut`'s `cs_auth`/`cs_lb` verbatim as ruled.
- **`palt_of_code` is NOT `vm_compute`-checkable at `|sel| = 33`, and no
  layout makes it so, because `nat` is unary.** Measured on the mirror,
  `bdec (bnum (replicate n true)) = replicate n true` by `vm_compute`:

  | `n` | 8 | 14 | 18 | 22 | 33 |
  |---|---|---|---|---|---|
  | time | 0.002 s | 0.012 s | 0.272 s | 14.5 s | killed at 4 min |

  Each four bits costs about ×50, so 33 extrapolates to hours of CPU, and
  the numeral alone wants ~275 GB of heap.  The obstacle is **proved**
  rather than timed: `palt_code_both_big : palt_ok (LPipe ws) (PBoth sel)
  -> 2 ^ 33 <= palt_code (PBoth sel)` (via `bnum_ge_pow2`).  It is not
  an artefact of this layout — an injective map out of the admitted
  interleavings *alone* needs values past `C(33,17) > 10^9`, which is
  already ~19 GB of unary `nat`.  The binary reading is still a real win
  over `encode_nat` (~`2^34` against ~`4^33`, a factor of `4×10^9`), and
  it is what is landed.
- So the two `PBoth` demos keep the **rewriting** proofs, as the ruling
  allows: `demo_p_both` is one lemma for every interleaving, proved by
  rewriting with `palt_of_code` and `sessp_one`, instantiated at
  `sel_LR`/`sel_RL`.  Every other demo's code is in 0..9 and computes.
  **This is what PIPE-STAGE and PIPE-2W will have to do too**: a `PBoth`
  round can be *reasoned* about but never *computed*, so no decision
  procedure, `Decision` instance or `bool_decide` witness may be put on
  the path of a `PBoth` round (`alts_ok_p`'s instance still exists and is
  still correct — it is simply unusable there).
- `merge` → **`pmerge`** throughout (function and its ten lemmas:
  `pmerge_length`, `pmerge_take`, `pmerge_take_lr`, `pmerge_prefix_take`,
  `pmerge_prefix`, `pmerge_nodollar`, `pmerge_no_dollar`, `pmerge_head`,
  `pmerge_sel_LR`, `pmerge_sel_RL`), so stdpp's map `merge` is no longer
  shadowed and PIPE-2W can import both.  Design §4.3's law is now
  `pmerge_prefix`.

**REFUTED ON THE WAY (new).** The ruling's phrase "`palt_of_code` must be
`vm_compute`-checkable at `|sel| = 33` (a 34-bit number)" reads a 34-bit
*number* as cheap; in Rocq's `nat` a 34-bit number is 1.7×10^10
constructors. If a computable resolution is ever wanted, the fix is not a
better code but a different carrier — `cs : list palt`, or `cs : list N`
— and that is a PIPE-STAGE decision, not a PIPE-MODEL one.

**NOTHING ELSE MOVED.** No landed `.v` file edited; `iris/_CoqProject`
carries the one new row; nothing imports `PipeDisc`, so the three audits'
cones are untouched.

### PIPE-DEC (2026-09-18) — `disc_p` IS DECIDABLE, and the pipe model needs NO canonicalisation of a state

Branch `app-pipe/pipe-dec`, commit `aa4491300`.  Whole tree GREEN on the
lane's mirror (`ec2-lane.sh dec build`, **RC=0**, zero `Error`); every one
of the 1598 `_CoqProject` rows has its `.vo`.  `PipeDisc.v` **unedited**;
no landed statement anywhere moved; nothing is `Admitted`; every proof
carries a minimal `Proof using`.  `Print Assumptions` on all eight
deliverables — `elem_of_choose`, `elem_of_palt_cands`,
`palt_cands_both_LR`, `alts_cands_p_alts_ok`, `alts_ok_p_cs_canon`,
`sessp_pro_len`, `disc_seg_p'_dec`, `disc_p_dec` — prints exactly *Closed
under the global context*.  The three audits cannot move: nothing imports
`PipeDiscDec`, and `AUDIT_FLAGS` reads only the `-R`/`-arg` lines of
`iris/_CoqProject`, not its file rows.

**WHAT LANDED.**  One new file, `iris/PipeDiscDec.v` (435 lines), in
`iris/_CoqProject` right after `PipeDisc.v`, ending in `Global Instance
disc_p_dec h : Decision (disc_p h)`.  **BLOCKER 1's pipe twin is closed**:
lane PIPE-STAGE can delete its `Context {Hdp : forall h, Decision
(disc_p h)}` and put the ledger's counter at `decide (disc_p h)`.

- §1 `choose n k` (every selector of length `n` with exactly `k` `true`s,
  by recursion on the first entry) and `elem_of_choose : sel ∈ choose n k
  <-> length sel = n /\ count_true sel = k`.
- §2 `palt_fix_cands` / `palt_cands` (the CANONICAL codes one line shape
  admits) with `palt_cands_alt : palt_ok l a -> palt_code a ∈ palt_cands
  l`, the brief's two-way `elem_of_palt_cands : c ∈ palt_cands l <->
  palt_ok l (palt_of c) /\ c = palt_code (palt_of c)`, `palt_cands_canon`,
  and the anti-vacuity witness `palt_cands_both_LR`.
- §3 `alts_cands_p` / `elem_of_alts_cands_p` / `alts_cands_p_alts_ok`
  (`alts_ok_p` is a `Forall2` over `plines_of`, so the enumerator is
  per-line and the length falls out).
- §4 `pcode_canon` / `cs_canon_p` and the canon chain: `cs_canon_p_at`,
  `pro_idx_p_canon`, `alt_cont_p_canon`, `alt_seq_p_canon`, `sessp_canon`,
  `alts_ok_p_cs_canon`, `disc_pt_all_p_canon`.
- §5 `alt_seq_p_pro_len`, `sessp_pro_len` — the prologue length bound at
  `pro_idx_p`.
- §6 `disc_seg_p'_dec` (`Defined`), then `disc_p_dec` (`Qed`).

**WHAT THE BRIEF/DESIGN GOT WRONG — and it is a SIMPLIFICATION, not a
cost.**

- **There is no boot-state canonicalisation to do, so `FileDiscDec`'s
  §§6–7 do NOT port and `disc_seg_p'_ex_dec` is not a statement.**  The
  brief asked for "the split/infix laws (`alt_seq_p_split`,
  `sessp_infix_blk`, …) and the canonicalisation `disc_seg_p'_canon`,
  then `disc_seg_p'_ex_dec`, then `disc_p_dec`".  `FileDisc.disc_f` needs
  all of that only because it is `exists s, fst_ok s /\ disc_seg_f' s
  seg` — the f-state is threaded across rounds and cycles, so the witness
  has to be pulled back onto the wire (`infixed`/`substrings`/`scands`).
  **A pipe dies with its era** (design §0, limit 3), so `sessp` threads
  NO state, `disc_seg_p'` quantifies over `ps` and `cs` alone, and the
  decision is of `disc_seg_p'` ITSELF.  `infixed`, `substrings`, `scands`,
  `alt_seq_p_split`, `sessp_infix_blk`, `disc_seg_f'_canon`'s twin and
  `fcont_ok`/`fst_ok`'s decidability (FileDiscDec §§0–1, 6–7) are all
  UNNEEDED: the lane's chain is `elem_of_choose` → `palt_cands` →
  `alts_cands_p` → `cs_canon_p` → `sessp_pro_len` → `disc_seg_p'_dec` →
  `disc_p_dec`, and the file is 435 lines against FileDiscDec's 643.
- **`PipeDisc`'s parenthetical at `disc_seg_p'` is superseded** ("`[disc_seg_p']`
  is NOT claimed decidable: the search over the resolutions `EchoDisc` can
  run needs a bound on `sel`, and no consumer asks for it").  The bound on
  `sel` is `palt_ok`'s own two conditions — `length sel = |dg_execL| +
  |dg_execR|` and `count_true sel = |dg_execL|` — and `choose` is the
  enumerator for it.  The note is worth AMENDING in `PipeDisc.v` when
  some later lane edits that file (this lane did not, per its bar); the
  new file's header carries the correction.
- **FILE-DEC's two portability findings repeat exactly.**
  `EchoDisc.bounded_lists` does not port (codes are not an initial
  segment of ℕ: `palt_code (PBoth sel) = 11 + 16 * bnum sel`), and
  `pro_cands`/`pro_canon` port VERBATIM — `pro_canon` never mentions
  `cs`, so only `EchoDisc.alt_seq_pro_len`'s LENGTH bound had to be
  restated, and PIPE-MODEL-2's ruling makes that ONE panic case rather
  than FileDisc's three: `palt_panic a = true -> a = PEcho 3` at BOTH
  line shapes (`palt_ok_pipe_panic`, `palt_panic_3`), so
  `alt_seq_p_pro_len` is `EchoDisc`'s proof with `pro_idx_p_Sp/_Sn` in
  place of `cs !!! q = 3`.
- **`palt_ok l (palt_of c) -> c = palt_code (palt_of c)` is REFUTED as a
  route, for the same reason as FileDisc's.**  `palt_of` accepts any `n`
  with `n mod 16 = 11` as a `PBoth`, while `palt_code (PBoth sel) = 11 +
  16 * bnum sel` and `bnum` is not onto (its image is
  `[2^|sel|, 2^(|sel|+1))` only), so nothing forces a code admitted by
  `alts_ok_p` to be its own alternative's code.  Taken instead:
  `cs_canon_p cs := (palt_code ∘ palt_of) <$> cs`, sound because EVERY
  consumer of `cs` reads it only through `palt_at = palt_of ∘ (!!!)` —
  checked one by one (`pro_idx_p`, `alt_cont_p`, `alt_seq_p`, `sessp`,
  `pro_ok_p`, `disc_pt_p`, `alts_ok_p`).  The out-of-range `!!!` reading
  is `0` and `palt_code (palt_of 0) = 0`, so the canonical map fixes it
  too (`pcode_canon_0`, `pdd_lookup_total_fmap`).
- **NO closure law of `PipeDisc` was missing.**  Unlike FILE-DEC (which
  had to land `disc_f`'s five closure laws in `FileOutPure`), everything
  this lane needed was already in `PipeDisc.v`: `pro_idx_p_S/_Sp/_Sn/
  _mono`, `alt_seq_p_S`, `alt_blk_p_length`, `sessp_length`,
  `sessp_ps_ext`, `disc_seg_p'_intro`, `disc_pt_all_p_dec`,
  `palt_of_code`, `palt_of_lt4`, `palt_code_echo_lt4`, `sel_LR_ok`.
  **PIPE-STAGE owes nothing to this file beyond importing it.**

**ANTI-VACUITY, at the branch that cannot be computed.**  A `Decision`
instance cannot be vacuous, but its ENUMERATOR can be empty and the
procedure would then answer "no" at a disciplined history — which is
caught not by a compile error but by `palt_cands_alt`'s completeness
half, and, concretely, by `palt_cands_both_LR : palt_code (PBoth sel_LR)
∈ palt_cands (LPipe ws)`, proved through `sel_LR_ok` and never by
evaluating `choose` or a `PBoth` code (`palt_code_both_big` says neither
can be evaluated).  **PIPE-MODEL-2's warning stands and is now sharp:**
`disc_seg_p'_dec` is a THEOREM and not a program — at any segment holding
one complete `LPipe` line its `cs` search ranges over `C(33,17) > 10^9`
selectors, so no `vm_compute`, `bool_decide` witness or `Defined`
evaluation may be put on the path of a `PBoth` round.  That is why
`disc_p_dec` is **`Qed`** (FILE-DEC's finding: a transparent instance
lets ssreflect's `rewrite /…_led` iota-reduce `if decide (disc_p h) then
0 else 1` at a literal history, and the ledger's `rewrite decide_True`
then stops matching) and why the PBoth demos in `PipeDisc` §8 are
rewriting proofs.

**ONE SOURCE-LEVEL TRAP, worth a durable note.**  A quotation in a Rocq
comment must not span a `*)`: `iris/_CoqProject` turns
`comment-terminator-in-string` into an ERROR, and a two-line comment
reading `… exactly "Closed under the    *)` / `(*  global context" …`
fails to compile with "Not interpreting `*)` as the end of current
non-terminated comment".  `tools/comment_quote_check.py` finds it without
a build — run it on any new file whose header quotes something.

**NOTHING ELSE MOVED.**  No landed `.v` file edited; `iris/_CoqProject`
carries the one new row; nothing imports `PipeDiscDec`, so the three
audits' cones are untouched.

### PIPE-REG (2026-09-18)

**LANDED** (branch `app-pipe/pipe-reg`, commits `119ef0f69`, `bc8ba82dc`,
`69c28f329`, `f708512a0`): whole `iris` tree green on the EC2 mirror; no
`Admitted`; every new result carries `Proof using`. `make audit-echo-only`
re-run and UNMOVED — exactly the FOURTEEN of `durable-notes.md`'s
baseline, textually — and that is the audit that matters here: its cone is
the one that walks the `Uk*`/`USh*`/`UInit*`/`UEcho*` program tier, where
every file this lane touched lives. `audit-tree-only` and `audit-only`
were started against the quiescent tree and never returned: the lane's
REMOTE CLONE was reclaimed underneath them (`/shared/xv6iris-pipe-reg` is
gone from the mirror, along with most other lanes' clones — 13 GB
freed), which happened AFTER the final whole-tree build came back `RC=0`,
so the green result stands. They cannot move: every new result is a theorem, no `Axiom`/`Admitted` was added, and
`urun_nopipe`'s definition became strictly WEAKER. **The coordinator
should still see both green on the merge gate.**

TWO TRAPS THIS COST, for whoever runs an audit next:
- **Run it against a QUIESCENT tree.** An audit with a `make` in flight
  fails `Compiled library … makes inconsistent assumptions over library …`
  — mid-build staleness, not a finding.
- **Never run two audits of the same target in one clone.** The second
  one's `coqc` raced the first and the pair died with `System error: "No
  space left on device"` on a filesystem with 23 GB free.

- NEW `iris/PipeReg.v` — `pipe_reg γp := □ (∀ w, pipe_cpay (pn_queue γp) w
  emp)`, `pipe_row_reg`, both persistence instances, `pipe_reg_of_taint` /
  `pipe_row_reg_of_taint` / `pipe_row_reg_nopipe`, `fileclose_cpay_of_reg`
  and `fileclose_cpays_of_regs` (kexit's whole `[∗ list]` row, one instance
  of each row's `□` — the second "Open, recorded" item of
  `completed/pipe-queue.md` closed), plus the two big-op moves
  (`fd_rows_insert`, `fd_rows_lookup`) at an arbitrary row predicate.
- `UexecSG.v` — THREE NEW CLASS FIELDS `srow_reg : fdstate -> iProp Σ`,
  `srow_reg_persistent`, `srow_reg_nopipe` (see "what the design got
  wrong", below).
- `UkRun.v` — `urun_nopipe fdv := ([∗ list] st ∈ fdv, srow_reg st) ∨ □
  riscv_kill_cred`; `urun_nopipe_intro/_closed/_taint/_quiet/_insert/_dup/
  _copy/_step` at byte-identical statements, `_step` running
  `UsysMemOk.usys_fd_ok_nopipe`'s own case split with a resource instead of
  a Prop; NEW `urun_nopipe_regs`, `urun_nopipe_insert_reg`,
  `urun_nopipe_regs_insert/_lookup/_lookup_total`, `srow_regs_nopipe`.
  `urun_rows_*` and `udep_exit_run` unchanged statements. `udep`'s exit law
  now takes the RESOURCE (`udep_exit_regs`); `udep_exit_dep` and
  `udep_exit_taint` did not move, the first a corollary.
- `UexecExecInst.v` — NEW `xv6_sbundle_exit_regs`;
  `xv6_sbundle_exit_nopipe` kept as its corollary at a byte-identical
  statement; `uexecSG_xv6` answers the three fields with `pipe_row_reg`;
  NEW `srow_reg_of_pipe_reg`, `srow_reg_of_taint` (the row's readings at
  the one altitude where `srow_reg` is not abstract).
  `UexecExecMint.v` — `udep_gen` / `udep_free` re-proved.
- `UkRunSys.wp_uk_ecall_pipe` — the `□ riscv_kill_cred` premise is GONE.
- `UkReadPipe.wp_uk_pipe_read_end` — the same, at the instance; the
  header comment rewritten.
- BEYOND THE BRIEF, because SH-PIPE cannot round without it:
  `PipeReg.pipe_cpay_of_reg_true` / `fileclose_cpay_of_reg_true` and
  `UexecExecInst.xv6_sbundle_close_of_reg` — CLOSE(21)'s row off the
  registry at the POINT family's payload (`True`), since the close link's
  fupd places `emp` and so places anything `emp` entails. No arm of
  `UkRun.udepw_cl` moves: its right arm is `udepw … 21`, which takes an
  explicit bundle, so this is what a pipe-holding program supplies there.
- BAR MET: every one of the ~25 `urun_nopipe` sites the brief lists
  (UkFork, UInitSh, UShEchoPay, UexecCond, UShEcho, UShKernel,
  UEchoKernel, UCatKernel, UShCat, UEchoFile, UInitBoot, UInitTreeExec,
  UEchoOut, USyncKernel, UInitKernel) compiles TEXTUALLY UNCHANGED.

**REFUTED, at the statement.**

1. **The run cannot be handed back OWED** (design §2's primary shape,
   `pipe_qfrag ∗ (pipe_reg γp -∗ urun …)`), and the reason is not the one
   the STOP RULE guessed. `UkRun.urun_close_upd` takes `urun_rows N fdv'`
   *as an input* and produces the `ukcq` whose continuation *hands the
   caller the `urun`* — so a debt discharged by the caller's continuation
   is circular: the row is needed strictly before the run the payer
   receives exists. (The secondary obstacle the STOP RULE did name is also
   real: `γp` is bound inside the post's existential and is not in scope at
   the post's `urun` position.) The FALLBACK landed.
2. **The registrar cannot be fragment-shaped at `UkRunSys`'s altitude, and
   cannot give the post back at any altitude.** `wp_uk_ecall_pipe` is
   stated over the deposit class and cannot open row 4's post, so it cannot
   reach `pipe_qfrag`; and a registrar that returned `spost_at` unchanged is
   unsatisfiable, because registering CONSUMES the fragment — a
   registration is a `□` and one fragment buys exactly one payment
   (`PipeReg.pipe_cpay_of_frag`, landed as the positive half of the vacuity
   exhibit). So the registrar takes the post and the leaf hands on the
   caller's own residue: a new parameter `Rp` in place of `spost_at` in the
   post. At `UkReadPipe` the same premise is fragment-shaped
   (`∀ γp, pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗ Rp γp`) and
   `Rp γp` replaces the fragment in that post — lane PIPE-PROTO's
   `pipe_proto_alloc` is the instance of record.
3. **`pipe_reg` is NOT `Timeless`**, as the brief suspected: `pipe_cpay`'s
   left arm is a fupd-producing wand and no `□` makes that timeless. No
   instance was declared and none is needed — no consumer of `urun_nopipe`
   strips a `▷` off it (every site in the tree was checked; the only
   destructors live in `UkRun.v` itself).
4. **The vacuity check is mechanisable after all**, one step in from where
   the design put it: `PipeReg.pipe_reg_not_free` shows a close link at the
   trivial payload cannot come from nothing, because firing it moves the
   pipe's AUTHORITY, so a conjured link beside the matching fragment
   refutes `pipe_queue_agree` (`pst_close true pst0 <> pst0`). What is
   *not* expressible is "`⊢ pipe_reg γp` is not derivable" itself — a
   meta-level claim — so the refutation is stated at the one step such a
   derivation would have to take.

**WHAT THE DESIGN GOT WRONG.**

*The registry cannot be named in `UkRun.v`, and this is the finding the
next waves have to build on.* Design §2 writes `urun_nopipe fdv := [∗
list] st ∈ fdv, pipe_row_reg st` in `UkRun.v`. `pipe_row_reg` names the
pipe's queue camera (`pipeG`), and `UkRun.v` binds no whole-system ghost
bundle **by design** ("this file binds no whole-system bundle" — its own
header). Giving it `pipeG` adds an implicit instance argument to `urun`
itself, hence a `Context` line to EACH OF THE ~70 U-tier files that state a
run (they bind `riscvGS`/`ufdG`/`ctokG`/`SG`/`PS` and no bundle) — and
adding it to `ufdG` or `ctokG` instead creates two instance paths for
`pipeG` in the ~95 files that also bind `xv6G`, which wedges rather than
fails (`durable-notes.md`, 2026-09-12). Both were measured and rejected.

The registry therefore enters through `uexecSG` — the U tier's ONE instance
record, which every such file already binds and of which there is exactly
one instance (`UexecExecInst.uexecSG_xv6`) — as the field `srow_reg` with
the two laws the engine's steps actually use (persistence; a non-pipe row
registers itself). Cost: three lines in `UexecSG.v`, three in the instance,
zero at any site.

*The taint arm had to stay* (`urun_nopipe := regs ∨ taint`, not `regs`).
`urun_nopipe_taint`'s and `urun_rows_taint`'s statements name
`riscv_kill_cred`, and the class the left arm is stated at has no `riscvGS`
parameter, so no class law can produce a row from the credential; and the
generic tier's supply (`UexecExecMint.udep_gen`, `UexecCond.
cond_entry_slot`) holds the credential and has no pipe names to build a
registry from. Adding `{sg_riscv : riscvGS Σ}` to `uexecSG` would remove the
arm at the price of a second class-arity change across 75 `Context` lines;
it is a cleanup lane's call, not this one's. **A registered program never
touches the arm**, so nothing about §2's claim is weakened: the registry is
what a pipe-holding verified program carries.

*Two smaller corrections.* (a) `urun_nopipe_taint` and `urun_nopipe_step`
already existed on `main` — the brief lists them as NEW. (b) The one site
that DESTRUCTS `urun_nopipe` and is not in the brief's list is
`UkRun.udep_exit_run` (`UkRun.v`), which is local and was restated.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**

PIPE-PROTO: `pipe_reg_of_inv` is now exactly `pipe_inv pn γp L -∗ □ (∀ w,
pipe_cpay (pn_queue γp) w emp)` — one close link per end, built inside the
invariant at `⊤` with `pipe_clink_of_frag`, `pst_close` touching only a
flag so (P1)/(P2)/(P3) all survive. Its consumer is
`UkReadPipe.wp_uk_pipe_read_end`'s registrar premise
`∀ γp, pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗ pipe_reg γp ∗ Rp γp`, so
`pipe_proto_alloc` should be stated to produce `pipe_reg γp` BESIDE the
invariant handle and the write token — i.e. `pipe_qfrag (pn_queue γp) pst0
={⊤}=∗ ∃ pn, pipe_inv pn γp L ∗ wtok γw ∗ pipe_reg γp` — and sh's PIPE arm
then instantiates `Rp γp := ∃ pn, pipe_inv pn γp L ∗ wtok γw`.

*Owed, and NOT this lane's* (reported for SH-PIPE / PIPE-STD, and the
campaign WILL hit it): CLOSE(21)'s row is still `UkRun.udepw_cl`, whose
left arm is the PURE `ukey_nonpipe` and whose right arm is a full `udepw …
21`. A program closing a pipe descriptor — sh does it six times per
round, two of them pipe ends — therefore still owes an explicit deposit at
21, which at the free instance is payable only from the taint. The
registry CAN pay it, but **only at the trivial payload**: row 21 is
`fileclose_cpay st (cl_P f)` and `pipe_reg γp` is `□ (∀ w, pipe_cpay …
w emp)`, so the twin of `xv6_sbundle_close_nonpipe` exists exactly for a
family whose `cl_P` is `emp` — which is a choice made at the DEPOSIT, not
at `udepw_cl_mint`, and that is why a third arm on `udepw_cl` is not a
mechanical addition. The honest shapes are either a `cl_P = emp`-guarded
arm on `udepw_cl`, or `pipe_reg` generalised to `□ (∀ w Φ, Φ -∗ pipe_cpay
… w Φ)` (which is NOT derivable from the invariant: the close link's fupd
would have to place a caller-chosen `Φ`, and the invariant only knows how
to place `emp`). SH-PIPE should take the close deposits as parameters, as
its brief already says, and the ruling belongs with whoever states sh's
round.

### SH-PARSE-PIPE-2 (2026-09-18) — the RIGHT command needs NO walk (a suffix of a `ustr` IS a `ustr`), `parsepipe` TURNS, and the left loop is uniform

Branch `app-pipe/sh-parse-pipe`, FOUR more files and five commits
(`ef4c32dd4`, `a639803e3`, `61b8673df`, `8da3cc91c`, and this note) on top
of part 1.  Whole tree green (`build`, RC=0); still not one landed
statement touched; no `Admitted`; every result carries `Proof using`; all
NINE of the lane's files are LEAVES (`grep -l UkShPipe iris/*.v` returns
only themselves), so no audited cone contains any of them.  **The audits
were run and are as expected: `audit-echo-only` FOURTEEN, `audit-only`
THIRTEEN.  `audit-tree-only` is THIRTEEN, not the ten this worklist's
rules claim** — upstream's tree-claim second app moved it (spec-cleanup's
"audit 13") and this lane's files are not in its cone; the rules line
should be corrected.

**WHAT LANDED.**

- `iris/UkShPipeRight.v` — **`wp_kshp_parsepipe_right`: the pipe line's
  RIGHT command needs NO new walk at all.**  `ustr_split` (with
  `ubytesq_app`, which is `UserHeap.ubytes_app` at an arbitrary `dfrac`),
  `ushq_nosym_shift`, `ushq_toks_right`, `ushq_shift` /
  `ushp_exec_at_rebase`.
- `iris/UkShPipePr.v` — `wp_kshp_parseredirs_miss`: the zero-turn walk at
  the WEAKEST premise (the peek MISS), because the landed one's premise is
  "the byte is not a symbol" and the `|` falsifies it.
- `iris/UkShPipeEx2.v` — **`wp_kshp_pex_loop_bar`**: the argument loop,
  UNIFORM (no tail split), two premises and one allocator capability
  lighter than the redirect loop.
- `iris/UkShPipeCm.v` — **`wp_kshp_parsepipe_bar`: the TURN**, the
  thirteen instructions 0x6c2..0x6e0 nobody had walked, with `gettoken`
  and THE RECURSION discharged and two call premises (`ushq_pex_left`,
  `ushq_pipecmd_call`) in SH-REDIR's `ush_open_call` style;
  `ushq_pex_left_nosym` witnesses that the first premise's SHAPE is
  inhabited.

**THE FINDING OF THE PART, and it replaced a 1,600-line copy with forty
lines: A SUFFIX OF A `ustr` IS A `ustr`.**  `parsepipe`'s recursive call
runs entirely above the `|`, and a `ustr`'s suffix is a `ustr` — its bytes
are non-NUL because the whole string's are, and the terminator it needs is
the whole string's own.  So the recursion is handed the line's own suffix
at base `s0 + (p + 2)`, where the line IS symbol-free
(`ushq_pipe_nosym_from`), and it is `UkShParseCmd.wp_kshp_parsepipe` — the
LANDED symbol-free walk — applied ONCE.  Three small things make it fit,
and each is a finding in its own right:

1. `ustr_split` takes the length equation as a premise (`len = k + n`) so
   `intros ->` puts the goal in the split form: NO length is ever
   rewritten under an iProp.  The prefix comes out as bare bytes (it has
   no terminator), the suffix as a string, and the closing wand carries
   the two pure facts the pieces cannot reconstruct.
2. `ushp_slot` stores an ABSOLUTE address, so the node the recursive call
   builds at the shifted base IS the node of the SHIFTED token list at the
   line's base (`ushp_exec_at_rebase`).  The resource does not move, only
   its reading — which is what lets `UkShPipeSeam.ush_cmd_of_ushp_pipe`
   take both sides at one `s0`, with the right list coming out as
   `[(S (S gp), ge)]`.
3. The right command is ONE token of the suffix, measured by the same two
   scans and assembled with `UkShParseSym`'s own `ushs_toks` constructors,
   so `ushp_tokens` comes out of `ushs_toks_tokens` and not a second
   induction.

**THE TURN, AND WHAT IS STILL A PREMISE.**  Of its three calls, 0x6ca
`gettoken` is discharged by part 1's `wp_kshp_gettoken_syms` (it answers
124 and leaves the cursor at `S (S gp)`) and 0x6d2 `parsepipe` by
`wp_kshp_parsepipe_right`; the guard itself turns on part 1's
`ushq_peek_pipe_hit_pipe`.  The two premises are the LEFT `parseexec` and
`pipecmd`.  Both premises take the RETURN PC as a parameter with the
caller supplying `ret_pc (m ra) = rpc` — the trick that keeps a pc out of
a rewrite under an iProp, and worth copying.

**A THIRD "ONE LINE OF N", and the rule it suggests.**  `parseexec`'s loop
calls `parseredirs` after EVERY argument, so its last call sits ON the
`|`; `UkShRedirPr.wp_kshp_parseredirs_ns` cannot serve it because its
premise is "no symbol at the cursor", spent in ONE line of its 584.  Three
landed walks have now been re-stated by this campaign for exactly this
reason (`gettoken`'s dispatch, `parseredirs`' zero turn, `parseexec`'s
loop).  **The rule: a walk's premise should be the WEAKEST fact its proof
spends, and for a peek that fact is `ushp_peek_res … = 0/1`, never a
property of the whole line.**  `ushp_peek_res_miss` and
`UkShRedirLex.ushp_peek_res_hit` are the pair to state everything at.

**WHAT IS LEFT OF THE LEFT SIDE — one mechanical copy, no unknowns.**
`ushq_pex_left` is instantiated by `wp_kshp_parseexec_bar`, which is
`UkShRedirPex.wp_kshp_parseexec_gt` (1,403 lines) with: `ushs_redir` →
`ushq_pipe`; its two `parseredirs` calls → `wp_kshp_parseredirs_miss`; its
loop → `wp_kshp_pex_loop_bar` (landed); and its post's answer the EXEC
node `p` rather than the REDIR node `t` (the only part that is more than a
name change, because the landed walk relays a node the pipe line does not
build).  Everything it calls is landed.

**ITEM (3), pipecmd's catalog row: STOPPED, and here is exactly what it
needs.**  `make gen-ucode` is NOT a dump rule — `tools/gen_ucode.py` reads
`user-rocq/<Module>{Instrs,Data,Syms}.v` (the TRACKED dump) plus
`tools/ucode_shp.txt`, and never opens `xv6-riscv/`; `tools/dump_elf.py`
is the tool that reads the ELF, and `make dump`/`dump-force` are the rules
that call it.  So the mirror's old `xv6-riscv` clone is IRRELEVANT to it.
What blocks it is the other half of its own header: **it shells out to
`coqc` and that `coqc` needs a BUILT `iris/`** (the probe imports
`WpDecodeBridge`), and this lane's local worktree has no `.vo` at all
(`ls iris/*.vo` = 0) — the build lives on the mirror.  So the row can only
be regenerated where a built tree is, i.e. on the mirror, which the lane's
instructions forbid.  To land it, someone needs: (a) `skipfunc pipecmd` →
`func pipecmd` in `tools/ucode_shp.txt`; (b) `make gen-ucode` in a tree
with a built `iris/`; (c) the regenerated `iris/UCodeShP.v` COMMITTED
(`make check-ucode`'s second half is `git diff --exit-code`); (d) the
ELEVEN `destruct shp_syms_pins as (…)` patterns in
`iris/UkShParse.v:857-877` each gaining one `_` (proof text only, no
statement moves), because the pins tuple gains a conjunct; (e) a rebuild
of the whole parser cone.  Then `pipecmd`'s 48 instructions are
`UkShRedirCmd.wp_kshp_redircmd`'s walk with five field stores instead of
seven, and `ushq_pipecmd_call` is its conclusion.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  `wp_kshp_parseexec_bar` (the
copy above) — it discharges `ushq_pex_left` and leaves `pipecmd` as the
turn's only premise.  After that the parser theorem at the pipe shape is
`parseline`/`parsecmd` at the same shape (the landed `_gt` versions with
the same substitutions) plus part 1's `wp_kshp_nulterminate_pipe` and
`ush_cmd_of_ushp_pipe`, which are landed.  The line-disjunct's FOURTH arm
stays where SH-LEX-REDIR §4 put it: coupled with the pipe child walk, so
it belongs to SH-PIPE-ROUND and not here.

### PIPE-PROTO (2026-09-18) — the protocol lands whole, and a cursor's exactness turns out to be an EXCLUSIVE RESOURCE (which retires (P2))

Branch `app-pipe/pipe-proto`, commits `3e52c3f23`, `72db8342f`.  ONE new
file (`iris/PipeProto.v`) plus one line of `iris/_CoqProject`.
**No landed statement moved** — `PipeQueue`/`UkReadPipe`/`UkWritePipe` were
not touched at all.  Whole-tree `ec2-lane.sh proto build` RC=0 (twice, the
second after the last edit); no `Admitted`; `Proof using` on every result
inside the section (the three top-level ones — `subG_pipeProtoΣ`,
`pnames_eq_dec`, `pst_eof_dec` — carry plain `Proof.`, the tree's own
convention for exactly those forms, cf. `subG_echoOutΣ`/`pipe_names_eq_dec`).
`Print Assumptions` on `pipe_proto_alloc`, `pipe_reg_of_inv`,
`pipe_wpay_of_inv`, `pipe_rpay_of_inv`, `pipe_round_ran`,
`pipe_round_reading` and `pipe_proto_test`: **"Closed under the global
context", all seven** — not even the tree's standing primitives.  The
audits cannot move: NOTHING in the tree `Require`s `PipeProto.v`.

**WHAT LANDED** (`iris/PipeProto.v`, right after `PipeReg.v`)

- `pipeProtoG`/`pipeProtoΣ`/`subG_pipeProtoΣ` — four cameras: the history's
  `mono_listR (leibnizO (bv 8))`, the EOF one-shot
  `csumR (exclR unitO) (agreeR (leibnizO (list (bv 8))))` (`KptGhost.kptR`'s
  shape), `ghost_varG Σ nat` for the two cursors, `exclR unitO` for the two
  side tokens.  `pnames` (six gnames), `pipeN`, `pst_eof_dec`.
- The pieces: `pws_auth`/`pws_lb` (+ `pws_auth_lb`, `pws_lb_prefix`,
  `pws_auth_grow`), `eof_pending`/`eof_shot` (+ `eof_pending_shot`,
  `eof_shot_agree`, `eof_shoot`), `wcur`/`rcur` (+ `_agree`, `_move`) with
  `wtok pn := wcur pn 0` and `rtok pn := rcur pn 0`, `side_L`/`side_R`
  (+ `_excl`), and every persistence/timelessness instance.
- **`pipe_body`, verbatim:**

        Definition pipe_body (pn : pnames) (γp : pipe_names) (L : list (bv 8))
            : iProp Σ :=
          (∃ s : pipe_st,
             pipe_qfrag (pn_queue γp) s
             ∗ pws_auth pn (ps_ws s)
             ∗ wcur pn (length (ps_ws s))
             ∗ rcur pn (ps_rp s)
             (* (P1) only the line ever goes in *)
             ∗ ⌜ps_ws s `prefix_of` L⌝
             (* (P3) after end-of-file the contents are frozen *)
             ∗ (eof_pending pn
                ∨ ∃ w : list (bv 8),
                    eof_shot pn w ∗ ⌜w = ps_ws s /\ ps_wo s = false⌝))%I.

  `pipe_inv pn γp L := inv pipeN (pipe_body pn γp L)`, with
  `pipe_body_timeless` and `pipe_inv_persistent`; the three properties as
  readings against the KERNEL's authority (the shape a link reads them at):
  `pipe_body_P1`, `pipe_body_P2` (derived, see below), `pipe_body_P3`.
- `pipe_clink_of_inv` (at any mask containing `↑pipeN`) and
  **`pipe_reg_of_inv : pipe_inv pn γp L -∗ pipe_reg γp`** — PIPE-REG's
  hand-off item, closed exactly as it predicted (`pst_close` touches only a
  flag, so (P1), both cursors and (P3) all survive; (P3) because the flag it
  clears can only make `ps_wo` falser).
- `pipe_inv_frag_excl : pipe_inv pn γp L -∗ pipe_qfrag (pn_queue γp) s ={⊤}=∗ False`
  — the exhibit that makes PIPE-REG's "registering CONSUMES the fragment"
  honest: once the protocol owns it, nobody else can hold it.
- **`pipe_proto_alloc`, verbatim:**

        Lemma pipe_proto_alloc (γp : pipe_names) (L : list (bv 8)) :
          pipe_qfrag (pn_queue γp) pst0 ={⊤}=∗
          ∃ pn : pnames,
            pipe_inv pn γp L ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn
            ∗ pipe_reg γp.

  i.e. `UkReadPipe.wp_uk_pipe_read_end`'s registrar premise at
  `Rp γp := ∃ pn, pipe_inv pn γp L ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn`.
- **THE WRITER'S BUILDER.**  `pipe_wQ pn L c j := wcur pn (c + j) ∗ pws_lb pn (take (c + j) L)`
  and `pipe_wQe pn L c j _ := pipe_wQ pn L c j` (an observation SPENDS its
  node, so handing the cursor back is the only thing it can do — which is
  design §3's "records nothing").  `pipe_wchain_of_inv` (the chain at cursor
  `c`, node `j`, count `cnt`, by induction on `cnt`), `pipe_wQ_line` ("the
  line is in" at `c + n = length L`: `wcur pn (length L) ∗ pws_lb pn L`),
  and **verbatim:**

        Lemma pipe_wpay_of_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8))
            (M : gmap Z (bv 8)) (ua : mword 64) (c n : nat) :
          (c + n <= length L)%nat ->
          (forall k : nat, (k < n)%nat ->
             M !! uint (add_vec_int ua (Z.of_nat k)) = Some (L !!! (c + k)%nat)) ->
          pipe_inv pn γp L -∗ wcur pn c -∗ pws_lb pn (take c L) -∗
          pipe_wpay (pn_queue γp) M ua (pipe_wQ pn L c) (pipe_wQe pn L c) n.

  plus `pws_lb_of_inv : pipe_inv pn γp L -∗ wcur pn c ={⊤}=∗ wcur pn c ∗ pws_lb pn (take c L)`
  and `pipe_wpay_of_inv_fupd` (the same payment for a caller that crossed
  `exec` with nothing but the handle and its permit — which is echo).
- **THE READER'S BUILDER.**  `pipe_rQ pn L c acc := rcur pn (c + length acc) ∗ ⌜acc = take (length acc) (drop c L)⌝`,
  `pipe_rQe pn L c acc s := pipe_rQ pn L c acc ∗ (⌜pst_eof s⌝ -∗ eof_shot pn (take (c + length acc) L))`,
  `pipe_rQe_eof`, `pipe_rchain_of_inv`, and **verbatim:**

        Lemma pipe_rpay_of_inv (pn : pnames) (γp : pipe_names) (L : list (bv 8))
            (c cap : nat) :
          pipe_inv pn γp L -∗ rcur pn c -∗
          pipe_rpay (pn_queue γp) (pipe_rQ pn L c) (pipe_rQe pn L c) cap.

  (no bound premise: a read takes what is there.)
- **SH'S ROUND.**  `pipe_body_ran`/`pipe_body_execL` and their
  invariant-level `pipe_round_ran`/`pipe_round_execL`; the symmetric payload
  `pipe_Qc pn PL PR := (side_L pn ∗ PL) ∨ (side_R pn ∗ PR)` with
  `pipe_Qc_two : pipe_Qc pn PL PR -∗ pipe_Qc pn PL PR -∗ (side_L pn ∗ PL) ∗ (side_R pn ∗ PR)`;
  `pipe_payL pn L := pws_lb pn L ∨ wtok pn`, `pipe_payR pn := ∃ w, eof_shot pn w`,
  and `pipe_round_reading`, which closes the round in ONE invariant access
  and answers `∃ w, eof_shot pn w ∗ ((pws_lb pn L ∗ ⌜w = L⌝) ∨ (wtok pn ∗ ⌜w = []⌝))`.
- **CONSUMER TEST, at the RESOURCE level** (the brief's stated alternative;
  a WP test would have to supply three programs' instruction streams,
  registers and heaps, and the two leaves it goes through are already landed
  and stated by PIPE-STD).  `pipe_wpost_cursor_line` and
  `pipe_rpost_img_line` show EVERY arm of the two posts hands the cursor
  back (and the read post's observation arm the EOF snapshot at `d = 0`);
  `pipe_reader_saw_line` derives `acc = L`; `pipe_proto_test` runs
  `pipe(2) → register → echo's whole-line payment + cat's read payment → the
  reading`, and its non-trivial conclusion is this lane's anti-vacuity
  exhibit.

**WHAT WAS REFUTED, at the statement (three, and the first is the one the
next waves have to build on)**

1. **A CURSOR'S EXACTNESS IS AN EXCLUSIVE RESOURCE, not an arithmetic
   consequence of a lower bound.**  Design §3's echo rows say the chain's
   `Q j` pins `ps_ws s = take j L` from "a `mono_list` lower bound of length
   `j` plus (P1)".  It does not: `mono_list_lb γws (take j L)` against the
   body's authority gives `take j L ⊑ ps_ws s`, (P1) gives `ps_ws s ⊑ L`, and
   together those give `ps_ws s = take k L` for SOME `k ≥ j` — and the node
   has to know WHICH byte of `L` it is appending, i.e. `k = j`.  Carrying
   `⌜length (ps_ws s) = j⌝` in `Q j` does not help either: it is a claim
   about a state the caller does not own, so nothing re-establishes it at the
   next node.  What actually pins it is that **echo is the only writer**, and
   the only way to say that in the logic is an exclusive permit that CARRIES
   the cursor.  So the protocol has a write cursor `wcur pn c` (half a
   `ghost_var nat`; the body holds the other half at `length (ps_ws s)`) and,
   for the same reason on the read side, `rcur pn c` at `ps_rp s`.  The
   permits are ALSO what make the chains compose across echo's four
   `kecho_w`s and cat's several `read`s, which is what the brief asked the
   builders for.
2. **(P2) AND `wtok_spent` ARE UNNECESSARY — not wrong, redundant.**  (P2)
   exists so sh can conclude "echo never wrote" from the start token; with
   the write cursor, `wtok pn` IS `wcur pn 0` and (P2) is one `ghost_var`
   agreement against the body's half (`pipe_body_P2`, landed at the design's
   exact statement).  So the body has one conjunct fewer and the protocol one
   camera fewer (no second one-shot for "the token went in"), and sh's
   `PExecL` reading is unchanged.
3. **(P3) CANNOT BE STATED AS A WAND, because the body must be TIMELESS.**
   Design §3 writes (P3) as `∀ w, ⌜γeof ↦ Some w⌝ -∗ ⌜w = ps_ws s ∧ ps_wo s = false⌝`.
   Every link's fupd runs at `⊤` with **no WP step** to strip a later off the
   opened invariant, so the body has to come out of `iInv .. as ">"` — and a
   wand is not `Timeless`.  (P3) is therefore the one-shot's two OWNED arms
   (`eof_pending pn ∨ ∃ w, eof_shot pn w ∗ ⌜…⌝`), which is timeless, and the
   design's wand is the derived `pipe_body_P3`.
4. **The reader's EOF observation cannot SET the snapshot unconditionally.**
   Design §3's cat row has two different observation nodes ("if `pst_eof s`
   … if merely empty with `ps_wo s = true` …"), but `pipe_olink` is a
   `∀ s` — ONE node that must be producible at EVERY state, including a
   non-empty one.  So `pipe_rQe acc s` carries the snapshot as a WAND from
   `⌜pst_eof s⌝`: where the state IS an end-of-file the node shoots the
   one-shot inside the invariant and the wand is trivial; elsewhere the wand
   is vacuous, which is the design's "records nothing" read correctly.
   `pipe_rpost_img`'s observation arm hands cat `ps_wo s = false` exactly
   when it delivered nothing (`d = 0`), which is the turn of cat's loop where
   `piperead` answered 0 — so the wand fires exactly there
   (`pipe_rpost_img_line`).

**WHAT THE DESIGN GOT WRONG, beyond the above**

- **§3 omits the READER's start permit.**  It lists only `wtok` among what
  the allocation hands out.  Without a read permit cat's chain cannot pin
  `ps_rp s` either, so `pipe_proto_alloc` hands out `rtok pn` as well, and
  `Rp γp` in `wp_uk_pipe_read_end`'s registrar premise is
  `∃ pn, pipe_inv pn γp L ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn`.
- **There is no landed NAME for `L`.**  The brief says "`L := wl_line (drop 1 ws)`
  is `EchoDisc`'s good continuation minus the prompt — find the landed name".
  There isn't one: `PipeDisc.pcont`'s `PRan` row spells it inline as
  `wl_line (drop 1 (pline_ws l)) ++ u_prompt` (`PipeDisc.v:1106`), and
  `EchoDisc.line_alts_of` likewise (`EchoDisc.v:994`).  The protocol takes
  `L` as a parameter and PIPE-STAGE / SH-PIPE-ROUND instantiate it; if the
  campaign wants a name, it belongs in `PipeDisc.v`, not here.
- **§3's "(P3) does not need a `ps_ro` premise: check" — CONFIRMED.**  PQ-FLAG
  refuted the read link's `⌜ps_ro s = true⌝` and (P3) does not want it:
  (P3) freezes `ps_ws`, only a write moves `ps_ws`, and the write link's
  `⌜ps_wo s = true⌝` is what refutes (P3)'s snapshot arm at a write
  (`pipe_wchain_of_inv`, the one place PQ-FLAG's premise is spent).  Both
  read-side steps (`pipe_rlink`, the observation) preserve (P3) with nothing
  to supply.  NO STOP RULE FIRED.
- **`pipe_reg` is reached ONLY through the taint-free left arm here.**
  `pipe_reg_of_inv` builds `pipe_cpay`'s LEFT arm (a real close link) at
  every `w`, so a registered pipeline program never touches the taint arm
  PIPE-REG had to keep — which is the claim §2 makes, now mechanised.

**THE ONE THING THE NEXT LANE NEEDS FIRST**

For **ECHO-PIPE**: `pipe_wpay_of_inv_fupd` is the payment to use, and its
only real obligation is the `M`-premise
`∀ k < n, M !! uint (add_vec_int ua (Z.of_nat k)) = Some (L !!! (c + k))` —
i.e. echo must read its own source run off the heap the call runs at, which
is the `∀ M pm sz, uheap -∗ uheap ∗ …` wrapper
`wp_uk_ecall_write_pipe_std` takes and which ECHO-PIPE owns (that wrapper is
one line around `pipe_wpay_of_inv_fupd`; it was deliberately NOT put here,
so that `PipeProto.v` stays below the `Uk*` tier and nothing in the U tier
has to import the protocol).  Echo's entry `Pay` is
`pipe_inv pn γp L ∗ wcur pn c` (NOT a `mono_list` lower bound: the permit is
what it needs), and its exit payload is `pws_lb pn L` at `c + n = length L`
via `pipe_wQ_line`, or `wtok pn` back if its exec failed.

For **CAT-PIPE**: `pipe_rpay_of_inv` needs only `rcur pn c`; cat's entry
`Pay` is `pipe_inv pn γp L ∗ rtok pn` and its exit payload is
`∃ w, eof_shot pn w` — the snapshot comes out of `pipe_rpost_img_line`'s
observation arm at `d = 0` (which is where the read answered 0), and
`pipe_rQ`'s pure conjunct is what funds cat's console write at cursor `c`
(design §4.1).

For **SH-PIPE-ROUND**: `pipe_round_reading` is the round, `pipe_Qc` is the
one symmetric payload both `wp_kshr_fork1` lends and both children exit
with, and `pipe_proto_alloc` is the registrar premise's instance — note it
hands out FIVE things, so `ush_pipe_call`'s answer conjunct `R γp` should be
instantiated at the whole quintuple.

### SH-PARSE-PIPE-3 (2026-09-18) — the catalog row, the constructor, and THE PARSER THEOREM at the pipe shape

Branch `app-pipe/sh-parse-pipe`, four more commits (`35e838ad5`,
`d5512683e`, `65e5d9591`, `28d30e086`) on top of part 2.  Whole tree green
(`build`, RC=0); no `Admitted`; every result carries `Proof using`; ELEVEN
new files, 10,857 lines, and the only landed files touched are the two the
coverage change forces (`iris/UCodeShP.v`, regenerated, and
`iris/UkShParse.v`, proof text only).

**`echo w1 … wn | cat` IS NOW PARSED**, from `parsecmd`'s entry to the
runner's tree, with nothing left to instantiate but the line, the two
allocator links and the exit payload every parser walk takes:

```coq
  UkShPipeCm.wp_kshp_parser_pipe :
    … ushq_pipe len f gp ge -> ushs_toks len f gp 0 args -> … -∗
    (∀ t, ushp_tree s0 t
            (UshpPipe (UshpExec args) (UshpExec [(S (S gp), ge)])) -∗
          ubytes γd s0 (S len)
            (ushp_nulfold [(S (S gp), ge)]
               (ushp_nulfold args (ushp_ext len f))) -∗ …)
```
`Print Assumptions` on it lists exactly the three platform assumptions the
landed redirect theorem has (`resv_matches`, `resv_is_valid`, funext).

**WHAT LANDED, in the order it had to.**

- **the catalog row** (`35e838ad5`): `tools/ucode_shp.txt`'s
  `skipfunc pipecmd` → `func pipecmd`, `iris/UCodeShP.v` REGENERATED
  (603 → 630 instruction facts, 12 → 13 functions, 372 → 377 decode
  lemmas; `pipecmd` is 0x260..0x29c, TWENTY-SEVEN instructions), and the
  consequence: `shp_syms_pins` gains a thirteenth conjunct, so the ELEVEN
  `destruct shp_syms_pins as (…)` patterns in `iris/UkShParse.v:857-877`
  each gained one `_` and `UkShParse.shpp_pipecmd` is new beside them.
- **`iris/UkShPipeCmd.v`** — `wp_kshp_pipecmd`: the constructor.
  `UkShRedirCmd.wp_kshp_redircmd_n`'s walk one size smaller (a SIX-word
  frame with five spills, `malloc(24)`, THREE field stores) with
  redircmd's NULL arm in shape, since `pipecmd` does not test malloc's
  answer either.
- **`iris/UkShPipePex.v`** — `wp_kshp_parseexec_bar`, the LEFT command's
  parse, at part 2's four substitutions.  They behaved exactly as
  predicted; the only one that was more than a name is the ANSWER (the
  redirect walk answers the REDIR node its last `parseredirs` built, and
  here no `parseredirs` turns, so `ret` still holds `execcmd`'s node).
- **`iris/UkShPipeCm.v`** grew `ushq_pipecmd_call_holds`,
  `ushq_pex_left_holds`, **`wp_kshp_parsepipe_bar_closed`** (the turn with
  BOTH premises discharged), `wp_kshp_parseline_bar`,
  `wp_kshp_parsecmd_bar` and **`wp_kshp_parser_pipe`**.
- `iris/UkShPipeParse.v` gained `ushp_pipe_node_addr` beside
  `ushp_pipe_close`.

**THE FINDINGS OF THIS PART.**

1. **`make gen-ucode` is a GENERATOR, not a dump rule, and the ruling was
   right**: `tools/gen_ucode.py` reads the TRACKED dump
   (`user-rocq/*{Instrs,Data,Syms}.v`) plus `tools/ucode_shp.txt` and
   never opens `xv6-riscv/`; `tools/dump_elf.py` is what reads the ELF and
   `make dump`/`dump-force` are the rules that call it.  The mirror's stale
   clone is irrelevant to it.  **What IS load-bearing is the other half of
   its header: it shells out to `coqc` and needs a BUILT `iris/`** — which
   is why it can only run where the build lives.
2. **THE FALSE GREEN, and it is a trap for every later coverage change:
   the lane helper's rsync syncs only `*.v` and `_CoqProject`, so a
   `tools/` edit does NOT reach the remote clone.**  The first
   `make gen-ucode` therefore read the OLD spec and printed
   `iris/UCodeShP.v: unchanged (603 instr …)` — a green run that had done
   nothing, exactly the failure the file's own header warns about ("a diff
   on an unchanged image means somebody hand edited a generated file").
   The fix is one `scp` of the spec before the run; the tell is the
   instruction COUNT in gen-ucode's own output.  Either the helper should
   sync `tools/`, or the brief should say to copy the spec over.
3. **`Local Notation`s do not travel, and three of them cost three build
   cycles.**  A copied walk silently loses `N` where the source file had
   `Local Notation wp_kshp_strlen := (UkShParse.wp_kshp_strlen N)`, and
   the error names a type mismatch (`"h6" has type "CpuId" while it is
   expected to have type "uk_names ?Σ"`) rather than a missing notation.
   Cheap check before building a copy: diff the two files' notation lists
   and grep the copied text for the difference.
4. **Three comment traps in one C quotation**, all in durable-notes and
   all worth re-reading before writing C into a Rocq comment: a
   `(struct cmd *)cmd` cast CLOSES the comment, `sizeof(*cmd)` OPENS a
   nested one (Rocq comments nest), and a `"` pair makes the rest a
   string.  Written as `(struct cmd * )` and `sizeof( *cmd )`.
5. **The name-clash rule for a transformed copy**: a premise you ADD to a
   copied walk must not collide with a register-file fact the copy
   already has.  `Hq`, `Hmiss`, `Hm23`, `Hr2`, `Hpos` were all taken; the
   errors are "X is already used" or a wrong-type application hundreds of
   lines away.  Name added premises `Hpq`/`Hmal01`/`Hmal23` and the like.

**WHAT IS LEFT OF THE PIPE PARSER: NOTHING.**  The chain from a typed line
to the runner's tree is now `UShLexRedir`-style lexability
(part 1: `ush_line_toks_holds_pipe`) → `wp_kshp_parser_pipe` → the seam
`ush_cmd_of_ushp_pipe` (part 1) → `ush_cmd γd t (UPipe (UExec …)
(UExec …))`, which is what lane SH-PIPE's `runcmd` arm consumes.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  The child WALK at the pipe
shape: `UkShMain.wp_kshm_child`'s twin (`wp_kshm_child_pipe`, the mould is
`UkShRedirSeam.wp_kshm_child_redir`), which is what turns this theorem into
a statement about the line sh READ.  It needs, and only needs: this
theorem, the seam, and the FOURTH arm of the line disjunct inside
`UkSh.ush_rest_line` — which SH-LEX-REDIR §4 shows is ONE coupled change
with that walk, so it belongs to SH-PIPE-ROUND and not here.  Nothing in
the parser blocks it any more.

### PIPE-NEG1 (2026-09-18) — the pipe row names its −1, the kernel discharge already existed and was being DROPPED, the PIPE arm is CLOSED at today's kernel — and `main` was RED at `UkShPipe.v`

Branch `app-pipe/pipe-neg1`.  Commits: `49d74380d` (the row and its cone at
the lane's original base), `52155fefc` (the leaf's second copy of the arm),
`3b72531ef` (notes), **`28f2d93fe` (merge `main`)**, `15e907ae4`
(deliverable 4), `1a763f267` (the `ukn_held` port).  No new file, no
`Admitted`, no `Axiom`; net diff against `main` is SIX files.

**THE LANE'S BASE MOVED UNDER IT, and the report has to start there.**  The
brief says "at main = the merged Wave-1 lanes incl. PIPE-REG and SH-PIPE".
At hand-off `main` was `299a9f774` and `iris/UkShPipe.v` DID NOT EXIST in
it — SH-PIPE's merge had been a no-op — so deliverable 4 was unreachable.
During the lane `main` advanced by ~200 commits: the upstream FILE
application program tier (`24a77ac43`) and `c41f80960` "Merge lane SH-PIPE
(**for real** — the 2026-09-18 'merge' was a no-op behind a failed `&&`
chain)".  The lane's first three commits are therefore against the old base
(whole tree green there, RC=0) and `28f2d93fe` merges `main` and
re-applies them.  **Whoever writes a brief that says "at main" should pin a
SHA**, and whoever merges a lane should check the merge landed: a no-op
merge and a real one look identical in `git log --oneline`.

**`main` IS RED, at `iris/UkShPipe.v`, for two independent reasons — both
predate this lane and both had to be fixed to get a green tree.**

1. **`ukn_held` does not exist any more.** SH-PIPE branched before
   upstream's OFF-LINK-2 L6, which deleted the parked discipline and the
   record field `UkRun.ukn_held`; `UkShPipe.v` still said
   `ukn_held N = ∅` in six statements, so the file does not ELABORATE:
   `Error: The reference ukn_held was not found in the current environment`
   on `make UkShPipe.vos`.  It is in `iris/_CoqProject`, so no whole-tree
   build could have been green after `c41f80960`.  `1a763f267` ports it —
   pure deletion: the premise goes from `wp_kshpi_dup`, `ushpi_dup_stub`,
   `wp_kshr_pipe_arm` (and with it the `⌜ukn_held N' = ∅⌝` conjunct it
   relayed to each child continuation, and the two `assert (Hhd' : …)` that
   built them), `wp_kshr_runcmd_pipe` and `wp_kshr_runcmd_ptop`.  The set
   was dead data at its end — this file's only use of it was to feed
   `UkRunSys.wp_uk_ecall_dup`, which no longer takes it.  `6766961ec` does
   the same to the campaign's OTHER site, `UkPipeMoves.
   wp_uk_close1_dup_pipe_std` (UPSTREAM-FIX's line 153); after the two, no
   file in the tree mentions `ukn_held`, `urun_parked_row`,
   `fdv_all_parked`, `fdv_held_in`, `urun_rows_parked`,
   `usys_fd_ok_parked`, `usys_fd_ok_held` or `riscv_kill_cred` outside a
   comment.
2. **The taint was still being passed into the registrar slot.** SH-PIPE
   also predates PIPE-REG, and its `ush_pipe_call_weak_of_leaf` applied the
   leaf as `with "[] Hrun [] Hkc Hstd [Hbuf]"` with `Hkc : app_taint` where
   `wp_uk_ecall_pipe`'s REGISTRAR premise now sits.  Fixed in `15e907ae4`
   as part of deliverable 4 (below).  `5e8e4dc0d`'s `riscv_kill_cred →
   app_taint` rename made the file LOOK ported; it only renamed.

**WHAT LANDED — the row.**  `iris/UsysMemOk.v`, the pipe row's failure arm,
verbatim (was `else sts' = sts`):

    else (r = (mword_of_int (-1) : mword 64) /\ sts' = sts))

so the row reads `if decide (uint r = 0) then (∃ a b γp, …) else (r =
mword_of_int (-1) /\ sts' = sts)` — the open and dup rows' spelling.  NEW
`usys_fd_ok_pipe_neg1`: the else-branch read at the guard a leaf
case-splits on (`usys_fd_ok USYS_pipe tf r sts sts' -> uint r <> 0 -> r =
mword_of_int (-1) /\ sts' = sts`), so no consumer unfolds the row.
`usys_fd_ok_length`'s pipe branch re-proved (`subst` → `destruct … as
[_ ->]`); every other lemma in the file is untouched, statements
byte-identical.

**...the kernel side.**  `iris/ProofSyscall.v` arm 4's failure branch
threads the fact instead of dropping it — `rewrite decide_False;
[ exact (conj Hr eq_refl) | …]`, one token.  **`ProofSysPipe.v` and
`SpecSysPipe.v` needed NO change**, which is the brief's deliverable 2
answered by "it was already done": `SpecSysPipe.sys_pipe_post` has ONE
failure arm and it already read `⌜r = (mword_of_int (-1) : mword 64)⌝`, and
`ProofSysPipe` walks all FIVE failure paths onto it (pipealloc at 1650,
each fdalloc scan at 1848 / 2041, and both copyouts at 2801 / 3191, the
last two sharing the C's one cleanup tail).  The −1 was proved against the
model all along; `ProofSyscall`'s arm 4 was USING it (to refute the success
guard: `rewrite Hr in Hz; vm_compute in Hz; discriminate`) and then
throwing it away.

**...the U tier.**  `UkRunSys.wp_uk_ecall_pipe`'s post failure arm is now
`(⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗ ustd (ukn_fd N) l)`, the sibling
open/dup leaves' spelling (`uint r <> 0` is a consequence and is NOT
restated — a redundant conjunct is a second thing every consumer has to
match); its `Hjoin` summary's last conjunct became `uint r <> 0 -> r =
mword_of_int (-1) /\ fdv' = fdv`; `ufd_auth_move`'s pipe branch re-proved.
`UkReadPipe.wp_uk_pipe_read_end` relays the same arm.

**...the exhibit.**  `iris/UkRunBr.v`, NEW `uv_btaken_bltz_neg1` /
`uv_btaken_bltz_one`: `uv_btaken BLT (mword_of_int (-1)) zero_reg = true`
and `uv_btaken BLT (mword_of_int 1) zero_reg = false`.  Two `vm_compute`
lines, and they are why the row had to name the VALUE: `r = 1` is equally
nonzero and does not take sh's `bltz a0`, so the old row admitted a state
in which the pipeline ran on two garbage descriptors, and the gap was not
bridgeable by a premise (`∀ r, uint r <> 0 -> r = -1` is refuted by the
second line — durable-notes.md, "Vacuity").

**...and deliverable 4: THE GAP IS CLOSED.**  `iris/UkShPipe.v` §7 was
"THE GAP, MEASURED".  `ush_pipe_ans_weak` and `ush_pipe_call_weak` are
DELETED (not kept as corollaries: a strictly weaker restatement of a landed
predicate has no caller and would only invite one) and
`ush_pipe_call_weak_of_leaf` becomes **`ush_pipe_call_of_leaf`**, proving
the FULL `ush_pipe_call` by the same three-instruction walk — the only
change in the body is that the failure branch's `%Hrne` binds
`r = mword_of_int (-1)`, which the existing `by iPureIntro` already closes,
because SH-PIPE had already WRITTEN `ush_pipe_ans`'s failure arm at
`⌜ r = (mword_of_int (-1) : mword 64) ⌝`.  NEW
**`wp_kshr_runcmd_pipe_closed`** and **`wp_kshr_runcmd_ptop_closed`**: the
consumer tests with the call SPENT.

**WHAT THE DESIGN GOT WRONG**

1. **`wp_kshr_runcmd_pipe`'s `ush_pipe_call` premise should NOT be deleted**
   (the brief: "closing `wp_kshr_runcmd_pipe` at today's kernel with NO
   premise").  It is the same premise `UkShRedir.ush_open_call` is at the
   REDIR arm, and a caller holding a REAL registrar (PIPE-PROTO's
   `pipe_proto_alloc`, `R γp := pipe_inv … ∗ wtok`) has to hand its own
   call in — deleting it would fix `R := emp` and lock the round out.  So
   the two landed statements do not move and the closed forms are new
   corollaries beside them.  **And they are not premise-free**: the call is
   traded for the three things the leaf actually needs — `app_taint` (this
   is the `R := emp` instance; a registered program supplies a registrar
   instead), `udepw_law 21` (what the two `ush_cldep`s are built from; not
   derived here, because the mint that derives it from the taint is an
   application-level file and importing it into a walk wedges) and a FULL
   LEDGER `fd_lowest_closed ld = None`, which is what makes both of
   pipe(2)'s allocations land above the standard streams.  sh at the prompt
   is exactly there.
2. **The leaf's failure arm occurs TWICE in `UkRunSys.v`** and only one
   copy is in the statement: `wp_uk_ecall_pipe` builds its post's two arms
   as an intermediate `iAssert (|==> ufd_auth … ∗ (… ∨ (⌜uint r <> 0⌝ ∗
   ustd …)))` before framing them.  A `check` passes with the inner copy
   stale and the real build fails 40 lines later (`The term
   "proj1 (Hfail Hr0)" has type "r = mword_of_int (-1)" while it is
   expected to have type "uint r ≠ 0"`).  Grep a leaf's whole proof for the
   arm's text, not just its statement.
3. **The brief's failure-arm inventory is short by two.**  It says
   "`pipealloc` fails, `fdalloc` fails twice, each `return -1`"; sys_pipe's
   three `return -1` statements cover FIVE paths, the two extra being the
   copyout pair.  (The object code merges them into two `li a5,-1`, at
   0x800055b2 and 0x8000563c.)
4. **The row's cone is smaller than the brief feared, and shrank further
   mid-lane.**  At the lane's base FIVE places destructed the pipe row's
   else-branch (`usys_fd_ok_length` / `_parked` / `_held`,
   `UkRunSys.ufd_auth_move`, and `wp_uk_ecall_pipe`'s `Hjoin`); upstream's
   L6 then deleted `_parked` and `_held` outright, leaving three.  Every
   other `usys_fd_ok` site either carries `n <> USYS_pipe` or consumes a
   different row.  Strengthening the row is safe by construction: it is
   SUPPLIED in exactly two places — `ProofSyscall`'s arm 4, and
   `usys_fd_ok_refl_at`, which excludes pipe.

**BUILD STATUS AT HAND-OFF, exactly.**  TWO builds matter and they are not
the same thing.
- **The row change IS whole-tree green**: at the lane's original base
  (`372b70c46`, PIPE-REG merged) `ec2-lane.sh neg1 build` returned **RC=0**
  over the whole `iris` tree with the first three commits in place — the
  row, `usys_fd_ok_pipe_neg1`, `ProofSyscall` arm 4, both of
  `wp_uk_ecall_pipe`'s copies of the failure arm, `UkReadPipe`'s relay and
  the two `uv_btaken` lines.  That is the deliverable 1–3 bar, met.
- **EVERY FILE THIS LANE TOUCHES IS BUILT, post-merge, with `.vo`s**:
  `UsysMemOk`, `ProofSyscall`, `UkRunBr`, `UkRunSys`, `UkReadPipe`,
  **`UkShPipe.vo`** and **`UkPipeMoves.vo`** all compiled for real against
  `d860835b2`+this branch, `errs=0` throughout.  So deliverables 1–4 and
  both `ukn_held` ports are machine-checked, not merely `check`ed.
- **THE POST-MERGE WHOLE-TREE BUILD ENDS AT RC=2 WITH ONE FAILED TARGET,
  `UShRound.vo`, AND IT IS THIS LANE'S FAULT — NOT UPSTREAM'S.**  The
  failure is `Segmentation fault (core dumped)` → `Error 139`, so it is
  resource exhaustion in the checker, not a type or proof error, and it is
  NOT the stack limit (it reproduces alone under `ulimit -s unlimited`).
  My first reading was "upstream's file, upstream's problem".  **That is
  wrong, and the discriminator is clean:**

      md5 UShRound.v  = 6d182af64e007c1283eb5516e4726bc7   -- IDENTICAL in
        /shared/xv6iris-pipe-neg1  and  /shared/xv6iris-pipe-merge
      UShRound.vo     = 153908 bytes, 11:38, in the MERGE clone (built)
                      =  37627 bytes, 10:55, in THIS clone (STALE, pre-sync)

  The UPSTREAM-FIX lane's clone, on the same mirror, at the same hour, with
  the same `UShRound.v` and WITHOUT this lane's seven files, compiles it.
  This clone does not.  **And it is not contention**, though the box was
  busy (load 19, ~14 foreign `rocqworker`s): load makes a compile slow, not
  SIGSEGV, and there were 180 GB of the mirror's 246 free throughout.  One
  caveat to carry into the bisect: `ulimit -s unlimited` lifts the limit
  for the MAIN thread, and glibc still gives pthreads an 8 MB default, so a
  blow-up on a worker thread would survive the raise — which is consistent
  with `WpGprCsrwC.vo` being cured by it and `UShRound.vo` not being.  The only source difference in its cone is this
  lane's diff (`UsysMemOk.v` md5 differs; the other six too), so **the −1
  conjunct, or something else in this lane's seven files, makes
  `UShRound.v` blow the checker's stack.**

  **THE CAUSE, FOUND — AND THE FIX (commit `222496294`).**  `rocq compile
  -time` puts the segfault on ONE command: the **`Qed.` of
  `UShRound.Hopen_hand`** (line 653; the last command to finish is
  `iExact "HK"`, chars 35526-35538).  With the stack raised that `Qed`
  does not crash, it **hangs** — which durable-notes.md's own rule says to
  read as a **CONVERSION**, not as a proof term that is merely large.
  `Hopen_hand` takes the nopipe row as a premise (`%Hnp` in its
  `iIntros`), so `usys_fd_ok`'s BODY is on its conversion path — and this
  lane had turned that body's pipe branch from the equation `sts' = sts`
  into a CONJUNCTION.  One extra binary node, in the heaviest `Qed` of the
  biggest file in the tree.

  The repair keeps the −1 and puts the arm behind a NAME:

      Definition usys_pipe_fail (r : mword 64) (sts sts' : list fdstate) : Prop :=
        r = (mword_of_int (-1) : mword 64) /\ sts' = sts.

  with the row reading `else usys_pipe_fail r sts sts'`.  The body is one
  head symbol per branch again — in fact SMALLER than before the −1
  landed, since the old branch was itself an application of `eq`.  Nothing
  about the row's MEANING moves: `usys_fd_ok_pipe_neg1` still hands every
  consumer `r = -1 /\ sts' = sts`, and it is the only reading anybody
  uses.  The consumers go through with an explicit `unfold usys_pipe_fail`
  rather than relying on delta at a `destruct`/`exact`:
  `usys_fd_ok_length`, `usys_fd_ok_pipe_neg1`, `UkRunSys.ufd_auth_move`,
  `ProofSyscall`'s arm 4.  `usys_fd_ok_nopipe` and
  `UkRun.urun_nopipe_step` never destruct the pipe branch (both carry
  `n <> USYS_pipe`) and did not move.  **VERIFICATION STATE at hand-off:
  `build UShRound.vo` had rebuilt 164 cone files with ZERO errors and had
  not yet reached `UShRound.v`, the mirror being saturated by another lane
  (~40 foreign workers).  The coordinator should let that finish and then
  gate the whole tree.**

  **THE LESSON, for the design notes**: a row in one of these big
  `if/decide` tables is on the CONVERSION path of every `Qed` that takes
  the row as a premise, so **its branches should each be one head symbol**
  — a named `Definition`, never two conjuncts spelled inline.  The open
  and dup rows get away with inline conjunctions only because nothing as
  heavy as `Hopen_hand` converts them.

  **(SUPERSEDED) THE SUSPECT LIST WAS TWO FILES, not seven** — `.CoqMakefile.d` says
  `UShRound.vo` depends DIRECTLY on exactly one of this lane's files,
  `UkRunSys.vo`, hence on `UsysMemOk.vo` only through it.  So the vector is
  either the row itself or `wp_uk_ecall_pipe`'s new post shape, and the row
  is the likelier of the two: `UShRound.v` proves sh's round at the FILE
  claim and never calls pipe(2), but its leaves run
  `UkRun.urun_nopipe_step` / `urun_rows_step`, which CASE-SPLIT the whole
  `usys_fd_ok` chain — and that chain's pipe branch is exactly what grew a
  conjunction.

  **WHAT THE NEXT LANE SHOULD DO ABOUT IT, concretely.**  Bisect those two
  against `UShRound.vo` alone: `git checkout main -- iris/<F>.v` and
  `make UShRound.vo`.  `UsysMemOk.v` is the prime suspect and
  the mechanism is almost certainly TERM SIZE, not logic — the row's
  else-branch went from an equation to a CONJUNCTION, so anything that
  normalises or case-splits the whole `usys_fd_ok` chain (a `vm_compute`, a
  `cbn` on the row, an `intuition`/`done` over it) now carries one more
  binary node per pipe branch, and `UShRound.v` is the largest file in the
  tree.  **If that is it, the fix is cheap and keeps the conjunct**: state
  the failure arm as a NAMED definition (e.g. `usys_pipe_failed r sts sts'`)
  so the row's body stays one head symbol wide, or split the sign out into
  `usys_fd_ok_pipe_neg1`'s shape and leave the row's else-branch the
  equation it was — the sign is only ever read through that lemma anyway,
  which is exactly why the lemma exists.  **Do not conclude the lane's
  logic is wrong: every file the lane touches builds, and the row, the
  leaf, the relay and sh's arm are all machine-checked (below).**
- The echo audit had not returned either, so **this lane reports no audit
  count**.
- **ONE REAL PROOF BREAK WAS FOUND BY THE BUILD AND FIXED** (`c7fcab036`):
  `wp_kshr_pipe_arm`'s two child continuations introduced
  `UkShRun.wp_kshr_fork1`'s child arm with a `%Hheq` for
  `⌜ukn_held N' = ukn_held N⌝`, which L6 deleted with the field, and
  `iIntros` failed with `iIntro: cannot turn (…) into a universal
  quantifier`.  **A `-vos` check cannot see this** — the statement
  elaborates, only the proof runs out of premises — which is the second
  time this lane was bitten by trusting `check` (see finding 2).

**THE MIRROR'S STACK LIMIT IS 8 MB, AND IT SEGFAULTS THE BUILD — `ec2-lane.sh`
should raise it.**  Bringing the clone up to the merged sources, the build died
twice, reproducibly and at the same place: `Segmentation fault (core dumped)`
→ `make[1]: *** [CoqMakefile:818: WpGprCsrwC.vo] Error 139`, in an UPSTREAM
model file this lane never touched.  It is not memory (20 GB of 246 in use)
and not parallelism (it happened at `-j18` and again at `-j10`): `ulimit -s`
on the mirror is **8192 KB**, and the helper's `ENV` sets only
`OCAMLRUNPARAM="l=…"`, which does not move the OS stack (durable-notes.md's
own advice under the fuel-constant note is "re-run with `ulimit -s
unlimited`"; the hard limit on the box IS unlimited).  Running
`ec2-lane.sh neg1 run 'ulimit -s unlimited; make -f CoqMakefile -j10'` builds
`WpGprCsrwC.vo` on the first try.  **`ec2-lane.sh`'s `ENV` should gain
`ulimit -s unlimited`** — every lane that has to rebuild the model/WP tier
will hit this, and the failure names a file that has nothing to do with the
lane, so it reads like someone else's breakage.  (Also useful: the worker
binary is `rocqworker`, not `rocqc`, so `pgrep -c rocqc` reports 0 during a
perfectly healthy build and makes it look wedged.)

**MAIN KEPT MOVING AFTER THIS LANE'S MERGE, and it does not matter.**  By
the end of the lane `main` had also gained PIPE-PROTO (`d3940f9b3`),
SH-PARSE-PIPE part 3 (`5006b8aeb`) and a brief **UPSTREAM-FIX** ("make main
build after the upstream merge; campaign files only", `6204044e4`) — so the
red tree above is known, and this lane's `1a763f267` OVERLAPS that lane's
job at `iris/UkShPipe.v`; take whichever is better and drop the other.
This branch's base is `d860835b2`, and `main` has touched NONE of the six
files this lane edits since then (`git diff d860835b2..main --` on them is
empty), so the merge is clean apart from this notes file.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  For SH-PIPE-ROUND and
PIPE-PROTO: nothing is owed about pipe(2) any more — take
`wp_kshr_runcmd_pipe` (not the `_closed` corollary, which fixes
`R := emp`) and instantiate `ush_pipe_call` from `wp_uk_ecall_pipe` with
the protocol's registrar, exactly as `ush_pipe_call_of_leaf` does with the
trivial one.  For the COORDINATOR: `main` cannot have been built since
`c41f80960`; re-run the gate, and note that `iris/UkShPipe.v` in this
branch is the ported file.

### PIPE-STAGE (2026-09-18) — the stage, the ledger, the links and the RECORD land; `app_pipe`'s only open field is `al_programs`; the `LinkRec` INSTANCE is a LANE, and the claim does NOT pin /cat

Branch `app-pipe/pipe-stage`, TWO commits (`a2df9095a`, `e683b65d0`).
Whole `iris` tree `ec2-lane.sh stage build` **RC=0**.  FOUR new files
(`PipeOutPure.v`, `PipeOut.v`, `PipeLinks.v`, `AppPipe.v`) plus
`PipeDiscDec.v` copied UNMODIFIED from main (lane PIPE-DEC); the diff to
existing files is FIVE ROWS of `iris/_CoqProject` and nothing else.  No
`Admitted`; every proof carries `Proof using`.  **The three audits cannot
have moved**: nothing in the tree imports these four files (checked —
`grep -l "Require .* \(PipeOut\|PipeOutPure\|PipeLinks\|AppPipe\)"` names
only the four themselves), so the echo/tree/system cones are untouched.

**`Print Assumptions`** — *Closed under the global context* (no axioms at
all, not even PrimString) on `good_out_p_of_stage`, `sessp_prefix_det2`,
`pecl_drain`, `pecl_step_echo`, `pecl_step_read`, `pipe_led_phi`,
`pipe_led_pow`, `pipe_birth_all`, `pipe_links_holds` and **`pipe_happ_echo`**
(the file application's twin needs the eleven primitives; this one needs
none).  `pipe_Hphi_R` and `pipe_Happ_init` are the eleven
PrimString/PrimInt63 primitives and nothing else.  `pipe_laws` adds exactly
the two Sail reservation `Parameter`s (`resv_matches`, `resv_is_valid`)
through `InitBoot.init_boot_bundle`, as `file_laws` does.

**WHAT LANDED.**

`iris/PipeOutPure.v` (~1,130) — `EchoOutPure.v`'s twin at `PipeDisc.sessp`.
`disc_p`'s closure laws (`disc_p_out`, `_in`, `_power`, `_other`, `_prefix`,
plus `disc_p_snoc`, `disc_seg_p'_other/_out/_in` and the open-cycle pair —
`PipeDisc` landed `disc_input_p`'s full set and, of `disc_p`'s, only
`disc_p_nil`/`disc_p_seg`); the byte facts (`disc_input_p_byte`,
`disc_input_p_byte_val`, `disc_byte_ok_p`, `echo_of_disc_p`,
`disc_seg_p_no_erase`, `_no_ctrl_d` — the pipe body byte `'|'` is 124, which
is none of 13/21/8/127/4, so every refutation is still one `lia`);
`pending_at_p`/`pending_p`/`D_from_p`/`D_p` and the append laws; F1
(`D_p_pending_sessp`, `D_p_stage_prefix`); F2 (`sessp_length_lt`,
`D2_next_input_p`); F4 (`good_out_p_of_stage`); `alts_pre_p` + `alts_pad_p`;
the era's cursor (`proc_before_p`, `proc_stream_p`, `pcount_p`,
`write_stage_byte_p`) and the banner-at-an-arbitrary-round pair;
`stage_sessp_pad`, `good_out_p_step`, `disc_seg_p'_pt_last`, `sessp_nonnil`.
**F3 IS `EchoOutPure.read_window_prefix` VERBATIM** (it is about the log and
names no discipline), and **where `FileOutPure` threads `fo_f0`, this file
threads nothing** — there is no `f0_st`, no `opt_list`, no `fst_ok` clause
and no second witness.

`iris/PipeOut.v` (~1,750) — the claim, the tag, the turn, the steps and the
ledger.  `pout_pure`, `ps_len_ok_p` (+ `_0`/`_empty_above`/`_write`/`_blk`/
`_echo`/`_pro`), `cs_len_ok_p_echo`, `pein_pure`, `rd_stage_p`,
`ch_arm_era_p`, `pcl_pure` (+ `_arm`/`_E`/`_rd_stage`/`_close`/`_out`/
`_read`/`_open`/`_byte`), `pout_pure_move`, `pout_pure_nil_stage`,
`echoed_lt_ins_p`, `phi_step_io_p`, `phi_step_cons_p`; then `pecl`, `ptag`,
`pturn`, `pecl_close`, `pecl_open`, `pecl_sup`, `pecl_arm`, `pecl_lt`,
`pecl_step_write`, `pecl_step_write_blk`, `pecl_step_write_pro`,
`pein_read_pure`, `cs_lb_weaken_p`, `pecl_step_read`, `pecl_step_echo`,
`pecl_step_byte`, `pecl_drain`; and `pipe_led` with `pipe_led_init`,
`era_full_split_p`, `pipe_led_pow`, `pipe_led_tx`, `pipe_led_rx`,
`pipe_led_phi`, `pipe_cl_all`, `pipe_birth_all`.

`iris/PipeLinks.v` (~390) — `pipe_cons_link_of_taint`,
`pipe_write_link_taint`, `pipe_write_link`, `pipe_write_link_blk`,
`pipe_write_link_pro`, `pread_ret`, `pipe_read_link`, `pipe_close_link`,
`pipe_byte_link`, `pipe_cons_run`, the bundle `pipe_links` with its six
components, seven persistence instances, six projections and
`pipe_links_holds`, and `pipe_happ_echo` (`App.al_echo`, a CLOSED
entailment).

`iris/AppPipe.v` (~310) — `pipe_phi := fun _ h => PipeDisc.pipe_phi h`,
`pipe_R`/`pipe_tag`/`pipe_kill`/`pipe_cons`/`pipe_ifc`/`pipe_turn`, the
record, `pipe_Happ_init`, `pipe_Hphi_R`, and
`Global Instance pipe_laws : App.xv6_app_laws app_pipe`.

**`app_pipe`'S FIELD LIST, VERBATIM**:

```coq
Definition app_pipe : xv6_app Σ :=
  MkApp echo_fixed pipe_cl_all echo_names echo_pred echo_boot
        pipe_R pipe_ifc pipe_turn pipe_phi.
```

FIVE of the nine fields are **`AppEcho`'s own names, imported and not
restated** (`echo_fixed`, `echo_names`, `echo_pred`, `echo_boot`, and
`pipe_cl_all` which is `Definition pipe_cl_all := echo_cl`).  The
`Context` hypotheses left are **exactly one**: `Hprog` (lane
SH-PIPE-ROUND's `al_programs`, in `Section PipeLaws`).  `Hdp` was never
needed — `PipeDiscDec.disc_p_dec` is on main and the counter reads it
directly, and per PIPE-DEC's warning no `decide` is on an evaluation path:
`pipe_led_init` rewrites with `decide_True` at `disc_p_nil` and every step
with `decide_ext` at one of `PipeOutPure`'s closure laws.

**WHAT THE DESIGN / THE BRIEF GOT WRONG.**

1. **`sessp_prefix_det2` IS REDUNDANT.**
   `FileOutPure.sessf_prefix_det2` exists for ONE reason: a file's
   transcript reads the era's boot state, and the discipline's
   existentially-chosen state and the claim's own filed one have no reason
   to agree.  A pipeline round reads NO state, so
   `PipeDisc.sessp_prefix_det` ALREADY compares two independent
   resolutions and is the lemma the stage spends.  It is landed under the
   brief's name and proved by `exact (sessp_prefix_det …)`; if the
   coordinator prefers, the name can be deleted and every call site points
   at `PipeDisc`.

2. **`postage` = `EchoOut.ostage` REUSABLE VERBATIM — CONFIRMED, and so is
   `EchoOut.cs_len_ok` with five of its six lemmas.**  `postage` is a
   definitional alias, so `cs_len_ok`, `cs_len_ok_inv`, `_intro`, `_mid`,
   `_write`, `_blk`, `_0` all apply unchanged.  Only `cs_len_ok_echo` needs
   a twin (`cs_len_ok_p_echo`), because its one non-arithmetic step is "a
   completed line's block is never empty", which is the pipeline model's
   fact.  **`ps_len_ok` DOES need a twin** and the reason is exact: it
   names `pro_idx` and the round-opening test `cs !!! (nlines − 1) = 3`,
   which at this model are `pro_idx_p` and
   `palt_panic (palt_at cs (nlines − 1))`.  So the era's stage record adds
   nothing and its two length laws are 1 + 6 lemmas of new text, not a
   second record.

3. **`EchoOutPure.cs_ok` HAS NO TWIN, and the reason is SHARPER than at the
   file application.**  Out of range `!!!` reads `0`, which decodes to
   `PipeDisc.PEcho 0` — and after PIPE-MODEL-2's ruling the ONLY `PEcho` an
   `LPipe` line admits is `PEcho 3`, so the out-of-range reading is
   precisely the alternative a pipeline line refuses.  No total condition on
   `cs` can work, and `FileOutPure`'s route is the only one: the stage
   carries the POINTWISE `alts_pre_p` and `PipeDisc.alts_ok_p` (which the
   determinacy theorem and `good_out_p` are stated at) is reached by
   PADDING.  The default alternative is `palt_def (LEcho _) := 0` and
   `palt_def (LPipe _) := palt_code PRan` (= 4); neither panics
   (`palt_panic_def`), so `alts_pad_p_pro_idx` moves no prologue round.

4. **`EchoOut.rd_stage_le` HAS NO TWIN EITHER** — `alts_pre_p I cs` ties
   each entry of `cs` to the LINE AT ITS INDEX in `I`, so shortening `I`
   can leave an entry with no line to answer.  (Upstream `FileOut` has no
   `rd_stage_f_le` for the same reason; the brief did not name this.)  What
   replaces it at the read is FileOut's route, and it had to be copied:
   **the read exports the claim's choice list TRUNCATED to the WINDOW's own
   line count** (`take (nlines Iw) (o_cs so)`, with `cs_lb_weaken_p`).

5. **A WRITER'S RANGE CONDITION NEEDED TWO NEW PURE LEMMAS**, hoisted
   where `FileOut` inlines the same argument twice:
   `alts_pre_p_at_prefix` and `pending_at_p_nonnil_pre`.  A write link names
   a lower bound `I0` of the era's input while the claim carries
   `alts_pre_p` at the era's WHOLE input, and `alts_pre_p` is monotone the
   other way — but the only entry `pending_at_p` reads is the last completed
   line's, whose BODY is the same body in the longer input.

6. **THE TAG IS STAGE'S CORRECTED SHAPE, and the design page's first guess
   is refuted at the statement.**  `ptag h := ⌜trace_shape h true⌝ ∗
   (⌜disc_p h⌝ ∨ pipe_taint)`.  `EchoOut.etag`'s left arm is `⌜disc h⌝`,
   which says NOTHING about the pipeline session: `disc_p h` does not imply
   `disc h` (a pipeline line is not an echo line;
   `PipeDisc.disc_p_disc` needs the `echo_only` premise), so any shape of
   the form `etag h ∗ …` is the wrong tag.  Unlike `FileOut.ftag` there is
   no THIRD conjunct: a pipe dies with its era, so there is no line list to
   carry a lower bound of.

7. **THE FIXED PART NEEDS NO SECOND GNAME — CONFIRMED**, and more:
   `pipe_cl_all` IS `AppEcho.echo_cl`, `pipe_birth_all` IS
   `AppEcho.echo_birth`, and **`pturn` IS `EchoOut.eturn` verbatim** (where
   `FileOut.fturn` is `eturn` plus the era's file pin).  Every one of
   `EchoOut`'s per-era ghosts (`era_pins`, `era_pin`, `turn`/`turn_auth`/
   `turn_lb`, `cs_auth`/`cs_lb`, `ps_auth`/`ps_lb`, `Elist_*`, `inp_lb`,
   `dl_cnt`, `pin_map`, `era_full`) and the whole `ch_E` layer are imported
   unchanged.

8. **`pipe_link_inst : LinkRec` IS NOT REACHABLE IN THIS LANE — IT IS A
   LANE.**  The evidence, at the statement: `LinkRec.LinkRec` has 94 fields,
   of which ELEVEN are CREDENTIAL FAMILIES (`lk_ban`, `lk_owed`, `lk_sp`,
   `lk_open`, `lk_blk`, `lk_pro`, `lk_sp_t`, `lk_open_t`, `lk_line`,
   `lk_lend`, `lk_rres`) with ~40 laws under them.  At the echo application
   those families are `EchoLinks.v` + `EchoLinksLine.v` = **2,247 lines**,
   and LINK-GEN §6 priced the FILE twin of exactly that half at
   `FileLinksLine.v` ≈ 1,100 lines and left it OWED: **there is no
   `file_link_inst` in the tree** (`grep -rn file_link_inst iris/*.v` is
   empty; `FileLinksLine.v` does not exist), so upstream's FILE application
   has not paid it either and the record instance has never been built for
   any second application.  A `PipeLinksLine.v` is the pipe twin of those
   families at `pending_at_p`/`pro_pin_p`/`proc_stream_p`/`pro_idx_p`, and
   it is not a step.  What this lane DID deliver for item 3 is exactly
   `FileLinks.v`'s landed content — the links, the taint routes, the bundle
   and `App.al_echo` — which is what a program tier actually spends.
   **What the instance's LINE-MODEL fields would be, priced and free:**
   `lk_ab I a := pcont (pline_of (bodies_of I !!! (nlines I − 1))) (palt_of a)`
   with **NO guard** (unlike the file's, which must send `RCRan` at a
   present `f` to `[]`: `pcont` reads the line and the alternative and NO
   state, which is the one place the pipeline application is *simpler* than
   the file one); `lk_apr` = `PipeDisc.pcont_shape`'s "a `$`-free run then
   the prompt", which holds at EVERY non-panic alternative of EITHER line
   shape; and `lk_pan`/`lk_exf`/`lk_noc` are the LITERAL numbers `3`/`1`/`2`,
   because `palt_code (PEcho k) = k` for `k < 4` — so those three fields are
   `reflexivity`-equal to `echo_link_inst`'s, and `PipeDisc.alt_execL_echo`
   (`alt_execL = EchoDisc.alt_execfail`) makes the exec-failed diagnostic
   the same bytes.

9. **`pipe_fs_pure` IS NOT A FIELD OF THE RECORD, AND THE CLAIM THEREFORE
   DOES NOT PIN /cat.  THIS IS AN OWNER DECISION AND IT IS ON
   SH-PIPE-ROUND'S / CAT-PIPE'S CRITICAL PATH.**  The brief says
   `app_pred := AppEcho`'s claim, the file system unmodified, and offers
   `pipe_fs_pure av := echo_fs_pure av /\ era0_cat_pins av` "if the record
   needs a pure image predicate beyond echo's".  It cannot have both:
   `app_pred` is the field that carries the image predicate, and
   `AppEcho.echo_pred`'s is `EchoFsPure.echo_fs_pure av := era0_pins av /\
   era0_sh_pins av /\ era0_echo_pins av` — /init, /sh and /echo, **and not
   /cat**.  So the record as landed (which typechecks, and no field forces a
   pipe-specific ghost, so the brief's STOP rule is not triggered) says
   nothing about cat's binary, and a round that `exec`s /cat cannot resolve
   it from the claim.  The two routes, priced:
   (a) **a pipe-specific `app_pred`** at `pipe_fs_pure := echo_fs_pure /\
   era0_cat_pins` — then the design's "the file system unmodified (the echo
   application's invariant, verbatim)" is FALSE as a description of what the
   theorem needs; `AppFile.file_pred` is the mould and the pure half is
   already landed (`FsCatPin.era0_cat_pins`, `FileDeltas`/`FileWrite`'s
   `file_pin fname_cat CAT_INO cat_bytes av <-> era0_cat_pins av`), but the
   transport, the era-0 image lemma and `al_xfer` would all be re-proved at
   the new predicate (and then `app_pred`, `app_boot`, `app_names` are no
   longer echo's names); or
   (b) **keep echo's claim and confine the pipeline round to era 0**, where
   `FsCatPin.era0_boot_cat_pins` gives `era0_cat_pins` free from the literal
   image — which costs the theorem its across-a-power-cycle generality for
   the PIPELINE line (design §0's limit 3 already gives up everything else
   across a cycle, so this may be exactly what the owner wants).
   Nothing in this lane depends on the answer; SH-PIPE-ROUND does.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  `AppPipe.pipe_laws` is
already an instance under `Context (Hprog : …)` whose statement is
`App.xv6_app_laws`'s `al_programs` field VERBATIM at `app_pipe`;
SH-PIPE-ROUND supplies exactly that and the record closes.  What it must
have in hand at /init's first instruction is
`app_turn app_pipe c (S gen_id)` = `PipeOut.pturn c (S gen_id)` =
**`EchoOut.eturn c (S gen_id)`, echo's five components with NOTHING added**
(`era_pin`, `turn v 0`, `dl_cnt v (1/2) 0`, `cs_lb v []`, `ps_lb v []`,
`inp_lb v []`) — so the era's first banner byte goes out through
`PipeLinks.pipe_write_link_pro` at `I0 = []`, `cs0 = []`, `P = 0`, exactly
as at the echo application, and there is no `file_write_link_first` to
imitate.  And it needs finding 9's ruling before it can resolve /cat.

### PIPE-CLAIM (2026-09-18, = PIPE-STAGE part 2) — the claim pins /cat at a cost of ZERO transcribed proofs, /init's whole console dance lands at it, and part 1's "the LinkRec instance is a lane" is now HISTORICAL

Branch `app-pipe/pipe-stage`, THREE further commits (`7429b00ab` the merge,
`4fdf35154`, `6d86a19b6`).  Whole `iris` tree `ec2-lane.sh stage build`
**RC=0**; every one of the lane's seven `.vo`s present.  No `Admitted`;
every proof carries `Proof using`.  Nothing in the tree outside the lane's
own files imports them, so the audits' cones are untouched.

**THE MERGE COST ALMOST NOTHING, and that is worth recording.**  190
upstream commits later — `riscv_kill_cred` → `app_taint`, the parked
discipline deleted, `StageRec`/`ReadRec`/`FileLinksLine`/`FileLinkInst`
landed, `EchoOut`/`EchoOutPure`/`FileOut`/`FileOutPure`/`FileLinks`
**byte-identical** — `PipeOutPure.v`, `PipeOut.v` and `PipeLinks.v` compiled
**UNCHANGED**.  The only adaptation any part-1 file needed was ONE field:
`RiscvPtsto.app_iface` gained `ai_lic` (upstream's lane SUP-ONE), so
`AppPipe.pipe_ifc` gains `pipe_cons_lic` — three lines, `pecl_sup` read one
step earlier.  The lane's four files are built on `EchoOut`'s ghost algebra
and `EchoDisc`'s prologue and on nothing that moved.

**WHAT LANDED.**

`iris/AppPipeClaim.v` (new, ~260) — design §5.6's ruling:

```coq
pipe_pred γ r av := echo_taint γ ∨ (⌜FileFsPure.file_fs_pure av⌝ ∗ cons_state r av)
```

echo's SHAPE with upstream's landed stronger pure conjunct
(`echo_fs_pure av /\ era0_cat_pins av`), imported read-only.
`pipe_pred_split`, `pipe_pred_cons`, `pipe_pred_echo`, `pipe_pred_absent`,
`pipe_sup_echo`, `pipe_taint_of_sup`, `pipe_xfer`, `pipe_boot`,
`pipe_xfer_boot`, `pipe_init_key`, `pipe_init`, `pipe_init_img`.

`iris/AppPipe.v` — `app_pred := pipe_pred`, `app_boot := pipe_boot`,
`pipe_cons_lic`, and three `reflexivity` ANTI-VACUITY checks
(`pipe_app_pred_eq`, `pipe_app_names_eq`, `pipe_app_boot_eq`) that the claim
equation the program tier takes as a parameter IS the one `al_programs`
hands over at this record.  `app_fixed`, `app_cl` and `app_names` are still
`AppEcho`'s own names.

`iris/AppPipeCons.v` (new, ~400) — the nine conjuncts of
`UInitCons.init_cons_laws_at` at `pipe_pred`: `pipe_fs_pure_acc`,
`pipe_echo_fs_pure_acc`, **`pipe_cat_pins_acc`** (the reading the lane
exists for), `pipe_cons_law`, `pipe_cons_abs_law`, `pipe_cons_never_law`,
`pipe_cons_seal_step`, `pipe_cons_shoot`, `pipe_sup_of_taint`,
`pipe_step_of_echo`, `pipe_cons_arm`, `pipe_cons_unarm_absent` /
`_present`, `pipe_cons_mknod` / `_present`, `pipe_cons_create_other`,
`pipe_unarm_root`, `pipe_fs_pure_unarm_dev`, `pipe_cons_unarm_efp_absent` /
`_present`.

`iris/UInitConsPipe.v` (new, ~330) — /init's WHOLE console dance at the pipe
claim: the four bundles (`init_cons_laws_pipe`, `init_cons_laws_efp_pipe`,
`init_cons_laws_made_pipe`, `init_cons_laws_made_efp_pipe`), the seal
(`init_cons_never_abs_law_pipe`, `init_cons_seal_law_pipe`,
`init_cons_seal_out_pipe`, `init_cons_cred_made_pipe`), both LEAF pairs
(`init_cons_leaves_pipe`, `init_cons_hit_pipe`) and sh's two console arms
(`sh_cons_absent_pipe`, `sh_cons_console_pipe`).

**NOTHING STOPPED.**  The brief said to stop at the first law needing
something the design had not priced; there was none.

**`Print Assumptions`.**  Part 1's four headline results are still *Closed
under the global context* (`good_out_p_of_stage`, `pecl_drain`,
`pipe_led_phi`, `pipe_happ_echo`).  The WHOLE claim layer and all four
bundles — `pipe_pred_split`, `pipe_xfer`, `pipe_xfer_boot`,
`pipe_taint_of_sup`, `pipe_init_img`, `pipe_cat_pins_acc`,
`pipe_step_of_echo`, `pipe_cons_mknod`, `init_cons_laws_pipe`,
`init_cons_laws_efp_pipe`, `init_cons_laws_made_pipe`, `pipe_Hphi_R`,
`pipe_Happ_init` — are the eleven PrimString/PrimInt63 primitives and
NOTHING else.  `pipe_laws` is those eleven plus the two Sail reservation
`Parameter`s, i.e. **moving the claim from `echo_pred` to `pipe_pred` cost
ZERO assumptions**.  The three LEAF results (`init_cons_leaves_pipe`,
`init_cons_hit_pipe`, `sh_cons_console_pipe`) add
`FunctionalExtensionality.functional_extensionality_dep` — and that is
INHERITED, not this lane's: `Print Assumptions` on the FILE twin
`UInitConsFile.init_cons_leaves_file_of_leg` prints the IDENTICAL list, so
funext enters with `UkInit`/`UexecExecInst`'s leaf cone and any pipe
adequacy will carry it exactly as a file adequacy would.  Reported rather
than hidden.

**WHAT THE DESIGN GOT WRONG, OR PRICED WRONG.**

1. **THE RECORD'S LAWS ARE NOT "RE-DERIVED"; THEY ARE ECHO'S, APPLIED.**
   §5.6 prices PIPE-CLAIM as "the record's laws re-derived at `pipe_pred`
   (mould: `AppEcho`'s proofs)".  They are not re-derived and no proof text
   of `AppEcho`'s `EchoPred` section is transcribed.  The two claims differ
   in a factor that is PERSISTENT and names NO instance:

   ```coq
   pipe_pred γ r av ⊣⊢ echo_pred γ r av ∗ (echo_taint γ ∨ ⌜era0_cat_pins av⌝)
   ```

   so the transport's copy — which is at the SAME view — gets the factor for
   free, and `pipe_xfer` / `pipe_xfer_boot` / `pipe_taint_of_sup` /
   `pipe_init_*` are `AppEcho`'s lemmas with it framed.  The ONE genuinely
   new step is reading `era0_cat_pins` off the image, and that is one line
   (`FileFsPure.file_fs_era0`, which upstream landed for the FILE
   application and which `AppFileRec` already spends).  **The estimate to
   correct for any future application of this shape: a claim that adds a
   PERSISTENT, instance-free conjunct to another application's costs the
   split lemma and nothing else.**

2. **THE MOVING-VIEW LEGS ARE ONE LEMMA, NOT FOUR.**  `AppFile` needs a
   four-premise `file_step_free` and a per-leg case analysis because its
   claim carries a DEED whose row the step may be touching.  The pipe claim
   carries none, so `pipe_step_of_echo` — the echo-side move as a WAND (so a
   leg that spends the console KEY is the same lemma as one that spends
   nothing) plus the `file_fs_pure` preservation as a Prop — covers arm,
   unarm, the console's own create and a create elsewhere.

3. **CONJUNCT (g) NEEDS ONE SIDE CONDITION, NOT TWO.**
   `UInitCons.init_cons_laws_at`'s (g) carries
   `⌜d <> ROOTINO \/ nmn <> fname_f⌝` beside the console one; lane INIT-FILE
   added it because a device called `f` in the root refutes the FILE claim's
   deed conjunct at every deed value.  The pipe claim has no deed:
   `pipe_cons_create_other` discharges (g) at the first side condition alone
   and the bundle drops the premise on the floor.  Consequently the pipe
   bundles take NO `file_cons_create_leg`-style parameter — the record
   equation is their only one.

4. **THE UNARM AT THE ECHO READING NEEDS THE *ROW*, NOT THE ARM'S VIEW, AND
   THE BRIEF DID NOT NAME IT.**  `init_cons_laws_at`'s (e) hands over
   `⌜Pure av0⌝`, and the landed leaves fix (b) at `EchoFsPure.echo_fs_pure`
   — THREE pins — while `FileDeltas.file_fs_pure_unarm_fresh` wants all FOUR
   at the arm's view.  So the /cat pin cannot ride across that way.  What
   carries it is upstream `UInitConsFile`'s route: the unarmed row is the
   DEVICE the arm put there and every pinned row is a FILE, so the four pins
   ride across AT THE ROW and the arm's view is needed only to separate the
   ROOT.  The two pure steps are Σ-free and are re-proved here
   (`pipe_unarm_root`, `pipe_fs_pure_unarm_dev`) rather than imported, which
   would put the FILE application's whole u-tier cone in front of this leaf.

5. **PART 1's FINDING 8 IS HISTORICAL.**  PIPE-STAGE reported that
   `pipe_link_inst : LinkRec` was a lane of its own and that upstream had
   not paid it either — `grep file_link_inst` was empty and
   `FileLinksLine.v` did not exist.  Both landed in the meantime
   (`iris/FileLinksLine.v`, 2,081 lines; `iris/FileLinkInst.v`, 760), so the
   pipe instance is now a well-defined PORT of two existing files at
   `pending_at_p` / `pro_pin_p` / `proc_stream_p` / `pro_idx_p`, ~2,800
   lines, and not an open question.  Its LINE-MODEL fields are still free
   for the reasons part 1 gave (`lk_ab` needs no guard, `lk_pan`/`lk_exf`/
   `lk_noc` are literally `3`/`1`/`2`).

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  SH-PIPE-ROUND supplies
`AppPipe.pipe_laws`' only `Context` hypothesis, `Hprog` = `al_programs`
verbatim at `app_pipe`, and everything /init's console dance needs is now in
hand at ONE parameter: the claim equation
`file_app = MkAppcfg echo_names (pipe_pred γ) r`, which is what
`al_programs` itself hands over (checked by `AppPipe.pipe_app_pred_eq` /
`_names_eq` / `_boot_eq`, three `reflexivity`s).  At /init's first
instruction it holds `app_turn app_pipe c (S gen_id)` =
`EchoOut.eturn c (S gen_id)` — echo's five components, nothing added — and
`app_boot app_pipe c (S gen_id) r` = `AppEcho.echo_boot`, the console key or
the console flag.  For the exec of /cat it holds
`AppPipeCons.pipe_cat_pins_acc`: `era0_cat_pins av` at every view the claim
holds of, or the taint.

### CAT-PIPE (2026-09-18) — the round lands with ONE cursor and no `Hpin`, the entry's `cannot open` arm is REFUTED, and the read's `-1` is the one wall: a pipe read that was KILLED has no row to stand on

Branch `app-pipe/cat-pipe`, FIVE commits (`fcbfefc97`, `962342757`,
`7554b1cf9`, `4cab67a22`, `691350495`).  ONE new file
(`iris/UCatPipe.v`, ~1,200 lines) plus ONE line of `iris/_CoqProject`;
**no landed statement moved, and no landed file was edited at all**.
Whole `iris` tree `ec2-lane.sh cat build` **RC=0** (twice, the second with
nothing left to compile).  No `Admitted`; every result carries
`Proof using`.  `make audit-echo-only` UNMOVED at **fourteen** (the same
`PrimInt63`/`PrimString`/`resv_*`/`funext` set).  Nothing in the tree
`Require`s `UCatPipe.v`, so no audit cone reaches this lane.

**`Print Assumptions`.**  `pcat_urun_nopipe` and `pcat_round_test`:
*Closed under the global context*.  `pcat_round_at` and `pcat_ecall_read`:
`resv_matches`, `resv_is_valid` and `functional_extensionality_dep` —
THREE.  `pcat_pay_at_of_round`: the two reservation `Parameter`s.
`pcat_image_entry`: the fourteen, i.e. `UCatKernel.cat_image_entry`'s set
exactly.  The bar was "≤ `UCatKernel`'s": the entry MEETS it, and the
round's three are not a regression on `UCatKernel.cat_round_at`'s two —
that lemma takes the read as a PREMISE (`cat_held_read`) and walks no
leaf at all, while this round BUILDS the read; the file lane's
corresponding read builder, `UkCatDeed.kcat_r_of_deed`, carries all
fourteen.  So the pipe round is three where the file's is fourteen.

**WHAT LANDED** (`iris/UCatPipe.v`)

- §1, the pure stage: `pcat_line`, `pcat_out`, `pcat_stage`,
  `pcat_stage_{nonnil,last,nstarted,pin_snoc}`, `pcat_blk_{low,pending,byte}`,
  `pcat_alt`/`pcat_alt_of`/`pcat_alt_panic`, `pcat_round_line`,
  `pcat_acc_line`, `pcat_signed_small`.  `UCatOut.cat_stage`'s twin at
  `PipeOutPure`, ONE CONJUNCT SHORTER: a pipeline round reads no state, so
  there is no `s0`, no `fst_upto`, no `cat_tie`.  What replaces the file's
  `uline_of … = LCat` is `palt_ok (pcat_line I0) PRan`, which is `True` at
  an `LPipe` line and `False` at an `LEcho` one — the shape the write link
  asks for, for free.
- §2, the cursor: `pcatcs`, **`pcch`** (`turn ∗ ps_lb ∗ cs_lb ∗ inp_lb`, or
  the taint — `UCatOut.cch` minus `f0_lb`), `pcch_timeless`, `pcch_0_alt`,
  **`pcch_step`** at `PipeLinks.pipe_write_link_blk` / `pipe_write_link` /
  `pipe_write_link_taint`.
- §3, the read: **`pcat_ecall_read`** (the standard-slot pipe read leaf
  RE-PROVED at `UkRunSys.wp_uk_ecall_read_at`, see finding 1),
  **`pcat_rpost`** (the post's cat-facing reading, see finding 3),
  **`pcat_read_walk`** (`UkCatDeed.wp_kcat_read_deed`'s twin: `c.li a7,5 ;
  ecall ; c.jr ra`).
- §4, **`pcat_hold`**, **`pcat_round_inv`** and **`pcat_round_at`**.
- §5, **`pcat_urun_nopipe`**: kexit's whole per-descriptor close row for a
  table whose slot 0 is a pipe read end, out of `PipeProto.pipe_reg_of_inv`
  — design §2's claim mechanised at cat (a verified program that HOLDS A
  PIPE and is not tainted).
- §6, `pcat_hi` / `pcat_hi_len` / **`pcat_round_test`**, the consumer test
  at `L = "hi\n"`.
- §7, **`pcat_pay_at`**, **`pcat_image_entry`**, **`pcat_pay_at_of_round`**.

**THE TWO STATEMENTS, VERBATIM.**

```coq
  Definition pcat_hold (pn : pnames) (l : list fdstate) (c : nat) : iProp Σ :=
    (UserFd.ustd γfd l ∗ (rcur pn c ∨ T))%I.

  Definition pcat_round_inv (pn : pnames) (l : list fdstate) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (P : nat) : iProp Σ :=
    (∃ c : nat, pcat_hold pn l c ∗ pcch γ v ps0 cs0 I0 pcat_alt P c)%I.

  Lemma pcat_round_at (pn : pnames) (γp : pipe_names) (L : list (bv 8))
      (l : list fdstate) (wb : bool) (v : era_pins)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (P : nat) (Cend : iProp Σ) :
    pcat_stage ps0 cs0 I0 P ->
    pcat_out I0 = L ->
    l !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    pipe_inv pn γp L -∗
    □ (∀ gn : gname, ChildTok.kill_shot gn -∗ T) -∗          (* Hktaint *)
    □ (T -∗ UkCatCat.kcat_dg_cr N) -∗                         (* Hdg *)
    □ (∀ (c nb : nat) (rv : mword 64) (fbb : nat -> bv 8),    (* Hw *)
         ⌜rv = (mword_of_int (Z.of_nat nb) : mword 64)⌝ -∗
         (⌜(Z.to_nat (bv_unsigned rv) <= 512)%nat
           /\ forall j : nat, (j < Z.to_nat (bv_unsigned rv))%nat ->
                pcont (pcat_line I0) (palt_of pcat_alt) !! (c + j)%nat
                = Some (fbb j)⌝
          ∨ T) -∗
         UserFd.ustd γfd l -∗
         pcch γ v ps0 cs0 I0 pcat_alt P c -∗
         UkCat.kcat_wr N (mword_of_int 1) (mword_of_int CatSyms.buf) nb
           (ubytes γd CatSyms.buf 512 fbb)
           (fun wret : mword 64 =>
              (⌜wret = (mword_of_int (Z.of_nat nb) : mword 64)⌝
               ∗ UserFd.ustd γfd l
               ∗ pcch γ v ps0 cs0 I0 pcat_alt P
                   (c + Z.to_nat (bv_unsigned rv))%nat
               ∗ ubytes γd CatSyms.buf 512 fbb))) -∗
    □ (∀ c : nat,                                             (* Hend *)
         (eof_shot pn (take c L) ∨ T) -∗
         pcat_hold pn l c -∗
         pcch γ v ps0 cs0 I0 pcat_alt P c -∗ Cend) -∗
    cat_code γt -∗
    UkCatCat.kcat_round N (mword_of_int 0)
      (pcat_round_inv pn l v ps0 cs0 I0 P) Cend.

  Lemma pcat_image_entry (ws : list (list (bv 8))) (Mn : gmap Z (bv 8))
      (sv t : Z) (gn : nat -> bv 8)
      (sts : list fdstate) (cw : Z) (cs : gset gname) (pidv : mword 32)
      (Q : Z -> iProp Σ) (Pay : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    line_ok ws ->
    UShEcho.echo_node_img ws Mn sv t gn ->
    UkShEcho.echo_argv_bytes ws gn ->
    length sts = NOFILE ->
    length ws = 1%nat ->
    □ (∀ W' : uvis, ⌜uvis_fd W' = sts⌝ -∗ pcat_pay_at W' Q Pay) -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
```

**NEITHER STOP RULE FIRED, and both are answered at the statement.**

- **STOP 1 (`kcat_round`'s shape forcing a per-read OFFSET).**  It does
  not.  `UkCatCat.kcat_round` says NOTHING about offsets — the whole of
  what `UCatKernel` needs `Hpin`/`cat_held_read`/`Hold : nat -> iProp` for
  is that a FILE read runs at an offset the DESCRIPTOR records, so the
  payer must pin "the offset I read at is my console cursor".  A pipe row
  is `FdOpen rb wb (FdPipe γp)` and records none; the read pointer is
  `PipeProto.rcur`, ONE EXCLUSIVE PERMIT the reader holds, and the console
  cursor IS that number.  So `pcat_round_inv` has one existential and two
  resources at it, there is no `Hold`, no `cat_pinned_read_at`, no boxed
  row, and the vacuity trap `UCatKernel` documents (a box over `off0`, or
  over the cursor at a fixed handle) cannot arise.  **What `UkCatCat` pins
  is only the BUFFER** (`CatSyms.buf`, 512, at `a1`/`a2`) and the fd word
  at `a0`.
- **STOP 2 (the write link wanting the stage's `cs`/`I` reading).**  It
  does not: `⌜acc = take (length acc) (drop c L)⌝` — `pipe_rQ`'s pure
  conjunct — is ENOUGH.  `pcat_acc_line` turns it into `L !! (c + j) =
  Some (acc !!! j)` and `pcat_round_line` into the link's own premise
  `pcont (pcat_line I0) (palt_of pcat_alt) !! (c + j) = Some (gb j)`,
  because `pcont _ PRan` is `L ++ u_prompt` and the cursor never reaches
  the prompt.  There is NO lend to design here.

**WHAT WAS REFUTED / WHAT THE DESIGN AND THE BRIEF GOT WRONG (five, each
read at the statement)**

1. **`UkReadPipe.wp_uk_ecall_read_pipe_std` CANNOT BE USED AS IT STANDS,
   for two independent reasons, and the lane re-proves it (nothing in
   `UkReadPipe.v` moves).**  (i) **Its count premise is the WHOLE WORD**:
   it asks for `uint (m !!! a2) = Z.of_nat cap`, while what cat's own read
   obligation `UkCat.kcat_r` gives its payer is `bv_signed
   (subrange_vec_dec (m !!! a2) 31 0) = Z.of_nat cnt` — the low 32 bits,
   signed, with the upper half unconstrained.  The premise is NOT
   derivable, and it is not needed: the walk underneath
   (`UkRunSys.wp_uk_ecall_read_at`) takes the signed reading, and the leaf
   spends the unsigned one only to re-derive it through
   `uread_count_is_cap`.  (ii) **It drops the walk's NO-FAULT ROW.**
   `wp_uk_ecall_read_at` hands out `Hnf` (every byte of the destination is
   writable-mapped in any table the key's projection admits) and
   `uvis_lazy W = false`, and `UkReadRows.spost_at_read_elim` exhibits the
   post's own table `P` with the three facts `Hnf` wants — the pipe leaf's
   continuation relays NONE of them, and without them a caller cannot
   refute `PipeQueue.pipe_rstop_noobs`' COPY-OUT FAULT arm, which is one of
   the three ways a pipe read answers -1.  **For whoever next edits
   `UkReadPipe.v`: both are one-line relays at the leaf, and both would
   retire `pcat_ecall_read`.**
2. **THE READ'S `-1` IS THE LANE'S WALL, and it is a KERNEL ROW, not a
   design question.**  The brief says "the `-1` arms are the kill/taint
   arms as in `UCatKernel`"; at the FILE claim there ARE no -1 arms —
   `UkCatDeed.kcat_r_of_deed` relays lane OFF-LINK's count bound on BOTH
   arms, so `Z.to_nat (bv_unsigned rv) <= 512`, the signed reading is the
   unsigned one, and `bv_signed rv < 0` is a contradiction
   (`UCatKernel.cat_signed_small`).  At a pipe the bound is FALSE:
   `UkReadPipe.uread_pipe_ans` admits `r = -1` and
   `PipeQueue.pipe_rstop_noobs` has three arms that produce it.  Two are
   refutable and are refuted here: the COPY-OUT FAULT at the first byte
   (from the relayed no-fault row, finding 1) and the file layer's SIGN
   GUARD (`n = 0`, refuted at `cap = 512`).  The third — **the reader's own
   KILL SHOT** — is not: a pipe read really does answer -1 when the reader
   is killed asleep, and the only row in the tree that refutes a -1 from a
   read, `UexecRet.uexec_live_ok`, states it **for `FdDevice 1` alone**
   (its premise is `sts !! fd = Some (FdOpen true rb (FdDevice 1))`).  cat
   branches on exactly that word (`bltz a0,0x6a` → `cat: read error`), and
   the pipeline model has NO alternative that prints it — so the arm must
   be closed or the theorem is false.  **It is closed by a NAMED premise,
   `□ (∀ gn, ChildTok.kill_shot gn -∗ T)` — "a kill taints the
   application".**  That is the weakest thing that closes it and is what
   `design/applications.md` already says the taint IS (the application's
   kill price; `AppPipe.pipe_kill` is the echo taint).  It is NOT "nobody
   is ever killed", and the round stays true at a tainted era, where cat
   prints its diagnostic and the model says nothing.  **THE COORDINATOR'S
   CHOICE**, in the shape the campaign already uses for `pipe_both_law`:
   keep it as a hypothesis of the pipeline theorem and audit it as such, or
   buy the kernel row (the pipe twin of `uexec_live_ok`'s read clause,
   which is `usertrap`'s second `killed()` check — a process that RESUMES
   was not killed — and is stated for the console only because that is the
   only place anyone has needed it).  Beside it the round takes `□ (T -∗
   UkCatCat.kcat_dg_cr N)`, cat's `read error` tail at a TAINTED era; that
   one is an ordinary payer obligation (the free write law's route,
   `UkCatCat.kcat_round_of_law`) and not a wall.
3. **`PipeProto.pipe_rpost_img_line` IS TOO LOSSY FOR A PROGRAM.**  Its
   proof drops the post's IMAGE ROW — the one fact that turns the ghost
   `acc` into the caller's buffer function — and drops `length acc = d` on
   the non-observation arms, so a reader cannot say how many of its buffer
   bytes the call filled.  The round needs both (it writes exactly `r`
   bytes of the buffer), so the lane states `pcat_rpost`: the same reading
   with both kept and the four `pipe_rstop_noobs` arms sorted by what cat's
   loop BRANCHES ON — the answer is a count `d` (request met, ring
   observed empty, or a fault above the first byte), or it is -1 and then
   `d = 0` and one of three things happened.  `pipe_rpost_img_line` is not
   wrong; it is the right reading for `pipe_proto_test`'s question and the
   wrong one for a walk.  (Also: `pipe_rstop_noobs` is NOT pure — its kill
   arm carries `Rk` — so it must be destructed in the logic.)
4. **"The cursor is inside the line" IS FALSE AS A LEMMA**, and the round
   does not want it.  `take 0 (drop c L) = []` for EVERY `c`, so from
   `pipe_rQ`'s pure conjunct at `acc = []` nothing bounds `c` at all.  What
   the round needs and gets is a LOOKUP (`pcat_acc_line`: `L !! (c + j) =
   Some (acc !!! j)` for `j < length acc`), from which `c + j < length L`
   follows where it is used and nowhere else.  Consequently
   `pcat_round_inv` carries NO bound on its cursor — one conjunct fewer
   than `UCatKernel.cat_round_inv`, which needs `p <= length bs` for
   `ard_count`'s arithmetic.
5. **THE ENTRY IS CHEAPER THAN THE FILE'S, not merely different, and the
   `cannot open` arm is REFUTED rather than assumed.**  `pcat_pay_at` is
   `UCatKernel.cat_pay_at` minus FOUR things — the file name's three closed
   facts, the `arg_path_of` implication over every image, the cwd half and
   the persisted argument area — all of which exist only to resolve
   `argv[1]`.  The refutation is mechanised in `pcat_pay_at_of_round`:
   `UkCatMain.kcat_pay_all` is an ADDITIVE conjunction whose second arm is
   guarded on `2 <= length args`, `UShCat.cat_args` has `Z.to_nat
   (uvis_argc W)` entries (`echo_args_length`), and the key's own reading
   `UShCat.cat_key_args_holds` makes that number the NODE's word count —
   which sh built at ONE.  So the arm closes by `lia` and
   `UkCatMain.kcat_dg_open` is never mentioned.  `UShCat.cat_entry_run` is
   entirely argv-generic and needed no change.

**TWO TRAPS WORTH RECORDING** (both cost real time)

- **A standalone `ctokG` section variable makes `ChildTok.kill_shot` a
  DIFFERENT TERM.**  `UkReadPipe`'s post carries `kill_shot (uvis_gen W)`
  with `ctokG` resolved THROUGH the `xv6G` bundle; a `Context `{!ctokG Σ}`
  beside `xv6G` in the consumer gives a second instance, and the two
  propositions print identically and do not unify (`iSpecialize: cannot
  instantiate … with …`, the two sides byte-identical on screen).
  `UCatKernel` omits `ctokG` for exactly this reason and does not say so;
  this is the same trap as its documented `uexecSG`/`uprogSG` one.
- **A leaf that hands its caller an ABSTRACT `Rk : iProp` cannot be
  reasoned about at all.**  `pcat_ecall_read` binds the KILL GENERATION
  `gn` instead and puts `ChildTok.kill_shot gn` in the post, which is what
  makes finding 2's premise statable.

**THE ONE THING THE NEXT LANE NEEDS FIRST**

For **SH-PIPE-ROUND**: cat's side of the round is now `pcat_round_at` +
`pcat_image_entry`, and what sh must LEND the right child is exactly the
three things `pcat_round_inv` is built from — `pipe_inv pn γp L`,
`rtok pn` (`= rcur pn 0`) and the era's console credential at cursor 0,
`pcch γ v ps0 cs0 I0 pcat_alt P 0` (which is `turn v P ∗ ps_lb v ps0 ∗
cs_lb v cs0 ∗ inp_lb v I0`, the SAME five-minus-one components
`EchoOut.eturn` has, with `cs0` NOT yet extended — `pcch_0_alt` says the
alternative is not named until the first byte).  What comes back at cat's
exit is `pcat_hold pn l c ∗ pcch … c ∗ (eof_shot pn (take c L) ∨ T)`,
i.e. `PipeProto.pipe_payR`'s success arm beside the lease at the cursor;
sh's `pipe_round_reading` then reads `w = L` off it and echo's `pws_lb`.
sh still owes the round's two program-tier premises, `Hw` (its own
`UEchoOut.kecho_w_of_link_data`-shaped supply, at `pcch_step` — which is
landed) and `Hdg`; and it owes the OWNER's ruling on finding 2's
`Hktaint`.
