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
  tree audit at 10, the system audit at 13.
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
- [x] **PIPE-REG** (U tier, design §2) — LANDED (see Findings).  New `iris/PipeReg.v`: `pipe_reg γp
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
- [ ] **PIPE-MODEL** (pure, design §1).  `iris/PipeDisc.v` at §1's
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
- [ ] **PIPE-STD** (U tier, design §5.4).  `UkReadPipe.wp_uk_ecall_read_pipe_std`
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
