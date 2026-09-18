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
- [x] **SH-PIPE** (U tier, sh's `runcmd`, design §5.1) -- LANDED, see Findings.  NEW `iris/UkShPipe.v`:
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
