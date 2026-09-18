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
- [x] **SH-PARSE-PIPE** (U tier, sh's parser, design §5.1).  LANDED IN PART
  (the lexer whole, the node and `nulterminate`'s PIPE row, the loop's
  exit at the `|`); the parsepipe turn STOPPED at its brief's stop rule —
  see the findings block.  Mould:
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

### SH-PARSE-PIPE (2026-09-18) — the pipe line's LEXER lands whole and its LEXABILITY is a theorem; what is left of the parser is TWO RE-STATEMENTS, and the one instruction nobody had walked is landed

Branch `app-pipe/sh-parse-pipe`, SEVEN commits (`d17064949`, `16cc644da`,
`6ed408fc8`, `0a2de5b53`, `9ba83f6a1`, `cb0a796c3`, `9c78e50fa`).  Whole
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
  turns on) and **`wp_kshp_pex_bar`**, the argument loop's exit at the `|`.

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
   `ushs_toks len f p 0 args` and `ushq_nosym_from len f 0`… with
   `wp_kshp_pex_bar` closing the last round.  No instruction of it is
   undiscovered (finding 5).
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
