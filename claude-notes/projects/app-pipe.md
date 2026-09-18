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
