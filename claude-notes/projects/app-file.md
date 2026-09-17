# Project: the FILE application — `echo … > f`, power cycle, `cat f`

**STATUS: OPEN (started 2026-09-17).**  Design of record:
[`../design/app-file.md`](../design/app-file.md).  Read that first; this
file is only what is LEFT, lane by lane, and what each lane found.

The target: `App.xv6_app_adequacy` at `AppFile.app_file`, closed at the
literal image (`UFileBootAdequacy.file_adequacy_fileΣ`), with
`make audit-file-only` beside the echo and tree audits, and the
conclusion `FileDisc.file_phi`.

## Rules for every lane

- Build on the VM (`./gcp-rocq/run-on-gcp --check <file>` while
  iterating, `--proofs` before landing); never a local `make`.  Two
  builds in one remote tree race: lanes SERIALISE their `--proofs` runs
  (a lane may run `--check` at any time).
- No landed statement moves unless the lane says so here first.
  `AppEcho.v`, `EchoOut.v`, `AppInv.v`, `App.v` are read, not edited,
  except where a lane below names them.
- Every new result carries `Proof using`; the echo audit stays at 14 and
  the tree audit at 10.
- Report back: what landed (file, lemma), what was refuted and why, and
  the one thing the next lane needs first.

## Wave 1 — independent of the claim (run in parallel)

- [ ] **OFF-HAND** (kernel tier).  Design §3.  `FileInvDefs.fdstate_ok`
  stops pinning `OffParked`; the generic slot's mint takes
  `fdv_all_parked` of its key's table as a premise (sites: userinit at
  `fdt0`; fork's child — a generic parent's table is parked by its own
  premise, a verified parent parks first, `FdPark`; exec's taint arm —
  the U-tier exec leaf gains the premise and the caller parks); the open
  publish (`ProofSysOpenPub`) takes the mode from the deposit's open
  family (`off_pub_hand` at `hand`, unchanged at `park`); the three
  held-offset U-tier members: `UkRunSys.wp_uk_ecall_open_recv_img_held`
  (receipt at `FdInode i γo OffHeld`, `uoff γo 0` beside `ualloc`),
  `UkWriteFile.wp_uk_ecall_write_file_held` (the chain's fires at
  `off_supply_held`; `uoff` in, `uoff` at the advanced offset out on
  every arm, the `-1` arm advancing by what landed),
  `UkReadFile.wp_uk_ecall_read_file_held` (the R-c content row with the
  offset KNOWN: at `uoff γo off`, `d` bytes are `content[off..off+d)`,
  `uoff γo (off + d)` back).  Bar: every landed member's statement
  unchanged; echo audit 14; whole tree green.
- [ ] **SH-REDIR** (U tier, sh).  Design §5.1.  `UkShParseTok`/`Lex`: the
  `>` token; `UkShParseRedir`: the loop turns ONCE for ` > f`; `redircmd`;
  `UkShParseCmd`: `nulterminate`'s REDIR row; `UkShRun`: `ush_simple`
  admits `URedir (UExec _) file 0x601 1` at the top, and the REDIR arm —
  `close(1)` at the ledger, the `open` as a CALL PREMISE (a lemma
  parameter shaped like `wp_uk_ecall_open_recv_img_held`'s conclusion,
  at the ledger `[c; closed; c]`), the `open %s failed` tail through
  `UkShDiag` (a third `ush_diag_leaf` site), the recursion into the EXEC
  arm; `UkShFork.ushf_lexable` grows the shape.  Bar: the existing
  simple-line theorems unchanged; the new walk stated at an abstract
  open premise so it compiles before OFF-HAND lands.
- [ ] **CAT-PIN** (mechanical).  `iris/FsCatPin.v` = `FsEchoPin.v` at
  cat's inum and `ElfUser.cat_elf` (`FsImgCheck` gains `fname_cat` and
  the two `vm_eq`s); `iris/FileFsPure.v`: `file_fs_pure av :=
  echo_fs_pure av /\ era0_cat_pins av`, `era0` from the image;
  `FsImgCheck.fsimg_root_no_f` (the root's entry map has no `f`, stated
  on `TreeImg.img_root_blk`'s constant reading — user-tree.md §8.1's
  cost rule).  Bar: `Closed under the global context` but the
  PrimString primitives; no landed file's statement moves.
- [ ] **MODEL** (pure).  `iris/FileDisc.v` at design §1's definitions
  VERBATIM (the designer's; a lane that finds a definition wrong reports
  it, it does not fix it): `uline`, `line_bytes`, `parse_line` and its
  inverse laws, `disc_input_f` (prefix-closed, decidable, the snoc laws
  `EchoDisc` has), `echo_chunks`, `subseq`, `sel_ok`, `fst`, `fcontent`,
  `ralt` with its `nat` encoding and `ralt_ok`, `fsm`, `cont`, `sessf`,
  `fst_after`, `fadm_boot`, `good_out_f`, `disc_f`, `file_phi`; the
  determinacy `sessf_prefix_det` (the twin of
  `EchoOutPure.sess_prefix_det`, which is what the stage spends); five
  `vm_compute` demos including the echo/power-off/cat transcript and a
  crash mid-round.  Bar: `Closed under the global context`.

## Wave 2 — the claim and the suppliers (after wave 1; the designer writes `AppFile.v`'s definitions first)

- [ ] **APP-CLAIM**: `iris/AppFile.v` — `file_fixed`, `file_names`,
  `f_state`, `file_pred`, the transport (commit and boot, design §2),
  `file_boot`, era 0 at the image, the record `app_file` with every
  `xv6_app_laws` field but `al_programs` (echo's re-instantiated at the
  projections, the ledger and tag grown by §4), the taint/supply lemmas.
- [ ] **F-OPEN**: the child's open supplier from the deed
  (`TreeMove.tree_open_create_au` / `UInitCons` mould): the create arm at
  `None`, the exists+truncate arm at `Some _`, both at a length-0 prefix,
  and the U-tier corollary on the held-offset open leaf — three arms:
  fd 1 on the node with the deed at `Some []` and `uoff γo 0`; `-1`
  with the deed unchanged; `-1` with the deed at `Some []` (created,
  then `filealloc` failed).
- [ ] **ECHO-FILE**: `iris/UEchoFile.v` (design §5.2).
- [ ] **CAT-ENTRY**: `iris/UCatKernel.v` + `iris/UCatOut.v` (design §5.3).
- [ ] **STAGE**: `EchoOut`/`EchoOutPure` grown by `o_fh` and the line
  shapes (design §4); the ledger's line list and the tag's lb; `al_pow`'s
  seed; `Hphi` at `file_phi`.
- [ ] **SH-ROUND**: sh's fork lends the deed, the exit payload returns
  it, the prompt link records `o_fh`; `UShCat`; the dispatch on the
  line's shape; the REDIR child's proof at the claim (the open premise
  instantiated, the taint arm parks).
- [ ] **ADEQUACY**: `iris/UFileBootAdequacy.v`, `iris/FileAssumptions.v`,
  `make audit-file{,-only}`; the design page's §0 rewritten as landed.

## Findings (append as lanes report)

### SH-REDIR (2026-09-17) — runcmd's REDIR arm landed; the parser did not

Branch `app-file/sh-redir`.  Whole tree green on the lane's remote tree;
`make audit-echo-only` still FOURTEEN; no landed sh statement moved (the
diff is three NEW files plus three lines of `iris/_CoqProject`).

**WHAT LANDED.**

`iris/UkShRedir.v` (new, immediately after `UkShDiag.v`):

- `ush_top` — the scope ONE level wider than `UkShRun.ush_simple`:
  `ush_top (URedir c1 _ _ _) := ush_simple c1`, and `ush_simple c`
  otherwise.  `ush_top_not_redir` bridges back.
- `wp_kshx_close_std` — sh's `close` stub (0xcae / 0xcb0 / 0xcb4) driven
  at the LEDGER (`UkRunSys.wp_uk_ecall_close_std`).  `UkSh.wp_ksh_close`
  spends a TAIL handle (`UserFd.ufd`) and is the wrong shape here: what a
  REDIR shuts is a STANDARD stream, which only the ledger can name.
- `ush_open_ans` / `ush_open_call` — the open as a CALL PREMISE (below).
- `wp_kshr_redir_arm` — the eight instructions 0xf6..0x10c
  (`c.lw a0,36(a0)` = rcmd->fd; `jal close`; `c.lw a1,32(s1)` = rcmd->mode;
  `c.ld a0,16(s1)` = rcmd->file; `jal open`; `bltz a0,0x10e`;
  `c.ld a0,8(s1)` = rcmd->cmd; `jal runcmd`), with the RECURSION as its
  CONTINUATION: it hands its caller the run back at `runcmd`'s own entry
  pc, the sub-tree, the ledger the open left, and the application's
  receipt `K ty`.  That is the form the application lane wants, because it
  can then carry `K ty` into its OWN EXEC walk (`UkShEcho.v`, where the
  pinned exec supply is nameable) instead of dropping it.
- `wp_kshr_runcmd_redir` — that arm with `UkShDiag.wp_kshr_runcmd_final`
  supplied for the subtree.  Claim-free, so it drops `K ty`.

`iris/UkShRedirLex.v` (new, after `UkShParseCmd.v`): `ushp_find_some`,
`ushp_peek_res_hit`, `ushp_T_redir_gt` / `ushp_T_redir_lt` (the two bytes
of the table at 0x12f0, read off the dump), `ushp_peek_redir_hit`,
`ushp_gt_is_sym`.

`iris/UkShRedirTok.v` (new): `wp_kshp_gtk_disp_gt` — gettoken's `>` switch
arm, 0x356 / 0x35a / 0x35e / 0x362 → 0x3ca / 0x3ce / 0x3d2 (the `>>`
LOOKAHEAD) / 0x3d6 / 0x3da / 0x3de / 0x3e0 / 0x3e2 → 0x388.  It lands on
0x388, which is exactly where `UkShParseTok.wp_kshp_gtk_disp`'s NUL arm
lands, so gettoken's tail (the `eq` write, the trailing blank scan, the
epilogue) is the SAME code in both and a whole-gettoken lemma for the
redirect shape is this lemma plus that tail.  The `>>` arm (0x42a,
`ret = '+'`) is refuted from "the byte after the `>` is not another one",
which is design §5.1's canonical redirect.

**ALREADY DONE BEFORE THIS LANE — DO NOT REDO.**

1. `UkShRun.ush_cmd`'s `URedir` row already describes all five fields (the
   sub-tree pointer at t+8, the file pointer at t+16, the file string, the
   mode word at t+32, the fd word at t+36), and `ush_cmd_redir`,
   `ush_cmd_forkable` and the `Persistent` instance already cover it.  The
   brief's "`ush_cmd` describes the REDIR node's fields" was landed.
2. `UkShRun.ush_diag_at` and `ush_diag_res` already name **0x10e** as a
   site, and `UkShDiag.ush_diag_leaf_holds` already WALKS it
   (`iris/UkShDiag.v:8546`, "0x10e: open %s failed").  The brief's "a THIRD
   `ush_diag_leaf` site … find the pc in the catalog" was landed; all this
   lane had to do was reach it.
3. `UkShParseLex.wp_kshp_peek` carries NO `ushp_no_symbols` — its answer is
   the computed `ushp_peek_res len f k tlen tf`.  So peek's `"<>"` TABLE HIT
   is a PURE lemma (`ushp_peek_redir_hit`), not a walk.  Only
   `ushp_peek_res_sym` (the miss) existed; the hit is the mirror image.

**REFUTED / STALE IN THE BRIEF.**

- **"`ush_simple` admits `URedir (UExec _) _ _ _` at the top of a tree (and
  nowhere deeper)" cannot be an edit to `ush_simple`.**  It is a structural
  `Fixpoint`, so "at the top and nowhere deeper" is not expressible in it;
  and widening it in place would silently strengthen
  `UkShRun.wp_kshr_runcmd`, whose proof has no ledger to spend on the arm.
  Landed as the layered `ush_top` instead, with every landed statement
  untouched.  The design page's §5.1 should say `ush_top`, not
  "`UkShRun.ush_simple` admits".
- **`UkShFork.ushf_lexable` IS GONE** — deleted by lane SH-LINE 2b (L3);
  `iris/UkShFork.v:1064` records the deletion and why ("it said every line
  the user could type lexes, and it is FALSE").  What stands in its place
  is `UkShLoop.ush_line_lexable` (a `Prop`: every admissible line has NO
  symbol byte and fewer than ten tokens) together with `UkSh.ush_rest_line`
  / `UkSh.ush_line_is`.  `ush_line_lexable` is consumed as a PREMISE
  (`UkShFork.ushf_rest_of_body`, `UkShMain`), so it cannot simply "grow":
  weakening its conclusion to a disjunction (the no-symbols shape ∨ the
  redirect shape) forces every consumer to case-split, i.e. the child walk
  (`UkShMain.wp_kshm_child` / `_child_alloc`) has to be re-stated for both
  shapes.  **That is deliverable 5 and it is BLOCKED on the parser
  theorem**, not on effort in this lane: there is nothing to case-split on
  until `parsecmd` produces a `URedir` node.
- **The fd word is PINNED to 1** in the landed walk
  (`ush_cmd (ukn_d N) t (URedir c1 file mode 1)`), because `close(1)` is
  what makes the allocation land on slot 1 and the ledger premise is stated
  at slot 1.  The mode is left general with `0 <= mode < Z31` (0x601 is an
  instance), and the file name is an arbitrary `uarg`, so the walk IS
  stated "at any one-token file name" as the brief asked.

**NOT LANDED, with the cost of each (this is the rest of SH-REDIR).**

- `parseredirs` turning ONCE (0x502..0x572 on the `>` path: ~24 new
  instructions, two `gettoken` calls, two `peek` calls, one `redircmd`
  call) — needs a whole-`gettoken` lemma first (below).
- **A whole `gettoken` for a line WITH a symbol.**  This is the linchpin
  and it is pure re-walking: `UkShParseTok.wp_kshp_gettoken` carries
  `ushp_no_symbols len f` and the redirect line falsifies it, so BOTH
  gettoken calls in `parseredirs` (the one that returns `'>'` and the one
  that returns `'a'` for the file name) need a new lemma.  The good news:
  `wp_kshp_ws_scan` and `wp_kshp_tok_scan` are already general (no
  `ushp_no_symbols`), and so is `wp_kshp_peek`; only the DISPATCH used the
  premise, and `wp_kshp_gtk_disp_gt` above is the missing third arm.  The
  work is a generalised dispatch (three arms: NUL → 0x388 with s5 = 0;
  non-symbol non-NUL → 0x3ec; `>` → 0x388 with s5 = 62 and s1 advanced) and
  ONE re-walk of gettoken's frame and tail (~35 hand instructions:
  0x310..0x34e, 0x388..0x3c8).
- `redircmd` (0x200..0x21e, `malloc(sizeof)` + `memset` + six field
  stores).  **It is NOT in any catalog**: `tools/ucode_shp.txt` lists it as
  `skipfunc redircmd` ("reached only from parseredirs' switch … excluded by
  `ushp_no_symbols`").  Landing the walk means turning that line into
  `func redircmd` and re-running `make gen-ucode` / `check-ucode` — a
  coverage change is an edit to the SPEC, never to the output
  (design/code-organization.md).  Do NOT add the rows before the walk
  exists: an `uinstr` fact for code no proof fetches is exactly what that
  spec file forbids.
- `parseexec`'s loop calling `parseredirs` after the last word, the
  resulting `URedir (UExec args) file 0x601 1`, `nulterminate`'s REDIR row,
  `parsepipe` / `parseline` / `parsecmd` and the parser theorem.  All of
  these are `ushp_no_symbols`-scoped today, so each needs a NEW lemma in a
  NEW file (the bar forbids moving the landed ones), and the pure
  vocabulary needs a token model that admits ONE symbol.

**THE `Hopen` SHAPE, VERBATIM — this is what the next lane instantiates.**

```coq
Definition ush_open_ans (N : uk_names Σ) (l : list fdstate)
    (K : fdtype -> iProp Σ) (r : mword 64) : iProp Σ :=
  ((∃ ty : fdtype,
      ⌜ r = (mword_of_int 1 : mword 64) ⌝ ∗
      UserFd.ustd (ukn_fd N) (<[1%nat := FdOpen false true ty]> l) ∗ K ty)
   ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗
      UserFd.ustd (ukn_fd N) l))%I.

Definition ush_open_call (N : uk_names Σ) (cwdv file mode : Z)
    (l : list fdstate) (K : fdtype -> iProp Σ) : iProp Σ :=
  (∀ (h : CpuId) (m : regfile) (av : nat),
     ⌜ m !!! Regidx a0_idx = (mword_of_int file : mword 64) ⌝ -∗
     ⌜ m !!! Regidx a1_idx = (mword_of_int mode : mword 64) ⌝ -∗
     shk_code (ukn_t N) -∗
     UserCwd.ucwd (ukn_cwd N) cwdv -∗
     UserFd.ustd (ukn_fd N) l -∗
     urun N h m (mword_of_int ShSyms.open) av -∗
     (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
        ⌜ ucallee_saved m m' ⌝ -∗
        ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
        UserCwd.ucwd (ukn_cwd N) cwdv -∗
        ush_open_ans N l K r -∗
        urun N h' m' (ret_pc (m !!! Regidx ra_idx)) av -∗
        WP (Loop : expr riscv_lang)) -∗
     WP (Loop : expr riscv_lang))%I.
```

It is stated at sh's `open` STUB ENTRY (`ShSyms.open` = 0xcc6), not at the
`ecall`, so the supplier owns the whole three-instruction stub — that is
what makes the walk claim-free.  `l` is the ledger with slot 1 ALREADY
CLOSED, i.e. `<[1%nat := FdClosed]> ld` for the walk's own `ld`; the walk
proves that half itself from `wp_kshx_close_std`, so F-OPEN never has to
reason about the close.  The cwd goes in and comes back unchanged (open is
not `chdir`), and it is there because that is what
`UkRunSys.wp_uk_ecall_open_recv_img`'s pinned bundle is stated at.

`K : fdtype -> iProp Σ` is deliberately ABSTRACT and deliberately indexed
by the row's type: the held-offset variant
(`wp_uk_ecall_open_recv_img_held`, lane OFF-HAND) is instantiated by
choosing `K ty := (the deed at `Some []` ∗ UserOff.uoff γo 0 ∗ …)` — the
offset lives INSIDE `K ty`, so `ush_open_call` does not have to be
restated when OFF-HAND lands.  The success arm's `r = 1` and the
`<[1 := FdOpen false true ty]>` are what `UserFd.ualloc` gives at a ledger
whose lowest closed slot is 1 (design/user-fd.md §2); F-OPEN discharges
them by `fd_lowest_closed` arithmetic on a three-element list.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**

For the APPLICATION side (F-OPEN / SH-ROUND): nothing from this lane is
missing — instantiate `ush_open_call` and use `wp_kshr_redir_arm` (not
`wp_kshr_runcmd_redir`, which drops the receipt) so that `K ty` reaches
your own EXEC walk.  The premise compiles today, before OFF-HAND lands.

For the rest of SH-REDIR: **the generalised `gettoken`** — the three-arm
dispatch plus one re-walk of gettoken's frame and tail.  Everything else in
the parser chain (peek, both scans, `parseredirs`' frame, `parseexec`'s
argument loop) is either already general or a mechanical re-walk that
cannot start until a `gettoken` exists that returns something other than
`'a'` and `0`.

### SH-PARSE (2026-09-17) — the redirect line's LEXER lands; the parser chain above `parseredirs` does not

Branch `app-file/sh-redir`, four commits on top of SH-REDIR's.  Whole
tree green on the lane's remote tree; `make audit-echo-only` still
FOURTEEN; `make check-ucode` green (the catalog moved, and it moved
because its SPEC did); every landed sh STATEMENT unchanged.

**WHAT LANDED.**

`iris/UkShParseSym.v` (new, pure, after `UkShParse.v`) — the line model.

- `ushs_one len f o` — every symbol byte of the line is at `o`, and the
  byte there is `'>'`.  `ushs_one_none : ushs_one len f None <->
  ushp_no_symbols len f`, BOTH DIRECTIONS: stage 4's landed premise is
  this model's symbol-free instance, not a parallel development.
- `ushs_redir len f p e` — design §5.1's canonical shape: one blank each
  side of the `'>'` at `p`, one word `[p+2, e)`, blanks to the end.
- the scan measures at that shape: `ushs_skipws_after_gt` (one blank),
  `ushs_toklen_file` (the file name's length), `ushs_skipws_tail`,
  `ushs_skipws_at_gt`, `ushs_toklen_at_gt`.
- `ushs_toks len f stop off toks` — `UkShParse.ushp_tokens` with the
  TERMINATOR as a parameter, and `ushs_toks_tokens` / `ushp_tokens_toks`
  the `stop = len` instance.  **This is not a convenience.**
  `ushp_tokens` has NO INHABITANT on a line whose symbol byte is
  reachable: its `Cons` needs `0 < ushp_toklen`, which is 0 at a symbol,
  and its `Nil` needs the blank scan to reach `len`.  So a redirect
  line's ARGUMENT tokens are not `ushp_tokens` of anything, and every
  loop invariant above `parseredirs` has to be re-stated at `ushs_toks`.
- `ushs_gettok_res / _end / _fin` — gettoken's answer at one symbol, with
  `ushs_gettok_res_nosym` / `_end_nosym` proving the landed
  `UkShParseTok.ushp_gettok_*` are their symbol-free instances.
- `ushs_gt_ok len f` — the ONLY thing gettoken needs to know about the
  line (every symbol byte is a `'>'` that is neither last nor doubled),
  with both line shapes shown to satisfy it.

`iris/UkShRedirGtk.v` (new) — **THE GENERALISED gettoken**, the linchpin
SH-REDIR named.

- `wp_kshp_gtk_disp_ns` — the switch at a cursor whose byte is not a
  symbol.  `UkShParseTok.wp_kshp_gtk_disp` carries `ushp_no_symbols len f`
  and USES it in exactly ONE LINE of its 460 (to know the byte AT THE
  CURSOR is not a symbol); everything else was already general.  So this
  is that walk at the premise it actually needs, and the landed lemma is
  its instance.  **That one-line-of-460 shape recurs** — see
  `wp_kshp_parseredirs_ns` below, and expect it at `parseexec`,
  `parsepipe` and `parseline` too.
- `wp_kshp_gettoken_sym` — gettoken end to end at `ushs_gt_ok`, a
  THREE-WAY case on the byte at the blank-scanned cursor: the NUL arm,
  the `'>'` arm (through SH-REDIR's landed
  `UkShRedirTok.wp_kshp_gtk_disp_gt`), and the default arm.  All three
  land on 0x388, so `wp_kshp_gtk_388` / `wp_kshp_gtk_fin` are walked once.
  The whole file compiles in ~10 s.

`iris/UkShRedirCmd.v` (new) — `wp_kshp_redircmd`, 0x200..0x25e.  An
eight-word frame (gettoken's, instruction for instruction, so
`wp_kshp_frame_pro` / `_epi` drive both ends), `malloc(40)` through
`ushp_malloc_ok`, `memset` across the `shp_code`/`shk_code` bridge, and
seven field stores that build `ushp_tree`'s REDIR node with the sub-tree
carried IN and handed back.  The NULL arm is `execcmd`'s: `redircmd` does
not test malloc's answer either.  `ushp_nth_byte_32_64` is the one pure
fact the two `sw`s need (the struct's `int` fields are `mword 32` and the
register is 64 bits).

`tools/ucode_shp.txt` — `skipfunc redircmd` becomes `func redircmd`, and
`iris/UCodeShP.v` is the REGENERATED output (564 → 603 instruction
facts).  Two consequences worth knowing before the next coverage change:
`shp_syms_pins` gains a twelfth conjunct, so `UkShParse.shpp_strlen` /
`shpp_strchr` each take one more underscore in their `destruct` pattern
(their STATEMENTS are untouched); and `make check-ucode`'s second half is
`git diff --exit-code`, so it can only pass after the regenerated catalog
is COMMITTED.

`iris/UkShRedirPr.v` (new) — `wp_kshp_parseredirs_gt`, **parseredirs
turning ONCE**, and `wp_kshp_parseredirs_ns`, parseredirs at zero turns on
a line whose `'>'` is somewhere else.

- the one-turn walk is the `'>'` `gettoken` (both out parameters NULL),
  the file-name `gettoken` (with `&q` / `&eq` — the first walk in the
  parser that uses its own frame's LOCALS), the three-way switch (the
  `'a'` test and the `'<'` test refuted, the `'>'` test taken),
  `redircmd(cmd, q, eq, 0x601, 1)`, and the SECOND `peek`, which answers 0
  because the cursor has reached the end of the line.  It returns
  `ushp_tree s0 t (UshpRedir c (S (S p)) e 1537 1)`.
- `wp_kshp_frame_pro_at` is why there is a second prologue lemma here, and
  this is the lane's one real surprise: **`UkShParse.wp_kshp_fp`
  quantifies the new frame pointer UNIVERSALLY.**  That is enough for
  every landed caller and not enough for any walk that touches its own
  LOCALS, because `q` and `eq` live at `s0-104` / `s0-112` while what the
  walk owns is the stack at `sp0`.  `wp_kshp_frame_pro_at` is
  `wp_kshp_frame_pro` with the frame pointer at its value and nothing else
  changed.  Any later walk with locals (`parseexec` has four) needs it.
- the extra stack depth the locals need is read off `urun`'s OWN budget
  (`urun_stack` at the post-prologue run), not assumed: the prologue only
  exposes `8 * k <= uint sp0`, which at `k = 14` gives `uint sp0 >= 112`
  and leaves `0 < uint sp0 - 112` UNPROVABLE.

`iris/UkShRedirLine.v` (new, pure) — the line-level half, and the
refutation below.

**REFUTED — and this is deliverable 5's shape, not an effort estimate.**

**`UkShLoop.ush_line_lexable` cannot become a disjunction.**
`ushs_line_is_nosym` proves it: a line `UkSh.ush_line_is ws f k len`
describes NEVER carries a symbol byte, because `ush_line_is` carries
`EchoDisc.line_ok ws`, hence `LineWords.wl_wf ws`, hence every buffer byte
is alphanumeric, a blank or the newline (`LineWords.wl_line_byte_val`).
Weakening `ush_line_lexable`'s CONCLUSION to "no symbols ∨ redirect shape"
therefore adds a right disjunct unreachable from its own premise: every
consumer would case-split on something that cannot happen, and the
redirect arm of `wp_kshm_child` would be vacuous.  (Same lemma also shows
`ush_line_lexable`'s first conjunct is derivable, not assumed.)

What replaces it is a SECOND line predicate, `ushs_line_is ws file f k
len`, positional exactly as `ush_line_is` is (the words of `ws`, one
blank, the `'>'`, one blank, the file name, the newline), with
`ushs_line_is_redir` the bridge to `ushs_redir` at `p = |wl_body ws| + 1`
and `e = |wl_body ws| + 3 + |file|`.  A widened `ush_line_lexable` is
`ush_line_lexable ∧ ush_line_lexable_redir`, the second quantified over
`ushs_line_is` — and the CHILD then has two lemmas, not one arm.

**NOT LANDED, and why.**

- **`parseexec`'s argument loop, `nulterminate`'s REDIR row,
  `parsepipe` / `parseline` / `parsecmd`, the parser theorem** (the
  brief's deliverable 4).  Not blocked by a design fact — it is five
  re-walks, ~3 500 lines, and the pieces they need are now all in place.
  Two of them are the cheap "one line of N" shape
  (`wp_kshp_parseredirs_ns` is already landed; `parsepipe` and
  `parseline` refute their peeks the same way).  Two are real:
  `wp_kshp_pex_loop` must be re-stated at `ushs_toks len f p 0 args` with
  the LAST round's `parseredirs` turning (its invariant is
  `ushp_exec_pre s0 p done` ∗ `ushp_tokens len f cur rest` today, and the
  tokens half is the part that has no inhabitant on this line), and
  `nulterminate`'s REDIR row is NEW CODE, not a premise change: the
  jump-table dispatch to case REDIR, the RECURSION into the sub-tree
  (hence an induction on `ushp_cmd`), and the NUL store at `efile`.
- **the child walk at the redirect shape** (deliverable 5).  BLOCKED on
  the parser theorem, exactly as SH-REDIR predicted: `wp_kshm_child` takes
  `ushp_no_symbols len f` and `ushp_tokens len f 0 toks` as PREMISES and
  calls `UkShParseCmd.wp_kshp_parser`, which does not exist at the
  redirect shape.  Its statement at the redirect shape is
  `UkShMain.wp_kshm_child` with those two premises replaced by

  ```coq
      ushs_redir len f p e ->
      ushs_toks len f p 0%nat args ->
      (length args < 10)%nat ->
  ```

  (everything else — `Hmalloc`, `sh_deps`, `shk_code`, `uxsup_at`, the
  kill credential, the three `ustr`s, `ustd`, `ucwd_any`, `uch_any`,
  `UMalloc`, the run at 0x9c0 — verbatim), PLUS one new premise, the open
  as a call:

  ```coq
      UkShRedir.ush_open_call N cwdv (s0 + Z.of_nat (S (S p)))
        (1537 : Z) (<[1%nat := FdClosed]> ld) K -∗
  ```

  and, inside, `UkShRedir.wp_kshr_redir_arm` in place of
  `UkShRun.wp_kshr_runcmd` at the top node, with the receipt `K ty`
  carried into the walk's own EXEC arm rather than dropped.
  `wp_kshm_child_alloc` is the same edit one level up.  **THE APPLICATION
  LANE INSTANTIATES `ush_open_call` AND NOTHING ELSE** — SH-REDIR's shape,
  verbatim, still compiles; `K ty` is where the held offset goes when
  OFF-HAND lands, so neither premise has to be restated then.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**

`wp_kshp_pex_loop` at `ushs_toks`.  Everything under it is landed —
`wp_kshp_gettoken_sym` answers `'>'`, `'a'` and 0; `wp_kshp_parseredirs_ns`
is the zero-turn call after each ordinary token; `wp_kshp_parseredirs_gt`
is the one turn after the LAST one — and everything above it
(`parsepipe`, `parseline`, `parsecmd`, the theorem) is mechanical once the
loop's invariant is stated at a terminated token list.  Start by copying
`UkShParseExec.wp_kshp_pex_loop` into a new file, replacing
`ushp_tokens len f cur rest` with `ushs_toks len f p cur rest` and
`ushp_no_symbols len f` with `ushs_redir len f p e`, and expect the two
`parseredirs` call sites to be the only places the proof text really
changes.  Use `wp_kshp_frame_pro_at`, not `wp_kshp_frame_pro`:
`parseexec` has four locals.
