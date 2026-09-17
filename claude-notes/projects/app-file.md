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

### SH-PARSE-2 (2026-09-17) — the parser chain above `parseredirs`, the parser theorem, and the child at the redirect shape

Branch `app-file/sh-redir`, on top of SH-PARSE's.  Whole tree green on the
lane's remote tree; `make audit-echo-only` still FOURTEEN; `make
check-ucode` green (the catalog did not move — this lane fetches no new
function); every landed sh STATEMENT unchanged.

**WHAT LANDED**, in the order the brief named it.

`iris/UkShParseSym.v` §7 (added): the three readings of `ushs_toks` the
argument loop turns on (`ushs_toks_nil_inv` / `_cons_inv'` / `_skip`,
plus the two constructors in applied form), gettoken's answer at an
ordinary word (`ushs_gettok_res_word` / `_end_word`, `_end_stop`,
`_fin_stop`), and `ushs_toklen_pos_nosym` / `_nows` — a token of positive
length starts at a byte that is neither blank nor symbol, which is what
makes every peek in the chain miss.

`iris/UkShRedirEx.v` (new) — **the argument loop**.

- `wp_kshp_pex_end` — the round that finds the line exhausted (peek 0,
  gettoken 0, `c.beqz` out to 0x662).  It touches NEITHER the node nor
  s1/s2/s3, so it is stated over none of them, and both arms of the loop
  reach it.
- `wp_kshp_pex_loop_gt` — `UkShParseExec.wp_kshp_pex_loop` at
  `ushs_redir` / `ushs_toks`.  **The turn is the LAST round's
  `parseredirs`, not a round of its own**: sh calls `parseredirs` after
  every argument, all of those calls but the last sit on an ordinary word
  (`wp_kshp_parseredirs_ns`) and the last sits on the '>'
  (`wp_kshp_parseredirs_gtn`).  So the induction is over a NON-EMPTY
  token list, the `Nil` goal is refuted from that premise, and the `Cons`
  goal splits on the tail — the two arms differing only in which
  `parseredirs` closes the round.

`iris/UkShRedirPex.v` (new) — `wp_kshp_parseexec_gt`.  Three lines of
`UkShParseExec.wp_kshp_parseexec`'s 1400 differ: the `peek(ps,es,"(")` is
refuted from the byte AT THE CURSOR rather than from the whole line, the
`parseredirs` before the loop sits on the first word and does nothing,
and the loop is the redirect one.

`iris/UkShRedirNul.v` (new) — **nulterminate's REDIR row**.  Four
instructions (0x832 `c.ld a0,8(a0)`, 0x834 `jal nulterminate`, 0x838
`c.ld a5,24(s1)`, 0x83a `sb zero,0(a5)`) and then the same 0x83e tail the
EXEC arm falls into, so `UkShParseCmd.wp_kshp_nul_fin` closes both.
Everything ABOVE the switch is the same walk at a different type word: 2
instead of 1, so the jump table is indexed at 0x13b8 rather than 0x13b4
and the row there sends control to 0x832 rather than 0x81a.
`ushp_jrow_redir` is those four .rodata bytes, read off the image.

`iris/UkShRedirCm.v` (new) — `wp_kshp_parsepipe_gt`, `wp_kshp_parseline_gt`.
`iris/UkShRedirPc.v` (new) — `wp_kshp_parsecmd_gt` and **the parser
theorem `wp_kshp_parser_redir`**.
`iris/UkShLoop.v` — `ush_line_lexable_redir` (below).
`iris/UkShRedirSeam.v` (new) — `ushs_toks_below` (the truncation),
`ush_cmd_of_ushs_redir` (**the seam**) and `wp_kshm_child_redir` (**the
child walk**).

**THE SHAPE FACT THAT DECIDED THE LANE: the REDIR node's child pointer
has to be NAMED.**  `ushp_tree`'s REDIR row hides it under an
existential, which is the right reading of a FINISHED tree and the wrong
postcondition for a CONSTRUCTOR — because `parseexec` stores the argv
TERMINATOR through the exec node AFTER `parseredirs` has swallowed it
into a REDIR node, and an existential pointer cannot address a cell.  So
`UkShRedirCmd.ushp_redir_node s0 t pc q eq mode fd` is the node's own
seven fields with the child pointer named and nothing said about what
lives there, `ushp_redir_close` is the one-way door to `ushp_tree`, and
`wp_kshp_redircmd` / `wp_kshp_parseredirs_gt` KEEP their landed
statements as three-line corollaries of the general walks (`_n` / `_gtn`,
which take the sub-command as an abstract `Sub`).  Everything from
`parseexec_gt` up to `parsecmd_gt` relays the two nodes SEPARATELY; only
the theorem closes them.

**TWO MALLOCS, AND THAT IS WHERE THE LANE STOPS.**  `execcmd` allocates
the exec node and `redircmd` the REDIR node, so the redirect parse chains
TWO allocator capabilities where the symbol-free parse chains one.  Every
walk from `wp_kshp_parseexec_gt` up takes them as
`Context (UM0 UM1 UM2)` with `ushp_malloc_ty UM0 UM1` and
`ushp_malloc_ty UM1 UM2`.  **`UkShMalloc` proves only the FIRST call** —
its own header says so: `ushm_fresh` says the free list is EMPTY
(`freep` is 0, `base` untouched) and "a second call is a different
theorem, not a weaker one".  So:

- `wp_kshm_child_redir` is stated and proved at TWO ABSTRACT capabilities
  and LANDS;
- **`wp_kshm_child_alloc_redir` — the same walk with the allocator
  DISCHARGED — is BLOCKED**, and blocked on a design fact rather than on
  effort: there is no `ushp_malloc_ty (usz γs szv) _` to instantiate
  `UM1 → UM2` with.  What unblocks it is a second-call malloc theorem in
  `UkShMalloc` (the free list after one `morecore`, with the remainder of
  the 65536-byte chunk on it), and nothing else in this lane.

**REFUTED.**

- **`UkShLoop.ush_line_lexable` cannot become a disjunction** — SH-PARSE
  proved it and this lane implements the replacement:
  `ush_line_lexable_redir`, quantified over
  `UkShRedirLine.ushs_line_is ws file f k len`, whose first conjunct is
  `ushs_redir` at `p = |wl_body ws| + 1`, `e = |wl_body ws| + 3 + |file|`
  and whose second is the token list with `0 < length args < 10`.  The
  first conjunct is DERIVABLE (`ush_line_lexable_redir_shape`, one line
  over `ushs_line_is_redir`) and is stated anyway, exactly as
  `ush_line_lexable`'s first conjunct is; what a supplier really owes is
  the token count.  A widened premise is the CONJUNCTION of the two
  predicates, never a disjunction inside one.
- **The seam could not be reused as it stood.**
  `UkShMain.ush_cmd_of_ushp` fixes the cut line to
  `ushp_nulfold toks (ushp_ext len f)`; the redirect cut is one byte
  longer (nulterminate's REDIR arm zeroes `efile` too) and the file name
  has to be read out of the same line afterwards.  Both are fixed by
  generalising in place: `UkShMain.ush_cmd_of_ushp_gen` takes the line
  ALREADY PERSISTED and three facts about it — each token is inside the
  line, its END byte is zero, no byte of its BODY is — and the landed
  `ush_cmd_of_ushp` is that lemma at stage 4's cut, in twenty lines.
- **`ushp_tokens_gap` did NOT have to be re-proved.**  The argument
  tokens all end below the '>', and every scan that measures them stops
  below it too, so they are `ushp_tokens` of the line TRUNCATED at the
  '>' — whose only symbol byte is the one the truncation cut off.  That
  is `UkShRedirSeam.ushs_toks_below`, and it puts stage 4's separation
  fact back in scope unchanged.

**THE EXACT STATEMENT OF `wp_kshm_child_redir`** (`iris/UkShRedirSeam.v`),
which is what lane SH-ROUND instantiates:

```coq
  Lemma wp_kshm_child_redir (UM0 UM1 UM2 : iProp Σ)
      (Hm0 : UkShParse.ushp_malloc_ty N UM0 UM1)
      (Hm1 : UkShParse.ushp_malloc_ty N UM1 UM2)
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 cwdv : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (gp fe : nat)
      (ld : list fdstate) (st1 : fdstate) (n : nat)
      (K : fdtype -> iProp Σ) :
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    ushs_redir len f gp fe ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    (⊢ ukn_pay N (-1)) ->
    UkSh.sh_deps -∗
    shk_code γt -∗
    ush_jtab γt -∗
    shp_code γt -∗ shp_rodata γt -∗
    ustr γd (DfracOwn 1) s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd γfd ld -∗
    UserCwd.ucwd γcwd cwdv -∗
    UM0 -∗
    UkShRedir.ush_open_call N cwdv (s0 + Z.of_nat (S (S gp))) 1537
      (<[1%nat := FdClosed]> ld) K -∗
    urun N h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    (∀ (h' : CpuId) (m' : regfile) (q : Z) (ty : fdtype),
       ⌜ m' !!! Regidx a0_idx = (mword_of_int q : mword 64) ⌝ -∗
       ush_cmd γd q
         (UExec (ush_args s0 (ushs_nulcut args len f fe) args)) -∗
       UserFd.ustd γfd
         (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld)) -∗
       UserCwd.ucwd γcwd cwdv -∗
       K ty -∗
       UM2 -∗
       urun N h' m' (mword_of_int ShSyms.runcmd)
         (UkShDiag.ush_Dg + (70 + n)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
```

Read it against `UkShMain.wp_kshm_child`: the two parser premises are
`ushs_redir` / `ushs_toks` plus `0 < length args` (the redirect parse
needs at least one argument — with none, `parseexec`'s FIRST
`parseredirs` would turn and the walk is a different one); the open is a
CALL PREMISE at the file name the line itself names; `ucwd_any` is a
CONCRETE `ucwd` because the open's bundle is stated at one; the ledger's
slot 1 is named because `close(1)` spends it; and `uxsup_at` /
`riscv_kill_cred` / `uch_any` are GONE, because this walk stops at
runcmd's REDIR arm and never reaches `wp_kshr_runcmd_final`.

**WHAT SH-ROUND INSTANTIATES.**  `ush_open_call` (SH-REDIR's shape,
verbatim — the held offset goes inside `K ty` when OFF-HAND lands, so
neither premise is restated then), the two malloc capabilities, and the
CONTINUATION: at runcmd's own entry pc, with the EXEC sub-tree
`ush_cmd γd q (UExec (ush_args s0 (ushs_nulcut args len f fe) args))`,
the ledger with slot 1 reopened at `ty`, the cwd, `K ty` and `UM2`.
`ushs_nulcut args len f fe` is `UkShRedirPc.ushs_nulcut`: the line with a
NUL at every argument's end index AND one at the file name's.  The
application's own EXEC walk goes in that continuation and `K ty` is in
hand there, which is the whole point of the shape.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  **malloc's SECOND call.**
Everything above it is stated and proved; what nothing can discharge is
`ushp_malloc_ty UM1 UM2`, and until `UkShMalloc` has a theorem for a
`malloc` that runs on a NON-EMPTY free list, `wp_kshm_child_redir` cannot
become `wp_kshm_child_alloc_redir` and the redirect line cannot be run
end to end from `ushm_fresh`.  The shape of that theorem is visible from
this side: after the first call the list holds the remainder of the one
65536-byte chunk `morecore` inserted, so the second call is the SAME walk
with `freep` non-zero and the search loop turning once — not the
first-generation induction over a circular list that `UkShMalloc`'s
header declines.

### SH-MALLOC-2 (2026-09-17) — malloc's SECOND call lands; the CHAIN from `ushm_fresh` is refuted

Branch `app-file/sh-redir`, three commits on top of SH-PARSE-2's.  Whole
tree green on the lane's remote tree (`--proofs`, `EXIT=0`, zero `Error`);
`make audit-all-only` unchanged (echo FOURTEEN, system THIRTEEN); `make
gen-ucode` prints every catalog unchanged (this lane fetched no new
function); no `Admitted`; every new result carries `Proof using`.  The
whole diff is `iris/UkShMalloc.v` and **no landed statement moved** —
`wp_kshm_malloc_first`'s statement is unchanged to the character, which
matters because `UkShParse.ushp_malloc_ty` is stated at its shape and
THIRTEEN files carry it as `Hypothesis ushp_malloc_ok`.

**WHAT LANDED**, all in `iris/UkShMalloc.v`.

- `ushm_one sz R` (§4c, `iris/UkShMalloc.v:1257`) — the free list after a
  call, the twin of `ushm_fresh`:

  ```coq
  Definition ushm_one (sz R : Z) : iProp Σ :=
    (∃ c : Z,
       ⌜ SH_BASE + 16 <= c /\ c mod 16 = 0 /\
         0 < R /\ R < 2 ^ 31 /\ c + 16 * R <= sz /\ sz < 2 ^ 38 ⌝ ∗
       uword γd SH_FREEP (mword_of_int SH_BASE) ∗
       ushm_hdr SH_BASE (mword_of_int c) 0 ∗
       ushm_hdr c (mword_of_int SH_BASE) R ∗
       (∃ g : nat -> bv 8, ubytes γd (c + 16) (Z.to_nat (16 * R - 16)) g) ∗
       usz γs sz)%I.
  ```

  `freep = &base`, `base = { ptr = c ; size = 0 }`, the one chunk at `c`
  pointing back with `R` units free and its body owned, the break at `sz`.
  What was already carved off is not mentioned.

- **`wp_kshm_malloc_first_st`** (`:1561`) and **`wp_kshm_malloc_first`**
  (`:3637`).  The brief asked for the bridge "first-call POST = `ushm_one`
  at `R = 4096 - nunits`, as a corollary without restating the first-call
  theorem".  **That bridge does not exist and cannot**, and this is the
  lane's first correction to the brief: `wp_kshm_malloc_first`'s post is
  `usz γs (sz + 65536) ∗ ubytes γd q nbytes g` and NOTHING else — §5's own
  header says so ("THE ALLOCATOR'S LEFTOVER IS DROPPED, deliberately …
  handing out a state predicate no lemma consumes would be a promise about
  the free list this proof does not make").  The free list is dropped by
  AFFINITY inside the 2050-line walk, so no corollary can recover it.
  What was done instead keeps every landed statement: the walk is now
  `wp_kshm_malloc_first_st`, whose success arm reads
  `ushm_one (sz + 65536) (4096 - ((nbytes + 15) / 16 + 1))` where the old
  one read `usz γs (sz + 65536)`, and `wp_kshm_malloc_first` is that lemma
  with the list dropped again, in twenty lines.  The walk itself did not
  change: the resources were still in the proof context at the return, and
  the only edits are the final `iApply "Hcont"`'s spec pattern (which had
  hidden them, `[Hsz Hpay]`) and the success arm's assembly.

- **`wp_kshm_malloc_one`** (`:3725`) — **THE SECOND CALL**:

  ```coq
  Lemma wp_kshm_malloc_one (h : CpuId) (m : regfile)
      (nbytes szv R : Z) (avail : nat) :
    m !!! Regidx a0_idx = (mword_of_int nbytes : mword 64) ->
    0 < nbytes -> nbytes <= 65504 ->
    (nbytes + 15) / 16 + 1 < R ->
    shm_code γt -∗ ushm_one szv R -∗
    urun N h m (mword_of_int ShSyms.malloc) (10 + avail) -∗
    (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
       ⌜ ucallee_saved m m' ⌝ -∗ ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
       (∃ (q : Z) (g : nat -> bv 8),
          ⌜ r = (mword_of_int q : mword 64) ⌝ ∗
          ⌜ 0 < q /\ q mod 16 = 0 /\ q + nbytes < 2 ^ 38 ⌝ ∗
          ushm_one szv (R - ((nbytes + 15) / 16 + 1)) ∗
          ubytes γd q (Z.to_nat nbytes) g) -∗
       urun N h' m' (ret_pc (m !!! Regidx ra_idx)) (10 + avail) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  ```

  TWENTY-FOUR instructions and NO failure arm: `0x118c..0x11a8` (frame and
  `nunits`), `0x11aa/0x11ae` (`prevp = freep`, not zero), `0x11b2`
  (`c.beqz` NOT taken, the init arm skipped), `0x11b4/0x11b6/0x11b8`
  (`p = base.s.ptr` IS the chunk, so the search loop's FIRST turn finds
  it), then `0x1244..0x1264` (exact fit refuted, the TAIL cut, `freep`) and
  `wp_kshm_malloc_epi` for `0x1268..0x1272`.  No `sbrk`, no `free`, not one
  back edge.
  - **the size test at `0x11b8` reads s3 and the one at `0x121a` reads s2.**
    Same C line, different instruction, so the first call's `bgeu` lemma is
    not this one's.
  - **`0x1244..0x1264` was WALKED AGAIN, not factored** (the brief asked
    which and why).  The first call reaches that block with s1/s4/s5/s6
    already restored and eleven register-chain facts threaded around it; a
    shared lemma would take the whole chain as parameters and be longer
    than either copy.  Eleven instructions, paid once.
  - `ushm_sext32_moi` (`:230`) is `WpUmodeLoad.sext32_moi` re-proved from
    `RiscvExtras.sext64_moi32_unsigned`: that file is NOT on `UkShMalloc`'s
    import path and the `0x11b6` `c.lw` needs the fact at a size that is
    not a literal.

- **The capability layer** (§7): `ushm_one_cap sz` (`∃ R, 1 <= R <= 4094`),
  `ushm_one_ge sz R` (`∃ R', R <= R'`) with `ushm_one_ge_mono`;
  `ushm_malloc_ok_one` — `UkShParse.ushp_malloc_ty N (ushm_fresh sz)
  (ushm_one_cap (sz + 65536))`, §6's adapter at the landed type with a
  strictly stronger post, so `UkShMain.wp_kshm_child_alloc` could take it
  instead and nothing else would move; `ushm_malloc_ty_le B UM UM'` —
  `ushp_malloc_ty` with `nbytes <= 65504` weakened to `nbytes <= B` — with
  `ushm_malloc_ty_le_top` (the landed type IS the bound at 65504, by
  `exact`: the two are convertible) and `ushm_malloc_ty_le_mono`; and the
  four instances `ushm_malloc_le_fresh`, `ushm_malloc_le_one`,
  `ushm_malloc_le_exec` (`ushm_malloc_ty_le 168 (ushm_fresh sz)
  (ushm_one_ge (sz + 65536) 4084)`) and `ushm_malloc_le_redir`
  (`ushm_malloc_ty_le 40 (ushm_one_ge sz 4084) (ushm_one_ge sz 4080)`).

**REFUTED — `wp_kshm_child_alloc_redir` DOES NOT LAND, and not for want of
proof effort.**

`UkShParse.ushp_malloc_ty UM UM'` (`iris/UkShParse.v:3552`) quantifies
`nbytes` UNIVERSALLY over `0 < nbytes <= 65504`, and `UM'` — being one
`iProp` fixed before `nbytes` is bound — may not mention it.  Chain two of
them from `ushm_fresh` and the arithmetic closes:

- at `nbytes = 65504`, `nunits = (65504+15)/16 + 1 = 4095`, so ONE call
  takes 4095 of the 4096 units `morecore` inserted and the strongest `UM1`
  a first call can promise is **"at least one unit is free"**
  (`ushm_one_cap`'s `1 <= R <= 4094` is exactly that bound, and it is
  tight);
- `ushp_malloc_ty N UM1 UM2` must then serve `nbytes = 65504` too, which
  needs 4095 free units.

**So no `UM1` satisfies both halves at a free list that is one 64 KiB
chunk**, and `UkShRedirSeam.wp_kshm_child_redir`'s
`Hm0 : ushp_malloc_ty N UM0 UM1` / `Hm1 : ushp_malloc_ty N UM1 UM2`
(`iris/UkShRedirSeam.v:403-404`) cannot both be discharged from
`ushm_fresh`.  SH-PARSE-2's diagnosis ("what unblocks it is a second-call
malloc theorem … and nothing else in this lane") is therefore incomplete:
the second-call theorem lands here and is not enough.

`wp_kshm_malloc_one`'s `nunits < R` is NOT a premise more effort could
drop:

- dropping it means walking the NO-FIT path — `0x11bc..0x11e0` (spill
  s1/s4/s5/s6, `nu = max(nunits, 4096)`, `s1 = &freep`, `s5 = -1`) and then
  the loop's BACK EDGE, `0x121e/0x1220/0x1222` taken to `0x1216`,
  `0x1216/0x1218/0x121a` at `base` (size 0, not taken), `0x121e..0x1222`
  again NOT taken, `sbrk` — about 45 instructions;
- and a **`free` at a TWO-BLOCK circular list**, which is a different walk
  from `wp_kshm_free_first`: the scan turns once (`0x1126` taken at
  `base -> chunk`), breaks at the chunk, and neither coalesce test fires,
  so `chunk->ptr = bp` and `freep = chunk` — about 25 instructions and a
  three-block list out;
- **and that walk cannot even reach its `sbrk`.**  `wp_kshm_sbrk`'s
  precondition is `usz_ok (sz' + 65536)` (`iris/UkShMalloc.v:346`), and
  all `ushm_one` can carry about the break is where it IS: the first call's
  own premise is `usz_ok (sz + 65536)`, which says nothing about room for a
  second 64 KiB.  Making the no-fit path reachable therefore means
  `ushm_one` carrying `usz_ok (sz + 65536)` AND every caller up to
  `UkShMain.wp_kshm_child_alloc` / `AppFile` supplying
  `usz_ok (sz + 131072)` — a premise change across the seam, not a walk.

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  **Re-state the thirteen
`ushp_malloc_ok` hypotheses at `ushm_malloc_ty_le 168`**, and
`wp_kshm_child_redir`'s two `Hm` parameters with them.  sh's constructors
call `malloc` at exactly two sizes — `execcmd` at 168
(`iris/UkShParseLex.v:1896`) and `redircmd` at 40
(`iris/UkShRedirCmd.v:401`) — so the capability they actually need is the
BOUNDED one, and at a bound the chain closes: the redirect line's whole
parse costs SIXTEEN of the chunk's 4096 units (12 + 4), and
`ushm_malloc_le_exec` / `ushm_malloc_le_redir` are already proved and
waiting.  The files are `UkShParseLex`, `UkShParseTok`, `UkShParseRedir`,
`UkShParseExec`, `UkShParseCmd`, `UkShRedirCmd`, `UkShRedirPr`,
`UkShRedirEx`, `UkShRedirPex`, `UkShRedirNul`, `UkShRedirCm`,
`UkShRedirPc`, `UkShRedirSeam` — each carries ONE `Local Notation
ushp_malloc_ty := (UkShParse.ushp_malloc_ty N)` and one or two
`Hypothesis` lines, so the edit is thirteen notation lines plus the two
`Hm` binders in `wp_kshm_child_redir`; no proof text moves, because a
bounded capability is applied at exactly the same call sites with the same
arguments.  It IS a statement move, which is why this lane did not make it
— but it is the cheap fix, and the expensive one (the second `morecore`,
`free` at two blocks, and `usz_ok` room threaded from `AppFile` down) buys
nothing the shell uses.
