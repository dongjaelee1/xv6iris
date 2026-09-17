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

## Wave 1 — as launched (2026-09-17), and what each left

- [x] **CAT-PIN** landed (`FsCatPin.v`, `FsFPin.v`, `FileFsPure.v`; cat is inum 3).
- [~] **OFF-HAND** did not land its members: it found the four coupled facts
  design §3 now records, and landed `FdPark.v`'s exact-payment supplier.
  Continued as **OFF-HAND-2** (kernel/spec: the mode in `fpnames`, the
  successor-parkedness carrier moved to the family's post, the publish's
  mode, the surrender bundle at the exec crossing) and then
  **OFF-HAND-3** (U tier: the held-row counter in `urun`, the hand-mode
  open leaf, the held read/write members, the held branch of
  `filewrite_in`/`fileread_in`).
- [~] **SH-REDIR** landed runcmd's REDIR arm with the open as a call premise
  (`UkShRedir.ush_open_call`, `wp_kshr_redir_arm`) and gettoken's `>` arm;
  the parser is **SH-PARSE** (the generalised gettoken, parseredirs once,
  redircmd into the catalog, parseexec/nulterminate/parsecmd at the redirect
  shape, the child walk at both line shapes).
- [ ] **MODEL** — running.

## Wave 2 — on the claim (`iris/AppFile.v`, branch `app-file/claim`, layer A landed 2026-09-17)

- [ ] **F-OPEN** (running): `FileDeltas.v` (the pure preservation of `f_ok`
  and the pins under every leg), `FileOpen.v` (the create/truncate open
  supplier from the deed at both deed values, the plain O_RDONLY open, the
  read piece), `UkFileOpen.v` (the corollaries at the parked leaves, in
  `ush_open_call`'s `K ty` shape).
- [ ] **F-WRITE** (running): `FileWrite.v` (the append phases and chain at
  the deed, the offset equation as a premise the held leaf discharges),
  `UkFileWrite.v` (the member at the parked leaf and the consumer test).
- [ ] **STAGE**: `EchoOut`/`EchoOutPure` grown by `o_fh` and the line
  shapes (design §4); the ledger's line list and the tag's lb; `al_pow`'s
  seed; `Hphi` at `file_phi`; the record `app_file` (AppFile layer B).
- [ ] **ECHO-FILE**: `iris/UEchoFile.v` (design §5.2), after OFF-HAND-3.
- [ ] **CAT-ENTRY**: `iris/UCatKernel.v` + `iris/UCatOut.v` (design §5.3),
  after OFF-HAND-3 and STAGE.
- [ ] **SH-ROUND**: sh's fork lends the deed, the exit payload returns
  it, the prompt link records `o_fh`; `UShCat`; the dispatch on the
  line's shape; the REDIR child's proof at the claim (`ush_open_call`
  instantiated by `UkFileOpen`, the taint arm surrenders), after SH-PARSE
  and STAGE.
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

### CAT-PIN — LANDED (2026-09-17, commit `9fb054b3b`)

**cat's inum is 3.**  Read off the image, not chosen: mkfs packs the
root in `UPROGS` order and `cat` is the first program after `README`
(inum 2), so the root's record 3 is `(3, "cat")`.  Its record is
`T_FILE`, `nlink = 1`, `size = 36728` — and those 36,728 bytes ARE
`user/_cat`, byte for byte (`FsImgCheck.fsimg_cat_bytes_bool`).

**What landed.**

- `iris/FsCatPin.v` — `CAT_INO = 3`, `cat_path`, `cat_bytes :=
  ElfUser.cat_elf`; `fsimg_cat_size` / `_nlink` / `_nlink_nz` /
  `_size_bound` / `_type_nz` / `_type_nd` / `_file_bytes` / `_abs`;
  `era0_cat_path_pin`, `era0_cat_content_pin`, `era0_cat_arun`,
  `era0_cat_pins`, `era0_cat_pins_of_snap`, `era0_boot_cat_pins`,
  `era0_recovery_cat_pins`, `era0_reboot_cat_pins`; and the resource
  forms `fs_snap_era0_cat_pins`, `astate_era0_cat_pins`,
  `astate_era0_boot_cat_pins`, `nview_era0_cat`, `nview_era0_boot_cat`.
  `FsEchoPin.v` with `echo` → `cat` throughout and nothing else.
- `iris/FsFPin.v` — `f_path`, `fsimg_f_path`, the five
  `fname_f_ne_*`, `f_absent`, `f_absent_apath`, `era0_f_absent`,
  `era0_boot_f_absent`, `era0_recovery_f_absent`.
- `iris/FileFsPure.v` — `file_fs_pure av := echo_fs_pure av /\
  era0_cat_pins av`, `file_fs_pure_echo`, `file_fs_pure_cat`,
  `file_fs_era0` (the twin of `AppEcho.echo_fs_era0`: same three
  premises, `file_fs_pure (abs_view (fss_inodes S))`).
- `iris/FsImgCheck.v` (additive) — `fname_cat`, `fname_f`,
  `fsimg_cat_path` (`= Some 3`), `fsimg_cat_type`,
  `fsimg_cat_bytes_bool`, `fsimg_cat_at`, `fsimg_cat_ok`.  Each exactly
  where echo's twin sits; no landed statement moved.
- `iris/ElfUser.v` (additive) — `cat_elf` and the fifth copy of the
  program theorem set, on `echo_elf`'s pattern (pure-bss writable
  segment: entry 0xf6, loads `(0x0, 0xecc, 0xecc, R-X)` and
  `(0x1000, 0x0, 0x220, RW-)`, `.bss = [0x1000, 0x1220)`).
- `user-rocq/_CoqProject` — `CatElfRaw.v` joins the list.  It was
  DUMPED but deliberately unlisted ("nothing needs it"); now something
  does.  **The next lane that adds a program must do the same**, and
  must `rm` the remote `CoqMakefile` afterwards (`run-on-gcp --proofs`
  regenerates it only when it is ABSENT, so a `_CoqProject` edit is
  invisible to the remote build until you delete it).

**The `no f` sentence is `FsConsPin`'s, not `TreeImg`'s.**  The brief
asked for it on `TreeImg.img_root_blk`'s constant reading; it is not
needed and would have cost an import of `TreeImg` (hence `App` and
`AppTree`) into an image leaf.  `FsConsPin.fsimg_console_path` already
pays the identical computation for `console` — a MISS, so the full scan
— through `FsImgCheck.fsimg_path_root`, which is `FsImg.path_at_disk_dir`'s
single `dir_first` pass and not `dir_view`.  `fsimg_f_path` is that line
at `fname_f`, and it is not measurably slower than its neighbours.
`TreeImg`'s `img_root_blk` / `Global Opaque` machinery exists for
`dir_view`, which nothing here calls.

**Traps hit (one).**  `FsFPin` is a PURE leaf — no `iris.proofmode` —
so `rewrite /f_absent` and `rewrite -Hdk` (ssreflect) do not parse
there: `Syntax error: '*' or [oriented_rewriter] expected after
'rewrite'`.  Every pin file in this family imports `iris.proofmode` for
its own `iProp` sections and therefore gets ssr rewriting for free; a
file that does not must spell `unfold` / `rewrite <-`.  Worth knowing
for MODEL (`FileDisc.v`), which is Iris-free by charter.

**Assumptions.**  `Print Assumptions` on `era0_cat_path_pin`,
`era0_cat_content_pin`, `era0_cat_arun`, `era0_cat_pins_of_snap`,
`era0_boot_cat_pins`, `era0_recovery_cat_pins`, `era0_f_absent`,
`era0_recovery_f_absent`, `file_fs_era0`, `ElfUser.cat_elf_wf` and
`FsImgCheck.fsimg_cat_ok`: the eleven `PrimString`/`PrimInt63`
primitives, nothing else — no `Admitted`, no project axiom, no `Spec*`
module parameter.  Echo audit still 14, tree audit still the system
theorem's thirteen (ten Rocq primitives + the two reservation
`Parameter`s + `functional_extensionality_dep`).  Whole tree green
(`--proofs -k`, no `Error`).

**THE ONE THING THE NEXT LANE NEEDS FIRST.**  APP-CLAIM: `f_ok av None`
is `FsFPin.f_absent av` — use that name rather than re-spelling the
`astep`, because `FsConsPin`'s section 5 delta algebra
(`cons_absent_arm` / `_create_other` / `_unarm` / `_trunc`, and the
name-generic `file_pin_*` family beside them) is written against
exactly this shape and is what carries the claim through the mknod and
the create legs.  `FsFPin` deliberately stops before those: they need
`FsAbsDelta` and belong with the claim, and the five `fname_f_ne_*`
inequalities they take are already proved there.

### OFF-HAND (kernel tier, 2026-09-17) — THE PIN DOES NOT COME OFF; ONE UNPAID SITE, NAMED

**The lane's verdict in one line: deliverable 1 reduces to a SINGLE unpaid
obligation — `fdv_all_parked` at the exec crossing — and the payer the brief
names for it does not exist at the tier it names.  Deliverables 2 and 3 sit
behind it.  Everything below is checked at the statement in the tree, not
inferred from the earlier RA blocks.**

**WHAT LANDED** (whole tree green on the lane's remote tree, `--proofs -k`, 0
`Error`; echo audit 14; every new lemma `Proof using` and `Closed under the
global context` — no platform axiom at all): `iris/FdPark.v`, additive, no
landed statement moved.

- `FdPark.fdst_parked_of_key` — the one step between the STRONG premise a
  slot's mint is narrowed by (`FdSlots.fdv_all_parked` of the key's table)
  and the WEAK one a deposit actually spends (`fdst_parked` of
  `FdSlots.fd_st_of_key` at the call's own argument word, which is how rows
  5 and 16 read the mode).  Out of range and off the end `fd_st_of_key`
  answers `FdClosed`, so the step is free at both.  This is the lemma the
  class field's premise is discharged through; without it every prover of
  `xv6_sbundle_of_supply_ne` would re-derive it.
- `FdPark.off_supply_of_st_at` / `off_supply_of_st_at_eq` — **the arm's
  supplier at an EXACT payment, which is what RA-2's `uoff_surr` cannot
  give.**  `uoff_surr` names its position under an `∃` (right for a
  boundary, which does not care), so `off_supply_of_st` hands its receipt
  back at the KERNEL's offset.  A held FILE MEMBER has to promise more:
  design/app-file.md §3's append step needs `uoff γo off` in and
  `uoff γo (off + d)` out at the CALLER's own `off`.  These take the payment
  at `uoff_rcpt`'s (exact) shape and return, beside the supplier, THE TIE
  `⌜m = OffHeld -> off' = off⌝` — the kernel learns it by agreement against
  its own half (`UserOff.uoff_agree_k`), so the caller still pays no
  equation and a PARKED row still costs exactly nothing (payment `True`,
  tie guarded by the mode).  It is also what makes a MULTI-NODE walk
  statable: filewrite's chain fires once per chunk, the receipt of node `k`
  is the payment of node `k+1` at the same exact shape, so a loop carries
  `uoff_rcpt st (off0 + p)` at its own byte cursor and the tie turns each
  fire's offset into `off0 + p` — the anchored-cursor equation
  design/user-write.md §3c says is missing.  With `uoff_surr` the cursor can
  only be re-existentialised at every node.
- `FdPark.uoff_rcpt_of_parked` — the exact payment read at an equation on
  the state, which is how a member's premise list holds it.

**REFUTED / BLOCKED.**

1. **DELIVERABLE 1 HAS EXACTLY ONE UNPAID SITE, AND IT IS EXEC.**  The mint
   sites that owe `fdv_all_parked (uvis_fd W)` are FOUR, not three (the
   brief asked): `SystemAdequacy.init_boot_of_sup` (`:1063`),
   `PinnedExec.pex_slot`'s taint arm (`:281`), `UInitBoot`'s taint-arm mint
   (`:860`) and `UInitSh`'s (`:1370`).  Of these:
   - `init_boot_of_sup` is FREE (`FdSlots.fdv_all_parked_fdt0`).
   - **FORK IS NOT A SITE AT ALL**, and the brief's "fork's child … a
     verified parent parks first" is unnecessary: `UexecRet.uexec_fork_child_F`
     (`:1320`) builds the child's slot at
     `bump_at W … (uvis_fd W) …` and `uexec_fork_F` pins `⌜fdv' = uvis_fd W⌝`
     — the CHILD'S KEY CARRIES THE PARENT'S TABLE VERBATIM, so the mint's
     premise transfers by that equation, for a generic parent and a verified
     one alike.  (RD-2's consequence (b) was about the descriptor BUNDLE,
     not the key.)
   - the generic tier's own Löb step is FREE too: the successor key's
     all-parkedness comes off `UsysMemOk.usys_fd_ok`'s open-arm conjunct,
     which RA-3 landed for exactly this.
   - **the remaining three are ONE crossing — exec** (`SpecKexec.exec_slot_pre`'s
     two wands), and its only supplier is `ProcInv.proc_priv_parked`
     (`:1459`), which IS the pin, in three steps
     (`FileInvDefs.fdstate_ok_parked :635` → `file_ref_parked :1802` →
     `ProcInv.ofile_slot_parked :432` / `ofile_slots_parked :655` /
     `proc_ofiles_parked :677`).  Relaxing the pin deletes it.  §8.4's wall 2
     therefore stands, now sharpened: it is the ONLY obligation left unpaid.
     (Note `proc_priv_parked` has ZERO proof consumers today — so the pin's
     relaxation costs nothing until the premise exists, and everything until
     then.)
   - **THE BRIEF'S REPLACEMENT PAYER IS REFUTED BY COVERAGE, NOT BY PROOF
     DIFFICULTY.**  "The U-tier exec leaf gains the premise; a verified
     caller parks with `UserOff.uoff_park` before the ecall" cannot work:
     `fdv_all_parked fdv` quantifies over all `NOFILE` slots, and a
     program's U-tier knowledge of its table is `UserFd.ustd` (slots
     `< NSTD = 3`) plus its `UserFd.ufd` handles (each carries `NSTD <= fd`).
     A `ufd` handle is an ordinary affine resource: a program may DROP it
     while its descriptor stays OPEN in `fdv`.  So parking every offset the
     caller can name leaves the rows it cannot name unconstrained, and the
     premise is unprovable at that tier however much the caller parks.  This
     is §8.3's finding C read at the exec arm.

2. **"THE MODE IS FREE" REFUTES `FileInvDefs.fdstate_ok_inj`, AND THIS IS NEW
   (no RA block records it).**  With `m` unconstrained,
   `FdOpen r w (FdInode n γo OffParked)` and `FdOpen r w (FdInode n γo OffHeld)`
   both satisfy `fdstate_ok` at ONE `C`, so `fdstate_ok_inj` (`:669`) is
   false and `file_pay_st_agree` (`:1736`) and `FileInv.file_ref_agree`
   (`:94`) fall with it — and they are load-bearing (two descriptors on one
   file must report one state; filedup's two shares must not drift apart,
   and a drifted pair would have one row claiming an `off_user_inv` that was
   never allocated).  **The fix is not to drop the pin but to MOVE it**: the
   offset mode is a per-FILE constant, so it belongs with the other two
   (`fp_inum`, `fp_ooff`) in the payload names record.  `FileInvDefs.fpnames`
   gains `fp_om : offmode` (six `MkFPNames` sites: `ProofPipealloc` ×4,
   `ProofSysOpenParts` ×2), `fdstate_ok` takes it where it takes `γo`, and
   the FD_INODE arm pins `m = fp_om pn`.  `fpay_tok`'s `to_agree` then makes
   two holders agree on the mode for free, exactly as they agree on the
   inum — and it is semantically right: `γo` is per FILE OBJECT, so dup and
   fork share one mode by construction (user-read.md §4).

3. **DELIVERABLE 2 IS §8.4's WALL 1, UNCHANGED, AND THE MODE-IN-THE-FAMILY
   WORDING DOES NOT ROUTE AROUND IT.**  `UsysMemOk.usys_fd_ok`'s open arm
   carries `fdst_parked (FdOpen rd wr t)` on the ACTUAL successor table, and
   that relation is threaded with NO tier index: `SpecSyscall.sysc_fd_ok`
   (`:328`) is it verbatim and `SpecUsertrap.ut_fd_ecall` (`:310`) relays it
   at every number.  An open that installs `FdInode i γo OffHeld` refutes it
   whatever the deposit's family says, because the family is invisible to a
   pure relation; and the conjunct cannot come off while the generic Löb
   reads successor-parkedness from it (finding 1).  So "the mode from the
   deposit's open family" needs the generic tier's successor-parkedness
   carrier moved to the slot's own post (`UexecSG.spost_at`'s `fdv'`, which
   the FAMILY chooses) FIRST — a lane, not a step, exactly as §8.4 priced it.

4. **DELIVERABLE 3: ALL THREE MEMBERS SIT BEHIND 1 AND 2.**
   `wp_uk_ecall_open_recv_img_held` is blocked by 3 above.  The two file
   members are blocked one step earlier than "no held descriptor exists":
   `SpecFilewrite.filewrite_extra` and `SpecFileread`'s read arms return NO
   OFFSET RECEIPT at any mode, so the briefed post (`uoff γo (off + landed)`
   on BOTH arms) is not derivable from the landed kernel rows even at a
   hypothetical held state — stating it would be stating the arm split, not
   using it.  **The cheap half, for whoever takes the split:**
   `SpecFilewrite.filewrite_in` (`:789`) and `SpecFileread.fileread_in`
   (`:929`) already match `FdInode i γo _` — THE MODE IS IGNORED — so the
   split's PARKED branch is byte-for-byte what is there now and every
   `_in_inode` / `_extra_inode` reader keeps its statement.  The whole cost
   is the HELD branch (payment `FdPark.uoff_rcpt st off`) plus a receipt
   parameter on `write_arms_at` / `read_arms`, and then `fsabs_filewrite_in`
   / `fsabs_fileread_in` gaining `⌜fdst_parked st⌝` — which is where the
   class premise of finding 1 attaches, through `fdst_parked_of_key`.
   The kernel fire sites are few and known: `ProofFilewrite:4947`
   (`Hoinvw`, handed to the body at `:5481`, spent at `:2960` / `:3098`) and
   `ProofFileread:2263` (spent at `:2839` / `:3190`); both become
   `FdPark.off_supply_of_st_at_eq`.

**THE ONE THING THE NEXT LANE NEEDS FIRST: the owner's ruling on §8.4's
U-tier held carrier — and this lane's check makes it CHEAPER than §8.4
priced it.**  The only obligation it has to discharge is `fdv_all_parked fdv`
at the exec crossing (finding 1), so §8.4's *set* of held descriptors is more
than is needed: a COUNTER suffices.  `uheld γ (n : nat)`, one half beside
`UserFd.ufd_auth` inside `UkRun.urun` and the other the program's, at the
invariant "`n` is the number of held rows in `fdv`": `n = 0` gives
`fdv_all_parked fdv` outright, a hand-open increments it as it hands the half
out, `FdPark.foff_row_park` at one row decrements, close of a held row
decrements.  A program that never hand-opened carries `uheld γ 0` and pays
the exec premise from that alone — which is what the three unpaid mint sites
need and what no `ustd`/`ufd` combination can give.  It is NOT RA-1's
finding-2 brute fix: it makes no program unable to hold a `uoff`, it makes
every program able to SAY whether it does.  With it, finding 1 closes, the
`fp_om` move of finding 2 makes the pin's relaxation type-correct, and
deliverable 2 still waits on the `spost_at` lane of finding 3.

### MODEL (2026-09-17) — `iris/FileDisc.v`, the pure model and its determinacy

Branch `app-file/model`, commit on that branch.  Whole tree green on the
lane's remote tree (only the two new files compile; nothing depends on
them yet).  `Print Assumptions` is **Closed under the global context** —
no axioms at all, not even PrimString — on `sessf_prefix_det`,
`file_phi`, `demo_f_bad`, `demo_f1`, `disc_f_disc`, `parse_line_body`,
`line_body_parse`, `disc_input_f_prefix`, `fcont_ok_subseq` and
`ralt_dec_enc`.  Every result carries `Proof using`.

**WHAT LANDED.**  `iris/FileState.v` is the claim lane's file copied
VERBATIM (every statement and every proof went through as written) and
sits before `EchoDisc.v` in `iris/_CoqProject`; `iris/FileDisc.v` sits
directly after it.

- lines: `fname_f`, `suf_gtf`, `uline`, `line_body`, `line_bytes`,
  `uline_ok`(+dec), `strip_gtf`, `parse_line`, `parse_line_ok`,
  `line_body_parse`, `parse_line_body`, `uline_of`, `lines_of`.
- D3: `fbody_byte`, `fbody_ok`, `fbody_ok_bytes`, `fbody_ok_short`,
  `disc_input_f` with `_dec`, `_nil`, `_snoc`, `_prefix`, `_body`, `_at`.
- contents: `fcont_ok`, `fst_ok`, `fcont_ok_nodollar`, `fcont_ok_nl`,
  `echo_args_chunks_shape`, `subseq_shape`, `fcont_ok_subseq`.
- alternatives: `dg_open`, `dg_exec_cat` (with `dg_open_line`,
  `dg_exec_cat_line`), `dg_catopen`, `alt_openfail`, `alt_execcat`,
  `alt_catopen` (each with its `_string` byte reading), `ralt`,
  `ralt_enc`/`ralt_dec`/`ralt_dec_enc`/`ralt_dec_lt4`, `ralt_panic`,
  `ralt_ok`(+dec), `fsm`, `cont`, `fst_ok_fsm`, `cont_panic`,
  `cont_shape`.
- session: `ralt_at`, `pro_idx_f` (+ `_S`, `_Sp`, `_Sn`, `_mono`, `_le`,
  `_ext`, `_add`), `fst_upto` (+ `_ext`, `_drop`), `alt_cont_f`,
  `alt_blk_f`, `alt_seq_f` (+ `_S`, `_ext`, `_bs_ext`, `_bs_app`,
  `_cs_ext`, `_ps_ext`, `_cons`, `_cons_assoc`, `_drop`), `sessf` (+
  `_nil`, `_snoc_other`, `_snoc_nl`, `_step`, `_mono`, `_take`,
  `_ps_ext`), `fst_after`, `pro_ok_f`(+dec, `_mono`), `pro_pin_f`,
  `pro_pin_f_of_ok`.
- discipline and claim: `disc_seg_f`, `disc_pt_f`, `alts_ok` (+ `_length`,
  `_at`), `disc_seg_f'` (+ `_intro`, `_nil`), `disc_f`, `good_out_f`,
  `echof_ws`/`echof_lines_in`/`echof_cyc`/`echof_lines_of`/
  `echof_lines_before` (+ `echof_lines_in_prefix`,
  `echof_lines_of_snoc`, `echof_lines_of_prefix`, `echof_lines_in_ok`),
  `fadm_boot`(+`fadm_boot_fst_ok`), `file_phi`.
- determinacy: `fd_dollar_split`, `fd_out_eq_panic`, `fd_prompt_of_dollar`
  (+`_r`), `cont_pair_det`, `alt_seq_f_prefix_det`, **`sessf_prefix_det`**.
- plain-echo compatibility: `sessf_sess`, `disc_f_disc`, with
  `alts_ok_lt4`, `alts_ok_of_lt4`, `pro_ok_f_ok`, `pro_idx_f_echo`,
  `alt_seq_f_sess`, `disc_input_f_of_echo`.
- demos: `demo_f1` (+ `demo_f1_file`, `demo_f1_disc`), `demo_f2`
  (+ `demo_f2_adm`), `demo_f3` (+ `demo_f3_adm`), `demo_f4`, `demo_f5`,
  and the NEGATIVE `demo_f_bad`.

**THE PROOF DOES NOT RUN ON A TABLE OF ALTERNATIVES.**  Twelve
alternatives at three line shapes would be a 12x12 comparison; what
replaces it is one observation, `cont_shape`: every non-panic
alternative's own output is a `'$'`-FREE RUN FOLLOWED BY THE PROMPT —
echo's line, each diagnostic, cat's, and the file's CONTENT, because a
content is echo's chunks and a chunk is a word, a blank or a newline.  So
`fd_dollar_split` settles every non-panic pair at once with no case
analysis, and only the panic alternative (which re-enters init's prologue
instead of printing a prompt) needs its own argument, `fd_out_eq_panic`.
Copy this shape rather than the head-byte table if another alternative is
ever added.

**WHERE §1 HAD TO BE CORRECTED — each with its counterexample.**

1. **`parse_line` inverts `line_body`, not `line_bytes`.**
   `parse_line (line_bytes l) = Some l` is FALSE at every `l`:
   `line_bytes LCat = sb "cat f" ++ [wl_nl]` and the parser sees the
   bodies `LineWords.bodies_of` cuts, which have their newline stripped,
   so it answers `None`.  Landed: `line_bytes l = line_body l ++
   [wl_nl]`, `parse_line_body : uline_ok l -> parse_line (line_body l) =
   Some l`, `line_body_parse : parse_line b = Some l -> b = line_body l`.
2. **The partial line is `fbody_byte`, not `wl_body_byte`.**  A user
   typing `echo hi > f` is mid-line at `echo hi >`, whose last byte '>'
   (62) is neither alphanumeric nor the blank, so `EchoDisc`'s predicate
   REFUTES a user halfway through an admissible line — the discipline
   would exclude the only line shape this application is about.  Landed
   `fbody_byte b := wl_body_byte b \/ b = wl_gt`; prefix closure,
   decidability and the length bound are unchanged.
3. **`file_phi`'s first clause must be GUARDED.**  `cycles_of [] = []`,
   so at the empty history `length s0s = 0` and `s0s !! 0 = Some FAbs` is
   unsatisfiable while `disc_f []` holds: `file_phi []` would be FALSE.
   Landed `forall s, s0s !! 0 = Some s -> s = None`, which says the same
   thing at every history that has a cycle.
4. **The brief's head-byte separation for `RCRan` is false.**  A content
   is a subsequence of an ECHO LINE's chunks, and 'c', 'e' and 'f' are
   alphanumeric: after `echo exec cat failed > f`, `cat f` prints exactly
   the bytes of the `RCExec` diagnostic, and after `echo fork > f` it
   prints `"fork\n"` followed by a prompt — sh's panic line.  Both are
   HARMLESS, because the conclusion is an equality of BYTES (as
   `EchoDisc.line_alts_of_prefix_bytes` already found for
   `echo exec echo failed`), and the fork one is the single collision
   `fd_out_eq_panic` exists for.  What is true, and what the proof uses,
   is only that no content, line or diagnostic carries a `'$'`.
5. **`fsm`'s `RFOpenM` keeps design §1's guard "only at an absent f"**,
   against the flat `Some []` of the coordinator's note: at a PRESENT f,
   xv6's `sys_open` truncates only AFTER `filealloc` has succeeded
   (`kernel/sysfile.c`), so at `Some bs` nothing was truncated and the
   flat version would ask the claim to step the deed to `Some []` while
   the abstract view is unchanged — unprovable at F-OPEN.  At `Some bs`
   this alternative is `RFOpenU`.
6. **Two dead parameters dropped:** `good_out_f` takes no `Ls` (the
   admissible-boot condition is `file_phi`'s own conjunct and the
   per-cycle claim never reads it), and `fst_after` takes no `ps` (the
   state is a function of `cs`, the bodies and the boot state only).
7. `FileState.echo_args_chunks [] = []` is the honest reading at a
   one-word line — xv6's echo loop starts at `argc = 1` and writes
   NOTHING — where §1's "closed by `["\n"]`" would read as `[["\n"]]`.
   `uline_ok` excludes the line either way; the difference matters to
   ECHO-FILE's write chain, which must not owe a newline it never wrote.

**THE NEGATIVE WITNESS IS THE POINT OF THE FILE.**  `demo_f_bad`: the
wire in which `echo hello world > f` was typed and `cat f` then printed
`goodbye` is NOT `good_out_f`.  It is refuted by `sessf_prefix_det`
itself — the honest transcript through the open `cat f` line is on the
wire, so any resolution must agree with it up to there — plus ONE head
byte: at the `cat` round the continuation's first byte is `'$'`, `'c'`,
`'e'`, `'f'`, or one of `hello world\n`'s own bytes (`fd_cat_head`,
`subseq_head`), never `'g'`.

**WHAT IS NOT THERE.**

- `disc_seg_f'` is NOT decidable here.  `EchoDisc`'s finite search over
  resolutions needs a bound on `sel`, which is finite (`sel_ok` bounds it
  by `length (echo_chunks ws)`) but unwritten; the demos use
  `disc_seg_f'_intro` with the decidable `disc_pt_all_f` instead.  If the
  adequacy path ever needs `Decision (disc_f h)`, that is the lane.
- `disc_f` has no snoc/prefix closure laws (`EchoDisc.disc_snoc`'s
  twins).  `disc_input_f` has its full set, and `echof_lines_of` has its
  prefix monotonicity.
- `FileDisc` does NOT import `EchoOutPure` (the handful of helpers it
  wanted are re-proved locally as `fd_*`), so `EchoOutPure`/`EchoOut` can
  be grown ON TOP of `FileDisc` without a cycle.

**WHAT THE STAGE LANE NEEDS FIRST.**  `o_fh`'s entry `i` is
`fst_upto cs s0 (bodies_of I) i` and its step law is `fst_upto`'s own
definition (`fst_upto cs s bs (S q) = fsm (fst_upto cs s bs q)
(uline_of (bs !!! q)) (ralt_at cs q)`), with `fst_after cs s0 I` the value
a prompt link records; the round index the stage keeps equal to
`length o_fh - 1` is `nlines I`, the same index `alt_seq_f` uses, and
`sessf_take`/`alt_seq_f_cs_ext` are what let a stage read a resolution it
has only a lower bound of.  Two shape changes to plan for: the range
condition that was `Forall (fun c => c < 4) cs` is now `alts_ok I cs`, a
`Forall2` against `lines_of I` which ALSO pins `length cs = nlines I`
(`alts_ok_length`, `alts_ok_at`); and the prologue counter is `pro_idx_f`,
which counts `RFFork` and `RCFork` beside `REcho 3` (`pro_ok_f`,
`pro_pin_f`, `pro_pin_f_of_ok`).  `sessf_prefix_det` is the twin of
`EchoOutPure.sess_prefix_det` at those hypotheses plus `fst_ok s` and ONE
boot state shared by both witnesses; `disc_f_disc` and `sessf_sess` say
nothing about the echo application's own claim changes at an echo-only
history.

### STAGE (2026-09-17) — the console side and the record; two blockers named

Branch `app-file/stage`.  Whole tree GREEN on the lane's remote tree
(`make -j8 -k` over the four sub-trees, `EXIT=0`, zero `Error`); **both
audits unchanged** (`make audit-all-only`: the echo theorem's FOURTEEN,
the system theorem's thirteen).  No echo file and no landed statement of
`AppFile.v`/`FileDisc.v` moves: the diff to existing files is FOUR LINES
of `iris/_CoqProject`.

**WHAT LANDED** (four new files, 4,900 lines).

`iris/FileOutPure.v` (2,140) — `EchoOutPure.v`'s twin at `FileDisc.sessf`.
`pending_at_f`/`pending_f`/`D_from_f`/`D_f` with the era's boot state
carried as an `option fst` (`f0_st` reads it); F1 `D_f_pending_sessf` /
`D_f_stage_prefix`; F2 `D2_next_input_f` (with `sessf_length_lt`, which
`FileDisc` does not state); F3 is `EchoOutPure.read_window_prefix`
verbatim, reached through `disc_byte_ok_f`/`disc_seg_f_no_erase`/
`disc_seg_f_no_ctrl_d`; F4 `good_out_f_of_stage`.  Beside them:
`disc_f`'s five closure laws (`disc_f_out`, `_in`, `_power`, `_other`,
`_prefix` — `FileDisc` landed `disc_input_f`'s full set and none of
these, and the ledger's three steps are stated at exactly them); the
era's process-byte cursor (`proc_before_f`, `proc_stream_f`, `pcount_f`,
`write_stage_byte_f`, `proc_stream_f_round_banner_open`); the stage
record `fostage` and its two length laws (`cs_len_ok_f`, `ps_len_ok_f`)
with `feout_pure`; and `sessf_prefix_det2`.

`iris/FileOut.v` (2,265) — the claim, the tag, the turn, the steps and
the ledger.  `fecl`, `ftag`, `fturn`, `f0_auth`/`f0_lb`/`file_era_pin`;
`fecl_close`, `fecl_open`, `fecl_sup`, `fecl_arm`, `fecl_lt`,
`fecl_step_write_first`, `fecl_step_write`, `fecl_step_write_blk`,
`fecl_step_write_pro`, `fecl_step_read`, `fecl_step_echo`,
`fecl_step_byte`, `fecl_drain`; `file_led` with `file_led_init`,
`file_led_pow`, `file_led_tx`, `file_led_rx`, `file_led_phi`;
`file_birth_all`.

`iris/FileLinks.v` (300) — `file_write_link`, `_first`, `_blk`, `_pro`,
`file_write_link_taint`, `file_cons_link_of_taint`, `file_read_link`
(with `fread_ret`), `file_close_link`, `file_byte_link`,
`file_cons_run`, and `file_happ_echo` (`App.al_echo`, a closed
entailment).

`iris/AppFileRec.v` (370) — AppFile layer B: `file_R`, `file_tag`,
`file_kill`, `file_cons`, `file_turn`, `file_ifc`, the record `app_file`,
`file_Happ_init` at the literal image, `file_Hphi_R`, and
`Global Instance file_laws : App.xv6_app_laws app_file` with EVERY field
but `al_programs` discharged.

**ASSUMPTIONS.**  `Print Assumptions` is *Closed under the global
context* on `good_out_f_of_stage`, `sessf_prefix_det2`, `D2_next_input_f`,
`D_f_pending_sessf`, `disc_f_in`, `write_stage_byte_f`, `alts_pad_ok`
(no axioms at all, not even PrimString), and on `fecl_step_echo`,
`fecl_step_write_pro`, `fecl_drain`, `file_led_pow`, `file_led_tx`,
`file_led_rx`, `file_led_phi`, `file_happ_echo`, `file_write_link_first`,
`file_write_link_pro`, `file_read_link`, `file_al_tx`, `file_al_rx`,
`file_al_pow`, `file_al_echo`, `file_Happ_init`, `file_Hphi_R` it is the
eleven PrimString/PrimInt63 primitives and nothing else.  `file_laws`
adds the two Sail reservation `Parameter`s the TREE audit already prints
(`resv_matches`, `resv_is_valid`), through `InitBoot.init_boot_bundle`.
NOTHING is `Admitted`.

**THE TWO SECTION HYPOTHESES, and why neither is an `Admitted`.**

1. `al_programs` — lane SH-ROUND's, taken as `Context (Hprog : …)` in
   `AppFileRec`'s `Section FileLaws`, so `file_laws` simply does not
   exist until that lane lands (the brief's preferred shape).
2. **`Decision (FileDisc.disc_f h)`** — `Context `{Hdf : forall hh,
   Decision (disc_f hh)}` in `FileOut.v`, from the ledger onwards.

**BLOCKER 1: THE TAINT COUNTER NEEDS `disc_f` DECIDED, AND `disc_f` IS
NOT DECIDABLE AS LANDED.**  `EchoOut.echo_led`'s counter is at
`decide (EchoDisc.disc h)` and the FILE ledger's must be at
`decide (FileDisc.disc_f h)`: the conclusion's antecedent is the file
discipline and `disc_f h` does NOT imply `disc h` (a `cat f` line is not
an echo line, so `disc_f_disc`'s equivalence needs the echo-only
premise).  So the design page's "`file_led` = echo's counter" and
"`ftag h := etag h ∗ fl_lb …`" are both WRONG as stated: `etag` carries
`⌜disc h⌝ ∨ T`, which says nothing about the file session.  The landed
shapes are `⌜trace_shape h true⌝ ∗ (⌜disc_f h⌝ ∨ file_taint c) ∗
fl_lb c (efl_of h)` and the counter at `decide (disc_f h)`.
ONLY `al_rx` HAS TO DECIDE (every other ledger step wants a `decide_ext`
over one of `disc_f`'s closure laws, all of which this lane proved), and
there it must hand out the byte's tag, whose left arm IS the discipline —
and the tag's consumers (the echo shift's `ecl_open`, hence
`D2_next_input_f`) need D1/D2 at the open cycle, not only D3.  So no
decidable WEAKENING of `disc_f` serves: the predicate the counter reads
must be implied by `disc_f` AND sufficient for the shift, i.e. equivalent
to it.
THE OBSTACLE IS NOT THE RESOLUTIONS, it is the BOOT STATE.  `disc_seg_f'`
is `∃ ps cs, …`, and `EchoDisc`'s `pro_cands`/`bounded_lists` machinery
ports (the extra work is a `sel` enumerator: `sel_ok (echo_chunks ws) sel`
bounds `sel` to the strictly-increasing sublists of
`seq 0 (length (echo_chunks ws))`).  What does not port is `disc_f`'s own
`∃ s : fst, fst_ok s ∧ …`, which ranges over ALL byte lists.  THE FIX,
priced: the witness set is finite once one observes that D1/D2 put the
WHOLE transcript for the input typed so far on the wire, so every
completed `RCRan` round's content appears on the wire in full and a
cycle's admissible boot states are `None` plus the contiguous substrings
of `obs_wire Uart0 seg` — a canonicalisation lemma of the shape
`EchoDisc.pro_canon` has for the prologue.  That is a lane
(`FileDiscDec.v`), not a step; it is NOT on the critical path for any
program lane, since every link and every other ledger step is closed.

**BLOCKER 2: `file_phi`'s `echof_lines_before` IS NOT REACHABLE, AND THE
INTERFACE IS WHY.**  `file_led`'s conjunct is `file_good h`, which is
`FileDisc.file_phi`'s body with TWO weakenings: the admissibility clause
is at `FileDisc.echof_lines_of h` (the lines of the WHOLE history) where
the design asks for `echof_lines_before h (S k)` (the lines of strictly
EARLIER cycles), and the guarded first clause (`s0s !! 0 = Some None`) is
dropped with it.  So `AppFileRec.file_phi` is
`fun _ h => disc_f h -> file_good h`, not `FileDisc.file_phi`.
WHY.  The drain (`fecl_drain`) hands the ledger the era's boot state
`s0` together with `AppFile.f_typed`'s witness — `∃ ls, fl_lb c ls ∗
⌜f_bytes_typed ls s0⌝` — and the ledger can only read that lower bound
against its own authority, which gives `ls ⊑ efl_of h`.  NOTHING RECORDS
WHEN THE BOUND WAS TAKEN.  Two lower bounds of a `mono_list` are
comparable but nothing says WHICH WAY, and the era-start list cannot be
attached to the witness on the way in: `App.app_boot` (which carries the
deed's witness) is produced by the TRANSPORT (`al_xfer`) and
`App.app_turn` by the LEDGER (`al_pow`), and the two never meet — a
transport is `□ (∀ r av, ▷ A r av ==∗ …)` and cannot produce a resource
it was not given.
THE FIX, priced.  `AppFile.f_typed` must carry the witness at a list the
ledger can bound: either (a) an INDEX (`mono_list_idx_own` at `j` with
`⌜j < n⌝`) where `n` is the era's line count, pinned in a `fe_n` field of
`FileOut.file_era` at `al_pow` (the ledger holds `fl_auth c (efl_of h)`
exactly there, and `efl_of h = echof_lines_before (h ++ [ObsPowerOn])
(S (obs_boots h))` because the new cycle is empty — that half IS
provable), with the bound paid by the LINK out of the discipline (at
init's first byte the era's input is empty, which this lane already
proves inside `fecl_step_write_first`); or (b) milestone 2's commit
receipt, which makes the boot state exact and the whole clause a
singleton.  (a) is a claim-lane change to `AppFile.f_typed` plus one
premise on `file_write_link_first`; nothing else in this lane moves.

**WHAT ELSE THE DESIGN SAID THAT THE PROOFS CORRECTED.**

- **`EchoOutPure.cs_ok` HAS NO TWIN.**  Echo's range condition is the
  TOTAL `∀ i, cs !!! i < 4`, which is free out of range because `!!!`
  reads 0 and `0 < 4`.  Out of range the file's entry decodes to
  `REcho 0`, and `ralt_ok (LCat) (REcho 0)` is FALSE — so no total
  condition works.  What the stage carries is the POINTWISE
  `FileOutPure.alts_pre I cs` ("every entry the list HAS is an
  alternative the line at its index admits"), and `FileDisc.alts_ok` —
  which the determinacy theorem and `good_out_f` are stated at — is
  reached by PADDING (`alts_pad`, `alts_pad_ok`, `alts_pad_pro_idx`,
  `stage_sessf_pad`).  The padding moves no prologue round, because
  `pro_idx_f` reads the list only through `ralt_panic` and no default
  alternative panics.  This is the single largest shape difference from
  `EchoOut.v` and it touches the echo step, the drain and `good_out_f`.
- **DETERMINACY NEEDS TWO BOOT STATES, and gets them free.**  MODEL's
  `sessf_prefix_det` fixes ONE `s` for both witnesses; the claim must
  compare the DISCIPLINE's witness (a state the trace predicate chose
  existentially) against ITS OWN (filed off the deed), and the two have
  no reason to be equal.  `FileDisc.alt_seq_f_prefix_det` ALREADY takes
  the two apart — a non-panic alternative's output is a `$`-free run
  followed by the prompt whatever the file holds — so
  `FileOutPure.sessf_prefix_det2` is MODEL's lemma restated at `s` and
  `s'`, 60 lines.  `FileDisc.sessf_prefix_det` can be generalised in
  place when MODEL's file is next opened; until then the twin stands
  beside it.
- **`feout_pure`'s `o_f0` CLAUSE IS AN IFF, not an implication.**  The
  design says "`o_f0 = None -> o_E = [] /\ o_w = []`"; the CONVERSE is
  what `file_write_link_first` needs (to know the state is not filed
  yet), and it is maintained because the ordinary writes all carry
  `f0_lb` (so they never run at `None`) and the echo is refuted at an
  empty transcript by `sessf_nonnil`.
- **THE ERA'S FIRST BYTE IS A PROLOGUE-CHOICE WRITE, not a plain one.**
  The design says "`file_write_link_first` … at cursor `P = 0`"; at
  `ps0 = []` the plain write's premise
  `proc_stream_f [] [] s0 [] !! 0 = Some b` is UNSATISFIABLE
  (`pro_of [] = []`), so the lemma would have been vacuous.  The landed
  `file_write_link_first` is the `_pro` shape at the empty stage, and it
  needs NO premise about the stage: `turn v 0` pins the cursor,
  `pro_pin_f` then pins the era's input to `[]`, `ps_len_ok_f`'s second
  clause pins the prologue resolution to `[]`, `cs_len_ok_f` pins the
  choice list, and the `o_f0` IFF then says the boot state is unfiled.
- **THE RECORD'S FIXED PART IS NOT `AppFile.file_fixed`.**  The second
  per-era map needs a gname that outlives every era and
  `file_fixed = echo_fixed * gname` has none to spare.  Rather than move
  a landed statement (lanes F-OPEN and F-WRITE are building on it), the
  RECORD's `app_fixed` is `FileOut.file_gn` — AppFile's paired with that
  one gname — and every AppFile lemma is read at `fgn_cl c`.
- **THE READ EXPORTS A TRUNCATED CHOICE LIST.**  `EchoOut.read_ret`
  hands out the claim's own `cs0`; here `alts_pre` ties every entry to
  the line at its index and the claim's list may run past the window's
  far end, so `fread_ret` exports `take (nlines (snd <$> (dl ++ ws)))
  (fo_cs so)` and `rd_stage_f` at that.

**EXACTLY WHAT A PROGRAM'S LINK PREMISE LOOKS LIKE NOW.**  The ordinary
byte, verbatim (`FileLinks.file_write_link`) — echo's argument list with
`f0_lb vf s0` beside the three bounds, `file_era_pin g k vf` beside
`era_pin`, and the byte read off `proc_stream_f` AT THE ERA'S BOOT STATE:

```coq
Lemma file_write_link (k : nat) (v : era_pins) (vf : file_era) (P : nat)
    (b : bv 8) (ps0 cs0 : list nat) (s0 : fst) (I0 : list (bv 8))
    (Φ : iProp Σ) :
  (nlines I0 <= length cs0)%nat ->
  pro_pin_f ps0 cs0 I0 ->
  proc_stream_f ps0 cs0 (Some s0) I0 !! P = Some b ->
  era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
  ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
  (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0
     ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
  out_link Uart0 k b Φ.
```

and the BLOCK-OPENING one (`file_write_link_blk`) asks, where echo asked
for `a < 4` and `line_alts_of (last_ws I0) !!! a !! 0 = Some b`:

```coq
  ralt_ok (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a) ->
  cont (fst_upto cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat)
       (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a)
    !! 0%nat = Some b ->
```

i.e. the program names the ALTERNATIVE its round is taking, proves the
LINE ADMITS it, and proves its byte is the first of that alternative's
output AT THE STATE `fst_upto` says the file is in.  `fst_upto` is the
whole of what the file adds to a writer's obligation, and a program
computes it from `s0` (which `f0_lb` pins), the bodies of `I0` (which
`inp_lb` pins) and the choices (which `cs_lb` pins) — no history, no
ledger, no deed.

**THE ONE THING LANE SH-ROUND NEEDS FIRST.**  `AppFileRec.file_laws` is
already an instance under `Context (Hprog : …)` whose statement is
`App.xv6_app_laws`'s `al_programs` field verbatim at `app_file`; SH-ROUND
supplies exactly that and the record closes.  What it must have in hand
at <init>'s first instruction is `app_turn app_file c (S gen_id)` =
`FileOut.fturn c (S gen_id)` — `EchoOut.eturn`'s five components plus
`file_era_pin c (S gen_id) vf` — and `app_boot app_file c (S gen_id) r` =
`AppFile.file_boot`, whose `▷ (f_typed c s ∨ file_taint c)` is stripped
and handed to `FileLinks.file_write_link_first` AS ITS `f0_typed g s0 ∨
file_taint` ARGUMENT, at the era's very first banner byte (`a = 3`,
`pro_alts !!! 3 !! 0 = Some b`).  That call is what mints `f0_lb vf s0`,
and every later write of the era — init's banner tail, sh's prompt, the
child's diagnostics, cat's content — carries it.  Do NOT try to file the
boot state at a plain `file_write_link`: at the era's start the prologue
resolution is empty and the plain link's premise is unsatisfiable.

### FILE-DEC (2026-09-17) — `disc_f` IS DECIDABLE; the boot state canonicalises to the wire

Branch `app-file/file-dec`, commit `efea93703`.  Whole tree GREEN on the
lane's remote tree (`run-on-gcp --proofs -k`, `EXIT=0`, zero `Error`);
**both audits unchanged** (`make audit-all-only`: the echo theorem's
FOURTEEN, the system theorem's thirteen).  `Print Assumptions
disc_f_dec` is *Closed under the global context* — no axioms at all, not
even the PrimString/PrimInt63 primitives.  Nothing is `Admitted`.

**WHAT LANDED.**  One new file, `iris/FileDiscDec.v` (643 lines), in
`iris/_CoqProject` right after `FileDisc.v`, ending in `Global Instance
disc_f_dec h : Decision (disc_f h)`.  **BLOCKER 1 IS CLOSED**:
`FileOut.v`'s `Context {Hdf : forall hh, Decision (disc_f hh)}` and
`AppFileRec.v`'s two copies are deleted and the three files rebuild
against the instance; the diff to them is those three `Context` lines
and their header comments, nothing else.  `AppFileRec`'s remaining
section hypothesis is `al_programs` alone.

- D1 `fcont_ok_iff` / `fcont_ok_dec` / `fst_ok_dec` — the `∃ v, bs = v ++
  [wl_nl]` arm IS `last bs = Some wl_nl ∧ Forall wl_body_byte (removelast
  bs)`, as the ruling said.
- D2 `sel_cands n` (the strictly increasing lists over `seq 0 n`, built by
  appending the largest index last), `elem_of_sel_cands`, `sel_ok_cands`
  (`sel_ok cs sel <-> sel ∈ sel_cands (length cs)`, against `FileState`'s
  actual definition); `ralt_fix_cands`/`ralt_cands` (the codes one line
  shape admits) with `elem_of_ralt_cands` and `ralt_cands_canon`;
  `alts_cands`/`elem_of_alts_cands`/`alts_cands_alts_ok`.
- D3 `alt_seq_f_pro_len`, `sessf_pro_len` — the length bound at
  `pro_idx_f`'s three panic alternatives.
- D4 `fst_upto_vs_nil`, `cont_state_ne`, `alt_cont_f_cat`,
  `alt_blk_f_infix`, `alt_seq_f_split`, `sessf_infix_blk`,
  `obs_wire_prefix`, `infixed`/`substrings`/`elem_of_substrings`,
  `scands`, and the design's lemma `disc_seg_f'_canon`.
- D5 `disc_seg_f'_ex_dec`, then `disc_f_dec`.

**WHAT THE DESIGN SAID THAT THE PROOFS CORRECTED.**

- **`bounded_lists` DOES NOT PORT; `pro_cands`/`pro_canon` port
  VERBATIM.**  The ruling had it the other way round ("the rest (`∃ ps
  cs`) ports from `EchoDisc.disc_seg'_dec` (`pro_cands`,
  `bounded_lists`, plus an enumerator of `sel`s)").  The codes a line
  admits are not an initial segment of ℕ — `ralt_enc (RFRan sel) = 15 +
  12 * encode_nat sel` — so `bounded_lists k n` cannot enumerate them and
  `alts_cands` is a per-line enumerator.  `EchoDisc.pro_canon`, on the
  other hand, never mentions `cs` at all, so D3's "port `pro_canon` to
  `pro_idx_f`" was unnecessary work: it is applied unchanged, and only
  `EchoDisc.alt_seq_pro_len`'s LENGTH bound had to be restated at
  `pro_idx_f` (three panic alternatives instead of `cs !!! q = 3`).
- **`ralt_ok l (ralt_dec c) -> c = ralt_enc (ralt_dec c)` IS REFUTED as a
  route**, which is why the canonicalisation of `cs` is the one that
  landed.  `ralt_dec` accepts a code `c` with `c mod 12 = 3` and `c ≥ 15`
  as `RFRan (default [] (decode_nat ((c - 15) / 12)))`, and
  `ralt_enc (RFRan sel) = 15 + 12 * encode_nat sel` — `encode_nat` need
  not be onto, so nothing forces `c` to be its own alternative's code,
  and `alts_ok` (stated at `ralt_dec c`) admits such a `c`.  Taken
  instead: `cs_canon cs := (ralt_enc ∘ ralt_dec) <$> cs`, sound because
  EVERY consumer of `cs` reads it only through `ralt_at = ralt_dec ∘
  (!!!)` — checked one by one and used as `cs_canon_at`,
  `pro_idx_f_canon`, `fst_upto_canon`, `alt_cont_f_canon`,
  `alt_seq_f_canon`, `sessf_canon`, `alts_ok_cs_canon`,
  `disc_pt_all_f_canon`.  The one wrinkle: `!!!` out of range reads `0`,
  and `ralt_enc (ralt_dec 0) = 0`, so the canonical map fixes the
  out-of-range reading too (`fdd_lookup_total_fmap`).
- **`fst_upto_derived` AS WRITTEN IN THE BRIEF IS FALSE; the pointwise
  PAIR is what is true.**  "the state before a round is either `s` itself
  or independent of `s`" fails at `RFOpenM`, the only `fsm` arm that
  READS the state: `fsm None _ RFOpenM = Some []` while `fsm (Some bs) _
  RFOpenM = Some bs`, so the value is `s` at a present `s` and `Some []`
  at an absent one — neither `= s` for all `s` nor `s`-independent.  What
  holds, and what the induction needs, is the two chains TOGETHER
  (`fst_upto_vs_nil`): for every `i`, either `fst_upto cs s bs i = s` AND
  `fst_upto cs (Some []) bs i = Some []`, or the two are equal.  The
  second conjunct of the left arm is exactly what carries `RFOpenM`: at
  `s = None` the two chains MERGE there, at `s = Some bs` they do not,
  and either way the disjunction is restored.
- **THE CASE SPLIT IS NOT AT "THE LAST CHECKED PREFIX", and needs no
  monotonicity.**  It is the decidable `Exists p ∈ in_pres seg, Exists i
  < nlines (ins p), alt_cont_f ps cs (Some b0) … i <> alt_cont_f ps cs
  (Some []) … i`.  Positive: `cont_state_ne` (`cont` reads the state at
  `RCRan` and at no other alternative) forces that round to be `RCRan` at
  an `s`-derived state, and the content is then contiguous in that
  prefix's wire (`alt_blk_f_infix`, `sessf_infix_blk`, two `prefix_of`
  steps through `obs_wire_prefix`), so `Some b0 ∈ scands seg`.  Negative:
  every block agrees (`alt_seq_f_cont_ext`) and `Some []` serves.  The
  shape of "checked prefix" `in_pres` gives is ONE ENTRY PER INPUT BYTE,
  the segment truncated JUST BEFORE that byte (`EchoDisc.in_pres`); the
  only property used is `in_pres_prefix_all` (each entry is a prefix of
  `seg`).
- **`disc_f_dec` MUST BE `Qed`, not `Defined`.**  With a transparent
  instance ssreflect's `rewrite /file_led` (unfold AND simplify)
  iota-reduces `if decide (disc_f []) then 0%nat else 1%nat` at the empty
  history, and `FileOut.file_led_init`'s `rewrite decide_True` reports
  "The LHS of decide_True does not match any subterm of the goal".
  Opaque, exactly as `EchoDisc.disc_dec` is.  (`disc_seg_f'_ex_dec` and
  the small instances stay `Defined`; nothing evaluates any of them.)
- **Scope note, not a correction**: `FileDisc.disc_seg_f'`'s comment
  ("`disc_seg_f'` is NOT claimed decidable: the search over the
  resolutions that `EchoDisc` can run needs a bound on `sel`, and no
  consumer asks for it") is superseded for the EXISTENTIAL form, which is
  what `disc_f` uses and what this lane decides.  `disc_seg_f' s seg` at
  a GIVEN `s` is still not claimed decidable — nothing asks for it — but
  it falls out of the same search.

**ONE TACTIC TRAP, worth a durable note.**  `lia` does not see through a
beta-redex hypothesis.  `Forall (fun j => j < m) l` taken apart by
`Forall_cons_1` / `Forall_singleton` / `Forall_forall` leaves `(fun j =>
j < m) x`, and `lia` answers *Cannot find witness* while the goal `x < n`
sits right there.  `cbn beta in H` first.  (The goal side is fine —
`apply` beta-reduces what it produces.)  Also: `apply Forall_singleton in
H` takes stdpp's iff the WRONG WAY (it wraps `H` instead of unwrapping
it); `rewrite Forall_singleton in H` is the one that works.
