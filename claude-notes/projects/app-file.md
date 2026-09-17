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
- [x] **MODEL** landed (`FileDisc.v` on `app-file/model`; design §1 corrected as it found — see its findings).

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

### F-WRITE — THE MOVE LANDS, THE CHAIN DOES NOT; THREE CONTRACT FACTS, NAMED (2026-09-17)

**The lane's verdict in one line: the APPEND step of design section 2 is
landed and closed, and `file_awrite_chain` is REFUTED at the shape the brief
asks for -- not by proof difficulty but because a node of
`FsAbsWriteFire.awrite_chain` is a `∀` over the fire's data with no premise
slot, and the file claim (unlike the tree claim) has to re-establish
`AppFile.f_typed` at `blk_splice off bs bs0` knowing neither `off`, nor `bs`,
nor that the row is `f`'s.  Deliverable 3 sits behind it.**

**WHAT LANDED** (`iris/FileWrite.v`, additive, commit `f9ec2f1c2`; whole tree
green on the lane's remote tree, 0 `Error`; `Proof using` on every result in
the section; `Print Assumptions` closed under the global context but the
eleven `PrimString`/`PrimInt63` primitives on `file_awrite_phases`,
`file_awrite_node`, `file_claim_read`, and closed outright on the pure ones).

- `FileWrite.file_wq` — THE CURSOR of design section 3: `fown r (Some (subseq
  (echo_chunks ws) sel))`, `⌜off = length (subseq …)⌝`, `⌜line_ok ws⌝`,
  `⌜sel_ok (echo_chunks ws) sel⌝`, `fl_lb c ls ∗ ⌜ws ∈ ls⌝` — or the taint,
  as `TreeMove.tree_wq`'s.
- `FileWrite.file_claim_read` — phase 1's read, `TreeMove.tree_claim_read`'s
  shape at `AppFile.file_deed_law`: the deed goes in, comes back, and the
  fact is `f_ok (abs_view I) s` with its typed witness, or the taint.
- `FileWrite.file_awrite_phases` — **ONE CHUNK, BOTH PHASES**, the brief's
  item 1 in full: phase 1 parks the deed at the appended content
  (`AppFile.file_app_step_park` at `f_typed c (Some (subseq … (sel ++ [jx])))`,
  built by `AppFile.f_typed_some` off `FileState.sel_ok_snoc`), phase 2 is
  `AppFile.file_resync` at `sel ++ [jx]`.  Visibility is free: `wri_pre`'s own
  `0 < length bs` makes `subseq … (sel ++ [jx]) <> subseq … sel`, so
  `FileState.echo_args_chunks_nonnil` is not needed.
- `FileWrite.file_awrite_full_anchored` / `file_awrite_node` — `awrite_full_at`
  WITH THREE PURE RELAYS ADDED AND NOTHING ELSE CHANGED, and the proof that
  the cursor pays it.  This is the precise statement of the ask: the day the
  relays exist, the chain is this node under `awrite_chain`'s induction.
- The delta algebra the step needs, all new: `delta_write_aents` /
  `_astep` / `_apath` / `_arun` (**a write is invisible to every directory's
  entry map** — at the written inum because a file has no entries either way,
  everywhere else because the row is untouched), `file_pin_write`,
  `file_pin_cat` (cat's pins are `FsConsPin.file_pin`'s fourth instance, a
  `reflexivity`), `cons_present_write` / `cons_absent_write` (**the console
  needs no premise at all**: its row is a DEVICE and `delta_write` at a
  non-file row is the identity), `file_fs_pure_write`, `f_ok_delta_write`
  (lane F-OPEN's `FileDeltas.v` is not on this branch, so the one lemma the
  brief allows is proved here), `blk_splice_end`
  (`blk_splice (length bs) sub bs = bs ++ sub`), and
  `file_write_premises_sat`, the vacuity witness for the new pure premises.

**REFUTED / BLOCKED — THREE FACTS, EACH A CONTRACT FACT.**

1. **THE OFFSET, AND THE BRIEF'S ROUTE TO IT IS CLOSED.**  The brief says to
   park `⌜off = length bs0⌝` as a pure premise "so that they are provable
   today and the tie discharges the premise the day the held member exists".
   That works for the PHASES lemma (landed) and **cannot work for the chain**:
   `awrite_full_at`'s node quantifies `off` with only `wri_pre`'s
   `off <= length bs0` on it, so the pure `∀ I off bs bs0 nl, wri_pre … ->
   off = length bs0` is FALSE at any row with non-empty content (instantiate
   `off := 0`) — the unsatisfiable-`∀`-premise trap of durable-notes.  And no
   RESOURCE can replace it either: the node is handed the KERNEL's half
   `off_gv γo (1/2) off`, and in mode `hand` the user's half is inside the
   kernel for the duration of the call (`FdPark.off_supply_of_st_at_eq` takes
   the caller's `uoff_rcpt` at the syscall boundary and spends it at each
   fire, `ProofFilewrite`'s `Hoinvw`), so nothing the client holds across the
   fire can agree with it.  **The equation has to be RELAYED**: the held
   branch of `SpecFilewrite.filewrite_in` must instantiate the chain at nodes
   carrying `⌜off = off0 + p⌝` at the caller's own anchor — design/user-write.md
   section 3c's anchored cursor, and it is `FileWrite.file_awrite_full_anchored`'s
   RELAY 2.
2. **THE CHUNK'S LENGTH — NEW, and nothing in the campaign records it.**
   `SpecCopyin.ubytes_at M ua bs` is a pure `∀` over `bs`'s own indices and is
   therefore PREFIX-CLOSED: the node says "these bytes are a run of the
   caller's image at this base", never "this is the whole chunk".  Nothing in
   `wri_pre` or in `awrite_full_at` bounds `length bs` by the remaining count
   — the count `n` is not even a parameter of `awrite_chain`, only `wchunks n`
   is.  So the client cannot identify `bs` with `echo_chunks ws !!! jx` AT THE
   FIRE; it can only do so afterwards, off `write_post_ok_at`'s
   `⌜|concat bss| = n⌝`, and that is too late because `file_step_park` needs
   `f_typed c s'` BEFORE the delta.  The kernel's own fire knows the number
   (it is what it passed to writei); the contract drops it.  RELAY 3.
3. **THE PARTIAL ARM'S DISTURBED TAIL — and this one refutes the MODEL, not
   just the proof.**  `awrite_part_at`'s delta is `delta_write i off bs` with
   only `take r bs` the caller's and `⌜length bs <= r + BSIZE⌝`: writei commits
   the partially copied block, so **up to one block of bytes nobody names
   lands in `f`**.  `AppFile.f_bytes_typed` admits only whole-chunk
   subsequences, so that arm's step cannot be paid at all — and it is one of
   the two arms the kernel may pick at EVERY node (`awrite_chain`'s `∧` is the
   kernel's choice, which is why `TreeMove.tree_awrite_chain` proves both).
   **design/app-file.md section 0's limit 1 ("the concatenation of the SUBSET
   of echo's chunks that landed") is therefore too strong.**  Two ways out,
   both the designer's call: admit a partial last chunk plus a bounded junk
   tail in `FileDisc`'s `ralt`/`fsm` and in `f_bytes_typed`; or refute the
   short-write arm, which is the capacity conjunct section 0 explicitly
   declines to take.  Note the first way out does NOT rescue item 1 above: with
   `off` unknown the splice may OVERWRITE inside the existing content, and no
   "prefix plus junk tail" predicate is closed under that either.

**WHAT `AppFile.v` NEEDS CHANGED (one thing, and it is RELAY 1).**
`f_ok av (Some bs)` is `∃ i, astep av ROOTINO fname_f = Some i /\ av !! i =
Some (MkAnode (AFile bs) 1)` — **the inum is existential**, so a deed holder
learns the CONTENT of `f` and never that the row its descriptor sits on IS
`f`'s.  `file_awrite_phases` therefore takes `⌜astep (abs_view I) ROOTINO
fname_f = Some i⌝` as a premise, and no chain node can supply it.  Worse, the
existential is not even stable: `AppFile.file_step_free`'s premise
`∀ s, f_ok av s -> f_ok av' s` lets a free step RELOCATE `f` to a different
inum at the same content.  The fix is to name the inum — either `f_state`
carries it (`∃ i s, ⌜astep av ROOTINO fname_f = Some i⌝ ∗ …` with `i` pinned by
a ghost the deed's holder shares) or the deed's state becomes
`option (Z * list (bv 8))`.  Everything else in `AppFile.v` was exactly right
for this lane: `file_step_park` / `file_app_step_park` / `file_resync` /
`file_deed_law` / `f_typed_some` / `fown` were used verbatim and nothing else
was wanted.  (Second, much smaller: there is no `file_app_step_taint`, the
twin of `TreeMove.tree_app_step_taint`; `FileWrite.v` proves it locally and it
belongs beside `file_app_step_park`.)

**THE EXACT PREMISE THE HELD MEMBER MUST DISCHARGE**, at the shape it is
stated in: `FileWrite.file_awrite_full_anchored`'s RELAY 2, `⌜off = off0⌝`,
where `off0` is the cursor's anchor `length (subseq (echo_chunks ws) sel)` —
i.e. `FdPark.off_supply_of_st_at_eq`'s tie `⌜m = OffHeld -> off' = off⌝` read
at `OffHeld` and RELAYED INTO THE CHAIN NODE, not merely held by the kernel.
That is a clause on the HELD branch of `SpecFilewrite.filewrite_in`
(OFF-HAND's finding 4 is where that branch is cut), not on any U-tier
statement.

**THE ONE THING LANE ECHO-FILE NEEDS FIRST.**  A ruling on findings 2 and 3,
because they decide `UEchoFile`'s post before a line of it is written:
either (a) the held branch of `filewrite_in` gains the anchored-and-sized
node (relays 2 and 3) AND the short-write arm is refuted, and then
`UEchoFile` gets design section 5.2's exact post, `sel ++ [j]` per write; or
(b) the model widens to admit a partial last chunk with a bounded junk tail,
and then `f_bytes_typed`, `FileDisc.ralt`/`fsm` and design section 0's
alternative list all move first.  Until one of them is taken, the only thing
`UEchoFile` can carry across a `write` is `TreeMove.tree_wq`'s existential
cursor, which says nothing about `f`'s content and so proves none of the
application's claim.  `FileWrite.file_awrite_node` is the piece that turns
either ruling into the chain in a dozen lines.

### OFF-HAND-2 (kernel/spec tier, 2026-09-17) — THE EXEC WAND CARRIES THE ROW; D1–D3 ARE GATED ON OFF-HAND-3's COUNTER, AND SO IS HALF OF D4

**The lane's verdict in one line: the brief's D1 (and therefore D2 and D3)
cannot land before the U-tier carrier the brief defers to OFF-HAND-3,
because relaxing the pin makes `FdSlots.foff_row` irreducible at the two
kernel fire sites and the only repair routes through
`FsAbsInvFire.fsabs_fileread_in` / `fsabs_filewrite_in`, which serve an
ARBITRARY state on behalf of the generic tier.  D4's kernel half landed in
full; D4's generic-mint half is blocked at the same wall, one file lower
than the brief expected.  Everything below is checked in the tree, not
inferred.**

**WHAT LANDED** (whole tree green on the lane's remote tree,
`make -f CoqMakefile -j32 -k`, `EXIT=0`, zero `Error`; `make -n` reports
nothing left; audits unchanged).  Sixteen files, one new premise:
THE EXEC CROSSING'S SLOT WANDS NOW CARRY THE RESUMED KEY'S ALL-PARKED ROW,
AND THE KERNEL PAYS IT.

- `SpecKexec.exec_slot_pre` — both wands gain `⌜fdv_all_parked (uvis_fd W')⌝`,
  between the pid row and `my_pay`.  This is §8.3's finding C's premise, at
  the place `PinnedExec.v:281`'s note said it belongs.
- `SpecKexec.wp_kexec_sconf_body` gains the pure premise `fdv_all_parked sts`
  (first in its chain), relayed by `SpecSysExec.wp_sys_exec_sconf_body`, and
  spent in `ProofKexec.kxau_close` — the ONE place in the tree that applies
  either wand — through `SpecKexec.exec_key_fd`.
- `ProofSyscall`'s exec arm pays it off the machine:
  `iDestruct (proc_priv_parked with "Hpriv Hufrag") as %Hpkexec`.  This is
  the only tier that holds the process block and its descriptor bundle at
  one instant, and it is the ONE LINE that changes when the pin relaxes.
- `InitBoot.init_boot_bundle` gains a pure row `⌜fdv_all_parked sts⌝` beside
  its wand, because `ProofForkret.fkr_boot` — the first process's one exec —
  holds neither the array nor the bundle.  Its producers state it at `fdt0`
  (`InitBoot.init_boot_bundle_triv`, `UInitBoot.init_boot_bundle_of_pinned`,
  `SystemAdequacy.init_boot_of_sup` / `init_boot_of_triv`, `App`,
  `UTreeAdequacy`), all discharged by `FdSlots.fdv_all_parked_fdt0`.
- `UexecExecMint.uslot_mint` — the GENERIC application's entry decider — is
  narrowed to all-parked keys (`⌜fdv_all_parked (uvis_fd W)⌝` on its
  `□ (∀ W, …)`), and `InitBoot.init_boot_bundle_triv` relays it.  The
  generic application's chain is therefore closed end to end.

**STATEMENTS THAT CHANGED SHAPE** (exhaustive): `SpecKexec.exec_slot_pre`,
`SpecKexec.exec_au_pre_triv_at`, `SpecKexec.wp_kexec_sconf_body` (hence the
`KEXEC` module type), `SpecSysExec.wp_sys_exec_sconf_body` (hence `SYSEXEC`),
`ProofSysExec.sx_break_au`, `ProofKexec.kxau_close`,
`InitBoot.init_boot_bundle` and `init_boot_bundle_triv`,
`SystemAdequacy.init_boot_of_sup` and `init_boot_of_triv`,
`UexecExecMint.uslot_mint`.  **NO U-TIER STATEMENT MOVED** — `pex_slot`,
`image_entry`, `image_entry_taint`, `xv6_sbundle` and every row-15 family
field are byte-identical, and the row-15 `of_mode` field was NOT added (see
D2/D3 below: it could only ever be `OffParked` without D1).

**REFUTED / BLOCKED, with the evidence.**

1. **D1 IS BLOCKED, AND NOT BY `fdstate_ok_inj`.**  The `fp_om` move of the
   previous lane's finding 2 is right and its shape is cheap (one field, one
   extra parameter on `fdstate_ok`, ~57 textual sites).  What it costs is
   elsewhere: with the FD_INODE arm pinned at `fp_om pn` instead of at
   `OffParked`, `FileInvDefs.fdstate_ok_inode` hands the kernel a state at an
   OPAQUE mode, and `FdSlots.foff_row` does not reduce.  The two sites are
   `ProofFileread.v:2253` (`assert (Hstm : st = FdOpen true wbx (FdInode …
   OffParked))`, spent at `:2263` on `FdSlots.foff_row_inode_of`, which takes
   the literal `OffParked`) and `ProofFilewrite.v:4935`/`:4947`.  Both need
   either the arm split (payment `FdPark.uoff_rcpt`, which this brief defers)
   or a pure `⌜fdst_parked st⌝` premise.  EITHER REPAIR ENDS IN THE SAME
   PLACE: the payment rides `SpecFileread.fileread_in`'s inode arm (which the
   whole dispatcher chain threads opaquely, so nothing between moves — this
   part of the previous lane's finding 4 is confirmed), but its GENERIC
   builder `FsAbsInvFire.fsabs_fileread_in` / `fsabs_filewrite_in`
   (`UexecExecInst.v:969`/`:975`) builds it at an arbitrary `st` for a
   process that knows nothing of its descriptors, so it needs
   `⌜fdst_parked st⌝` — i.e. the class field `xv6_sbundle_of_supply_ne`
   narrowed to all-parked keys, i.e. every VERIFIED program able to state
   all-parkedness of its own table.  That is OFF-HAND-3's counter.  **D2 and
   D3 sit behind D1 and were not attempted**: without a held publish,
   `xfam`'s `of_mode` can only ever be `OffParked`, so adding it is dead
   weight, and weakening `UsysMemOk.usys_fd_ok`'s open arm would give up a
   true fact for nothing.

2. **D2's "ONE CONSUMER TO RE-ROUTE" DOES NOT EXIST.**  Checked by grep over
   the whole tree: `UsysMemOk.usys_fd_ok_parked` has ZERO proof consumers
   (only comments).  So do `ProcInv.proc_priv_parked`'s whole chain
   (`FileInvDefs.fdstate_ok_parked` → `file_ref_parked` →
   `ProcInv.ofile_slot_parked` → `ofile_slots_parked` → `proc_ofiles_parked`
   → `proc_priv_parked`) and `SpecKexec.kexec_image_ok_parked` /
   `exec_key_ok_parked`.  The generic Löb step does NOT read
   successor-parkedness off `usys_fd_ok` today — RA-3 landed the conjunct and
   the theorem, not a consumer.  **This lane gave `proc_priv_parked` its
   first consumer** (`ProofSyscall`'s exec arm, above), which is why it must
   NOT be deleted: it is now the payer of the exec crossing's row.

3. **D4's `FdPark.uoff_surr_at` CANNOT RIDE THE SLOT WANDS, for a reason
   about the kexec contract and not about the tier.**  `SpecKexec`'s frame
   carries NO descriptor resource at all — no `fd_frags`, no `fd_auths`, no
   `file_ref` — and `sts` is a free binder in `wp_kexec_sconf_body`
   (`SpecKexec.v:1303`'s own note says so).  `ProofKexec.kxau_close` spends
   `proc_priv` into the continuation one line before it applies either wand
   (`ProofKexec.v:679`), so even that is not in hand.  A RESOURCE on the
   wands would therefore have to be threaded through the whole five-phase
   kexec walk with nowhere to live; the PURE row is what the crossing can
   carry, and it is also what the consumer needs — the generic tier's own
   Löb step wants a FACT about every successor key, and the left disjunct of
   a `⌜…⌝ ∨ uoff_surrs` cannot be recovered from the right one.  **So the
   surrender's home is one tier up**: `ProofSyscall`'s exec arm, which holds
   `fd_frags` and `proc_priv`, is where `FdPark.uoff_surr_at` enters and
   `FdPark.fd_frags_park_at` converts it into exactly the pure row this lane
   landed.  One line changes there and nothing below it.

4. **D4's OTHER HALF — narrowing the generic mint at the TAINT arm — IS
   BLOCKED, AND THE WALL IS `UkSh.ush_gen_slot`.**  Attempted and reverted:
   putting the row on `ExecEntry.image_entry_taint` (and hence on
   `PinnedExec.pex_slot`'s taint arm, `UexecExecMint.uslot_mint_pay` /
   `uslot_mint_all`, `UInitBoot`, `UInitSh`, `UShEchoPay`, `UShKernel`)
   compiles all the way down to `UShKernel.v:655`, where
   `iExact "Hgen"` must produce `UkSh.ush_gen_slot` (`UkSh.v:6502`):
   `□ (∀ W, T -∗ my_pay (uvis_gen W) (ukn_pay N) -∗ uslot W)` — quantified
   over EVERY key and spent at `UkSh.ush_gen_run` (`:6509`) on the key inside
   `UkRun.urun`'s existential.  A verified program that is TAINTED hands its
   own run to the generic family at a table the U tier cannot name, so
   narrowing the family pushes the obligation exactly where the previous
   lane's finding 1 says it cannot go.  `uslot_mint` (the trivial-payload
   entry decider) is used ONLY by the generic application and is narrowed;
   `uslot_mint_pay` / `uslot_mint_all` are not.  `UkRun.urun_nopipe`
   (`UkRun.v:655`, a pure table fact carried across the run and maintained by
   `usys_fd_ok_nopipe`) is the SHAPE the carrier should copy — but its
   `∨ □ riscv_kill_cred` escape is exactly what a parked carrier may not
   have, since the taint is the case that needs the fact.

**THE ONE THING OFF-HAND-3 NEEDS FIRST: the counter must live where
`ush_gen_slot` can read it, i.e. inside `UkRun.urun`, and it must be a FACT
about the whole table and not a disjunction with the taint.**  The previous
lane's `uheld γ n` is right; what this lane adds is where it has to surface:
`UkRun.urun` needs a derived reading `urun_parked : urun N h m pc avail -∗
⌜fdv_all_parked fdv⌝` at `n = 0` (shaped like `UkRun.urun_nopipe` and
maintained across a round by `UsysMemOk.usys_fd_ok_parked`, which is already
proved and has been waiting for its first consumer), because
`UkSh.ush_gen_run` and `/init`'s twin are the sites that spend the generic
slot and they hold nothing else.  With that: `image_entry_taint` and the two
remaining mints narrow, D1's pin relaxation gets its `⌜fdst_parked st⌝` for
`fsabs_fileread_in` / `fsabs_filewrite_in` through
`FdPark.fdst_parked_of_key`, and `ProofSyscall`'s exec arm swaps
`proc_priv_parked` for the caller's `FdPark.uoff_surr_at` +
`fd_frags_park_at` — the one line this lane deliberately left as the pin's.

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

### F-OPEN (2026-09-17) — THE CREATE ARM AND THE READ SUPPLIERS LANDED; O_TRUNC IS A SECOND MOVE THE DEED CANNOT PAY

**The lane's verdict in one line: the open supplier is provable from the
deed at every leg the deed can reach, and the two it cannot are BOTH the
same shape — a syscall that must READ or MOVE the claim in TWO
∗-separated pieces while the deed pays for one.  Where the piece only
READS, the fix is free (split the deed's half; a fraction agrees and
refutes but does not park), and the lane took it.  Where the piece
MOVES, the fix is a kernel seam and is named below.**

**WHAT LANDED** (whole tree green on the lane's remote tree; every new
lemma `Proof using`; `Print Assumptions` on all 26 named results is
`Closed under the global context` or the eleven `PrimInt63`/`PrimString`
primitives and NOTHING else — no project axiom, no `resv_*`, no funext).

- `iris/FileDeltas.v` (deliverable 1, ~1100 lines, pure).  It is
  `FsConsPin` section 5 re-proved ONCE over two shapes that cover all
  four readings the claim needs — `name_absent nm av` (the root has no
  entry `nm`: `FsConsPin.cons_absent` and `FsFPin.f_absent` ARE this,
  definitionally) and `node_pin nm ino a av` (`FsConsPin.file_pin` and
  `cons_present_at` are this through their own `_astep`/`_of_parts`
  pair) — and at a NON-DIRECTORY child, which `delta_create_armed`
  collapses and `delta_create_dev` does not.  Legs: `name_absent_arm` /
  `_unarm` / `_create` / `_dots` / `_trunc` / `_write` and
  `node_pin_arm` / `_unarm` / `_unarm_fresh` / `_create` / `_create_at` /
  `_dots` / `_trunc_ne` / `_trunc_nonfile` / `_write_ne` /
  `_write_nonfile`.
  - `f_ok` at every leg: `f_ok_arm`, `f_ok_unarm`, `f_ok_unarm_none`,
    `f_ok_unarm_fresh`, `f_ok_create_other`, `f_ok_dots`,
    `f_ok_trunc_ne`, `f_ok_trunc_nil`, `f_ok_write_ne`; and `f`'s own
    three moves `f_ok_create_f`, `f_ok_trunc_f`, `f_ok_write_f`,
    `f_ok_append_f` with `blk_splice_append`.
  - the pins and the console under each: `file_fs_pure_arm` /
    `_unarm_fresh` / `_create` / `_dots` / `_trunc_ne` / `_write_ne`;
    `cons_absent_arm_nd` / `_create_nd` / `_dots` / `_trunc_any` /
    `_write_any` and the four `cons_present_*` twins.
  - the INUM SEPARATION: `subseq_length_le` (a chunk subset is no longer
    than the chunk list, through `NoDup_submseteq` and a
    Permutation-respecting `sum_list_with`), `f_bytes_typed_short` (a
    typed content is shorter than `EchoDisc.line_max` = 100),
    `init_bytes_length` / `sh_bytes_length` / `echo_bytes_length` /
    `cat_bytes_length` at **Z**, and `f_inum_not_pinned` /
    `f_inum_ne_cons`.
  - the three composite steps a supplier spends: `file_create_at_f`,
    `file_trunc_at_f`, `file_write_at_f` (each: the four pins, the
    console's two guards and `f_ok`, in one `split_and!`).
- `iris/FileOpen.v` (deliverable 2, ~900 lines).
  - **THE FRACTION** (section 1): `fdq r q s` is `AppFile.fdeed` at any
    fraction; `fdq_split` / `fdq_join` / `fdq_agree` / `fdq_whole_excl`
    and `file_deed_law_q` — a positive fraction AGREES with the exact arm
    and REFUTES the in-flight one, so it reads the claim; only the whole
    half parks.
  - `file_cons_law` (the era's console flag read through
    `AppFile.file_pred_cons` and `AppEcho.echo_cons_law`),
    `fclaim_facts`, `file_claim_read` (`TreeMove.tree_claim_read`'s twin:
    the deed in, the deed out, the three pure facts or the taint),
    `file_app_step_free_at`.
  - **THE CREATE BUNDLE** (deliverable 2a): `file_arm_fam`,
    `file_unarm_fam`, `file_cre_fam`; `file_arm_commit` (free, and it
    MINTS the permit carrying the deed), `file_unarm_commit` (free, and
    it SPENDS it), `file_acre_commit` (the parent leg: at `f` in the root
    the two-phase move — `file_app_step_park` in phase 1,
    `AppFile.file_resync` in phase 2 — and at any other name the free
    step with the deed back), `file_open_create_au` and
    `file_open_create_au_notrunc`.  Three receipt arms exactly as the
    brief asked: `⌜nm ≠ f⌝ ∗ fown r s`, `⌜s = None ∧ d = ROOTINO ∧ nm =
    f⌝ ∗ fown r (Some (i, []))`, or the taint.
  - **THE READ** (deliverable 2c): `file_read_recv`, `file_read_piece`
    (`UkTreeRead.tree_read_piece` at a FRACTION instead of a frozen pin)
    and `file_read_arms_learn` (`read_arms_tree_learn`'s twin, with the
    fraction returned on every arm — `read_post_fail`'s sign-guard arm
    gives the whole `pf_at` back and its copyout arm the fired receipt).
  - **THE O_RDONLY OPEN** (deliverable 2b, the RESOLVING half):
    `f_pin_walks` / `f_pin_resolves`, `file_pin_law_q`,
    `file_open_recv` / `file_aopen_piece`, `file_open_plain_au` and
    `file_open_recv_file`.  Three arms: `-1` with the table untouched,
    the descriptor `FdInode i γo OffParked` **on the deed's own inum**
    with BOTH fractions back, or the taint.
  - `f_pin_misses` (the ABSENT half's pin), and section 6 is the STOP
    record.

**THE CLAIM CHANGED UNDER THE LANE AND IT WAS THE RIGHT CHANGE.**  Lane
F-WRITE's relay 1 (`dst = option (Z * list (bv 8))`) was merged mid-lane.
It **closed a wall this lane had already hit**: at a content-only deed
the create's UNARM leg is unprovable — `f_ok av0 (Some bs)` and `f_ok av
(Some bs)` may name DIFFERENT inums, so `av0 !! i = None` does not give
`i ≠ f`'s inum, and deleting `i` leaves the root's `f` entry dangling
(no `f_ok` holds of the result, so the claim breaks and cannot be
stepped).  With the inum in the state `f_ok_unarm_fresh` is three lines.
`AppTree` gets the same fact from `aview_rooted`; the file claim has no
tree, and the inum is what replaces it.

**WHAT THE CONSOLE OWES, AND WHO PAYS IT.**  The unarm's OTHER side
condition is "the armed inum is not the CONSOLE's", and the deed says
nothing about the console.  Every supplier here therefore takes
`AppEcho.cons_made (fn_cons r) jc` — persistent, minted by /init's own
mknod, already carried down the process chain — and `file_cons_law`
turns it into the pin at every view.  It costs the caller nothing it does
not already hold and it also makes `cons_absent` vacuous inside every
step, which is why no supplier below needs a console credential.

**REFUTED / BLOCKED — and both are ONE sentence at two places.**

1. **THE O_TRUNC LEG OF THE CREATE BUNDLE CANNOT BE PAID FROM THE DEED,
   and it is structural.**  `SysOpenDefs.open_au_create_at` (`:549`)
   joins `open_trunc_piece Γ vom Ft` and `cre_child_unfired Γ (AFile [])
   Farm Fun` under one `∗`.  The create's parent leg MOVES the claim, and
   a move is `AppFile.file_step_park` (`:544`, joins the holder's HALF
   with the claim's to make `fdeed_whole`) plus `AppFile.file_resync`
   (`:848`, needs `ftkt r s`, the ticket's HALF) — both on the nose, so
   no proper fraction parks and the truncate piece is left with nothing
   to read the claim with.  It must read it: `f_ok av s` determines `s`
   from the view, so every case is decidable EXCEPT "`i` is the deed's
   inum and its content is non-empty", which is exactly the case that
   needs the move.
   - **Deferring the create's phase 2 to the truncate does not work**,
     and this is the part that is not obvious: in this xv6 revision
     `itrunc` runs AFTER `filealloc`/`fdalloc`, so
     `SpecSysOpen.open_post_fail_create`'s arm (a) — create fired, the
     descriptor table was full — hands the truncate piece back UNFIRED
     (`:705`).  A claim parked there is in flight for ever: a resync
     needs the map authority, i.e. a later fire, and the redirect child's
     next act is a console `fprintf` and `exit`.  That arm is exactly the
     brief's third arm (`-1` with `fown r (Some [])`), so it is not one
     to give up.
   - **THE FIX, and it is small**: key the truncate piece as the unarm is
     keyed to its arm.  `open_trunc_piece` becomes `∀ i, <permit i> -∗
     atrunc_commit_at Γ appE i Φ` with the permit the create's own `Fok`
     receipt (FRESH arm) or the `Fex`/`Fo` receipt (EXISTS arm), on
     `FsAbsCreateFire.aunarm_of_arm`'s (`:531`) mould.  Then the deed
     rides `Fok` into the truncate and the whole 0x601 bundle is one more
     instance of `FileOpen` section 3.  Kernel sites: `SysOpenDefs`
     (`open_trunc_piece`, both `_at` bundles and the four `_of_all`),
     `SpecSysOpen`'s two post folds and two receipts, and the generic
     supplier.  `SysOpenDefs`' own note at `open_trunc_piece` says the
     piece is unkeyed "because no inum exists to name at supply time" —
     true of the SUPPLY, not of the FIRE, which is why a permit and not
     an index is the shape.
2. **THE ABSENT-`f` OPEN LOSES ITS CREDENTIAL.**  `PinnedObs.pobs_hop_dead`
   (`:498`) takes `K`, reads the claim with it and answers the miss out
   of `pobs_miss_free` — `K` is dropped, and `pobs_P_dead` (`:479`) has
   no slot for it.  So cat's "cannot open" arm would burn the deed
   fraction it was paid with, and a holder that cannot reassemble
   `AppFile.fdeed` can never move the claim again.  Putting the fraction
   in `Pmiss` fixes the arm that actually fires; the `hop never fired`
   arm of `SysOpenDefs.namei_walk_dead_era` (`:456`) returns the unfired
   `ax_hop` itself, which is not a `PieceFam` and has no refund to
   eliminate to.  **NOTE THIS IS NOT THE FILE LANE'S PROBLEM ALONE**:
   /init's own first open goes through the same lemma with its EXCLUSIVE
   `cons_key` as `K` (`UInitCons.init_cons_open_bundle_absent`), so the
   same credential is being dropped there.  The fix is one of: a
   refunding dead hop (`Pmiss k d := K ∨ T`, plus a refunding
   "never fired" arm), or the walk piece becoming a `pf_at`.
3. **DELIVERABLE 3 (the U-tier corollaries) IS NOT TAKEN**, and the
   reason is 1: `wp_uk_ecall_open_create_deed` is the create bundle at
   mode 0x601, which is the bundle 1 blocks; at 0x201 it would be a
   corollary of `file_open_create_au_notrunc` with no consumer.  The
   pieces it needs are otherwise all here — `file_open_create_au`'s three
   receipt arms are already the three arms the brief lists, and
   `file_open_recv_file` is the plain open's.

**AppFile.v NEEDS NOTHING CHANGED.**  Every lemma this lane wanted was
there in the shape it wanted, `file_step_park` / `file_resync` /
`file_app_step_park` / `file_app_step_taint` / `file_pred_cons` /
`f_typed_some` / `f_ok_fcontent` included.  Two observations for the
designer, neither a change request: (i) `file_step_free`'s premise
`∀ s, f_ok av s -> f_ok av' s` is exactly as strong as the same at the
ONE `s` the view admits (`f_ok_det`), so no supplier ever needs more —
worth a line at the definition; (ii) `fdeed` is spelled at `1/2` and this
lane had to unfold it to split it (`FileOpen.fdq`), so a fractional
`fdeed_frac` beside it in `AppFile` would keep the unfolding out of the
suppliers.

**THE ONE THING LANE SH-ROUND NEEDS FIRST.**  `UkShRedir.ush_open_ans`'s
`-1` arm carries NO application payload — it is `⌜r = -1⌝ ∗ ustd … l`,
while its fd arm carries `K ty`.  The file application's open has THREE
outcomes, not two: fd 1 with `fown r (Some (i, []))`, `-1` with the deed
UNCHANGED, and `-1` with the deed at `Some (i, [])` (the create fired and
`filealloc` failed — `SpecSysOpen.open_post_fail_create` arm (a), and
the deed is genuinely moved there).  So `ush_open_ans` needs its `-1` arm
to carry an application receipt too (`Kf : iProp Σ`, or a second
`fdtype`-free payload), or sh's redirect drops the deed on a path the
kernel spec says is reachable.  Everything else SH-ROUND needs of this
lane is `FileOpen.file_open_create_au`'s conclusion, instantiated at
`K ty := ∃ i γo, ⌜ty = FdInode i γo OffParked⌝ ∗ fown r (Some (i, []))`.

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

### STAGE-2 (2026-09-17) — the conclusion IS `FileDisc.file_phi`; BLOCKER 2 superseded

Branch `app-file/stage`.  Whole tree GREEN on the lane's remote tree
(`--proofs -k`, `EXIT=0`, zero `Error`); **both audits unchanged**
(`make audit-all-only`: the echo theorem's FOURTEEN, the system theorem's
thirteen).  Three files move: `FileOutPure.v`, `FileOut.v`,
`AppFileRec.v`.  `FileDisc.v`, `AppFile.v`, `FileLinks.v` and every echo
file are untouched, and `FileOut`'s `Hdf` context hypothesis is left
verbatim for lane FILE-DEC.

**BLOCKER 2 IS SUPERSEDED.**  `AppFileRec.file_phi` is now
`fun _ h => FileDisc.file_phi h` — the antecedent, the guarded first
clause and `echof_lines_before` all included, with no change to
`AppFile.f_typed` and no index on the witness.  `FileOut.file_good` is
deleted.

**WHAT LANDED.**

`iris/FileOutPure.v` (+330).  THE PURE FACT and the conclusion's body.
- `in_pres_first` — the prefix before a cycle's first console input byte
  is itself input-free.
- `disc_f_first_out : disc_f h -> trace_shape h true ->
  obs_wire Uart0 (open_seg h) = [] -> ins (open_seg h) = []`.  D2 at that
  prefix asks for `sessf ps cs s [] = pro_of ps` on the wire, and
  `pro_ok_f`'s round bound is `pro_done ps`, so `pro_of ps` is nonempty
  (`EchoDisc.pro_of_pos`) — it cannot sit on an empty wire.
- `echof_lines_before_cut`, `echof_lines_of_cut`, and the corollary
  `efl_of_first_out`.
- `file_phi_body` (= `FileDisc.file_phi`'s body at a given `s0s`),
  `file_phi_of_body`, and its steps: `file_phi_body_nil`, `_step_io`,
  `_off`, `_on`, `_last_adm`, `_out`, `_drain`; plus `fop_snoc_inv`.

`iris/FileOut.v`.  THE LEDGER.
- `f0_pinned h s0s` — `emp` while `obs_wire Uart0 (open_seg h) = []`,
  and `∃ vf s0, ⌜∃ u1, s0s = u1 ++ [s0]⌝ ∗ file_era_pin (obs_boots h) vf
  ∗ f0_lb vf s0` once the cycle has drained; with `_undrained`, `_io`,
  `_drained`, `_drain`.
- `file_phi_res h := ∃ s0s, ⌜disc_f h -> file_phi_body h s0s⌝
  ∗ f0_pinned h s0s`, the ledger's fifth conjunct.
- `f0_lb_agree : f0_lb v s -∗ f0_lb v s' -∗ ⌜s = s'⌝` (the old
  authority-against-bound lemma is now `f0_auth_lb_agree`).
- `fdrain_ret` takes the era index and hands `file_era_pin k vf ∗
  f0_lb vf s0` beside the witness; `fecl_drain` takes
  `obs_wire Uart0 seg <> []`.
- `f0_typed_adm` is restated at an arbitrary line list.
- `file_led_tx`'s Uart0 premise gains the pin and the bound;
  `file_led_phi : file_led h -∗ ⌜file_phi h⌝`.

`iris/AppFileRec.v`.  `file_phi := fun _ h => FileDisc.file_phi h`;
`file_al_tx` proves the drain's wire premise and relays the pin at
`obs_boots h`; `file_Hphi_R` and `file_laws` rebuilt unchanged otherwise.

**THE ARGUMENT, IN ONE PARAGRAPH.**  `al_pow` parks a PROVISIONAL `None`
for the new cycle (`None` is admissible against any line set, and an
empty cycle is `good_out_f` at any state).  At a Uart0 output the drain
hands the era's boot state `s0`, its deed witness, the era pin and
`f0_lb vf s0`.  If the cycle's wire was still empty this is the era's
FIRST drain: under the discipline the cycle has no input either
(`disc_f_first_out`), so the ledger's line list IS the list of lines
typed in strictly earlier cycles (`efl_of_first_out`), and
`f0_typed_adm` read there is exactly `file_phi`'s third clause — at cycle
0 that list is empty and the same reading refutes `f0_typed`'s `Some`
arm, which is the guarded FIRST clause.  The provisional entry is
replaced by `s0` and `f0_pinned` records it.  If the cycle HAS drained,
the handed pin and bound are checked against the kept ones
(`file_era_pin_agree`, then `f0_lb_agree`), so the entry does not move
and the body extends by the drain's own `good_out_f`.

**WHAT THE DESIGN SAID THAT THE PROOFS CORRECTED.**

- **THE OPEN CYCLE'S INDEX IS `pred (length (cycles_of h))`, NOT
  `obs_boots h`.**  §4.3a (and the lane brief) spell the first drain's
  reading as `efl_of h = echof_lines_before h (obs_boots h)` with
  `S k = obs_boots h` at the open cycle.  That is off by one and the
  spelling it names is VACUOUS: the per-era maps (`pin_map`, `f0_map`,
  `file_era_pin`) are keyed 1-BASED (`pin_dom M n` is `{1..n}`;
  `f0_map_on` inserts at `S (obs_boots h)`) while `s0s` is indexed by the
  CYCLE, 0-based, so cycle index = era index - 1 — and
  `echof_lines_before h (obs_boots h)` is `echof_lines_of h` outright by
  `FileDisc.echof_lines_before_all`.  What `file_phi`'s third clause
  wants at the open cycle is `echof_lines_before h (pred (length
  (cycles_of h)))`.  `efl_of_first_out` is therefore indexed by the CYCLE
  COUNT (`S n = length (cycles_of h)`), which also keeps the whole lane
  free of a `length (cycles_of h) = obs_boots h` bridge — a bridge that
  is FALSE without a `trace_shape` premise, since `cyc_step` opens a
  cycle for an io event at the empty cycle list
  (`length (cycles_of [ObsUartOut Uart0 b]) = 1`, `obs_boots` of it `0`).
- **THE CARRIER MUST NAME ITS LAST ENTRY WITHOUT THE ANTECEDENT.**
  `f0_pinned` names the era's fixed state, but `length s0s = length
  (cycles_of h)` lives INSIDE `disc_f h -> …`, so nothing says `s0s` is
  nonempty when the discipline fails.  Rather than add an unconditional
  length conjunct beside the implication, the tx step sets
  `s0s' := removelast s0s ++ [s0]`: its last entry is `s0` whatever `s0s`
  was (`EchoOutPure.epu_removelast_snoc`), and the discipline is spent
  only on showing `s0s` was a snoc in the first place.  So the carrier is
  the brief's, with no extra conjunct.
- **`f0_pinned` SPELLS THE LAST ENTRY AS A SNOC, NOT WITH `last`.**
  `FileOut.v` requires `Stdlib.List`, whose `last` (with a default) wins
  over stdpp's `option`-valued one, so `⌜last s0s = Some s0⌝` does not
  typecheck there at all.  `⌜∃ u1, s0s = u1 ++ [s0]⌝` is what both
  consumers want anyway.
- **THE DRAIN CANNOT ALWAYS MINT THE BOUND, AND THE SIDE CONDITION IS THE
  WIRE.**  `fecl_drain`'s state is `f0_st (fo_f0 so)`; at an UNFILED
  stage the authority is `●ML []` and no `◯ML [s]` comes out of it.  It
  is not a gap: `feout_pure`'s `o_f0` IFF says an unfiled stage has empty
  `E` and `w`, so `ch_acc` is `D_f … [] ++ []` = `[]` and the wire is
  empty.  So `fecl_drain` takes `obs_wire Uart0 seg <> []`, which its one
  caller (`file_al_tx`, at `open_seg h ++ [ObsUartOut Uart0 b]`) proves
  by inspection, and nothing is filed on the drain path.
- **TWO LOWER BOUNDS AGREE WITH NO AUTHORITY IN HAND.**  The ledger never
  holds `f0_auth` (the stage does), so the era-agreement step cannot go
  through `f0_auth_lb_agree`.  `mono_list_lb_op_valid_1_L` makes two
  `◯ML` comparable, and a list that never grows past one entry makes two
  one-element bounds equal — `f0_lb_agree`, four lines.
- **NOTHING IN `AppFile.v` HAD TO MOVE.**  STAGE priced fix (a): an index
  (`mono_list_idx_own` at `j`) on `AppFile.f_typed` plus a `fe_n` field on
  `file_era`, to record WHEN the witness's bound was taken.  It is not
  needed.  The moment is pinned by the WIRE, not by an index:
  `obs_wire Uart0 (open_seg h) = []` is a pure fact the ledger already
  has about the history it already has, and it holds exactly until the
  era's first drain — which is the only moment at which the ledger has to
  read the bound.

**ASSUMPTIONS.**  `Print Assumptions` is *Closed under the global
context* on `FileOutPure.disc_f_first_out`, `efl_of_first_out`,
`file_phi_body_drain`, and on `FileOut.fecl_drain`, `file_led_pow`,
`file_led_rx`, `file_led_tx`, `file_led_phi` (no axioms at all, not even
PrimString — STAGE reported the eleven primitives for the `file_led_*`
family, which the conclusion's move to `file_phi` retires); on
`AppFileRec.file_Hphi_R` it is the eleven PrimString/PrimInt63 primitives
and nothing else.  NOTHING is `Admitted`, and the two section hypotheses
are unchanged (`al_programs`, `Decision (disc_f h)`).

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

### OFF-HAND-3 (kernel/U tier, 2026-09-17) — THE CARRIER IS A BIT ON THE RECORD, NOT A GHOST; D4 CLOSES; R2/R3/R4 REDUCE TO ONE COUPLED CHANGE, NAMED

**The lane's verdict in one line: R1's carrier landed in the shape OFF-HAND-2
asked for — inside `UkRun.urun`, readable where `UkSh.ush_gen_slot` is spent,
a FACT about the whole table and not a disjunction with the taint — but it is
a STATIC BIT ON `uk_names`, and the ghost counter the two previous lanes
proposed is REFUTED three ways.  With it, **D4's other half — the narrowing
OFF-HAND-2 attempted and reverted at `UShKernel.v:655` — LANDED**, and R2, R3
and R4 now sit behind exactly one further change, which this lane traced end
to end and prices below.  Everything is checked at the statement in the tree.**

**WHAT LANDED** (whole tree green on the lane's remote tree, `make -f
CoqMakefile -j32 -k`, `EXIT=0`, zero `Error`, `make -n` reports nothing left;
`make audit-all-only`: echo audit fourteen, system audit thirteen; every new
result `Proof using`).  Three commits, each green on its own.

*(1) `97fa5150e` — the run carries whether the process answers for its offsets*

- `UkRun.uk_names` gains `ukn_park : bool`, with the class `ukn_parked`
  (`ukn_triv`/`ukn_const`'s mould).
- `UkRun.urun_parked_row N fdv := ukn_park N = true -> fdv_all_parked fdv`,
  and `urun_rows N fdv := urun_nopipe fdv ∗ ⌜urun_parked_row N fdv⌝` — the two
  table rows in ONE conjunct.  **That bundling is what made the change
  affordable**: 103 leaves destructure `urun` positionally and hand the
  conjunct straight back to `urun_close`, and not one of those sites moved.
- `urun_rows_parked` is the reading a narrowed taint arm spends;
  `urun_rows_nopipe` the projection for rows still stated at the pipe half.
- `urun_rows_step` is the round's effect, and **`UsysMemOk.usys_fd_ok_parked`
  has its first consumer** — OFF-HAND-2 predicted exactly this.  It holds at
  EVERY number, so every quiet leaf is free; `urun_rows_insert` / `_dup` /
  `_copy` serve open, close, dup and pipe, each free from a fact the
  descriptor row already carries (open's `fdst_parked` conjunct was being
  destructed as `_` at `UkRunSys.v:945/3955/4824`).
- `uslot_of_urun` / `_all` / `_ro` take the bit as an argument `pk` with the
  premise that makes it honest, and hand the program `⌜ukn_park N = pk⌝`
  beside `⌜ukn_pay N = Q⌝`.  `UkFork`'s child record is minted at the PARENT's
  bit (the child's table IS the parent's, so the two rows are one
  proposition).  `UkRun.udepw_at` / `udepw_at_ref` lend the PAIR.

*(2) `7d08f1659` — the exec crossing's all-parked row reaches the entry*

- `ExecEntry.image_entry_at` / `image_entry` gain `⌜fdv_all_parked (uvis_fd
  W')⌝`.  **The row was already on `SpecKexec.exec_slot_pre`'s wands (lane
  OFF-HAND-2) and every producer DROPPED it** — `ExecBundle.
  exec_slot_of_entry_at` and `ExecRun`'s abstract twin both intro'd it as
  `%Hpk` and threw it away.  `PinnedExec`'s four bundles spell it out inline.
- Every verified entry constructor passes `pk := true` now
  (`USyncKernel.sync_uexec_slot`, `UEchoKernel.echo_uexec_slot`,
  `UEchoOut.echo_uexec_slot_at`, `UInitKernel.init_uexec_slot` /
  `init_slot_of_kexec` / `init_boot_con`, `UShKernel.sh_uexec_slot` /
  `sh_slot_of_kexec`), each with `fdv_all_parked` as a new pure premise
  discharged by the caller off the relay, or at the boot by
  `FdSlots.fdv_all_parked_closed` at `fdt0`.
- `UexecCond.cond_entry_slot` and the two gate lemmas take it, and
  **`UexecExecMint.uslot_mint`'s all-parked premise — landed by OFF-HAND-2
  and until now dropped (`iIntros "!>" (W) "_ #Hpay"`) — is spent.**

*(3) `ec00a5833` — D4's other half: the taint arm carries the row*

- `ExecEntry.image_entry_taint` gains `⌜fdv_all_parked (uvis_fd W')⌝`, and so
  do the inline taint spellings on `PinnedExec.pex_slot` / `pex_slot_at` /
  `pinned_exec_bundle` / `_at` / `_boot`.  The two consumers pay it from the
  `%Hpk` they were already introducing.
- `UkRun.urun_gen` is narrowed to all-parked keys and takes `ukn_park N =
  true`, paid off `urun_rows`'s row.
- `UkSh.ush_gen_slot` carries BOTH the narrowed family and the record's park
  bit, **as a pure conjunct of the slot itself** — that placement is what the
  change turns on.  A section hypothesis would have to be named in the
  `Proof using` of every lemma on sh's walk between the entry and the taint
  (measured: the first build round produced one such error per lemma and the
  call graph is the whole file), while the slot is already threaded to exactly
  those lemmas and is already persistent.  `UShKernel.sh_uexec_slot` supplies
  the bit from the equation the entry constructor hands over.
- `UInitBoot`'s boot taint arm DROPS the row: the generic family it is
  inhabited from (`UexecExecMint.uslot_mint_all`) is not narrowed yet.

**STATEMENTS THAT CHANGED SHAPE** (exhaustive): `UkRun.uk_names` (hence
`MkUkNames`'s arity), `urun`, `urun_close`, `urun_close_upd`, `udep_exit_run`,
`udepw_at`, `udepw_at_ref`, `udepw_at_mint`, `urun_gen`,
`uslot_of_urun`/`_all`/`_ro`; `ExecRun.uexec_sup_run` / `_ids` / the abstract
twin; `UkRunExecRef`'s two supply shapes; `TreeExec`'s entry wand;
`ExecEntry.image_entry_at` / `image_entry` / `image_entry_taint`;
`PinnedExec.pex_slot` / `pex_slot_at` / `pinned_exec_bundle` / `_at` /
`_boot`; `UexecCond.cond_entry_slot` / `sync_gate_slot` / `echo_gate_slot`;
`USyncKernel.sync_uexec_slot`; `UEchoKernel.echo_uexec_slot`;
`UEchoOut.echo_uexec_slot_at`; `UShEcho.echo_slot_of_kexec`;
`UShEchoPay.echo_slot_of_kexec_at`; `UInitKernel.init_uexec_slot` /
`init_slot_of_kexec` / `init_boot_con`; `UShKernel.sh_uexec_slot` /
`sh_slot_of_kexec` / its two local taint-arm premises; `UkSh.ush_gen_slot`.
**No leaf statement in `UkRunSys`, `UkFork`, `UkRunMem`, `UkRunBr`,
`UkRunLeaf` moved, and no program-walk statement in `UkSh`, `UkInit`,
`UkEcho`, `UkCat`, `UkSync` moved.**

**REFUTED / BLOCKED, with the evidence.**

1. **THE HELD-ROW COUNTER AS A GHOST IS REFUTED, AND SO IS EVERY
   RESOURCE-SHAPED CARRIER.**  The consumer the brief names —
   `UkSh.ush_gen_run` and `/init`'s twin — spends the generic slot INSIDE
   `UkRun.urun`'s existential holding nothing but the run, so whatever carries
   all-parkedness must be free at every site between a program's entry and
   that spend.  Three shapes, three failures:
   - an EXCLUSIVE ghost half (the brief's `uheld N n`) appears in every
     statement between the entry and the exec — sh's walk alone is ~40 lemmas
     across nine files — and no landed U-tier statement can carry it without
     moving;
   - a PERSISTENT certificate is free to thread and CANNOT BE REVOKED, which
     is exactly what R4's hand-open needs.  There is no camera in which a
     freely duplicable witness survives an update that contradicts it;
   - a one-shot `csum (excl ()) (agree ())` gives both, but the "still parked"
     half is the EXCLUSIVE one, so it is the first case again.
   A STATIC FIELD ON THE RECORD is the only shape that is at once free to
   thread (it is pure), revocable (a program that means to hand-open is minted
   at `false`) and not an escape hatch (no taint disjunct — OFF-HAND-2's own
   constraint).  `uk_names` already carries two such classes, so this is the
   file's idiom, not a new mechanism.
2. **A COUNT CANNOT PAY THE SURRENDER ROUTE, AND NOTHING IN THE CAMPAIGN
   RECORDS THIS.**  R1's second half — "a verified program with held rows
   SURRENDERS them before an exec or a fork, and its counter says its handles
   are all the held rows there are" — is not statable at a `nat`.  What the
   crossing takes is `FdPark.uoff_surr_at sts`, whose right disjunct
   `uoff_surrs sts` (`FdPark.v:174`) is a BIG-OP OVER THE TABLE, one
   `∃ o, uoff γo o` per held row.  Producing it from "I hold k halves and the
   count is k" needs to know WHICH rows are held; the count does not say, and
   no lemma recovers it.  So the surrender needs the SET-valued carrier §8.4
   originally priced, or a program must CLOSE its held descriptors before it
   forks or execs.  **This is the one thing on the file lane's critical path
   this lane could not settle** — see "the one thing" below.
3. **R2 (D1) IS BLOCKED ON ONE COUPLED CHANGE, AND IT IS NOT WHERE THE
   PREVIOUS TWO LANES LOOKED.**  The premise `⌜fdst_parked st⌝` that
   `FileInvDefs.fdstate_ok`'s relaxation needs has ONE attachment point: the
   two generic builders `FsAbsInvFire.fsabs_fileread_in` (`:304`) /
   `fsabs_filewrite_in` (`:354`), which are built inside
   `UexecExecInst.xv6_sbundle_of_supply_ne` (`:958`) / `xv6_sbundle_of_supply`
   (`:1020`) — the FIELDS `UexecSG.sbundle_of_supply_ne` (`:468`) /
   `sbundle_of_supply` (`:499`).  This lane traced every consumer of the
   fields:
   - `UexecExecMint.udep_gen` (`:99/:104/:107/:112`), which proves
     `UkRun.udep`'s pure minting law at EVERY key.  **This is nearly free if
     the new premise is GUARDED BY THE NUMBER** — `(n = USYS_read \/ n =
     USYS_write -> fdv_all_parked (uvis_fd W))` — because those are the only
     two rows of `xv6_sbundle` that build a fire contract, and every spend of
     the law (`UkRun.udep_dep`, `udep_close_dep`, `udep_exit_dep`,
     `udepw_of_psok`) is at a CONCRETE number or under `psok n`, which at
     `uprogSG_free` is `free_num n` and excludes 5 and 16 by computation.
     **Without the guard the premise reaches all ~50 leaves of `UkRunSys` and
     every program's call sites**, so the unguarded form must not be taken.
   - `UkRun.udepw_law_of_psok` at 16, spent by `UexecExecMint.uslot_mint`
     (`:411`): `udepw_law n` quantifies `N m pc` and `udepw` quantifies the
     key, so the narrowed law is at ALL keys and `uslot_mint`'s single-key
     premise does not pay it.  A second definition (`udepw_law_parked`) is
     what echo's write deposit becomes, and echo's own leaves pay it from
     `urun_rows_parked` — echo's record is at `ukn_park = true` as of this
     lane, so this is now possible and was not before.
   - `UexecRet.uexec_wp_uslot` (`:2569`, `:2607`, inside `uslot_of_creds`
     `:2748`) — the GENERIC slot's Löb, minting at `usys_num (uvis_tf W)`, a
     symbolic number.  **This is the work left, and it is COUPLED to the
     field**: narrowing `uslot_of_creds` narrows the Löb hypothesis, and that
     hypothesis is exactly the `X`-family `uexec_dep_F_of_supply` (`:2565`,
     `:2604`) hands to `sbundle_of_supply`, so the field's own `X` argument
     narrows with it — which in turn makes `xv6_sbundle`'s EXEC row owe
     all-parkedness at the exec'd key, payable off `SpecKexec.exec_slot_pre`'s
     wands.  The rest of the Löb is mechanical: the trap-out key inherits the
     row through `user_trap_frame_trapped`'s `Hfdw`, the fork arm through
     `⌜fdv' = uvis_fd W⌝` (`uexec_fork_parent_F`), and every other arm through
     `usys_fd_ok_parked` on `uexec_ret_cont_gen`'s SECOND pure row, which
     `uexec_arm_of_all` (`:2637`) already introduces as `_`.
   **That conjunct must therefore STAY in `usys_fd_ok`'s open arm** until the
   Löb is re-plumbed — i.e. **R4's "free the mode in the open arm" must come
   AFTER this, not before**, which inverts the brief's R4 ordering.
4. **R3 IS BLOCKED BY R2 AND BY NOTHING ELSE, AND THE REASON IS ONE
   `destruct`.**  `FsAbsInvFire.fsabs_fileread_in` already destructs its
   descriptor type as `[i γo om | γp | ma]` — it is GENERIC IN THE MODE today
   — and hands the inode arm's content over at any `om`.  The moment
   `SpecFileread.fileread_in`'s inode arm asks for `FdPark.uoff_rcpt st off0`,
   that supplier owes a `UserOff.uoff` at `om = OffHeld` and has none.  So
   OFF-HAND's "cheap half" is cheap only AFTER R2.  Everything else about R3
   was re-checked and stands: `filewrite_in`'s inode arm
   (`SpecFilewrite.v:789`) matches `FdInode i γo _` with the mode IGNORED, so
   the split's PARKED branch is byte-for-byte today's and every `_in_inode` /
   `_extra_inode` reader keeps its statement; the two fire sites are
   `ProofFileread.v:2253/:2263` and `ProofFilewrite.v:4935/:4947` and both
   become `FdPark.off_supply_of_st_at_eq`, which OFF-HAND landed for exactly
   this.
5. **R4 SITS BEHIND R2 AND R3** and, per finding 3, its `usys_fd_ok` half must
   come LAST.  `ProofSyscall`'s exec arm can be re-routed the day
   `proc_priv_parked` goes, but its replacement payer
   (`FdPark.uoff_surr_at` through `fd_frags_park_at`) is blocked on finding
   2's set-valued carrier and not on the tier — OFF-HAND-2's finding 3 stands.

**THE ONE THING LANES ECHO-FILE AND CAT-ENTRY NEED FIRST: a ruling on finding
2, because it decides whether the REDIR child may exec at all while it holds
f.**  design/app-file.md §3 has the child `open(f,…)` at a HELD offset, write
four times, and then `exec /echo` carrying the held row into echo's entry.
With the carrier this lane landed, a record that answers for its offsets
(`ukn_park = true`) may not hold a held row at all, and a record at `false`
cannot pay the exec crossing's all-parked wand — so **as designed, the child
cannot reach echo's entry.**  The two ways out, both the designer's:
 (a) the child CLOSES f before the exec and `UEchoFile` re-opens on its own —
     then §3's "exec /echo carries the deed, the held offset and the fd-1 row
     into echo's entry" is wrong and §5.2 changes; or
 (b) the carrier grows from a bit to the SET of held rows (`uoff_surrs`'s own
     index), which is the only thing that makes `FdPark.fd_frags_park_at`'s
     right disjunct payable from the U tier, and hence the only thing that
     lets a held row cross a boundary at all.
Until one is taken, `UEchoFile`'s WRITE post can be planned against finding 4
(the arm split is a mechanical consequence of R2) but its EXEC step cannot,
and `UCatKernel`'s open-at-a-held-offset hits the same wall one syscall over.

### F-OPEN-2 (2026-09-17) — THE DEAD WALK REFUNDS, THE U-TIER COROLLARIES LAND, AND O_TRUNC NEEDS THREE SEAMS AND NOT ONE

**The lane's verdict in one line: seam 2 was smaller than F-OPEN priced
(one fix, not two — put `K` on the CURSOR and `namei_walk_dead_era` does
not move at all) and seam 1 is BIGGER than the ruling priced (keying the
truncate piece is necessary and NOT sufficient: the create surface has
TWO arms and the caller hands in ONE piece, so the permit is a
disjunction and the application owes both disjuncts — which costs two
further kernel-tier restatements, both named below).**

**WHAT LANDED** (whole tree green on the lane's remote tree; every new
lemma `Proof using`; `make audit-all-only` unchanged — echo audit
fourteen, system audit thirteen, tree audit unchanged).

- **SEAM 2, IN FULL** (`iris/PinnedObs.v` section 8a, `iris/PinnedOpen.v`
  section 3a, `iris/UInitCons.v`, `iris/FileOpen.v`).
  - `PinnedObs.pobs_P_dead_lin T K d0` / `pobs_Pmiss_ref T K` /
    `pobs_miss_hold`, and section 8's three lemmas at them:
    `pobs_hop_dead_lin` / `pobs_hop_dead_hi_lin` / `pobs_walk_dead_lin`.
    **`SysOpenDefs.namei_walk_dead_era` DID NOT HAVE TO CHANGE**, and that
    is the lane's first finding: F-OPEN read the two arms as needing
    separate fixes (a refunding `Pmiss`, plus a refund on the "hop never
    fired" arm, which "is not a `PieceFam` and has no refund to eliminate
    to").  Put `K` on the CURSOR — section 11a's construction one list
    shorter — and BOTH arms refund out of the definition as it stands:
    the never-fired arm hands back `P k d`, the fired-and-missed arm hands
    back `Pmiss k d`, and at this family both carry `K`.  The walk piece
    did not have to become a `pf_at` either.
  - `pobs_dead_cursor_refund` / `pobs_dead_miss_refund` /
    `pobs_dead_start_refund` read the credential off each of the three
    places the failure fold can return it (the third is the argstr arm,
    where the cursor sits behind the walk one-shot — one `={⊤}=>`).
  - `PinnedOpen.pinned_open_bundle_dead_lin` / `pinned_open_dead_lin`.
  - `UInitCons.init_cons_open_bundle_absent` / `_recv_absent` /
    `init_cons_laws_open_absent` re-instantiated at it: **/init's
    EXCLUSIVE `cons_key` now survives its own first open**, which it did
    not before.  Their statements gained the refund and nothing else.
  - `FileOpen.file_open_miss_au` / `file_open_miss_recv` close F-OPEN's
    STOP item (b): cat's absent-`f` open is a bundle from a deed FRACTION
    and the fraction comes home.
- **DELIVERABLE 3, IN FULL except the create corollary** (`iris/UkFileOpen.v`,
  new): `wp_uk_ecall_open_read_deed` (O_RDONLY at a present deed — the
  descriptor is on the deed's OWN inum and both fractions come home),
  `wp_uk_ecall_open_miss_deed` (the same call at an absent deed — `-1`,
  the ledger untouched, the fraction back) and `wp_uk_read_deed_learns`
  (the bytes in the buffer ARE the deed's).  All three are `UkTreeRead`'s
  mould at `AppFile`'s deed and spend nothing but a landed U-tier leaf
  plus one `FileOpen` bundle and one receipt reader.  **The leaf is a
  visible parameter**: all three are stated over the PARKED-offset members
  (`UkRunSys.wp_uk_ecall_open_recv_img`, `UkReadFile.wp_uk_ecall_read_file`),
  so lane OFF-HAND-3's held-offset twins re-instantiate each by swapping
  exactly one application.
- **THE SH SEAM** (`iris/UkShRedirAns.v`, new): `ush_open_ans2` /
  `ush_open_call2` — `UkShRedir`'s pair with a `-1` payload `Kf`, plus
  `ush_open_ans2_mono` and `ush_open_ans2_drop` (at `Kf := emp` the two
  are the same proposition, so the merge lane loses nothing).  A NEW FILE
  and not a definition beside the landed pair, per the brief's own
  fallback: `iris/UkShRedir.v` lives on branch `app-file/sh-redir`, which
  lane SH-PARSE-2 had checked out and DIRTY (untracked `UkShRedirEx.v`, a
  commit eighteen minutes old) while this lane ran.
- **SEAM 1's SHAPE AND ITS APPLICATION HALF** (`iris/SysOpenDefs.v`
  section 2b'', `iris/FileOpen.v` section 3f).  `atrunc_commit_i` (the
  trunc commit at ONE inum), `atrunc_of_permit` (the keyed family, on
  `aunarm_of_arm`'s mould), the two bridges `atrunc_commit_i_of_at` /
  `atrunc_commit_at_of_i`, the generic supplier's one line
  `atrunc_of_permit_of_all` (the permit unread), `atrunc_of_permit_unit`,
  and `trunc_permit_cre` — the create's own fired receipt, read as a
  permit.  On the application side `FileOpen.file_trunc_free`,
  `file_trunc_of_cre` and `file_trunc_piece`: **the deed rides the
  create's receipt into the truncate's fire, at BOTH deed values, and the
  truncate is FREE there.**  All of it is ADDITIVE — no landed statement
  moved for it.

**STATEMENTS THAT CHANGED SHAPE** (three, all named in the brief or
forced by it):
1. `UInitCons.init_cons_open_bundle_absent` / `init_cons_open_recv_absent`
   / `init_cons_laws_open_absent` — the refunding cursor
   (`pobs_P_dead_lin` for `pobs_P_dead`, the two miss obligations for
   `pobs_miss_free`, and a `∗ K` plus one `={⊤}=>` on the receipt).  No
   consumer outside `UInitCons` reads them.
2. `FileOpen.file_cre_recv` / `file_cre_fam` gain the console gname `jc`
   and their `nm ≠ f` arm gains `⌜fclaim_facts jc s av⌝` — the three
   facts the leg already read, needed downstream by `file_trunc_of_cre`
   to identify the truncated row.  `file_open_create_au` /
   `_notrunc` carry the extra index and are otherwise verbatim.
3. Nothing else.  `SysOpenDefs.open_trunc_piece` is UNCHANGED, and that
   is the STOP below.

**REFUTED / BLOCKED — seam 1's bundle, and it corrects the ruling.**
The ruling was: key the truncate piece to the open's own receipt (`Fok`
on the FRESH arm, `Fex`/`Fo` on the EXISTS arm) and the 0x601 bundle
falls out.  The FRESH half is exactly right and is landed
(`file_trunc_of_cre`).  The EXISTS half does not work, for three reasons
in order, and the third is the one that stops the lane:

1. **THE EXISTS ARM'S PERMIT MUST TIE ITS INUM TO THE CLAIM, and neither
   `Fex`'s nor `Fo`'s receipt can.**  A truncate at an inum this claim
   cannot identify is UNSTEPPABLE, not merely unprovable: the row might
   be one of the four era-0 binaries and `delta_trunc` there destroys
   `FileFsPure.file_fs_pure`.  The FRESH arm is safe precisely because
   `cre_pre` hands the row over — `AFile []` at nlink 1, hence none of the
   four BY LENGTH (`FileDeltas.f_inum_not_pinned` at length 0) and `f`'s
   own inum only if `f` was already empty.  `dlookup_commit_at` quantifies
   `d` and `nm` INSIDE, so "the found node is `f`'s" is exactly what its
   receipt cannot say.  **The fix is TL-3K's shape one piece over**: the
   permit carries the walk's terminal identification as the same GUARDED
   PURE facts `SysMknodDefs.npar_cur` already carries (`∀ pl,
   ⌜arg_path_of M pv pl⌝ -∗ ⌜last (path_elems pl) = Some nm⌝`, and the
   parent's), which the kernel HOLDS at the fire — both arms state them —
   and which an application knowing its own path reads off in one line.
2. **AND THE DEED ARITHMETIC NEEDS THE ARM PIECE'S REFUND.**  With the
   tie, the EXISTS move `Some (i, bs) → Some (i, [])` needs the deed's
   WHOLE half (`file_step_park` joins it with the claim's) while
   identifying `i` needs a POSITIVE FRACTION inside `Fex`'s receipt — two
   places, one half.  The split that works is `q1` into `Farm` and `q2`
   into `Fex` with `q1 + q2 = 1/2`, **because on the EXISTS run the ARM
   NEVER FIRES**: its piece comes back and `FileOpen.fdq_join` puts the
   half together at the truncate.  So the exists disjunct of the permit
   is `Fex`'s receipt BESIDE `Farm`'s refund, and
   `SpecSysOpen.open_post_ok_create`'s EXISTS arm must give up
   `cre_child_unfired`'s arm half under `om_trunc`.
3. **AND AT AN ABSENT DEED THE SPLIT IS IMPOSSIBLE.**  At `s = None` the
   create's own parent leg MOVES the claim, so the whole half must sit in
   `Farm` and `Fex` gets nothing — and the exists disjunct, a run
   `s = None` makes UNREACHABLE but which the SUPPLY must still cover, has
   no fraction left to refute itself with.  (Refuting it is all `s = None`
   needs: `f_ok av None` says the root has no `f`, contradicting `Fex`'s
   `ents !! nm = Some i` at the tie — but only at a view the application
   can READ, i.e. only holding a fraction.)  **The fix is
   `cre_arm_fired`'s own trick once more**: create's `dirlookup` either
   FINDS the name (and `Fex` fires) or does not (and the ARM fires), so
   the two are EXCLUSIVE on every run, and `acre_commit_at_gen` can take
   the unfired `Fex` piece beside the arm's receipt — at which point the
   parent leg reassembles `q1 + q2` and the split costs nothing.

So `open_trunc_piece` was left at its landed shape: changing it without
(1)–(3) would buy the file lane nothing and would cost the whole sys_open
chain an arity sweep (~190 mention sites across `SysOpenDefs`,
`SpecSysOpen`, eight `ProofSysOpen*` files and ten consumers) for a piece
no application could then supply.  The three restatements are the lane
after this one, and they are all one shape: **a piece's permit carries
what the FIRE knows and the SUPPLY could not name** — TL-3K's cursor at
the create commit, this at the truncate, and §7.9(8)'s two at unlink.

**TWO SMALLER FINDINGS FOR THE DESIGNER.**
- `PinnedObs` section 8's `pobs_hop_dead` takes `K` as a resource and
  drops it; section 8a's twin takes NOTHING linear (the cursor carries
  it) and is strictly more useful.  Section 8 now has no consumer that
  section 8a would not serve better; a later sweep should delete it
  rather than keep two.
- `UkTreeRead.tree_open_fd_tie` is claim-free (it is pure ledger
  arithmetic) and `UkFileOpen` reuses it across applications; it wants to
  move down beside `UConsOpen`'s arithmetic, which is where its twins
  already live.

**THE ONE THING LANE SH-ROUND NEEDS FIRST** is unchanged from F-OPEN and
is now LANDED as vocabulary: `UkShRedirAns.ush_open_call2` /
`ush_open_ans2`, the redirect stub's shape with a `-1` payload.  Instantiate
`K ty := ∃ i γo, ⌜ty = FdInode i γo OffParked⌝ ∗ fown r (Some (i, []))`
and `Kf := fown r s ∨ ∃ i, fown r (Some (i, []))` — the second disjunct is
`SpecSysOpen.open_post_fail_create`'s arm (a), where the create fired and
`filealloc` failed past it, and it is why the `-1` arm cannot be
payload-free.  What SH-ROUND must NOT assume is a 0x601 bundle: until
seam 1's three restatements land, `FileOpen.file_open_create_au` takes the
truncate piece as a PREMISE, so the redirect child's open is suppliable
only at `om_trunc = false` (`file_open_create_au_notrunc`).

### ADEQUACY (2026-09-17) — THE TOP-LEVEL THEOREM IS A THEOREM; NO WALL, ONE PREMISE

Branch `app-file/adequacy`, commit `cd2625d57`.  Whole tree GREEN on the
lane's remote tree (`run-on-gcp --proofs -k`, `EXIT=0`, zero `Error`; only
the one new file compiled).  `make audit-file-only` runs and prints
EXACTLY FOURTEEN — the echo theorem's fourteen, item for item.  `make
audit-all-only` UNCHANGED (echo fourteen, system thirteen).  Nothing is
`Admitted`, there is no new `Axiom`, and every `Qed` carries `Proof
using`.  TWO new files and two edited: `iris/UFileBootAdequacy.v`,
`iris/FileAssumptions.v`, two rows of `iris/_CoqProject`, and the
`audit-file`/`audit-file-only` rules in the `Makefile`.  No landed
statement moves; `AppFileRec.v` is untouched.

**NO WALL.**  Every premise of `App.xv6_app_adequacy` composes at
`AppFileRec.app_file` as landed: the eleven laws are
`AppFileRec.file_laws` (ten discharged, `al_programs` its section
hypothesis), era 0's claim is `AppFileRec.file_Happ_init` at the literal
mkfs image, and `Hphi` is `RiscvAdequacy.obs_ledger_at_phi` at
`AppFileRec.file_Hphi_R`.  Nothing about the crash-slot transport
(`file_xfer_boot`), the kill/taint laws or the UART ledger steps needed
restating.  `user-tree.md` §8.2's three walls do not recur here, because
STAGE/STAGE-2/FILE-DEC had already paid what they were about.

**WHICH MOULD, AND WHY.**  `UInitBootAdequacy.v` (ECHO), not
`UTreeAdequacy.v`.  The two files are the same statement one application
over, but the tree twin's `app_phi` is `True`, its `Hphi` is `Logic.I`
and its closed corollary keeps only the reducibility conjunct.  The file
application has a real trace predicate read off its own ledger, so the
echo shape is the one that fits: BOTH conjuncts survive into the
corollary.  What is taken from the tree twin is only its treatment of a
law that is not proved yet.

**WHAT LANDED, with file:lemma.**

- `iris/UFileBootAdequacy.v:121  file_prog_law` — `App.al_programs` at
  `app_file`, NAMED, verbatim from `AppFileRec`'s own
  `Context (Hprog : …)`, so the instance below is that hypothesis applied
  and not a restatement of it.  Naming it is what makes the premise
  readable in the corollary's binder list.
- `iris/UFileBootAdequacy.v:143  file_laws_at` — `#[local] Instance … | 0
  := @AppFileRec.file_laws Σ _ _ _ _ _ _ _ Hprog`.  The priority is
  load-bearing: `AppFileRec.file_laws` is itself a `Global Instance` whose
  trailing `Hprog` argument is NOT a class, so resolution must never reach
  it.
- `iris/UFileBootAdequacy.v:154  file_adequacy_at_img` — the Σ-generic
  theorem at the image's facts, `echo_adequacy_modulo_phi`'s shape: the
  laws arrive as the instance, era 0's claim is the one argument and
  `Hphi` goes in as a HOLE (`UInitBootAdequacy`'s measured rule -- handing
  `xv6_app_adequacy` its obligations at once makes the elaborator unify
  each against a record field whose type it is still solving).
- `iris/UFileBootAdequacy.v:228  fileLineΣ` / `:234  fileΣ` — the concrete
  functor list: `xv6Σ ; bioslotΣ ; echoOutΣ ; fileLineΣ ; fileAppΣ ;
  fileOutΣ`.  `fileLineΣ` is `UInitBootAdequacy.echoLineΣ` spelled again
  rather than imported, because importing it would put the whole echo
  program tier into this file's build cone for one line.
- `iris/UFileBootAdequacy.v:243  file_adequacy_fileΣ` — THE AUDIT TARGET.
- `iris/FileAssumptions.v` + `make audit-file` / `audit-file-only` —
  `EchoAssumptions.v`'s mould.  `audit-all-only` IS LEFT ALONE: the tree
  rule was never added to it either (it is still `audit-only
  audit-echo-only` under `-j2`), so a fourth entry there would be a change
  of policy, not a lane's business.

**THE TOP-LEVEL STATEMENT, VERBATIM.**

```coq
Corollary file_adequacy_fileΣ
    (Hprog : file_prog_law (Σ := fileΣ))
    (g : gstate)
    (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  forall (n : nat) (κs : list mobs) t2 g2,
    language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
      κs (t2, g2) ->
    (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
    /\ FileDisc.file_phi κs.
```

The trace predicate is `FileDisc.file_phi` VERBATIM (`iris/FileDisc.v`,
the `file_phi` STAGE-2 landed): IF the console input kept the FILE
discipline (`disc_f κs`), THEN there is one boot state per power cycle
such that the FIRST cycle boots with no `f`, every later cycle boots at a
chunk subsequence of an `echo … > f` line typed in a STRICTLY EARLIER
cycle (`fadm_boot (echof_lines_before κs (S k))`), and each cycle's
console output is a prefix of the transcript its input calls for from
that state (`good_out_f`).  It is the `echo_phi` twin, spelled at the
record only through `AppFileRec.file_phi := fun _ h => FileDisc.file_phi h`
— the corollary names no record, so the ghost layer stays out of the
STATEMENT's trusted base.

**THE SHAPE THE AUDIT RULE HANDLES, AND IT IS THE PREMISE ONE.**  `Hprog`
is a section hypothesis in the theorem and therefore an explicit PREMISE
of the corollary — `Hprog -> …`, not a section variable the audit prints.
A theorem's premises are part of its statement and NEVER appear in a
`Print Assumptions` (`EchoAssumptions.v` makes the same point about the
late `Hsh_owed`), and the measured audit confirms it: the fourteen lines
below and NO `Hprog`.

```
PrimInt63.int / .eqb / .sub / .lsl / .lsr / .land / .lor
PrimString.string / .get / .cat / .length
xv6iris_extras.resv_matches / resv_is_valid
FunctionalExtensionality.functional_extensionality_dep
```

The `Axiom` shape — which WOULD print — was declined and should not be
re-proposed: it is weight in the tree that `tools/lemma_diff.py` reports
as a regression, and an audit line nothing ever discharges is worth less
than a binder nothing hides.  `FileAssumptions.v`'s header carries the
complementary check in prose, which is where a reader meets it.

**IS `Hprog` SATISFIABLE?** (durable-notes: a premise on the anchor
theorem is worth a satisfiability witness before it is worth an audit.)
Its SHAPE is — the same field is proved at two other records,
`App.app_triv_init_boot` and `UInitBoot.echo_Hinit_boot`, and its three
equational premises are the ones every record gets.  What is peculiar to
this claim is which ROUTE is open, and that is the lane's one finding for
SH-ROUND.

**WHAT SH-ROUND MUST DELIVER, VERBATIM** (`iris/UFileBootAdequacy.v`, and
identical to `AppFileRec`'s `Context (Hprog : …)`):

```coq
  Definition file_prog_law : Prop :=
    forall (HR : riscvGS Σ) (GEN : GenId)
           (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
           (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ)
           (c : app_fixed (app_file (Σ := Σ)))
           (r : app_names (app_file (Σ := Σ))),
      @file_app Σ HF
        = MkAppcfg (app_names app_file) (app_pred app_file c) r ->
      @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = app_ifc app_file c ->
      @riscvF_genGS Σ (@riscv_fixedGS Σ HR) = riscv_pre_genGS ->
      ⊢ AppInv.app_inv FsCfg.fsc_fs -∗ app_boot app_file c (S gen_id) r -∗
        app_turn app_file c (S gen_id) -∗
        |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
```

Once it is a lemma, the discharge is `Definition`-level: instantiate
`Hprog` at it in `file_adequacy_fileΣ` and delete the premise; nothing
else in either new file moves, and `FileAssumptions.v` keeps its target.

**THE TREE'S DISCHARGE IS NOT AVAILABLE HERE, AND THAT IS A RULING, NOT A
COST.**  `UTreeAdequacy.tree_Hinit_boot` pays the same field in three
lines: the era's turn mints the taint (`AppTree.tree_sup_of_bump`), the
taint IS `AppInv.app_sup` at that claim, and the supply buys
`SystemAdequacy.init_boot_of_sup` — the honest "the era's first process is
not verified against the claim, and the claim records it".  At `app_file`
that route is closed twice over.  (1) There is no turn-to-taint mint and
there must not be one: `AppTree.tree_sup_of_bump` has no file twin, and
`FileOut.file_led`'s counter is `if decide (disc_f h) then 0%nat else
1%nat`, so a `file_taint` held from boot is inconsistent with the ledger
at every history where the user KEEPS the discipline — the `al_rx` step
could not be reproved.  (2) Even read as a weakening it would gut the
conclusion, because `FileOut.file_led_phi` proves `file_phi h` from the
taint by REFUTING `disc_f h`: a boot-time taint makes the theorem say
only "the user never kept the discipline".  So SH-ROUND's route is
`UInitBoot.echo_Hinit_boot`'s — a VERIFIED /init that execs /sh — and the
tainted-at-boot arm that made the tree application a theorem is not on
this campaign's menu.  Recorded here so nobody prices it again.

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

### OFF-HAND-4 (kernel/U tier, 2026-09-17) — THE CARRIER IS THE SET; THE VERIFIED ENTRIES DROP THE ROW; THE SURRENDER'S HOME IS NOT THE TAINT ARM, AND THE EVIDENCE IS ONE CONSUMER CHAIN

**The lane's verdict in one line: S1 landed exactly as design/app-file.md
§3 fact 4 rules it, and so did the HALF of S2 the ruling is really about —
a verified entry no longer receives "the table is all parked", so a held
row may cross `exec` into a verified image.  The OTHER half — the taint
arm taking `FdPark.uoff_surr_at` in place of the pure row — is REFUTED AS
STATED by its own consumer chain, and the refutation says where the
surrender bundle does belong.  S3 is not attempted and the ordering fact
that decides it is recorded.  Everything below is checked at the statement
in the tree.**

**WHAT LANDED** (whole tree green on the lane's remote tree, `make -f
CoqMakefile -j32 -k`, `EXIT=0`, zero `Error`, `make -n` reports nothing
left; `make audit-all-only`: echo audit fourteen, system audit thirteen;
every new result `Proof using`).  Two commits, each green on its own.

*(1) `22292e156` — S1: the carrier is the SET of descriptors a record may hold*

- `UkRun.uk_names`'s `ukn_park : bool` is `ukn_held : gset nat`.  `∅` is
  what `true` was and `ukn_parked` is that as a class
  (`ukn_parked_eq : ukn_held N = ∅`), so **no landed site's spelling
  moved** — `urun_rows_parked`, `UkSh.ush_gen_slot` and the five entry
  constructors read exactly as before, one word apart.
- `UsysMemOk.fdv_held_in H l` is the row, IN THE CONTRAPOSITIVE — every
  UNPARKED row's index is in `H` — because that is the direction every
  consumer has it, and it makes the set an OVER-approximation (so a record
  may be minted at a set wider than it holds, and a fork may widen its
  child's).  `fdv_held_in_empty` is the reading at `∅`,
  `fdv_held_in_of_parked` the other way, `fdv_held_in_mono` the widening,
  `fdv_held_in_insert` / `_closed` the kit.
- `UkRun.urun_parked_row N fdv := fdv_held_in (ukn_held N) fdv`, and
  `urun_rows` is the same bundled conjunct — so the 103 leaves that
  destructure `urun` positionally still do not move.  `urun_rows_held` is
  the new projection (`urun_rows` is persistent, so reading the row off a
  run a leaf is KEEPING costs it nothing).
- `uslot_of_urun` / `_all` / `_ro` mint at a caller-chosen `hs : gset nat`
  with `fdv_held_in hs (uvis_fd W)` as the honest premise and hand the
  program `⌜ukn_held N = hs⌝`.  `UkFork.wp_uk_ecall_fork` / `_argv` mint
  the CHILD at a PARENT-CHOSEN `hs` with `ukn_held N ⊆ hs`, and the child
  arm carries `⌜ukn_held N' = hs⌝`: the child's table IS the parent's, so
  any superset is honest, and the redirect child of §3 has no other place
  to say it may hold slot 1.

*(2) `6cdf267bf` — S2's verified half: the entries drop the row*

- `ExecEntry.image_entry_at` / `image_entry` DROP
  `⌜FdSlots.fdv_all_parked (uvis_fd W')⌝`, and so do the four inline
  VERIFIED spellings on `PinnedExec.pex_slot` / `pex_slot_at` /
  `pinned_exec_bundle` / `_at`.  `image_entry_taint` KEEPS its row (see
  finding 1).
- **The fact is not lost, it moves to the party that can state it.**
  `SpecKexec.kexec_image_ok_fd` pins `uvis_fd W' = sts` and `sts` is a
  PARAMETER of the entry, so each verified constructor says the discipline
  about the table it is stated at: `UShKernel.sh_image_entry_at`,
  `UShEcho.echo_image_entry` and `ExecRun.image_entry_of_taint` take
  `fdv_all_parked sts`; `UInitSh.init_sh_image_entry` takes
  `fdv_all_parked fdv`.
- **AND /init SUPPLIES IT FROM ITS OWN RUN** (`UkRun.urun_rows_parked` at
  the empty held set).  That is precisely what lane OFF-HAND-2 recorded as
  impossible and `UInitSh.v:1376`'s note said in so many words — "only
  `take NSTD fdv = l` … the rest of the table is unconstrained at this
  tier, which is why the premise must ride the kexec SLOT WANDS".  The
  set-valued carrier is what makes it possible; the note is rewritten.
  sh does the same for its /echo child.
- What that costs: the empty held set becomes a PURE ROW on every exec
  supply and fork arm that reaches an entry — `UkInit.init_exec_sup_pos`,
  `UkShEcho.sh_exec_sup_echo`, `UkShFork.ushf_child_law` and
  `wp_kshf_fork_core`'s child arm, `UkShRun.wp_kshr_fork` /
  `wp_kshr_fork1` / runcmd's two child arms, `UkShDiag.wp_kshr_fork1_final`,
  `UkInitMain`'s fork wrapper and `wp_kinit_main_child`,
  `UkShEcho.wp_kshr_exec_echo` / `wp_kshm_child_echo` — read off
  `UkSh.ush_gen_slot_held` (new) at sh and off `UkRun.ukn_parked` at /init.

**STATEMENTS THAT CHANGED SHAPE** (exhaustive).  S1: `UkRun.uk_names`
(hence `MkUkNames`'s last argument type), `ukn_parked`,
`urun_parked_row`, `urun_rows_step` (a new guard at `USYS_dup`),
`urun_rows_dup` (`+ fdst_parked st`), `urun_rows_copy`
(`+ fdst_parked (fdv !!! k)`), `urun_gen` (`ukn_held N = ∅`),
`uslot_of_urun` / `_all` / `_ro`; NEW `UkRun.urun_rows_held`;
`UkRunSys.wp_uk_ecall_dup` / `wp_uk_ecall_dup_untracked`
(`+ ukn_held N = ∅`); `UkFork.wp_uk_ecall_fork` / `wp_uk_ecall_fork_argv`;
`UkSh.ush_gen_slot`; NEW in `UsysMemOk`: `fdv_held_in`,
`fdv_held_in_of_parked`, `fdv_held_in_empty`, `fdv_held_in_mono`,
`fdv_held_in_insert`, `fdv_held_in_closed`, `usys_fd_ok_held`; `UkInit.v`
and `UkInitMain.v` gained a section `Context {!ukn_parked N}` (named only
in the `Proof using` of the lemmas that walk a dup or an exec).
S2: `ExecEntry.image_entry_at` / `image_entry` (and `image_entry_of_at` /
`image_entry_at_of`, `ExecArgs`'s reading bridge);
`PinnedExec.pex_slot` / `pex_slot_at` / `pinned_exec_bundle` / `_at`;
`ExecRun.image_entry_of_taint` (`+ fdv_all_parked sts`) and
`wp_uk_ecall_exec_taint_test` (`+ ukn_held N = ∅`);
`UShKernel.sh_image_entry_at`; `UShEcho.echo_image_entry`;
`UkShEcho.wp_kshr_exec_echo` / `wp_kshm_child_echo` /
`sh_exec_sup_echo`; `UkShFork.ushf_child_law` /
`wp_kshf_fork_core`'s child arm; `UkShRun.wp_kshr_fork` /
`wp_kshr_fork1` / `wp_kshr_runcmd`'s two child arms;
`UkShDiag.wp_kshr_fork1_final`; `UkInit.init_exec_sup_pos`;
`UkInitMain.wp_kinit_main_child` and its fork wrapper;
`UInitSh.init_sh_image_entry`; NEW `UkSh.ush_gen_slot_held`.
**Nothing in `SpecKexec`, `ProofKexec`, `ProofSyscall`, `ProcInv`,
`FdPark`, `FileInvDefs`, `FileInv`, `UexecRet`, `UexecSG`,
`UexecExecInst`, `FsAbsInvFire`, `InitBoot` or `UInitBoot` moved.**

**REFUTED / BLOCKED, with the evidence.**

1. **THE TAINT ARM CANNOT TAKE THE SURRENDER BUNDLE, AND ITS OWN CONSUMER
   CHAIN IS WHY.**  `ExecEntry.image_entry_taint`'s row is spent by
   `UexecExecMint.uslot_mint` (`:397`) → `UexecCond.cond_entry_slot`
   (`:348`) → **the two GATED VERIFIED arms** `sync_gate_slot` (`:271`)
   and `echo_gate_slot` (`:306`), and those need the PURE
   `fdv_all_parked (uvis_fd W)` because they mint a verified record at
   `ukn_held = ∅` — `UkRun.uslot_of_urun*`'s honest premise, which is a
   fact about the table and not a resource.  `FdPark.uoff_surr_at`
   (`:347`) is `⌜fdv_all_parked sts⌝ ∨ uoff_surrs sts`; its right disjunct
   is a big-op of EXCLUSIVE `uoff` halves, no lemma turns it into a pure
   fact, and SPENDING it (`FdPark.fd_frags_park_at`, `:366`) produces a
   DIFFERENT table `fdv_park sts` — so a slot at the key whose table is
   `sts` cannot be minted from the halves at all.  The generic TAIL of
   `cond_entry_slot` needs nothing today, so an `image_entry_taint` at
   `uoff_surr_at` would simply drop the bundle unspent: sound, and
   vacuous.
   **WHERE THE BUNDLE DOES BELONG is where `FdPark.v:577` already says:
   the fork/exec DEPOSIT, spent by the KERNEL before the key is built.**
   `SpecKexec.exec_slot_pre`'s rows are kernel-supplied,
   `fd_frags_park_at` is the kernel's step, and `ProofSyscall`'s exec arm
   (`:5299`, `ProcInv.proc_priv_parked` at `:1459`) is the one site that
   holds the descriptor bundle and the block at once.  Done there, the key
   the taint arm is applied at is all-parked BY CONSTRUCTION and the arm
   keeps a PURE row — which is also what keeps the two gated arms
   provable.  So the §3 sentence "the taint arm takes the SURRENDER
   BUNDLE" should read "the exec DEPOSIT takes it, and the taint arm keeps
   the row the kernel then proves".
2. **THE FANCY UPDATE NEVER REACHES `ProofKexec.kxau_close`, AND AT THE
   PLACE IT DOES REACH IT IS UNELIMINABLE.**  `kxau_close` (`:637`)
   applies `exec_slot_pre`'s two wands and hands `S W'` straight into
   `SpecKexec.exec_post_ok`; `S` is abstract there, so a
   `|={⊤}=> S W'` would be carried, not eliminated.  The elimination would
   have to happen one level DOWN, where `image_entry_taint` is turned into
   `exec_slot_pre` — `ExecBundle.ex_node_id` (`:101`, arms at `:138` /
   `:157`) and `ExecRun.ex_node_abs` (`:722`, arms at `:795` / `:808`) —
   and there the entry's continuation `X` is a PARAMETER, so
   `|={⊤}=> X W' ⊢ X W'` is not provable.  The fupd shape is therefore
   refuted at the abstract supplier, independently of finding 1.
3. **DUP(2) IS THE ONE SYSCALL ROW THE SET-VALUED CARRIER DOES NOT SURVIVE
   FOR FREE, AND NOTHING IN THE CAMPAIGN PREDICTED IT.**  Four of
   `UsysMemOk.usys_fd_ok`'s five moving rows INSTALL a parked descriptor
   (close installs `FdClosed`, open carries `fdst_parked` explicitly, pipe
   installs two ends), so they preserve `fdv_held_in H` at ANY `H`.  DUP
   COPIES its argument's row onto the slot `fdalloc` chose, and that slot
   is not one the record can be said to hold — `fd_least_closed` says
   nothing about the held set.  So `usys_fd_ok_held` carries a guard at
   `USYS_dup`, `urun_rows_dup` / `_copy` carry it row-shaped, and both dup
   leaves (`UkRunSys.wp_uk_ecall_dup`, `_dup_untracked`) take
   `ukn_held N = ∅` and discharge the guard from their own run.  **A held
   descriptor cannot be dup'd at all this lane**; §3 has dup share the
   object's surrender, which needs the two slots' halves to be ONE
   resource, and that is the next lane's.
4. **A `Prop`-VALUED RESTATEMENT PROVED BY `exact` IS A HANG, NOT AN
   ERROR.**  `UkShDiag.wp_kshr_fork1_final` (`:8928`) is
   `UkShRun.wp_kshr_fork1` restated at this file's stack need and closed
   by `exact (wp_kshr_fork1 …)`.  Adding one pure row to the child arm of
   the ORIGINAL and not to the COPY does not fail: the unifier spins on
   the 9013-line file's goal with a perfectly stable 1.8 GB RSS, which
   reads exactly like a slow file.  **When a fork/exec arm grows a row,
   grep for its restatements before building** — `ukn_pay N' =` in premise
   position is the tell, and there are twelve such copies in the U tier.

5. **S3 IS NOT ATTEMPTED, and the ordering fact that decides it is this.**
   The pin (`ProcInv.proc_priv_parked` through
   `SpecKexec.exec_slot_pre`'s pure rows) is what makes finding 1's
   "all-parked BY CONSTRUCTION" true today, so removing it and narrowing
   the generic family are ONE change, not two: `UexecCond.cond_entry_slot`'s
   generic tail needs nothing at present, so nothing forces
   `UexecRet.uexec_wp_uslot` (`:2816`, inside `uslot_of_creds` `:2748`) to
   be re-plumbed until `UexecSG.sbundle_of_supply_ne` (`:468`) /
   `sbundle_of_supply` (`:499`) are guarded and
   `FsAbsInvFire.fsabs_fileread_in` (`:304`) / `fsabs_filewrite_in`
   (`:354`) take the row.  OFF-HAND-3's finding 3 stands unchanged on the
   route; what this lane adds is that the route's FIRST step is a kernel
   one (the deposit, finding 1) and not a U-tier one.

**THE ONE THING OFF-HAND-5 — THE HELD BRANCH, THE PUBLISH, THE LEAVES —
NEEDS FIRST: a ruling on the surrender's HOME (finding 1).**  It decides
two statements that everything else hangs off.  If the bundle rides the
exec/fork DEPOSIT (this lane's evidence), then `ExecEntry.image_entry_taint`
keeps a pure row forever, `fdv_all_parked` never leaves the kernel, and
S3's order is: `ProofSyscall`'s exec arm takes `FdPark.uoff_surr_at`
through `fd_frags_park_at` where `proc_priv_parked` is → the pure rows come
off `SpecKexec.exec_slot_pre` → `FileInvDefs.fpnames`' mode → the held
branch of `fileread_in`/`filewrite_in` → the hand-mode open leaf.  If
instead the taint arm is to grow a resource, then
`UexecCond.cond_entry_slot`'s two GATED arms have to be re-keyed onto
`fdv_park (uvis_fd W)` first — a new key, not a new premise — and that is a
different and much larger change than §3 prices.  Until it is ruled, the
held-row EXEC is unblocked at the entry (this lane) and blocked at the
deposit, and `UEchoFile`'s entry can be written (mint at `ukn_held = {1}`,
`fdv_held_in {1} sts` as its own premise) while its caller's exec cannot
yet pay.

### READ-RELAY (2026-09-17) — THE COPYOUT'S REASON RIDES READ'S `-1` ARM ALL THE WAY UP, AND A MAPPED BUFFER REFUTES IT IN ONE LINE

**The lane's verdict in one line: design/app-file.md §5.3 (c) is SETTLED
AS REFUTED — the `cat: read error` tail is unreachable at a U-tier caller
whose destination buffer it owns, `RCReadErr` is not added, and there is
NO second reason for the failing copyout that the U tier cannot exclude.**

**THE REASON, PRECISELY.**  readi's one `-1` exit is `either_copyout`
answering `-1` on the USER arm.  Its contract already named the byte
(`SpecEitherCopyout.either_copyout_ran` `:116`, out of
`SpecCopyout.copyout_wrote` `:174`): `~ uva_wmapped P (uint
(add_vec_int dst (Z.of_nat d)))` with `d < len` — an address in the
destination run the process's page table does not map for WRITING
(walkaddr answered 0 and vmfault declined, or the re-walk's leaf has
PTE_W clear).  Stated at the ENTRY descriptor, which is the weaker and
therefore usable form (the round's table only GREW: `uptd_ext_sz` +
`UserPtTree.uva_wmapped_mono`).  The relay's carrier is one pure
definition, `SysReadDefs.rd_fail_why P dst n := exists d, (d < n)%nat /\
~ uva_wmapped P (uint (add_vec_int dst (Z.of_nat d)))` — keyed by the
64-bit va like every image equation in the tower, so it promises nothing
about `dst + n` not wrapping, and the index is EXISTENTIAL because
copyout walks whole pages and the failing round may have delivered a
prefix of its own chunk first.

**ONLY ONE REASON, and that is a fact about the code, checked:** readi's
other break (`bmap` returned 0) is dead under `bm_covers`
(`SpecReadi.v:264`), and `either_copyout` answers 0 unconditionally on
the kernel arm (`SpecEitherCopyout.either_copyout_post`'s else branch),
which is why readi's `-1` arm already carried `user = true`.  At an OPEN
READABLE INODE descriptor the only other `-1` above is fileread's own
sign guard, which `FsAbsReadFire.read_post_fail`'s LEFT disjunct already
keys on `n < 0`.  So `0 <= n` plus a mapped buffer leaves no `-1` at all.
Nothing was weakened to cover a second reason; there is none.

**THE RELAY, SITE BY SITE (every statement that changed shape, and
nothing else did).**

1. `SysReadDefs.v` — NEW and pure: `rd_fail_why`, `rd_nwmapped_entry`
   (the round's verdict brought back to the entry table),
   `rd_fail_why_entry`, `rd_fail_why_mono`, and `rd_fail_why_refute` —
   the refutation itself, three lines, "a buffer every byte of which is
   writable-mapped has no failing address in it".  The file gains
   `Require Import UserPtTree` / `ProcPtOwn`.
2. `SpecReadi.wp_readi_sconf_body` — the post's `-1` arm gains a THIRD
   conjunct, `rd_fail_why (pv_upt (us_V U)) dst n`, inside the existing
   `⌜…⌝` premise slot (no new premise).  `READI`/`LinkReadi` unchanged.
3. `ProofReadi.v` — the same arm in `rd_cont`, and as a premise of the
   three return blocks `rd_ret`, `rd_join`, `rd_exit` (all `Local`, all
   pass it through by `exact`).  The loop's chunk post keeps
   `either_copyout`'s third component; the failing index is `tot + dwr`
   off readi's own `a2` (`InstrBytes.pa_add_add`) and is inside the
   request because `dwr < mm <= nc - tot` and `nc <= n`.
4. `FsAbsReadFire.read_post_fail` — gains `(P : uptd)` after `γo` and
   `(addr : mword 64)` last; its `0 <= n` disjunct gains
   `⌜rd_fail_why P addr (Z.to_nat n)⌝` as its SECOND conjunct.
   `read_arms` gains `(P : uptd)` after `γo`.  Consequent parameter-list
   moves only: `read_arms_ret`, `read_arms_neg`, `arf_stable_fail_arm`
   (also gains `addr`), `arf_stable_of_arms`.  `read_post_ok`,
   `read_stable_arms` and `aread_commit_at` are untouched.
5. `SpecFileread.fileread_extra_core` — SAME parameter list; its inode
   branch now passes `pt` into `read_arms`.  **That is the whole reason
   nothing above `fileread` moved**: `pt` was already there for the
   console arm's swallowed byte (lane CONS-SWALLOW W3), so
   `fileread_extra`, `fileread_arms`, `SpecSysRead.sys_read_arms`,
   `SpecSyscall` and `UexecExecInst.xv6_spost`'s row 5 are all unchanged.
   `fileread_extra_inode` / `fileread_extra_inode_of` take `pt` in their
   `read_arms` premise (their own binders unchanged).
6. `ProofFileread.v` — the `blez` skip case's `-1` disjunct carries the
   reason at fileread's own `addr` (readi's `a2` IS `m !!! Ra1`,
   `HJ6a2`), and the fired arm supplies it.
7. `UkReadFile.read_arms_file_learn`, `UkTreeRead.read_arms_tree_learn`,
   `FileOpen.file_read_arms_learn` — each gains `(P : uptd)` after `γo`;
   their CONCLUSIONS are unchanged.
8. `UkFileOpen.wp_uk_read_deed_learns` and
   `UkReadFile.wp_uk_cat_read_learns` — statements UNCHANGED (`P` comes
   out of `spost_at_read_elim` inside the proof).

**PROOF-SCRIPT-ONLY at readi's six other callers.**  `user = true` is no
longer the LAST conjunct of the `-1` arm, so `discriminate` on it needs
one more layer: `ProofDirlookup:1660`, `ProofDirlink:3025`,
`ProofSysUnlinkW3:535`, `ProofKexecACode` (×4), `ProofKexecB2` (×2),
`ProofKexecB3` (×3).  Nothing else in the kernel tier noticed.

**THE REFUTATION, AND IT REALLY IS ONE LINE.**
`FsAbsReadFire.read_arms_mapped` — at `0 <= n`, `Z.to_nat n <= k`, and
"every byte of `[addr, addr+k)` is `uva_wmapped` in `P`",
`read_arms … -∗ read_post_ok …`.  Both `*_learn` families were split so
the mapped corollary does not re-prove the ok arm:
`UkReadFile.read_post_ok_file_learn` + `read_arms_file_learn_mapped`,
`FileOpen.file_read_post_ok_learn` + `file_read_arms_learn_mapped`.
**The program pays nothing for the mapped row**: it is the read leaf's
own, handed out beside the resume image
(`UkReadFile.wp_uk_ecall_read_file`'s fifth pure row, the twin of the
write side's `UkRunSys.usrc_ok` mapped conjunct), and
`UkReadRows.spost_at_read_elim` hands out the `proc_pt_wf` /
`perm_of` / `lazy_free` triple the row consumes.  So the ONLY premise the
mapped corollaries add is `0 <= cnt`.

**WHAT CAT-WALK APPLIES.**
`UkFileOpen.wp_uk_read_deed_learns_mapped` — same statement as
`wp_uk_read_deed_learns` plus `(0 <= cnt)%Z`, and its deed arm has NO
`⌜rv = -1⌝` disjunct: it is `(∃ off, the count ∗ the bytes) ∗ fdq` or the
taint, full stop.  cat reads 512 bytes into a buffer it owns, so that is
exactly its shape, and `cat: read error` has no arm to file.
`UkReadFile.wp_uk_cat_read_learns_mapped` is the same thing at the
generic leaf, kept beside the landed test as the end-to-end check that
the leaf's row alone discharges the relay.

**ONE DELETION, deliberate** (so `tools/lemma_diff.py` has its answer):
`UkReadFile.cat_recv` is gone, replaced everywhere by the new
`UkReadFile.file_read_fam i q bs0 nl` — the same `MkPfam`, named once
because three lemmas now share it.

**FOR THE NEXT LANE.**  The write side's RELAY 4 (design §3) is still
open at the INODE chain: `FsAbsWriteFire.awrite_part_at` carries no
reason and F-WRITE's finding 3 stands.  The shape to copy is this lane's:
the reason is a pure `Prop` in the vocabulary LEAF (`SysWriteDefs`'s twin
of `rd_fail_why`), the chain node carries it, and the refutation is one
lemma at the arms.

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

### F-OPEN-3 (2026-09-17) — THE TRUNCATE'S PERMIT, THE ONE SWEEP, AND THE 0x601 BUNDLE FROM ONE DEED

**The lane's verdict in one line: the permit is exactly the ruling's two
things — the walk's tie and the `Fok ∨ (Fex ∗ the unfired arm)`
disjunction — and it works, but the EXISTS disjunct is paid for by a PURE
reading of the claim at the lookup's own view rather than by the deed
fraction lane F-OPEN-2 priced, so restatements 2 and 3 were never on the
critical path and no third kernel seam was needed.  What did NOT land is
the ruling's `s = None` refutation, and the reason is a VIEW and not a
fraction (P3 below).**

**WHAT LANDED** (whole tree green on the lane's remote tree; every new
lemma `Proof using`; `make audit-all-only` and `audit-tree-only`
unchanged — echo fourteen, system thirteen, tree thirteen).

- **THE SWEEP** (`iris/SysOpenDefs.v` sections 2b'/2b'', `iris/SpecSysOpen.v`
  section 2g, `iris/FsAbsOpenFire.v`, seven `ProofSysOpen*` files and six
  consumers).  `open_trunc_piece Γ vom Kt Ft` takes a PERMIT; the plain
  surface's is `trunc_permit_triv` (nothing rides on its walk's terminal)
  and the O_CREATE surface's is `trunc_permit_of Γ (tie) Farm Fok Fex` —
  the tie (`trunc_tie_at pl P` at the one-path tier, `trunc_tie_arg M pv P`
  under the reading of argument 0, and the two conversions
  `trunc_tie_arg_of_at` / `trunc_tie_at_of_arg`) beside
  `cre_acre_fired Fok d nm i (AFile []) ∨ (cre_ex_fired Fex d nm i ∗
  pf_at (aarm_commit_at Γ appE (AFile [])) Farm)`.  The generic supplier is
  one line (`open_trunc_piece_of_all`, the permit unread), and
  `open_trunc_piece_mono` / `open_trunc_piece_{at_to_arg,arg_to_at}` move a
  piece between the two tiers.
- **THE PERMIT IS PAID ONCE, WHERE WHAT PAYS IT IS IN HAND**
  (`iris/ProofSysOpenEntryC.v`, at create's return;
  `iris/ProofSysOpenCreArm.v` `socr_fresh_key` / `socr_exists_key`).
  Below that point the piece travels KEYED at the inode the call reached
  (`SysOpenDefs.open_trunc_at`), which is what `ProofSysOpenJoin`,
  `ProofSysOpenAlloc`, `ProofSysOpenStores` and `ProofSysOpenShared`'s four
  arm builders now take, and what `FsAbsOpenFire.opf_atrunc_fire` fires
  (`atrunc_commit_i` at that inum).  The plain surface keys for nothing
  (`open_trunc_at_of_triv`).
- **THE KEYED PIECE KEEPS THE PERMIT ON ITS REFUND SIDE**
  (`SysOpenDefs.cre_ft_kept`, and this is the one piece of the design the
  ruling did not name).  `pf_at` is a CONJUNCTION, so paying the permit
  spends it on the COMMIT side only and the refund may keep it —
  which is what makes `SpecSysOpen.open_post_fail_create`'s arm (a)
  survive: `itrunc` runs past `fdalloc`, so a create that fired and an
  open that then failed hands the caller back exactly what it parked in
  the permit.  Without it that arm loses the deed and F-OPEN's "third
  arm" is gone.
- **THE APPLICATION HALF** (`iris/FileOpen.v` sections 3e', 3f, 3f', 3f'').
  `fclaim_free` / `file_claim_read_free` (the claim read at a view NOBODY
  holds a fraction at: `file_pred`'s pins, and the TYPED witness of
  whatever state the claim is at, whose pure part bounds the content by
  `EchoDisc.line_max`), `file_dlk_recv` / `file_dlk_fam` /
  `file_dlk_piece` (the exists observation's family, carrying that pure
  reading and NOTHING linear), `file_trunc_of_exists` (the EXISTS
  disjunct: the arm piece's refund is the deed's whole half, the tie says
  the row is the root's `f`, the pure reading says it is none of the four
  era-0 binaries, and the move `Some (i, bs) → Some (i, [])` is the
  two-phase park-and-resync — with the already-empty case split off, since
  `AppFile.file_resync` wants `s ≠ s'`), and `file_trunc_piece` at the
  permit.
- **THE RECEIPT, READ** (`FileOpen.file_open_create_recv`, with
  `file_open_pay` / `file_legs_pay` / `file_permit_pay` / `file_kept_pay`
  / `file_open_create_fail_pay`).  Three outcomes at the redirect child's
  own mode: `-1` with the deed home (from the arm piece's refund on four
  shapes, and from the KEYED PIECE'S REFUND on arm (a)), a descriptor on
  an inode with `f` present and empty at it, or a descriptor on the found
  DEVICE create's F-OK admits.
- **THE 0x601 BUNDLE, FROM ONE DEED** (`FileOpen.file_open_create_au`).
  No trunc premise at any mode: the bundle supplies its own piece.  New
  premise `last (path_elems pl) = Some fname_f` (the tie is what
  identifies the truncated row, so the lemma must say the path names `f`);
  `Fex` is `file_dlk_fam c` and `Ft` is `file_trunc_fam c r s`.
  `file_open_create_au_notrunc` is SUBSUMED — kept as a one-line corollary
  under `om_trunc vom = false` so a 0x201 caller need not read the guard.

**STATEMENTS THAT CHANGED SHAPE, EXHAUSTIVELY.**  At `om_trunc vom = false`
every one of them reads exactly as it did — the guards are `if om_trunc vom`
and the `else` arm is the landed text — so no existing caller's CONTENT
moved; what moved is the syntax they destruct.

1. `SysOpenDefs.open_trunc_piece` — one more argument (the permit);
   `open_trunc_piece_{true,false,none}` follow it.  New beside it:
   `open_trunc_piece_of_all`, `open_trunc_piece_mono`,
   `open_trunc_piece_{at_to_arg,arg_to_at}`, `open_trunc_at` with
   `_{true,false,none,of_permit,of_triv}`, `cre_ft_kept`,
   `trunc_permit_triv`, `trunc_tie_at`, `trunc_tie_arg`,
   `trunc_tie_{arg_of_at,at_of_arg}`, `trunc_permit_of`,
   `trunc_permit_of_mono`.  `Typeclasses Opaque` extended to all of them
   (unsealed, one `iFrame` in `ProofSysOpenCreArm` took twenty minutes).
2. `SysOpenDefs.open_au_pre_plain` / `open_au_plain_at` — the piece at
   `trunc_permit_triv`; `open_au_pre_create` / `open_au_create_at` — the
   piece at `trunc_permit_of` at the matching tie.  No arity change: the
   permit is built from parameters the bundles already had.
3. The four `SysOpenDefs.open_au_*_of_all` — their trunc premise names the
   bundle's permit.
4. `SpecSysOpen.open_post_ok_plain` / `open_receipt_plain` — the DEVICE and
   DIRECTORY arms at `open_trunc_at Γ vom i Ft`.
   `open_post_fail_plain` — arm 3 the same; arms 1 and 2 at the trivial
   permit.
5. `SpecSysOpen.open_post_ok_create` / `open_receipt_create` — the walk's
   terminal cursor at `cre_cur_kept`, the FRESH arm's create receipt and
   the EXISTS arm's lookup receipt at `cre_rcpt_kept`, the EXISTS arm's
   child legs at `cre_child_kept`, the EXISTS-DEVICE arm's piece at
   `cre_trunc_kept`.
6. `SpecSysOpen.open_post_fail_create` — the cursor at `cre_cur_kept`, and
   the trunc piece moved OUT of the common prefix INTO the arms: (a) at
   `cre_trunc_kept` beside `cre_rcpt_kept`, (b) at `cre_fail_kept` (the
   piece and the child legs TOGETHER, because whether the permit was paid
   is what decides both), (c) and the walk-dead arm at the unkeyed piece.
7. `SpecSysOpen.cre_fail_to_open` — its trunc premise is the one-path
   permit.  New definitions: `cre_permit`, `cre_trunc_kept`,
   `cre_cur_kept`, `cre_rcpt_kept`, `cre_child_kept`, `cre_fail_kept` and
   their five intro lemmas.
8. `FsAbsOpenFire.opf_atrunc_fire` — takes `pf_at (atrunc_commit_i Γ appE i)`.
9. `FsAbsInvFire.fsabs_trunc_piece` — one more argument (the permit, unread).
10. `ProofSysOpen{Join,Alloc,Stores}`'s block premise — `open_trunc_at …
    (bv_unsigned inum) Ft`; `ProofSysOpenShared.so_arm_{fail,dev,dir,notr}`
    the same at their `i`; `so_arm_dead` at the trivial permit;
    `ProofSysOpenWalk`'s block at the trivial permit (it keys at the two
    join calls and at the C-FAIL arm); `ProofSysOpenEntryC`'s block at the
    one-path permit (it pays it at create's return and runs the tail at
    `socr_ft`).
11. `ProofSysOpenCreArm.socr_fresh` / `socr_exists` — one more argument
    (`vom`) and the three guarded slots; `socr_res_of_fail` returns the
    KEYED piece; `socr_ok_exists_arm`'s device arm the same;
    `socr_arms_fresh` / `socr_arms_exists` run the tail at `socr_ft`.  New:
    `socr_ft`, `socr_ft_recv`, `socr_ft_kept`, `socr_fresh_key`,
    `socr_exists_key`.
12. `PinnedOpen.pinned_open_bundle_at` / `pinned_open_bundle` — the trunc
    premise at the trivial permit; `pinned_open_dev`'s device arm returns
    `open_trunc_at … ino Ft`.  `UInitCons.init_cons_open_bundle` and
    `init_cons_recv` the same at the console's inum.
13. `UkTreeCreate.tree_open_create_fail_recv` — ONE NEW PREMISE,
    `om_trunc vom = false` (the tree application's own mode; without it the
    guarded arms cannot be read).  Its two consumers pass the `Htr` they
    already hold.
14. `FileOpen.file_trunc_recv` — three arms (`fown r s`,
    `fown r (Some (i, []))`, the taint), the middle one no longer under
    `⌜s = None⌝`; `file_trunc_piece` restated at the permit, with the path
    premises and the line witness; `file_open_create_au` /
    `_notrunc` as above.  New beside them: `fclaim_free`,
    `file_claim_read_free`, `file_dlk_recv` / `file_dlk_fam` /
    `file_dlk_piece`, `file_trunc_of_exists`, `file_open_pay`,
    `file_permit_pay`, `file_kept_pay`, `file_legs_pay`,
    `file_open_create_fail_pay`, `file_open_create_recv`.  Section 6's
    STOP record is rewritten (what closed, what the pure reading replaced,
    and the two holes that remain).
15. `ProofSysOpenFull`, `TreeMove`, `UConsOpen` and `UkTreeRead` changed at
    CALL SITES only (one conversion in `Full` between the two tiers, one
    argument each in the other three).  Nothing else.  `AppFile.v` again
    needed no change.

**WHAT THE RULING SAID AND THE PROOFS CORRECTED.**

1. **The EXISTS disjunct needs NO deed fraction, so F-OPEN-2's
   restatements 2 and 3 are not needed.**  The ruling took F-OPEN-2's
   finding 2 (identify `i` with a positive fraction inside `Fex`'s
   receipt, reassemble the half from the arm's refund) and its finding 3
   (the split is impossible at `s = None`, so make `Fex` and the arm
   exclusive).  Neither is required: what the truncate must know about the
   row is that it is none of the four era-0 binaries, and the CLAIM SAYS
   THAT AT THE LOOKUP'S VIEW WITHOUT ANY FRACTION — `file_pred`'s
   non-taint arm carries `⌜file_fs_pure av⌝`, and BOTH arms of `f_state`
   carry the typed witness of whatever state the claim is at, whose pure
   part bounds the content by `EchoDisc.line_max`
   (`FileDeltas.f_bytes_typed_short`), so `f_inum_not_pinned` applies.
   That is `file_claim_read_free`, it costs nothing linear, and it leaves
   the deed's WHOLE half in the arm piece where the create leg needs it.
2. **The permit must keep itself on the refund side.**  The ruling had the
   permit spent at the fire; it is spent at create's RETURN (that is the
   only instant where the tie, the cursor and the fired arm are all in
   hand, and the tail below the join is parametric in nothing else).
   Spending it there would burn the caller's investment on every arm that
   does not fire the truncate — arm (a) above all — so the keyed piece
   carries `Ft.(pf_refund) ∗ Kt i` (`cre_ft_kept`).  The `∧` in `pf_at` is
   what makes that free.
3. **The walk's terminal cursor is SPENT, not read.**  The tie needs it
   (`d = ROOTINO` for this claim is a fact only the cursor carries), `P`
   is an arbitrary possibly-linear predicate, and the kernel may not
   duplicate it — so a TRUNCATING create's arms do not report the terminal
   cursor (`cre_cur_kept`).  For every landed caller this is free: they
   are at `om_trunc vom = false`, and the file application's cursor is the
   pure `⌜d = ROOTINO⌝`.
4. **The fold's "name existed" failure arm has TWO producers** and they
   differ in whether the permit has been paid (create's own failure fold
   reaches it with the piece whole; sys_open's later failure past a good
   found node reaches it keyed).  The arm therefore reports
   `cre_fail_kept` — the piece and the child legs TOGETHER — rather than
   the piece alone, because the arm's half is what the permit was paid
   with.

**REFUTED / BLOCKED (deliverable P3): THE `s = None` EXISTS DISJUNCT IS
DISCHARGED AND NOT REFUTED, AND THE REASON IS A VIEW.**  The ruling said
the disjunct is refuted at an absent deed because "`f_ok av None` says the
root has no `f`, contradicting `Fex`'s found entry at the tie".  The two
facts are at DIFFERENT VIEWS and no later view carries the entry: `Fex`'s
receipt is the instant create's `dirlookup` read the parent (`avx`), the
`itrunc` fires much later, and between them create has `iunlockput`ed the
parent — so the kernel cannot restate the entry at the truncate's view,
and it would be dishonest if it did (another process may unlink in the
window).  Refuting therefore needs the claim's OWN VALUE read at `avx`
(not the determined one `file_claim_read_free` gives), which needs a
positive deed fraction inside the `Fex` piece; at `s = None` the create's
parent leg has already claimed the half in full (`file_step_park` at `f`
joins it with the claim's to make `fdeed_whole`, and the bundle's pieces
are `∗`-separated).  So:

- `FileOpen.file_trunc_of_exists` DISCHARGES the disjunct instead: at
  `s = None` the truncate at that row is a FREE step (the row is not
  pinned, `f_ok av None` is preserved) and the deed comes back UNMOVED.
  The lane is green and the bundle is suppliable at every deed value.
- The price is in `file_trunc_recv`'s first arm (`fown r s`): on a
  truncating `open(f, 0x601)` the fd arm's payload is
  `fown r (Some (i, [])) ∨ fown r s` and not `fown r (Some (i, []))`
  alone.  The second disjunct is unreachable on any RUN and unrefutable in
  the STATEMENT.
- TWO WAYS TO CLOSE IT, and neither is this lane's: (i) F-OPEN-2's
  restatement 3 — `FsAbsCreateFire.acre_commit_at_gen` takes the UNFIRED
  `Fex` piece beside the arm's receipt, making create's two arms exclusive
  IN THE LOGIC, at which point `Fex` may hold `q2` and the parent leg
  reassembles `q1 + q2` (kernel-tier, and it moves create, mknod, unlink
  and open); or (ii) an APPLICATION-SIDE ESCROW — the deed's half in an
  invariant of the claim's own with a one-shot in the arm piece saying it
  has not fired, so the lookup may READ it and the arm may TAKE it
  (`FileOpen`'s business alone, no kernel restatement).  (ii) is the
  cheaper of the two and is the concrete counter-scenario the ruling asked
  for before re-proposing (i).
- A SECOND, SMALLER HOLE OF THE SAME SHAPE: the EXISTS arm's DEVICE
  sub-arm (create's F-OK admits a found device) cannot be refuted either,
  for the same reason — the row's type is reported at the OPEN's
  observation instant and the claim's tie is at the lookup's.  A caller
  that wants "the fd is on `f`'s own inode" must close both.

**THE ONE THING LANE SH-ROUND NEEDS FIRST.**  `FileOpen.file_open_create_au`
is now the redirect child's whole open at `0x601`: one deed in, the bundle
out, no truncate premise.  What SH-ROUND must instantiate is
`UkShRedirAns.ush_open_call2` at

    K ty := ∃ i γo, ⌜ty = FdInode i γo OffParked⌝ ∗
              (fown r (Some (i, [])) ∨ fown r s)
    Kf   := fown r s ∨ (∃ i, fown r (Some (i, []))) ∨ file_taint c

— `Kf` is exactly what F-OPEN-2 named (arm (a)'s deed comes home through
the keyed piece's refund, `cre_ft_kept`), and `K` is F-OPEN-2's with the
second disjunct the paragraph above explains.  THE RECEIPT READER IS
WRITTEN: `FileOpen.file_open_create_recv` folds `open_receipt_create` at
these families into THREE outcomes — the `-1` arm at `file_open_pay`
(F-OPEN-2's `Kf`, with the taint), a descriptor on an INODE with
`fown r (Some (i, []))` or the unmoved deed, and a descriptor on a found
DEVICE with `file_open_pay` — and `file_open_create_fail_pay` /
`file_legs_pay` / `file_permit_pay` / `file_kept_pay` are where each of
the five failure shapes hands the deed back.  So SH-ROUND's remaining
choice is only whether to take the fd arm at that shape or close (ii)
first; everything else it needs of this lane is landed, and the U-tier
wrapper (`wp_uk_ecall_open_create_deed`, `UkTreeCreate`'s mould at this
claim) is the one piece still unwritten — it wants OFF-HAND-3's held
offset anyway, exactly as F-OPEN-2's three U-tier corollaries do.
