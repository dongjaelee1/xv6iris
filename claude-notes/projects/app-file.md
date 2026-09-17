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
