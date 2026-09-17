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
