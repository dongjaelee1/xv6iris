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
