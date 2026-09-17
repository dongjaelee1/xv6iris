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
