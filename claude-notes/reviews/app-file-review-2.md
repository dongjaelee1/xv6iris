# Review 2: the FILE application campaign, seven hours after review 1

Independent review, 2026-09-17 (evening), of `main` at `d8ffd312c`
(22:38) against the first review's commit `3327a0dc7` (15:38), plus the
three lanes in flight (`app-file/off-hand` = OFF-LINK-6, uncommitted diff
of 11 files; `app-file/sh-redir` = SH-CHILD-2, one commit ahead and in a
`MERGE_IN_PROGRESS` state; INIT-FILE, no commit yet).  Every number below
was taken with `git` or `grep` on this tree; nothing under `iris/` was
edited.  The owner's question was "are you just running in circles?"; the
short answer is in §0, the numbers in §1, the causes in §2–§3, the fix in
§4, the path in §5.

## 0. The verdict, in eight sentences

1. It is NOT running in circles: since review 1 the offset design has
   gone from "the half in the kernel's bundle" to a landed, green,
   mode-generic kernel (`FsAbsWriteFire.awrite_full_adv`,
   `SpecFilewrite.filewrite_in_held`, `ProofFilewrite.fw_loop` at both
   modes, `FdPark.v` deleted), the link record exists at both
   applications (`LinkRec.echo_link_inst` definitional,
   `FileLinkInst.file_link_inst` green), cat's entry is a theorem with no
   Iris premise left (`UCatKernel.cat_child_of_entry`), and 13 of the 22
   skeleton obligations have a discharging lemma on `main` (§1.1).
2. It is ALSO not converging at the place that matters: the three
   skeleton files still carry **12 `Admitted` and 15 `Hypothesis`**
   (`grep` on `iris/UEchoFile.v`, `iris/UShRound.v`, `iris/UInitFile.v`),
   exactly as SKELETON left them seven hours ago, and **nine of those
   fifteen hypotheses are dischargeable today by a lemma that already
   exists on `main` and that no lane applied** (§1.1, column "on main").
   The campaign's progress metric — hypotheses and `Admitted` in those
   three files — has not moved since 16:08.
3. The residue chains are shrinking in only one of three cases (§1.3):
   CAT-GEOM went 6 → 4 → 3 → 2 and its last two residues are another
   lane's; LINK-GEN's residue count stayed at 3–6 for six lanes because
   each lane found a NEW echo-specific statement one layer below the one
   it fixed; OFF-LINK's residue list has contained "L2, L4, L5" in all
   five of its reports — what changed each time was the reason they
   were blocked, not the list.
4. The single largest cost is not the kernel and not the mathematics; it
   is that echo's assumptions live in `UkSh.v`/`UkShEcho.v`/`UShLine.v`
   as literals (`disc_input`, `body_ok`, `alt_execfail`/`17`,
   `ush_fd1p`, `ush_line_is`, `OffParked`) and were found ONE PER LANE
   (eighteen since review 1, listed in §2.1) because every lane stated
   its obligations at echo's landed NAMES instead of instantiating them.
5. The coordinator's turns went to merges: 45 of 147 commits on `main`
   since review 1 are merges (31%), 39 are notes (27%), 63 are proof
   commits (43%); 22 of the merges are "merge main into a lane"; 7 are
   fix-forwards; 25 commit messages mention a conflict; the worklist file
   was touched by 53 commits, 22 of them merges.  Two tree-wide changes
   (SUP-ONE's rename of 212 sites in 50 files; OFF-LINK-2's deletion of
   `ukn_held` from 15 files) landed while five lanes were open and broke
   `main` for three of them (§2.3).
6. One item on the critical path is UNOWNED and not in the design's
   remaining list: WRITE-RELAY-3's `TB : uptd -> Prop` guard.
   `filewrite_in_held`'s link arm on `main` is `∀ P : uptd,
   awrite_chain_adv … P …` (`iris/SpecFilewrite.v:687`), so echo must pay
   the partial node at EVERY page table, and `UEchoFile.ef_relay4` refutes
   it only at a table tied to the caller's own (`perm_of (ud_um P) sz =
   pmv`, `proc_pt_wf P`, `lazy_free`).  `ef_chain` cannot be proved as
   stated until that guard lands (§5, item 3).
7. Two rulings since review 1 were wrong and re-done (the `off_settle`
   supplier, OFF-LINK → OFF-LINK-2; the ANCHORED node, OFF-LINK-3/4 →
   OFF-LINK-5) and four smaller ones (`(⊢ Cend)`, `lk_pan : nat`,
   `Hdsc_nl` at `body_ok`, "read(5) excluded by construction"); together
   about five of twenty-two lane-equivalents (§2.4).  All six were
   refuted at the STATEMENT, by the next lane, as review 1's §A5 said
   the earlier ones were.
8. The fix is not another sub-lane.  It is to stop the three chains,
   hand the three skeleton files to ONE assembly lane each with the right
   to change any statement it needs (§4, option 1), run the remaining
   kernel work (OFF-LINK-6 + L5 + TB) as ONE serial lane whose exit
   criterion is "`UShRound.Hopen_hand`, `UShRound.Hchild_cat`'s lend and
   `UEchoFile.ef_chain` compile as `Definition`s", and merge at lane end
   only.  Priced: ~4,000–5,500 lines and 6–8 serial lanes to
   `file_Hinit_boot` (§5).

## 1. The measurements

### 1.1 The 22 SKELETON obligations, as of `main` (`d8ffd312c`)

Read from `iris/UShRound.v`, `iris/UEchoFile.v`, `iris/UInitFile.v` and
`grep`ped for every lemma a later findings block claims.  DISCHARGED =
the hypothesis is gone from the file; DISCHARGEABLE = the hypothesis is
still in the file but a lemma on `main` proves it as stated;
CHANGED SHAPE = the hypothesis was restated by a later lane;
OPEN = nothing on `main` proves it.

| # | hypothesis | status on main | the lemma (file) | note |
|---|---|---|---|---|
| 1 | `Hoff_link` | **DISCHARGED** | `UEchoFile.ef_off_link` (via `OffGv.off_ret_adv`, then `off_link`) | WRITE-RELAY + OFF-LINK-2 |
| 2 | `Hrelay3` | **DISCHARGED** | `UEchoFile.ef_full_adv_of` (`SpecCopyin.ubytes_at_inj`) | WRITE-RELAY |
| 3 | `Hrelay4` | **DISCHARGED** | `UEchoFile.ef_relay4` (`FsAbsWriteFire.awrite_part_at_mapped_single`) | but see §0(6): only at a tied `P` |
| 4 | `Hdep1` (`UEchoFile.v:319`) | CHANGED SHAPE, still a hypothesis | `UkWriteFile.udepwf_std_write_file` (parked) / `udepwf_std_write_file_held` (held) | the hypothesis binds `om` free; the held deposit is at `OffHeld`; echo's fd 1 IS held, so the hypothesis must be re-stated at `OffHeld` |
| 5 | `Hwrite1` (`:338`) | **DISCHARGEABLE**, still a hypothesis | `UkWriteFile.wp_uk_ecall_write_std` | OFF-LINK L5 said "discharged by `exact`"; never applied |
| 6 | `Hwbl` (`UShRound.v:195`) | **DISCHARGEABLE** | `FileLinkInst.file_Hwbl` | LINK-GEN-2 |
| 7 | `Hwbwc` (`:197`) | **DISCHARGEABLE** | `FileLinkInst.file_Hwbwc` | LINK-GEN-2 |
| 8 | `Hcltaint` (`:205`) | CHANGED SHAPE (era-pin premise), DISCHARGEABLE | `FileLinkInst.file_Hcltaint` | LINK-GEN → LINK-GEN-4 |
| 9 | `Hwc` (`:209`) | CHANGED SHAPE (`ush_mid_at (lk_rres FI)`), DISCHARGEABLE | `FileLinkInst.file_Hwc`, `UShLine.ush_mid_wc_read_t_at` | LINK-GEN-3/4 |
| 10 | `Hwbr` (`:216`) | CHANGED SHAPE, DISCHARGEABLE | `FileLinkInst.file_Hwbr`, `UShLine.ush_wb_read_holds_at` | LINK-GEN-3/4 |
| 11 | `Hktaint` (`:223`) | free (record equation), still a hypothesis | — | renamed `app_taint` by SUP-ONE |
| 12 | `Hopen_hand` (`:327`) | **OPEN** | `wp_uk_ecall_open_recv_img_hand` does not exist; `UserOff.off_pub_hand_0` exists, unused by the publish | OFF-LINK-6 (L2+L4) then L5 |
| 13 | `Hlexr` (`:339`) | **DISCHARGEABLE** (a closed theorem) | `UShLexRedir.ush_line_lexable_redir_holds` | SH-LEX-REDIR said "delete the hypothesis"; SH-CHILD then found nothing consumes it |
| 14 | `Hchild_echo` (`:344`) | **OPEN** | generic `UShEchoPay.sh_exec_sup_echo_wq_holds_at` exists; `file_stage_inst : StageRec file_link_inst` does NOT | priced field-by-field in LINK-GEN-3 §5; open since LINK-GEN (six lanes) |
| 15 | `Hexecfail` (`:354`) | CHANGED SHAPE (`ush_execfail_law_wq_at (lk_exfb FI) …`), DISCHARGEABLE | `UShEchoPay.ush_execfail_law_wq_at_hold` | LINK-GEN-2/4 |
| 16 | `Hpanic` (`:361`) | **DISCHARGEABLE** | `UShPanic.ush_panic_law_hold_at file_link_inst sh_hold` | LINK-GEN |
| 17 | `Hchild_cat` (`:402`) | CHANGED SHAPE twice; the ENTRY is a theorem | `UCatKernel.cat_child_of_entry` (no Iris premise) | but its `Pay` = `cat_lend`, which contains `cat_open_hand` and `cat_held_read`, both OPEN until L4/L5 |
| 18 | `Hchild_redir` (`:482`) | **OPEN** | `UkShRedirBody.sh_redir_child_law` is a `Definition` (a statement); `ushf_rest_of_body_file` takes it as a premise | SH-CHILD-2 in flight; needs 12, `efile_image_entry` (Admitted), 15, plus SH-CHILD's three residues |
| 19 | `Hcons`/`Htag` | free (section `Context`) | — | — |
| 20 | the links bundle | **DISCHARGED** | `FileLinks.file_links`, `file_links_holds` | LINK-GEN |
| 21 | `ush_tag_law`'s `D` | **DISCHARGED** (carrier); `sh_tag_law_file` still `Admitted` | `UkSh.ush_tag_law_at`, `ush_tag_law_of_at` | LINK-GEN item 21 |
| 22 | `init_boot_pay` with the deed | **OPEN** | `UInitKernel.init_boot_pay` unchanged | INIT-FILE in flight |

Tally: DISCHARGED 5 (1, 2, 3, 20, 21), DISCHARGEABLE-but-not-applied 9
(5, 6, 7, 8, 9, 10, 13, 15, 16), free 2 (11, 19), CHANGED SHAPE needing
one re-statement 1 (4), OPEN 5 (12, 14, 17's lend, 18, 22).  The skeleton
files themselves were edited by five different lanes' commits
(`git log -- iris/UShRound.v`: SKELETON, CAT-GEOM-2, SUP-ONE's rename,
OFF-LINK-2, LINK-GEN-4, CAT-GEOM-4) — the "SKELETON owns the file" rule
that stopped SH-LEX-REDIR from deleting `Hlexr` and OFF-LINK from applying
`wp_uk_ecall_write_std` was not a rule anyone else followed.

**Obligations discovered SINCE the skeleton that are not in the 22**
(each cost a lane or a sub-lane; §2.1 has the mechanism):

| new item | found by | status on main |
|---|---|---|
| `UkSh.ush_read_ans`'s `disc_input` literal | LINK-GEN-3 | closed (LINK-GEN-4, `_at Dsc`) |
| `UkSh.ush_rest_line`'s `ush_line_is` (no `>` possible) | SH-LEX-REDIR §4, SH-CHILD | closed (`ush_line_at`, `ush_rest_line_at D`) |
| `UkSh.ush_gets_done`'s `body_ok` / `line_ok` (`cmd_echo`) | LINK-GEN-5 | closed (LINK-GEN-6, `ush_gets_done_at Dl`) |
| the walk's three `disc_input` readings (`UkSh.v:3961/:4190/:4338`) | LINK-GEN-4 | closed (LINK-GEN-5, `Dsc` + 3 laws) |
| `Hws : fbody_ok J -> uline_ws (uline_of J) = wl_words J` — false at `LCat` (`FileDisc.uline_ws LCat = []`, `iris/FileDisc.v:139`) | LINK-GEN-6 | **OPEN**, a one-line model choice |
| `UkShEcho.wp_kshr_exec_echo`'s `ush_fd1p` (`iris/UkShEcho.v:461/:539/:831`) | SH-CHILD | **OPEN**, SH-CHILD-2 in flight |
| `UkShDiag.ush_execfail_law`'s `alt_execfail`/`17` literal | LINK-GEN-2 | closed (`_at dg n`) |
| `UkShEcho.ush_execfail_law_wq`'s constant carrier | LINK-GEN-3 | closed (LINK-GEN-4, `_wq_at`) |
| `UkShEcho.ushf_child_law_holds`'s constant carrier | LINK-GEN-4 | **OPEN** (one statement) |
| `LinkRec.lk_pan/lk_exf : nat`, `lk_exfb` missing | LINK-GEN-2 | closed |
| the file `StageRec` (`file_stage_inst`) and the fact `fab I 0 = line_alts_of (last_ws I) !!! 0` | LINK-GEN-3 | **OPEN** |
| `UkRun.uslot_of_urun_ro` cannot carve cat's `.bss` buffer | CAT-GEOM | closed (`uslot_of_urun_all`) |
| `ExecEntry.image_entry` is `□` over the key: linear rows must ride `Pay` | CAT-GEOM-3/4 | closed (`cat_lend`) |
| `kcat_round_of_law`'s `(⊢ Cend)` — unsatisfiable at a claim | CAT-GEOM-3/4 | closed (`□ Cend`) |
| `cat_round_at`'s `□ kcat_dg_cr` — an UNSATISFIABLE premise (vacuous round) | CAT-GEOM-2 | closed (deleted) |
| the redirect seam's exit payment `(⊢ ukn_pay N (-1))` | SH-CHILD | **OPEN** (SH-CHILD-2) |
| `echo_argv_bytes` at the redirect NUL cut | SH-CHILD | **OPEN** (SH-CHILD-2) |
| `Hcat_body` — the `cat` line's walk from 0x97a through the `cd` test | SH-CHILD | **OPEN** (`UkShRedirBody.v:271`, a `Hypothesis`) |
| `off_settle` cannot be the taint's home (vacuity) | OFF-LINK | closed (OFF-LINK-2, `off_link` in the lend) |
| the anchored node / `write_held_post`'s existential `off0` | OFF-LINK-4 → OFF-LINK-5 | closed (client-advanced node) |
| `fdstate_ok`'s `m = OffParked` pin (`iris/FileInvDefs.v:564`) and the publish's literal `OffParked` — ONE change (L2+L4) | OFF-LINK-5 | **OPEN**, OFF-LINK-6 in flight (146 occurrences of `fdstate_ok` in 21 files) |
| `awrite_part_at` is ALSO the disk-full short arm | WRITE-RELAY | closed (`wi16_atomic`, WRITE-RELAY-2) |
| the `TB : uptd -> Prop` guard on `filewrite_in` (WRITE-RELAY-3) | WRITE-RELAY | **OPEN and UNOWNED** — see §0(6) |
| survey R1 "the supply IS the taint" | SUP-ONE | refuted, recorded |
| "read(5) is excluded by construction" (CAT-GEOM-2) | CAT-GEOM-3 | corrected (`udepw_law_of_sup_read`) |

So the OPEN set on `main` is: 5 skeleton items + 9 new items = **14
named obligations plus 12 `Admitted` proofs**, versus 22 named
obligations plus 12 `Admitted` seven hours ago.  That is the honest
convergence number: the NAMED set shrank by a third; the PROVED set did
not move.

### 1.2 Commits, merges, lanes

- Window: `3327a0dc7` (15:38:51) → `d8ffd312c` (22:38:38): **7h00m**.
- `git log --oneline 3327a0dc7..main | wc -l` = **147** (seven of these
  are TL-9 commits from before the review that reached `main` through a
  later merge; net ≈ 140).  Merge commits **45** (31%); `claude-notes`
  commits **39** (27%); non-merge proof commits **63** (43%).
- "Merge main into <lane>" / "Merge remote-tracking" / "Merge branch
  'main'": **22**.  Commits titled fix-forward/repair: **7**.  Commit
  messages mentioning "conflict": **25**.
- `claude-notes/completed/app-file.md`: touched by **53** commits, **22**
  of them merges — every lane appends to one 10,811-line file and every
  merge of it conflicts.
- Findings blocks appended since review 1: **23** (SKELETON, WRITE-RELAY,
  LINK-GEN, SH-LEX-REDIR, CAT-GEOM, OFF-HAND-7 (stopped), OFF-LINK,
  WRITE-RELAY-2, SUP-ONE, SH-CHILD, LINK-GEN-2 ×2, LINK-GEN-3, OFF-LINK-2,
  LINK-GEN-4, CAT-GEOM-2, OFF-LINK-3, LINK-GEN-5, CAT-GEOM-3, OFF-LINK-4,
  CAT-GEOM-4, LINK-GEN-6, OFF-LINK-5) = **22 lanes in 7 hours**, ≈ 3.1
  lanes/hour, four to six concurrent at any moment (the timestamps in
  `git log --format='%h %ci %s'` show CAT-GEOM-2 17:35–19:39 overlapping
  SH-CHILD 17:54–18:30, LINK-GEN-2 18:06–18:39, LINK-GEN-3 17:53–18:44,
  OFF-LINK-2 18:27–19:33, SUP-ONE 16:23–17:50).  Median lane length
  between first and last commit: ~35 minutes; OFF-LINK-3's is five
  minutes (a merge plus a derivation), LINK-GEN-6's ten minutes of
  commits after an hour wedged.
- In flight: OFF-LINK-6 (worktree `off-hand`: 11 files, +189/−167,
  uncommitted, in `FileInvDefs.v`/`ProofFile*`/`ProofSysOpen*` — the
  L2+L4 change); SH-CHILD-2 (`app-file/sh-redir` one commit ahead,
  worktree in `MERGE_IN_PROGRESS` with 31 files staged from `main`);
  INIT-FILE (no commit, no worktree diff).

### 1.3 The residue chains — what each lane returned as "what remains"

**OFF-LINK (5 lanes, 16:07 → 21:55).**
- OFF-LINK: landed L1 (`FdPark.v` gone), the vacuity check, `off_settle`,
  L5's ledger-slot leaf, half of L6.  Remains: L2 (`fp_om`), L3 (box arm,
  "stopped on the node's LEND"), L4 (mint), L5 (held leaves), L6's
  deletions — **5**.
- OFF-LINK-2: landed L6, L3 (lend/box/supplier/fires at `off_link`;
  `off_settle` deleted).  Remains: L2 ("written and reverted a second
  time"), L3's contract arms, L4, L5 — **4**.
- OFF-LINK-3: landed the merge and its fix-forward; produced the
  "anchored node" derivation.  Remains: (a) the arms + fire sites, (b)
  L2, (c) L4, (d) L5 — **4**.
- OFF-LINK-4: landed the anchored node, both held arms, echo's held
  deposit.  Remains: the write fire's loop, L2, L4, L5 — **4**.
- OFF-LINK-5: DELETED the anchored node (`awrite_*_anch`, `fw_au_anch`,
  `write_held_post` — 17 names), landed the client-advanced node and
  both loops at both modes.  Remains: L2+L4 as ONE change (146 sites),
  L5, CAT-GEOM-4's two hypotheses — **3**.
- Last three residues: {loop, L2, L4, L5} → {L2+L4, L5, cat's two} →
  (OFF-LINK-6 running on L2+L4).  **L2, L4 and L5 appear in all five
  reports.**  The list shrank by two items in five lanes; the kernel
  under it was rebuilt twice (settle → link; anchor → client node).

**LINK-GEN (6 lanes, 15:59 → 21:55).**
- LINK-GEN: `LinkRec`, `UShPanic`/`UInitBanner` swept, items 20/21.
  Remains: the file instance (~1,100 lines est.), `Hcltaint`'s shape,
  `UEchoOut`/`UShEchoPay` need a stage abstraction, `UShLine`'s read leaf
  (3 laws), `Hchild_echo` — **5**.
- LINK-GEN-2 (a, b): `FileLinksLine.v` (2,081 lines, twice the estimate),
  `file_link_inst` green after three record fields were re-typed.
  Remains: `Hchild_echo` (StageRec), `Hcltaint` one line, `Hexecfail`'s
  shape — **3**.
- LINK-GEN-3: `StageRec`/`CurRec`, `UEchoOut`/`UShEchoPay`/`UShLine`/
  `UShRest` generic.  Remains: `ush_execfail_law_wq`'s constant carrier,
  a `ReadRec` blocked on `ush_read_ans`'s `disc_input` literal (NEW), the
  file `StageRec` fields, the `fab I 0 = line_alts_of …` fact — **4**.
- LINK-GEN-4: seven `UkSh` statements at `Dsc`, `ReadRec`, the read leaf
  generic.  Remains: the walk's three readings ("a lane"),
  `ushf_child_law_holds`'s carrier, the file `ReadRec`, `StageRec` — **4**.
- LINK-GEN-5: the walk at `Dsc` + 3 laws, `FileReadInst.v`,
  `file_read_leaf_holds`.  Remains: `Hdsc_nl` is FALSE at the file →
  the line axis ("one law"), the carrier, `StageRec` — **3**.
- LINK-GEN-6: `ush_gets_done_at Dl`; the loop's three readings become
  `uline_ok` lemmas.  Remains: `Hws` (NEW), `Hchild_echo` (StageRec),
  `Hchild_redir`, `Hchild_cat`, the carrier, the deed steps — **6**, of
  which three are other lanes'.
- Last three of LINK-GEN's own residues: {line axis, carrier, StageRec}
  → {`Hws`, carrier, StageRec}.  **`StageRec` has been the residue of
  all six reports; the carrier of the last four.**  Each lane closed the
  wall it was briefed on and found the next literal one file lower
  (`UShPanic` → `UkShDiag` → `UkShEcho` → `UkSh.ush_read_ans` →
  `UkSh.wp_kshg_loop` → `UkSh.ush_gets_done` → `FileDisc.uline_ws`).

**CAT-GEOM (4 lanes, 16:16 → 20:44).**
- CAT-GEOM: `UShCat.v` (1,134 lines), the diagnostic at the cursor,
  `cat_image_entry`.  Remains: `cat_pay_at` at the claim (absent arm,
  present arm/publish, `Hw`, the taint's ledger), `Hchild_cat`'s free
  `M`/`av`, `catq_filed`'s measure — **6**.
- CAT-GEOM-2: both arms, the ledger on the taint disjunct, `Hw`, the
  node premises, and two residues nobody listed (`Hw` outright; the
  vacuous `kcat_dg_cr` premise deleted).  Remains: `cat_open_hand`
  (OFF-LINK), `cat_held_read` (OFF-LINK), `cat_taint_open` ("a real
  gap"), the exit cursor — **4**.
- CAT-GEOM-3: the exit cursor pinned, read(5)'s free law, `catq_cat`.
  Remains: `(⊢ Cend)` → `□ Cend` (another lane's files), the two
  OFF-LINK hypotheses, the lend's linear rows — **3**.
- CAT-GEOM-4: `□ Cend`, `cat_taint_open` discharged, `cat_lend`,
  `cat_child_of_entry`.  Remains: `cat_open_hand`, `cat_held_read` —
  **2**, both OFF-LINK-6's.
- **This chain converged**: 6 → 4 → 3 → 2, the residue is now entirely
  outside its files, and it did so because its files (`UCatKernel.v`,
  `UShCat.v`, `UCatOut.v`, `UkCatDeed.v`) were touched by nobody else.

### 1.4 Lines landed versus the estimate

- `git diff --stat 3327a0dc7..main -- iris | tail -1`: **137 files
  changed, +16,406 / −3,612**.  New files: 12, **7,351 lines**
  (`FileLinksLine` 2,081, `UShCat` 1,134, `LinkRec` 788, `UEchoFile` 558,
  `UShRound` 517, `UShLexRedir` 461, `StageRec` 410, `FileReadInst` 395,
  `UkShRedirBody` 349, `ReadRec` 275, `FileLinkInst` 239, `UInitFile`
  144); `FdPark.v` (622) deleted.  Largest diffs in existing files:
  `UCatKernel.v` +1,904, `UkSh.v` 809, `FsAbsWriteFire.v` 685,
  `UEchoOut.v` 599, `UShLine.v` 499, `UShEchoPay.v` 466,
  `ProofFilewriteChain.v` 432.
- Review 1 priced the program tier at ~9,500 lines as a twin (the echo
  tier is 10,252 lines today, `wc -l` over its eleven files), "a quarter
  with LINK-GEN".  What landed instead: **4,188 lines of link machinery
  and instance** (`LinkRec` + `StageRec` + `ReadRec` + `FileLinksLine` +
  `FileLinkInst` + `FileReadInst`) — LINK-GEN's own estimate for the
  residual twin was ~1,100 — plus **3,038 lines of cat** (`UCatKernel`'s
  growth + `UShCat`), plus **1,219 lines of skeleton STATEMENTS**
  (`Admitted`), plus **810 lines of redirect-line work** (`UShLexRedir`
  + `UkShRedirBody`).  Program-tier PROOF landed since review 1, in the
  sense of "a `Qed` that `file_Hinit_boot` will spend": the cat entry
  (`cat_child_of_entry`), `file_link_inst`, `file_read_leaf_holds`,
  `file_gets_holds` (modulo `Hws`), `ush_line_lexable_redir_holds` —
  roughly 5,000 lines.  Against the ~9,500 (or ~2,400 with LINK-GEN)
  estimate, the tree is at least half-way in LINES and at zero in
  DISCHARGED SKELETON PROOFS.

## 2. Why it is taking so long — the causes, ranked by measured cost

### 2.1 (Rank 1) Echo's assumptions are literals in kernel/shell STATEMENTS and were found one per lane

Eighteen since review 1 (§1.1's second table), of which the sh-tier ones
form a strict descending chain through `UkSh.v`: `UShPanic`'s `line_alts_of
… !!! a` and `a < 3` (LINK-GEN) → `UkShDiag.ush_execfail_law`'s
`alt_execfail`/`17` (LINK-GEN-2) → `UkShEcho.ush_execfail_law_wq` (LINK-GEN-3)
→ `UkSh.ush_read_ans`'s `disc_input` (LINK-GEN-3, closed by -4) →
`wp_kshg_loop`'s three readings (LINK-GEN-4, closed by -5) →
`ush_gets_done`'s `body_ok`/`line_ok` (LINK-GEN-5, closed by -6) →
`FileDisc.uline_ws LCat = []` (LINK-GEN-6, open).  Six lanes, ~50 minutes
each, to walk one file top to bottom.

**Could one sweep have found them?  Yes, and the tree contains the
proof.**  LINK-GEN-2 built `file_link_inst` by attempting to INHABIT the
record and got all three mis-typed fields from one compile.  SKELETON
found 21 of its 22 obligations in one compile.  What neither did was
attempt to instantiate the ECHO LEMMAS at the file's values: SKELETON's
hypotheses were stated AT ECHO'S NAMES (`Hchild_echo : sh_exec_sup_echo_wq
Wcf`, `Hwc` at `ush_mid`, `Hexecfail : ush_execfail_law_wq Wcf`), so the
literals INSIDE those names (`alt_execfail`, `rd_res`, `disc_input`) were
invisible to it.  A one-hour pass of the form

    Definition file_sh_entry := UShKernel.sh_image_entry_at <file arguments>.
    Definition file_init_sh  := UInitSh.init_sh_image_entry <file arguments>.

with every failing unification written down would have produced the whole
chain in one table: each `iApply`/`Definition` failure names the literal
it cannot unify (LINK-GEN-6's build note: "`iApply` against a
section-variable-indexed lemma reports the INSTANTIATED goal … reading the
two sides of that message is the fastest way to find the next statement
to move").  Even cheaper and with no build: `grep -n "EchoDisc\.\|alt_execfail\|
cmd_echo\|line_alts_of\|disc_input\b\|ush_fd1p\|body_ok\|OffParked"` over
`UkSh.v`, `UkShEcho.v`, `UkShFork.v`, `UkShDiag.v`, `UShLine.v`,
`UShKernel.v`, `UInitSh.v`, `UInitKernel.v` lists every site in seconds
(it was not run; §3.6's three checks are mask, persistence and home — none
of them is "does this statement name echo").  The remaining literals on
`main` that such a grep finds today: `UkShEcho.v:461/:539/:831`
(`ush_fd1p`), `UkShEcho.ushf_child_law_holds` (`ush_execfail_law_wq`),
`FileDisc.uline_ws LCat`, `FileInvDefs.v:564` (`m = OffParked`), and the
`OffParked` literals in `FileOpen.v` / `ProofSysOpen*.v` that OFF-LINK-5
named.

### 2.2 (Rank 2) Lanes stop at "a full deliverable" and hand the last step to nobody

§3.6 says lanes are "sized so that a refuted ruling wastes one file, not a
sweep".  It was followed — and it produced the opposite failure.  Nine
hypotheses on `main` have a discharging lemma nobody applied (§1.1),
because each lane's brief ended at its own file: SH-LEX-REDIR proved
obligation 13 and wrote "this lane deliberately did not make [the
deletion], since `UShRound` is SKELETON's file"; OFF-LINK landed
`wp_uk_ecall_write_std` "so `UEchoFile.v`'s `Hwrite1` is discharged
today" — the hypothesis is still there; LINK-GEN-2 landed `file_Hwbl`
… `file_Hwbr` and wrote a table of "what to apply" instead of applying
it; LINK-GEN-4 restated three hypotheses in `UShRound.v` and left every
proof `Admitted`.  The file-ownership convention meant the CONSUMER file
had no owner from 16:08 until now.  Meanwhile the same sizing rule made
the genuinely COUPLED changes un-landable: L2 was "written and reverted"
by OFF-LINK, again by OFF-LINK-2, re-walked by OFF-LINK-3, deferred by
OFF-LINK-4 and finally declared "one change with L4" by OFF-LINK-5 —
three lanes wrote the same 145-site patch and threw it away because the
partner edit was outside their brief.  SH-LEX-REDIR §4 says the same of
the redirect disjunct ("the premise, the disjunct in `UkSh.ush_rest_line`
and the three-way case are ONE coupled change with [the walk]. Adding any
part before the walk exists buys a premise no caller can discharge").

### 2.3 (Rank 3) Coordinator overhead and parallelism on a shared tree

Numbers: 45 merges / 147 commits; 22 "merge main into lane"; 7
fix-forwards; 25 conflict mentions; the worklist touched by 53 commits.
Concretely:
- SUP-ONE's rename (`riscv_kill_cred` → `app_taint`, 212 occurrences, 50
  files, 98 boxes dropped, eleven proof sites) landed at 16:23–17:50 while
  OFF-LINK, WRITE-RELAY-2, CAT-GEOM-2, LINK-GEN-2, LINK-GEN-3, SH-CHILD
  were open; every one of them merged it (`8abd25e8a`, `32ea6c6a2`,
  `9338fea2f`, `0b04eefe6`, `69333fe01`, `5ce67ba7f`).
- OFF-LINK-2's L6 (`ukn_held` deleted from `MkUkNames`, 15 files) landed
  at 18:27 and left `main` RED in `UEchoOut.v`, `UShEchoPay.v`,
  `UkShRedirBody.v` — fixed by LINK-GEN-5 (a different lane, 20:02) and
  independently by OFF-LINK-3's fix-forward (19:44).  WRITE-RELAY's
  arity change broke `UEchoFile.v`; it was repaired on `main`
  (`9cc716234`, `49c2fa35d`) AND by LINK-GEN-3 "independently … the merge
  took main's" — duplicated work.  SUP-ONE's `fdst_nopipe` export broke
  `UkFileOpen.v` at four sites; fixed by `ba34a9c5f` and again by
  LINK-GEN-3.
- LINK-GEN-6 merged `app-file/sh-redir` because its brief said "if
  SH-CHILD-2 has landed", it had not, and the lane lost about an hour to a
  wedged `UkSh.v`/`UShKernel.v` and a `ush_Dbody := 88` that came along.
- The VM: LINK-GEN-6 records a 30-minute `iIntros` wedge, CAT-GEOM-2 a
  30-minute/2.5 GB non-terminating `iApply`, SH-CHILD-2's `UkShEcho.v`
  "compiling for fifty-one minutes", an interrupted remote build leaving
  zero-length `.vo`s, and "never run two builds against the same remote
  tree".  `FileInvDefs.v` (OFF-LINK-6's file) sits under ~300 files; the
  moment it lands every open lane's next merge rebuilds the tree.

**Is the parallelism net positive?**  Split by file overlap.  CAT-GEOM
(disjoint files) converged in four lanes with two clean merges — positive.
LINK-GEN ×6, SH-CHILD, SH-LEX-REDIR and OFF-LINK-2 all edited `UkSh.v`
(809-line diff), `UkShFork.v`, `UkShEcho.v`, `UShRound.v` — every one of
those lanes paid a merge, three of them paid a fix-forward, and one
paid an hour's wedge.  Two serial lanes on the sh tier would have
produced the same six generalisations (each was ~30–50 minutes of proof
once the wall was named) with zero merges and, more importantly, with
ONE agent holding the whole `UkSh.v` chain in its head instead of six
agents each rediscovering the next literal.  The kernel side (OFF-LINK
1–5) was effectively serial already (one worktree, one branch) and its
cost was rulings, not merges.  Verdict: parallelism was net negative on
the sh tier and neutral elsewhere; six concurrent lanes on a tree with
two tree-wide renames in flight is the wrong number for this VM.

### 2.4 (Rank 4) Rulings refuted at the statement, since review 1

| ruling | made by | refuted by | cost |
|---|---|---|---|
| the disconnect lives in `UserOff.off_supply` (survey R2) | survey / brief | OFF-LINK's vacuity check (`vacuity_supply_not_taint`) | ~half a lane; the right shape (`off_link` in the box) landed in the same lane |
| `off_settle` as the supplier's output with the lend a bare half | OFF-LINK | WRITE-RELAY-2 / OFF-LINK-2 ("the two halves are one change") | one lane: `off_settle`/`_parked`/`_taint` landed 16:39, deleted 19:05 |
| the ANCHORED node: the half in the kernel's hands, `off = off0` relayed as a premise | OFF-LINK-3 (derivation), OFF-LINK-4 (landed) | OFF-LINK-5 ("the anchor is UNNECESSARY", `write_held_post` unstatable) | two lanes: 17 names landed 20:09–20:42 and deleted 21:19 |
| the generic supply IS the taint (survey R1) | survey | SUP-ONE (altitude + the tree's `True` kill) | ~half a lane |
| `LinkRec.lk_pan/lk_exf : nat` | LINK-GEN | LINK-GEN-2 (uninhabitable at `LCat`) | half a lane |
| `Hdsc_nl` at `EchoDisc.body_ok` | LINK-GEN-4/5 | LINK-GEN-5 itself (false at `disc_input_f`) | one lane (LINK-GEN-6) |
| `(⊢ Cend)` premises; "read(5) excluded by construction" | CAT-WALK / CAT-GEOM-2 | CAT-GEOM-3/4 | one lane |
| `Hchild_cat` with free `M`/`av` | SKELETON | CAT-GEOM | small |

About **five lane-equivalents of twenty-two** (≈ 25%).  Every one is the
class review 1 §A5 named: a mask, a persistence, or a resource HOME
(`write_held_post`'s existential `off0`; a half needed in two closures;
`image_entry`'s `□` over the key) checkable from the definition before
ruling.  §3.6 rule 1 was adopted and the anchored node still went through
two lanes — because the check was done by the lane AFTER, not before the
brief.  To its credit, the vacuity check (§3.6 rule 1's teeth) DID catch
R2 before it was built.

### 2.5 (Rank 5) Rate limits and the VM

Not measurable from `git`; the notes record the wedges above and the
build-race rule.  The observable symptom is lanes whose commit span is
five to ten minutes after an hour of wall clock (OFF-LINK-3, LINK-GEN-6),
which is consistent with builds and rate limits, not with proof
difficulty.  It is a multiplier on §2.3, not an independent cause.

## 3. What keeps cropping up — the recurring shapes, and whether §3.6 catches them

| shape | instances since review 1 | would §3.6's three checks (mask / persistence / home across fork-exec-wait) have caught it? |
|---|---|---|
| **a premise nobody can pay (vacuity)** | `cat_round_at`'s `□ kcat_dg_cr` (CAT-GEOM-2: "UNSATISFIABLE at a claim … vacuously true"); `(⊢ Cend)` (CAT-GEOM-3/4); `ushf_rest_of_body`'s three lexer premises "NEITHER PROOF READ THEM" (SH-CHILD); `Hlexr` dead; `off_settle_taint` (caught by the vacuity check) | only when the vacuity check is actually written; it was written once (OFF-LINK) and caught one.  A rule that would catch the rest: **every `□`/`⊢` premise of a round or entry lemma must be INHABITED at the claim in the same lane** (CAT-GEOM's `cat_pay_at_of_law` is the pattern) |
| **one resource wanted in two closures** | the offset half (node's closure vs kernel's hands — OFF-LINK-3/4/5, the whole anchor episode); the deed fraction across a child's walk (`cur_hold`, LINK-GEN-3); the ledger thrown away on the taint arm (`ustd_any`, CAT-GEOM-2) | the HOME check catches it if asked "who holds it at the fire / at exec / at wait", which OFF-LINK-3 asked and answered WRONG (it put it in the kernel).  The check is necessary, not sufficient; the decisive question is "which closure NEEDS to read it", and the review-1 §A1 answer (the node) was right the first time |
| **a fact at the wrong VIEW / mask / logic level** | `write_held_post`'s existential `off0` (OFF-LINK-5); `image_entry` `□` over the key so `Pay` must carry rows (CAT-GEOM-3/4); `sk_lend_stage` cannot conjure a linear `R` (LINK-GEN-3); the write reason names a `uptd` in the PRE (WRITE-RELAY shape iii, still unlanded) | yes for persistence (`□ (∀ W', …)` cannot hold a linear); the existential-witness one is a fourth check §3.6 lacks: **a post stated with a witness the caller named must bind that witness in the statement, not under an `∃` in the pre** |
| **an echo literal in a generic statement** | eighteen (§2.1) | **no** — §3.6 has no such check.  Add: before briefing any file-era lane, grep the tier for echo's names, and instantiate the tier's top lemma at the file's arguments as a `Definition` |
| **`Prop` where an Iris resource is needed, or vice versa** | `(⊢ Cend)` vs `□ Cend`; `Hcltaint : T -∗ Wcl` needing a `ghost_map` pin (LINK-GEN); `Hchild_cat` at every `M`/`av`; `cat_pay_at`'s path row as a PURE premise because `kcat_o_of_deed_miss` quantifies the image (CAT-GEOM-2, correctly) | the persistence check catches `Hcltaint`; the `⊢`/`□` one needs the rule above |
| **a change that cannot land in pieces (NEW, not in the prompt's list)** | L2+L4 (three lanes wrote and reverted L2); L3's lend + return ("the two halves are one change"); the redirect walk + `ush_rest_line`'s disjunct + the three-way case (SH-LEX-REDIR §4); `ush_execfail_law` → `_wq` → `ushf_child_law_holds` (three lanes for one carrier) | **no** — §3.6 rule 3 (one file per lane) is what CAUSED it.  Add: a lane's brief names the coupled set and lands it whole, or names it as blocked and does not touch it |

## 4. How to adjust — options, each evaluated against the tree

### Option 1 (RECOMMENDED): stop the sub-lane chains; one assembly lane per skeleton file, fixing residues INLINE

The evidence for it: the one chain that converged (CAT-GEOM) is the one
whose lane owned its consumer files and closed residues nobody had listed
(`cat_hw_of_link`, the vacuous premise) as it went.  The evidence
against the alternative: nine dischargeable hypotheses untouched for
seven hours.

What each assembly lane needs in hand TODAY, from `main`:

**ECHO-FILE (`iris/UEchoFile.v`, 6 `Admitted`, 2 hypotheses).**
- Statement changes it must make itself: `Hdep1`/`Hwrite1` become
  `Definition`s at `UkWriteFile.udepwf_std_write_file_held` and
  `wp_uk_ecall_write_std`, with the descriptor row at `OffHeld` (today
  the file binds `om` free; echo's fd 1 is held, so the statements
  should say so); `ef_node` restated at `FsAbsWriteFire.awrite_full_adv`
  (OFF-LINK-5's node) and `ef_chain` at `awrite_chain_adv`; `efq` keeps
  `uoff` (OFF-LINK-5 reversed OFF-LINK-4's "need not carry `uoff`").
- Kernel pieces present: `awrite_full_adv`/`awrite_part_adv`/
  `awrite_chain_adv` (`FsAbsWriteFire.v:839`), `udepwf_std_write_file_held`,
  `wp_uk_ecall_write_std`, `FileWrite.file_awrite_node` (at the PLAIN node
  — needs an `_adv` twin, ~60 lines; the three moves OFF-LINK-5 §3
  describes), `awrite_part_at_mapped_single`, `SysWriteDefs.wchunks_one`.
- Kernel piece MISSING: the `TB` guard (§0(6)).  Without it `ef_chain`
  must pay `awrite_chain_adv … P …` for every `P`; `ef_relay4`'s premises
  (`proc_pt_wf P`, `perm_of (ud_um P) sz = pmv`, `lazy_free`) are not
  available at an arbitrary `P`.  Either WRITE-RELAY-3 lands first (~150
  lines: `filewrite_in`'s two inode arms gain `∀ P, ⌜TB P⌝ -∗`, row 16
  of `UexecExecInst.xv6_sbundle` instantiates `TB` at `uvis_perm`/
  `uvis_sz`/`uvis_lazy`, six U-tier suppliers gain `iIntros (P) "%Htb"`,
  `ProofSyscall.sysc_dep_write` gains two premises) or the assembly lane
  does it inline.  This is new to the plan and must be owned.
- Price: 600–900 lines by `UEchoOut.echo_uexec_slot_at`'s mould (902
  lines), one lane.  Risk: the `∀ P`; and `efile_image_entry` needs the
  hand-mode row to exist in the exec'ing table, which is a PURE premise
  here (SKELETON finding 6) so it does not wait for OFF-LINK-6.

**SH-ROUND (`iris/UShRound.v`, 5 `Admitted`, 13 hypotheses).**
- Nine hypotheses become `Definition`s today (§1.1: 6–10, 13, 15, 16 and
  11 from `Hcons`/`Htag`).  `Hlexr` is deleted.
- `Hchild_cat`: `UCatKernel.cat_child_of_entry` — one application; the
  lend's `cat_open_hand`/`cat_held_read` are supplied by OFF-LINK-6/L5's
  leaves (`UkFileOpen`'s `_hand` corollary and `wp_uk_read_deed_learns_held`,
  ~100 lines once the leaves exist).
- `Hchild_echo`: the file `StageRec` — `file_stage_inst` does not exist.
  LINK-GEN-3 §5 prices every field against names that ARE on `main`
  (`FileLinksLine.fcur`, `wr_blk_t_f`, `blkcs_f`, `fwc_lend`,
  `file_write_link_blk`); ~300–400 lines, the one real proof being
  `ck_step` (whose file twin is `UCatOut` section 1) and the one model
  fact `fab I 0 = line_alts_of (last_ws I) !!! 0` (pure).
- `Hchild_redir`: `UkShRedirBody.sh_redir_child_law` is stated; the walk
  needs SH-CHILD-2's three items (seam exit payment as `Cr`+`Hcq`, `Fd1`
  parameter on `wp_kshr_exec_echo`/`sh_exec_sup_echo`, `echo_argv_bytes`
  at the NUL cut) + `Hopen_hand` + `efile_image_entry`.  ~400–600 lines.
- `Hcat_body` (`UkShRedirBody.v:271`): the 'c' branch from 0x97a through
  the `cd` compare (`UkShCd.v` still exists and walks `cd`; the `cat`
  line fails its three-byte compare and rejoins fork1) — a short walk,
  ~150–300 lines, new to the plan since SH-CHILD.
- `Hws`: set `FileDisc.uline_ws LCat := wl_words cmd_cat_f` (LINK-GEN-6's
  option 1; no consumer reads `LCat`'s value) — one line plus re-checking
  `FileDisc`'s four `uline_ws` lemmas and FILE-DEC.
- `ushf_child_law_holds`'s constant carrier — one statement in
  `UkShEcho.v` (LINK-GEN-4 residue 2).
- The round's own steps: `sh_prompt_alt_of_deed` (the deed decides the
  alternative — `cat_tie` + `file_write_link_blk`), `sh_hold`'s
  re-establishment after each child (the model's `fst_after`/`sessf` step
  meeting `cat_tie` — the ONE genuinely new piece of mathematics in this
  file), `sh_child_law_file`'s pure three-way case, `sh_kill_law_file`,
  `sh_tag_law_file` + the `disc_f`/^D pure lemma, and
  `sh_round_holds_file` through `UShRest.sh_rest_holds_at` +
  `UkShRedirBody.ushf_rest_of_body_file`.  ~800–1,200 lines.
- Price: 1,800–2,800 lines, two lanes if serial (StageRec + children
  first, the round second).  Risk: `Hcat_body`'s walk and the deed
  re-establishment are the only two things that are not instantiation.

**INIT-FILE (`iris/UInitFile.v`, 1 `Admitted`) — running.**  The
six-step recipe in the file header is right and can be executed NOW
against the `Admitted` `sh_round_holds_file` (that is what the skeleton
was for).  Needs `UInitKernel.init_boot_pay` with the deed in `Pay`
(item 22; `file_boot`'s `fown r s` beside `fturn`), the banner through
`FileLinks.file_write_link_first`, `sh_tag_law_file` via
`UkSh.ush_tag_law_of_at`, and `UInitSh.init_sh_image_entry` instantiated.
~400–800 lines, one lane.  Risk: low; every step has an echo twin
(`UInitBoot.echo_Hinit_boot`).

### Option 2: a "file-instance sweep" lane

Worth doing, but as the FIRST HOUR of the SH-ROUND assembly lane, not as a
lane of its own: attempt `Definition`s of `UShKernel.sh_image_entry_at`,
`UInitSh.init_sh_image_entry` and `UkShFork.ushf_child_law_at` at the
file's arguments, plus the grep of §2.1, and write the table before
proving anything.  Expected yield today: the five literals §2.1 lists as
still on `main` and probably one or two more in `UkShFork.v`/`UkShRun.v`
(the exec arm's supply shape).  Cost ~one hour; it replaces the next
three "one layer lower" sub-lanes.

### Option 3: drop the `LEcho` line from the file era

With LINK-GEN landed, `Hchild_echo` costs the file `StageRec` (~300–400
lines) plus the `fab` fact — not the ~1,250-line twin review 1 priced
without LINK-GEN.  Dropping `LEcho` would also change the MODEL
(`FileDisc.uline`, `disc_input_f`, `cont`, `ralt_ok`'s `REcho` row,
`cont_fpan`), re-open FILE-DEC's decidability and STAGE-2's `file_phi`,
and weaken the theorem (a plain `echo` line would taint the era, so the
theorem would say nothing about a session that mixes the two).  Saves
one short lane, costs a model lane and a weaker statement.  **Do not
take it.**  The same reasoning applies to every other cut review 1 §C3
priced; none has become cheaper.

### Option 4: serialise lanes and merge less often

Yes, with numbers: **at most two concurrent lanes touching `iris/`**
(one kernel: OFF-LINK-6 → L5 → TB; one program tier: the assembly lanes
in order ECHO-FILE → SH-ROUND → INIT-FILE, or INIT-FILE first since it is
independent), merge at lane END only, no `git merge main` mid-lane unless
the lane's own files moved on `main`, and **no tree-wide rename or field
deletion until `file_Hinit_boot` closes** (SUP-ONE's rename and
OFF-LINK-2's `ukn_held` deletion were each correct and each cost every
open lane a merge and three of them a fix-forward; the dead vocabulary
can be deleted in one cleanup lane at the end, as review 1 §D8 said).
The worklist conflicts go away if each lane writes its findings to its
own file under `claude-notes/projects/app-file/<lane>.md` and the
coordinator keeps a ten-line index; that is a notes-layout change, not a
process change, and it removes 22 merge conflicts.

### Option 5: what else the evidence supports

- **Make the progress metric the count of `Hypothesis` + `Admitted` in
  the three skeleton files** (today 15 + 12) and report it at every
  lane end.  Lines landed and "what remains" prose have not tracked
  progress; this number has.
- **Invert the ownership rule**: the assembly lane owns the skeleton
  file AND may edit any statement it needs to discharge a hypothesis;
  a kernel lane's exit criterion is a `Definition` in the skeleton file
  compiling, not a paragraph saying it would.
- **Kill the "one thing next" paragraph for good.**  Review 1 §D5 asked
  for it; §3.6 adopted it; every lane since still ended with "what
  remains" and the coordinator turned each into a sub-lane.  The
  dependency graph exists (§1.1's table); the lane report should update
  the TABLE, not append a list.
- **The vacuity check is the one §3.6 rule that demonstrably worked**
  (it refuted R2 before it was built, and it is one `Example` per
  ruling).  Require one per new `∨ app_taint` arm and per new `□`/`⊢`
  premise of a round or entry lemma, and require the inhabited witness
  (CAT-GEOM's `cat_pay_at_of_law`) for every new entry statement.

## 5. The critical path today, in order

From `main` at `d8ffd312c` plus the three running lanes.  "Assembly" =
instantiation of a landed shape with an echo twin to copy; "new" =
mathematics with no twin in the tree.

| # | item | owner | price | kind |
|---|---|---|---|---|
| 1 | L2+L4: `fpnames.fp_om`, `fdstate_ok` at `fp_om pn` (146 occurrences, 21 files), the publish minting hand/park (`ProofSysOpenPub` at `off_pub_hand_0`), `usys_fd_ok`'s open arm relaxed | OFF-LINK-6 (running, 11 files in the worktree) | ~1 lane; rebuilds ~300 files | assembly (mechanical sweep) |
| 2 | L5: `wp_uk_ecall_open_recv_img_hand`/`_dimg_hand`, `UkFileOpen`'s `_hand` deed corollaries (create for the redirect child, read for cat), `udepwf_st_read_file_held`, `wp_uk_read_deed_learns_held`; exit criterion: `UShRound.Hopen_hand` and `cat_open_hand`/`cat_held_read` compile as `Definition`s | OFF-LINK-6 or one more kernel lane, SERIAL after 1 | ~300 lines | assembly |
| 3 | WRITE-RELAY-3: the `TB : uptd -> Prop` guard on `filewrite_in`'s inode arms (both modes), row 16, six suppliers, `sysc_dep_write` | **UNOWNED** — assign to the kernel lane after 2, or to ECHO-FILE inline | ~150 lines, touches `SpecFilewrite` (cone) | assembly (shape (iii) is already designed) |
| 4 | ECHO-FILE assembly: `file_awrite_node_adv`, `ef_node`, `ef_chain`, `ef_w_of_deed`, `ef_pay_all`, `efile_uexec_slot_at`, `efile_image_entry`; `Hdep1`/`Hwrite1` as `Definition`s at `OffHeld` | one assembly lane, after 3 (the statements can start now) | 600–900 lines | assembly; the three moves inside `ef_node` (agree / advance / return) are the only new content and are ~30 lines |
| 5 | SH-CHILD-2: `Fd1` parameter on `wp_kshr_exec_echo`/`sh_exec_sup_echo`, the exec arm at `efile_image_entry`, the seam's `Cr`+`Hcq` exit payment, `echo_argv_bytes` at the NUL cut | SH-CHILD-2 (running; its tree is mid-merge and its last `UkShEcho.v` compile took 51 minutes) | 300–500 lines | assembly |
| 6 | `Hcat_body`: the `cat` line's walk from 0x97a through the `cd` compare into fork1 | SH-ROUND assembly (or SH-CHILD-2) | 150–300 lines | new-ish (a short walk with `UkShCd`'s compare as mould) |
| 7 | `Hws`: `FileDisc.uline_ws LCat := wl_words cmd_cat_f` + `FileDisc`'s four `uline_ws` lemmas re-checked | SH-ROUND assembly | ~20 lines | trivial |
| 8 | `file_stage_inst : StageRec file_link_inst` (LINK-GEN-3 §5's table) + `fab I 0 = line_alts_of (last_ws I) !!! 0` | SH-ROUND assembly | 300–400 lines | assembly (`UCatOut` §1 is the twin of `ck_step`); the `fab` fact is a pure lemma over twelve cases |
| 9 | `UkShEcho.ushf_child_law_holds` at `ush_execfail_law_wq_at dg nn` with `Lp -> dg I = alt_execfail` | SH-ROUND assembly | ~30 lines | trivial |
| 10 | SH-ROUND: nine `Definition`s (§1.1), `Hlexr` deleted, `Hchild_cat` by `cat_child_of_entry`, `Hchild_echo` by `sh_exec_sup_echo_wq_holds_at file_stage_inst`, `Hchild_redir` by `UkShRedirBody.sh_redir_child_law` + 5, `sh_child_law_file`, `sh_kill_law_file`, `sh_tag_law_file` (+ the `disc_f` ^D pure lemma), `sh_prompt_alt_of_deed`, `sh_hold`'s round trip, `sh_round_holds_file` via `UShRest.sh_rest_holds_at` + `ushf_rest_of_body_file` | SH-ROUND assembly (1–2 lanes) | 800–1,200 lines | mostly assembly; **new**: `sh_hold`'s re-establishment across a child (the model's `fst_after` step against `cat_tie`) and `sh_prompt_alt_of_deed` |
| 11 | INIT-FILE: `init_boot_pay` with the deed, the banner at `file_write_link_first`, `init_sh_image_entry` at the file families, `file_Hinit_boot` | INIT-FILE (running; can proceed against the `Admitted` round now) | 400–800 lines | assembly (`UInitBoot.echo_Hinit_boot` is the mould) |
| 12 | Close: `FileAssumptions.v` repointed at `file_adequacy_closed`, `make audit-file-only` at fourteen | coordinator | 10 lines | — |
| 13 | Cleanup: `OffParked` literals, `off_supply*`, `FileWrite.file_awrite_full_anchored`, `UkShLoop.ush_line_lexable*` (no consumer), the `_at`/echo-`Definition` doubles that are never read | one lane, LAST | — | — |

Total remaining: **~4,000–5,500 lines; 6–8 lanes if run as two serial
streams** (kernel: 1 → 2 → 3; program: 11 now, then 4, then 5–10 as one
or two assembly lanes).  Genuinely new mathematics on this path: the
three moves inside `ef_node` (small), `Hcat_body`'s walk (short), and
the deed's round trip in `sh_hold` (the one place the file model meets
the shell's loop; it is the theorem's content and it has never been
attempted).  Everything else is instantiation of a shape that exists on
`main` with an echo twin to copy.  Risks, in order: the `∀ P` in
`filewrite_in_held` (item 3, unowned — if it is not taken, ECHO-FILE
stops at `ef_chain` the way F-WRITE stopped at RELAY 4); a second
"one change" discovered inside L2+L4 while `FileInvDefs.v` rebuilds the
tree (OFF-LINK-5 measured 146 sites, three earlier lanes reverted it);
and the sh-tier files being edited by more than one lane at once again.

## 6. What review 1 got wrong, for calibration

- §C1.1's OFF-LINK shape ("the box's taint arm, `off_supply` deleted,
  the node advances") was right in outcome and wrong in one detail the
  survey then amplified: it did not say where the lend's taint arm goes,
  and the survey's R2 ("push the disconnect into `off_supply`") sent
  OFF-LINK down a refuted path for half a lane.  OFF-LINK's vacuity
  check, which review 1 §D1 asked for, is what caught it.
- §C1's lane count ("2 kernel + 1 console + 4 program ≈ 7 lanes") was off
  by a factor of three: 22 lanes ran and the program tier's proofs are
  still `Admitted`.  The undercount came from pricing LINK-GEN as one
  lane (it was six, because the literals were found one layer at a
  time) and OFF-LINK as one (five, because the half's home was ruled
  three ways).  This review's §5 count assumes the assembly-lane
  process; under the sub-lane process it would be wrong by the same
  factor again.
- §A4's "nothing at fork, dup, exec or the generic tier" held exactly
  (SKELETON finding 6, OFF-LINK-2's "the generic tier is told NOTHING
  about offsets any more").
- §B's TL-7 precedent (generalise, don't twin) held and was cheaper than
  the twin (4,188 lines of machinery+instance vs ~8,000 of twins), but
  the instance was twice LINK-GEN's own estimate (`FileLinksLine.v`
  2,081 vs ~1,100) — the pure algebra does not get cheaper for being a
  transcription.
