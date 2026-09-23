# Review: the FILE application campaign (`echo … > f`, power cycle, `cat f`)

Independent review, 2026-09-17, of the tree at `main` (`da12f4845`, read
through `79d0e349e`) plus the three lanes in flight (`app-file/off-hand`
= OFF-HAND-7, `app-file/f-open` = F-OPEN-6, `app-file/cat-entry` =
CAT-ENTRY-2).  Every claim cites a file, a lemma or a notes section.
Nothing in `iris/` was edited.

## 0. The verdict, in six sentences

1. The theorem is stated and closed modulo one premise
   (`UFileBootAdequacy.file_prog_law`, `iris/UFileBootAdequacy.v:121`),
   and that premise — the verified program tier — has **zero lines
   landed** (no `UEchoFile.v`, `UShRound.v`, `UShCat.v` exist; `SH-ROUND`
   and `ECHO-FILE` are unstarted in `completed/app-file.md`).  It is, by
   the echo application's own size (`UInitBoot.v`+`UInitSh.v`+`UShLine.v`+
   `UShPanic.v`+`UShRest.v`+`UShEchoPay.v`+`UEchoOut.v`+`UInitBanner.v`+
   `UInitConsK.v`+`EchoLinks.v`+`EchoLinksLine.v` ≈ 9,500 lines), the
   LARGEST remaining item, and it has never been priced in the worklist.
2. Six of the seven OFF-HAND lanes built machinery that the sixth deleted
   (`completed/app-file.md`, OFF-HAND-6: "the exec crossing's all-parked
   row is DELETED on BOTH arms together with the whole
   `fdv_held_in`/`ukn_held` carrier"), and the seventh is building on a
   shape that still cannot pay echo's first write (§A1 below: F-WRITE's
   RELAY 2 is unaddressed by design §3 fact 4, and fact 4 makes it
   harder, not easier).
3. The root cause of the offset non-convergence is one abstraction
   choice made at RD-1/RA-1 and never revisited: putting the user half
   of the offset ghost somewhere the KERNEL has to account for it at
   every tier crossing.  The owner's `link ∨ taint` principle (design
   §3.5) dissolves every OFF-HAND wall — but only if applied fully
   (§2): the half goes to the program, the box gets a taint arm, and the
   whole state/bundle/advance/park/pin apparatus of OFF-HAND-6/7 becomes
   unnecessary.  The current design §3 grafts the principle onto fact 4
   and keeps all of that apparatus.
4. The deed-piece walls (F-OPEN 1–6) were the kernel spec's
   `∗`-separated piece shape meeting one linear deed; the escrow inside
   the claim (F-OPEN-5) is the right general answer and should have been
   the day-1 shape.  What remains there (the device residue, F-OPEN-6) is
   small and correctly scoped.
5. Three kernel obligations that echo's first write NEEDS are recorded in
   the findings and absent from the plan: F-WRITE's RELAY 2 (the anchored
   offset), RELAY 3 (the chunk's length) and RELAY 4 (the partial arm's
   reason — READ-RELAY: "the write side's RELAY 4 is still open").
   `FileWrite.file_awrite_node` (`iris/FileWrite.v:495`) takes all three
   as premises and nothing in the tree supplies them.
6. The process failure is structural, not per-lane: rulings were issued
   at the resource-shape level without a statement-level check (mask,
   persistence, where the resource lives across exec), lanes refuted them
   at the statement, and no top-down skeleton of the consumer
   (`UEchoFile`, `UShRound`) was ever compiled to discover what the
   kernel actually owes.  The "one thing the next lane needs first" chain
   is the shape of a missing global plan.

## A. Diagnosis: why this is not converging

### A1. The offset: a wrong resource home, six lanes, and a hole still open

**The chain of events, checked against the findings.**  RD-1 landed
`UserOff.uoff γo off := off_gv γo (1/2) off` (`iris/UserOff.v:78`) — the
user half of the offset ghost as a program resource — and found that
`FdSlots.foff_row` claims that half as a persistent per-row invariant
(`OffGv.off_user_inv`, `iris/OffGv.v:100`), so a handed-out half has no
row (design/user-read.md §2, "THE ONE THING THAT DID NOT LAND").  RA-1
answered by putting a MODE in the descriptor state (`FdSlots.offmode`,
`iris/FdSlots.v:177`) and pinning every live row parked in the file
invariant (`FileInvDefs.fdstate_ok`'s `m = OffParked`,
`iris/FileInvDefs.v:540`).  From there every later wall follows
mechanically: the generic tier must be told "all rows parked" (RA-1
finding 2, user-read.md §8.1); that fact has no U-tier carrier (RA-3
finding C); the pin is the only kernel supplier of it and relaxing the pin
deletes it (RA-2 wall 2, §8.4); the surrender bundle at fork/exec has no
payer (RA-2 wall 3).  The owner PARKED this route on 2026-09-17
(user-read.md §8: "park and relay… the resolution… is relayed upstream
rather than fought from outside").  OFF-HAND-1..5 then fought it from
outside the same day: a ghost counter (OFF-HAND, "THE ONE THING"), a bit
on the record (OFF-HAND-3, commit `97fa5150e`), a set on the record
(OFF-HAND-4, `22292e156`), the row on the exec wands (OFF-HAND-2), the
row as the builder's (OFF-HAND-5, `a957fd615`).  OFF-HAND-6 deleted all of
it (`a02d138d9`: "`urun_rows_held` and `urun_rows_parked` are DELETED;
`ukn_held` survives as DEAD DATA").  Four lanes' landings reverted by a
fifth is the campaign's clearest measurable non-convergence.

**Why they were all doomed, in one sentence the tree already contained:**
the kernel's fire cannot depend on who the caller is, and every shape that
put the user half anywhere the kernel must find it (a row invariant, a
surrender deposit, a bundle entry) forced the kernel to distinguish
callers it cannot distinguish (OFF-HAND-5 finding 1: "the kernel cannot
branch on the taint").  The pipe layer had already solved exactly this
problem with `link ∨ taint` (design/pipe.md, "The coupling, or the
taint"; `PipeQueue.pipe_wpay`, `iris/PipeQueue.v:293`), and nobody read it
across.

**Fact 4 (design §3, OFF-HAND-6) is not the resolution; it re-creates
the original wall one level down.**  The half now rides the descriptor
bundle (`FdSlots.foff_row (… OffHeld off) := uoff γo off`,
`iris/FdSlots.v:762`) and is spent by the kernel's supplier
(`FdPark.off_supply_of_st_at_eq`).  But the APPLICATION's chain node must
learn the fire's offset, and the only way a node can learn it is by
agreement: `FsAbsWriteFire.awrite_full_at` (`iris/FsAbsWriteFire.v:567`)
hands the node the kernel's half `off_gv γo (1/2) (Z.of_nat off)`, the
node returns it unmoved, and only afterwards does
`wrf_awrite_fire_gen` run the supplier (`iris/FsAbsWriteFire.v:717`,
the `iMod ("Hsup" with "Hg")` after phase 2).  So a node whose CLOSURE
holds `uoff γo off0` learns `off = off0` by `OffGv.off_gv_agree`
(`iris/OffGv.v:57`) with nothing owed by the kernel — F-WRITE's RELAY 2
for free.  Fact 4 takes that half OUT of the closure and into the
kernel's hands, so the node can learn nothing; RELAY 2 then needs a
premise slot in `awrite_full_at` that does not exist (F-WRITE finding 1:
"the pure `∀ … off = length bs0` is FALSE… the equation has to be
RELAYED… a clause on the HELD branch of `SpecFilewrite.filewrite_in`"),
and OFF-HAND-6 declared that branch unnecessary ("NO contract
mode-split").  Design §3's sentence "The fire's offset IS the row's value
(RELAY 1, free)" is true FOR THE KERNEL and does nothing for the node;
`FileWrite.file_awrite_full_anchored` (`iris/FileWrite.v:462`) still
carries `⌜off = off0⌝` as a premise nobody supplies.  OFF-HAND-7 will
discover this after H2+H3 land, at the first attempt to state
`UEchoFile`'s chain.

**Two more relays are open and off the plan.**  RELAY 3: `SysWriteDefs.
wri_pre` (`iris/SysWriteDefs.v:55`) bounds `length bs` only by `off +
length bs ≤ MAXFILE*BSIZE`, and `SpecCopyin.ubytes_at`
(`iris/SpecCopyin.v:166`) is a `∀` over `bs`'s own indices, so the node
cannot identify `bs` with `echo_chunks ws !!! j` (F-WRITE finding 2).
RELAY 4: `awrite_part_at` (`iris/FsAbsWriteFire.v:603`) commits `take r
bs` plus up to `BSIZE` unnamed bytes with no reason conjunct, and it is
one of the two arms the kernel may pick at EVERY node (`awrite_chain`'s
`∧`); `AppFile.f_typed` cannot be re-established there (F-WRITE finding
3), and READ-RELAY's closing paragraph says the write twin is still open.
`TreeMove.tree_awrite_chain` (`iris/TreeMove.v:384`) pays both arms only
because the tree claim does not care what bytes land.  Without RELAY 4
`UEchoFile` cannot supply a single chain node.  None of the three is on
the worklist, in flight, or in design §3.

### A2. The deed pieces (F-OPEN 1–6): the right mechanism arrived on the fifth lane

The claim's deed is one `ghost_var` half (`AppFile.fdeed`,
`iris/AppFile.v:235`); the kernel's create surface asks for FOUR
`∗`-separated pieces plus a truncate piece plus a lookup piece
(`SysOpenDefs.open_au_create_at`), each a `PieceFam.pf_at` with its own
refund.  One linear half can pay one mover; every other piece has to READ
the claim without it.  F-OPEN found the O_TRUNC piece unpayable (a second
mover); F-OPEN-2 keyed it to the create receipt and found the EXISTS arm
needed a fraction the parent leg had already consumed (findings 1–3);
F-OPEN-3 did the 190-site sweep and found the `s = None` refutation
needed the claim at the LOOKUP's view (P3); F-OPEN-4 found the
application-side escrow refuted by the mask
(`FileOpen.file_escrow_mask_blocked`, `iris/FileOpen.v:1598`); F-OPEN-5
landed the escrow INSIDE the claim (`AppFile.f_esc_live`,
`iris/AppFile.v:613`; `file_escrow_park` `:1325`) with a persistent
ledger tie because "the syscall's fold DROPS the lookup receipt on two
arms".  Five lanes to reach: **park the whole deed in the claim for the
duration of the syscall; every piece reads it freely; the mover takes it
with a one-shot.**  That is the general answer to "one deed, N pieces"
and it should have been the design of §2 from the start — F-OPEN-3's own
correction 1 ("the EXISTS disjunct needs NO deed fraction… the claim says
that at the lookup's view without any fraction") was the signal, two
lanes before it was acted on.  What remains (the device sub-arm on the
FRESH-paid permit, F-OPEN-5 S3) is a kernel-spec imprecision, small, and
F-OPEN-6 is the right lane for it.  Candidate (1) of the brief — a
coarser claim ("open+write+close is one atomic move") — is not available
without restating the kernel spec: the kernel fires pieces at distinct
instants and returns receipts per piece; the escrow is the cheapest way to
make N pieces read one resource, and it is landed.

### A3. Candidate (2): the file-specific derived spec exists; the generic spec's piece shapes are what the lanes trip on

`FileOpen.v` (2,099 lines), `UkFileOpen.v` (1,364), `FileDeltas.v`
(1,193), `FileWrite.v` (518) ARE the derived spec: one lemma per syscall
shape the campaign uses (`wp_uk_ecall_open_create_deed`
`iris/UkFileOpen.v:685`, `wp_uk_ecall_open_read_deed`,
`wp_uk_read_deed_learns_mapped`, `file_awrite_node`).  The lanes did not
trip on generality per se; they tripped on THREE defects of the generic
spec that recur in every application campaign: (i) a piece's permit does
not carry what the FIRE knows (F-OPEN-2: "TL-3K's cursor at the create
commit, this at the truncate, and §7.9(8)'s two at unlink" — the same fix
three times); (ii) receipts stated at a different VIEW from the fire
(F-OPEN-3 P3, F-OPEN-5 S3); (iii) a chain node with no premise slot for
facts the kernel holds at the fire (F-WRITE 1–3).  The tree campaign
(user-tree.md §7.5–§7.10, WALL A/B/C/D) hit (i) and (ii) first; the file
campaign hit them again.  A derived spec cannot fix a missing premise
slot in the generic node; only the generic statement can, and that is
where the remaining kernel work is (§C).

### A4. Candidates (3)/(4): HELD is needed in some form, but the needed form is tiny

**Parked cannot deliver the target, for cat before echo.**  At a parked
row the read reports an existential offset (`UkReadFile.
read_arms_file_learn`, `∃ off`, `iris/UkReadFile.v`), so cat's SECOND
read (its loop reads until 0) is at an unknown offset and could
re-deliver the content: `cat f` printing `hello world\nhello world\n` is
not refutable, and that is "other junk".  Strengthening `off_user_inv` to
publish the value is a per-`γo` invariant that would have to name the
inode's content across invariants — the mask problem of F-OPEN-4 in
another dress.  Reporting the offset (R-c) is a number with no tie to
the row (design §7).  So some resource must tie the offset to the
descriptor: HELD in the sense of RD-1 is necessary.

**But what echo and cat need of HELD is exactly RD-1's landed `uoff`
plus agreement inside the node — nothing at fork, dup, exec, or the
generic tier.**  The campaign never forks or dups a held row (the
redirect child opens AFTER the fork; echo and cat exit); the exec
crossing carries the process's linear resources in `Pay`
(`ExecEntry.image_entry_at`; `UShEchoPay`'s "THE LEND") exactly as the
deed crosses; the generic tier pays the taint.  Candidate (4)'s "treat
exec as parking and re-derive the offset from the deed" fails for the
same reason parked fails (the kernel's node has no slot), but it is
unnecessary: the fragment crosses exec for free.

### A5. Process: the evidence, lane by lane

- **Every OFF-HAND ruling was refuted at the statement by the next lane**:
  OFF-HAND (the brief's fork site "unnecessary", exec the only unpaid
  site), OFF-HAND-2 (D1 blocked, "one consumer to re-route does not
  exist"), OFF-HAND-3 (the ghost counter "REFUTED three ways"),
  OFF-HAND-4 (the taint arm "CANNOT take the surrender bundle"),
  OFF-HAND-5 (the deposit "VACUOUS at the verified arm", "the kernel
  cannot branch on the taint"), OFF-HAND-6 ("the contract mode-split is
  REFUTED as unnecessary", "`fpnames` needs NO `fp_om`").  F-OPEN-2..5
  likewise ("keying is necessary and NOT sufficient", "the exists
  disjunct needs no fraction", "refuted by the mask", "the tie had to be
  persistent").  Each refutation is a fact checkable by reading two or
  three definitions before ruling (a mask, a `Persistent` instance, a
  `□`, where a resource lives across `kexec`).  The designer ruled
  first and read second.
- **No top-down skeleton was ever compiled.**  `UCatKernel.cat_round_at`
  (`iris/UCatKernel.v`, CAT-WALK-2) shows what a skeleton buys: stating
  the round with an abstract `Hold : nat -> iProp` found the exact
  obligation the kernel owes and refuted two vacuous shapes BEFORE any
  kernel lane.  `UkShRedir.ush_open_call` (SH-REDIR) as an abstract call
  premise let the parser and the claim lanes run independently.  Nothing
  of the kind exists for `UEchoFile` or `UShRound`, which is why RELAY
  2–4 were found by F-WRITE bottom-up and then dropped.
- **The owner's park was overridden the same day** (user-read.md §8
  status vs. OFF-HAND's launch date), and the worklist's "Wave 1" still
  lists OFF-HAND as if the route were open.
- **Lanes were too big and briefed with the ruling's shape baked in.**
  OFF-HAND-2 touched sixteen files; OFF-HAND-3 moved thirty-plus
  statements in three commits; F-OPEN-3 swept ~190 sites.  When the
  ruling is wrong the sweep is wasted; when the lane's brief says "no new
  files" (CAT-ENTRY) the lane cannot take the shape the guiding principle
  demands and stops.
- **The largest item is unpriced.**  See §C: the program tier at the file
  claim is a twin of ~8,000 echo-specific lines unless the link family is
  generalised, and design §4 explicitly declined the generalisation
  ("A functor over a line model was considered and declined").

For calibration, what was done right: the pure model with a negative
witness (`FileDisc.demo_f_bad`); the theorem stated early and modulo one
named premise (ADEQUACY); the abstract call premise; the round law for
cat's loop; the escrow, once reached.

## 2. The owner's principle (`link ∨ taint`) applied to the file offset

### 2.1 Which walls are instances of "conjuring a precondition in the generic proof"

| wall | where | instance? | why |
|---|---|---|---|
| the all-parked row (class field / exec wands / taint arm) | RA-1 §8.1, OFF-HAND-2 `SpecKexec.exec_slot_pre`, OFF-HAND-3 `image_entry*` | **yes** | it exists only so the kernel's fire always finds a supplier (`off_supply_parked` needs `off_user_inv`); with `link ∨ taint` the fire needs no supplier when the payment is the taint |
| the surrender bundle / `uoff_surr_at` | RA-3, OFF-HAND-4 | **yes** | it exists to re-mint the row invariant before a copy; with no row invariant there is nothing to re-mint |
| the exec deposit spent kernel-side | OFF-HAND-5 | **yes** | same |
| OFF-HAND-5's guarded generic premise (`n = read ∨ write -> fdv_all_parked`) | `UexecSG.sbundle_of_supply_ne` (attempted, reverted) | **yes** | the generic supply pays the taint instead |
| the dup/fork park (H4) | OFF-HAND-6 finding 4, design §3 | **yes** | with the half in the program's hands the kernel copies rows freely (`foff_row := True`); a forked child without the fragment pays the taint |
| the open arm's `fdst_parked` conjunct | RA-3 landing (1), `UsysMemOk.usys_fd_ok` | **yes** | it carried successor-parkedness for the Löb; with no modes there is nothing to carry (it stays TRUE and harmless if left) |
| the reference-count pin `¬ parked -> q = 1` | OFF-HAND-6 finding 2 | **yes** | it exists to save `fdstate_ok_inj` at a mode-bearing state; with no mode the landed lemma stands |
| `usys_fd_ok`'s advancing read/write row (H3) | OFF-HAND-6 finding 3, OFF-HAND-7 | **yes** | it exists because the value was put in the STATE; in the fragment it is the program's |
| the escrow for the absent deed | F-OPEN-3..5 | **no** | that wall is "N `∗`-separated pieces, one linear deed"; the taint arm each piece already has (`file_taint c ∨ …`) was not the obstacle, the VIEW was; the escrow is the right answer and stays |
| the truncate permit's device residue | F-OPEN-5 S3, F-OPEN-6 | **no** | a kernel-spec disjunction that admits an unreachable pair (device ∧ FRESH-paid); not a generic-proof precondition; F-OPEN-6's kernel-side fix is right |

Eight of ten.  Design §7's list of "four refuted shapes" agrees on the
diagnosis but §3 keeps the machinery the diagnosis condemns (value in the
state, half in the bundle, `fdst_adv`, the count pin, the advancing row).

### 2.2 What the coupling should look like

**The two taints are one at this application.**  `riscv_kill_cred := ai_kill
riscvF_app_iface` (`iris/RiscvPtsto.v:632`); `App.al_programs`'s interface
equation `riscvF_app_iface = app_ifc A c` (`iris/App.v:371ff`) makes it
`app_kill app_file c = file_kill c = file_taint (fgn_cl c)`
(`iris/AppFileRec.v:95`) `= echo_taint c.1` (`iris/AppFile.v:159`, a
`mono_nat_lb`).  `App.al_kill : app_sup_raw ⊢ □ app_kill` (`iris/App.v:278`)
and `AppFile.file_sup_of_taint` / `file_taint_of_sup` (`iris/AppFile.v:967`,
`:974`) close the loop: kernel taint ⟺ file taint ⟺ `app_sup`.  So the
kernel invariant should key on `□ riscv_kill_cred` exactly as
`PipeQueue.pipe_taint_cred` does (`iris/PipeQueue.v:111`) and on nothing
application-shaped; at `app_triv` it is `True` (a generic application's
boxes may disconnect for free, which is right — that application claims
nothing about offsets), at `app_tree` it is `True` too (`app_iface_triv`,
user-tree.md §9.3(6)), at `app_echo`/`app_file` it is the taint the
generic tier already holds through `app_sup`.  The generic builders
ALREADY take it: `FsAbsInvFire.fsabs_filewrite_in : app_sup -∗ cons_licence
-∗ pipe_taint_cred -∗ |==> filewrite_in …` (`iris/FsAbsInvFire.v:359`) —
the inode arm just has to use the premise the pipe arm uses.

**The box.**  The kernel's half lives in the file object's off box,
`FileOffCell.off_resident γo k := ∃ v, a_foff k ↦₄ v ∗ ⌜off_wf v⌝ ∗ off_gv γo
(1/2) (bv_unsigned v)` (`iris/FileOffCell.v:106`).  The pipe shape is

    off_resident γo k := (∃ v, cell v ∗ ⌜off_wf v⌝ ∗ off_gv γo (1/2) v)
                       ∨ (∃ v, cell v ∗ ⌜off_wf v⌝ ∗ □ riscv_kill_cred)

(`PipeInvDefs.pipe_qres`, `iris/PipeInvDefs.v:688`, is the model).  The
cell is kept in both arms (the store `f->off += r` needs it); the ghost is
dropped in the taint arm, permanently.

**The link IS the node, and the node already has the shape.**
`awrite_full_at` / `awrite_part_at` / `aread_commit_at` take the kernel's
half in and give it back (`iris/FsAbsWriteFire.v:567`, `:603`;
`iris/FsAbsReadFire.v:249`).  Change phase 2 to give it back ADVANCED
(`off_gv γo (1/2) (Z.of_nat (off + length bs))`, resp. `off + d`): a node
whose closure holds `uoff γo off0` agrees (`off = off0`), updates both
halves (`UserOff.uoff_advance`, `iris/UserOff.v:113` is exactly this
step), keeps `uoff γo (off0 + d)` in its cursor and returns the kernel
half advanced.  `off_supply` (`iris/UserOff.v:130`) and both suppliers are
then deleted; the fire lemmas lose the `Hsup` argument.  The payment
becomes `link ∨ taint` at the arm: `filewrite_in`'s inode arm
(`iris/SpecFilewrite.v:789`) `awrite_chain … ∨ □ riscv_kill_cred`,
`fileread_in`'s (`iris/SpecFileread.v:929`) likewise; the posts
`write_arms_at` / `read_arms` become `fired ∨ (taint ∗ payment back)`
(`PipeQueue.pipe_wpost`'s shape).  The kernel's two fire sites
(`iris/ProofFilewrite.v:4947`, `iris/ProofFileread.v:2263`, both today
`foff_row_inode_of … as "#Hoinvw"`) case on the box's arm: coupled+link →
fire the node; taint or tainted box → move/keep the box in the taint arm,
hand the payment back.

**The mint.**  `ProofSysOpenPub.v:330` calls `off_pub_park`; it calls
`UserOff.off_pub_hand_0` (`iris/UserOff.v:210`) instead and the receipt
carries `uoff g 0` where it carries `off_user_inv g` today
(`iris/ProofSysOpenPub.v:315`).  The resource then rides the open's fd arm
to the U tier: `SpecSysOpen`'s three `open_arms_*_split`, `ProofSyscall`'s
arm 15, and `UkRunSys`'s open leaves' destructs — the same threading RA-3
did for `fdst_parked` in one lane (user-read.md §8.3 landing (1)).  A
generic program drops the fragment (affine); its later writes pay the
taint.

**The descriptor bundle carries nothing about offsets.**  `FdSlots.foff_row
:= True` at every state; `fd_frags` is persistent again;
`ProofSysDup`/`ProofKforkB3` copy rows as before OFF-HAND-6.  The `foff_row`
consumers outside `FdSlots`/`FdPark` are 21 files, most with 1–5 sites
(grep count in this review's session) — RA-1's 24-file sweep in size.

### 2.3 What survives of OFF-HAND-6/7

| piece | fate |
|---|---|
| `UserOff.uoff`, `uoff_advance`, `uoff_agree_k`, `off_pub_hand_0` (RD-1) | **survive; they are the core** |
| `FdSlots.offmode`, `OffHeld off`, `fdst_adv`, `om_adv` (OFF-HAND-6 H1) | unnecessary; `OffHeld` is minted nowhere (7 files mention it); leave `offmode` frozen at `OffParked` or delete in a cleanup |
| `foff_row` at held = the half (H1) | unnecessary; `foff_row := True` |
| `FdPark.v` (622 lines: the park, the surrender, `off_supply_of_st*`) | dead; delete |
| the reference-count pin on `file_pay_st` (H2) | unnecessary; `fdstate_ok_inj` stands as landed |
| `fdstate_ok`'s `m = OffParked` pin | harmless and TRUE (nothing mints `OffHeld`); leave, so `FileInvDefs.v`'s ~300-file cone does not rebuild for this |
| `usys_fd_ok`'s advancing read/write row, `sysc_fd_ok`/`ut_fd_ecall` relays, `sys_read_out`/`sys_write_out` returning the row, the Löb absorbing a changing table, `file_ref` retyped (H3, OFF-HAND-7's brief) | **unnecessary in full** — the table does not change at read/write |
| the kernel-side dup/fork park (H4) | unnecessary |
| the hand-mode open leaf (H5) | replaced by "every open hands the fragment"; the U-tier leaf gains one conjunct |
| `fdv_all_parked` rows on `InitBoot.init_boot_bundle` / `SystemAdequacy.init_boot_of_sup`, `UkRun.ukn_held`, `urun_parked_row := True` | dead data; delete in a cleanup |
| the deleted exec row (OFF-HAND-6 H3) | stays deleted |

OFF-HAND-7 should be stopped and re-briefed (§D).

### 2.4 The deed pieces and the escrow under the principle

Unchanged.  Each create/lookup/truncate piece already has the form
`… ∨ file_taint c` (`FileOpen.file_trunc_recv` two arms; `file_dlk_recv`'s
`(⌜f_ok av s⌝ ∨ esc_spent g) ∨ file_taint c`; the wrapper's fd arm
`fown r (Some (i, [])) ∨ file_taint c`), i.e. the deed pieces already
follow `link ∨ taint`; their difficulty was the view, and the escrow is
the fix.  The device residue is a spec precision fix (F-OPEN-6).  Nothing
to change.

## B. What the tree campaign did differently, and what is reusable

**The tree campaign converged to a theorem whose conclusion is `True`.**
`UTreeAdequacy.tree_adequacy_treeΣ` pays `Hinit_boot` in three lines by
minting the taint out of the era's licence and taking the generic bundle
(user-tree.md §9.3(2)); its `app_phi` is `True` and "no verified `/init`
would change that" (§9.3(3)); the ADEQUACY lane records that this
discharge "is not available here… a boot-time taint makes the theorem say
only 'the user never kept the discipline'".  So the convergence is not a
process success to copy: it is what a claim with no trace content can
do.  The tree's OWN program-tier campaign (TL-5..8, four lanes) did not
converge either: after TL-8, D4 is still open on the licence count and a
deed-indexed boot-bundle twin (§9.7(4)/(5)).  What TL-3P..TL-3R did that
worked was to name each wall as a kernel-spec shape and fix the shape once
(the cursor on the walk, TL-3K; the rooted view, TL-3R); what F-OPEN did
was the same, three lanes later than it could have (§A2).

**What is genuinely reusable and was (or should be) reused:**
- `TreeMove`'s two-phase move and `tree_claim_read` mould — reused
  (`FileWrite.file_awrite_phases`, `FileOpen.file_claim_read`).
- `UkTreeCreate`'s create-family bundles from one deed at a length-zero
  prefix — reused (`FileOpen.file_open_create_au`).
- TL-7's generalisation of `UInitCons` off `echo_names` (`Pure`/`Made`
  parameters, echo's instance definitional, user-tree.md §9.6(1)) — the
  file application's `/init` can take echo's instance verbatim through
  `AppFile.file_pred_cons` (`iris/AppFile.v:674`), since the file claim's
  console projections ARE echo's.  This is the precedent for §D's
  recommendation 3 (generalise the LINKS the same way).
- The lesson of §9.1 (`tree_bump_free_is_vacuous`): a resource mintable
  from the claim alone is free — the file escrow's token is allocated by
  the holder (`AppFile.file_escrow_park`), so it is safe; worth a one-line
  vacuity check in `AppFile.v`.
- NOT reusable: the tree's console dance at the deed (`UInitTreeCons`),
  because the file claim keeps echo's console claim; the tree's entries
  (`UInitTreeExec`) because sh runs on the generic slot there.

## C. The shortest credible path to `al_programs`

### C1. The critical path, ordered

1. **OFF-LINK (kernel, one lane, replaces OFF-HAND-7's H2–H5).**
   §2.2 verbatim: the box's taint arm (`FileOffCell`), the node advances
   (`FsAbsWriteFire`/`FsAbsReadFire` three nodes + three fire lemmas),
   `filewrite_in`/`fileread_in` at `link ∨ taint` with posts `fired ∨
   taint` (`SpecFilewrite`, `SpecFileread` + their `Proof*` fire sites),
   the publish hands the fragment (`ProofSysOpenPub`), the fragment rides
   the open arm to the U tier (`SpecSysOpen` splits, `ProofSyscall` arm 15,
   `UkRunSys` open leaves), `foff_row := True`, `FdPark.v` deleted.  In the
   SAME node sweep: RELAY 3 (`⌜length bs = chunk_len n k⌝` on
   `awrite_full_at`, the chain carrying `n`).  Consumers of the node
   statements: 21 files mention them (`TreeMove`, `UkTreeRead`,
   `UkTreeWrite`, `FileWrite`, `FileOpen`, `UkWriteFile`, `UkReadFile`,
   `FsAbsInvFire`, `UexecExecMint`, `PinnedObs`…); at `app_tree` the taint
   is `True`, so `tree_awrite_chain` pays the box's taint arm for nothing.
2. **WRITE-RELAY (kernel, one lane; READ-RELAY's twin).**  RELAY 4: the
   partial arm carries `SpecCopyin`'s failing-address reason from
   `SpecWritei`'s `-1` through `ProofWritei` into `ProofFilewrite`'s
   partial fire and `awrite_part_at`; `UkRunSys.usrc_ok`'s mapped row
   refutes it in one lemma (`FsAbsReadFire.read_arms_mapped`'s twin).
   Independent of 1 except at `FsAbsWriteFire.v`; serialise on that file.
3. **LINK-GEN (U tier/console, one lane, parallel with 1–2).**
   Generalise `EchoLinks.echo_links` (`iris/EchoLinks.v:764`) and
   `EchoLinksLine.ewc_lcred` (`iris/EchoLinksLine.v:490`) over a link
   record {per-era pin resource, stream function, choice range}, with the
   echo instance definitional (TL-7's pattern), so that `UShLine`,
   `UShPanic`, `UShRest`, `UShEchoPay`, `UEchoOut`, `UInitBanner`,
   `UInitConsK` are INSTANTIATED at `FileLinks` instead of twinned.  The
   file instance is `FileLinks.file_write_link`'s extra `f0_lb vf s0 ∗
   file_era_pin g k vf` and `proc_stream_f`.  Without this, the program
   tier is ~8,000 lines of twins (the "echo-refs" counts in this session:
   `EchoLinks` 107, `EchoLinksLine` 219, `UShLine` 68, `UShPanic` 60,
   `UEchoOut` 42, `UInitBoot` 138, `UInitConsK` 56, `UInitBanner` 24).
4. **ECHO-FILE (`UEchoFile.v`, after 1–2).**  Per write `j` (four): the
   chain `awrite_chain … Q 0 (wchunks n)` at `Q k := file_wq` extended by
   `uoff γo (length content)`; each full node = `FileWrite.file_awrite_node`
   with RELAY 2 by agreement (closure `uoff`), RELAY 3 from the node's
   length premise, the append step `file_app_step_park` + `file_resync`
   (landed), `sel ++ [j]`; each partial node refuted by RELAY 4 at the
   mapped `usrc_ok` row; the `-1`/nothing-fired arm keeps `sel`.  The
   leaf: `UkWriteFile.wp_uk_ecall_write_file` is HANDLE-fixed
   (`NSTD ≤ fd`) and echo writes fd 1, a LEDGER slot — so one new
   ~20-line instance of `UkRunSys.wp_uk_ecall_write_at` at
   `udepwf_std` with `l !! 1 = Some (FdOpen false true (FdInode i γo _))`
   is needed (not listed anywhere).  The exit payload: `ushf_wq`'s twin
   carrying `fown r (Some (i, subseq … sel))` and the fragment dropped.
   Mould: `UEchoOut.echo_uexec_slot_at` (902 lines) with `kecho_pay_all`
   reused; estimate ~700–900 lines.
5. **CAT-ENTRY-2 (in flight; finish at the fragment).**  `Hold p :=
   ufd γfd fd (FdOpen true wb (FdInode i γo _)) ∗ uoff γo p ∗ fdq r q (Some
   (i, bs))` — `UCatKernel.cat_round_at`'s `Hold` is abstract, so this is
   an instantiation; `UkCatDeed.kcat_r_of_deed_at`'s `⌜off = off0⌝` premise
   is discharged by agreement inside `FileOpen.file_read_piece`'s node.
   Then `cat_image_entry` as CAT-WALK-2 §"WHAT UCatKernel's ENTRY STILL
   NEEDS" lists (items 2–4).
6. **SH-ROUND (the shell, after 3–5).**  (a) the child dispatch on
   `parse_line` of the buffer: `UkShFork.ushf_child_law`'s twin at three
   shapes — echo (`UkShEcho.wp_kshm_child_echo_holds` at the file links),
   redirect (`UkShRedirSeam.wp_kshm_child_alloc_redir`, `iris/UkShRedirSeam.v:584`,
   with `ush_open_call` at `UkFileOpen.wp_uk_ecall_open_create_deed` and the
   fragment in `K ty`, then the exec arm at a `sh_exec_sup_echo`-shaped
   supply whose lend `Cr` carries the deed, the fragment and "slot 1 is
   `f`"), cat (`UShCat` = `UShEcho` at `FsCatPin`); (b) the deed through
   fork/wait: `UkShFork.ushf_wq` (`iris/UkShFork.v:284`) gains `fown r s'`;
   sh's per-round pure invariant `dst_content s = fst_upto …`
   (`UCatOut.cat_tie`'s shape) re-established at the prompt; (c) the
   prompt link: `FileLinks.file_write_link_blk` filing `RFRan sel` /
   `RCRan` at an empty content (CAT-ENTRY's ruling (b)), else the plain
   link; (d) `UkShLoop.ush_line_lexable_redir` threaded from
   `UkShFork.ushf_rest_of_body` (SH-MALLOC-3's last paragraph);
   (e) `UShRest.sh_rest_holds`'s twin (`iris/UShRest.v:134`) at the file
   families.  With LINK-GEN this is instantiation plus (a)–(c); without it
   it is also the twins.
7. **INIT-FILE (`file_prog_law`).**  `UInitBoot.echo_Hinit_boot`'s twin
   (`iris/UInitBoot.v:750`): `init_boot_pay` (`iris/UInitKernel.v:683`) at
   the file console record (echo's `cons_cred` through `file_pred_cons`,
   the banner at `file_write_link_first` filing `s0`), `Pay` gaining the
   deed from `file_boot`, `UInitSh.init_sh_image_entry` (already abstract
   in `T`, `Cr`, `Rsh`) with the deed in the lend to sh, then
   `file_adequacy_fileΣ` with `Hprog` instantiated.

Lane count: 2 kernel + 1 console + 4 program ≈ 7 lanes if the rulings
hold, versus the current plan where OFF-HAND-7 alone is "a lane, not a
step" (OFF-HAND-6 finding 3) and RELAY 2/3/4 are three more unplanned
lanes after it.

### C2. Dead weight to ignore

`FdPark.v`; `FdSlots.OffHeld`/`fdst_adv`/`foff_row`'s held arm;
`FileInvDefs.file_ref_parked_keep` and the `_parked` chain
(`fdstate_ok_parked` → … → `ProcInv.proc_priv_parked`, consumer-less since
OFF-HAND-5); `UkRun.ukn_held`/`urun_parked_row`; the `fdv_all_parked` pure
rows on `InitBoot.init_boot_bundle`, `SystemAdequacy.init_boot_of_sup`;
`OffGv.off_permit` and `off_user_inv` (once the mint changes);
`UserOff.off_supply*`/`off_pub_park`; `FileWrite.file_awrite_full_anchored`
(its three relay premises become one agreement and one node premise);
`FileOpen.file_open_create_au_notrunc`; `UkCatDeed.kcat_r_of_deed`'s
existential-offset form; `PinnedObs` §8 (F-OPEN-2 says §8a supersedes it).
`UkRunSys.wp_uk_ecall_dup*`/`UkFork.wp_uk_ecall_fork*`'s `ukn_held` premises
(unused since OFF-HAND-6).

### C3. Scope cuts, priced

- **Drop the plain `echo` line (`LEcho`) from `uline`.**  Saves the
  `UEchoOut`/`UShEchoPay` twins at the file stage (~1,250 lines without
  LINK-GEN, ~200 with) and one arm of the dispatch.  Costs: `FileDisc`'s
  `sessf_sess`/`disc_f_disc` compatibility becomes moot; the owner's
  scenario does not need it.  Worth taking only if LINK-GEN is declined.
- **Assume `f` absent at the first redirect / one redirect per history**:
  saves nothing now — the EXISTS arm is paid by the escrow (landed) and the
  kernel bundle demands the piece regardless.
- **Drop the power cycle from milestone 1**: saves nothing — STAGE-2,
  FILE-DEC and ADEQUACY already closed the durable side; the theorem's
  conclusion is per cycle.
- **A non-truncating shell**: not available (0x601 is in the binary) and
  no longer needed (F-OPEN-5).
- **Accept "f empty" more liberally**: no proof saving; the alternatives
  `RFExec`/`RFOpenM`/`RFSilent` already carry it.
- **Do NOT cut cat's second read**: the loop's round law
  (`UkCatCat.kcat_round`) makes it free, and the ordering it needs is the
  same fragment the first read needs.

## D. Recommendations, ranked

1. **Stop OFF-HAND-7 and re-brief it as OFF-LINK (§2.2, §C1.1).**
   Touches: `FileOffCell.off_resident`, `FsAbsWriteFire.awrite_full_at`/
   `awrite_part_at`/`wrf_*_fire_gen`, `FsAbsReadFire.aread_commit_at`/
   `arf_read_fire_gen`, `SpecFilewrite.filewrite_in`/`write_arms_at`,
   `SpecFileread.fileread_in`/`read_arms`, `ProofFilewrite.v:4947`,
   `ProofFileread.v:2263`, `ProofSysOpenPub.v:330`, `SpecSysOpen`'s three
   splits + `ProofSyscall` arm 15 + `UkRunSys` open leaves,
   `FdSlots.foff_row := True`, delete `FdPark.v`, `FsAbsInvFire.fsabs_*_in`
   pay `pipe_taint_cred` on the inode arm.  Why it reduces work: it deletes
   H2–H5 (an advancing `usys_fd_ok` row with 20 sites, the Löb, `file_ref`
   retyped, the count pin, the park, the hand-mode leaf) and closes RELAY 2
   by `off_gv_agree` inside the node, which no shape with the half outside
   the node's closure can do.  Vacuity check to write first (durable-notes,
   "Vacuity"): a scratch lemma that the taint arm of `off_resident` is
   reachable from `app_sup` at `app_file` and that a verified node at
   `uoff γo off0` is NOT payable from `app_sup` (else the coupled arm says
   nothing).
2. **Fold RELAY 3 into the same node sweep and brief WRITE-RELAY (RELAY 4)
   now, before ECHO-FILE.**  Touches `SysWriteDefs.wri_pre`/the chain's
   `n`, `awrite_part_at`, `SpecWritei`/`ProofWritei`, `ProofFilewrite`'s
   partial fire, one `write_arms_mapped` lemma.  Why: `UEchoFile` cannot
   supply a chain node without both; they were found by F-WRITE and dropped
   from the plan.
3. **Brief LINK-GEN before SH-ROUND; reverse design §4's "functor declined".**
   Touches `EchoLinks.v`, `EchoLinksLine.v` (a link record with echo's
   instance definitional, TL-7's pattern), and then `UShLine`/`UShPanic`/
   `UShRest`/`UShEchoPay`/`UEchoOut`/`UInitBanner`/`UInitConsK` become
   instantiable at `FileLinks`.  Why: the alternative is ~8,000 lines of
   twins, maintained twice; the echo audit stays at 14 because the instance
   is definitional (as `init_cons_laws` did in TL-7).  Also give `FileLinks`
   the `echo_links`-style bundle CAT-ENTRY asked for.
4. **Compile the consumer skeletons before any further kernel ruling.**
   `UEchoFile.v` and `UShRound.v` as statements with `Admitted` proofs,
   built on the VM, stating exactly what each write's node closure holds
   and what sh's fork lends/wait returns.  Why: every OFF-HAND/F-OPEN
   refutation was a statement-level fact; `UCatKernel.cat_round_at` is the
   proof this works (two vacuous shapes caught before a lane).  Make
   "compiles as a statement" the bar for a ruling.
5. **Restate the process rules in `completed/app-file.md`**: a lane's brief
   names the STATEMENTS it may move (as OFF-HAND-6 reported them) and is
   sized so a refuted ruling wastes at most one file's sweep; a ruling
   cites the definition (mask, persistence, home across `kexec`) it was
   checked against; the "one thing the next lane needs first" paragraph is
   replaced by a dependency graph maintained at the top of the worklist,
   with the program tier priced.  Record that the owner's 2026-09-17 park
   of R-a was overridden and why that was wrong.
6. **Keep F-OPEN-6 and CAT-ENTRY-2 running; adjust CAT-ENTRY-2's `Hold`
   instantiation to the fragment** (`uoff γo p` instead of `OffHeld p`
   + the bundle half).  One line in its brief.
7. **After ECHO-FILE compiles, add the ledger-slot write leaf**
   (`UkRunSys.wp_uk_ecall_write_at` at `udepwf_std` with slot 1 an inode;
   ~20 lines beside `UkWriteFile.wp_uk_ecall_write_file`).  Why: echo
   writes fd 1, and every landed inode write leaf is handle-fixed at
   `NSTD ≤ fd`.
8. **Cleanup lane, last**: delete the dead weight of §C2 so the next reader
   of `FdSlots`/`UkRun`/`InitBoot` does not inherit the refuted shapes as
   live vocabulary — durable-notes' "a fact about something that no longer
   exists is deleted".
