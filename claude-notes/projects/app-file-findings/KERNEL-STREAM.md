# KERNEL STREAM — findings

One serial lane (review 2 §4, design §3.7), branch `app-file/off-hand`.
Its exit criterion is measurable, so the metric leads.

## THE METRIC

`grep -c "Hypothesis\|Admitted" iris/UEchoFile.v`

| when | value | what moved |
|---|---|---|
| at the start (main `d8ffd312c`) | **9** | 2 `Hypothesis` + 6 `Admitted` + the file's own header line |
| after `75a610017` | **7** | `Hdep1` and `Hwrite1` are `Lemma`s closed by `exact` |

The six `Admitted`s are SKELETON's and untouched; `tools/lemma_diff.py`
reports them only as line-number drift.

## THE COMMITS

| commit | what |
|---|---|
| `94a649b1a` | **L2** — `FileInvDefs.fdstate_ok` reads `fp_om pn` |
| `abe94870d` | **L4** — the open publishes at its caller's mode; the handed half rides out |
| `75a610017` | `UEchoFile`'s `Hdep1`/`Hwrite1` discharged |

Whole tree green at each (`EXIT=0`, zero `Error`); all four audits
byte-identical throughout — **system THIRTEEN, echo FOURTEEN, tree
THIRTEEN, file FOURTEEN**; `lemma_diff` clean of anything this stream
dropped; `comment_quote_check` 0 sites; `Proof using` everywhere.

## 1. L2 — `fpnames.fp_om`, and why the mode is a PER-FILE constant

`fdstate_ok`'s FD_INODE arm pinned `m = OffParked`; it now pins `m = om`,
a parameter, instantiated by `file_pay_st` at `fp_om pn`.

**THE MODE BELONGS TO THE FILE, NOT THE DESCRIPTOR**, and that is forced:
`dup` and `fork` hand out a second descriptor on the SAME `struct file`,
hence on the same `f->off`, so two rows of one file cannot disagree about
who owns the offset. That is why the field is on `fpnames` and not on
`FdSlots.FdInode`.

Cost, measured: 145 occurrences across 15 files; `fdstate_ok_inode_names`
gained a third conjunct (the modes agree), which is what ties the carve's
row to the descriptor's in both file walks; `file_pay_st_ok`'s existential
gained `om`; `foff_row_of_ok`'s premise is now the ROW itself
(`foff_row` at the mode) instead of `off_user_inv`. `fdstate_ok_inj` and
`file_pay_st_agree` needed no content change — `fpay_tok_agree` gives
`pn1 = pn2`, hence `fp_om` agreement, for free.

Both file walks now TAKE the mode instead of knowing it:
`SpecFilewrite.filewrite_in_inode_om`/`_any` is the mode-keyed reading,
`ProofFilewriteChain.fw_au_st_init` turns the row plus that reading into
the loop's carrier at either mode, `ProofFilewrite`'s inode entry carries
the ROW and passes `omfx` to `fw_loop`, and `ProofFileread` gets `Hom`
(the mode agreement) beside `Hieq`/`Hgo` and fires at `om0`.

## 2. L4 — the publish chooses, and the choice is the CALLER'S FAMILY'S

**THE MODE IS A FIELD OF THE DEPOSIT FAMILY** (`UexecExecInst.xfam`'s
`of_om`, twelve literals, all `OffParked`), read by `ProofSyscall` and
threaded down. Which mode a program's opens install is a property of the
PROGRAM, not of the `open(2)` arguments, so it rides where the program's
other families ride. Every landed family says `OffParked`, which is what
keeps the tree and console applications byte-for-byte what they were.

`ProofSysOpenPub` is **the one place in the kernel that chooses**: at PARK
the second half of the shadow becomes the row's invariant
(`UserOff.off_pub_park`); at HAND it goes to the caller
(`off_pub_hand_0`), the row (`FdSlots.foff_row` at `OffHeld`) claims
nothing, and the half travels out on the success arm. There is exactly one
user half, which is why these are one lemma apart and not two independent
decisions.

New: `UserOff.foff_pub om γo` (`emp` at PARK, `uoff γo 0` at HAND) and
`foff_pub_t om t`, the same keyed on the descriptor TYPE — **a device row
has no offset shadow**, so the open walk's arm threads `foff_pub_t omo t`
rather than a `bool_decide` guard, and the two sides line up definitionally.

One new premise, and it is a fact about the C code: `bv_unsigned voff = 0`
(sys_open stores a zero `f->off`), threaded through `so_stores_au` and
`so_tail_pub_au` and discharged by computation at `ProofSysOpenAlloc`,
which already instantiates `voff` at `mword_of_int 0`.

**`usys_fd_ok`'s open row no longer pins `fdst_parked`.** The comment that
defended it — "without it this row LICENSES A GENERIC OPEN TO INSTALL A
HELD DESCRIPTOR, which is what stopped the guarded generic WP's Löb step"
— named a consumer (`usys_fd_ok_parked` and its kit) that lane OFF-LINK-2
had already deleted. Nothing in the tier reads all-parkedness off that
predicate today, so relaxing it cost three `destruct` patterns.

## 3. WHAT A HELD PROGRAM NOW OWES, END TO END

* `open` at `of_om := OffHeld` ⟶ the success arm carries `uoff γo 0`
  (`FileOpen.file_open_fd_K`, `UkFileOpen.redir_K`, both mode-keyed).
* `write` at that row ⟶ `SpecFilewrite.filewrite_in_held`'s link arm, the
  client-advanced chain, whose nodes keep the half in their own closure.
* `read` at that row ⟶ `FsAbsReadFire.aread_in_om OffHeld`, likewise.
* the kernel carries NOTHING: no `uoff` across a call, no supplier at a
  held fire, and both posts are the landed ones.

## 4. WHAT IS LEFT, AND WHO OWES IT

1. **The `_hand` deed corollaries.** `UkFileOpen`'s three deed opens are
   instantiated at `OffParked`; the `_hand` twins are the same terms at
   `OffHeld`, and they are what make `UCatKernel.cat_open_hand` and
   `UShRound.Hopen_hand` compile as `Definition`s. Nothing new is needed:
   the receipt already carries `foff_pub OffHeld γo = uoff γo 0`.
2. **`udepwf_st_read_file_held` / `wp_uk_read_deed_learns_held`** — the
   read side's twins of what item 1 does for the open; they close
   `cat_held_read`.
3. **WRITE-RELAY-3's `TB` guard** (review 2 §0(6)), still unowned by a
   landed statement: `filewrite_in_held`'s link arm is
   `∀ P : uptd, awrite_chain_adv … P …`, so echo must pay the partial node
   at EVERY page table and `ef_relay4` refutes it only at a table tied to
   the caller's own.
4. **ECHO-FILE's assembly** — the six `Admitted`s, `file_awrite_node_adv`,
   `efile_uexec_slot_at`, `efile_image_entry`.

## 5. TWO PROCESS FINDINGS, BOTH EXPENSIVE

* **A tree-wide `sed` that uses a sentinel character must not use one the
  tree already contains.** A placeholder pass over eight predicate names
  substituted a `§` and then expanded EVERY `§` in `iris/`, rewriting 3,327
  comment lines in 442 files into nonsense. It compiles, so no build
  catches it; only `grep` does. Recovered by rebuilding each file from
  `git show HEAD:` through a line-level `difflib` alignment that restored
  the `equal` blocks from HEAD and kept the intended edits. **Sentinel
  characters must be chosen by `grep -c` on the tree first.**
* **`--check-proof` is unusable for a whole subtree after touching a low
  file**, and reverting the edit does not help: the runner drops the stale
  artifacts of every changed `.v` and the revert does not put them back.
  Touch a low file only immediately before a whole-tree `--proofs -k`.
