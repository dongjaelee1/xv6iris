# lane FORK-REFUND -- handover

LANDED on branch `lane/fork-refund` as **e58f284a2**, on top of origin/main
**174da0e13**.  NOT PUSHED.  Working tree clean.

## Gate (all green, base 174da0e13, build `fr6`)
COMPILED=663, zero `Error`, EXIT=0; VM `make -f CoqMakefile -n` pending=0;
`make audit-only … | md5sum` = **57f7327206c4b276d05035342fea8ecf** (unchanged);
`python3 tools/lemma_diff.py --ref origin/main` = 19 files CLEAN;
`run-on-gcp --check-dumps` clean.  No Admitted, no new assumption.

Builds: fr1 (dead -- the sync had dropped `kernel-rocq/*.vo`; rebuilt by hand),
fr2, fr3, fr4 (green at base 36d6c6d62), fr5 (green at 93cf3d36b),
fr6 (green at 174da0e13).  Rebased twice, both times by patch + `--3way`
(never `stash`/`reset`); three files overlapped upstream each time
(UConsOpen/UInitConsK/UShLine, then ProofSyscall/UexecExecInst/UkWriteLeaf)
and all merged cleanly.

## Design of record
`Rc` is a field of `sfam`: `UexecSG.sfork_lend`, for the reason `sfork_pay`'s
own header gives -- the lend goes DOWN on fork's deposit and BACK on its
failing arm, `uexec_ret_F_split` tears the two apart, and only `f` travels
with both.  So every relay keeps its ARITY (`ut_fork_in/out`,
`sysc_fork_in/out`, `uexec_arm_F`/`uexec_dep_F`/`uexec_ret_F`); only
`SpecSysFork`/`SpecKfork`, not family-indexed, take `Rc` explicitly.
`uexec_fork_child_F X W Q Rc := □(kill) ∗ Rc ∗ (∀ g' pidc, my_pay -∗ Rc -∗ X …)`
-- beside the continuation, so the kernel can refund without building a child.
kfork: refunds at ProofKforkMain `kfork_arm1` (allocproc, +0x10a) and
`kfork_arm2` (uvmcopy, +0x7c); spends at `kfork_arm3`; the capstone carries it
in the abstract `R` the prologue hands whichever closure runs.

## Left for the next lanes
- `wp_uk_ecall_fork_any` stays at `Rc := emp` (owner's ruling: the next
  program lane deletes the `_any` wrappers and moves sh onto the general leaf).
- `UkInitMain` drops the refund at its own statement's arm; IO-LEAF threads it
  out to init's failure print.
- The refund arrives only on an actual resume at `r = -1`: a killed parent's
  lend is covered by the taint arm of its payload, not by this row.
