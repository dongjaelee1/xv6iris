# TXT-ROW handover (lane/txt-row, /shared/xv6iris-2-sup)

STATE: LANDED as `a103f2e15`, on top of origin/main `ee1dbb690`
(claude-notes: TXT-ROW and IO-LEAF M3 launched).  NOT pushed.  Working
tree clean.  VM tree `/mnt/rocq/trees/_shared_xv6iris-2-sup`.  Build logs
`tx1`..`tx4`; **next free `tx5`.**

GATE (tx3 COMPILED=81 EXIT=0 zero Error; tx4 confirming COMPILED=0
EXIT=0): `make -f CoqMakefile -n` 0 ROCQ compile; audit-only md5
57f7327206c4b276d05035342fea8ecf (unchanged -- no new assumption);
lemma_diff --ref origin/main = 3 GONE in UEchoOut, justified below;
no Admitted; `--check-dumps` clean.

## THE LEAF

`UkRunSys.wp_uk_ecall_write_chain_txt` -- `_buf` with the source run in
the TEXT half:

    ([∗ list] j ∈ seq 0 nb,
       UserHeap.utext (ukn_t N)
         (uint (m !!! Regidx (mword_of_int 11)) + Z.of_nat j)%Z (f j))

in the premise and handed back (persistent, so free).  Everything else
is `_buf` word for word: the three argument-word rows, `take NSTD
(uvis_fd W) = l`, `uvis_lazy W = false`, the `uva_rmapped` row at `j <
nb`, the post at the trapping key.  `_buf` and
`wp_uk_ecall_write_chain` are UNTOUCHED.

## THE READING

`UserHeap.lazy_free_ux_addr` (new, beside `lazy_free_uw_addr`): a page
the PROJECTION lists at all is a real user leaf -- `perm_leaf` tests U
and R only -- and under `lazy_free` the fill supplied nothing, so
`ux_addr (perm_of (ud_um P) sz) a -> uva_rmapped P a`.  Proved from
`UserPerm.perm_of_mapped_U` + `uva_rmapped_page`; no new dependency
(`pte_vu` is named qualified as `PtTree.pte_vu`, UserPtTree already
requires PtTree).

`UkRunSys.uheap_text_bytes` (new, beside `uheap_ubytes_run` /
`uheap_ubytes_w`): the text invariant read along a run, giving
`ux_addr pmv (a+j)` AND `0 <= a+j < 2^38` in one pass (the text half
states both at the same byte, unlike the data half's two lemmas).

## FILES (4)

* `UserHeap.v`  -- `lazy_free_ux_addr` added.
* `UkRunSys.v`  -- `uheap_text_bytes` + `wp_uk_ecall_write_chain_txt`.
* `UkEcho.v`    -- `wp_kecho_write_chain_txt`, the 0x352/0x354/0x358
  stub over the new leaf (copy of `wp_kecho_write_chain`).
* `UEchoOut.v`  -- `echo_wtxt_holds : echo_wtxt` (one `iApply`);
  `kecho_w_of_link_txt`, `kecho_pay_of_link` and `echo_uexec_slot_at`
  lose the `echo_wtxt ->` premise.  `perm_of_mapped`,
  `lazy_free_mapped`, `lazy_free_rmapped` REMOVED (lemma_diff's three
  GONE): the first was `UserPerm.perm_of_mapped_U` verbatim, the other
  two are now `UserHeap.lazy_free_ux_addr`; nothing in the tree
  referred to any of them but UEchoOut's own comments, which now point
  at the engine.  `echo_wtxt`'s Definition STAYS -- it is what
  `echo_wtxt_holds` is stated at and what the file's narrative names.

Untouched: UkSh*.v / UShLine.v / UShKernel.v / UInitSh.v (IO-LEAF M3),
UexecRet.v / UkStore.v / SpecUsertrap.v / UserChildren.v / ProofKwait.v
(TRAP-ROWS M2 part 2), EchoOut.v, EchoLinks.v, App.v, AppEcho.v,
claude-notes/, main.

## WHAT IS LEFT ON `echo_uexec_slot_at`

Two named premises, BOTH IO-LEAF M3's:
* `UEchoOut.echo_out_argv args` -- argc = 3 and argv[1..2] are the
  line's two tokens (sh's parser: `UShEcho.echo_argv_is` through
  `UkShEcho.echo_off`);
* `take NSTD (uvis_fd W) !! 1 = Some (FdOpen rb true (FdDevice CONSOLE))`
  -- echo's fd 1 is the console, carried by the exec channel off
  init's pinned table (M1(f) `UInitFd.ufd_l3_row1`).

Nothing is owed by the ENGINE any more for echo's output.
