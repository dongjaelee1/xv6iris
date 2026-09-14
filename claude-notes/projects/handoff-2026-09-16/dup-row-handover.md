# DUP-ROW handover (lane/dup-row, /shared/xv6iris-2-sup)

STATE: LANDED on `lane/dup-row` as `18f1ab44e`, on top of origin/main
`7102d9de0` (IO-LEAF M1(e)).  Not pushed.  Working tree clean.
Gate green: dr4 COMPILED=131 EXIT=0 zero Error; `make -f CoqMakefile -n` 0
ROCQ compile; audit-only md5 57f7327206c4b276d05035342fea8ecf; lemma_diff
--ref origin/main CLEAN; no Admitted / no new assumption; --check-dumps clean.

## The row (UsysMemOk.usys_fd_ok, USYS_dup)
FAILURE arm gains:
    /\ ((forall fd st, usys_argfd tf = Z.of_nat fd -> sts !! fd = Some st
                       -> st = FdClosed)
        \/ fd_lowest_closed sts = None)
SUCCESS arm gains:
    sts !! Z.to_nat (usys_argfd tf) <> Some FdClosed
Exhaustive: argfd rejects only out-of-range / null slot, fdalloc only a full
scan, argint is void, filedup cannot fail.

## Files (6)
UsysMemOk.v (row + usys_fd_ok_length), ProofSyscall.v (sysc_dup_priv proves
all three), UkRunSys.v (ufd_auth_move + three dup leaves; wp_uk_ecall_dup's
-1 arm carries `fd_lowest_closed l = None`; wp_uk_ecall_dup_closed NAMES -1),
UkInit.v (wp_kinit_dup_cons / wp_kinit_dup_closed relay), UInitFd.v +
UInitCons.v (notes refreshed; no statement change).
SpecSysDup.v UNCHANGED -- the kernel post always had both reasons.
Untouched: UkInitMain.v, UInitBoot.v, UInitKernel.v, UInitBanner.v,
EchoLinks.v, UkEcho/UShEcho/UEchoKernel, claude-notes/, main.

## WHAT IO-LEAF MUST DO TO PIN FDS 1 AND 2
`UInitFd.ufd_head` is entered at `ufd_l1` BEFORE the dups
(`UkInitMain.v` open site, `ufd_head_l1`) and the two dups are walked in
`UkInitMain.wp_kinit_main_from_1e`.  So:
1. carry the NAMED ledger on the console arm from the second open through
   both dups instead of weakening to `ufd_head` at the open
   (`UkInit.uki_open2_of_console` also weakens there);
2. use `UkInit.wp_kinit_dup_cons` at `ufd_l1 init_cons_fd` then
   `ufd_l2 init_cons_fd`.  Its -1 arm now carries `fd_lowest_closed l = None`,
   and `UInitFd.ufd_scan1` / `ufd_scan2` (= `init_cons_scan1` / `2`) give
   `Some 1` / `Some 2` by `reflexivity`, so the arm dies by `congruence`;
   `init_cons_alloc1` / `init_cons_alloc2` then give fd = 1, fd = 2 and the
   exit ledger `init_cons_l3`, whose rows 0, 1, 2 are all `init_cons_fd`;
3. give `ufd_head` a console arm at `ufd_l3` (or a second, sharper head) for
   `UInitSh` / `UConsLine` to read fds 1 and 2 off.
Nothing further is needed from the kernel: the row and both U-tier leaves are
in place.
