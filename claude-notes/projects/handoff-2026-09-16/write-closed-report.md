# lane WRITE-CLOSED -- report

Checkout /shared/xv6iris-2-sup, branch lane/write-closed on a43341d28.
Commit **0173644ed** "IO-LEAF WRITE-CLOSED: the write obligation at a closed
descriptor" (author = the checkout's config). Two files: NEW
iris/UkWriteClosed.v (283 lines) and one row (plus a comment) in
iris/_CoqProject. No existing iris/*.v touched. Not pushed. Nothing consumes
the new file yet.

## Result: NOT blocked -- the U tier reaches the closed-fd arm without a deposit

Terms. A *descriptor* is a slot number in a process's open-file table; the
program's own view of the low three slots (0, 1, 2 -- the standard streams)
is the *ledger* `UserFd.ustd (ukn_fd N) l`, a list of `fdstate`s of which
`FdClosed` means the slot is empty. A *deposit* (`UkRun.udepwf_std`) is the
separation-logic resource a user program hands the kernel at a system call so
that the kernel's contract for that call has its precondition; the *free write
law* `udepw_law 16` is a placeholder that mints such a deposit for `write`
(syscall 16) out of nothing and is the thing the audit wants gone. A *per-call
obligation* (`UkSh.ksh_w`, `UkInit.kinit_w1`) is what the program's proof
spends at a `write` site: "given the arguments and the run, the call completes
and the continuation is reached".

The kernel's write contract `SpecFilewrite.filewrite_in st n M ua Q`
(iris/SpecFilewrite.v:791-799) is a `match` on the descriptor's state `st`,
and its `_ => emp` arm covers `FdClosed`: a write to a closed descriptor
asks for NOTHING (sys_write's argfd fails before any file is touched; the
call returns -1 and prints nothing). Which arm applies is decided at the
syscall key by `SpecArgfd.fd_st_of_key v0 sts` (iris/SpecArgfd.v:184-188):
argument 0 read as a 32-bit signed int, looked up in the key's descriptor
table. The U-tier relay is `UkWriteLeaf.sbundle_at_write_intro_at`
(iris/UkWriteLeaf.v:178-193): `filewrite_in (fd_st_of_key a0 sts) ... -∗
sbundle_at uslot 16 f W`. So the deposit at a closed fd is `emp`, exactly
as the read side's `UShLine.ush_read_sup_closed` (iris/UShLine.v:427-446)
already exploits for `read`. No leaf row is missing.

## The lemmas (verbatim, iris/UkWriteClosed.v)

```coq
  Lemma ksh_w_of_closed (N : uk_names Σ) (fdw ua : mword 64) (nb : nat)
      (l : list fdstate) (i : nat) :
    bv_signed (trunc32 fdw) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some FdClosed ->
    ⊢ UkSh.ksh_w N fdw ua nb
        (UserFd.ustd (ukn_fd N) l) (UserFd.ustd (ukn_fd N) l).

  Lemma kinit_w1_of_closed (N : uk_names Σ) (fdw : mword 64) (b : bv 8)
      (l : list fdstate) (i : nat) :
    bv_signed (trunc32 fdw) = Z.of_nat i ->
    (i < NSTD)%nat ->
    l !! i = Some FdClosed ->
    ⊢ UkInit.kinit_w1 N fdw b
        (UserFd.ustd (ukn_fd N) l) (UserFd.ustd (ukn_fd N) l).
```

`bv_signed (trunc32 fdw) = Z.of_nat i` is the kernel's own reading of the
descriptor argument (argfd reads a 32-bit signed int), at the shape
`UkWriteLeaf.uwr_fd_st_dev` (iris/UkWriteLeaf.v:232-247) already uses; a
literal descriptor discharges it by `vm_compute; reflexivity`. Premises:
no deposit, no law, no credential -- only the ledger row.

Supporting lemmas in the same file: `uwr_fd_st_closed` (fd_st_of_key reads
FdClosed at a closed low slot), `uwrite_sup_closed` (`⊢ udepwf_std N m pc
16 (xfam_wr Q (ukn_pay N)) l` at ANY cursor family Q), `kwc_fam` (the
sfam-typed family, UInitBanner.kbn_fam's mould), and the two witnesses at
init's all-closed head ledger, which is where the audit needs them:

```coq
  Lemma ksh_w_of_closed_l0 (N : uk_names Σ) (ua : mword 64) (nb : nat) :
    ⊢ UkSh.ksh_w N (mword_of_int 2 : mword 64) ua nb
        (UserFd.ustd (ukn_fd N) ufd_l0) (UserFd.ustd (ukn_fd N) ufd_l0).
  Lemma kinit_w1_of_closed_l0 (N : uk_names Σ) (b : bv 8) :
    ⊢ UkInit.kinit_w1 N (mword_of_int 1 : mword 64) b
        (UserFd.ustd (ukn_fd N) ufd_l0) (UserFd.ustd (ukn_fd N) ufd_l0).
```

## Which arm each is proved from

* `ksh_w_of_closed`: `UkSh.wp_ksh_write_chain` (iris/UkSh.v:1121-1140,
  the three-instruction write stub on `UkRunSys.wp_uk_ecall_write_chain`,
  iris/UkRunSys.v:3854) with the deposit `uwrite_sup_closed`, which is
  `sbundle_at_write_intro_at` (iris/UkWriteLeaf.v:178) at
  `filewrite_in FdClosed ... = emp` (iris/SpecFilewrite.v:791-799, the
  `| _ => emp` arm), the descriptor state read by `fd_st_of_key`
  (iris/SpecArgfd.v:184). The post (`spost_at`) is thrown away: its closed
  arm `filewrite_extra` is `emp` too (iris/SpecFilewrite.v:815-823).
* `kinit_w1_of_closed`: `UkInit.wp_kinit_write_chain` (iris/UkInit.v:1378,
  on `UkRunSys.wp_uk_ecall_write_chain_buf`, iris/UkRunSys.v:3698) with the
  same deposit; the one byte goes in as a one-byte run and comes back.

## Placement

`_CoqProject` row right after `UkWriteLeaf.v` (line 2155 -> the new row at
2161): the file requires UkSh (row 1942), UkInit (row 359) AND UkWriteLeaf
(row 2155, where row 16's reading `xfam_wr`/`sbundle_at_write_intro_at`
lives), so the topologically correct row is after UkWriteLeaf, not merely
after UkSh. It sits below UInitBanner/UShOut/the application.

## Gate

* wc-1 (baseline at a43341d28): COMPILED=1059, EXIT=0.
* wc-2 (confirming): COMPILED=1 (UkWriteClosed.v), EXIT=0,
  `grep -c "^Error" /tmp/wc-2.log` = 0.
* VM `make -f CoqMakefile -n`: 0 lines `ROCQ compile`.
* local md5 of UkWriteClosed.v / _CoqProject == VM tree's
  (1809bea558d3577901f4f0b5e57fa10f / d631e041597dece575ace5950b31c075).
* `python3 tools/lemma_diff.py --ref a43341d28`: CLEAN (nothing dropped,
  nothing admitted, no new assumption).
* No Admitted, no `∨ True`, no `⌜P \/ True⌝` in the new file.
* `./gcp-rocq/run-on-gcp --check-dumps`: the VM's tracked dumps match.
* Audit md5 unchanged by construction (nothing consumes the file).
* rocq-warm: UkWriteClosed.v OK.

## What the consumers do next (not done here, by instruction)

At init's `ufd_l0` head arm (sh's fd 2 closed): replace `ksh_w_of_law ...
sh_deps` by `ksh_w_of_closed N (mword_of_int 2) ua nb l 2 ltac:(vm_compute;
reflexivity) ltac:(unfold NSTD; lia) H` (H : l !! 2 = Some FdClosed), and
`UkShDiag.ksh_w1_of_law` by the same through `ksh_w1`'s `∀ ua` (with
`ksh_w_frame`/`ksh_w_mono` to move `ubyte`/`Ci`). Init's banner at fd 1
closed: `kinit_w1_of_closed` + `kinit_w1_frame`. The two-arm entry rows
(`UkSh.ush_fd0`-style) then branch on the row and pay the console arm from
`UShOut.ksh_w_of_link_prompt` / `UInitBanner.kinit_w1_of_link` and the
closed arm from these.
