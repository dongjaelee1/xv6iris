# IO-LEAF M1(f) handover (lane/io-leaf-fd, /shared/xv6iris-2-sup)

STATE: LANDED as `eab187afb` on `lane/io-leaf-fd`, over origin/main
`8367785f1`.  NOT pushed.  Working tree clean.  Build logs `fd1`, `fd2`
(next free `fd3`).  VM tree /mnt/rocq/trees/_shared_xv6iris-2-sup is green
at exactly this state.

GATE (fd2): COMPILED=19 EXIT=0, zero Error; `make -f CoqMakefile -n` 0
ROCQ compile; audit-only md5 57f7327206c4b276d05035342fea8ecf; lemma_diff
--ref origin/main = 4 GONE (all justified, below); no Admitted; no new
assumption; --check-dumps clean.  Cone: UInitFd UkInit UInitCons
UkInitPutc UConsLine UInitSh UConsOpen UkShEcho UShLine UkInitVprintf
UInitConsK UShConsK UShEcho UkInitPrintf UkInitMain UInitKernel
UInitBanner UInitBoot UInitBootAdequacy.

## The trusted diff
* `UInitFd.ufd_head T st γfd` : was
  `(∃ l, ustd γfd l ∗ ⌜l !! 0 = Some st⌝) ∨ ustd γfd ufd_l0 ∨ (ustd_any ∗ T)`;
  is `ufd_headL T γfd (ufd_l3 st)` where
  `ufd_headL T γfd l := ustd γfd l ∨ ustd γfd ufd_l0 ∨ (ustd_any γfd ∗ T)`.
  `ufd_head1 T st γfd := ufd_headL T γfd (ufd_l1 st)` is the PRE-DUP head.
* `UInitBanner.kinit_banner0_holds` : lost `(⊢ udepw_law 16) ->`; its
  conclusion is `∀ N, UkInitMain.kinit_banner0 N (FdOpen true true
  (FdDevice CONSOLE))`.
* `UkInit.kinit_banner_pay stc len f` : `ustd γfd (ufd_l3 stc) -∗ ...`
  (was `∀ l, ustd γfd l -∗ ...`).
* `UkInitMain.kinit_banner0 stc` / `kinit_round0 stc`; `wp_kinit_start`
  takes `kinit_banner0 stc`; `wp_kinit_main_from_1e` takes
  `ufd_head1 T stc γfd` (was `ufd_head`).
* `UInitKernel.init_boot_pay`'s 3rd conjunct: `∀ N', kinit_banner0 N' stc`.
* UNCHANGED: `UInitBoot.echo_Hinit_boot`, `UInitBootAdequacy`, `ufd_head_row`
  (so `UkSh.ush_fd0` / `UInitSh` / `UConsLine` are untouched).

## The 4 GONE, justified
`UInitFd.ufd_std_at`, `ufd_head_at`, `ufd_head_l1` -- all three existed only
for the EXISTENTIAL console arm; the arm is a named ledger now
(`ufd_head_l3` / `ufd_head1_l1` replace the constructors).
`UkInit.wp_kinit_dup_head` -> `wp_kinit_dup_headL`, which takes the ledger
and the slot its scan reaches and refutes the -1 arm from them.

## What is still owed
* `Hsh_owed`'s `sh_deps` conjunct STAYS: init's three die arms and
  `UkInit.init_deps` still spend `udepw_law 16` (M4/M6).
* Rounds k > 0 still print through the flagged deposit -- `kinit_round0`'s
  left disjunct is supplied only at `wp_kinit_start` and the Löb
  hypothesis re-enters with `iRight` (M6, needs M3's turn back).
* `ufd_head_row12` is proved and unused: the first consumer that wants
  sh's fds 1 and 2 (M2/M4) reads them off it.
