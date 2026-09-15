# Lane RESIDUALS -- report (checkout /shared/xv6iris-2-disc, branch lane/residuals)

Base: origin/main 81107fe83 (code 7da574e81 = IO-LEAF step 4 (B)).  Never pushed.
No claude-notes edited.  `iris/_CoqProject` untouched (no file added).

## 0. Vocabulary (plain concurrent-separation-logic and xv6 terms)

* A RESOURCE is a proposition of Iris's separation logic a process can own,
  split (`∗`) or hand over; a WAND `P -∗ Q` consumes `P` and produces `Q`; a
  PERSISTENT resource (`□ P`) can be copied; an AFFINE ARM is a disjunct
  `∨ True` under which a resource may be thrown away.  A LAW is a persistent
  wand taken as a premise and discharged once at the top of the theorem.
* A CREDENTIAL is the linear resource a process must hold to put a byte on
  the console under the application's claim.  `Wc n p` -- the shell's WRITE
  credential at input boundary `n` with `p` prompt bytes out; `Wb n` -- the
  BANNER-OWED credential (what a closed prompt leaves; init's next banner is
  paid from it); `Wp n` -- the ROUND-OPEN credential init lends.  `Pm n` --
  the PIECES of the console lease the shell holds mid-line.  `T` -- the
  TAINT, the persistent fact that the era is off the discipline; a tainted
  walk pays everything.
* The FREE WRITE LAW `UkSh.sh_deps` (= `udepw_law 16`) is a placeholder that
  counts a `write(2)` as paid without a credential.  `Hsh_owed`'s first
  conjunct (`⊢ UkSh.sh_deps`) is the top theorem's admission of it.
* THE EXIT FAMILY `UkInit.init_rd Rdl Wb n := Rdl n ∗ init_rd_cred Wb n`,
  `init_rd_cred Wb n := Wb n ∨ True`: what the shell's exit payload hands
  init back per input count.  THE LEND `init_lend_cred stc Wp Wb l n` is the
  credential init lends its forked child, correlated with the ledger row.
* The FORK ANSWER: what the kernel's fork trap hands the parent -- either
  `r = -1` (fork failed, the lend refunded) or a child's pid `r = sign_extend'
  64 pidv` with the CHILD TOKEN `child_tok γ pidv Q` (the quarter of the
  child's generation a later `wait` redeems).  The EXEC SEAM: the kernel's
  `exec` contract's program-facing wand (`SpecKexec.exec_slot_pre`), which
  hands the program its own weakest precondition at the exec'd key `W'`.

## 1. Commits

* (A) `c0474175b` -- the fork answer carries the pid's range; the shell's and
  init's pid sub-arms at a negative return are REFUTED.
* (B) NOT DONE -- blocked at the exec seam (§3), as the brief instructed.
* (C) NOT DONE -- every arm it names is downstream of (B) (§4).
* (D) NOT DONE -- downstream of (C) (§4).

## 2. (A) THE PID SUB-ARM -- what was done

### 2.1 The brief's premise was wrong, and the fix

The brief said the pid-range row `⌜1 <= bv_unsigned pidv <= PIDMAX⌝` already
sits on `UkFork.wp_uk_ecall_fork`'s parent post.  It does not: the row
exists on the KERNEL's fork contract (`SpecKfork.v:279`, the pid arm of
kfork's post) and is in hand at the one trap-loop site that builds the
program-facing answer (`ProofSyscall.v:~5008`, hypothesis `Hpb`), but the
program-facing answer `UexecRet.ufork_ans` (UexecRet.v:983) dropped it, so
nothing above the trap loop could see it.  There is no other source: the
child token carries the pid but no range, and the kernel's contract text
(`SpecKfork`, `SpecSyscall`, `SpecUsertrap`) is untouched.  The change is ONE
pure row on `ufork_ans`, provable at its one construction site from the
kernel's existing post; every relay above is a pass-through (`UkFork`,
`UkShRun.wp_kshr_fork`, `wp_kshr_fork1(_tail/_any)`,
`UkShDiag.wp_kshr_fork1_final`, `UkInitMain.wp_kinit_fork`).  Cone: the 134
files above `UexecRet` (one full build, rs-1).

### 2.2 Every changed statement, verbatim

`UexecRet.ufork_ans` (NEW; was without the middle row):
```
  Definition ufork_ans (Q : Z -> iProp Σ) (Rc : iProp Σ) (r : mword 64)
      (cs cs' : gset gname) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64) /\ cs' = cs⌝ ∗ Rc)
     ∨ ∃ (γ : gname) (pidv : mword 32),
         ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
         ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
         ⌜cs' = cs ∪ {[γ]}⌝ ∗
         child_tok γ pidv Q)%I.
```
THE FORK ANSWER'S SHAPE, everywhere it is spelled in the program tier (the
parent post of `UkFork.wp_uk_ecall_fork` and `wp_uk_ecall_fork_argv`; the
parent and panic continuations of `UkShRun.wp_kshr_fork`, `wp_kshr_fork1`,
`UkShDiag.wp_kshr_fork1_final`; the panic continuation of
`UkShFork.wp_kshf_fork_core`; `UkInitMain.wp_kinit_fork`'s parent post),
the pid arm reads
```
         ∨ ∃ (γ : gname) (pidv : mword 32),
             ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
             ⌜(1 <= bv_unsigned pidv <= PIDMAX)%Z⌝ ∗
             child_tok γ pidv Q ∗
             UserChildren.uch (ukn_ch N) (Sc ∪ {[γ]}))
```
(the new pure row SECOND, so every pass-through pattern keeps working; the
`-1` arm unchanged).  No binder list changed; no name changed.

### 2.3 The refutations

* `UkShFork.wp_kshf_fork`, console arm, the fork answer's pid sub-arm at
  `sign_extend' 64 pidv = -1`: REFUTED by the new top-level lemma
  ```
  Lemma ushf_pid_sext_ne_m1 (pidv : mword 32) :
    1 <= bv_unsigned pidv <= PIDMAX ->
    (sign_extend' 64 pidv : mword 64) <> (mword_of_int (-1) : mword 64).
  ```
  (through `UmodeArith.sext32_small`/`uint_moi` and three closed `Z` lemmas
  `ushf_pid_lt_Z31`, `ushf_pid_Z64`, `ushf_pid_ne_m1`; the one `vm_compute`
  is on the closed literal `uint (mword_of_int (-1))`).  The sub-arm used to
  pay the panic on the FREE law (`ush_diag_leaf_holds` + the affine assembler
  `ush_at_of_pm`); both uses are gone from that arm.
* `UkInitMain.wp_kinit_main_loop`, fork-failed branch (the `blt a0,x0`
  TAKEN), the answer's pid disjunct: REFUTED (`sext32_small`, `moi_lt_s`, new
  `pid_ltb0 : 1 <= z <= PIDMAX -> Z.ltb z 0 = false` beside M6b's three `Z`
  lemmas).  It used to call `wp_kinit_main_die_df` on
  `init_lend_cred_triv` -- one of the two remaining PRODUCERS of
  `init_lend_cred`'s affine arm is gone (the other is `wp_kinit_banner`, §4).

### 2.4 Files

`iris/UexecRet.v`, `iris/ProofSyscall.v` (one `iSplitR`), `iris/UkFork.v`
(+`Require Import ProcGeom`), `iris/UkShRun.v`, `iris/UkShDiag.v`,
`iris/UkShFork.v` (+`ProcGeom`), `iris/UkInitMain.v`.

## 3. (B) THE EXEC-SEAM ROWS -- BLOCKED; exactly what is missing

Checked first, as the brief asked.  The seam does NOT carry the two rows:

* `SpecKexec.exec_slot_pre S Q Pfin Φo cw na alen afun sts`
  (iris/SpecKexec.v:799-826): both wands bind `W' : uvis` and pin ONLY
  `⌜kexec_image_ok f na alen afun sts W'⌝` (resp. `⌜exec_key_ok na alen sts
  W'⌝`), `⌜uvis_cwd W' = cw⌝`, `⌜uvis_lazy W' = false⌝`, `my_pay (uvis_gen
  W') Q`.  `uvis_ch W'` and `uvis_pid W'` are unconstrained.
* `PinnedExec.pinned_exec_bundle(_at)` (iris/PinnedExec.v:296-395): the
  program-facing `□ ∀ na alen afun W', ⌜kexec_image_ok …⌝ -∗ ⌜uvis_cwd W' =
  cw⌝ -∗ ⌜uvis_lazy W' = false⌝ -∗ ⌜exec_args_of M av na alen afun⌝ -∗ my_pay
  (uvis_gen W') Q -∗ Pay -∗ X W'` -- the same four facts, nothing on
  children or pid.
* The facts are TRUE at the kernel's discharge: the key handed up is
  `SpecKexec.exec_key U' sts gn cs pidv na` (iris/ProofKexec.v:731, 782),
  whose `uvis_ch`/`uvis_pid` are `cs`/`pidv` by `reflexivity` (as
  `SpecKexec.exec_key_cwd` is), where `cs`/`pidv` are the kexec spec's
  binders for the caller's children row and pid (exec keeps both).  They
  are simply not STATED.

What (B) needs, and why it is a lane of its own (cone ~150 files, every
Spec/Proof of kexec, sys_exec, syscall, usertrap and the whole user tier):
1. `exec_slot_pre` gains two parameters `cs : gset gname` and `pidv : mword
   32` (as `cw`/`sts` are) and, in both wands, the rows `⌜uvis_ch W' = cs⌝
   -∗ ⌜uvis_pid W' = pidv⌝ -∗` (proved by `reflexivity` at `exec_key` in
   `ProofKexec`, mirrored in `ProofKexecA`/`ProofKexecD`/`ProofSysExec`).
2. Relayed by `SpecSysExec.sys_exec_slot_pre`/`sys_exec_au_pre`,
   `SpecKexec.exec_au_pre`, `SpecSyscall`'s exec row, `SpecUsertrap`, the
   user tier's exec deposit (`UexecSG.sbundle_at … USYS_exec`, `UexecApply`
   ~1059, `UexecRet`'s exec arm at `uvis_ch W`/`uvis_pid W` of the caller's
   key), `UexecExecInst.sbundle_exec_intro`, `PinnedExec.pex_slot`/
   `pinned_exec_bundle(_at)`.
3. `UkRun.udepw_at_ref` / `UkRunExecRef.udepw_at_refR` quantify the
   deposit's key over `cs pidv` universally and hand the supplier only
   `uheap`/`ufd_auth`; to PIN `cs = ∅`/`pidv` the supplier needs the record's
   children/pid authorities (`UkRun.urun_ids`) handed through beside them
   (a further `_refR`-style twin, as M6b did for the refund), so that init's
   fork child's `uch (ukn_ch N') ∅` and `∃ p, ⌜p <> 1⌝ ∗ upid (ukn_pid N') p`
   (UkInitMain ~1005, currently dropped with `_`) agree the key.
4. Then `UkInit.init_exec_sup_pos`/`init_lend_ref`, `UInitSh.
   init_exec_sup_of_sh_slot`, `UShKernel.sh_uexec_slot`/`sh_slot_of_kexec`
   carry `⌜uvis_ch W = ∅⌝`/`⌜uvis_pid W <> 1⌝` into `wp_ksh_start`;
   `UkSh.ush_pstate` carries `uch ∅` and `upid p` with `p <> 1` in place of
   `uch_any`/`upid_any`; `UkShFork`'s re-entry then has `Sc = ∅`, so the
   reaped generation is the forked one (`uwait_ans_pid_mine`) and the
   not-my-child arm disappears.
Nothing was weakened; nothing of (B) was started.

## 4. (C) and (D) -- BLOCKED by (B): the dependency chain

The brief asked (C) to proceed "for the arms that do not depend on (B)".
After (A) there are none; the chain is one line long:

* `UkSh.ush_wcp`'s affine arm (UkSh.v:1574) has two producers: (a)
  `UInitSh.init_exec_sup_of_sh_slot` (UInitSh.v:1250-1262) mapping
  `init_lend_cred`'s affine arm; (b) `UkShFork.wp_kshf_fork`'s wait re-entry
  when the reaped generation is not the forked one (UkShFork.v:826-830,
  `ush_posb_of_wc` at the third arm).  (b) is exactly (B).  (a) is
  circular with init's arms (below) and would die with them.
* Consumers of that arm are what keeps `init_rd_cred`'s `∨ True` alive: the
  affine assembler `UkSh.ush_at_of_pm` (= `UShLine.ush_at_of_mid`, the right
  arm of `ush_rd_x`) is used at `ush_gets_done_0`'s third arm (the shut-fd-0
  exit on `ush_wcp`'s True arm) and at `ush_posb_at` (the fork's affine arm,
  UkShFork.v:852); `ush_wcp_triv` at `ush_gets_done_line`'s third arm
  propagates the same arm.  So `init_rd_cred := Wb n` needs `ush_wcp`'s
  third arm gone, which needs (b), which is (B).
* `init_lend_cred`'s third arm (UkInit.v:1700) has, after (A), two
  producers: `UkInitMain.wp_kinit_banner` (lines 1146/1156, built from
  `init_rd_cred`'s True arm -- the token's credential arm) and
  `UkInitMain:1352` (from `UserConsole.uinit_lend_c`'s `C n ∨ T` right arm,
  which IS the taint and would fit a `T` arm).  The first needs
  `init_rd_cred`'s arm gone, i.e. (B).
* (D): `sh_deps` is spent on the PAID walk at `UkSh.ksh_w_of_wcp`'s True arm
  (the prompt on `ush_wcp`'s affine arm) with no `T` in hand; it cannot be
  restated as `□ (T -∗ sh_deps)` while that arm exists.  The other paid-walk
  spenders (getcmd's taint arm; the fork's taint sub-arm running the
  generic child) do have `T`, but the True arm alone keeps the unconditional
  premise, so `Hsh_owed`'s first conjunct cannot be deleted before (B)+(C).

So the order of record becomes: (B) [a lane of its own, §3] -> (C) -> (D),
with (A) landed.

## 5. Every `∨ True` left in iris/Uk*.v iris/USh*.v iris/UInit*.v iris/UEcho*.v

(grep, non-comment)
1. `UkInit.v:1657` `init_rd_cred Wb n := Wb n ∨ True` -- reason: the shell's
   exits through `ush_at_of_pm` (§4).
2. `UkInit.v:1700` `init_lend_cred`'s third arm -- reason: built in
   `wp_kinit_banner` from (1)'s True arm (§4).  Its other producer, the
   fork-failed pid disjunct, is GONE with (A).
3. `UkSh.v:1574` `ush_wcp`'s third arm -- reason: the wait re-entry's
   not-my-child arm (B) and `UInitSh`'s mapping of (2).
`UShLine.ush_rd_x` is (1) by definition (no `∨ True` of its own).  No new
`∨ True` introduced.

## 6. Remaining spenders of `sh_deps` (the free write law)

Paid walk: `UkSh.ksh_w_of_wcp` (the prompt on `ush_wcp`'s True arm);
`UkSh.wp_ksh_getcmd`'s taint arm; `UkShFork.wp_kshf_fork`'s affine/taint arm
(the generic child `UkShMain.wp_kshm_child_alloc` and its fork panic on
`ush_diag_leaf_holds`).  GONE from the paid walk with (A): the console arm's
pid sub-arm.
Generic (never entered by the paid child): `UkShRun.wp_kshr_fork1_any`,
`wp_kshr_runcmd`'s EXEC-returning / REDIR-failing arms via `ush_diag_leaf`;
every `UkShDiag.ksh_w1_of_law` site (`ush_diag_leaf_holds`, `wp_kshd_panic`,
`wp_kshd_die`, the printf tower's free-law corollaries); `UkShMain` (535,
710).  Forwarded only: `UShKernel.sh_uexec_slot` (550) / `sh_slot_of_kexec`
(764) -> `wp_ksh_start`; `UInitSh` (1096); `UInitBoot` (447, 599, 712, 905);
`UInitBootAdequacy.Hsh_owed` (139).

## 7. Remaining spenders of `udepw_law 16` (init's free write law)

`UkInitMain.wp_kinit_main_die_df` (230) and `_die_de` (377): the
closed-ledger arm and the lend's affine arm; `UkInitMain.wp_kinit_banner`
(1112): the same two arms plus the token's taint arm; definitions kept:
`UkInit.init_deps` (586), `UkInit.wp_kinit_write` (1184),
`UkInit.kinit_w1_of_law` (1312), `UkInitPrintf.wp_kinit_printf` (667).
Outside init: `UkEcho`/`UEchoKernel`/`UShEcho` (the generic echo entry,
`echo_slot_of_kexec`), `UkCat`.  Unchanged by this lane.

## 8. Trusted surface

`Hsh_owed` UNCHANGED (verbatim as in UInitBootAdequacy.v:139-140:
`(⊢ UkSh.sh_deps (PS := uprogSG_free)) /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)`).
`init_rd_cred`, `init_lend_cred`, `ush_wcp`, `sh_uexec_slot`'s premise list:
UNCHANGED.  Audit md5 57f7327206c4b276d05035342fea8ecf (the thirteen)
expected unchanged.  KERNEL CONTRACT TEXT unchanged; the trap loop's fork
answer `UexecRet.ufork_ans` (named by `SpecSyscall.sysc_fork_out` and
`SpecUsertrap`) gained a pure row the kernel proof already had -- reported
here because it strengthens what those contracts promise.

## 9. Gate lines (A) -- build rs-1 in `-disc` (VM tree `_shared_xv6iris-2-disc`)

```
scratchpad/rs-1.out:  COMPILED=136  EXIT=0
grep -c "^Error" /tmp/rs-1.log                                   -> 0
VM: make -f CoqMakefile -n | grep -c "ROCQ compile"              -> 0
VM: make audit-only 2>&1 | grep -v '^make\|^cd ' | md5sum       -> 57f7327206c4b276d05035342fea8ecf  (the thirteen, unchanged)
md5sum of the seven changed files: local = VM (all seven)
python3 tools/lemma_diff.py --ref origin/main
  -> 7 file(s) checked -- CLEAN (nothing dropped, nothing admitted, no new assumption)
grep 'Admitted\|admit\.' <the seven files>                       -> none
./gcp-rocq/run-on-gcp --check-dumps  -> the VM's tracked dumps match this checkout
git status --porcelain (after the commit)                        -> empty
```
The audit did not change, so nothing to explain line by line; (D) -- the
only expected change -- was not reached.

## 10. What the brief did not settle

* The pid-range row lives on `UexecRet.ufork_ans` (the trap loop's
  program-facing fork answer), not on `UkFork`'s leaf alone -- there was no
  other source (§2.1).
* (C)/(D) have NO (B)-independent part after (A) (§4); the brief assumed
  some.

## 11. Where a successor picks up

(A) is green and committed.  Next: (B) as its own lane per §3 (kernel-side
seam rows first, then the two twins in `UkRunExecRef`, then the entry), then
(C) and (D) exactly as the brief states them.
