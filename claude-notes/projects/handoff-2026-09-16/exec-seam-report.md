# Lane EXEC-SEAM -- report (checkout /shared/xv6iris-2-disc, branch lane/exec-seam)

Base: origin/main 6645b0260 (code 146e7cac1 = RESIDUALS (A)).  Never pushed.
No claude-notes edited.  No new file; iris/_CoqProject untouched.  Land the
three commits by cherry-pick, in order.

## 0. Vocabulary (plain concurrent-separation-logic and xv6 terms)

* A RESOURCE is a proposition of Iris's separation logic a process can own,
  split (`∗`) or hand over; a WAND `P -∗ Q` consumes `P` and yields `Q`; a
  PERSISTENT resource (`□ P`) can be copied; an AFFINE ARM is a disjunct
  `∨ True` under which a resource may be thrown away; a LAW is a persistent
  wand discharged once at the top of the theorem.
* The KEY `W : uvis` is a process's visible state record (image, registers,
  descriptor view `uvis_fd`, working directory `uvis_cwd`, generation
  `uvis_gen`, CHILDREN SET `uvis_ch` -- the generations of its live children
  -- and PID `uvis_pid`).  A SLOT `uslot W` is the weakest precondition of
  running the process at that key.
* THE EXEC SEAM is the kernel exec contract's program-facing wand
  (`SpecKexec.exec_slot_pre`): the exec'ing process hands in the slot of the
  program it is about to become, at every key `W'` the kernel may resume it
  at, and the kernel pins facts about `W'` before applying it.
* A CREDENTIAL is the linear resource a process must hold to put a byte on
  the console under the application's claim: `Wc n p` (the shell's, at input
  boundary `n` with `p` prompt bytes out), `Wb n` (BANNER-OWED: what a closed
  prompt leaves; init's next banner is paid from it), `Wp n` (ROUND-OPEN: what
  init lends).  `Pm n` are the PIECES of the console lease.  `T` is the TAINT:
  the persistent fact that the era is off the discipline; a tainted walk pays
  everything.
* The FREE WRITE LAW `UkSh.sh_deps = udepw_law 16` lets a `write(2)` count as
  paid without a credential; `Hsh_owed`'s first conjunct was the top theorem's
  admission of it.  The CLOSED-FD LEAF (`UkWriteClosed.kinit_w1_of_closed_l0`)
  pays a write to a closed descriptor: it reaches no wire.

## 1. Commits (all on lane/exec-seam, explicit paths, gated, not pushed)

* (B) `75e353efc` -- the exec seam carries the children set and the pid;
  sh's wait re-entry identifies its child (19 files).
* (C) `10b399a6c` -- the kills: no `∨ True` left in iris/Uk*.v iris/USh*.v
  iris/UInit*.v iris/UEcho*.v (9 files).
* (D) `d1cc70d8b` -- the free write law under the taint; `Hsh_owed`'s first
  conjunct DELETED (9 files).

## 2. (B) THE EXEC SEAM -- every changed KERNEL CONTRACT statement

`exec_slot_pre` gains two parameters `(cs : gset gname) (pidv : mword 32)`
after `sts`, and BOTH slot wands gain the rows `⌜uvis_ch W' = cs⌝ -∗
⌜uvis_pid W' = pidv⌝ -∗` after the lazy row and before the pay fact.  The
program-facing wand is STRONGER (the kernel owes two more facts), never an
assumption: at the kernel's discharge the key is `SpecKexec.exec_key U' sts gn
cs pidv na` and both rows are `reflexivity` (new lemmas `exec_key_ch`,
`exec_key_pid`; `ProofKexec`'s two success arms pay them with `exact`).

OLD `SpecKexec.exec_slot_pre` (origin/main): the same text without the two
parameters and without the two rows, i.e. each wand read
```
        ⌜uvis_cwd W' = cw⌝ -∗
        ⌜uvis_lazy W' = false⌝ -∗
        my_pay (uvis_gen W') Q -∗
```
### SpecKexec.exec_slot_pre NEW
```coq
  Definition exec_slot_pre (S : uvis -> iProp Σ) (Q : Z -> iProp Σ)
      (Pfin : Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ)
      (cw : Z)
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) : iProp Σ :=
    ((∀ (av : aview) (i : Z) (f : elf_bytes) (nl : nat) (W' : uvis),
        Pfin i -∗
        Φo av i (MkAnode (AFile f) nl) -∗
        ⌜kexec_loadable f⌝ -∗
        ⌜kexec_image_ok f na alen afun sts W'⌝ -∗
        ⌜uvis_cwd W' = cw⌝ -∗
        ⌜uvis_lazy W' = false⌝ -∗
        ⌜uvis_ch W' = cs⌝ -∗
        ⌜uvis_pid W' = pidv⌝ -∗
        my_pay (uvis_gen W') Q -∗
        S W')
     ∗ (∀ (av : aview) (i : Z) (a : anode) (W' : uvis),
          Pfin i -∗
          Φo av i a -∗
          ⌜~ anode_loadable a⌝ -∗
          ⌜exec_key_ok na alen sts W'⌝ -∗
          ⌜uvis_cwd W' = cw⌝ -∗
          ⌜uvis_lazy W' = false⌝ -∗
          ⌜uvis_ch W' = cs⌝ -∗
          ⌜uvis_pid W' = pidv⌝ -∗
          my_pay (uvis_gen W') Q -∗
          S W'))%I.
```

OLD `exec_au_pre`: `… (sts : list fdstate) : iProp Σ := (ex_start … ∗ pf_at (aopen_commit_at Γ appE) Fo ∗ pf_at (fun S => exec_slot_pre S Q (P (length (path_elems pl))) Fo.(pf_recv) cw na alen afun sts) Fs)%I.`
### SpecKexec.exec_au_pre NEW
```coq
  Definition exec_au_pre (Fs : pfam Σ (uvis -> iProp Σ)) Γ (γfs : fs_names)
      (cw : Z) (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (pl : list (bv 8))
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) : iProp Σ :=
    (ex_start γfs cw P Pmiss pl
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ pf_at (fun S => exec_slot_pre S Q (P (length (path_elems pl)))
                         Fo.(pf_recv) cw na alen afun sts cs pidv) Fs)%I.
```

OLD `exec_post_fail`: the same three arms at `… sts` (no `cs pidv`).
### SpecKexec.exec_post_fail NEW (head + arms)
```coq
  Definition exec_post_fail (Fs : pfam Σ (uvis -> iProp Σ)) Γ
      (γfs : fs_names) (cw : Z) (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (pl : list (bv 8))
      (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
      (sts : list fdstate) (cs : gset gname) (pidv : mword 32) : iProp Σ :=
    (
     exec_au_pre Fs Γ γfs cw Q P Pmiss Fo pl na alen afun sts cs pidv
     ∨ (
          (namei_walk_dead_era γfs P Pmiss pl
             ∗ pf_at (aopen_commit_at Γ appE) Fo
             ∗ pf_at (fun S => exec_slot_pre S Q (P (length (path_elems pl)))
                                 Fo.(pf_recv) cw na alen afun sts cs pidv)
                 Fs)
          ∨
          (∃ (i : Z) (av : aview) (a : anode) (c : exec_fail_cause),
             P (length (path_elems pl)) i
             ∗ ⌜arow_at av i a⌝ ∗ Fo.(pf_recv) av i a
             ∗ ⌜exec_fail_ok a na alen c⌝
             ∗ pf_at (fun S => exec_slot_pre S Q (P (length (path_elems pl)))
                                 Fo.(pf_recv) cw na alen afun sts cs pidv)
                 Fs)))%I.
```

`exec_arms` passes `cs pidv` to `exec_post_fail` (its own binders); the
kexec contract body `wp_kexec_sconf_body` states the bundle as
`exec_au_pre Fs Γfs fsc_fs (pv_cwi (us_V U)) Q P Pmiss Fo (bview plen pfun) na alen afun sts cs pidv`
(OLD: `… sts`); `exec_au_pre_triv_at`, `exec_au_pre_triv`, `exec_slot_pre_ne`,
`exec_au_pre_ne`, `exec_post_fail_refund` gain the two binders as pass-throughs.
NEW in SpecKexec:
```
Lemma exec_key_ch  … : uvis_ch  (exec_key U' sts gn cs pidv na) = cs.   (* reflexivity *)
Lemma exec_key_pid … : uvis_pid (exec_key U' sts gn cs pidv na) = pidv. (* reflexivity *)
```

SpecSysExec (the syscall boundary): `sys_exec_slot_pre`, `sys_exec_au_pre`,
`sys_exec_post_fail` gain `(cs : gset gname) (pidv : mword 32)` after `sts`;
`sys_exec_arms` passes its own `cs pid`; the contract body
`wp_sys_exec_sconf_body` states the bundle as
`sys_exec_au_pre Fs Γfs fsc_fs (pv_cwi (us_V U)) Q P Pmiss Fo (us_M U) v0 v1 sts cs pid`
(OLD: `… sts`).  OLD texts are the NEW ones minus the two parameters.
### SpecSysExec.sys_exec_slot_pre NEW
```coq
  Definition sys_exec_slot_pre (S : uvis -> iProp Σ) (Q : Z -> iProp Σ)
      (P : nat -> Z -> iProp Σ)
      (Φo : aview -> Z -> anode -> iProp Σ) (cw : Z)
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (cs : gset gname) (pidv : mword 32) : iProp Σ :=
    (∀ (pl : list (bv 8)) (na : nat) (alen : nat -> nat)
       (afun : nat -> nat -> bv 8),
       ⌜exec_path_of M pv pl⌝ -∗ ⌜exec_args_of M av na alen afun⌝ -∗
       exec_slot_pre S Q (P (length (path_elems pl))) Φo cw na alen afun sts
         cs pidv)%I.
```
### SpecSysExec.sys_exec_au_pre NEW
```coq
  Definition sys_exec_au_pre (Fs : pfam Σ (uvis -> iProp Σ)) Γ
      (γfs : fs_names) (cw : Z) (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (cs : gset gname) (pidv : mword 32) : iProp Σ :=
    ((∀ pl : list (bv 8), ⌜exec_path_of M pv pl⌝ -∗ ex_start γfs cw P Pmiss pl)
     ∗ pf_at (aopen_commit_at Γ appE) Fo
     ∗ pf_at (fun S => sys_exec_slot_pre S Q P Fo.(pf_recv) cw M pv av sts
                         cs pidv) Fs)%I.
```
### SpecSysExec.sys_exec_post_fail NEW
```coq
  Definition sys_exec_post_fail (Fs : pfam Σ (uvis -> iProp Σ)) Γ (γfs : fs_names) (cw : Z)
      (Q : Z -> iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
      (M : gmap Z (bv 8)) (pv av : mword 64) (sts : list fdstate)
      (cs : gset gname) (pidv : mword 32) : iProp Σ :=
    (sys_exec_au_pre Fs Γ γfs cw Q P Pmiss Fo M pv av sts cs pidv
     ∨ (∃ (pl : list (bv 8)) (na : nat) (alen : nat -> nat)
          (afun : nat -> nat -> bv 8),
          ⌜exec_path_of M pv pl⌝ ∗ ⌜exec_args_of M av na alen afun⌝ ∗
          exec_post_fail Fs Γ γfs cw Q P Pmiss Fo pl na alen afun sts cs pidv))%I.
```

SpecSyscall / SpecUsertrap: NO TEXTUAL EDIT.  They name the exec deposit
only through `UexecSG.sbundle_at … USYS_exec`, whose kernel instance
`UexecExecInst.exec_sbundle X f W` now reads
`sys_exec_au_pre (MkPfam X (xf_Rs f)) … (uvis_fd W) (uvis_ch W) (uvis_pid W)`
(OLD: `… (uvis_fd W)`), so both contracts promise the two rows
transitively.  `exec_sbundle_cong` gains the two premises `uvis_ch W =
uvis_ch W' -> uvis_pid W = uvis_pid W' ->` (both already in
`UexecSG.skey_eq`); `xv6_sbundle_mono`, `xv6_sbundle_of_supply`, the six
`sbundle_*exec*` intro/elim lemmas and `ProofSyscall.sysc_exec_in_open`
(conclusion at `… sts cs pid`) are pass-throughs.

THE BOOT BUNDLE keeps its arity (App.Hinit_boot, BootChain, ParkCap,
ProofMain, ProofUserinit name it): the two readings are quantified INSIDE
the existential, the first process's constructor reads neither, and
`ProofForkret`'s boot arm specialises it at the block's `cs pid`.
OLD: the same text without the `∀ (cs : gset gname) (pidv : mword 32),` line
and without `cs pidv` at the end.
### InitBoot.init_boot_bundle NEW
```coq
  Definition init_boot_bundle (cw : Z) (sts : list fdstate) : iProp Σ :=
    (cons_reader fsc_cons 0%nat -∗
     ∃ (P Pmiss : nat -> Z -> iProp Σ)
       (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ))
       (R : iProp Σ),
       ∀ (cs : gset gname) (pidv : mword 32),
         exec_au_pre (MkPfam uslot R) (fs_gamma_L fsc_fs) fsc_fs cw
           (fun _ => True%I) P Pmiss Fo init_boot_path
           1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) sts cs pidv)%I.
```

Kernel Proof files (only the reflexivity discharge and pass-throughs):
`ProofKexec` (two `exact (exec_key_ch …)`/`exact (exec_key_pid …)`;
`kxau_close_fail`, `kxau_close_ok`, the phase-A call get `cs`/`cs pidv`),
`ProofKexecA` (`kxa_receipt`, `kxa_receipt_x`, `kxa_fail_dead`, `kxa_fail_obs`
gain `cs pidv`; `kxc_phaseA_au` gains a `(cs : gset gname)` binder),
`ProofSysExec` (`sys_exec_au_pre_at` gains `cs pidv`; `sx_break_au`'s bundle
row at `… sts cs pid`), `ProofSyscall`, `ProofForkret`, `InitBoot`.
`PinnedExec.pex_slot_at` / `pex_slot` / `pinned_exec_bundle_at` /
`pinned_exec_bundle` gain `cs pidv` and their constructor wand gains
`⌜uvis_ch W' = cs⌝ -∗ ⌜uvis_pid W' = pidv⌝ -∗` (after the lazy row);
`pinned_exec_bundle_boot_at` / `_boot` keep the old 4-row constructor and
drop the two rows themselves.

### The new twin (the U-tier supplier's route to the two facts)

`UkRun.udepw_at_ref` / `UkRunExecRef.udepw_at_refR` quantify the deposit's
key over `cs pidv` and lend the supplier only the heap and the descriptor
authority, so a supplier could not SAY what `cs`/`pidv` are.  The twin lends
the record's children/pid authority `UkRun.urun_ids N cs pidv` beside them
and takes it back; the leaf is `wp_uk_ecall_exec_at_cwd_refR`'s proof with
one resource handed through (M6b's precedent; UexecSG/UkRun/UkRunSys
untouched).  `udepw_at_refR_ids_of_refR` is the forgetful direction.
### UkRunExecRef.udepw_at_refR_ids NEW
```coq
  Definition udepw_at_refR_ids (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) (R : iProp Σ) : iProp Σ :=
    (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z)
       (fdv : list fdstate) (gn : gname) (cs : gset gname) (pidv : mword 32),
       my_pay gn (ukn_pay N) -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗ ufd_auth (ukn_fd N) fdv -∗
       urun_ids N cs pidv -∗
       uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗ ufd_auth (ukn_fd N) fdv ∗
       urun_ids N cs pidv ∗
       sbundle_pay_refR uslot (ukn_pay N) R
         (uvis_of_run m pc M pm sz fdv c gn cs pidv false))%I.
```
### UkRunExecRef.wp_uk_ecall_exec_at_cwd_refR_ids NEW
```coq
  Lemma wp_uk_ecall_exec_at_cwd_refR_ids (N : uk_names Σ) (h : CpuId) (m : regfile)
      (pc : mword 64) (avail : nat) (c : Z) (R : iProp Σ) :
    usysno m = USYS_exec ->
    is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗
    urun N h m pc avail -∗
    UserCwd.ucwd (ukn_cwd N) c -∗
    udepw_at_refR_ids N m pc c R -∗
    (∀ h' : CpuId,
       UserCwd.ucwd (ukn_cwd N) c -∗
       R -∗
       urun N h'
         (<[Regidx (mword_of_int 10) := (mword_of_int (-1) : mword 64)]> m)
         (add_vec_int pc 4) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
```

### init -> sh, the two facts' path

* `UkInitMain.wp_kinit_fork`'s child arm KEEPS the fork leaf's
  `UserChildren.uch (ukn_ch N') ∅` and `∃ p : Z, ⌜p <> 1⌝ ∗ upid (ukn_pid N') p`
  (they were dropped with `_ _`); `wp_kinit_main_child` and the main loop's
  child arm thread them.
* `UkInit.init_exec_sup_pos` takes both fragments as premises (before the
  deposit) and concludes `udepw_at_refR_ids …` (was `udepw_at_refR`);
  `wp_kinit_exec` takes `udepw_at_refR_ids` and calls the new leaf.
* `UInitSh.init_exec_sup_of_sh_slot` reads `cs = ∅` (`uch_agree` against the
  lent `urun_ids`) and `bv_unsigned pidv = p` (`upid_agree`), hands the
  authority back, and its constructor wand (`Hcon`, the `pinned_exec_bundle`
  argument) carries the two rows; `sbundle_pay_exec_intro_refR`'s statement
  is at `(uvis_ch W) (uvis_pid W)`.
* `UShKernel.sh_uexec_slot` / `sh_slot_of_kexec` take
  `uvis_ch W = ∅ -> bv_unsigned (uvis_pid W) <> 1 ->` and hand `wp_ksh_start`
  `uch γch ∅` and `ush_pid`.
* `UkSh.ush_pstate` / `ush_bstate` carry `uch γch ∅ ∗ ush_pid` in place of
  `uch_any γch ∗ upid_any γpid` (same conjunct count, so every positional
  reader stands; `UkShEcho.ush_pstate_at` follows):
### UkSh.ush_pid / ush_pstate / ush_bstate NEW
```coq
  Definition ush_pid : iProp Σ :=
    (∃ p : Z, ⌜p <> 1⌝ ∗ UserChildren.upid γpid p)%I.
  Global Instance ush_pid_timeless : Timeless ush_pid.
  Proof. rewrite /ush_pid. apply _. Qed.
  Definition ush_pstate (l : list fdstate) : iProp Σ :=
    (ush_std l ∗ UserCwd.ucwd γcwd FsImg.ROOTINO ∗ UserChildren.uch γch ∅
     ∗ ush_pid ∗ ush_posb l 0%nat)%I.
  Definition ush_bstate (l : list fdstate) : iProp Σ :=
    (ush_std l ∗ UserCwd.ucwd γcwd FsImg.ROOTINO ∗ UserChildren.uch γch ∅
     ∗ ush_pid ∗ ush_posb l 3%nat)%I.
```

OLD `ush_pstate l := (ush_std l ∗ UserCwd.ucwd γcwd FsImg.ROOTINO ∗ UserChildren.uch_any γch ∗ UserChildren.upid_any γpid ∗ ush_posb l 0%nat)%I` (and `ush_bstate` at `3%nat`).

* `UkShFork.wp_kshf_fork_core` forks at `∅`, waits at sh's own pid `p <> 1`,
  proves `Sw' = ∅` once (NEW `ushf_wait_empty`, `ushf_pid_ne_1`) and rebuilds
  `uch γch ∅ ∗ ush_pid`; its re-entry continuation is
  `∀ Sw Sw' ret pidv, ⌜pidv <> 1⌝ -∗ ⌜ret = -1 -> Sw' = ∅⌝ -∗ ushf_fans ∅ Q Rc Sw -∗ uwait_ans_pid ret Sw Sw' pidv -∗ Pex -∗ ◇ ush_posb … l 0`.
  In `wp_kshf_fork`'s console arm the reaped generation is the forked one:
  `wait_ans`'s `γ' ∈ Sw ∨ pidv = 1` has its right disjunct refuted by `pidv
  <> 1` and its left by `Sw = ∅ ∪ {[γ]}`; THE NOT-MY-CHILD ARM IS GONE.
### UkShFork.ushf_wait_empty NEW
```coq
  Lemma ushf_wait_empty (Q : Z -> iProp Σ) (Rc : iProp Σ)
      (Sw Sw' : gset gname) (ret : mword 64) (pidv : mword 32) :
    pidv <> (mword_of_int 1 : mword 32) ->
    (ret = (mword_of_int (-1) : mword 64) -> Sw' = (∅ : gset gname)) ->
    ushf_fans ∅ Q Rc Sw -∗ uwait_ans_pid ret Sw Sw' pidv -∗
    ⌜Sw' = (∅ : gset gname)⌝.
```

## 3. (C) THE KILLS

NEW texts:
### UkInit.init_rd_cred NEW
```coq
  Definition init_rd_cred (Wb : nat -> iProp Σ) (n : nat) : iProp Σ :=
    Wb n.
```
OLD: `init_rd_cred Wb n := (Wb n ∨ True)%I`.
### UkInit.init_lend_cred NEW
```coq
  Definition init_lend_cred (T : iProp Σ) (st : fdstate)
      (Wp Wb : nat -> iProp Σ)
      (l : list fdstate) (n : nat) : iProp Σ :=
    ((⌜l = ufd_l3 st⌝ ∗ Wp n)
     ∨ (⌜l = ufd_l0⌝ ∗ Wb n)
     ∨ T)%I.
```
OLD: `init_lend_cred (st) (Wp Wb) (l) (n) := ((⌜l = ufd_l3 st⌝ ∗ Wp n) ∨ (⌜l = ufd_l0⌝ ∗ Wb n) ∨ True)%I` -- no `T` parameter.  Every application gained the `T` argument (UkInit, UkInitMain, UInitSh); `wp_kinit_main_die_df` gained a `(T : iProp Σ)` binder (and, in (D), `{!Persistent T}`).
### UkSh.ush_wcp NEW
```coq
  Definition ush_wcp (l : list fdstate) (n p : nat) : iProp Σ :=
    ((⌜ ush_fd0c l /\ ush_fd1p l /\ ush_fd2p l ⌝ ∗ Wc n p)
     ∨ (⌜ (exists j : nat, (j <= 2)%nat /\ ush_lcl l j) /\ (p < 3)%nat ⌝ ∗ Wb n))%I.
```
OLD: the same two arms `∨ True`.

Every deleted name, and where its users went:
* `UkSh.ush_wcp_triv` -- users: `ush_wcp_cons`'s and `ksh_w_of_wcp`'s affine
  branch (deleted with the arm), `ush_posb_of` (deleted), `ush_gets_done_line`'s
  affine arm (deleted).
* `UkSh.ush_at_of_pm` (section hypothesis, the credential-less payload
  assembler) -- users: `ush_pos_of_posb`, `ush_posb_at` (both deleted),
  `ush_gets_done_0`'s affine arm (deleted), `ush_rest_l`'s second pure premise
  `⌜∀ i, ush_bnd i -> ⊢ Pm i -∗ ush_at i⌝` (DELETED from the obligation --
  a premise fewer makes the trusted obligation's discharger STRONGER, and
  `sh_pay_rest`'s own text is unchanged), `wp_ksh_loop`'s discharge of it.
  Positional threading `Hpm2` dropped from `UShKernel.sh_uexec_slot` /
  `sh_slot_of_kexec`, `UInitSh.init_exec_sup_of_sh_slot`,
  `UInitBoot.init_cons_sup_of_sh_slot` (`Hsh_pm2` gone), `UkShFork.wp_kshf_fork`
  / `wp_kshm_body` / `ushf_rest_of_body`.
* `UkSh.ush_pos_of_posb` -- user `ush_gets_done_pos` (deleted).
* `UkSh.ush_posb_at`, `ush_posb_of` -- users: `wp_kshf_fork`'s affine/taint arm,
  which is the TAINT arm alone now: it destructs `T ∗ ush_pos` directly and
  rebuilds `ush_posb`'s right arm at the re-entry.
* `UkSh.ush_gets_done_pos` -- user: `wp_ksh_loop`'s exit at the `bltz` (fd 0
  shut); it destructs `ush_gets_done` directly and REFUTES the line-read arm:
  `wp_ksh_getcmd`'s return row is TOTAL now,
  `⌜(g 0 = ubyte0 -> a0 = -1) /\ (g 0 <> ubyte0 -> a0 = 0)⌝`
  (was the first half only; the second is `seqz`/`negw` computed on a
  nonzero byte), and a line's first byte is 'e'.
* `UShLine.ush_at_of_mid` -- no user (the right-arm assembler);
  `ush_at_of_mid_wb` is the one-arm family's assembler.
* `UkInit.init_lend_cred_triv` -- users: `wp_kinit_banner` (its token arm is
  real now; the row's taint is the lend's `T` arm), the restart loop's mint
  (`uinit_lend_c`'s `∨ T` arm -> the lend's `T` arm).
* `UkInit.init_pay_of_lend` -- user: `wp_kinit_main_die_de`'s non-console
  arms; the closed row pays the pair with the lend's own `Wb np`, the taint
  row with the pair's taint arm (`ucons_pay_taint`).
* `UInitSh`'s mapping of the affine arm (`- iRight. by iRight.`) -- the lend's
  `T` arm now goes to the entry law's right disjunct: `UShKernel.sh_uexec_slot`
  / `sh_slot_of_kexec` take `(ush_wcp … ∨ T)` and so does the entry law `Hbd`
  (`UShLine.ush_posb_of_lend` takes `(ush_wcp … ∨ T)` and builds the cursor's
  taint arm); `UkInitKernel`'s boot token pays the pair's one arm.

Every `∨ True` left in iris/Uk*.v iris/USh*.v iris/UInit*.v iris/UEcho*.v
(non-comment): NONE.  `grep -n "∨ True"` over those files is empty after (C)
and after (D).

## 4. (D) THE FREE LAW

### The trusted change

`UInitBootAdequacy.Hsh_owed`, OLD:
### UInitBootAdequacy.Hsh_owed OLD (origin/main)
```coq
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)
```
NEW:
### UInitBootAdequacy.Hsh_owed NEW
```coq
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)
```

`UInitBoot.echo_Hinit_boot` loses the matching premise `(⊢ UkSh.sh_deps (PS
:= uprogSG_free)) ->`.  The adequacy proof takes the single entailment
(`pose proof … as Hre`).

### The audit after (D) (VM `make audit-only`, `grep -v '^make\|^cd '`), md5 57f7327206c4b276d05035342fea8ecf -- UNCHANGED

```
Axioms:
PrimInt63.sub : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimString.string : Set
xv6iris_extras.resv_matches : forall n : BinNums.Z, Values.mword n -> bool
xv6iris_extras.resv_is_valid : bool
PrimInt63.lsr : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lsl : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lor : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.land : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.int : Set
PrimString.get : PrimString.string -> PrimInt63.int -> PrimString.char63
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
PrimInt63.eqb : PrimInt63.int -> PrimInt63.int -> bool
PrimString.cat : PrimString.string -> PrimString.string -> PrimString.string
```
Line by line: the eleven `PrimInt63`/`PrimString` primitives (the statement
names a `PrimString`-backed disk image; primitives have no body and the
traversal lists them like axioms), the two LR/SC reservation hooks
(`resv_matches`, `resv_is_valid`, arbitrary but fixed), and
`functional_extensionality_dep` from the proof.  The md5 did NOT change
although a hypothesis was deleted, and that is expected: `Print
Assumptions` sees axioms, never the theorem's own premises -- `Hsh_owed`
was a premise of `echo_adequacy_modulo_phi`, so its first conjunct was
invisible to the audit before and after.  One hypothesis fewer is the
whole trusted change; the brief's "the md5 WILL change if the hypothesis
count changes" does not hold for a premise.

### Why the law was derivable, and what the brief did not foresee

* `FsAbsInvFire.fsabs_filewrite_in` is stated under `|==>` but every arm of
  its proof is `iModIntro`, so NEW `UexecExecMint.filewrite_in_of_sup :
  app_sup -∗ out_licence -∗ filewrite_in st n M ua (fun _ => True)` is
  update-free and fits `UkRun.udepw`'s modality-free shape.  NEW
  `udepw_of_sup_write`, `udepw_law_of_sup_write : app_sup -∗ out_licence -∗
  udepw_law (PS := PSx) 16` mirror `udepw_of_sup`'s 15/17.  At the top,
  `Htsw : echo_taint γ -∗ app_sup` and `Hlic : □ (echo_taint γ -∗
  out_licence)` give `□ (T -∗ udepw_law 16)` for both init and sh.
* NOT IN THE BRIEF: init's own free law (`init_deps`' first conjunct, the
  unconditional `udepw_law 16`) was spent on the CLOSED-LEDGER row of
  `wp_kinit_main_die_df` / `_die_de` / `wp_kinit_banner` with no taint in hand
  (line 712 of UInitBoot fed it `Hsh_deps`).  Those writes go to a closed
  fd 1 and reach no wire, so they pay through the closed-fd leaf
  `UkWriteClosed.kinit_w1_of_closed_l0` with the ledger `ustd (ukn_fd N)
  ufd_l0` as the per-byte carrier (`Ch := fun _ => ustd …`), and the taint
  row cashes the law under `T`.  `init_deps` moves out of UkInit's section
  (the closed-fd law must be record-generic: the exec'ing child's
  diagnostics run at the record its fork minted) and its first conjunct is
  the PAIR in the old conjunct's position, so every `#(Hwr & Hwl15 &
  Hwl17)` / `[$Hwr $Hwl15 $Hwl17]` pass-through stands:
### UkInit.kinit_wcl / kinit_wlaw / init_deps NEW
```coq
  Definition kinit_wcl : iProp Σ :=
    (□ (∀ (N0 : uk_names Σ) (b : bv 8),
          kinit_w1 N0 (mword_of_int 1 : mword 64) b
            (UserFd.ustd (ukn_fd N0) ufd_l0) (UserFd.ustd (ukn_fd N0) ufd_l0)))%I.
  Global Instance kinit_wcl_persistent : Persistent kinit_wcl.
  Proof. rewrite /kinit_wcl. apply _. Qed.
  Definition kinit_wlaw (T : iProp Σ) : iProp Σ :=
    (□ (T -∗ udepw_law 16) ∗ kinit_wcl)%I.
  Global Instance kinit_wlaw_persistent T : Persistent (kinit_wlaw T).
  Proof. rewrite /kinit_wlaw. apply _. Qed.
  Definition init_deps (T : iProp Σ) : iProp Σ :=
    (kinit_wlaw T ∗ □ (T -∗ udepw_law 15) ∗ □ (T -∗ udepw_law 17))%I.
```
OLD: `init_deps T := (udepw_law 16 ∗ □ (T -∗ udepw_law 15) ∗ □ (T -∗ udepw_law 17))%I` inside the section.  `uki_open1_of_dance` takes `□ (T -∗ udepw_law 17)` directly.  The three spenders take `kinit_wlaw T` (was `udepw_law 16`) and bind `{!Persistent T}`; `UInitBoot.init_deps_of_laws` takes `□ (T -∗ udepw_law 16) -∗ kinit_wcl -∗ …` and UInitBoot discharges `kinit_wcl` from `kinit_w1_of_closed_l0` (new `Require Import UkWriteClosed`).

### The shell: `sh_deps` premises on the paid walk became `□ (T -∗ sh_deps)`

`UkSh.wp_ksh_getcmd` (its taint arm cashes it: the prompt on a tainted
turn), `wp_ksh_loop`, `wp_ksh_cmd_head`, `wp_ksh_console`, `wp_ksh_main`,
`wp_ksh_start`; `UShKernel.sh_uexec_slot` / `sh_slot_of_kexec`;
`UInitSh.init_exec_sup_of_sh_slot`; `UInitBoot.init_cons_sup_of_sh_slot`
(at `echo_taint γ`); `UkShFork.wp_kshf_fork` / `wp_kshm_body` /
`ushf_rest_of_body` (the taint arm cashes it for the generic child
`UkShMain.wp_kshm_child_alloc` and the panic `ush_diag_leaf_holds`).
`wp_ksh_gets` / `wp_ksh_gets_loop` lose the premise (only forwarded).
`ksh_w_of_wcp` lost it in (C) (no arm to print on).

### `sh_uexec_slot`'s premise list, NEW (comments stripped; OLD differed by
`Hpm2`, `ush_wcp …` bare in two places, `UkSh.sh_deps` bare, and no
`uvis_ch`/`uvis_pid` rows -- the OLD text is appended at the end)
### UShKernel.sh_uexec_slot NEW (premise list)
```coq
  Lemma sh_uexec_slot (R : gname -> gname -> gname -> iProp Σ)
      (γp : gname) (cn : cons_names) (T K : iProp Σ) `{!Persistent T}
      (Q : Z -> iProp Σ)
      (Ql : Z -> iProp Σ)
      (Pm : nat -> iProp Σ)
      (Wc : nat -> nat -> iProp Σ)
      (Wb : nat -> iProp Σ)
      (Hrl : forall (N : uk_names Σ) (l : list fdstate),
         ukn_pay N = Q -> ⊢ UkSh.ush_read_recv_leaf N γp T Pm cn l)
      (Hpm1 : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q -> ⊢ UkSh.ush_at N γp i -∗ UkSh.ush_lease N γp T Pm i)
      (Hpm3 : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q -> ⊢ T -∗ Pm i -∗ UkSh.ush_at N γp i)
      (Hpmwb : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q -> UkSh.ush_bnd i ->
         ⊢ Pm i -∗ Wb i -∗ UkSh.ush_at N γp i)
      (Hwc : forall n : nat,
         ⊢ Pm (n + length EchoDisc.echo_line)%nat -∗ Wc n 2%nat -∗
           Pm (n + length EchoDisc.echo_line)%nat
           ∗ Wc (n + length EchoDisc.echo_line)%nat 3%nat)
      (Hwbwc : forall n : nat, ⊢ Wb n -∗ Wc n 0%nat)
      (Hwbl : forall n : nat, ⊢ Wc n 3%nat -∗ Wc n 0%nat)
      (Hwbr : forall n : nat,
         ⊢ Pm (n + length EchoDisc.echo_line)%nat -∗ Wb n -∗
           Pm (n + length EchoDisc.echo_line)%nat ∗ T)
      (W : uvis) (n0 n : nat) :
    (forall (N : uk_names Σ) (l : list fdstate) (n : nat),
       ukn_pay N = Q ->
       ⊢ upos γp n -∗ Ql (-1) -∗ (UkSh.ush_wcp Wc Wb l n 0%nat ∨ T) -∗
         UkSh.ush_posb N γp T Wc Wb Pm l 0%nat) ->
    (forall x y : Z, Q x = Q y) ->
    tf_resume_pc (uvis_tf W) = (mword_of_int ShSyms.start : mword 64) ->
    shk_img_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 8192 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * (2 + (8 + (16 + (ush_Dbody + n0)))))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    uvis_cwd W = FsImg.ROOTINO ->
    uvis_lazy W = false ->
    uvis_ch W = ∅ ->
    bv_unsigned (uvis_pid W) <> 1 ->
    □ (∀ γt γd γs : gname,
        usz γs (uvis_sz W) -∗
        ([∗ map] k ↦ b ∈ base.filter
              (fun kv : Z * bv 8 =>
                 kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                        - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
              (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
           ubyte γd k b) -∗
        |==> ∃ f : nat -> bv 8, R γt γd γs ∗ ubytes γd sh_buf sh_nbuf f) -∗
    udep -∗
    □ (T -∗ UkSh.sh_deps) -∗
    UkSh.ush_tag_law T -∗
    sh_prompt_law Wc -∗
    (∀ N : uk_names Σ,
       ush_rest_l N γp T Wc Wb Pm (R (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    UkSh.ush_fd0 T (take NSTD (uvis_fd W)) -∗
    (□ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N T)
     ∨ (□ (∀ N : uk_names Σ, UkSh.ush_open_absent_leaf N T K) ∗ K)
     ∨ T) -∗
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ uslot W') -∗
    my_pay (uvis_gen W) Q -∗
    upos γp n -∗
    Ql (-1) -∗
    (UkSh.ush_wcp Wc Wb (take NSTD (uvis_fd W)) n 0%nat ∨ T) -∗
    uslot W.
  Proof.
```

## 5. Every remaining spender of `sh_deps` (= `udepw_law 16` at sh)

PAID WALK: none unconditional.  Under the taint only: `UkSh.wp_ksh_getcmd`'s
taint arm (the prompt of a tainted turn), `UkShFork.wp_kshf_fork`'s taint arm
(the generic child and its panic), each from `□ (T -∗ sh_deps)`.
GENERIC (the paid child never enters them; unconditional premise kept):
`UkSh.wp_ksh_write`, `UkSh.ksh_w_of_law` (definitions), `UkShRun` (1285,
1953, 3068: `wp_kshr_fork1_any`, `wp_kshr_runcmd`'s arms), `UkShDiag` (every
`ksh_w1_of_law` site: `ush_diag_leaf_holds`, `wp_kshd_panic`, `wp_kshd_die`,
the printf tower's corollaries), `UkShMain` (535, 710).
FORWARDED: none left bare -- the entry chain forwards `□ (T -∗ sh_deps)`.
`Hsh_owed`: no longer names it.

Every remaining spender of `udepw_law 16` (init's and the generic programs'):
`UkInit.wp_kinit_write` (1181), `kinit_w1_of_law` (1309), `kinit_wlaw`
(2008, under `T`), `UkInitPrintf.wp_kinit_printf` (667), `UkInitMain`'s three
spenders only through `kinit_wlaw T` (taint row) -- the closed row is the
closed-fd leaf, the console row the era's links; outside init: `UkCat`,
`UkEcho`, `UShEcho`, `UEchoKernel` (the generic echo entry; unchanged).

## 6. Gate lines per commit (VM tree `_shared_xv6iris-2-disc`)

(B) `75e353efc`: builds es-1 (79 files, 2 errors), es-2 (110, 1 error),
es-3 `COMPILED=113 EXIT=0`; `grep -c "^Error" /tmp/es-3.log` -> 0;
`make -f CoqMakefile -n | grep -c "ROCQ compile"` -> 0; md5 of the 19
changed files local = VM (bc864d15e430447a72bf15b3b15183fb); audit md5
57f7327206c4b276d05035342fea8ecf; `python3 tools/lemma_diff.py --ref
origin/main` -> 19 file(s) checked -- CLEAN; no Admitted; `--check-dumps`
"the VM's tracked dumps match this checkout".

(C) `10b399a6c`: builds es-4..es-8 (errors fixed in turn), es-9
`COMPILED=35 EXIT=0`; ^Error 0; make -n 0; md5 local = VM
(45c85b52b1968e2414051f00254b29a6); audit md5 57f7…; lemma_diff: 9 GONE
(UShLine.ush_at_of_mid; UkInit.init_pay_of_lend, init_lend_cred_triv;
UkSh.ush_wcp_triv, ush_at_of_pm (hypothesis), ush_pos_of_posb, ush_posb_at,
ush_posb_of, ush_gets_done_pos -- every one a deliberate deletion, §3), no
NEWAXIOM, no Admitted; check-dumps clean.

(D) `d1cc70d8b`: builds es-10 (2 errors), es-11 `COMPILED=55 EXIT=0`;
^Error 0; make -n 0; md5 local = VM (cbe29b00dd179df34bf07e5c1dc936a8);
audit text printed in §4, md5 57f7… unchanged; lemma_diff: the same 9 GONE
as (C), nothing new; no Admitted; check-dumps clean.

Build logs stay on the VM at /tmp/es-N.log; the .out files are in the
scratchpad (es-1.out .. es-11.out).

## 7. What the brief did not settle (decisions taken, to be confirmed)

1. The identity rows are placed AFTER the lazy row and BEFORE the pay fact
   in both slot wands (the residuals report's order); every consumer that
   destructs the wand was updated for it.
2. The boot bundle: `∀ cs pidv` INSIDE `init_boot_bundle`'s existential
   rather than two new parameters -- keeps App/BootChain/ParkCap/ProofMain/
   ProofUserinit textually unchanged; the first process's constructor
   ignores the two rows.
3. The twin is an EXTENSION of UkRunExecRef.v (`_refR_ids`), not a new file;
   UexecSG/UkRun/UkRunSys untouched.
4. sh's pid fact is carried as `UkSh.ush_pid := ∃ p, ⌜p <> 1⌝ ∗ upid γpid p`
   (one conjunct, the pstate's arity unchanged) and the children set as
   `uch γch ∅`; the fork core proves `Sw' = ∅` once (`ushf_wait_empty`)
   rather than in every re-entry.
5. `init_lend_cred` gained a `T` PARAMETER (its third arm is `T`), so every
   application names the taint; `wp_kinit_main_die_df` binds `T` now.
6. The lend's `T` arm is mapped to the entry law's right disjunct: the entry
   (`sh_uexec_slot`, `sh_slot_of_kexec`, `Hbd`, `ush_posb_of_lend`) takes
   `(ush_wcp … ∨ T)`; a tainted lend is the cursor's own taint arm.  This is
   what replaced "UInitSh's mapping of the affine arm".
7. `ush_rest_l` lost its `ush_at_of_pm` premise (a change inside the trusted
   obligation's cone; `sh_pay_rest`'s text unchanged).
8. `wp_ksh_getcmd`'s return row was made total (the second direction was
   needed to refute the line-read arm at the shell's exit without an
   assembler).
9. (D)'s mechanism: the brief's `□ (T -∗ sh_deps)` IS derivable (the
   `|==>` on `fsabs_filewrite_in` is vestigial), but ONLY the shell's spend
   sites were taint arms; init's closed-ledger rows needed the closed-fd
   leaf, threaded as `init_deps`' bundled first conjunct (`kinit_wlaw`).
   `UkWriteClosed` is imported by UInitBoot only (it sits above UkSh, so
   UkInitMain cannot import it; the leaf reaches init as a law).
10. The audit md5 did not change (a premise, not an axiom) -- see §4.

## 8. Where a successor picks up

All three milestones are green and committed on lane/exec-seam; the working
tree is clean.  Next is lane R3 (r3-survey-2.md §6): `ush_gen_slot` and the
wb-assembler into `ush_rest_l`'s box, the fork's taint arm to the generic
slot through `ush_gen_run` (which then deletes `uxsup`, the generic child and
the panic -- and with them the last `□ (T -∗ sh_deps)` premises of the three
fork lemmas), new `UShRest.sh_rest_holds`, `sh_pay_rest` DELETED and
`Hsh_owed` with it (now a single conjunct).

## Appendix: `sh_uexec_slot`'s OLD premise list (origin/main, comments stripped)
### UShKernel.sh_uexec_slot OLD premise list (origin/main)
```coq
  Lemma sh_uexec_slot (R : gname -> gname -> gname -> iProp Σ)
      (γp : gname) (cn : cons_names) (T K : iProp Σ) `{!Persistent T}
      (Q : Z -> iProp Σ)
      (Ql : Z -> iProp Σ)
      (Pm : nat -> iProp Σ)
      (Wc : nat -> nat -> iProp Σ)
      (Wb : nat -> iProp Σ)
      (Hrl : forall (N : uk_names Σ) (l : list fdstate),
         ukn_pay N = Q -> ⊢ UkSh.ush_read_recv_leaf N γp T Pm cn l)
      (Hpm1 : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q -> ⊢ UkSh.ush_at N γp i -∗ UkSh.ush_lease N γp T Pm i)
      (Hpm2 : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q -> UkSh.ush_bnd i ->
         ⊢ Pm i -∗ UkSh.ush_at N γp i)
      (Hpm3 : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q -> ⊢ T -∗ Pm i -∗ UkSh.ush_at N γp i)
      (Hpmwb : forall (N : uk_names Σ) (i : nat),
         ukn_pay N = Q -> UkSh.ush_bnd i ->
         ⊢ Pm i -∗ Wb i -∗ UkSh.ush_at N γp i)
      (Hwc : forall n : nat,
         ⊢ Pm (n + length EchoDisc.echo_line)%nat -∗ Wc n 2%nat -∗
           Pm (n + length EchoDisc.echo_line)%nat
           ∗ Wc (n + length EchoDisc.echo_line)%nat 3%nat)
      (Hwbwc : forall n : nat, ⊢ Wb n -∗ Wc n 0%nat)
      (Hwbl : forall n : nat, ⊢ Wc n 3%nat -∗ Wc n 0%nat)
      (Hwbr : forall n : nat,
         ⊢ Pm (n + length EchoDisc.echo_line)%nat -∗ Wb n -∗
           Pm (n + length EchoDisc.echo_line)%nat ∗ T)
      (W : uvis) (n0 n : nat) :
    (forall (N : uk_names Σ) (l : list fdstate) (n : nat),
       ukn_pay N = Q ->
       ⊢ upos γp n -∗ Ql (-1) -∗ UkSh.ush_wcp Wc Wb l n 0%nat -∗
         UkSh.ush_posb N γp T Wc Wb Pm l 0%nat) ->
    (forall x y : Z, Q x = Q y) ->
    tf_resume_pc (uvis_tf W) = (mword_of_int ShSyms.start : mword 64) ->
    shk_img_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 8192 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) mod 8 = 0 ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1) ->
    (forall j : nat, (j < 8 * (2 + (8 + (16 + (ush_Dbody + n0)))))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                     - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    uvis_cwd W = FsImg.ROOTINO ->
    uvis_lazy W = false ->
    □ (∀ γt γd γs : gname,
        usz γs (uvis_sz W) -∗
        ([∗ map] k ↦ b ∈ base.filter
              (fun kv : Z * bv 8 =>
                 kv.1 < uint (tf_resume_gpr0 (uvis_tf W) !!! Regidx csp_rs1)
                        - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
              (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)),
           ubyte γd k b) -∗
        |==> ∃ f : nat -> bv 8, R γt γd γs ∗ ubytes γd sh_buf sh_nbuf f) -∗
    udep -∗
    UkSh.sh_deps -∗
    UkSh.ush_tag_law T -∗
    sh_prompt_law Wc -∗
    (∀ N : uk_names Σ,
       ush_rest_l N γp T Wc Wb Pm (R (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    UkSh.ush_fd0 T (take NSTD (uvis_fd W)) -∗
    (□ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N T)
     ∨ (□ (∀ N : uk_names Σ, UkSh.ush_open_absent_leaf N T K) ∗ K)
     ∨ T) -∗
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') Q -∗ uslot W') -∗
    my_pay (uvis_gen W) Q -∗
    upos γp n -∗
    Ql (-1) -∗
    UkSh.ush_wcp Wc Wb (take NSTD (uvis_fd W)) n 0%nat -∗
    uslot W.
  Proof.
```
