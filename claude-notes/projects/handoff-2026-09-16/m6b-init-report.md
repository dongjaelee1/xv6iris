# lane M6B-INIT -- report

Checkout `/shared/xv6iris-2-sup`, branch `lane/m6b-init` on origin/main
`7348e5bd1` (code `b65275c81`).  Never pushed.  No claude-notes edited.

Terms.  A CREDENTIAL is the linear resource a process must hold to put a byte
on the console wire under the application's claim; a LAW is a persistent
(`□`) conversion of one credential into another; the FREE WRITE LAW
(`udepw_law 16`) is the flagged deposit that lets a `write(2)` count as paid
without any credential; the LEND is what init hands the shell it forks
(position `upos`, console lease `ucons_pay … Rdl (-1)`, a credential); the
REFUND is what the kernel hands back when a fork or exec fails; AFFINE means a
resource may be dropped with no obligation (Iris `iProp` is affine).

## Commits (both on `lane/m6b-init`, explicit paths, not pushed)

* (A) `b48cb3199` -- `die_dw` deleted on the wait leaf's -1 row.
  Files: `iris/UkInit.v`, `iris/UkInitMain.v`.
* (B) `6d87c8558` -- the two diagnostics through the links, the `Wp` lend, the
  refund at the lend's shape.  Files: NEW `iris/UkRunExecRef.v` (+ its bare
  `_CoqProject` row after `UkRunSys.v`), `iris/UkInit.v`, `iris/UkInitMain.v`,
  `iris/UInitKernel.v`, `iris/UInitSh.v`, `iris/UInitBoot.v`.

## (A) `die_dw`

`UkInit.wp_kinit_wait` calls `UkRunSys.wp_uk_ecall_wait_null_live` (not the
`_pid` twin -- see "Decisions") and hands its caller the row.  NEW statement:

```coq
  Lemma wp_kinit_wait (h : CpuId) (m : regfile) (avail : nat)
      (cs : gset gname) :
    uint (m !!! Regidx a0_idx) = 0 ->
    init_code γt -∗
    urun N h m (mword_of_int InitSyms.wait) avail -∗
    UserChildren.uch (ukn_ch N) cs -∗
    (∀ (h' : CpuId) (ret : mword 64) (cs' : gset gname),
       ⌜ret = (mword_of_int (-1) : mword 64) -> cs' = (∅ : gset gname)⌝ -∗
       uwait_ans ret cs cs' -∗
       urun N h' (<[Regidx a0_idx := ret]> (<[Regidx a7_idx := (mword_of_int 3 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       UserChildren.uch (ukn_ch N) cs' -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
```

In `UkInitMain.wp_kinit_main_loop`'s wait head the "wait itself failed" arm
(`bge a0,x0` not taken) is refuted: on `uwait_ans`'s reaping arm the pid is in
`[1, PIDMAX]`, so `sign_extend' 64 rv` is a small positive (`UmodeArith.
sext32_small`, `moi_ge_s`) and the `bge` was taken; on the -1 arm the row gives
`cs' = ∅`, the arm gives `cs' = cs`, and `γsh ∈ cs` (the shell's token) is the
contradiction.  Three pure `Z` lemmas at UkInitMain's top level carry the
arithmetic off the `mword` context: `pid_lt_Z31`, `pid_Z63`, `pid_geb0`
(`1 <= z <= PIDMAX -> …`; `Require Import ProcGeom` added).

DELETED: `UkInitMain.wp_kinit_main_die_dw` (its only user was the arm above,
now refuted) and the notation `LIT_WAIT := 0x9c8` (the 29-byte literal; the
instruction facts `uis_init_52..60` in `UCodeInit` are generated and stay).
lemma_diff: exactly these two GONE.

## (B) the two diagnostics through the links; the `Wp` lend

### The credential families init's walk carries (all opaque in `Uk*`)

* `Wp : nat -> iProp Σ` -- the ROUND-OPEN credential (top:
  `UInitDiag.kinit_pro (echo_taint γ) γ`), replacing the old `Wc : nat -> nat
  -> iProp Σ` parameter of init's walk everywhere (`UkInit.init_lend_cred`,
  `init_exec_sup_pos/_lend`, `init_cons_sup(_taint)`; `UkInitMain.kinit_ban_law`,
  `kinit_lent`, `wp_kinit_banner`, `wp_kinit_fork`, `wp_kinit_main_child`,
  `wp_kinit_main_loop`, `_from_1e`, `_repair_tail`, `_repair`, `wp_kinit_main`,
  `wp_kinit_start`; `UInitKernel.init_uexec_slot`, `init_slot_of_kexec`,
  `init_boot_pay`, `init_boot_con`).  The shell side keeps `Wc`; the two meet
  at `UInitSh.init_exec_sup_of_sh_slot`, which takes BOTH and the law
  `(forall n, ⊢ Wp n -∗ Wc n 0%nat)` (top: `UInitDiag.kinit_own_of_pro` then
  `UInitBanner.kinit_own_is_cred`).
* `Wb`, `Rdl` unchanged.

```coq
  Definition init_lend_cred (st : fdstate) (Wp Wb : nat -> iProp Σ)
      (l : list fdstate) (n : nat) : iProp Σ :=
    ((⌜l = ufd_l3 st⌝ ∗ Wp n) ∨ (⌜l = ufd_l0⌝ ∗ Wb n) ∨ True)%I.

  Definition init_lend_ref (cn : cons_names) (T : iProp Σ) (st : fdstate)
      (Wp Wb Rdl : nat -> iProp Σ) (γfd' : gname)
      (l : list fdstate) (γ : gname) (n : nat) : iProp Σ :=
    (UserFd.ustd γfd' l ∗ upos γ n ∗ ucons_pay cn γ T Rdl (-1)
     ∗ init_lend_cred st Wp Wb l n)%I.     (* NEW: what a failed exec refunds *)

  Definition init_exec_sup_pos (cn : cons_names) (T : iProp Σ) (st : fdstate)
      (Wp Wb Rdl : nat -> iProp Σ) (γ : gname) (n : nat) : iProp Σ :=
    (∀ (N' : uk_names Σ) (m : regfile) (pc : mword 64) (l : list fdstate),
       ⌜ ukn_pay N' = ucons_pay cn γ T (init_rd Rdl Wb) ⌝ -∗
       ⌜ m !!! Regidx a0_idx = (mword_of_int 0x9a8 : mword 64) ⌝ -∗
       ⌜ m !!! Regidx a1_idx = (mword_of_int 0x1000 : mword 64) ⌝ -∗
       init_rodata (ukn_t N') -∗ init_argv (ukn_d N') -∗
       UserFd.ustd (ukn_fd N') l -∗ UInitFd.ufd_row T st l -∗
       init_lend_cred st Wp Wb l n -∗ upos γ n -∗ ucons_pay cn γ T Rdl (-1) -∗
       udepw_at_refR N' m pc FsImg.ROOTINO
         (init_lend_ref cn T st Wp Wb Rdl (ukn_fd N') l γ n))%I.
```
(`init_exec_sup_lend cn T st Wp Wb Rdl := □ ∀ γ n, init_exec_sup_pos …`,
`init_cons_sup cn T Cns st Wp Wb Rdl` -- binder change only.)

```coq
  Lemma wp_kinit_exec (h : CpuId) (m : regfile) (avail : nat) (c : Z) (R : iProp Σ) :
    init_code γt -∗ urun N h m (mword_of_int InitSyms.exec) avail -∗ UserCwd.ucwd γcwd c -∗
    udepw_at_refR N (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m) (mword_of_int 0x3ac) c R -∗
    (∀ h' : CpuId, UserCwd.ucwd γcwd c -∗ R -∗
       urun N h' (<[Regidx a0_idx := (mword_of_int (-1) : mword 64)]>
                    (<[Regidx a7_idx := (mword_of_int 7 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗ WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
```
(was: `udepw_at_ref … -∗ (∀ h', ucwd -∗ ukn_pay N (-1) -∗ …)`.)

### The refund at the lend's shape -- NEW file `iris/UkRunExecRef.v`

WHY IT EXISTS (the finding the brief asked for): `init_exec_sup_of_sh_slot`'s
refund arm produced `ukn_pay N' (-1)` = `ucons_pay cn γ T (init_rd Rdl Wb) (-1)`
through `UkInit.init_pay_of_lend` (the affine arm) -- and it could produce
nothing else: `UkRun.udepw_at_ref` bakes the refund wand as `□ (sexec_refund
f -∗ ukn_pay N (-1))` (`UexecSG.sbundle_pay_ref`) and
`UkRunSys.wp_uk_ecall_exec_at_cwd` hands the caller exactly `ukn_pay N (-1)`.
The child's payload family IS the shell's exit family (`init_rd Rdl Wb`, which
the shell files unfold), and the round-open credential does not fit in it
(`Wb n ∨ True` cannot hold `Wp n`, and `Wb n` only exists AFTER the 21 bytes
are printed).  So the credential can only come back at its own shape, which
needs the exec leaf at a supplier-named refund.  Rather than editing
`UexecSG`/`UkRun`/`UkRunSys` (cones 134/75/70 files, the whole shell included),
the generalisation is a NEW leaf file after `UkRunSys.v`, cone = its consumers
only:

```coq
  Definition sbundle_pay_refR (X : uvis -d> iPropO Σ) (Q : Z -> iProp Σ)
      (R : iProp Σ) (W : uvis) : iProp Σ :=
    (∃ f : sfam, ⌜sexit_pay f = Q⌝ ∗ □ (sexec_refund f -∗ R)
                 ∗ sbundle_at X USYS_exec f W)%I.
  Lemma sbundle_pay_ref_of_refR X Q W : sbundle_pay_refR X Q (Q (-1)) W -∗ sbundle_pay_ref X Q W.
  Definition udepw_at_refR (N : uk_names Σ) (m : regfile) (pc : mword 64)
      (c : Z) (R : iProp Σ) : iProp Σ :=
    (∀ M pm sz fdv gn cs pidv, my_pay gn (ukn_pay N) -∗ uheap … -∗ ufd_auth … -∗
       uheap … ∗ ufd_auth … ∗ sbundle_pay_refR uslot (ukn_pay N) R
         (uvis_of_run m pc M pm sz fdv c gn cs pidv false))%I.
  Lemma udepw_at_ref_of_refR N m pc c : udepw_at_refR N m pc c (ukn_pay N (-1)) -∗ udepw_at_ref N m pc c.
  Lemma wp_uk_ecall_exec_at_cwd_refR (N) (h) (m) (pc) (avail) (c : Z) (R : iProp Σ) :
    usysno m = USYS_exec -> is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
    uinstr_is (ukn_t N) pc false (ECALL tt) -∗ urun N h m pc avail -∗ UserCwd.ucwd (ukn_cwd N) c -∗
    udepw_at_refR N m pc c R -∗
    (∀ h', UserCwd.ucwd (ukn_cwd N) c -∗ R -∗ urun N h' (<[a0 := -1]> m) (add_vec_int pc 4) avail -∗ WP Loop) -∗
    WP Loop.
```
The leaf's proof is `wp_uk_ecall_exec_at_cwd`'s verbatim (one name changed);
the original is the twin at `R := ukn_pay N (-1)`.  Folding the original into
UkRunSys as a restatement is a post-Qed cleanup (it costs the 70-file cone).
The intro twin `UInitSh.sbundle_pay_exec_intro_refR` (statement in the hunks
below) is `UexecExecInst.sbundle_pay_exec_intro_ref` with `□ (Rs -∗ R)`; it
lives in UInitSh because the new leaf file must not import the FS tower.

### The laws (UkInitMain)

```coq
  Definition kinit_ban_law (stc : fdstate) (Wp Wb : nat -> iProp Σ) : iProp Σ :=
    (□ (∀ n : nat, Wb n -∗ kinit_banner0 stc (Wp n)))%I.          (* was … (Wc n 0%nat) *)

  Definition kinit_diag_law (stc : fdstate) (Wp Wb : nat -> iProp Σ) : iProp Σ :=   (* NEW *)
    (□ (∀ (n : nat) (N' : uk_names Σ),
          Wp n -∗ UkInit.kinit_banner_pay N' stc 21%nat (init_lit LIT_EXEC) (Wb n))
     ∗ □ (∀ (n : nat) (N' : uk_names Σ),
            Wp n -∗ UkInit.kinit_banner_pay N' stc 18%nat (init_lit LIT_FORK) emp))%I.
```
`kinit_diag_law stc Wp Wb -∗` is a new premise right after `kinit_ban_law` in
`wp_kinit_main_loop`, `_from_1e`, `_repair_tail`, `_repair`, `wp_kinit_main`,
`wp_kinit_start`, and after `init_deps T` in `wp_kinit_main_child`; the
Löb hypothesis keeps it (persistent).  Top: `UInitDiag.kinit_execfail_law_holds`
/ `kinit_forkfail_law_holds`; the banner law is now
`UInitDiag.kinit_banner_law_pro_holds` (leaves `kinit_pro`), not
`UInitBanner.kinit_ban_law_holds` (which stays defined, unused at the top).

### The two die lemmas

```coq
  Lemma wp_kinit_main_die_df (N' : uk_names Σ) `{!ukn_const N'}
      (stc : fdstate) (Wp Wb : nat -> iProp Σ) (l : list fdstate) (np : nat)
      (hdf : CpuId) (mdf0 : regfile) (n : nat) :
    ukn_pay N' (-1) -∗ udepw_law 16 -∗ kinit_diag_law stc Wp Wb -∗
    init_code (ukn_t N') -∗ init_rodata (ukn_t N') -∗
    UserFd.ustd (ukn_fd N') l -∗ init_lend_cred stc Wp Wb l np -∗
    urun N' hdf mdf0 (mword_of_int 0x84) (12 + (12 + (4 + n))) -∗ WP Loop.

  Lemma wp_kinit_main_die_de (N' : uk_names Σ) `{!ukn_const N'}
      (T : iProp Σ) (stc : fdstate) (Wp Wb Rdl : nat -> iProp Σ)
      (cn : cons_names) (l : list fdstate) (γ : gname) (np : nat)
      (hde : CpuId) (mde0 : regfile) (n : nat) :
    ukn_pay N' = ucons_pay cn γ T (init_rd Rdl Wb) ->
    udepw_law 16 -∗ kinit_diag_law stc Wp Wb -∗
    init_code (ukn_t N') -∗ init_rodata (ukn_t N') -∗
    init_lend_ref cn T stc Wp Wb Rdl (ukn_fd N') l γ np -∗
    urun N' hde mde0 (mword_of_int 0xaa) (12 + (12 + (4 + n))) -∗ WP Loop.
```
Both build ONE per-byte family `∃ Ch` before the printf walk and spend
`UkInitPrintf.wp_kinit_printf_chain` once: on the lend's console arm (`l =
ufd_l3 stc`) from the law (`Ch 0` and the `□` per-byte steps of
`kinit_banner_pay`), on the closed row and the affine arm from
`UkInit.kinit_w1_of_law` at `Ch := fun _ => emp` (the free write law).
* `die_df` (18 bytes): the last token is `emp` on the console arm and is
  dropped; init then `exit(1)`s on its trivial payload (`Hpayfree`).  WHAT
  HAPPENS TO THE LEASE: the caller (`wp_kinit_main_loop`'s fork-failed arm)
  drops the refunded `upos γ np` and `ucons_pay cn γ T Rdl (-1)` on the floor.
  That is admitted by the logic (affine) and honest for the system: init's
  exit payload is `fun _ => True` (userinit forks it from nobody) and nothing
  reads the console once init has died.
* `die_de` (21 bytes): the family's closing wand yields `ukn_pay N' (-1)`.  On
  the console arm the last token is `UserFd.ustd … (ufd_l3 stc) ∗ Wb np` and
  the exit payload is REBUILT with the REAL `Wb np`: the lease's left arm is
  opened, `UserConsole.upos_agree` pins its count to `np` from the refunded
  `upos γ np`, and `ucons_pay_tok … (init_rd Rdl Wb) np (-1)` closes it with
  `init_rd_cred`'s LEFT arm; the lease's taint arm goes through
  `ucons_pay_taint`.  On the other two arms the exit is
  `UkInit.init_pay_of_lend` (the affine arm), as before.

### `wp_kinit_fork`'s -1 arm (parent post), NEW

```coq
        ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ UserChildren.uch γch Sc
          ∗ upos γ np ∗ ucons_pay cn γ T Rdl (-1)
          ∗ init_lend_cred stc Wp Wb l np)
         ∨ ∃ (γc : gname) (pidv : mword 32), … (unchanged) …)
```
(was `(⌜r = -1⌝ ∗ uch γch Sc)` with the leaf's `Rc` discarded.)  In the loop's
fork-failed branch the -1 arm feeds `die_df` its credential; the pid arm (a
negative return cannot be on it, but `UkFork`'s parent post carries no pid
range) feeds `die_df` the lend's `True` arm, i.e. the free law.

### `wp_kinit_main_child`
Gains `kinit_diag_law stc Wp Wb -∗` after `init_deps T -∗`; calls
`wp_kinit_exec … (init_lend_ref cn T stc Wp Wb Rdl (ukn_fd N') l γ np)` and
hands the refund to `die_de`.  The exec supply's ledger row `ustd (ukn_fd N')
l` now goes INTO the deposit (it used to be `iClear`ed at the supplier) so the
refund can return it.

### TRUSTED: `UInitKernel.init_boot_pay` -- OLD / NEW verbatim

OLD:
```coq
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Wc : nat -> nat -> iProp Σ) (Wb Rdl : nat -> iProp Σ)
      : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat ∗ Rdl 0%nat
     ∗ Wb 0%nat
     ∗ □ (∀ (n : nat) (N' : uk_names Σ),
            Wb n -∗ UkInitMain.kinit_banner0 N' stc (Wc n 0%nat)))%I.
```
NEW:
```coq
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Wp Wb Rdl : nat -> iProp Σ)
      : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat ∗ Rdl 0%nat
     ∗ Wb 0%nat
     ∗ □ (∀ (n : nat) (N' : uk_names Σ),
            Wb n -∗ UkInitMain.kinit_banner0 N' stc (Wp n))
     ∗ UkInitMain.kinit_diag_law stc Wp Wb)%I.
```
Read: the boot hands init the console dance, the reader token at 0, the read
credential at 0, the banner-owed credential at 0, the banner law (`Wb n` pays
the 18-byte banner at any record, leaving the round-open credential `Wp n`)
and the two diagnostic laws (`Wp n` pays the 21-byte / 18-byte diagnostic at
any record, leaving `Wb n` / nothing).  At the top `Wp := UInitDiag.kinit_pro
(echo_taint γ) γ`, `Wb := UInitBanner.kinit_ban …`, `Rdl := UShLine.ush_rd_pin γ`.
`Hsh_owed`, `sh_pay_rest`, EchoDisc: UNCHANGED (textually and in meaning).

### Every `∨ True` left in init's files, by name

1. `UkInit.init_rd_cred Wb n := (Wb n ∨ True)%I` -- the exit family's
   credential arm.  Obligation that kills it: EVERY exit of the shell hands
   back `Wb n` (the banner-owed credential at its boundary), i.e. lane
   STEP4-SH's `ush_wcp` third arm dies and every `ush_at`/`ush_gets_done`
   assembly reaches `UShLine.ush_at_of_mid_wb` (the left arm) rather than
   `ush_at_of_mid` (the right arm) -- plus the fork arm's re-entry and the
   wait redemption at `Wb n`.  The shell files (`UShLine` 505/544/559/577)
   unfold `init_rd_cred` by name, so its shape is theirs to change.
2. `UkInit.init_lend_cred`'s third arm `∨ True` -- NOT re-cut to `T`: the arm
   is built in `wp_kinit_banner` exactly where the token's credential arm is
   `init_rd_cred`'s `True` (line ~1110: `iDestruct "Hb" as "[Hb | _]" … iApply
   init_lend_cred_triv`), and there init holds neither a credential nor `T`.
   It dies with (1): once `init_rd_cred` is `Wb n`, `wp_kinit_banner`'s only
   credential-less case is the taint row, which has `T`, and the arm can be
   `T` (and then `UInitSh`'s entry lands it in `ush_wcp`'s taint/`True` arm).
   The two arms are ONE obligation.
No other `∨ True` in `UkInit`, `UkInitMain`, `UkRunExecRef`, `UInitDiag`,
`UInitBanner`, `UInitKernel`, `UInitFd`, `UserConsole`, `UInitSh`, `UInitBoot`.

### Spenders of `udepw_law 16` (init's free write law) that remain

* `UkInitMain.wp_kinit_main_die_df` and `_die_de`: the closed-ledger arm
  (`l = ufd_l0`: fd 1 closed, the write reaches no wire) and the lend's affine
  arm (item 2 above).  The console arm is paid through the link.
* `UkInitMain.wp_kinit_banner`: the same two arms plus the token's taint arm
  (`wp_kinit_printf`, unchanged since M6a).
* Definitions kept: `UkInit.init_deps T` (the bundle: `udepw_law 16 ∗ □ (T -∗
  udepw_law 15) ∗ □ (T -∗ udepw_law 17)`), `UkInit.wp_kinit_write`,
  `UkInit.kinit_w1_of_law`, `UkInitPrintf.wp_kinit_printf`.
The closed-fd arm could be paid honestly by `UkWriteClosed.kinit_w1_of_closed_l0`
(exists), but `UkWriteClosed` imports `UkSh`, so it can only reach `UkInitMain`
as a further opaque law premise -- not done here (not in the brief; the arm is
"writes nothing").

### `wp_kinit_wait` and the pid row -- decision
The brief's recipe was the `_pid` twin with `upid (ukn_pid N) 1`.  The row it
needs (`⌜r = -1 -> Sc' = ∅⌝`) is already on `wp_uk_ecall_wait_null_live`
(UkRunSys.v:2286), and init's entry constructor DROPS its pid fragment
(`UInitKernel.init_uexec_slot`: `iIntros (N h) "… Hchf _ Dlo _ Hrun"`, the
first `_` is `upid`), so the `_pid` route would have threaded a new premise
through seven walk lemmas and the constructor for nothing.  `_live` it is; the
`_pid` twin remains what a forked CHILD (which knows its pid is not 1) uses.

## Hunks in `iris/UInitSh.v` (12; full diffs saved as
`scratchpad/hunks-UInitSh.diff`)
1. `@@ -68,4 +68,7` header: `Require Import UkRunExecRef.` after `UkRun`.
2. `@@ -104,4 +107,8` header: `Require Import PieceFam.` and `FsBytesGamma.`
   after `PinnedExec` (the twin's statement names `pfam`/`MkPfam`/`fs_gamma_L`).
3. `@@ -922,4 +929,30` NEW lemma `sbundle_pay_exec_intro_refR` (statement above)
   immediately before `init_exec_sup_of_sh_slot`.
4. `@@ -948,4 +981,9` `init_exec_sup_of_sh_slot`: new binder `(Wp : nat ->
   iProp Σ)` after `(Wb …) {HWb}`, before `Rsh`.
5. `@@ -1029,4 +1067,9` new Coq-level premise after `Hbd`'s:
   `(forall n : nat, ⊢ Wp n -∗ Wc n 0%nat) ->`.
6. `@@ -1073,7 +1116,7` conclusion `UkInit.init_exec_sup_lend cn T st Wp Wb Rdl`;
   `intros … Hbd Hpw.`
7. `@@ -1085,5 +1128,5` `rewrite /udepw_at_refR` (was `/udepw_at_ref`).
8. `@@ -1107,5 +1150,4` the `iClear "Hstd"` after `ustd_agree` is gone (the
   ledger goes into the deposit).
9. `@@ -1113,20 +1155,10` the pre-bundle `iAssert (UkSh.ush_wcp …)` is removed
   (replaced by a comment).
10. `@@ -1178,9 +1210,33` `Hcon`: its `Pay` is `sh_pay ∗ upos γp np ∗ ucons_pay
    cn γp T Rdl (-1) ∗ (UserFd.ustd (ukn_fd N) l ∗ UkInit.init_lend_cred (FdOpen
    true true (FdDevice ConsoleInv.CONSOLE)) Wp Wb l np)`; inside it the old
    `ush_wcp` assembly, with the console arm through `Hpw np`; `iClear "Hstd'"`.
11. `@@ -1219,12 +1275,15` `pinned_exec_bundle` at the same `Pay`, framed with
    `Hstd Hcred` instead of `Hwcp`.
12. `@@ -1238,20 +1297,23` the refund: `sbundle_pay_exec_intro_refR uslot … (ukn_pay
    N) _ P Pmiss Fo Pay` with wand `iIntros "!> (_ & Hps & Hls & Hstd & Hcred)".
    rewrite /UkInit.init_lend_ref. iFrame …` (was `init_pay_of_lend`).
Nothing else in UInitSh changed (`sh_pay`, `sh_pay_rest`, `sh_Rsh`, the pins
lemmas untouched).

## Hunks in `iris/UInitBoot.v` (12; `scratchpad/hunks-UInitBoot.diff`)
1. `@@ -101,4 +101,8` header: `Require Import UInitDiag.` before `UInitBanner`.
2. `@@ -389,4 +393,7` `init_cons_sup_of_sh_slot`: binder `(Wp : nat -> iProp Σ)`
   after `Wb`.
3. `@@ -424,4 +431,7` premise `(forall n : nat, ⊢ Wp n -∗ Wc n 0%nat) ->` after
   `Hbd`'s.
4. `@@ -430,7 +440,7` conclusion `… st Wp Wb Rdl`; `intros … Hbd Hpw.`
5. `@@ -439,6 +449,6` the `UInitSh.init_exec_sup_of_sh_slot` application gains
   `Wp` (after `Wb`) and `Hpw` (after `Hbd`).
6. `@@ -822,7 +832,20` `echo_Hinit_boot`: `assert (Hpw : forall n, ⊢
   UInitDiag.kinit_pro (echo_taint γ) γ n -∗ EchoLinks.ewc_cred (echo_taint γ) γ
   (S gen_id) n 0%nat)` by `kinit_own_of_pro` + `rewrite <- kinit_own_is_cred`;
   `Hxs` stated at `(UInitDiag.kinit_pro (echo_taint γ) γ)` in `Wc`'s slot.
7. `@@ -831,9 +854,10` the `init_cons_sup_of_sh_slot` application gains
   `(UInitDiag.kinit_pro (echo_taint γ) γ)` and `Hpw`.
8-10. `@@ -869`, `-876`, `-892`: `Hcon`, `init_boot_con`, `init_boot_pay`
   instantiated at `(UInitDiag.kinit_pro (echo_taint γ) γ)` instead of
   `(EchoLinks.ewc_cred (echo_taint γ) γ (S gen_id))`.
11. `@@ -903,6 +927,13` the boot payment takes the three laws from `Hlks`:
    `UInitDiag.kinit_banner_law_pro_holds` (as `Hblaw`; was
    `UInitBanner.kinit_ban_law_holds`), `kinit_execfail_law_holds` (`Hxlaw`),
    `kinit_forkfail_law_holds` (`Hflaw`).
12. `@@ -922,5 +953,8` the payment's last conjuncts: `iSplitR; [iExact "Hblaw"|].
    rewrite /UkInitMain.kinit_diag_law. iSplitR; [iExact "Hxlaw" | iExact "Hflaw"]`.

## Files NOT touched
`UInitDiag.v`, `EchoLinksPro.v`, `UInitBanner.v`, `UInitFd.v`, `UserConsole.v`
(its cone is the whole shell), `UkInitPrintf.v`, `UkInitLit.v`, every shell
file, `UkRun.v`, `UkRunSys.v`, `UexecSG.v`, `UexecExecInst.v`.

## Gate
Builds in `-sup` (VM tree `_shared_xv6iris-2-sup`): `m6b-1` (A, one bullet
error), `m6b-2` (A: EXIT=0, COMPILED=20), `m6b-mk1..4` (B, `make
UkInitMain.vo`/`UInitBoot.vo` loops), `m6b-4` (B, full: EXIT=0, COMPILED=21).
Gate on `m6b-4` (= commit `6d87c8558`'s tree; local md5 of all seven changed
files equals the VM's):
```
grep -c "^Error" /tmp/m6b-4.log                                   -> 0
VM: make -f CoqMakefile -n | grep -c "ROCQ compile"                -> 0
VM: make audit-only 2>&1 | grep -v '^make\|^cd ' | md5sum         -> 57f7327206c4b276d05035342fea8ecf  (the thirteen)
python3 tools/lemma_diff.py --ref origin/main
  -> iris/UkInitMain.v  GONE Notation LIT_WAIT ; GONE Lemma wp_kinit_main_die_dw
     6 file(s) checked -- 2 thing(s) to justify   (both expected; no CHANGED,
     no Admitted/admit/Abort, no new axiom)
grep -n 'Admitted\|admit\.' <the seven files>                    -> none
./gcp-rocq/run-on-gcp --check-dumps
  -> the VM's tracked dumps match this checkout  (rc=0)
git status --porcelain                                            -> empty
```
`iris/_CoqProject`: one bare row `UkRunExecRef.v` after `UkRunSys.v`, no prose.

## Decisions the brief did not settle
1. `_live` instead of `_pid` for init's wait (above).
2. The refund generalisation as a NEW leaf file (`UkRunExecRef.v`) rather
   than editing `udepw_at_ref`/the exec leaf in place (cone 70-134 files
   including every shell file the sibling lane is editing).
3. `init_lend_cred`'s third arm stays `True` (above): the walk does not
   support `T` there.
4. The exec-supply now keeps the child's ledger fragment inside the deposit
   (`Pay`) so a failed exec can refund it; on a successful exec the shell's
   constructor drops it (the old record is replaced).
5. `kinit_diag_law` is ONE bundled persistent premise (two `□ ∀ n N'`
   conjuncts) threaded beside `kinit_ban_law`, and `init_boot_pay` names it
   as its LAST conjunct.
6. The fork-failed branch's pid disjunct (unreachable, unrefutable here)
   pays through the free law with the lend's `True` arm.
