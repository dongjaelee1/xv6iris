# Lane STEP4-SH -- report (checkout /shared/xv6iris-2-disc, branch lane/step4-sh)

Base: origin/main e4376a1c6 (M6B-INIT landed; merged --ff-only before (A)'s gate).
Commits (both green, gated, by explicit path):

* (A) `06f61205b`  IO-LEAF step 4 (A): the fork LENDS, the wait REDEEMS, PROLOGUE-ALTS-3 consumed
* (B) `ee1a0276e`  IO-LEAF step 4 (B): M4b(2) -- sh's own two diagnostics through the era's links

## 0. Vocabulary (plain concurrent-separation-logic and xv6 terms)

* a RESOURCE is a proposition of Iris's separation logic a process can own,
  hand over or split (`∗`); a WAND `P -∗ Q` consumes `P` and produces `Q`; a
  PERSISTENT resource (`□ P`) can be copied; an AFFINE arm is a disjunct
  `∨ True` under which a resource may be thrown away (the thing this lane
  kills); a LAW is a persistent wand taken as a premise and discharged once
  at the top (the application's instantiation, `UInitBoot`).
* the CONSOLE LEASE is what /init lends the shell it forks; its PIECES `Pm n`
  (`UShLine.ush_mid`) are what the shell holds between a line's bytes; its
  PAYLOAD `ush_at n = upos γp n ∗ ukn_pay N (-1)` is what the shell hands
  back at `exit` (`ukn_pay N (-1)`: the record's exit payload at status -1).
* `Wc n p` -- the shell's WRITE CREDENTIAL at input boundary `n` with `p`
  prompt bytes out (`p = 3`, NEW: the line's BLOCK is still owed, nothing
  chosen).  `Wb n` -- the BANNER-OWED credential (what a closed prompt
  leaves; /init's next round pays its banner from it).  `Wp n` -- the
  ROUND-OPEN credential /init lends (M6b).  All are opaque section
  parameters below the top; the instances are in §5.
* the LEDGER `l` is the shell's descriptor table restricted to the standard
  streams; `ush_fd0c`/`ush_fd1p`/`ush_fd2p l` say fd 0 / 1 / 2 is the console.
* the LEND `Rc` is what sh's fork hands its child; the child's PAYLOAD `Q` is
  what its exit hands back (redeemed by the parent's `wait`); the REFUND is
  what a failed `exec` hands the child back (the ledger fragment and the lend).
* `sh_deps` is the FREE WRITE LAW: a `write(2)` counted as paid without a
  credential (`UkSh.ksh_w_of_law`, `UkShDiag.ksh_w1_of_law`).
* the ERA'S LINKS (`EchoLinks.echo_links T γ`) are the per-byte protocol of
  the console output: a byte written at cursor `P` moves the era's credential
  from index `i` to `i+1` of the block it belongs to (`echo_blk_step`); the
  line's ALTERNATIVES `EchoDisc.line_alts` are the four blocks a round can
  print after the line: 0 = "hello world\n$ ", 1 = "exec echo failed\n$ ",
  2 = "$ " (nobody wrote), 3 = "fork\n" (the shell's own panic, no prompt).
* `T` is the TAINT: the persistent fact that the era is off the discipline;
  every credential has a taint arm, and a tainted walk pays everything.

## 1. What (A) did -- IO-LEAF step 4 core

### 1.1 The credential family (EchoLinksLine.v)

`ewc_lpr` gained a fourth index; everything below the top is stated at the
TIGHT family `EchoLinksLine.ewc_lcred` (the loose `EchoLinks.ewc_cred` is no
longer the shell's `Wc`):

```
Definition ewc_lpr (v : era_pins) (n p : nat) : iProp Σ :=
  match p with
  | O => ewc_line v n | S O => ewc_sp_t v n | S (S O) => ewc_open_t v n
  | _ => ewc_blk v n 0%nat 0%nat end.
Definition ewc_lcred (k : nat) (n p : nat) : iProp Σ := (∃ v, era_pin γ k v ∗ ewc_lpr v n p)%I.
Lemma ewc_lcred_blk_line (k n) : ewc_lcred k n 3 -∗ ewc_lcred k n 0.
Lemma ewc_lcred_taint (k n p) (v) : era_pin γ k v -∗ T -∗ ewc_lcred k n p.
Lemma ewc_lcred_of_post (k n) (v) : era_pin γ k v -∗ ewc_post v n 0 -∗ ewc_lcred k n 0.
Lemma ewc_lcred_blk_lend (k n) : ewc_lcred k n 3 -∗ ∃ v, era_pin γ k v ∗ ewc_blk v n 0 0.
Lemma ewc_lcred_blk_panic (k n) : ewc_lcred k n 3 -∗ ∃ v, era_pin γ k v ∗ ewc_panic v n 0.
```
About (argument orders): `ewc_line_of_pro T v n`, `ewc_blk_0_lend T v n a`,
`ewc_lcred_taint T γ k n p v`, `ewc_lcred_read T γ k n v`,
`ewc_lcred_blk_lend T γ k n`, `ewc_lcred_of_post T γ k n v`,
`ewc_lcred_blk_line T γ k n`, `ewc_lcred_blk_panic T γ k n`,
`EchoLinksBan.ewc_ban_line T v n`.

### 1.2 The command loop (UkSh.v)

New top-level ledger facts and the closed arm's shape:
```
Definition ush_fd1p (l : list fdstate) : Prop := exists rb, l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)).
Definition ush_lcl (l : list fdstate) (j : nat) : Prop :=
  (forall i, (i < j)%nat -> l !! i = Some (FdOpen true true (FdDevice CONSOLE)))
  /\ (forall i, (j <= i < NSTD)%nat -> l !! i = Some FdClosed).
```
New section hypotheses (all discharged at `UInitBoot.echo_Hinit_boot`, §5):
```
Hypothesis ush_wb_wc : forall n, ⊢ Wb n -∗ Wc n 0%nat.
Hypothesis ush_wc_blk_line : forall n, ⊢ Wc n 3%nat -∗ Wc n 0%nat.
Hypothesis ush_wb_read : forall n, ⊢ Pm (n + length echo_line) -∗ Wb n -∗ Pm (n + length echo_line) ∗ T.
Hypothesis ush_wc_read : forall n, ⊢ Pm (n + length echo_line) -∗ Wc (n + length echo_line) 3%nat  (* retargeted to 3 *)
```
The credential slot, the body state and the trusted obligation's inner state:
```
Definition ush_wcp (l : list fdstate) (n p : nat) : iProp Σ :=
  ((⌜ ush_fd0c l /\ ush_fd1p l /\ ush_fd2p l ⌝ ∗ Wc n p)
   ∨ (⌜ (exists j : nat, (j <= 2)%nat /\ ush_lcl l j) /\ (p < 3)%nat ⌝ ∗ Wb n)
   ∨ True)%I.
Lemma ush_wcp_cons (l k n) : length l = NSTD -> fd_lowest_closed l = Some k -> ush_wcp l n 0 -∗ ush_wcp (<[k := console]> l) n 0.
Lemma ush_posb_blk_line l : ush_posb l 3 -∗ ush_posb l 0.
Lemma ush_gets_line_of_posb l f : ush_posb l 2 -∗ ∃ n0, ush_gets_line l n0 0 f ∗ (ush_wcp l n0 2 ∨ T).
Definition ush_gets_done l i f := ((⌜i = 0⌝ ∗ ush_pos) ∨ (⌜i = length echo_line /\ ush_line_is f 0 i⌝ ∗ ush_posb l 3) ∨ (T ∗ ush_pos))%I.
Lemma ush_gets_done_line_t l n0 f : T -∗ Pm (n0 + 17) -∗ ush_gets_done l 17 f.
Definition ush_pstate l := (ush_std l ∗ UserCwd.ucwd γcwd FsImg.ROOTINO ∗ UserChildren.uch_any γch ∗ UserChildren.upid_any γpid ∗ ush_posb l 0%nat)%I.
Definition ush_bstate l := (… same … ∗ ush_posb l 3%nat)%I.
Lemma ush_pstate_of_bstate l : ush_bstate l -∗ ush_pstate l.
```
`ush_rest_l`'s inner premise is `ush_bstate l -∗` (TRUSTED SURFACE CHANGE:
`UInitSh.sh_pay_rest`'s obligation now hands the body the slot at index 3 and
the loop state with the cwd pinned at `FsImg.ROOTINO` and the pid row
`upid_any`; `sh_pay_rest`'s own text and binders are unchanged).
`wp_ksh_gets_loop` takes `(ush_wcp l n0 2 ∨ T)`; `wp_ksh_console/main/start`
take `UserChildren.upid_any γpid -∗` after `uch_any`.
About: `wp_ksh_start … (Hpsok_free Wc Wb ush_wb_wc ush_wc_blk_line Pm
ush_pm_of_at ush_at_of_pm ush_at_of_pm_taint ush_at_of_pm_wb ush_wb_read
ush_wc_read) cn ush_read_leaf (R K) h m f n0 l`; `ush_gets_done_line {Σ} N
{uartGhostG0} γp T {HT} (Wc Wb Pm ush_at_of_pm_taint ush_wb_read ush_wc_read)`;
`ush_wcp_cons {Σ} (Wc Wb ush_wb_wc) l (k n) _ _`; `ush_posb_blk_line … (Wc Wb
ush_wc_blk_line Pm) l`; `ush_posb`/`ush_pstate`/`ush_bstate`/`ush_rest_l`/
`ush_loop_head`/`ush_gets_done` binder lists unchanged from step 3.

### 1.3 The reader's receipt (UShLine.v)

`rd_res v n := ∃ ps0 cs0, ⌜rd_stage ps0 cs0 n⌝ ∗ turn_lb v (length (proc_upto ps0 cs0 n)) ∗ ps_lb v ps0 ∗ cs_lb v cs0`
(persistent, timeless) rides in `ush_rd_pin`, `ush_mid` and `ush_rd_in`; the
read leaf rebuilds it on its window arm.  New `ush_mid_wc_read_t` (lands at 3) and
```
Lemma ush_wb_read_holds (γ) (T) `{!Persistent T} `{!Timeless T} (γp n) :
  ush_mid γ γp (n + length echo_line) -∗ (∃ v, era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v n 0)
  -∗ ush_mid γ γp (n + length echo_line) ∗ T.
```
(the closed-prompt arm of `ush_gets_done_line` is REFUTED: a line read under
a banner-owed credential contradicts the receipt, `EchoLinks.wr_owed_read_refute`).

### 1.4 The wait's twin (UkShRun.v)
```
Lemma wp_kshr_wait_pid (N) `{!ukn_const N} (h m avail Sc p) :
  uint (m a0) = 0 -> shk_code -∗ urun … wait -∗ uch Sc -∗ upid (ukn_pid N) p -∗
  (∀ h' ret Sc' pidv, ⌜bv_unsigned pidv = p⌝ -∗ upid p -∗ ⌜ret = -1 -> Sc' = ∅⌝ -∗
     uwait_ans_pid ret Sc Sc' pidv -∗ urun … -∗ uch Sc' -∗ WP) -∗ WP.
```
(on `UkRunSys.wp_uk_ecall_wait_null_pid` / `UexecRet.uwait_ans_pid_mine`).

### 1.5 The fork arm (UkShFork.v) -- the lend, the payload, the redemption
```
Context `{HWct : forall n p, Timeless (Wc n p)}.
Definition ushf_wq (n : nat) : iProp Σ := (Wc n 3%nat ∨ Wc n 0%nat)%I.
Definition ushf_kill_law : iProp Σ := (□ (∀ n, riscv_kill_cred -∗ Wc n 0%nat))%I.
Definition ushf_child_law : iProp Σ := (□ (∀ N' h m dw dv s0 len g sz ld n np,
   ⌜ukn_pay N' = fun _ => ushf_wq np⌝ -∗ ⌜m s1 = s0⌝ -∗ ⌜ush_line_is g 0 len⌝ -∗ <bounds> -∗
   ⌜ush_fd0c ld ∧ ush_fd1p ld ∧ ush_fd2p ld⌝ -∗ shk_code -∗ shp_code -∗ shp_rodata -∗ ush_jtab -∗
   ustr line -∗ ustr ws -∗ ustr sy -∗ ustd ld -∗ ucwd ROOTINO -∗ uch_any -∗ ushm_fresh -∗
   Wc np 3 -∗ urun 0x9c0 (60 + (8 + (ush_Dg + n))) -∗ WP))%I.   (* (B): no sh_deps *)
Definition ushf_fans Sc Q Rc Sw := (⌜Sw = Sc⌝ ∗ Rc) ∨ (∃ γ pidc, ⌜Sw = Sc ∪ {[γ]}⌝ ∗ child_tok γ pidc Q).
```
The console arm of `wp_kshf_fork` calls the core at `Q := fun _ => ushf_wq np`,
`Rc := Wc np 3`, a killer pays via `ushf_kill_law` (taint); the child runs
the PAID echo entry through `ushf_child_law`; the parent waits at its own
pid; the wait's -1 arm is refuted against the live token; the reaping arm
REDEEMS (`ChildTok.gen_pay_timeless`) when the reaped generation is the
forked one.  Deleted: `ushf_pstate_at`, `ushf_pstate_of_at`, `wp_kshf_fork_any`
(no users; the arm is `wp_kshf_fork` alone), `UkShCd.wp_kshc_cd` (the cd arm
is refuted from the line fact in `wp_kshm_body`; helpers `ushc_bytes_sub`,
`ushc_ustr_of_bytes` kept for the child's line cut).

### 1.6 The paid child (UkShEcho.v, UEchoOut.v, UShEchoPay.v NEW)
```
Definition sh_exec_sup_echo (Q : Z -> iProp Σ) (Cr : iProp Σ) : iProp Σ :=
  (□ (∀ N' m pc s0 t g ld, ⌜ukn_pay N' = Q⌝ -∗ ⌜m a0 = s0⌝ -∗ ⌜m a1 = t + 8⌝ -∗ ⌜echo_argv_bytes g⌝ -∗
      ⌜UkSh.ush_fd1p ld⌝ -∗ UserFd.ustd (ukn_fd N') ld -∗ ush_cmd (ukn_d N') t (echo_cmd s0 g) -∗ Cr -∗
      udepw_at_refR N' m pc FsImg.ROOTINO (UserFd.ustd (ukn_fd N') ld ∗ Cr)))%I.
Definition sh_exec_sup_echo_wq Wc := □ ∀ np, sh_exec_sup_echo (fun _ => ushf_wq Wc np) (Wc np 3).
```
`UEchoOut.echo_uexec_slot_at … (rb) (Q) : (forall x y, Q x = Q y) -> … ->
□ (ech v ps0 cs0 n0 P 12 -∗ Q (-1)) -∗ era_pin -∗ echo_links -∗ udep -∗
my_pay (uvis_gen W) Q -∗ ech … 0 -∗ uslot W` (About: `T γ {Persistent0 PS} W v
ps0 cs0 n0 P rb Q _`); `kecho_pay_of_link` takes the wand instead of the
`echq` equation.  UShEchoPay.v: `echo_slot_of_kexec_at`,
`sh_exec_sup_echo_wq_holds : (⊢ □ riscv_kill_cred -∗ T) -> ⊢ echo_links T γ -∗
udep (PS := uprogSG_free) -∗ sh_echo_slot T -∗ UkShEcho.sh_exec_sup_echo_wq Wc`,
`ushf_kill_law_holds (v) : … era_pin -∗ UkShFork.ushf_kill_law Wc`,
`ushf_child_law_holds_at : … -∗ UkShFork.ushf_child_law (PS := uprogSG_free) Wc`.
Deleted `UShEcho.sh_exec_sup_of_echo_slot`, `_holds`, `_closed` (users: none
after the fork moved to the paid entry; UShEchoPay replaces them).
The parser tower (`wp_kshp_execcmd/parseexec/parsepipe/parseline/parsecmd/
parser`) takes an abstract exit resource `{Pex}` with `□ (Pex -∗ ukn_pay N (-1))`
(the null-store death pays with the lend); `UkShMain` passes the identity wand.

### 1.7 The entry (UShKernel.v, UInitSh.v, UInitBoot.v)

`sh_uexec_slot`/`sh_slot_of_kexec` gained Coq premises `Hwbwc : forall n, ⊢ Wb n
-∗ Wc n 0`, `Hwbl : forall n, ⊢ Wc n 3 -∗ Wc n 0`, `Hwbr : forall n, ⊢ Pm (n+17)
-∗ Wb n -∗ Pm (n+17) ∗ T`; `Hwc` targets 3; the constructor's `upid` fragment
feeds `wp_ksh_start` as `upid_any`.  The exact UInitSh.v (5 hunks) and
UInitBoot.v (9 hunks) diffs are saved verbatim at
`scratchpad/step4-hunks-UInitSh.diff` and `scratchpad/step4-hunks-UInitBoot.diff`
(summary: UInitSh -- `Hwc` retargeted to 3 and the three law premises added
after it; the slot's console arm proves three rows (`ufd_l3_row1`), its closed
arm `exists 0; split; [lia | exact ufd_l0_lcl]` with new `Lemma ufd_l0_lcl :
UkSh.ush_lcl UInitFd.ufd_l0 0`; `sh_slot_of_kexec` passes `Hwbwc Hwbl (Hwbr γp)`.
UInitBoot -- imports `mono_nat`, UShPanic, EchoLinksPro, EchoLinksLine,
EchoLinksBan; `init_cons_sup_of_sh_slot` mirrors the three laws; the family
is `EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id)`; `Hsh_wc` via
`ush_mid_wc_read_t`; `Hplaw` via `UShPanic.sh_prompt_law_holds_line`; `Hpw`
via `ewc_line_of_pro`; new `Hsh_wbwc` (`EchoLinksBan.ewc_ban_line`), `Hsh_wbl`
(`ewc_lcred_blk_line`), `Hsh_wbr` (`ush_wb_read_holds`); the boot residue
`rd_res v0 0` is extracted from `echo_turn` and put into `Rdl 0`).
(B) touches neither file.

## 2. What (B) did -- M4b(2): sh's own diagnostics through the links

### 2.1 fork1's panic is the CALLER's (UkShRun.v)

`wp_kshr_fork1_tail` (Local) takes `(X : iProp Σ)` in place of the borrowed
exit payload, carries it through both arms, and hands the panic to a new
continuation; `wp_kshr_fork1` takes `(Pex : iProp Σ)` and a panic continuation;
neither takes `UkSh.sh_deps` any more:
```
Lemma wp_kshr_fork1 (N : uk_names Σ) `{!ukn_const N}
    (P : gname -> gname -> gname -> iProp Σ) `{FP : !Forkable P}
    (szv : Z) (l : list fdstate) (D : gmap nat fdstate)
    (h : CpuId) (m : regfile) (n : nat) (cw : Z)
    (Sc : gset gname) (Q : Z -> iProp Σ) (Rc : iProp Σ) (Pex : iProp Σ) :
  (forall x y : Z, Q x = Q y) ->
  shk_code (ukn_t N) -∗ shk_rodata (ukn_t N) -∗ P (ukn_t N) (ukn_d N) (ukn_s N) -∗ usz (ukn_s N) szv -∗
  UserFd.ustd (ukn_fd N) l -∗ UserCwd.ucwd (ukn_cwd N) cw -∗ UserChildren.uch (ukn_ch N) Sc -∗
  ([∗ map] fd ↦ st ∈ D, UserFd.ufd (ukn_fd N) fd st) -∗
  Rc -∗ □ (riscv_kill_cred -∗ Q (-1)) -∗
  Pex -∗
  urun N h m (mword_of_int ShSyms.fork1) (2 + (Dg + n)) -∗
  ((∀ (h' : CpuId) (m' : regfile) (r : mword 64),
      ⌜ uint (m' !!! Regidx a0_idx) = 0x1298 ⌝ -∗
      ⌜ r = (mword_of_int (-1) : mword 64) ⌝ -∗
      ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ UserChildren.uch (ukn_ch N) Sc ∗ Rc)
       ∨ ∃ (γ : gname) (pidv : mword 32), ⌜r = (sign_extend' 64 pidv : mword 64)⌝ ∗
           child_tok γ pidv Q ∗ UserChildren.uch (ukn_ch N) (Sc ∪ {[γ]})) -∗
      UserFd.ustd (ukn_fd N) l -∗ Pex -∗
      urun N h' m' (mword_of_int ShSyms.panic) (Dg + n) -∗ WP (Loop : expr riscv_lang)) ∗
   (<the parent continuation as before, with Pex in place of ukn_pay N (-1)>) ∗
   (<the child continuation, unchanged>)) -∗
  WP (Loop : expr riscv_lang).
```
The tail's panic continuation is `∀ h' m', ⌜uint (m' a0) = 0x1298⌝ -∗ ⌜mt a0 =
-1⌝ -∗ X -∗ urun N h' m' panic (Dg + n) -∗ WP` (the `-1` from the taken
`beq`, `eq_vec_true_iff`).  `wp_kshr_fork1_any` keeps its statement (it still
takes `sh_deps`): it passes `Pex := ukn_pay N (-1)` and pays the panic on the
free law (`ush_diag_leaf`) -- runcmd's LIST/BACK arms, generic runner.
`UkShDiag.wp_kshr_fork1_final` mirrors (binders `… Sc Q Rc Pex _`, no
`sh_deps`); `UkShDiag.shd_msg_str` is no longer `Local`.

### 2.2 The two laws and the two paid walks (UkShDiag.v)
```
Definition ush_panic_law (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ) : iProp Σ :=
  (□ (∀ (N : uk_names Σ) (n : nat) (l : list fdstate),
        ⌜ UkSh.ush_fd2p l ⌝ -∗ Wc n 3%nat -∗
        ∃ Pf : nat -> iProp Σ,
          Pf 0%nat
          ∗ □ (∀ (p : nat) (b : bv 8), ⌜ line_alts !!! 3%nat !! p = Some b ⌝ -∗
                 ksh_w1 N (mword_of_int 2 : mword 64) b
                   (UserFd.ustd (ukn_fd N) l ∗ Pf p) (UserFd.ustd (ukn_fd N) l ∗ Pf (S p)))
          ∗ □ (Pf 5%nat -∗ Wb n)))%I.

Definition ush_execfail_law (Cr Cd : iProp Σ) : iProp Σ :=
  (□ (∀ (N : uk_names Σ) (l : list fdstate),
        ⌜ UkSh.ush_fd2p l ⌝ -∗ Cr -∗
        ∃ Pf : nat -> iProp Σ,
          Pf 0%nat
          ∗ □ (∀ (p : nat) (b : bv 8), ⌜ line_alts !!! 1%nat !! p = Some b ⌝ -∗
                 ksh_w1 N (mword_of_int 2 : mword 64) b
                   (UserFd.ustd (ukn_fd N) l ∗ Pf p) (UserFd.ustd (ukn_fd N) l ∗ Pf (S p)))
          ∗ □ (Pf 17%nat -∗ Cd)))%I.

Lemma wp_kshd_panic_paid (N : uk_names Σ) `{!ukn_const N}
    (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
    (l : list fdstate) (h : CpuId) (m : regfile) (n np : nat) :
  UkSh.ush_fd2p l -> uint (m !!! Regidx a0_idx) = 0x1298 ->
  ush_panic_law Wc Wb -∗ shk_code (ukn_t N) -∗ shk_rodata (ukn_t N) -∗
  UserFd.ustd (ukn_fd N) l -∗ Wc np 3%nat -∗
  (UserFd.ustd (ukn_fd N) l -∗ Wb np -∗ ukn_pay N (-1)) -∗
  urun N h m (mword_of_int ShSyms.panic) (ush_Dg + n) -∗ WP (Loop : expr riscv_lang).

Lemma wp_kshd_execfail_paid (N : uk_names Σ) `{!ukn_const N}
    (Cr Cd : iProp Σ) (l : list fdstate) (h : CpuId) (m : regfile) (n : nat) (x : uarg) :
  UkSh.ush_fd2p l -> uint (m !!! Regidx s1_idx) mod 8 = 0 -> ua_len x = 4%nat ->
  (forall j : nat, (j < 4)%nat -> ua_bytes x j = echo_line !!! j) ->
  ush_execfail_law Cr Cd -∗ shk_code (ukn_t N) -∗ shk_rodata (ukn_t N) -∗
  UkShRun.ush_ptr (ukn_d N) (uint (m !!! Regidx s1_idx) + 8) (ua_ptr x) -∗ UkShRun.ush_str (ukn_d N) x -∗
  UserFd.ustd (ukn_fd N) l -∗ Cr -∗
  (UserFd.ustd (ukn_fd N) l -∗ Cd -∗ ukn_pay N (-1)) -∗
  urun N h m (mword_of_int 0xda) (ush_Dg + n) -∗ WP (Loop : expr riscv_lang).
```
Closed byte facts (all `vm_compute`): `ush_fork_msg_len : length (line_alts
!!! 3) = 5`, `ush_fork_msg_byte p : p < 4 -> shd_lit 0x1298 p = line_alts !!! 3
!!! p`, `ush_fork_msg_nl : shd_lit 0x1290 2 = line_alts !!! 3 !!! 4`,
`ush_fork_msg_lookup`; `ush_bytes_of_forallb` (a run of byte equalities from
one `forallb … (seq lo cnt) = true`), `ush_execfail_len : length (line_alts
!!! 1) = 19`, `ush_execfail_lookup`, `ush_execfail_w1 : ∀ p, 0 <= p < 0+5 ->
shd_lit 0x12a8 p = line_alts !!! 1 !!! p`, `ush_execfail_arg : ∀ j, 0 <= j <
0+4 -> echo_line !!! j = line_alts !!! 1 !!! (5 + j)`, `ush_execfail_w2 : ∀ p,
7 <= p < 7+8 -> shd_lit 0x12a8 p = line_alts !!! 1 !!! (p + 2)`.  Both walks
are `wp_kshd_panic_chain` / `wp_kshd_die_chain` at the families `C1/C2/C3 :=
ustd l ∗ Pf (index)`, so `ksh_w1_of_law` (the free law's byte) is not applied.

### 2.3 The discharges at the era's links (UShPanic.v, EchoLinksLine.v)
```
Lemma ewc_lcred_of_post_a (k n a : nat) (v) : (a < 3)%nat -> era_pin γ k v -∗ ewc_post v n a -∗ ewc_lcred k n 0%nat.
Lemma ewc_lcred_blk_open (k n a : nat) : ewc_lcred k n 3%nat -∗ ∃ v, era_pin γ k v ∗ ewc_blk v n a 0%nat.

Lemma ksh_w1_of_link_blk (N) (v) (n) (l) (rb) (a i : nat) (b : bv 8) :
  l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) -> line_alts !!! a !! i = Some b ->
  era_pin γ (S gen_id) v -∗ echo_links T γ -∗
  UkShDiag.ksh_w1 N (mword_of_int 2) b (ustd (ukn_fd N) l ∗ EchoLinksLine.ewc_blk T v n a i)
                                        (ustd (ukn_fd N) l ∗ EchoLinksLine.ewc_blk T v n a (S i)).
(* ksh_w1_of_link_panic is now the instance at a = 3, statement unchanged *)

Lemma ush_panic_law_holds :
  echo_links T γ -∗
  UkShDiag.ush_panic_law (EchoLinksLine.ewc_lcred T γ (S gen_id))
    (fun n => ∃ v, era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v n 0%nat)%I.
      (* the second argument IS UInitBanner.kinit_ban T γ, spelled out *)
Lemma ush_execfail_law_holds (n : nat) :
  echo_links T γ -∗
  UkShDiag.ush_execfail_law (EchoLinksLine.ewc_lcred T γ (S gen_id) n 3%nat)
                            (EchoLinksLine.ewc_lcred T γ (S gen_id) n 0%nat).
```

### 2.4 The fork arm pays "fork\n" from the lend (UkShFork.v)

`wp_kshf_fork_core` (Local) takes `(Pex : iProp Σ)` in place of the exit
payload and a panic continuation `∀ Sc h' m' r, ⌜uint (m' a0) = 0x1298⌝ -∗
⌜r = -1⌝ -∗ <fork answer> -∗ ustd γfd l -∗ Pex -∗ urun N h' m' panic (ush_Dg +
(66 + n)) -∗ WP`; its re-entry takes `Pex -∗ ◇ ush_posb l 0` and no `sh_deps`.
`wp_kshf_fork`, `wp_kshm_body`, `ushf_rest_of_body` gained the Coq premise
`(forall i, UkSh.ush_bnd i -> ⊢ Pm i -∗ Wb i -∗ UkSh.ush_at N γp i)` (the
loop's own `ush_at_of_pm_wb`; a premise of the DISCHARGER, not of the
trusted obligation `ush_rest_l`) and the Iris premise `UkShDiag.ush_panic_law
Wc Wb -∗` after `ushf_child_law`.  On the CONSOLE arm the core is entered at
`Pex := Pm np` (the pieces, no payload assembled up front): the panic's
`-1` row pays the five bytes from `Rc = Wc np 3` through `wp_kshd_panic_paid`
and the exit through `ush_at_of_pm_wb np` on the `Wb np` the message
leaves; the re-entry gets `Pm np` back and no longer round-trips through
`ush_at_of_pm`/`ush_pm_of_at` (the taint sub-arms of the redemption are gone
with it; the not-my-child arm is `ush_posb_of_wc` at `ush_wcp`'s third arm).
The AFFINE/TAINT arm passes `Pex := ukn_pay N (-1)` and pays the panic on the
free law as before.

### 2.5 The exec-failed child pays "exec echo failed\n" from the refund (UkShEcho.v, UShEchoPay.v)
```
Definition wp_kshr_exec_echo (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) : Prop :=
  forall N (Hc : ukn_const N) h m t szv s0 g ld n,
    ukn_pay N = Q -> m a0 = t -> echo_argv_bytes g -> UkSh.ush_fd1p ld -> UkSh.ush_fd2p ld ->
    ⊢ shk_code (ukn_t N) -∗ sh_exec_sup_echo Q Cr -∗
      UkShDiag.ush_execfail_law Cr Cd -∗ □ (Cd -∗ Q (-1)) -∗
      ush_jtab -∗ ush_cmd (ukn_d N) t (echo_cmd s0 g) -∗ usz -∗ ustd ld -∗ ucwd ROOTINO -∗ uch_any -∗ Cr -∗
      urun N h m runcmd (6 + (2 + (ush_Dg + n))) -∗ WP.
Definition wp_kshm_child_echo (Q : Z -> iProp Σ) (Cr Cd : iProp Σ) : Prop :=
  … UkSh.ush_fd1p ld -> UkSh.ush_fd2p ld ->
    ⊢ shk_code -∗ sh_exec_sup_echo Q Cr -∗ □ (Cr -∗ Q (-1)) -∗
      UkShDiag.ush_execfail_law Cr Cd -∗ □ (Cd -∗ Q (-1)) -∗ shp_code -∗ … -∗ Cr -∗ urun 0x9c0 … -∗ WP.
Definition ush_execfail_law_wq (Wc) : iProp Σ := (□ (∀ np, UkShDiag.ush_execfail_law (Wc np 3%nat) (Wc np 0%nat)))%I.
Lemma ushf_child_law_holds (Wc) : ush_execfail_law_wq Wc -∗ sh_exec_sup_echo_wq Wc -∗ UkShFork.ushf_child_law Wc.
```
Neither runner takes `UkSh.sh_deps` any more (nothing on the paid child's walk
spends it: the parser tower's death pays with `Cr`, the failed exec's
diagnostic through the links, the exit with `Cd`).  `UShEchoPay.
ushf_child_law_holds_at` (statement unchanged) discharges the new law from
`UShPanic.ush_execfail_law_holds` at every `np`, PINNED `(PS := uprogSG_free)`
(left to instance search the assertion lands at another `uprogSG` and the
final `iApply` unfolds the child law for ~40 minutes without returning --
found by bisection with truncated probe copies; the pin is the fix).

"open %s failed" (0x10e): UNREACHABLE on the paid walk -- `echo_cmd` is a
`UExec`, so runcmd's REDIR arm (the only site of 0x10e) is never entered by
the paid child; it is still on the free law in the generic runner.
"cannot cd": REFUTED in (A) (`wp_kshm_body`, the first byte is 'e').

## 3. `About` binder lists (B)

(`About … Arguments` lines, printed at width 200; a trailing cut means the
explicit binders continue as in the statement)

```
Arguments wp_kshr_fork1 {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1} Dg%nat_scope {ctokG0 SG PS} N {ukn_const0} P%function_scope {FP} szv%Z_scope l%list_scope D h m n%nat_scope 
Arguments wp_kshr_fork1_final {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} N {ukn_const0} P%function_scope {FP} szv%Z_scope l%list_scope D h m n%nat_scope cw%Z_scope 
Arguments ush_panic_law {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} (Wc Wb)%function_scope
Arguments ush_execfail_law {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} (Cr Cd)%bi_scope
Arguments wp_kshd_panic_paid {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} N {ukn_const0} (Wc Wb)%function_scope l%list_scope h m (n np)%nat_scope _ _
Arguments wp_kshd_execfail_paid {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} N {ukn_const0} (Cr Cd)%bi_scope l%list_scope h m n%nat_scope x _ _ _ _%function_scope
Arguments shd_msg_str {Σ riscvGS0} gt gd dq a%Z_scope len%nat_scope _ _
Arguments ksh_w1_of_link_blk {Σ riscvGS0 xv6G0 fileG0 ufdG0 GEN ghost_varG0 ghost_varG1 echoOutG0} T%bi_scope γ {Persistent0 PS} N v n%nat_scope l%list_scope rb%bool_scope 
Arguments ush_panic_law_holds {Σ riscvGS0 xv6G0 fileG0 ufdG0 GEN ghost_varG0 ghost_varG1 echoOutG0} T%bi_scope γ {Persistent0 PS}
Arguments ush_execfail_law_holds {Σ riscvGS0 xv6G0 fileG0 ufdG0 GEN ghost_varG0 ghost_varG1 echoOutG0} T%bi_scope γ {Persistent0 PS} n%nat_scope
Arguments wp_kshf_fork {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1} N {Hpay uartGhostG0} γp T%bi_scope {HT} (Wc Wb Pm)%function_scope {ctokG0 SG PS} Hpsok_free%function_scope 
Arguments wp_kshm_body {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1} N {Hpay uartGhostG0} γp T%bi_scope {HT} (Wc Wb Pm)%function_scope {ctokG0 SG PS} Hpsok_free%function_scope 
Arguments ushf_rest_of_body {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1} N {Hpay uartGhostG0} γp T%bi_scope {HT} (Wc Wb Pm)%function_scope {ctokG0 SG PS} Hpsok_free%function_scope
Arguments ushf_child_law {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1} Wc%function_scope {ctokG0 SG PS}
Arguments wp_kshr_exec_echo {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} Q%function_scope (Cr Cd)%bi_scope
Arguments wp_kshm_child_echo {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} Q%function_scope (Cr Cd)%bi_scope
Arguments ush_execfail_law_wq {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} Wc%function_scope
Arguments ushf_child_law_holds {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1 ctokG0 SG PS} (Hpsok_free Wc)%function_scope
Arguments ushf_child_law_holds_at {Σ riscvGS0 xv6G0 fileG0 ufdG0 GEN ghost_varG0 ghost_varG1 echoOutG0} T%bi_scope γ {HPT HTT} _
Arguments ewc_lcred_of_post_a {Σ echoOutG0} T%bi_scope γ (k n a)%nat_scope v _
Arguments ewc_lcred_blk_open {Σ echoOutG0} T%bi_scope γ (k n a)%nat_scope
```

## 4. Every `∨ True` left in the shell's files, with its killer

1. `UkSh.ush_wcp l n p`'s third arm (`∨ True`).  Two producers remain:
   (a) `UInitSh.init_exec_sup_of_sh_slot`'s mapping of `UkInit.init_lend_cred`'s
   affine arm at the entry -- killer: the init side deletes that arm (the
   coordinator's merge item; every shell exit now hands back `Wb n` or the
   taint, see §7); (b) `UkShFork.wp_kshf_fork`'s re-entry when the reaped
   generation is not the forked one -- killer: two rows on the exec seam
   (`SpecKexec.exec_slot_pre` / `PinnedExec.pinned_exec_bundle`): `uvis_ch W'
   = ∅` and `uvis_pid W' = pidv` (`pidv ≠ 1`) for sh's exec'd key, threaded
   from the fork child's facts (UkInitMain:954 drops `∃ p, ⌜p <> 1⌝ ∗ upid`).
2. `UShLine.ush_rd_x` = `UkInit.init_rd_cred`'s `∨ True` (init side, not
   this lane's file): consumed by `ush_at_of_pm` (the affine assembler) at
   `ush_gets_done_0`'s affine arm and at the fork arm's pid-sub-arm fallback
   (§5.2) -- killer: the coordinator kills `init_rd_cred`'s arm once every
   exit hands back `Wb n` (§7).
3. `UkSh.ush_wcp_triv`'s propagation at `ush_gets_done_line`'s affine arm --
   dies with 1(a).
No new `∨ True` was introduced by (A) or (B).

## 5. Remaining spenders of `sh_deps` (the free write law)

After (B) the paid shell's own diagnostics spend it nowhere; what remains:
* `UkSh.ksh_w_of_wcp` -- the prompt on `ush_wcp`'s `True` arm (dies with §4.1);
* `UkSh.wp_ksh_getcmd`'s taint arm (a tainted turn writes on the free law);
* `UkShFork.wp_kshf_fork`, console arm, the fork answer's PID sub-arm at
  `sign_extend' 64 pidv = -1` (pidv = 0xFFFFFFFF) -- pays the panic on
  `ush_diag_leaf_holds` with the affine assembler `ush_at_of_pm`; killer: a
  pid-range row (`bv_unsigned pidv < 2^31`) in `UkFork.wp_uk_ecall_fork`'s
  parent post (xv6 pids are positive ints);
* `UkShFork.wp_kshf_fork`, affine/taint arm -- the generic child walk
  (`UkShMain.wp_kshm_child_alloc`) and its fork panic (`ush_diag_leaf_holds`);
* `UkShRun.wp_kshr_fork1_any` (runcmd's LIST/BACK arms) and `wp_kshr_runcmd`'s
  EXEC-returning / REDIR-failing arms via `ush_diag_leaf` -- the GENERIC
  runner, never entered by the paid child;
* every `UkShDiag.ksh_w1_of_law` site inside `ush_diag_leaf_holds`,
  `wp_kshd_panic`, `wp_kshd_die` and the printf tower's free-law corollaries
  (generic diagnostics; the paid walks use the `_chain` lemmas at a family);
* `UShKernel.sh_uexec_slot` hands `sh_deps` to `wp_ksh_start` (the loop
  itself: prompts on the closed arm are `UkWriteClosed.ksh_w_of_closed`, not
  the free law; the free law reaches only the sites above);
* init side (not this lane): `UkInit.kinit_w1_of_law`, the generic echo entry
  `UShEcho.echo_slot_of_kexec` (udepw_law at row 16).

## 6. Gate lines

(A), build s4-5: COMPILED=30 EXIT=0; ERRORS=0; MAKE_N=0 (`make -n` prints no
`ROCQ compile`); audit md5 57f7327206c4b276d05035342fea8ecf; source md5 local
= VM; no Admitted; lemma_diff: 7 GONE (UShEcho.sh_exec_sup_of_echo_slot,
_holds, _closed; UkShCd.wp_kshc_cd; UkShFork.ushf_pstate_at,
ushf_pstate_of_at, wp_kshf_fork_any -- users listed in §1.5/§1.6) + 3
NEWAXIOM (UkSh.ush_wb_wc, ush_wc_blk_line, ush_wb_read -- section
hypotheses, discharged at UInitBoot.echo_Hinit_boot as Hsh_wbwc, Hsh_wbl,
Hsh_wbr); --check-dumps clean.

(B), build s4-8: COMPILED=15 EXIT=0; ERRORS=0 (zero `^Error` in /tmp/s4-8.log);
MAKE_N=0 (`make -f CoqMakefile -n` prints no `ROCQ compile`); audit md5
57f7327206c4b276d05035342fea8ecf (the thirteen, unchanged); source md5 local =
VM for all seven changed files; `grep '^\s*Admitted\.' iris/*.v` = 0;
`python3 tools/lemma_diff.py --ref origin/main`: the same 10 items as (A) --
7 GONE + 3 NEWAXIOM, all justified above; nothing new from (B) (the changed
statements keep their names: wp_kshr_fork1, wp_kshr_fork1_final, wp_kshf_fork,
wp_kshm_body, ushf_rest_of_body, ushf_child_law, wp_kshr_exec_echo,
wp_kshm_child_echo, ushf_child_law_holds, ksh_w1_of_link_panic's proof);
`./gcp-rocq/run-on-gcp --check-dumps`: "the VM's tracked dumps match this
checkout".  Build logs: scratchpad/s4-6.out (B1 alone, green), s4-7 (killed:
the UShEchoPay hang, §2.5), s4-8 (the gate).

## 7. For the coordinator: do all shell exits hand back `Wb n`?

NOT YET, but closer.  Exits of the paid shell now: (i) the shut-fd-0 exit
(`ush_at_of_pm_wb`, `Wb n`); (ii) the fork panic on the console arm
(`ush_at_of_pm_wb`, `Wb n` -- NEW in (B)); (iii) the fork panic's pid sub-arm
(§5, `ush_at_of_pm`, affine -- needs the pid-range row); (iv) the affine arm
of `ush_gets_done_0` and the fork's affine/taint arm (`ush_at_of_pm` /
taint).  So `init_rd_cred`'s `∨ True` cannot be killed yet; it can once (iii)
gets its row and (iv)'s affine arm dies with §4.1.

## 8. Decisions this brief did not settle

* `p = 3` as the block-owed index (kept apart from 0 because `ewc_line` is a
  disjunction the fork cannot undo); the tight family `ewc_lcred` as `Wc`.
* The cwd pinned at `FsImg.ROOTINO` inside `ush_pstate` (R3(2)); the pid row
  `upid_any` in the loop state; the body state at slot index 3.
* `UkShCd.wp_kshc_cd` deleted rather than kept dead.
* The parser tower's abstract `{Pex}` exit instead of a payload equation.
* Wait redemption's not-my-child arm left affine (exec-seam rows, §4.1b).
* The reader's receipt residue `rd_res` inside `ush_mid` (so `ush_wb_read`
  is refutable at all).
* (B): the panic is the CALLER's in `wp_kshr_fork1` (an `X`/`Pex` threaded
  through the tail) rather than a law inside UkShRun; the laws are stated at
  abstract `Wc/Wb` (`ush_panic_law`) and at abstract ends `Cr/Cd`
  (`ush_execfail_law`) so the runners stay opaque in the family; `sh_deps`
  dropped from fork1, the fork core, `ushf_child_law` and both paid runners
  because nothing on them spends it; `ksh_w1_of_link_panic` generalised to
  `ksh_w1_of_link_blk` (name kept as the a = 3 instance).
* `ush_at_of_pm_wb` reaches the fork arm as a premise of `ushf_rest_of_body`
  (the discharger), NOT of the trusted `ush_rest_l`; `sh_pay_rest` unchanged.

## 9. Where a successor picks up

Both commits are green.  Next in the brief's order: nothing of step 4 is
left in this lane; the residuals are the exec-seam rows (§4.1b), the
pid-range row (§5), and the init-side arms (§4.2, §7).
