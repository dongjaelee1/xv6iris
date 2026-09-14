# Lane STEP3-SH -- report (checkout /shared/xv6iris-2-disc, branch lane/step3-sh)

Vocabulary used below (plain concurrent-separation-logic and xv6 terms):

* a RESOURCE is a proposition of Iris's separation logic that a process can
  own, hand over or split (`∗`); a WAND `P -∗ Q` consumes `P` and produces `Q`;
  a PERSISTENT resource (`□ P`) can be copied; an AFFINE arm is a disjunct
  `∨ True` that lets a resource be thrown away, which is what step 4 kills.
* the CONSOLE LEASE is what /init lends the shell at its fork: the shell's half
  of the console POSITION PAIR (`upos γp n` -- the shell's cursor into the
  console input, at input count `n`), the console ring's reader token and the
  era's read half.  Its PIECES `Pm n` (`UShLine.ush_mid γ γp n`) are what the
  shell holds while running; the PAYLOAD `ush_at n := upos γp n ∗ ukn_pay N (-1)`
  is what it hands /init back at `exit`.
* `Wc n p` is the shell's WRITE CREDENTIAL at line boundary `n` with `p` prompt
  bytes ("$ ") written; `Wb n` is the BANNER-OWED credential at `n` (/init's
  next round's banner is payable from it); both are opaque section parameters
  in the shell's files.
* the LEDGER `l : list fdstate` is the shell's descriptor table restricted to
  the standard streams; `ush_fd0c l` = fd 0 is the console, `ush_fd2p l` = fd 2
  is the console and writable, `l !! 2 = Some FdClosed` = fd 2 is closed.
* `sh_deps` is the FREE WRITE LAW (the flagged deposit): the placeholder that
  lets a `write(2, "$ ", 2)` count as paid without the era's credential.

## 0. Commits

ONE commit on `lane/step3-sh` in /shared/xv6iris-2-disc, by explicit path,
author = the checkout's config, NOT pushed:

    791e7216d  IO-LEAF step 3 (shell side): the loop holds the lease's pieces,
               the credential slot gets its closed arm
    (parent 4ab8f963f = origin/main b7c49dea2 code + one notes commit)

Files: iris/UkSh.v, UkShLoop.v, UkShCd.v, UkShFork.v, UkShEcho.v, UShLine.v,
UShKernel.v, UShOut.v, UShPanic.v, UserConsole.v, UInitSh.v, UInitBoot.v
(12 files, +679/-493).  One commit, not three: the "UkSh core" and
"consumers + entry" stages were never buildable on their own.  Nothing
else in the tree was touched (no _CoqProject row, no claude-notes, no
init-side file).  Working tree clean after the commit.

## 1. What was done, per file (against step3-interface.md)

### UkSh.v (the shell's command-loop kernel)

* `ush_fd0c_cons` (top level, beside `ush_fd2p_cons`): the console preamble's
  opens preserve "fd 0 is the console".  NEW, needed by `ush_wcp_cons`'s
  console arm.
* `Context (Wc)` then `Context (Wb : nat -> iProp Σ)` immediately after it.
* `ush_prompt_law` GAINS A SECOND CONJUNCT (statement change, see section 6):
  the closed-fd-2 arm `∀ l, ⌜l !! 2 = Some FdClosed⌝ -∗ ksh_w 2 "$ " 2 (ustd l) (ustd l)`.
  Reason: the contract routes `ksh_w_of_wcp`'s closed arm through
  `UkWriteClosed.ksh_w_of_closed`, but `UkWriteClosed` imports `UkSh`, so the
  only way that lemma can reach `ksh_w_of_wcp` (inside `UkSh`) is as a law the
  entry supplies.  `UShOut.sh_prompt_law_holds` and
  `UShPanic.sh_prompt_law_holds_line` discharge the new conjunct from
  `ksh_w_of_closed` (via the small closed lemma `UShOut.sh_fd2_signed`).
* `ush_wcp` -- the three arms exactly as the contract spells them, with the
  `(* AFFINE -- step 4 kills it *)` comment on the `∨ True`.
* `ush_wcp_triv`, `ush_wcp_cons` (console arm stays, closed arm stays for
  `k <> 2`, goes to the True arm at `k = 2`), `ksh_w_of_wcp` (console arm
  through the law's first conjunct; closed arm through its second conjunct
  with `Wb n` framed by `ksh_w_mono`; True arm through the free law
  `ksh_w_of_law`).
* `Context (Pm)`, `ush_lease`, the four hypotheses `ush_pm_of_at`,
  `ush_at_of_pm`, `ush_at_of_pm_taint`, `ush_wc_read` and the NEW
  `ush_at_of_pm_wb` MOVED ABOVE `ush_posb`, together with `ush_pos_of_pm`,
  `ush_pos_of_lease_taint`.
* `ush_posb l p := (∃ n, ⌜ush_bnd n⌝ ∗ Pm n ∗ ush_wcp l n p) ∨ (T ∗ ush_pos)`;
  `ush_pos_of_posb`, `ush_posb_at`, `ush_posb_of` (through `ush_pm_of_at`),
  `ush_posb_of_wc`, `ush_posb_cons`, `ush_posb_taint` as the contract lists.
  NOTE: `ush_pos_of_posb`/`ush_posb_at` now abstract over `ush_at_of_pm` and
  `ush_posb_of` over `ush_pm_of_at` (they assemble / take apart the payload);
  see the `About` lists in section 3 -- this is what forced the `ush_rest_l`
  decision in section 7.
* `ush_gets_done_0` / `ush_gets_done_line` as the contract states them
  (console arm refuted by `ush_fd0c_not_closed`; closed arm through
  `ush_at_of_pm_wb`; True arm through `ush_at_of_pm`; the line case sends the
  closed arm to the True arm at `n0 + 17`).  `ush_gets_line_of_posb` no longer
  splits on `ush_pm_of_at`.
* DELETED: `ush_promptw`, `ush_prompt_in`, `ush_prompt_in_triv`,
  `ush_prompt_in_cons`, `ksh_w_of_prompt_in`, `ush_lease_of_posb`; the
  `ush_prompt_in l -∗` premise of `ush_loop_head`, `wp_ksh_loop`,
  `wp_ksh_cmd_head`, `wp_ksh_console`, `wp_ksh_main`, `wp_ksh_start`,
  `wp_ksh_getcmd`; the dead `sh_deps -∗` premise of `wp_ksh_read` (and its
  `Hdp` at the call in `wp_ksh_gets_loop`).
* `ush_rest_l` GAINS TWO PURE PREMISES right after `⌜ukn_const N⌝ -∗`:
  `⌜forall i, ⊢ ush_at i -∗ ush_lease i⌝ -∗ ⌜forall i, ush_bnd i -> ⊢ Pm i -∗ ush_at i⌝ -∗`
  (section 7, decision D1).  `wp_ksh_loop` pays them from the section
  hypotheses at the one place the obligation is applied.

### UkShLoop.v, UkShCd.v, UkShFork.v, UkShEcho.v (consumers)

* `Context (Wb)` right after `Context (Wc)`, and `Context (Pm)` after it
  (`ush_pstate`/`ush_posb` now take `Pm`); every `UkSh.ush_posb N γp T Wc …`
  is `UkSh.ush_posb N γp T Wc Wb Pm …`; `ushl_head T Wc Wb Pm l sz`,
  `ushl_head_of_R` no longer passes `ush_prompt_in_triv`.
* UkShFork: `wp_kshf_fork`, `wp_kshf_fork_any`, `wp_kshm_body` take the two
  lease laws as Coq-level premises (`Hpm1`, `Hpm2`); `ushf_rest_of_body`
  introduces them from `ush_rest_l`'s new pure premises; the fork arm's
  re-entry stays on `ush_at` through
  `UkSh.ush_posb_at N γp T Wc Wb Pm Hpm2 l 0` and
  `UkSh.ush_posb_of N γp T Wc Wb Pm Hpm1 l 0 np0` (the True arm, as the
  contract says).
* UkShRun, UkShDiag, UkShMain, UConsLine: untouched (they name none of the
  changed binders; UConsLine mentions `ush_pstate`/`ush_rest_l` in comments).

### UShLine.v (the entry law and the lease instance)

* `ush_rd_x γ Wb n := ush_rd_pin γ n ∗ (Wb n ∨ True)` DEFINED LOCALLY with the
  `(* AFFINE -- step 4 kills it *)` comment, because THIS checkout's `UkInit`
  has no `init_rd` yet (the coordinator's c74734d65 is in the main checkout
  only).  It unfolds to exactly `UkInit.init_rd (ush_rd_pin γ) Wb n`; the
  coordinator unifies by replacing the body with `UkInit.init_rd (ush_rd_pin γ) Wb n`
  (`UShLine` may import `UkInit`: `UkInit` imports neither `UkSh` nor
  `UShLine`).
* Every premise `ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_pin γ)` became
  `… (ush_rd_x γ Wb)` (`ush_mid_of_at`, `ush_at_of_mid`, `ush_at_of_mid_taint`,
  `ush_read_ans_of_era`, `ush_read_recv_era`, `ush_read_recv_leaf_holds`, all
  with a `Wb` binder); NEW `ush_at_of_mid_wb` (the left arm); `ush_posb_of_at`
  REPLACED by `ush_posb_of_lend` exactly as the contract states it.

### UShKernel.v / UShOut.v / UShPanic.v (the entry)

* `sh_uexec_slot` / `sh_slot_of_kexec`: NEW parameters `Ql`, `Wb`, `Hpmwb`;
  `Hbd` is the entry law; spatial `sh_prompt_at … -∗` and `Q (-1) -∗` became
  `Ql (-1) -∗ UkSh.ush_wcp Wc Wb (take NSTD …) n 0%nat -∗`; `ush_rest_l N γp T Wc Wb Pm …`.
* DELETED: `sh_prompt_at`, `sh_prompt_at_triv`, `sh_prompt_in_of_at`.
* KEPT (deviation, section 7 D3): `UShKernel.sh_prompt_pay` and
  `UShOut.sh_prompt_pay_of_ushpr`.
* `UShOut.sh_prompt_law_holds` / `UShPanic.sh_prompt_law_holds_line` prove the
  law's new closed conjunct.

### UserConsole.v

* ONLY `ucons_pay_mono`, as the contract states it.

### UInitSh.v / UInitBoot.v (MINIMAL, against the unchanged init side)

* `sh_pay_rest` (TRUSTED, section 5) and `sh_pay`/`sh_pay_of_parts` gain `Wb`
  and `Pm` binders.
* `init_exec_sup_of_sh_slot` / `init_cons_sup_of_sh_slot` gain `Rdl`, `Wb`,
  the premise `(forall n, ⊢ Rd n -∗ Rdl n)`, the `Hpmwb` law and the entry law;
  the slot is built at `Ql := ucons_pay cn γp T Rdl` (the lease converted by
  `ucons_pay_mono`) and the credential slot is `ush_wcp_triv`; the
  `(Rt ∨ True)` conjunct handed over by `UkInit.init_exec_sup_pos` is dropped
  at the `iIntros` (`_`); `Rt := sh_prompt_pay` stays only because
  `init_exec_sup_pos` still takes it.
* `echo_Hinit_boot`: `Wb := fun _ => True%I`, `Rdl := UShLine.ush_rd_pin γ`,
  `Rd := UShLine.ush_rd_x γ (fun _ => True%I)`, `Pm := UShLine.ush_mid γ`,
  `Ql := ucons_pay fsc_cons γp (echo_taint γ) (ush_rd_pin γ)`; `Rd 0` is
  built as `ush_rd_pin γ 0 ∗ (True ∨ True)` (left arm); the new laws are
  `UShLine.ush_at_of_mid_wb` and `UShLine.ush_posb_of_lend`; `Hsh_rdl` drops
  the affine credential pointwise.

## 2. Verbatim statements

See the appendix at the end of this file (every new/changed definition and
lemma statement, comments stripped for the two long entry lemmas).

## 3. `About` binder lists (from the green tree, build s3-2)

`Arguments` lines as Rocq prints them (`{}` = implicit / instance):

```
ush_posb      {Σ} N {uartGhostG0} γp T (Wc Wb Pm) l p
ush_wcp       {Σ} (Wc Wb) l (n p)                       -- no N, no γp, no T
ush_pstate    {Σ ufdG0 ghost_varG0 ghost_varG1} N {uartGhostG0} γp T (Wc Wb Pm) l
ush_rest_l    {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1} N {uartGhostG0} γp T {ctokG0 SG PS} (Wc Wb Pm) R
ush_loop_head {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1} N {uartGhostG0} γp T {ctokG0 SG PS} (Wc Wb Pm) R l
ush_gets_done {Σ} N {uartGhostG0} γp T (Wc Wb Pm) l i f
ush_lease     {Σ} N {uartGhostG0} γp T Pm n
```
Lemmas that abstract over the section hypotheses (the reason for D1):
```
ush_posb_at        {Σ} N {uartGhostG0} γp T {HT} (Wc Wb Pm ush_at_of_pm) l p
ush_pos_of_posb    {Σ} N {uartGhostG0} γp T (Wc Wb Pm ush_at_of_pm) l p
ush_posb_of        {Σ} N {uartGhostG0} γp T {HT} (Wc Wb Pm ush_pm_of_at) l (p n)
ush_posb_of_wc     {Σ} N {uartGhostG0} γp T (Wc Wb Pm) l (p n) _          -- no law
ush_posb_taint     {Σ} N {uartGhostG0} γp T {HT} (Wc Wb Pm) l p           -- no law
ush_gets_done_0    {Σ} N {uartGhostG0} γp T {HT} (Wc Wb Pm ush_pm_of_at ush_at_of_pm ush_at_of_pm_wb) l n0 f _ _
ush_gets_done_line {Σ} N {uartGhostG0} γp T (Wc Wb Pm ush_wc_read) l n0 f _ _
wp_ksh_start       {Σ riscvGS0 ufdG0 GEN ghost_varG0 ghost_varG1} N {Hpay uartGhostG0} γp T {HT ctokG0 SG PS}
                   (Hpsok_free Wc Wb Pm ush_pm_of_at ush_at_of_pm ush_at_of_pm_taint ush_at_of_pm_wb ush_wc_read) …
```
So the call shape is `wp_ksh_start N γp T Hpsok_free Wc Wb Pm Hpm1 Hpm2 Hpm3 Hpmwb Hwc cn Hrl …`
(UShKernel passes exactly that); `UkShCd`/`UkShFork` still declare `Wc Wb Pm`
BEFORE their `Hpsok_free` (`UkShCd.wp_kshc_cd N γp T Wc Wb Pm Hpsok_free …`).

## 4. Deleted names and where their users went

| deleted | former users | now |
|---|---|---|
| `UkSh.ush_promptw`, `ush_prompt_in`, `ush_prompt_in_triv`, `ush_prompt_in_cons` | `wp_ksh_getcmd` (prompt), the loop head/back edge (`wp_ksh_loop`, `UkShLoop.ushl_head_of_R`), `wp_ksh_console`/`wp_ksh_main`/`wp_ksh_start`, `UShKernel.sh_prompt_in_of_at` | the credential arrives in `ush_wcp` inside `ush_posb` at the right count; the prompt branches once in `ksh_w_of_wcp`; the back edge passes `ush_pstate` only |
| `UkSh.ksh_w_of_prompt_in` | `ksh_w_of_wcp` (True arm), `wp_ksh_getcmd` (taint arm) | `ksh_w_of_law … ltac:(reflexivity) with "Hdp"` directly (the free law) |
| `UkSh.ush_lease_of_posb` | none in the tree | -- |
| `UShKernel.sh_prompt_at`, `sh_prompt_at_triv`, `sh_prompt_in_of_at` | `sh_uexec_slot`, `sh_slot_of_kexec`, `UInitSh.init_exec_sup_of_sh_slot` | the spatial `UkSh.ush_wcp Wc Wb (take NSTD …) n 0%nat` premise; UInitSh builds it with `ush_wcp_triv` (a comment in `UkInitMain.v:1405` still names `sh_prompt_at`; init-side file, lane I's) |
| `UShLine.ush_posb_of_at` | `UInitBoot.echo_Hinit_boot` (`Hsh_bd`) | `UShLine.ush_posb_of_lend` |
| the `sh_deps -∗` premise of `wp_ksh_read` | `wp_ksh_gets_loop` passed `Hdp` | removed |

NOT deleted although the contract lists them: `UShKernel.sh_prompt_pay`,
`UShOut.sh_prompt_pay_of_ushpr` (section 7, D3).  `UkSh.ush_pm_of_at` is KEPT
(the contract keeps all four hypotheses).

## 5. TRUSTED statement change: `UInitSh.sh_pay_rest`

`UInitBootAdequacy.v:140`'s conjunct of `Hsh_owed` reads, unchanged,
`(⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)`; the definition it names changed:

OLD (origin/main b7c49dea2):
```
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ)
       (Wc : nat -> nat -> iProp Σ),
       ⌜ Persistent T ⌝ -∗
       ush_rest_l (PS := uprogSG_free) N γp T Wc
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.
```
NEW:
```
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ)
       (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
       (Pm : nat -> iProp Σ),
       ⌜ Persistent T ⌝ -∗
       ush_rest_l (PS := uprogSG_free) N γp T Wc Wb Pm
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.
```
`Pm` is a binder because `ush_rest_l` now quantifies the loop head, whose
process state holds `Pm n` (the contract's `∀ γp N T Wc Wb` omitted it; the
handover note "sh_pay_rest quantifies Wc, Wb AND Pm" has it).  AND the body
of `ush_rest_l` changed (two pure premises, section 7 D1), so the OBLIGATION
`Hsh_owed` owes is: for every record, taint, credential families and lease
pieces, GIVEN the two lease laws, the shell's rest-of-line body.  Without the
two premises the obligation would have been unprovable for an opaque `Pm`
(the fork arm's `-1` exit must assemble `ukn_pay N (-1)` from `Pm n`).

## 6. Every `∨ True` arm left, and the step-4 obligation it stands for

1. `UkSh.ush_wcp`'s third arm `∨ True` -- step 4: the fork arm's re-entry
   (`ush_posb_at`/`ush_posb_of` at UkShFork.v:~296/~480) LENDS the
   credential; `ush_wcp_cons` at `k = 2` goes to the console arm through
   `Wb n -∗ Wc n 0` (PROLOGUE-ALTS-3's ban arm); `ush_gets_done_line`'s closed
   arm is refuted by the discipline lemma; `UInitSh`'s `ush_wcp_triv` is
   replaced by lane I's correlated credential; `ksh_w_of_wcp`'s True arm
   (the free law) dies with them.
2. `UShLine.ush_rd_x`'s `(Wb n ∨ True)` (= `UkInit.init_rd_cred`) -- step 4
   makes it `Wb n`: `ush_at_of_mid` (the right arm; used by
   `UkSh.ush_at_of_pm`, i.e. every exit without a credential) is then
   unprovable and the exits that use it (the fork arm's assembly,
   `ush_pos_of_posb`, `ush_posb_at`, the True arms of `ush_gets_done_0`)
   must produce `Wb n` (M3b core's `ewc_panic_done` route) or the taint.
3. `UkSh.ush_prompt_law` itself has no affine arm; `sh_deps`'s free law is
   still spent at `ksh_w_of_wcp`'s True arm and `wp_ksh_getcmd`'s taint arm
   (as before: the endgame audit's leaves, minus `ksh_w_of_prompt_in`).

No other `∨ True` was added.  The init side's `(Rt ∨ True)` is consumed by
`_` in `init_exec_sup_of_sh_slot` (lane I deletes the binder).

## 7. Decisions where the contract was silent or could not be followed as written

* D1 (`ush_rest_l` gains two pure premises).  `ush_posb_at` (payload assembly
  from the pieces) and `ush_posb_of` (its inverse) are the fork arm's
  accessors, and Rocq abstracts their proofs over the section hypotheses
  `ush_at_of_pm` / `ush_pm_of_at`.  `UkShFork` proves `ush_rest_l` for an
  OPAQUE `Pm` (that is what `sh_pay_rest` quantifies), so it cannot supply
  the laws itself; the file's own precedent (`⌜ukn_const N⌝`, `shk_code`,
  `ush_jtab` -- "facts only the entry can produce are premises of the
  OBLIGATION") is followed: the two laws are pure premises of `ush_rest_l`,
  paid by `wp_ksh_loop` from the section hypotheses.  Alternative considered
  and rejected: quantifying the laws in `sh_pay_rest` (a bigger trusted change).
* D2 (`ush_prompt_law` gains the closed-arm conjunct).  Reason in section 1;
  the contract's own route (`ksh_w_of_closed`) is what discharges it.
* D3 (`sh_prompt_pay` and `sh_prompt_pay_of_ushpr` kept).  `UInitBanner.
  sh_prompt_pay_of_kinit_own` (init-side, forbidden to this lane) consumes
  both, and `Rt := sh_prompt_pay` is the placeholder instantiation the
  UNCHANGED `UkInit.init_exec_sup_pos` still needs.  Lane I deletes the three
  together with `Rt`.
* D4 (`ush_rd_x` local).  Section 1, UShLine.
* D5 (`sh_pay_rest` binds `Pm`).  Section 5.
* D6 The `%Hpm1 %Hpm2` names in `ushf_rest_of_body`/`wp_kshm_body` etc. are
  Coq-level premises, not section hypotheses, so `ushf_rest_of_body`'s
  statement is unchanged apart from the binders.

## 8. Gate (build s3-2, VM tree /mnt/rocq/trees/_shared_xv6iris-2-disc; log /tmp/s3-2.log on the VM)

```
vmbuild s3-2:            COMPILED=34  EXIT=0        (grep -c "^Error" /tmp/s3-2.log = 0)
make -f CoqMakefile -n:  0 lines "ROCQ compile"
make audit-only | grep -v '^make\|^cd ' | md5sum:  57f7327206c4b276d05035342fea8ecf  (the thirteen, unchanged)
tools/lemma_diff.py --ref origin/main:  10 GONE + 1 NEWAXIOM, all justified:
    UShKernel: sh_prompt_at, sh_prompt_at_triv, sh_prompt_in_of_at   (contract: DELETE)
    UShLine:   ush_posb_of_at                                         (REPLACED by ush_posb_of_lend)
    UkSh:      ush_promptw, ush_prompt_in, ush_prompt_in_triv,
               ush_prompt_in_cons, ksh_w_of_prompt_in                (contract: DELETE)
               ush_lease_of_posb                                      (no user in the tree; its body
                                                                       was ush_posb_at + ush_pm_of_at)
    NEWAXIOM UkSh.ush_at_of_pm_wb: a section Hypothesis (the fifth lease law),
               discharged at echo_Hinit_boot by UShLine.ush_at_of_mid_wb
Admitted/admit/Abort in the 12 files: none
run-on-gcp --check-dumps: "the VM's tracked dumps match this checkout"
git status --porcelain after the commit: clean
```
The previous attempt's build s3-1 (EXIT=2) had three errors; the fixes:
`UShOut.v`/`UShPanic.v` `iSplit` on `(∀…) ∗ (∀…)` -> `iSplitL ""` (neither
conjunct is persistent, so `iSplit` refuses a `∗`); `UInitSh.v` `iClear "Hrt"`
inside a `[Hpos Hlease]` sub-goal (where `Hrt` is not in scope) -> the
`(Rt ∨ True)` is dropped at the `iIntros` with `_`; `UkShFork.v` `"Hpos" not
found` -> `ush_posb_at`/`ush_posb_of` need the lease laws (D1).

## 9. Where a successor picks up

Nothing is left open in this lane.  For the coordinator's glue:
* `UShLine.ush_rd_x γ Wb n` is `ush_rd_pin γ n ∗ (Wb n ∨ True)` locally;
  replace its body by `UkInit.init_rd (ush_rd_pin γ) Wb n` (same term after
  unfolding `init_rd`/`init_rd_cred`) and add `Require Import UkInit` to
  UShLine (no cycle: UkInit imports neither UkSh nor UShLine).
* the sites to replace: `UInitSh.init_exec_sup_of_sh_slot`'s
  `iApply UkSh.ush_wcp_triv` (the credential slot) and its
  `ucons_pay_mono cn γp T Rd Rdl (-1)` (the lend), the `_` that eats
  `(Rt ∨ True)`; `UInitBoot.echo_Hinit_boot`'s `(fun _ => True%I)` for `Wb`
  and `Hsh_rdl`; `Rt := UShKernel.sh_prompt_pay` and
  `UShOut.sh_prompt_pay_of_ushpr` / `UInitBanner.sh_prompt_pay_of_kinit_own`
  go together with `init_exec_sup_pos`'s `Rt`.
* `sh_pay_rest`'s final shape (R3's): the two lease laws are now premises of
  `ush_rest_l`, so `sh_pay_rest` needs no law binders; the taint-instance
  ruling (`echo_taint c`) from the checkpoint is untouched.


## Appendix -- verbatim statements (comments stripped where noted)

```
----- iris/UkSh.v: Lemma ush_fd0c_cons
Lemma ush_fd0c_cons (l : list fdstate) (k : nat) :
  length l = NSTD ->
  ush_fd0c l ->
  ush_fd0c (<[k := FdOpen true true (FdDevice CONSOLE)]> l).

----- iris/UkSh.v: Definition ush_prompt_law
  Definition ush_prompt_law : iProp Σ :=
    (□ ((∀ (n : nat) (l : list fdstate),
           ⌜ ush_fd2p l ⌝ -∗
           ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
             (ustd γfd l ∗ Wc n 0%nat) (ustd γfd l ∗ Wc n 2%nat))
        ∗ (∀ l : list fdstate,
             ⌜ l !! 2%nat = Some FdClosed ⌝ -∗
             ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
               (ustd γfd l) (ustd γfd l))))%I.

----- iris/UkSh.v: Definition ush_wcp
  Definition ush_wcp (l : list fdstate) (n p : nat) : iProp Σ :=
    ((⌜ ush_fd0c l /\ ush_fd2p l ⌝ ∗ Wc n p)
     ∨ (⌜ l !! 2%nat = Some FdClosed ⌝ ∗ Wb n)
     ∨ True)%I.

----- iris/UkSh.v: Lemma ush_wcp_triv
  Lemma ush_wcp_triv (l : list fdstate) (n p : nat) : ⊢ ush_wcp l n p.

----- iris/UkSh.v: Lemma ush_wcp_cons
  Lemma ush_wcp_cons (l : list fdstate) (k n p : nat) :
    length l = NSTD ->
    ush_wcp l n p -∗
    ush_wcp (<[k := FdOpen true true (FdDevice CONSOLE)]> l) n p.

----- iris/UkSh.v: Lemma ksh_w_of_wcp
  Lemma ksh_w_of_wcp (l : list fdstate) (n : nat) :
    sh_deps -∗
    ush_prompt_law -∗
    ush_wcp l n 0%nat -∗
    ksh_w (mword_of_int 2) (mword_of_int sh_prompt_pv) 2%nat
      (ustd γfd l) (ustd γfd l ∗ ush_wcp l n 2%nat).

----- iris/UkSh.v: Definition ush_lease
  Definition ush_lease (n : nat) : iProp Σ := (Pm n ∨ (T ∗ ush_pos))%I.

----- iris/UkSh.v: Hypothesis ush_pm_of_at

  Hypothesis ush_pm_of_at : forall n : nat, ⊢ ush_at n -∗ ush_lease n.

----- iris/UkSh.v: Hypothesis ush_at_of_pm

  Hypothesis ush_at_of_pm :
    forall n : nat,
      ush_bnd n -> ⊢ Pm n -∗ ush_at n.

----- iris/UkSh.v: Hypothesis ush_at_of_pm_taint
  Hypothesis ush_at_of_pm_taint : forall n : nat, ⊢ T -∗ Pm n -∗ ush_at n.

----- iris/UkSh.v: Hypothesis ush_at_of_pm_wb
  Hypothesis ush_at_of_pm_wb :
    forall n : nat,
      ush_bnd n -> ⊢ Pm n -∗ Wb n -∗ ush_at n.

----- iris/UkSh.v: Hypothesis ush_wc_read
  Hypothesis ush_wc_read :
    forall n : nat,
      ⊢ Pm (n + length echo_line)%nat -∗ Wc n 2%nat -∗
        Pm (n + length echo_line)%nat ∗ Wc (n + length echo_line)%nat 0%nat.

----- iris/UkSh.v: Definition ush_posb
  Definition ush_posb (l : list fdstate) (p : nat) : iProp Σ :=
    ((∃ n : nat, ⌜ush_bnd n⌝ ∗ Pm n ∗ ush_wcp l n p)
     ∨ (T ∗ ush_pos))%I.

----- iris/UkSh.v: Lemma ush_pos_of_posb
  Lemma ush_pos_of_posb (l : list fdstate) (p : nat) :
    ush_posb l p -∗ ush_pos.

----- iris/UkSh.v: Lemma ush_posb_at
  Lemma ush_posb_at (l : list fdstate) (p : nat) :
    ush_posb l p -∗
    ∃ n : nat, (⌜ush_bnd n⌝ ∨ T) ∗ ush_at n.

----- iris/UkSh.v: Lemma ush_posb_of
  Lemma ush_posb_of (l : list fdstate) (p n : nat) :
    (⌜ush_bnd n⌝ ∨ T) -∗ ush_at n -∗ ush_posb l p.

----- iris/UkSh.v: Lemma ush_posb_of_wc
  Lemma ush_posb_of_wc (l : list fdstate) (p n : nat) :
    ush_bnd n -> Pm n -∗ ush_wcp l n p -∗ ush_posb l p.

----- iris/UkSh.v: Lemma ush_posb_cons
  Lemma ush_posb_cons (l : list fdstate) (k p : nat) :
    length l = NSTD ->
    ush_posb l p -∗
    ush_posb (<[k := FdOpen true true (FdDevice CONSOLE)]> l) p.

----- iris/UkSh.v: Lemma ush_posb_taint
  Lemma ush_posb_taint (l : list fdstate) (p : nat) :
    T -∗ ush_pos -∗ ush_posb l p.

----- iris/UkSh.v: Lemma ush_gets_done_0
  Lemma ush_gets_done_0 (l : list fdstate) (n0 : nat) (f : nat -> bv 8) :
    ush_bnd n0 -> l !! 0%nat = Some FdClosed ->
    Pm n0 -∗ ush_wcp l n0 2%nat -∗ ush_gets_done l 0%nat f.

----- iris/UkSh.v: Lemma ush_gets_done_line
  Lemma ush_gets_done_line (l : list fdstate) (n0 : nat) (f : nat -> bv 8) :
    ush_bnd n0 ->
    ush_line_is f 0%nat (length echo_line) ->
    ush_wcp l n0 2%nat -∗
    Pm (n0 + length echo_line)%nat -∗ ush_gets_done l (length echo_line) f.

----- iris/UkSh.v: Definition ush_gets_done
  Definition ush_gets_done (l : list fdstate) (i : nat) (f : nat -> bv 8)
      : iProp Σ :=
    (((⌜i = 0%nat⌝ ∨ ⌜i = length echo_line /\ ush_line_is f 0%nat i⌝)
      ∗ ush_posb l 0%nat)
     ∨ (T ∗ ush_pos))%I.

----- iris/UkSh.v: Definition ush_loop_head
  Definition ush_loop_head (R : iProp Σ) (l : list fdstate) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (n : nat),
       ⌜ ush_regs m ⌝ -∗
       ⌜ ush_fd0p l ⌝ -∗
       ush_pstate l -∗
       R -∗
       ubytes γd sh_buf sh_nbuf f -∗
       urun N h m (mword_of_int 0x938) (16 + (ush_Dbody + n)) -∗
       WP (Loop : expr riscv_lang))%I.

----- iris/UkSh.v: Definition ush_rest_l
  Definition ush_rest_l (R : iProp Σ) : iProp Σ :=
    (□ (∀ (l : list fdstate),
        ⌜ ukn_const N ⌝ -∗
        ⌜ forall i : nat, ⊢ ush_at i -∗ ush_lease i ⌝ -∗
        ⌜ forall i : nat, ush_bnd i -> ⊢ Pm i -∗ ush_at i ⌝ -∗
        shk_code γt -∗
        ush_jtab γt -∗
        ush_loop_head R l -∗
        ∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (k i2 : nat) (n : nat),
          ⌜ ush_regs m ⌝ -∗
          ⌜ m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ⌝ -∗
          ⌜ m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ⌝ -∗
          ⌜ (k <= i2 < sh_nbuf)%nat /\ f i2 = ubyte0 ⌝ -∗
          ⌜ ush_fd0p l ⌝ -∗
          ush_rest_line f k -∗
          ush_pstate l -∗
          R -∗
          ubytes γd sh_buf sh_nbuf f -∗
          urun N h m (mword_of_int 0x97a) (16 + (ush_Dbody + n)) -∗
          WP (Loop : expr riscv_lang)))%I.

----- iris/UShLine.v: Definition ush_rd_x
  Definition ush_rd_x (γ : echo_gn) (Wb : nat -> iProp Σ) (n : nat)
      : iProp Σ :=
    (ush_rd_pin γ n ∗ (Wb n ∨ True))%I.

----- iris/UShLine.v: Lemma ush_mid_of_at
  Lemma ush_mid_of_at (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : nat -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ UkSh.ush_at N γp n -∗ UkSh.ush_lease N γp T (ush_mid γ γp) n.

----- iris/UShLine.v: Lemma ush_at_of_mid
  Lemma ush_at_of_mid (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : nat -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    UkSh.ush_bnd n ->
    ⊢ ush_mid γ γp n -∗ UkSh.ush_at N γp n.

----- iris/UShLine.v: Lemma ush_at_of_mid_wb
  Lemma ush_at_of_mid_wb (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : nat -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    UkSh.ush_bnd n ->
    ⊢ ush_mid γ γp n -∗ Wb n -∗ UkSh.ush_at N γp n.

----- iris/UShLine.v: Lemma ush_at_of_mid_taint
  Lemma ush_at_of_mid_taint (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (Wb : nat -> iProp Σ) (N : uk_names Σ) (γp : gname) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ T -∗ ush_mid γ γp n -∗ UkSh.ush_at N γp n.

----- iris/UShLine.v: Lemma ush_posb_of_lend
  Lemma ush_posb_of_lend (γ : echo_gn) (T : iProp Σ) `{!Persistent T}
      (N : uk_names Σ) (γp : gname) (Wc : nat -> nat -> iProp Σ)
      (Wb : nat -> iProp Σ) (l : list fdstate) (n : nat) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ upos γp n -∗ ucons_pay fsc_cons γp T (ush_rd_pin γ) (-1) -∗
      UkSh.ush_wcp Wc Wb l n 0%nat -∗
      UkSh.ush_posb N γp T Wc Wb (ush_mid γ γp) l 0%nat.

----- iris/UShKernel.v: Lemma sh_uexec_slot
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
           ∗ Wc (n + length EchoDisc.echo_line)%nat 0%nat)
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

----- iris/UShKernel.v: Lemma sh_slot_of_kexec
  Lemma sh_slot_of_kexec (R : gname -> gname -> gname -> iProp Σ)
      (γp : gname) (cn : cons_names) (T K : iProp Σ) `{!Persistent T}
      (Q Ql : Z -> iProp Σ)
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
           ∗ Wc (n + length EchoDisc.echo_line)%nat 0%nat)
      (na : nat)
      (alen : nat -> nat) (afun : nat -> nat -> bv 8) (sts : list fdstate)
      (W' : uvis) (n0 n : nat) :
    (forall (N : uk_names Σ) (l : list fdstate) (n : nat),
       ukn_pay N = Q ->
       ⊢ upos γp n -∗ Ql (-1) -∗ UkSh.ush_wcp Wc Wb l n 0%nat -∗
         UkSh.ush_posb N γp T Wc Wb Pm l 0%nat) ->
    (forall x y : Z, Q x = Q y) ->
    kexec_image_ok sh_elf na alen afun sts W' ->
    uvis_cwd W' = FsImg.ROOTINO ->
    kexec_sz sh_elf - PGSIZE + 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= kxc_sp_final (kexec_sz sh_elf) alen na ->
    length sts = NOFILE ->
    uvis_lazy W' = false ->
    
    □ (∀ γt γd γs : gname,
        usz γs (uvis_sz W') -∗
        ([∗ map] k ↦ b ∈ base.filter
              (fun kv : Z * bv 8 =>
                 kv.1 < uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1)
                        - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
              (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
           ubyte γd k b) -∗
        |==> ∃ f : nat -> bv 8, R γt γd γs ∗ ubytes γd sh_buf sh_nbuf f) -∗
    udep -∗
    UkSh.sh_deps -∗
    UkSh.ush_tag_law T -∗
    sh_prompt_law Wc -∗
    (∀ N : uk_names Σ,
       ush_rest_l N γp T Wc Wb Pm (R (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    UkSh.ush_fd0 T (take NSTD sts) -∗
    (□ (∀ N : uk_names Σ, UkSh.ush_open_console_leaf N T)
     ∨ (□ (∀ N : uk_names Σ, UkSh.ush_open_absent_leaf N T K) ∗ K)
     ∨ T) -∗
    □ (∀ W : uvis, T -∗ my_pay (uvis_gen W) Q -∗ uslot W) -∗
    my_pay (uvis_gen W') Q -∗
    upos γp n -∗
    Ql (-1) -∗
    UkSh.ush_wcp Wc Wb (take NSTD sts) n 0%nat -∗
    uslot W'.

----- iris/UShOut.v: Lemma sh_fd2_signed
Lemma sh_fd2_signed : bv_signed (trunc32 (mword_of_int 2 : mword 64)) = Z.of_nat 2.

----- iris/UShOut.v: Lemma sh_prompt_law_holds
  Lemma sh_prompt_law_holds :
    echo_links T γ -∗
    UShKernel.sh_prompt_law (EchoLinks.ewc_cred T γ (S gen_id)).

----- iris/UserConsole.v: Lemma ucons_pay_mono
  Lemma ucons_pay_mono (cn : cons_names) (γ : gname) (T : iProp Σ)
      (Rd Rd' : nat -> iProp Σ) (xs : Z) :
    □ (∀ n : nat, Rd n -∗ Rd' n) -∗
    ucons_pay cn γ T Rd xs -∗ ucons_pay cn γ T Rd' xs.

----- iris/UInitSh.v: Definition sh_pay_rest
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ)
       (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
       (Pm : nat -> iProp Σ),
       ⌜ Persistent T ⌝ -∗
       ush_rest_l (PS := uprogSG_free) N γp T Wc Wb Pm
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.

----- iris/UInitSh.v: Lemma sh_pay_of_parts
  Lemma sh_pay_of_parts (T : iProp Σ) `{!Persistent T}
      (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
      (Pm : gname -> nat -> iProp Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    sh_pay_state Rsh n0 -∗ sh_pay_rest Rsh -∗ UkSh.ush_tag_law T -∗
    sh_pay T Wc Wb Pm Rsh n0.

----- iris/UInitSh.v: Lemma init_exec_sup_of_sh_slot
  Lemma init_exec_sup_of_sh_slot (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cn : cons_names) (st : fdstate) (K : iProp Σ) `{!Persistent K}
      (Rd : nat -> iProp Σ) `{!forall i : nat, Timeless (Rd i)}
      (Rdl : nat -> iProp Σ)
      (Pm : gname -> nat -> iProp Σ)
      (Wc : nat -> nat -> iProp Σ)
      (Wb : nat -> iProp Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    (forall n : nat, ⊢ Rd n -∗ Rdl n) ->
    (forall (γp : gname) (N : uk_names Σ) (l : list fdstate),
       ukn_pay N = ucons_pay cn γp T Rd ->
       ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp T (Pm γp) cn l) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp T Rd ->
       ⊢ UkSh.ush_at N γp i -∗
         UkSh.ush_lease N γp T (Pm γp) i) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp T Rd -> UkSh.ush_bnd i ->
       ⊢ Pm γp i -∗ UkSh.ush_at N γp i) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp T Rd ->
       ⊢ T -∗ Pm γp i -∗ UkSh.ush_at N γp i) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp T Rd -> UkSh.ush_bnd i ->
       ⊢ Pm γp i -∗ Wb i -∗ UkSh.ush_at N γp i) ->
    (forall (γp : gname) (n : nat),
       ⊢ Pm γp (n + length EchoDisc.echo_line)%nat -∗ Wc n 2%nat -∗
         Pm γp (n + length EchoDisc.echo_line)%nat
         ∗ Wc (n + length EchoDisc.echo_line)%nat 0%nat) ->
    (forall (γp : gname) (N : uk_names Σ) (l : list fdstate) (i : nat),
       ukn_pay N = ucons_pay cn γp T Rd ->
       ⊢ upos γp i -∗ ucons_pay cn γp T Rdl (-1) -∗
         UkSh.ush_wcp Wc Wb l i 0%nat -∗
         UkSh.ush_posb N γp T Wc Wb (Pm γp) l 0%nat) ->
    udep (PS := uprogSG_free) -∗
    UkSh.sh_deps (PS := uprogSG_free) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) Wc -∗
    
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N T)
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N T K) ∗ K)
     ∨ T) -∗
    init_sh_slot T (sh_pay T Wc Wb Pm Rsh n0) -∗
    
    UkInit.init_exec_sup_lend cn T st
      (UShKernel.sh_prompt_pay (PS := uprogSG_free)) Rd.

----- iris/UInitBoot.v: Lemma init_cons_sup_of_sh_slot
  Lemma init_cons_sup_of_sh_slot (γ : echo_fixed) (r : echo_names)
      (cn : cons_names) (st : fdstate)
      (Rd : nat -> iProp Σ) `{!forall i : nat, Timeless (Rd i)}
      (Rdl : nat -> iProp Σ)
      (Pm : gname -> nat -> iProp Σ)
      (Wc : nat -> nat -> iProp Σ)
      (Wb : nat -> iProp Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (UkSh.ush_Dbody + n0)))) <= 0xFE0 ->
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    (forall n : nat, ⊢ Rd n -∗ Rdl n) ->
    (forall (γp : gname) (N : uk_names Σ) (l : list fdstate),
       ukn_pay N = ucons_pay cn γp (echo_taint γ) Rd ->
       ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp (echo_taint γ)
           (Pm γp) cn l) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp (echo_taint γ) Rd ->
       ⊢ UkSh.ush_at N γp i -∗
         UkSh.ush_lease N γp (echo_taint γ) (Pm γp) i) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp (echo_taint γ) Rd -> UkSh.ush_bnd i ->
       ⊢ Pm γp i -∗ UkSh.ush_at N γp i) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp (echo_taint γ) Rd ->
       ⊢ echo_taint γ -∗ Pm γp i -∗ UkSh.ush_at N γp i) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp (echo_taint γ) Rd -> UkSh.ush_bnd i ->
       ⊢ Pm γp i -∗ Wb i -∗ UkSh.ush_at N γp i) ->
    (forall (γp : gname) (n : nat),
       ⊢ Pm γp (n + length EchoDisc.echo_line)%nat -∗ Wc n 2%nat -∗
         Pm γp (n + length EchoDisc.echo_line)%nat
         ∗ Wc (n + length EchoDisc.echo_line)%nat 0%nat) ->
    (forall (γp : gname) (N : uk_names Σ) (l : list fdstate) (i : nat),
       ukn_pay N = ucons_pay cn γp (echo_taint γ) Rd ->
       ⊢ upos γp i -∗ ucons_pay cn γp (echo_taint γ) Rdl (-1) -∗
         UkSh.ush_wcp Wc Wb l i 0%nat -∗
         UkSh.ush_posb N γp (echo_taint γ) Wc Wb (Pm γp) l 0%nat) ->
    udep (PS := uprogSG_free) -∗ UkSh.sh_deps (PS := uprogSG_free) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) Wc -∗
    UInitSh.init_sh_slot (echo_taint γ)
      (UInitSh.sh_pay (echo_taint γ) Wc Wb Pm Rsh n0) -∗
    UkInit.init_cons_sup cn (echo_taint γ)
      (init_cons_cred (echo_taint γ) r) st
      (UShKernel.sh_prompt_pay (PS := uprogSG_free)) Rd.
```
