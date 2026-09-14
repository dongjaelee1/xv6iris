# lane IO-LEAF -- handover
# (M1, M2, M3a, M3b(1), M4a(1), M4a(2a), M4a(3), M3b-core-part-1, M3c,
#  M5a, M5b, M5(3), M6a(1), M6a(2)a, M6a(2)b, M6a(3)a, M6a(3)b LANDED.
#  `Hsh_owed` HAS TWO CONJUNCTS.)

Checkout `/shared/xv6iris-2`, branch `lane/io-leaf` = `b39fd4d48` =
`origin/main` (pushed).  VM tree green at exactly this state (io58:
COMPILED=27 EXIT=0).  Logs `io1`..`io58` used; **next free `io59`.**

## M6a(3) STEPS 1-2 LANDED (2026-09-14; the four steps below are now 3-4)

**M6a(3)a `a43341d28`** -- `E_lb v n` rides the lease pieces (`ush_mid`,
`ush_rd_pin`, `ush_rd_in`; `kinit_dl0` at 0).  **M6a(3)b `b39fd4d48`** --
`UkSh` takes `Wc : nat -> nat -> iProp` beside `Pm` (the credential at
boundary `n` with `p` prompt bytes out; the instance is
`EchoLinks.ewc_cred T γ (S gen_id)`, `ewc_pr` the 0/1/2 family), the
persistent `ush_prompt_law` (0 -> 2 at the prompt; `UShKernel.sh_prompt_law
Wc`, `UShOut.sh_prompt_law_holds`) and the Coq-level `ush_wc_read` (2 at `n`
-> 0 at `n+17` on `Pm (n+17)`; `UShLine.ush_mid_wc_read`); the loop's slot
`ush_wcp l n p := (⌜ush_fd2p l⌝ ∗ Wc n p) ∨ True` inside `ush_posb l p`,
`ush_pstate` at p = 0, getcmd -> `ush_posb l 2` -> gets ->
`ush_gets_done_line` spends the read law.  THE `∨ True` IS THE ENTRY (step
3's): see the as-landed note in app-echo.md.  `ush_rest_l` gained `Wc` (it
quantifies the loop head), hence `sh_pay T Wc Rsh n0` and `sh_pay_rest`'s
`∀ Wc`.  Arg-order trap: `UkShCd`/`UkShFork` declare `Wc` BEFORE their
`Hpsok_free` (calls: `N γp T Wc Hpsok_free …`), `UkSh` after it
(`wp_ksh_start N γp T Hpsok_free Wc Pm Hpm1 Hpm2 Hpm3 Hwc cn Hrl …`).

## STEP 3 -- THE DESIGN OF RECORD (coordinator, 2026-09-14, after the
## banner-optional ruling; supersedes the reviewer's Q3 where they differ)

Families (all opaque below the top; instances at `echo_Hinit_boot`):
  `Rdl n` -- the READ side of the lease at boundary `n` (UShLine.ush_rd_pin);
  `Wb  n` -- the BANNER-OWED credential at `n` (UInitBanner.kinit_ban n =
             ∃ v, era_pin ∗ ewc_ban v n 0);
  `Wc n p` -- the shell's credential at `n`, `p` prompt bytes out; AT p = 0 IT
             IS A DISJUNCTION `∃ v, era_pin ∗ (ewc_owed v n ∨ ewc_ban v n 0)`
             (prompt-shaped after a banner that reached the wire, banner-
             owed otherwise -- PROLOGUE-ALTS-3 pays the '$' from either);
             at p = 2 it is `ewc_open` as today.
  `Pm n`  -- the mid-line pieces (UShLine.ush_mid), unchanged.
sh's EXIT family `Rd n := Rdl n ∗ Wb n` (UkInit defines it from the two;
`ukn_pay N = ucons_pay cn γ T Rd`).  The LEND is `ucons_pay cn γ T Rd' (-1)`
at the DIFFERENT family `Rd' n := Rdl n ∗ Wc n 0`, minted by `uinit_lend` at
family `Rd'` from the token opened at `Rd` -- so `Rc ≠ Q (-1)` in exactly
the ruling's sense, and `UserConsole` does not change.
init's loop head holds `uinit_tok cn T Rd`; per round: open it (`reader n ∗
Rdl n ∗ Wb n` or T); the banner: on the console arm the law `□ ∀ n N', Wb n
-∗ kinit_banner0 N' stc (Wc n 0)` (kinit_ban_law becomes n-indexed; Bn
LEAVES init_boot_pay, kinit_round0 DIES), on the closed arm the banner is
written through `UkWriteClosed.kinit_w1_of_closed_l0` and `Wb n` becomes
`Wc n 0` by its ban arm (no conversion), on the taint arm T; then
`uinit_lend` at `Rd'`, `wp_kinit_fork` lends `upos γ n ∗ ucons_pay Rd' (-1)`
(the `(Rt ∨ True)` conjunct is GONE; `init_exec_sup_pos` takes the lend at
`Rd'`); FORK-REFUND hands `Rc` back whole (die_df's credential: M6b).
sh's ENTRY (`sh_slot_of_kexec`/`sh_uexec_slot`): `upos γp n -∗ ucons_pay cn
γp T Rd' (-1) -∗ uslot W'` -- the raw pieces + the credential; NO
`sh_prompt_at`, NO `ush_prompt_in`, NO `Q (-1)` (the exit payload is
assembled by sh where it exits).  The entry law (UShLine): `upos γp n ∗
ucons_pay Rd' (-1) -∗ ush_posb l 0` with `ush_posb l p := (∃ n, ⌜bnd n⌝ ∗ Pm
n ∗ ush_wcp l n p) ∨ (T ∗ ush_pos)` and `ush_wcp l n p := (⌜ush_fd0c l ∧
ush_fd2p l⌝ ∗ Wc n p) ∨ (⌜l !! 2 = Some FdClosed⌝ ∗ Wc n 0)` -- the BOTH-
CONSOLE row on the credential arm (from init's l3 head, preserved by the
preamble's opens) is what refutes `ush_gets_done_0` on that arm (fd 0 closed
contradicts fd0c); the closed arm keeps the credential UNCHANGED through the
prompt (`ksh_w_of_closed`) and reaches sh's exit only via the shut fd 0 (-1
read) or the discipline lemma (fd 0 open, fd 2 closed: an untainted read at
an unwritten prompt is refuted -- PROLOGUE-ALTS-3's (3)).
`Context (Pm)` and its laws move ABOVE `ush_posb`; `ush_pm_of_at` dies
(nothing holds `ush_at` in the loop); `ush_at_of_pm` becomes the EXIT
ASSEMBLERS: `bnd n -> Pm n -∗ Wb n -∗ ush_at n` (at the new `Rd`) and
`ush_at_of_pm_taint` (kept); sh reaches `Wb n` at the shut-fd-0 exit from the
slot's closed arm only if the credential there is ban-shaped -- so the closed
arm's credential is `Wc n 0`'s BAN arm specifically: state the slot's closed
arm as `⌜closed⌝ ∗ Wb n` and let the top's `Wc n 0` disjunction absorb it at
the prompt on the console row; the "fork\n" exit (M3b core) reaches `Wb n'`
by `EchoLinksLine.ewc_panic_done`.
`sh_pay_rest` quantifies `Wc`, `Wb` AND `Pm` -- plan its final shape ONCE
(it is R3's to delete).
Files: UkInit, UkInitMain, UInitKernel, UInitBanner, UkSh, UShLine,
UShKernel, UkShLoop/Cd/Fork/Echo (Wb beside Wc), UInitSh, UInitBoot,
UInitBootAdequacy (Hsh_owed's second conjunct's text only if sh_pay_rest's
binder list is reported), EchoLinks only through PROLOGUE-ALTS-3's lemma.


**THREE TRAPS, all paid:**
* `git apply --3way` STAGES its result -- save rebase patches with
  `git diff HEAD -- iris/`, never `git diff`.
* the sync DELETES the `.vo` of every file you edited, so `rocq-warm check
  B.v` fails with "Cannot find a physical path bound to logical path A"
  once you have touched `A.v`.  Rebuild that one first, FROM THE REPO
  ROOT: `./gcp-rocq/run-on-gcp -q bash -lc 'cd /mnt/rocq/trees/_shared_xv6iris-2/iris
  && make -f CoqMakefile -j8 A.vo'`.  `--proofs A.vo` does NOT work.
* `rewrite !length_app` unfolds `u_banner` too (it is itself an append),
  so `length u_banner` disappears from the goal; rewrite the appends
  by name (`rewrite (length_app u_banner) (length_app (pro_alts !!! 1))`).

## WHAT LANDED THIS LAUNCH

**M6a(1) `a72323b79`** -- the credential at an arbitrary LINE BOUNDARY.
`EchoLinks.v` gained the three pure shapes `wr_pro` / `wr_blk` /
`wr_open` (`wr_owed := wr_pro ∨ wr_blk`), the half-written `wr_sp`, and
the three steps `wr_pro_dollar`, `wr_blk_dollar`, `wr_open_read`; on top
of them `ewc_owed` / `ewc_sp` / `ewc_open`, `echo_prompt_dollar`,
`echo_prompt_space`, `ewc_read`.  `UShOut.ushpr` is indexed by the
boundary, so `ksh_w_of_link_prompt` and `sh_prompt_pay_of_ushpr` hold at
EVERY prompt.  GONE: `UShOut.ushps`.

**M6a(2)a `61f015f7b`** -- the fourth shape `wr_ban` (the round's banner
owed, `j` failed sub-rounds in, at PROLOGUE-ALTS-2's own offset), with
`wr_ban_byte` / `wr_ban_pro` / `wr_ban_round0` and, on the Iris side,
`ewc_ban v n i` / `echo_banner_step` / `ewc_ban_done`.  `UInitBanner` is
rebased on them and is ROUND-AGNOSTIC: `kinit_ban n` / `kinit_own n`,
`kinit_ban0_of_eturn`, `kinit_banner_law_holds`,
`sh_prompt_pay_of_kinit_own`.  GONE: `kinit_turn0`,
`kinit_banner0_holds`, `bnr_ushpr`.

**M6a(2)b `e8b61dc6a`** -- the (A) restructure of /init's walk.

    OLD  init_boot_pay T Cns cn stc Rt Rd :=
           init_cons_dance_all T Cns stc ∗ ucons_reader cn 0 ∗ Rd 0
            ∗ ∀ N', UkInitMain.kinit_banner0 N' stc Rt
    NEW  init_boot_pay T Cns cn stc Rt Bn Rd :=
           init_cons_dance_all T Cns stc ∗ ucons_reader cn 0 ∗ Rd 0
            ∗ Bn ∗ □ (∀ N', Bn -∗ UkInitMain.kinit_banner0 N' stc Rt)

`UkInitMain` gained `kinit_ban_law stc Bn Rt := □ (Bn -∗ kinit_banner0
stc Rt)` (persistent, carried beside `init_deps` through all seven walk
lemmas, so the Löb hypothesis KEEPS it) and `kinit_round0 Bn := Bn ∨ True`
(affine, where the payment used to be).  Instantiated at
`Bn := UInitBanner.kinit_ban_any = ∃ n, kinit_ban n`, so the law is
round-agnostic and /init's walk names no round.  `echo_Hinit_boot`'s
statement and `Hsh_owed` did not move; the audit md5 is unchanged.
GONE: `kinit_banner0_pay_holds`, `proc_upto0_banner`, `pro_pin_zero`.

## /INIT'S ARMS AFTER (A)

* ROUND 0's banner: through the link, from the era's turn at stage 0.
* ROUND k > 0's banner: PAYABLE at the same law, waiting only for a
  credential to reach the restart head -- i.e. for a child's exit payload
  to carry one.  Until then the restart head re-enters on `kinit_round0`'s
  `True` arm and prints through the flagged deposit, as before.
* `die_dw` (wait returned -1) is **NOT deletable**.  The -1 reason is
  `UserChildren.wait_why cs gn nullst = ⌜nullst = false⌝ ∨ ⌜cs = ∅⌝ ∨
  ChildTok.kill_shot gn`.  Two arms die (`cs = ∅` against `γsh ∈ cs`;
  `nullst = false` once the leaf's `b` stops being existential --
  `UexecRet.uwait_ans` hides it, `uwait_ans_at` does not), but the third,
  a KILLED /init, is real: a killed process runs on to its next trap and
  does print the diagnostic.  Deleting the arm needs a kernel row
  `kill_shot gn -∗ riscv_kill_cred` (then the taint pays it, K1's route);
  there is none today.  So the three die arms all stay, M6b's.

## THE REST OF THE LANE -- THE ANALYSIS THAT MATTERS

There is NO circularity: round 0 has the credential from `eturn`, and
every later round gets it from the child it reaped.  What there IS is a
SHAPE MISMATCH across the fork, and it decides the remaining design:

* what /init LENDS a child is the credential at the round's PROMPT
  (`wr_pro`/`ewc_owed`, what its banner left behind);
* what a child HANDS BACK at its exit is the credential at the NEXT
  round's BANNER (`wr_ban`) -- /init's exec-failed child files
  `pro_alts !!! 1` and the prologue continues; the shell files
  `line_alts !!! 3` ("fork\n") and the block continues into the new
  round's prologue;
* the two are different propositions at the SAME count, and `Rd` (the
  lease's payload family) is ONE family used for both directions.

Hence, with `Rc := Q (-1)` as today, no single `Rd` works: ban-shaped is
false at the shell's mid-run boundaries, prompt-shaped is false at
/init's loop head, and a disjunction of the two cannot be resolved by
either side (they differ only in the EXISTENTIAL stage `P`).

**THE ONLY PLACEHOLDER-FREE SHAPE IS `Rc ≠ Q (-1)`** -- which is
D8(iii)'s own ruling ("`Q (-1)` can no longer serve as sh's entry lend;
`UShKernel.sh_slot_of_kexec` and the constructors take the RAW bundle"):

    Rc := ucons_reader cn n ∗ upos_a γ n ∗ <the PROMPT credential>
    Q  := ucons_pay cn γ T Rd,  with Rd n carrying the BAN credential

`wp_uk_ecall_fork` already takes the two independently.  `UserConsole`'s
`uinit_lend` has to mint the pair and build the lend at the prompt shape
while the tok stays at the ban shape (the coordinator has allowed
`UserConsole.v`), and D3's UNBUNDLING of `UkSh.ush_at` follows: the
shell's loop invariant keeps the PIECES (`Pm`) and the credential, and
assembles the payload only where it actually exits or forks -- which is
exactly where the ban shape is true (after "fork\n"), the taint paying
the kill arms.

WHAT SH'S LOOP THEN LOOKS LIKE, and it CLOSES with no placeholder:

    loop head, count n:  wr_pro (n = 0, the round's choice still open)
                         or wr_blk (n > 0, the line's block still owed)
    prompt "$ ":         echo_prompt_dollar (echo_link_pro at a = 0, or
                         echo_link_blk at a = 2 -- the child recorded no
                         choice) then echo_prompt_space  ->  wr_open
    gets (17 bytes):     ewc_read (the cursor does not move --
                         EchoOut.pcount_echo)              ->  wr_blk at n+17
    back edge:           wr_blk, which is the loop head's shape again

M3b's `Rc` at `UkShFork.v:319` is then `ewc_owed`/`ewc_blk` at `np0`, the
shape `echo_link_blk` wants at the child's first byte 'h'; when the child
runs echo it files `a = 0` instead of sh's `a = 2` and sh writes the
alternative's trailing "$ " through `echo_link_w`.

STEPS, in the order they can land green:

 1. `UShLine.ush_mid γ γp n` gains `E_lb v n` (persistent; the read's own
    receipt supplies it -- `read_ret` hands `E_lb v (n + |ws|)` whenever
    `ws <> []`).  That is what lets the boundary step spend `ewc_read`.
 2. `UkSh` takes `Wc`/`Wc'` beside `Pm` (the credential at a boundary and
    after the prompt) with the routed hypotheses; `ush_prompt_law` is
    ALREADY PROVED -- it is `UShOut.ksh_w_of_link_prompt` at the boundary
    index (M6a(1)) -- so only the routing through `UShKernel` ->
    `UInitSh` -> `UInitBoot` is missing.  sh's loop head, prompt site and
    gets loop thread them; `ush_prompt_in`/`sh_prompt_pay` stay as the
    ENTRY route.
 3. D3's unbundling + `Rc ≠ Q (-1)` + `Rd`'s ban credential; the shell's
    "fork\n" through the link; /init's exec-failed child's diagnostic
    through the prologue-choice link (`die_de`).  When those land the
    `∨ True` arms (`kinit_round0`, `Rt ∨ True`, `sh_prompt_at`) are dead
    and can be dropped from the statements.
 4. M3b core in opaque terms, then the wait redemption on TRAP-ROWS-5's
    `_pid` rows (`wp_uk_ecall_wait_null_pid`, `uwait_ans_pid_mine`;
    `wp_kshr_wait` needs the `_pid` twin in `UkShRun.v`).

## GATE (io54)

COMPILED=5 EXIT=0, zero Error; `make -f CoqMakefile -n` 0 ROCQ compile;
audit-only md5 `57f7327206c4b276d05035342fea8ecf` (unchanged);
`lemma_diff --ref origin/main` six GONE, all justified in the commit
messages; no Admitted; `--check-dumps` clean.
