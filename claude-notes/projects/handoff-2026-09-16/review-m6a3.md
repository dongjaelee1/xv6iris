# Review: IO-LEAF M6a(3) steps 1 and 2 (read-only, 2026-09-14)

Tree read: `/shared/xv6iris-2` on `lane/io-leaf`, step 1 = `a43341d28`, step 2 =
the working tree. NOTE: the tree moved while I read it (the coordinator is
iterating on `UkSh.v`: build `io56` failed at `iSpecialize: "Hwc" not found`, and
the live tree already adds `[Hans Hwc]` and `ush_pstate ... ∗ ush_posb l 0`).
Nothing above `UkSh.v` has been compiled yet; findings 1 and 5 are about files
the build has not reached. Line numbers are the live tree's.

Terms (defined once). A CREDENTIAL is a linear separation-logic resource whose
possession licenses one console write and which the write transforms. The
LEASE is the console-input resource init lends the shell (`UserConsole.ucons_pay`
= reader token + position half + `Rd n`, or the taint). A SLOT is a place in a
loop invariant reserved for a resource. AFFINE means the holder may drop it.
A `∨ True` PLACEHOLDER is a disjunct that lets a slot be discharged with nothing
(durable-notes "Vacuity": never write one; leave the conjunct out). A
SECTION VARIABLE (`Context`) is abstracted onto every definition/lemma that
uses it, in declaration order, at `End Section`. The TRUSTED SURFACE is the set
of statements the owner must read to believe the theorem (`Hsh_owed`'s two
conjuncts among them).

---------------------------------------------------------------------------

## Finding 1 (BLOCKING; trusted surface moves): `ush_rest_l` now takes `Wc`, and three callers plus `sh_pay_rest` were not updated

Chain: `UkSh.ush_rest_l` (`UkSh.v:6611`) mentions `ush_loop_head` (`:6478`)
and `ush_pstate` (`:6439`); `ush_pstate` now carries `ush_posb l 0` (`:6441`,
live tree); `ush_posb` (`:1667`) carries `ush_wcp` (`:1503`), which mentions the
section variable `Wc` (`:1485`). Coq abstracts transitively, so after
`End UkSh` the constant is

    UkSh.ush_rest_l N γp T Wc R          (N :493, γp :509, T :514, Wc :1485)

exactly as `ush_pstate`/`ush_loop_head` became `N γp T Wc ...`. The diff does
not touch these four sites, which will fail with a type error (an `iProp` in
the `nat -> nat -> iProp` slot):

- `iris/UShKernel.v:596` and `:783` — `ush_rest_l N γp T (R (ukn_t N) ...)`.
- `iris/UkShFork.v:982` — `UkSh.ush_rest_l N γp T (UkShLoop.ushl_R N sz)`.
- `iris/UInitSh.v:513` (inside `sh_pay_rest`) and `:533` (inside `sh_pay`).

`UInitSh.sh_pay_rest` (`:509-514`) is the second conjunct of `Hsh_owed`
(`UInitBootAdequacy.v:140`, `UInitBoot.v:570`). It cannot keep its type. So the
step-2 plan's "`Hsh_owed` untouched" is false: the trusted obligation must
quantify the credential family. Fix (smallest honest one):

    Definition sh_pay_rest Rsh :=
      (∀ γp N T (Wc : nat -> nat -> iProp Σ), ⌜Persistent T⌝ -∗
         ush_rest_l (PS := uprogSG_free) N γp T Wc (Rsh ...))%I.

and `sh_pay` (`:533`) takes the same `∀ Wc` (its use is at the concrete
`ewc_cred`, so `sh_pay_of_parts` instantiates). The discharger
`UkShFork.ushf_rest_of_body` (`:975-1020`) is generic in `Wc` (it only passes
`ush_posb` through `ush_posb_at`/`ush_posb_of` at `UkShFork.v:285`/`:468`), so
the `∀ Wc` is provable at the same cost as today. Report OLD/NEW to the owner
(checkpoint §5), and since SH-LINE R3 must restate `sh_pay_rest` at the
application's taint anyway (checkpoint §1, RULED), fold BOTH quantifier changes
into ONE trusted move if the lane order allows; otherwise land this one now and
say so. Step 3 will add a second family (`Pm` must enter `ush_posb`, below), so
plan the final shape of `sh_pay_rest` before touching it twice.

## Finding 2 (design, medium): `Wc n 0 := ewc_owed` is not the loop's back-edge shape once a child has run

`ewc_pr v n 0 = ewc_owed v n = wr_pro ∨ wr_blk` (`EchoLinks.v:570/:87/:95`):
"the '$' is the FIRST byte of something" (a prologue alternative at `a = 0`, or
the line's block at `a = 2` when the child recorded no choice). After a
SUCCESSFUL echo the child has already recorded `a = 0` and written twelve
bytes; sh's `"$ "` is then two ordinary `echo_link_w` bytes, and the credential
sh holds at that prompt is "block chosen, cursor at `P_blk + 12`, `cs ++ [0]`"
— a shape `ewc_pr` has no index for. The D8 review §2 already says the prompt
site needs three link shapes. Consequences:

- `UkSh.ush_prompt_law` (`:1487`) is the right ABSTRACTION (`Wc n 0 → Wc n 2`),
  and `Wc n 2 = ewc_open` IS the post-prompt shape on both routes
  (`wr_open ps (cs++[0]) n P` holds after `W` twice). So UkSh survives.
- The INSTANTIATION at the top (`UInitBoot.v:~777`, `ewc_cred ... n 0`) is
  final only for turns where no child wrote. M3b core must WIDEN `ewc_owed`
  (or `ewc_pr _ _ 0`) at `EchoLinks` with a third arm and extend
  `echo_prompt_dollar` (`EchoLinks.v:706`) to it; nothing in UkSh changes.
  Record this in the M6a(3) note so nobody reads `ush_prompt_law_holds` as the
  end of the prompt story.

## Finding 3 (vacuity/inventory, medium): the new `∨ True` is exactly the pattern the notes forbid, and its left arm is uninhabited anywhere today

`ush_wcp l n p := (⌜ush_fd2p l⌝ ∗ Wc n p) ∨ True` (`UkSh.v:1503`). Every
producer of `ush_posb` in the system today takes the right arm: sh's entry
(`UShLine.ush_posb_of_at`, `:584-601`, via `ush_posb_of` → `ush_wcp_triv`),
the fork arm's re-entry (`UkShFork.v:468`), `ush_gets_done_0` (`UkSh.v:~2050`).
So `ush_prompt_law`, `ush_wc_read`, `ksh_w_of_wcp` and `ush_gets_done_line`'s
left path are proved but never spent on a real credential: step 2 proves
nothing new about the wire, and the endgame audit's `∨ True` inventory GROWS
by one (the prompt site now has three placeholders: `ush_prompt_in`,
`sh_prompt_at`, `ush_wcp`). This is consistent with the handover's "step 2 is
only routing", and it is NOT a violation of ruling A (which is about the
lease `Rd`), but it is a violation of durable-notes "Vacuity" in letter, so:
say in the commit message and in the audit that `ush_wcp`'s right arm is
step-3-dead together with `ush_prompt_in`/`sh_prompt_at`, and that the left
arm is uninhabited until step 3.

Is the coordinator right that the entry cannot supply `Wc np 0` NOW? Yes.
`UInitBanner.kinit_own n` (`:285`) IS `ewc_cred T γ (S gen_id) n 0`
definitionally, so init holds `Wc n 0` after every paid banner — but its `n`
is `kinit_ban_any`'s existential (`:393`, packed at
`kinit_ban_any_of_eturn`), while the lease's `np` is `uinit_tok`'s
(`UserConsole.v:368`), and `UkInit.init_exec_sup_pos`'s `Rt` (`:1649`) is a
bare `iProp`, not indexed by the `n` of the `upos γ n` beside it.
`init_boot_pay` (`UInitKernel.v:620`) separates `Rd 0` from `Bn`, so even at
round 0 (both at 0) the walk has lost the tie by the fork. The other routes
fail too: `sh_prompt_pay`'s conversion drops its post (`UShOut`
`sh_prompt_pay_of_ushpr`, `iIntros "[$ _]"`) and its `C` is opaque;
`uinit_lend` (`:388`) mints `γ` at the token's `n` but knows no credential.
The ONLY tie is one existential over reader, `Rd n` AND the credential — i.e.
the credential riding in `Rd`, which is step 3. Verdict: acceptable interim.

## Finding 4 (Q2 detail): what the drops lose

- `ush_gets_done_line` (`UkSh.v:~2060`) on the right arm: loses nothing (there
  was nothing). Fine.
- `ush_gets_done_0` drops `Wc n 2` AFTER the prompt was written. Reachable only
  with fd 0 CLOSED at the read (`Hcl`): on the console arm EOF is refuted
  (`UConsLine.disc_no_ctrl_d`) and -1 by T2. With fd 0 closed, sh's own
  preamble opened nothing, so fd 2 is closed too and `⌜ush_fd2p l⌝` is false
  — the slot was already on `True`. No real loss, but the leaf does not say
  so; a one-line comment there is enough now, and step 3's closed-arm guard
  (below) makes it a theorem.
- `ush_posb_at` at the fork (`UkShFork.v:285`): drops the credential, re-enters
  on `True`. Acceptable while `sh_deps` is assumed. But note the consequence
  for step 3: on the real transcript EVERY turn forks, so after step 3 ties the
  entry, only the FIRST prompt is paid through the slot; the second needs the
  fork to LEND `Wc` to the child and the child's payload to hand the
  "12 bytes in" shape back (M3b core, and Finding 2's widening).
- No lemma is proved for the wrong reason: the right arms claim nothing, and
  `ush_wc_read`/`sh_prompt_law` are hypotheses satisfiable at any `Wc` (at
  `fun _ _ => True` trivially; at `ewc_cred` proved).

## Finding 5 (Q5): argument orders — all correct except the `ush_rest_l` omission; one dead binder

Derived from `UkSh.v`'s declaration order: explicit section variables are
`N :493`, `γp :509`, `T :514`, `Hpsok_free :542`, `Wc :1485`, `Pm :1737`,
`ush_pm_of_at :1745`, `ush_at_of_pm :1747`, `ush_at_of_pm_taint :1754`,
`ush_wc_read :1761`, `cn :2205`, `ush_read_leaf :2207`; everything in
backticks/braces (`HT`, `Hpay`, `SG`, `PS`, the cameras) is implicit.

- `wp_ksh_start N γp T Hpsok_free Wc Pm Hpm1 Hpm2 Hpm3 Hwc cn Hrl ...`
  (`UShKernel.v:671-676`): correct (a Lemma inherits what its proof uses;
  `wp_ksh_start`'s proof reaches `ush_wc_read` through `gets`).
- `UkSh.ush_posb N γp T Wc l 0` (UkShFork/UkShEcho/UShLine/UInitBoot/
  UShKernel/UInitSh): correct — `ush_posb` uses `ush_at` (N, γp), `T`, `Wc`;
  not `Pm` (declared after it).
- `UkSh.ush_pstate N γp T Wc`, `UkSh.ush_loop_head N γp T Wc` (UkShCd/UkShFork/
  UkShLoop): correct. UkShCd's `Local Notation ush_loop_head := (UkSh.ush_loop_head N γp)` (`:211`) is unused.
- `UkSh.ush_prompt_law N Wc` (`UShKernel.v:438`): correct — its body uses
  `ksh_w` (N only), `ustd γfd`, `Wc`; not `T`.
- `UkSh.ush_wcp` would be `ush_wcp Wc l n p` (no `N`); no external use.
- `UkSh.ush_rest_l N γp T Wc R`: MISSED (Finding 1).
- `sh_uexec_slot R γp cn T K Q Pm Wc Hrl Hpm1 Hpm2 Hpm3 Hwc W' n0 n Hbd`
  (`UShKernel.v:893`): matches the lemma's binder order.
- `UShOut.sh_prompt_law_holds (echo_taint γ) γ (PS := uprogSG_free)`
  (`UInitBoot.v:~783`): correct. UShOut's `Context (γp : gname)` (`:176`) is
  used by nothing in the file (`grep γp` finds only the binder), so no lemma
  takes it. It is a dead binder; delete it when convenient.
- Files not in the diff (`UkShRun`, `UkShMain`, `UkShDiag`, `UkShParse*`)
  reference none of the re-aritied names. `UkShEcho.ush_pstate_at`/
  `ush_echo_round_carry` have no external callers.

## Q3: step 3's shape, given step 2

`Rd`'s job: carry what init's restart head must READ (the reader's half, the
boundary fact, and the credential for the NEXT banner). Sketch:

1. Families. UkSh gains a second opaque family `Wb : nat -> iProp` ("the
   banner credential at boundary n"; at the top `UInitBanner.kinit_ban n`,
   `:282`) beside `Wc`. `Rd n := UShLine.ush_rd_pin γ n ∗ (kinit_ban n ∨ ⌜stc = FdClosed⌝)`,
   built in `UInitBoot` where `stc = init_cons_fd` is known. `Rd 0` at boot
   comes whole from `kinit_ban0_of_eturn` (`UInitBanner.v:309`): the reader
   half and the ban half at ONE count. `Bn` leaves `init_boot_pay`
   (`UInitKernel.v:620`) and `kinit_round0` (`UkInitMain.v:1039`) dies.
2. init's head (`wp_kinit_main_loop`, `UkInitMain.v:1116`): open
   `uinit_tok`'s left arm → `reader n ∗ rd_pin n ∗ (ban n ∨ closed)`. Console
   arm: `kinit_banner_law_holds` (`UInitBanner.v:325`, already round-agnostic)
   turns `ban n` into `kinit_own n = Wc n 0`. Closed arm: the banner is a
   closed-fd write (`kinit_w1_of_closed`, init twin of the RULED
   `ksh_w_of_closed`; nothing reaches the wire) and the guard is kept. Then
   `upos_alloc n` (the inside of `uinit_lend`, `UserConsole.v:388`; the
   tok→lend lemma becomes init-side because the ban half has been converted
   and must not be re-folded).
3. `Rc := reader n ∗ upos_a γ n ∗ rd_pin n ∗ upos γ n ∗ (Wc n 0 ∨ ⌜stc = FdClosed⌝)`
   = `Pm n ∗ (Wc n 0 ∨ guard)` at `Pm := UShLine.ush_mid γ` (`UShLine.v:~505`,
   which already bundles reader/upos/upos_a/dl/E_lb). `Q := ucons_pay cn γ T Rd`
   unchanged in form. `wp_kinit_fork` (`:757`) and `wp_kinit_main_child`
   (`:520`) lose `(Rt ∨ True)` (`:574/:789/:883`); `init_exec_sup_pos`
   (`UkInit.v:1648`) takes `Pm' n -∗ (Wc n 0 ∨ guard) -∗` instead of
   `upos -∗ (Rt ∨ True) -∗ ucons_pay (-1) -∗`, with `Rt` replaced by the
   nat-indexed family (`init_exec_sup_lend := □ ∀ γ n, ...` already
   quantifies `n`).
4. `sh_slot_of_kexec`/`sh_uexec_slot` (`UShKernel.v:474/:709`): the payload
   premise `Q (-1)` becomes the raw `Pm n ∗ (Wc n 0 ∨ guard)` (D8(iii)); `Hbd`
   (`:498-501`) becomes `Pm n -∗ (Wc n 0 ∨ guard) -∗ ush_posb ... l 0` with
   the left arm inhabited; `sh_prompt_pay`, `sh_prompt_at`, `ush_prompt_in`,
   `ush_prompt_in_triv` and `ksh_w_of_prompt_in` are deleted; `ush_wcp`'s
   `∨ True` becomes `∨ ⌜stc = FdClosed⌝` (a GUARDED arm, durable-notes
   "Shaping a change": the guard is a flag the entry already carries via
   `ufd_head T stc`), and the loop's pure row `⌜ush_fd0p l⌝` gets a fd-2
   companion so the slot need not be ledger-indexed.
5. `ush_at`'s unbundling: `ush_posb l p := (∃ n, ⌜bnd n⌝ ∗ Pm n ∗ slot) ∨ (T ∗ ush_pos)`.
   `Context (Pm)` and its hypotheses move above `:1667` (they need only
   `ush_at`/`ush_pos`, `:1638-1641`). `ush_at_of_pm` (`:1747`, "the pieces go
   back together at a boundary") becomes FALSE at the new `Rd` (the pieces do
   not contain a ban credential) and is replaced by two exit assemblers:
   `Pm n -∗ Wb n -∗ ukn_pay N (-1)` (after the "fork\n" panic; the step
   `Wc n 0 → Wb n` is a new EchoLinks lemma: `echo_link_blk` at `a = 3` then
   four `W`, landing on `wr_ban` with `cs ++ [3]`, `EchoLinks.v:222`) and
   `⌜stc = FdClosed⌝ -∗ Pm n -∗ ukn_pay N (-1)`; `ush_at_of_pm_taint` stays.
   sh's `exit` at `UkSh.v:7147-7150` (`ush_pos_pay`) is reached only from
   `ush_gets_done_0`, i.e. the closed arm, so it uses the guard.
   `wp_ksh_memset_null` (`:2542`, takes `ukn_pay N (-1)` as a resource) is the
   CHILD's and pays `Q_child`, not `Rd` — unaffected here.
6. `sh_pay_rest` then quantifies `Wc` AND `Pm` (Finding 1: plan it once).

Obstacles, concretely:
(a) sh's exit on a shut fd 0: it holds no credential; the arm is reachable only
    on the all-closed ledger (`UInitFd.ufd_l0`), so the honest payload is the
    GUARD, not a prompt-shaped credential. `Rd n` must therefore be a
    disjunction — ban-shaped ∨ closed-guard (the taint is already
    `ucons_pay`'s right arm) — and NOT ban ∨ prompt-shaped: on the console arm
    sh never exits normally (EOF refuted, -1 refuted), so a prompt-shaped arm
    at init's head would be unreachable, and init could not consume it
    honestly anyway (a banner right after `"$ "` is in no `line_alts`/`pro_alts`
    entry). Do not add it.
(b) init's closed-fd head arm lends `Pm n ∗ ⌜stc = FdClosed⌝`; its own banner
    that round goes through the closed-fd write leaf; the era's ban credential
    at round 0 on that arm is dropped (affine) or kept unconverted — either is
    honest since nothing reaches the wire.
(c) `sfork_lend` (FORK-REFUND): the -1 arm returns `Rc` whole, so `die_df`
    holds `Pm n ∗ Wc n 0` and pays `"init: fork failed\n"` through
    `echo_link_pro` at `a = 2`. That needs `wr_pro`, and `Wc n 0` is
    `wr_pro ∨ wr_blk`; at a round start `wr_blk` is refutable
    (`n/17 = length cs` vs `S (length cs)`), so no new shape — one small
    EchoLinks lemma `ewc_owed_round_start`. sh's own fork1 -1 arm
    (`UkShFork.v:319`, `Rc := emp`) is M3b core's.
(d) `∨ True` arms that die at step 3: `kinit_round0`; the six `(Rt ∨ True)`
    (`UkInitMain.v:574/789/837/883/1046`, `UkInit.v:1658`) on the console arm
    (the closed arm becomes the guard, not a deletion); `ush_prompt_in` +
    `_triv`; `sh_prompt_at` + `_triv`; `UInitSh.v:1075/1127/1173/1202`
    (become the guard); `ush_wcp`'s right arm (becomes the guard). NOT dying:
    `UkShFork.v:320` `Q := fun _ => True, Rc := emp` and the
    `(⊢ ukn_pay N (-1))` premises (M3b core); `ush_read_ans_of_era`'s
    discard is half-closed by step 1 (`E_lb` now carried; `cs_lb`/`ps_lb`
    still dropped, harmless). The checkpoint's "after step 3 every `∨ True`
    arm is dead" is overstated; say "every init/sh-entry placeholder".

## Q4: `die_dw` — the candidate row is not derivable for a trivial-payload init

The row (`SchedCtx.kill_row`, `:262`) keeps, once the flag is set,
`kill_shot gn ∗ (kill_owed gn ∨ taken_at gn)`; `kill_paid` (`:338`) adds
`my_pay gn Q ∗ □ (riscv_kill_cred -∗ Q (-1))`. A writer that paid with the
taint (`SpecSetkilled`'s left arm) converts it through that wand and stores
`kill_owed`; the row FORGETS which arm paid. For init, `Q = fun _ => True`
(`UInitBoot.v:477-490`, userinit's choice in `InitBoot.init_boot_bundle`), so
`kill_owed gn_init = my_pay gn_init (fun _ => True) ∗ True` — persistent and
free to anyone who has read the row. Hence `□ (kill_shot gn -∗ riscv_kill_cred)`
is FALSE as a consequence of the current row, for init in particular. To make
it derivable you need all three of:

1. init's payload at -1 non-free: an exclusive ghost token `init_tok` that init
   holds for its whole life (`Q := fun _ => init_tok`, status-independent so
   `ukn_const` survives; `Hpayfree` at `UkInitMain.v:124` becomes a LINEAR
   resource threaded through the seven walk lemmas, and init's own `exit(1)`
   arms pay it). Trusted change: `InitBoot.init_boot_bundle`'s
   `(fun _ => True)` and the `my_pay (uvis_gen W') (fun _ => True)` sites in
   `UInitBoot`/`UInitKernel`.
2. `kill_row`'s paid arm remembering the taint when the taint paid
   (`□ riscv_kill_cred ∨ (kill_owed gn ∨ taken_at gn)`), with the
   setkilled/kkill proofs storing the left arm — a kernel spec change.
3. A reader leaf (in `killed()`/`wait`'s -1-by-kill arm, the only place the
   row is open with the shot in hand) that lets a caller holding
   `my_pay gn Q ∗ Q (-1)` refute `kill_owed` (exclusive token) AND refute
   `taken_at gn` for a LIVE caller (kexit has not run) — the latter needs
   a proc-state fact the row does not carry today.

That is three kernel-side items against "the kernel rows are complete". The
honest alternative: leave `die_dw` on `init_deps`' `udepw_law 16` (it is
unreachable in the real system — only an unverified program can call
`kill(1)`, and none runs under the discipline — but init's per-process proof
cannot see that). Cost to the endgame: `Hsh_deps` cannot be deleted whole,
because `init_deps`' 16 is built from it (`UInitBoot.v:674`,
`init_deps_of_laws`). Narrow it instead: split `udepw_law 16` out of
`init_deps` into a single owed Coq hypothesis stated at init's one site
("init's diagnostic write after being killed is free"), delete `sh_deps` from
`Hsh_owed` once the other three leaves are paid, and present the theorem as
"modulo that one arm" with the reachability argument in prose. Owner's call;
put it to them with both prices.

## Minor

- `ewc_pr`'s `match p` sends every `p >= 2` to `ewc_open` (`EchoLinks.v:~604`);
  harmless (only 0 and 2 are used) but a three-constructor index would refuse
  a wrong `p` at compile time.
- `ush_wcp` is ledger-indexed only so `ksh_w_of_wcp` can instantiate the law;
  the step-3 loop row makes the index unnecessary (Q3 item 4).
- Step 1 (`a43341d28`) is fine: `E_lb v n` is persistent, rides under the
  existing existential (last position, per "Shaping a change"), and the
  far-end bound is derived correctly for both the empty and the delivered
  window (`UShLine.v:~990-1005`).
