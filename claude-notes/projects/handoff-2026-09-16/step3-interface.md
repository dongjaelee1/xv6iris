# IO-LEAF STEP 3 -- THE INTERFACE CONTRACT (coordinator, 2026-09-14)

Step 3 of the io-leaf plan (`claude-notes/projects/handoff-2026-09-16/io-leaf-handover.md`,
"STEP 3 -- THE DESIGN OF RECORD") is cut in two lanes that meet at the
names below.  Lane S (the shell side, checkout `-disc`) and lane I (the
init side, the main checkout, the coordinator).  Every name and statement
here is binding; where the text says "step 4" it means the arm stays
AFFINE (`∨ True`) in step 3 and is killed by step 4 (M3b core + the wait
redemption + PROLOGUE-ALTS-3's two lemmas).

## Vocabulary

* `Pm n`  -- the shell's mid-line PIECES of the console lease at input
  count `n` (`UShLine.ush_mid`: both halves of the position pair, the
  ring's reader token, the era's read half `dl_cnt` and the writer's
  bound `E_lb`).
* `Wc n p` -- the shell's WRITE credential at line boundary `n` with `p`
  prompt bytes out (top: `EchoLinks.ewc_cred T γ (S gen_id) n p`).
* `Wb n`  -- the BANNER-OWED credential at boundary `n`: init's next
  round's banner is payable from it (top: `UInitBanner.kinit_ban n =
  ∃ v, era_pin ∗ ewc_ban v n 0`).  NEW section parameter everywhere `Wc`
  is one, declared IMMEDIATELY AFTER `Wc` (`Context (Wb : nat -> iProp Σ)`).
* `Rdl n` -- the READ side of the lease at `n` (`UShLine.ush_rd_pin γ n`,
  today's `Rd`).
* THE EXIT FAMILY `Rd n := Rdl n ∗ (Wb n ∨ True)` -- what sh's exit payload
  carries per count, spelled ONCE as `UkInit.init_rd Rdl Wb n`
  (`UkInit.init_rd_cred Wb n := Wb n ∨ True` is the affine credential; step
  4 makes it `Wb n`).  `ukn_pay N = ucons_pay cn γp T (init_rd Rdl Wb)`.
* THE LEND: `ucons_pay cn γp T Rdl (-1)` (the read pieces, or the taint)
  PLUS a credential correlated with init's descriptor row (below).

## UkSh (lane S)

```
Context (Wc : nat -> nat -> iProp Σ).
Context (Wb : nat -> iProp Σ).            (* NEW, right after Wc *)

Definition ush_wcp (l : list fdstate) (n p : nat) : iProp Σ :=
  ((⌜ush_fd0c l /\ ush_fd2p l⌝ ∗ Wc n p)          (* the BOTH-CONSOLE arm *)
   ∨ (⌜l !! 2%nat = Some FdClosed⌝ ∗ Wb n)       (* the CLOSED arm: the prompt
                                                    writes nothing (UkWriteClosed.
                                                    ksh_w_of_closed); the credential
                                                    is carried unchanged at every p *)
   ∨ True)%I.                                     (* the AFFINE arm -- step 4 *)
```
* `ksh_w_of_wcp`: credential arm through `ush_prompt_law`; closed arm
  through `UkWriteClosed.ksh_w_of_closed` with the credential framed
  (`ksh_w_mono`); True arm through the free law (`ksh_w_of_prompt_in` at
  `ush_prompt_in_triv`, or whatever is left once `ush_prompt_in` dies --
  see below).
* `ush_wcp_cons l k n p` (the console preamble installs the console at
  `k`, the lowest closed slot): credential arm stays; closed arm stays
  when `k <> 2`; when `k = 2` it goes to the True arm (step 4: to the
  credential arm through `Wb n -∗ Wc n 0`, PROLOGUE-ALTS-3's ban arm).
* `Context (Pm)` and `ush_lease`, `ush_pm_of_at`, `ush_at_of_pm`,
  `ush_at_of_pm_taint`, `ush_wc_read` MOVE ABOVE `ush_posb` (all four
  hypotheses KEPT in step 3), plus ONE NEW hypothesis:
  ```
  Hypothesis ush_at_of_pm_wb :
    forall n : nat, ush_bnd n -> ⊢ Pm n -∗ Wb n -∗ ush_at n.
  ```
  (the exit assembler at the shut-fd-0 exit's closed arm; discharged by
  `UShLine.ush_at_of_mid_wb` -- the payload's `Rd n` left arm).
* ```
  Definition ush_posb (l : list fdstate) (p : nat) : iProp Σ :=
    ((∃ n : nat, ⌜ush_bnd n⌝ ∗ Pm n ∗ ush_wcp l n p) ∨ (T ∗ ush_pos))%I.
  ```
  with `ush_pos_of_posb`, `ush_posb_at` (`∃ n, (⌜bnd n⌝ ∨ T) ∗ ush_at n`,
  credential dropped -- the fork arm's accessor, step 4 rewrites it),
  `ush_posb_of l p n : (⌜bnd n⌝ ∨ T) -∗ ush_at n -∗ ush_posb l p` (through
  `ush_pm_of_at`; the True arm), `ush_posb_of_wc l p n : ush_bnd n -> Pm n
  -∗ ush_wcp l n p -∗ ush_posb l p`, `ush_posb_cons`, `ush_posb_taint`.
* `ush_gets_done`: keep the shape; the constructors become
  ```
  ush_gets_done_0    : ush_bnd n0 -> l !! 0%nat = Some FdClosed ->
                       Pm n0 -∗ ush_wcp l n0 2%nat -∗ ush_gets_done l 0%nat f
  ```
  (credential arm REFUTED: `ush_fd0c` against the shut slot 0 --
  `ush_fd0c_not_closed`; closed arm: `ush_at_of_pm_wb`; True arm:
  `ush_at_of_pm`; the call site at UkSh.v:~3590 has `Hcl` in scope),
  ```
  ush_gets_done_line : ush_bnd n0 -> ush_line_is f 0 17 ->
                       ush_wcp l n0 2%nat -∗ Pm (n0 + 17) -∗ ush_gets_done l 17 f
  ```
  (credential arm: `ush_wc_read` to the credential arm at `n0 + 17`;
  closed arm: to the True arm at `n0 + 17` (step 4: PROLOGUE-ALTS-3's
  discipline lemma refutes it); True arm: True arm).
* `ush_prompt_in` / `ush_promptw` / `ush_prompt_in_triv` / `_cons`,
  `ush_loop_head`'s prompt-in binder (`UkShLoop.ushl_head_of_R` passes
  `ush_prompt_in_triv`), `ksh_w_of_prompt_in`: DELETE the entry route --
  the credential now arrives in `ush_wcp` at the right count.  The prompt
  on the True arm goes through the free law directly.  If deleting drags
  in more than the walk's prompt site, keep `ksh_w_of_prompt_in` at a
  `sh_deps`-only statement and delete the rest.
* `ush_pstate l` carries `ush_posb l 0%nat` (unchanged shape);
  `ush_rest_l`, `ush_loop_head`, `ush_gen_slot` etc. mechanical.
* The dead `sh_deps -∗` premise of `wp_ksh_read` (~2212; call ~3507
  passes "Hdp"): remove it while you are there.

## Consumers of UkSh (lane S)

`UkShLoop` (`ushl_head T Wc Wb l sz`, `ushl_head_of_R`), `UkShCd`,
`UkShFork`, `UkShEcho`, `UkShRun`, `UkShDiag`, `UkShMain` (if any):
`Context (Wb)` right after `Context (Wc)`; every `UkSh.ush_posb N γp T Wc
…` becomes `UkSh.ush_posb N γp T Wc Wb Pm …` -- check the real abstracted
binder list with `About UkSh.ush_posb` (Rocq abstracts only the section
variables a definition uses; `ush_wcp` takes `Wc Wb l n p` and no `N`).
The fork arm's re-entry (UkShFork.v:~285 `ush_posb_at`, ~468
`ush_posb_of`) stays on `ush_at` (the True arm) in step 3.

## The entry (lane S: UShLine + UShKernel + UShOut)

* `UShLine`:
  ```
  Definition ush_rd_x (γ : echo_gn) (Wb : nat -> iProp Σ) (n : nat) : iProp Σ :=
    UkInit.init_rd (ush_rd_pin γ) Wb n.        (* = ush_rd_pin γ n ∗ (Wb n ∨ True) *)
  ```
  (`UShLine` may `Require Import UkInit` -- check the import graph; if
  UkInit is above UShLine, put `init_rd`/`init_rd_cred` in `UserConsole`
  instead and tell the coordinator).  Every premise `ukn_pay N =
  ucons_pay fsc_cons γp T (ush_rd_pin γ)` becomes `… (ush_rd_x γ Wb)`;
  `ush_mid_of_at` (drops the credential), `ush_at_of_mid` (right arm),
  NEW `ush_at_of_mid_wb : … -> ush_bnd n -> ⊢ ush_mid γ γp n -∗ Wb n -∗
  UkSh.ush_at N γp n` (left arm), `ush_at_of_mid_taint`,
  `ush_read_recv_leaf_holds` at the new equation.  `ush_posb_of_at` is
  REPLACED by the entry law:
  ```
  Lemma ush_posb_of_lend (γ) (T) `{!Persistent T} (N) (γp) (Wc) (Wb) (l) (n) :
    ukn_pay N = ucons_pay fsc_cons γp T (ush_rd_x γ Wb) ->
    ⊢ upos γp n -∗ ucons_pay fsc_cons γp T (ush_rd_pin γ) (-1) -∗
      UkSh.ush_wcp Wc Wb l n 0%nat -∗
      UkSh.ush_posb N γp T Wc Wb (ush_mid γ γp) l 0%nat.
  ```
  (the lend's token arm: `upos_agree` pins the count, the pieces are
  `ush_mid`; its taint arm: `T ∗ ush_pos` with `ush_pos` from
  `ucons_pay_taint` at the exit family).
* `UShKernel.sh_uexec_slot` / `sh_slot_of_kexec` / `wp_ksh_start`: the
  Coq-level premises gain `Wb`; `Hbd` becomes
  ```
  (forall (N : uk_names Σ) (l : list fdstate) (n : nat),
     ukn_pay N = Q ->
     ⊢ upos γp n -∗ Ql (-1) -∗ UkSh.ush_wcp Wc Wb l n 0%nat -∗
       UkSh.ush_posb N γp T Wc Wb Pm l 0%nat)
  ```
  with a NEW parameter `Ql : Z -> iProp Σ` (the lend; top: `ucons_pay cn
  γp T Rdl`) beside `Q` (the exit payload; top: `ucons_pay cn γp T (init_rd
  Rdl Wb)`); the spatial premises `sh_prompt_at (take NSTD …) -∗` and
  `Q (-1) -∗` become `Ql (-1) -∗ UkSh.ush_wcp Wc Wb (take NSTD (uvis_fd W)) n 0%nat -∗`
  (after `upos γp n -∗`).  DELETE `sh_prompt_at`, `sh_prompt_at_triv`,
  `sh_prompt_pay`, `sh_prompt_in_of_at`; `UShOut.sh_prompt_pay_of_ushpr`
  and `ksh_w_of_link_prompt`'s prompt-pay consumers go with them
  (`ksh_w_of_link_cred` / `sh_prompt_law_holds` STAY).
  `ush_rest_l N γp T Wc Wb …`.

## UInitSh / UInitBoot (lane S: MINIMAL, lane I: the real glue)

Lane S makes the two files compile against the OLD init side (`UkInit.
init_exec_sup_pos` keeps its `(Rt ∨ True)` premise, `ufd_head`, and hands
the lease `ucons_pay cn γ T Rd (-1)` at the EXIT family `Rd`):
* `UserConsole` gains `ucons_pay_mono : □ (∀ n, Rd n -∗ Rd' n) -∗
  ucons_pay cn γ T Rd xs -∗ ucons_pay cn γ T Rd' xs` (lane S adds it; lane
  I adds `uinit_lend_c` -- a different lemma, no collision).
* `init_exec_sup_of_sh_slot` / `init_cons_sup_of_sh_slot` gain the binders
  `Wb` and `Rdl : nat -> iProp Σ` (the lend family) and the Coq-level
  premise `(forall n : nat, ⊢ Rd n -∗ Rdl n)`; sh's slot is built at `Ql :=
  ucons_pay cn γp T Rdl` (the lease converted by `ucons_pay_mono`) and the
  entry credential is `ush_wcp`'s True arm (`ush_wcp_triv`) where
  `sh_prompt_at` used to be built.  The `(Rt ∨ True)` premise is simply
  dropped on the floor there (it is init's old prompt credential and
  nothing reads it any more); `Rt` stays a binder of the two lemmas ONLY
  because `UkInit.init_exec_sup_pos` still takes it -- lane I deletes it.
* `sh_pay`, `sh_pay_rest` (`∀ γp N T Wc Wb`) gain the `Wb` binder.
* At the top (`UInitBoot.echo_Hinit_boot`): `Wb := fun _ => True%I`, `Rdl
  := UShLine.ush_rd_pin γ`, `Rd := UShLine.ush_rd_x γ (fun _ => True%I)`
  (so `init_boot_pay`'s `Rd 0` conjunct is `ush_rd_pin γ 0 ∗ (True ∨ True)`),
  `Ql := ucons_pay fsc_cons γp (echo_taint γ) (ush_rd_pin γ)`; the new
  Coq-level premises (`ush_at_of_pm_wb`, the entry law) discharged from
  `UShLine`'s new lemmas.  Nothing else in the two files changes; lane I
  replaces the placeholder instantiations.

## The init side (lane I -- the coordinator; NOT lane S's files)

`UInitFd`: `ufd_row T st l := ⌜l = ufd_l3 st⌝ ∨ ⌜l = ufd_l0⌝ ∨ T`
(persistent), `ufd_head_open_row : ufd_head -∗ ∃ l, ustd γfd l ∗ ufd_row
T st l ∗ □ (∀ γ, ustd γ l -∗ ufd_head T st γ)`.
`UkInit`: `init_rd`, `init_rd_cred`; `init_lend_cred stc Wc Wb l n :=
(⌜l = ufd_l3 stc⌝ ∗ Wc n 0) ∨ (⌜l = ufd_l0⌝ ∗ Wb n) ∨ True`;
`init_exec_sup_pos cn T st Wc Wb Rdl γ n := ∀ N' m pc l, ⌜ukn_pay N' =
ucons_pay cn γ T (init_rd Rdl Wb)⌝ -∗ … -∗ ustd (ukn_fd N') l -∗ ufd_row T
st l -∗ init_lend_cred st Wc Wb l n -∗ upos γ n -∗ ucons_pay cn γ T Rdl (-1)
-∗ udepw_at_ref …`.  `UserConsole.uinit_lend_c`.  `UkInitMain`:
`kinit_ban_law stc Wc Wb := □ ∀ n, Wb n -∗ kinit_banner0 stc (Wc n 0)`,
`kinit_round0` dies, `wp_kinit_banner` opens the token, `wp_kinit_fork`
lends `Rc := upos γ np ∗ ucons_pay cn γ T Rdl (-1) ∗ init_lend_cred stc Wc
Wb l np`.  `UInitKernel.init_boot_pay T Cns cn stc Wc Wb Rdl :=
init_cons_dance_all ∗ ucons_reader cn 0 ∗ Rdl 0 ∗ Wb 0 ∗ □ (∀ n N', Wb n
-∗ kinit_banner0 N' stc (Wc n 0))` (TRUSTED: reported OLD/NEW).
`UInitBanner`: `kinit_ban_any`, `sh_prompt_pay_of_kinit_own` die.
