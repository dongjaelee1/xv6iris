# Review: brief-io-leaf.md (D1-D7) against origin/main c33d42af6

Tree read: `/shared/xv6iris-2-disc` at `c33d42af6` (ECHO-OUT part 5 landed). Line numbers below are that tree's, not the survey's (36d6c6d62).

## 1. D1 -- one persistent link law `echo_links`

**Sound and the simplest, with three mechanical caveats.**

(a) *Where it can be stated.* `echo_write_link`/`_blk`/`echo_read_link` live in `Section echo_links` (EchoOut.v:2461), whose context is `HRg : riscvGS Σ` (:2462) **and** the four equations `Hout/Hin/Htag/Hwin` (:2466-2469). `out_link`/`read_link` need only `HRg`; the equations are used only in the proofs (`rewrite !out_res_at0`). So `echo_links` must be defined in a *sibling* section with `HRg` and no equations, and `echo_links_holds` proved inside `Section echo_links`. `read_ret` (:2542-2555) is currently *inside* the equation section although it uses nothing from it; it moves out with the definition.

(b) *Persistence.* Each conjunct is a closed `⊢` under the equations, so `⊢ □ (...)` follows by `iModIntro` with an empty spatial context; `□ ∗ □ ∗ □` is `Persistent`. No obstacle.

(c) *Parameters the U tier inherits.* `Section echo_out` binds `T`, `γ : echo_gn`, `Persistent T`, `Timeless T` (:959-960). Hence `echo_links` is `echo_links T γ`, and every U-tier section that takes it gains `` `{!echoOutG Σ} ``, a `γe : echo_gn` variable and **`Timeless T`** -- UkSh.v:375-376 has `Persistent T` only. All instances are the taint (`mono_nat_lb_own`), so this costs nothing but a binder. `uprogSG_free`/`PS`/`uk_names`/`N` are not in the way: `echo_links` mentions none of them. The one place they bite: `sh_deps` today is `udepw_law 16` (UkSh.v:435) and is *applied* as `UkSh.sh_deps (PS := uprogSG_free)` (UInitBootAdequacy.v:~140, UInitSh.v:923); after redefinition it no longer depends on `PS`, so those two named-argument applications must change. Redefining (`sh_deps := echo_links γe`) keeps all 49 `sh_deps -∗` premise sites textually and gives the smallest lemma_diff; I would still rename (`sh_links`) -- the name is a lie otherwise -- but that is the coordinator's call.

(d) *The top.* `echo_Hinit_boot` already `intros ... Hout Hin Hwin` (UInitBoot.v:586) and already fills `Tn` with `echo_turn γ (S gen_id)` (:726-742), which is definitionally `EchoOut.eturn γ (S gen_id)` (AppEcho.v:1421-1422). So `echo_links_holds` can be instantiated exactly where `Hsh_deps` is used today (:650, :697), and `Tn` is *already concrete at the top*; only `UkInitMain.wp_kinit_start` (:2379 `(Tn : iProp Σ)`, `iClear "Htn"` :2426) and `UInitKernel.init_boot_pay` (:578-580) take it opaquely. UkInitMain must gain `γe` and `GEN` (UkSh already has `GEN`, :349).

The statement I would write (EchoOut.v, after `Section echo_out`'s ghosts, before `Section echo_links`):

```coq
Section echo_links_def.
  Context `{HRg : !riscvGS Σ}.
  Definition echo_links : iProp Σ :=
    (□ (∀ (k : nat) (v : era_pins) (P n0 : nat) (b : bv 8) (cs0 : list nat) (Φ : iProp Σ),
          ⌜((n0 `div` length echo_line) <= length cs0)%nat⌝ -∗
          ⌜proc_upto cs0 (S n0) !! P = Some b⌝ -∗
          era_pin k v -∗ turn v P -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
          (((turn v (S P) ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T) -∗ Φ) -∗
          out_link Uart0 k b Φ)
     ∗ □ (∀ (k : nat) (v : era_pins) (P n0 a : nat) (b : bv 8) (cs0 : list nat) (Φ : iProp Σ),
          ⌜(0 < n0)%nat⌝ -∗ ⌜(n0 `mod` length echo_line)%nat = 0%nat⌝ -∗
          ⌜((n0 `div` length echo_line) <= S (length cs0))%nat⌝ -∗
          ⌜P = length (proc_upto cs0 n0)⌝ -∗ ⌜(a < length line_alts)%nat⌝ -∗
          ⌜line_alts !!! a !! 0%nat = Some b⌝ -∗
          era_pin k v -∗ turn v P -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
          (((turn v (S P) ∗ cs_lb v (cs0 ++ [a]) ∗ E_lb v n0) ∨ T) -∗ Φ) -∗
          out_link Uart0 k b Φ)
     ∗ □ (∀ (k : nat) (v : era_pins) (n : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
          era_pin k v -∗ dl_cnt v (1/2) n -∗ (read_ret k v n ws -∗ Φ) -∗ read_link k ws Φ))%I.
End echo_links_def.
(* inside Section echo_links: *)
Lemma echo_links_holds : ⊢ echo_links.
```
After PROLOGUE-ALTS item 3 lands, a fourth `□` conjunct for `echo_write_link_pro` and (see §4) a taint route `□ (∀ k b Φ, T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ)` go in the same bundle -- the `∨ T` loop invariants need the latter and I did not find it in the tree.

## 2. D2/D3 -- the child's death, the payload shapes, the stage indices

**D2 is sound in principle but the brief omits the ENGINE change that makes it so.** Verified chain:

- `uk_step_obl` hands the residue back as `uk_paycont Q gn (Kc ∧ ukc ...)` = `my_pay gn Q ∗ (Kc ∧ ukc)` (UkStep.v:514-517, the `R -∗ ...` conjunct). `Kc` is the *program's* continuation, chosen by whoever applies `wp_uk_step` (:1085, `▷ (my_pay gn Q ∗ Kc)`).
- `wp_uk_store_denied` applies it at **`Kc := True`** (UkStore.v:1738 `wp_uk_step ... True%I Qp`) and takes `(⊢ (Qp (-1) : iProp Σ))` (:1723) precisely because `Kc` was thrown away. The fault leg it builds is `... ∧ uk_paycont Qp gn (uslot W)` (:1774) and the deposit comes from the Coq-level `Hkcf : u_fault_flavor ... -> ⊢ my_pay gn Qp -∗ (□ riscv_kill_cred ∨ kill_owed gn)` (:1757-1761), which `uk_store_obl_base`/`_rvc` take as premises (:1136-1138, :1299) and spend at the producer (:1074-1083, `iSplitR` today because the arm is `∗`, UexecRet.v:1510).
- **The fix**: choose `Kc := Qp (-1)`. Then the fault leg is `my_pay ∗ (Qp (-1) ∧ uslot W)`; after T3's `ukill_cred_at ∧ uexec_kill_arm_F` the producer does `iSplit`, left `kill_owed_of` from the `∧`'s left, right the slot from its right -- one copy, exactly as the brief hopes. But that requires restating `uk_store_obl_base`/`_rvc`'s `Hkcf` premise and fault-leg shape (UkStore.v:1136-1148, :1299-1309), `uk_store_fault_post_fetch`'s premise (:797-799), `wp_uk_store_denied` (:1723, :1738) and `UkRunMem.wp_uk_sb_denied` (:415 `(⊢ ukn_pay N (-1)) ->`) -- four engine statements in TRAP-ROWS' cone, landable only *after* T3 (the handover marks T3 "NOT WRITTEN"; the app-echo note says its statement is accepted and it is TRAP-ROWS M2). D2 names only `wp_ksh_memset_null` and the sh sites. The "STOP if T3 does not let the left side be paid from a linear resource" clause is the right clause, but as landed today T3 alone does not: the leaf's `Kc := True` does.

**Stage indices -- D3's "turn at the alternative's end" is off by two everywhere and wrong for alternative 2.** `line_alts` entries end in `"$ "` (EchoDisc.v:250-254) and that prompt is written by *sh* after `wait` (user/sh.c: `wait(0)` then the loop's `getcmd` -> `write(2,"$ ",2)`; the site is UkSh.v:4376). So, with `P_blk := length (proc_upto cs0 n0)` and `n0 = 17 * S (length cs0)`:

- echo's exit (alt 0): `turn v (P_blk + 12) ∗ cs_lb v (cs0 ++ [0]) ∗ E_lb v n0` -- echo wrote the block-first `'h'` (`_blk`, `a = 0`) and 11 more; the `"$ "` is not echo's.
- the exec-failed child (alt 1): `turn v (P_blk + 17) ∗ cs_lb v (cs0 ++ [1]) ∗ E_lb v n0`.
- the null-store death (alt 2): the child wrote **nothing**; nobody has recorded a choice; the block-first `'$'` is sh's, via `_blk` at `a = 2` *after* the wait. Payload arm: `turn v P_blk ∗ cs_lb v cs0 ∗ E_lb v n0`.

Hence sh's child payload is not one shape but

```coq
Q_child v P_blk cs0 n0 := fun _ =>
   (∃ a, ⌜(a < 2)%nat⌝ ∗ turn v (P_blk + length (line_alts !!! a) - 2) ∗ cs_lb v (cs0 ++ [a]) ∗ E_lb v n0)
 ∨ (turn v P_blk ∗ cs_lb v cs0 ∗ E_lb v n0)
 ∨ T
```
(status-independent, Timeless, `iRight`-able from the taint -- D3's properties hold). sh learns the arm by destructing after `gen_pay_timeless` (`wait((int*)0)` tells it nothing), and its prompt site must then pay `'$'` by **(W)** in arm 1 and by **(W')** at `a = 2` in arm 2 -- plus `echo_write_link_pro` at `a = 0` for the *first* prompt of a session. Three link shapes at one write site (UkSh.v:4376); survey site 5 undercounts this.

**sh's own payload / init's `Q`.** init's fork `Q` (UkInitMain.v:863-865 `(ucons_pay cn γ T)`) is paid by two different programs: sh (after exec) and init's own exec-failed child (`die_de`, :279-283). Their turn stages differ -- `39(k+1)` with `ps = replicate (k+1) 1` for the child, the start of a fresh round after `"fork\n"` (`cs0 ++ [3]`, PROLOGUE-ALTS 1b) for sh -- so `Q_init_child` must be `fun _ => ucons_pay cn γ T (-1) ∗ ((∃ s, ⌜round_start s⌝ ∗ turn v (P s) ∗ ps_lb v ... ∗ cs_lb v ... ∗ E_lb v ...) ∨ T)`, an existential over the stage. Timeless (∃/∗/∨ of Timeless), so `gen_pay_timeless` (ChildTok.v:730) still applies and `uinit_redeem` (UserConsole.v:375) takes the first conjunct: **init's redemption goes through.** The fork wand `□ (riscv_kill_cred -∗ Q (-1))` is `ucons_pay_taint` + `iRight` as today (:877-882).

One consequence the brief does not draw: `Q (-1)` can no longer double as sh's *entry* lend. `UShKernel.sh_slot_of_kexec` takes `my_pay (uvis_gen W') Q -∗ upos γp n -∗ Q (-1) -∗ uslot W'` (UShKernel.v:645-650) and mints `ush_at` from `Q (-1)` *as the lease*; at sh's entry the turn is at `P = 18`, not at a round start, so `Q (-1)` is false there. The constructor (and `sh_uexec_slot` :474, `UInitSh.init_sh_slot` :905-935, `UkInit.init_exec_sup`) must take the raw lend `upos ∗ ucons_pay (-1) ∗ turn v 18 ∗ ps_lb ∗ cs_lb v [] ∗ E_lb v 0 ∗ dl_cnt v (1/2) 0` as `Pay`. That is W6, and it lands in M3/M6, not "not in the brief".

## 3. D4/D7 -- init's rounds, concretely

Round `k` head: init holds `uinit_tok` and `B_k := era_pin (S gen_id) v ∗ turn v (39k) ∗ ps_lb v (replicate k 1) ∗ cs_lb v [] ∗ E_lb v 0 ∗ dl_cnt v (1/2) 0` (round 0 = `eturn`, EchoOut.v:1280-1283, plus `ps_lb v []` once item 3 lands).

1. Banner bytes `j < 18` by (W) at `P = 39k + j`, premise `proc_upto ps0 [] 1 !! (39k + j) = Some (u_banner !! j)` -- `pro_of_replicate_banner` (phase-1 stmts :71-73) is exactly this, once `proc_upto` takes `ps`. Each byte returns `turn v (S P) ∗ ... ∨ T`.
2. `uinit_lend` (:1126); fork with `Rc := upos γ np ∗ ucons_pay cn γ T (-1) ∗ B_k@(39k+18)` (binder :806; `dl_cnt` must ride too -- sh reads; `era_pin` is persistent).
3. `-1` arm (T5): `Rc` returns; init writes `"init: fork failed\n"`: byte 0 by `_pro` at `a = 2` (`P = 39k+18`), 17 more by (W); `exit(1)`; the turn is dropped (terminal).
4. pid arm, child: exec sh with `Pay := Rc`'s contents. Failure: refund (PieceFam.v:99-101 `pf_at := AU ∧ refund`; PinnedExec.v:160-162) hands the bundle back; today UkInitMain.v:545-570 says the lease is "SPENT here ... On the FAILING arm the child still holds them", so the plumbing exists. `die_de` (:279) writes `'i'` by `_pro` at `a = 1`, 20 more by (W) -> `turn v (39(k+1)) ∗ ps_lb v (replicate (k+1) 1)`; `exit(1)` pays `Q_init_child 1` with the lease it still holds and the round-start arm.
5. init's wait (`wp_uk_ecall_wait_null` :2076 via `wp_kinit_wait` :1623): `gen_uniq_tok` + `gen_pay_timeless` (:1440-1449 as today) -> `ucons_pay ∗ (round-start ∨ T)`; `uinit_redeem` -> `uinit_tok`; round `k+1` with `B_{k+1}`.

Two gaps in the pure layer, both PROLOGUE-ALTS', both needed before M6: (i) the loop invariant's stage is an *existential* `s` with `round_start s`, and the banner at round `k+1` after **sh's** `"fork\n"` exit is at a stage `pro_of_replicate_banner` does not cover; a lemma `round_start s -> proc_upto (ps s) (cs s) (S (n s)) !! (P s + j) = Some (u_banner !! j)` is nowhere in the phase-1/1b statements. (ii) `echo_write_link_pro`'s premise `¬ pro_done (pro_from r ps)`: with 1b's `pro_from_done : pro_done (pro_from r ps) <-> r < pro_rounds ps`, the writer's `ps_lb v ps0` alone cannot decide it for the *true* `ps` (a lower bound admits more rounds); it is decidable from the **turn** -- `turn_agree` pins `P` to the auth stage's `pcount`, which excludes any byte past the writer's -- so the premise must be stated on the writer's `ps0` and the reconciliation done inside `eout_step_write_pro`, the way `_blk` states `P = length (proc_upto cs0 n0)` on the writer's `cs0`. That is item 3's design, and the brief's phrasing (`ps_lb` "is enough") assumes it.

## 4. D5/D6 -- the read leaf, `ush_at`, M1 and the printf tower

**M1 as "init's banner alone" is separable only for round 0.** The banner is inside `for(;;)` (`wp_kinit_main` :2026 is the loop); round `k>0` needs the turn back through the child's payload, i.e. init's new `Q`, which sh must pay -- and sh's payload is M3-M5. So M1 must be either (a) round 0 on the link with the turn *dropped* after the banner (affine; `Rc`/`Q` unchanged; zero sh impact; the whole design risk -- tower, `Tn` concrete, (W) at `P = 0..17` -- in one build), leaving rounds `k>0` on `udepw_law 16` until M6; or (b) the loop invariant carrying `B_k ∨ ⌜k > 0⌝`. I recommend (a) and moving "init's loop" to M6 beside `echo_Hinit_boot`. Note `init_deps` (UkInit.v:571-572) and the three die arms (`udepw_law 16 -∗` :171/:283/:395) keep 16 from `init_deps_of_laws` (UInitBoot.v:324) through M5.

**The tower.** `wp_kinit_printf` already *is* the specialised no-`%` printf: premise `(forall j, j < len -> bv_unsigned (f j) <> 37)` (UkInitPrintf.v:103). There is no cheaper route than re-threading `wp_kinit_vprintf_step/_loop` (:879/:1207) and `wp_kinit_putc` (:111, post `ucallee_saved` only): the bytes are only known there. But keep EchoOut *out* of the tower by threading an abstract per-byte family. Statement:

```coq
Lemma wp_kinit_printf_chain (a : Z) (len : nat) (f : nat -> mword 8) (Ch : nat -> iProp Σ) ... :
  (* the five pure premises of wp_kinit_printf, unchanged *)
  □ (∀ i : nat, ⌜(i < len)%nat⌝ -∗ Ch i -∗ out_link Uart0 (S gen_id) (bv_of f i) (Ch (S i))) -∗
  init_code γt -∗ utext_str γt a len f -∗ Ch 0%nat -∗
  urun N h m (mword_of_int InitSyms.printf) (12 + (12 + (4 + n))) -∗
  (∀ h' m', ⌜ucallee_saved m m'⌝ -∗ Ch len -∗ urun N h' m' (ret_pc ...) ... -∗ WP Loop) -∗ WP Loop.
```
Each one-byte `write` goes through `wp_kinit_write_chain` (:1238, 0 callers) with `uwrite_chain_sup` (UkWriteLeaf.v:247-262) at `cons_out_chain (S gen_id) M ua (fun j => ...) 0 1`, whose node is `Q 0 ∧ (∀ b, ⌜M !! ua = Some b⌝ -∗ out_link Uart0 k b (Q 1))`; the loop invariant is "`i` bytes written, `Ch i` in hand"; the short arm (`write_cons_arms` middle arm via `uwrite_post_cons` :282) is refuted from `utext_str`'s mapped byte with T1's `write_cons_short`. The caller instantiates `Ch i := (turn v (P+i) ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T` and discharges the step from `echo_links` -- which is why the taint route of §1 is needed (the `T` arm of `Ch i` must also produce an `out_link`). Same shape for `UkShDiag.wp_kshd_vprintf_loop` (:2078, post `ucallee_saved`), where the expected bytes are the *expansion* of `"exec %s failed\n"` at a runtime `ush_str` (UkShRun.v:1169-1176); the pinning lemma is `expand fmt ["echo"] = take 17 (line_alts !!! 1)` by `vm_compute`, with `"echo"` pinned by UkShEcho.v:148-156's `ush_line_is f k len -> ...` (the three strings' bytes), and `ush_line_is f 0 len` is `wp_kshm_child_echo`'s premise (:787). So W7's lemma exists in parts; the diag tower must gain a byte-precise post to use it.

**The read leaf fits at `cap = 1`.** `wp_ksh_gets_loop` reads `wp_ksh_read ... 1%nat 1%nat np` (UkSh.v:2638) and today weakens the answer (`ush_read_ans_pos`, :2647). With `dl_cnt v (1/2) n` beside `upos γp n` in `ush_at`, `echo_read_link` gives `read_ret` (EchoOut.v:2542): `⌜length dl = n⌝`, `(dl ++ ws) prefix_of echoed pops`, `E_byte`, and `ein_read_byte` (:2396) yields `x.2 = echo_line !!! (n mod 17)`; with the invariant `n = 17q + i` this is `ush_line_is` (:213-215) byte by byte, the `'\n'` at `i = 16` ends `gets`, and the loop head has `n = 17(q+1)` -- R2's `∃ q, n = 17 q`. `dl_cnt`'s `n` and `upos`'s `n` agree by construction (both start at 0 and move only in reads; a mismatch is refuted inside `ein_step_read`). `read_ret`'s `cs_lb v cs0'` is the claim's, existential; sh keeps its own. The `-1` and closed arms must hand `ush_at n` back with `dl_cnt` inside (no link fired). All fine. The one real ripple: `ush_at n := upos γp n ∗ ukn_pay N (-1)` (:1140-1141) becomes `upos ∗ ucons_pay(-1) ∗ era_pin ∗ dl_cnt ½ n ∗ (turn v P ∗ cs_lb v cs0 ∗ E_lb v n)` with `P`/`cs0` pinned to the boundary, `ush_pos_pay` (:1146) goes, `sh_Rsh` (UInitSh.v:615-616) is untouched (it is heap+break), but `ush_loop_head`/`ush_rest` (:5459) and the third `Hsh_owed` conjunct's equation `ukn_pay N = ucons_pay ...` (UInitBootAdequacy.v; UInitSh.v:913-915) change with it.

## 5. Warts left open, and new gaps

- **W1 (engine, §2):** four statements in UkStore.v/UkRunMem.v, after T3. Not in D2.
- **Stage indices (§2):** the "alternative's end" is `- 2` everywhere; alt 2 has no recorded choice; sh's `Q` is a three-arm `∃ a`; sh's prompt site has three link shapes.
- **`Q (-1)` vs the entry lend (§2):** `UShKernel.v:645-650`, `:474`, `UInitSh.v:905-935` take the raw bundle as `Pay`.
- **`ukn_triv -> ukn_const` true size:** 23 textual mentions (UkShRun 8, UkShEcho 4, UkShDiag 3, UkEcho 3, UkShMain 2, UkSh 1, UShEcho 1, UEchoKernel 1), but the cost is the *linear* payload threaded through the child's walk: the 14 signatures SELF-KILL step 5 threaded the arm through (UkShParseExec.v:1523/1070, UkShParseCmd.v:141/634/2486/3382, UkShMain.v:505/669, UkShFork.v:238/494/562/923, UkShEcho.v:781/811), the three `Hypothesis ushp_pay_free : (⊢ ukn_pay N (-1))` (UkShParseLex.v:173, ParseExec.v:121, ParseCmd.v:123 -- a section hypothesis cannot become a resource; each becomes a premise on the lemmas that reach exit/memset/exec), the three UkShRun sites (:2504/:2542/:2844, all the child's exit) and UkShDiag.v:7669. One copy suffices: the branches exec (as `Pay`), memset-null (as `Kc`), exit(1)-after-diag are disjoint control paths.
- **`uch_any` -> named set:** confinable to the `fork1 -> wait` window (`if(fork1()==0) runcmd(...); wait(0);`): `ush_pstate` (UkSh.v:5306) keeps `uch_any`, opened at fork, closed by `uch_any_of` after wait. The four `wp_kshr_fork*` wrappers (UkShRun.v:960/1079/1469/1760) and `wp_kshf_fork*` (UkShFork.v:237/490) change; the `_any` variants (`Rc := emp`, `Q := True`) become unusable and should be deleted rather than restated. sh has exactly one child, so `gen_uniq_tok` is init's argument verbatim (:1440-1444).
- **The exec image's `Pay`:** `sh_exec_sup_echo` (UkShEcho.v:447-460) is a `□ ∀ N'` at `⌜ukn_pay N' = fun _ => True⌝`, established once at sh's entry, but `Q_child v P_blk cs0 n0` differs per line. The supply must quantify the stage *inside* the `□` (`∀ v P cs0 n0, ⌜ukn_pay N' = Q_child v P cs0 n0⌝ -∗ ... -∗ udepw_at_ref ...`) and echo's constructor (UEchoKernel.v:446-448, today `my_pay (uvis_gen W) (fun _ => True)`) is stated per stage with `Pay := turn v P_blk ∗ cs_lb v cs0 ∗ E_lb v n0` and the pure `P_blk = length (proc_upto cs0 n0)`, `n0 = 17 * S (length cs0)`. `UkEcho.v:62`'s `Context {Hpay : !ukn_triv N}` becomes `Context (v P cs0 n0) {Hpay : ukn_pay N = Q_child ...}`; the exit (:955 `ukn_triv_eq`) pays arm `a = 0`. M2 can be decoupled from sh by taking `Q_child` abstractly with a wand `□ (bundle-at-end -∗ Qe 0)` -- but the stage must still be a parameter.
- **`read_ret` inside the equation section** (EchoOut.v:2542): moves for D1.
- **`Timeless T`** missing in the U-tier sections (UkSh.v:376 and siblings).
- **`line_alts` in the tree** (EchoDisc.v:250-254) still has alt 3 = `"fork\ninit: starting sh\n$ "`; sh's `"fork\n"` site and init's restart depend on 1b landing (launch condition, consistent).
- **W2/W8:** covered by T1/T5 as briefed; nothing further.

## 6. Questions for the owner

1. May IO-LEAF restate the four engine statements (`uk_store_obl_base/_rvc`, `wp_uk_store_denied` at `Kc := Qp (-1)`, `UkRunMem.wp_uk_sb_denied`) itself after T3, or does that row belong to TRAP-ROWS T3's cone?
2. Is init's child payload as an existential over "round-start stages" (one `Q` paid both by the exec-failed init-child and by sh's `"fork\n"` exit) acceptable, or must init distinguish the two arms?
3. May M1 be round 0 only (the turn dropped after the banner; rounds `k>0` on `udepw_law 16` until M6), given that any other M1 pulls sh's payload rework forward?
