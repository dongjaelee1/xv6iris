# IO-LEAF — THE SURVEY (read-only, 2026-09-16; tree at origin/main `36d6c6d62`)

Assumed lane outcomes (in flight, taken as given): PROLOGUE-ALTS makes init's
exec-failure loop and its terminal fork failure prologue alternatives; TRAP-ROWS
gives the short console write the reason `~ uva_rmapped P (ua + k)` (T1) and
strips the kill case from the user-level read's and wait's `-1` arms (T2/T4).

## 0. THE THREE LINK STATEMENTS EVERY SITE MUST MEET (verbatim)

`EchoOut.v:2474-2480` — **(W)**
```
    Lemma echo_write_link (k : nat) (v : era_pins) (P n0 : nat) (b : bv 8)
        (cs0 : list nat) (Φ : iProp Σ) :
      ((n0 `div` length echo_line) <= length cs0)%nat ->
      proc_upto cs0 (S n0) !! P = Some b ->
      era_pin k v -∗ turn v P -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
      (((turn v (S P) ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T) -∗ Φ) -∗
      out_link Uart0 k b Φ.
```
`EchoOut.v:2494-2504` — **(W′)** adds `0 < n0`, `n0 mod length echo_line = 0`,
`(n0 div length echo_line) <= S (length cs0)`, `P = length (proc_upto cs0 n0)`,
`a < length line_alts`, `line_alts !!! a !! 0 = Some b`, and returns
`cs_lb v (cs0 ++ [a])`.
`EchoOut.v:2539-2541` — **(R)**
```
    Lemma echo_read_link (k : nat) (v : era_pins) (n : nat)
        (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
      era_pin k v -∗ dl_cnt v (1/2) n -∗ (read_ret k v n ws -∗ Φ) -∗
      read_link k ws Φ.
```
`eturn k := ∃ v, era_pin k v ∗ turn v 0 ∗ dl_cnt v (1/2) 0 ∗ cs_lb v [] ∗ E_lb v 0`
(`EchoOut.v:1262-1266`); all five conjuncts Timeless (`:1286`).

What a program actually hands over is
`SpecConsolewrite.cons_out_chain k M ua Q j cnt` (`SpecConsolewrite.v:158-167`),
node = `Q j ∧ (∀ b, ⌜M !! uint (ua + j) = Some b⌝ -∗ out_link Uart0 k b (…S j…))`,
supplied by `UkWriteLeaf.uwrite_chain_sup` (`UkWriteLeaf.v:247-262`) into
`udepwf_std … 16 (xfam_wr Q (ukn_pay N)) l`, read back as
`SpecFilewrite.write_cons_arms Q n r` (`SpecFilewrite.v:677-682`), middle arm
`∃ k, ⌜r = k⌝ ∗ ⌜k < n⌝ ∗ Q k` (WART W2). Read side: `xfam.rf_in`
(`UexecExecInst.v:312`), row 5 (`:512,525-526`), post (`:688-694`); the fupd is
`WpUart.cons_read_pay k Rin := ∀ ws, read_link k ws (R ws)` (`WpUart.v:2491-2493`).

## 1. THE RESOURCES AT EACH SITE

| # | site (file:line) | holds today | link needs (from §0) | GAP |
|---|---|---|---|---|
|1|init banner, `wp_kinit_write` `UkInit.v:1154` (18 one-byte calls from `UkInitPutc.v:317`; literal `0x978 "init: starting sh\n"`, `UkInitMain.v:156/1075`)|`udepw_law 16` only; post discarded|(W) at `P=0..17`, `n0=0`, `cs0=[]`; `proc_upto [] 1 !! P = Some b`|swap to `wp_kinit_write_chain` (`UkInit.v:1238`, **0 callers**) and thread `turn v P` through `wp_kinit_putc` (`UkInitPutc.v:111`; post is `ucallee_saved` only — says nothing about the byte), `wp_kinit_vprintf_step/_loop/_` (`UkInitVprintf.v:879/1207/1326`), `wp_kinit_printf` (`UkInitPrintf.v:100`). Turn from `eturn` via `Tn` (§2).|
|2|init's three die arms `UkInitMain.v:167/279/391` (18/21/29 bytes, same putc tower)|`udepw_law 16 -∗` raw, `ukn_pay N' (-1)`|(W)/(W′) at the prologue alternative's index|PROLOGUE-ALTS must give `pro_alts`; the arm needs `turn` — arms 1 and 3 reach the die head with the turn already **lent away** (§2).|
|3|init fork→sh `UkInitMain.v:863-873` → `UkFork.v:784`|`Rc := (upos γ np ∗ ucons_pay cn γ T (-1))`, `Q := ucons_pay cn γ T`, wand `□ (riscv_kill_cred -∗ Q (-1))` paid at `:877-882`|`Rc` grows by the turn bundle at `P = 18`|add a conjunct to `Rc` and to `Q`; both binders exist (`UkFork.v:794,805`).|
|4|init wait `UkInit.v:1623`, reap `UkInitMain.v:1440-1444`|`gen_uniq_tok` → `gen_pay_timeless` → `uinit_redeem`|`Q xs` must be Timeless|exists; the turn is Timeless, so `gen_pay_timeless` (`ChildTok.v:730`) still applies.|
|5|sh prompt `"$ "` `UkSh.v:4376` (2 bytes, fd 2) via `wp_ksh_write` `UkSh.v:906`|`sh_deps`; post discarded|(W′) at the block's first byte with sh's own alternative index `a`, then (W)|swap to `wp_ksh_write_chain` (`UkSh.v:957`, **0 callers**); sh must carry `turn`+`cs_lb`+`E_lb`+the index `a`, i.e. know which of `line_alts` it is producing.|
|6|sh/child diagnostics `UkShDiag.v:704` (1 byte per char; 19 `sh_deps` premises above it)|`sh_deps`|(W) per byte|the bytes come from a `%s` argument (`ush_diag_res`, `UkShRun.v:1168-1176`), not a literal — see WART W7.|
|7|sh read `UkSh.v:1371` → `UShLine.ush_read_sup` `UShLine.v:288`|`in_licence`, `upos γp n`, `ucons_pay … (-1)`; `rf_in := fun _ => True` (`UShLine.v:175`), paid by `cons_read_pay_triv` at `UShLine.v:332`, answer dropped at `:559`|(R): `era_pin k v ∗ dl_cnt v (1/2) n`|replace `rf_in` by `read_ret`'s Φ; `dl_cnt` half must live beside `upos γp n` in `ush_at` (`UkSh.v:1140`). §4.|
|8|sh fork→child `UkShFork.v:308` → `UkFork.v:1132-1133`|`Rc := emp`, `Q := fun _ => True`; child arm gives `⌜ukn_pay N' = fun _ => True⌝` (`UkFork.v:1114`), re-presented as `⌜ukn_triv N'⌝` (`UkShRun.v:993/1512`, `UkShDiag.v:7730`)|`Rc` = the turn bundle, `Q (-1)`/`Q 0` = turn ∨ taint|**both binders are hard-wired to the trivial values** by `wp_uk_ecall_fork_any`; the whole `wp_kshr_fork`/`_fork1`/`_fork1_final`/`wp_kshf_fork*` chain must move to `wp_uk_ecall_fork` and every `ukn_triv` premise below become `ukn_const`+the payload equation.|
|9|sh wait `UkShRun.v:817` → `wp_uk_ecall_wait_any` `UkRunSys.v:2200`|the answer is **discarded**: `iIntros (h' r Sc') "_ Hrun Hch"` (`UkRunSys.v:2220`); the `child_tok` is discarded too (`UkFork.v:1141-1145`)|`child_tok γ pidv Q` + `wait_ans`'s `exit_tok γ' rv xs` → `gen_pay_timeless`|move sh to `wp_uk_ecall_wait_null` (`UkRunSys.v:2076`) at a named `uch (ukn_ch N) Sc`; today sh holds `uch_any` throughout.|
|10|child exec of echo `UkShEcho.v:730` → `PinnedExec.pex_slot_at` `PinnedExec.v:172-188`|`Pay` is a plain binder; the failed-exec refund is dropped (`UkShEcho.v:558-562`)|`Pay := turn bundle`; transported by `□ (∀ W', … -∗ my_pay (uvis_gen W') Q -∗ Pay -∗ X W')`|binder exists; the refund on exec failure must stop being dropped (it is the turn).|
|11|echo's writes `UkEcho.v:1384` (`argv[i]`, twice dynamically), `:1546` (`" "`), `:1744` (`"\n"`) via `wp_kecho_write` `UkEcho.v:968`|`udepw_law 16`; post discarded|(W) at `P = 18+2+j`|swap to `wp_kecho_write_chain` (`UkEcho.v:1065`, **0 callers**); thread through `wp_kecho_main_body/_sep/_loop/_main/_start` (`UkEcho.v:1205/1458/1635/1790/2353`).|
|12|echo exit `UkEcho.v:922`, sh's `exit(0)` `UkSh.v:865`, child's `exit(1)` `UkShRun.v:2497`|`ukn_pay N (-1)` free at `ukn_triv` (`UkRun.v:197`); `wp_uk_ecall_exit` `UkRunSys.v:4220` takes `ukn_pay N (uexitst m)`|the exit payload at the status the walk passes|`UkShRun.v:2504/2542/2844`, `UkShDiag.v:7669`, `UkShParse{Lex,Exec,Cmd}` `ushp_pay_free` all assume `⊢ ukn_pay N (-1)` — false once the payload is linear (WART W1).|
|13|child's null-store death `UkSh.wp_ksh_memset_null` `UkSh.v:1700` (SELF-KILL step 5)|premise `(⊢ ukn_pay N (-1))`|`ChildTok.kill_owed gn` = `∃ Q, my_pay gn Q ∗ Q (-1)`|same as 12: the leaf's price is a Coq-level `⊢`, free only at `ukn_triv`.|

## 2. THE TURN'S ROUTE

The route already exists in full — it is the one the **console lease** travels
(`UserConsole.uinit_tok → uinit_lend → Rc/Q → PinnedExec.Pay → UkSh.ush_at →
sh's exit → gen_pay → uinit_redeem`, `UserConsole.v:343/356/375`). The turn is a
second passenger on exactly that channel; every crossing below is that channel's.

1. **Mint → init.** `App.Hpow`'s power-on arm yields `app_turn A c (S (obs_boots h))`
   (`App.v:400`); `App.Hinit_boot` takes it (`App.v:582`); `UInitBoot.echo_Hinit_boot`
   relays `echo_turn γ (S gen_id)` (`UInitBoot.v:550`) into
   `UInitKernel.init_boot_pay`'s **third conjunct `Tn`** (`UInitKernel.v:578-580`,
   filled at `UInitBoot.v:710`), which reaches `UkInitMain.wp_kinit_start`'s
   premise `Tn -∗` (`UkInitMain.v:2417`) and is **`iClear`ed at `UkInitMain.v:2426`**.
   Binder exists. `Tn` is an opaque `iProp` — it must become concrete enough for
   the banner (WART W6).
2. **Init's first byte.** `eturn`'s five conjuncts *are* (W)'s argument list at
   `P = 0, n0 = 0, cs0 = []`; premises `0 div 17 ≤ 0` and
   `proc_upto [] 1 !! 0 = Some 'i'` are closed computations on `u_prologue`
   (`EchoDisc.v:232`). Each byte returns `turn v (S P) ∗ cs_lb v [] ∗ E_lb v 0`
   or the taint (`EchoOut.v:2479`). No adoption step and no first-write lemma:
   part 4 deleted `eout_step_write_first`.
3. **init → sh.** `Rc` at `UkInitMain.v:865` becomes
   `(upos γ np ∗ ucons_pay cn γ T (-1) ∗ <turn at P=18>)`, and `Q`
   (`ucons_pay cn γ T`, status-independent — `ucons_pay_const`, `UserConsole.v:282`)
   gains the turn disjunct. Binders exist (`UkFork.v:794,805`); the taint wand
   `□ (riscv_kill_cred -∗ Q (-1))` is still paid by `ucons_pay_taint` composed
   with `Hkt` (`UkInitMain.v:877-882`) since the turn arm is `∨ T`.
4. **sh → child.** `Rc := emp`, `Q := fun _ => True` are **hard-wired** at
   `UkFork.v:1132-1133`. Binder must be re-opened: sh moves off
   `wp_uk_ecall_fork_any` onto `wp_uk_ecall_fork`, and `⌜ukn_triv N'⌝`
   (`UkShRun.v:993/1102/1512/1803`, `UkShEcho.v`, `UkShMain.v:102`, `UkEcho.v:62`)
   becomes `⌜ukn_pay N' = Q⌝` with `ukn_const` (`ucons_pay_const`'s mould).
5. **child exec → echo.** `PinnedExec`'s linear `Pay` (`PinnedExec.v:172-188`,
   `:215-261`, `:296-329`, `:348-379`, `:405-426`, `:440-461`); the transport wand
   already carries it into the new image's slot constructor. Binder exists; the
   **failure refund** (`pf_at = AU pf_recv ∧ pf_refund`, `PieceFam.v:99-101`) is
   currently thrown away at `UkShEcho.v:558-562` and must be kept — that refund is
   the turn on the exec-failed alternative (`line_alts !!! 1`).
6. **echo's exit.** `wp_uk_ecall_exit` (`UkRunSys.v:4220`) takes `ukn_pay N (uexitst m)`
   at `uexitst m = 0`. Shape: `Q := fun _ => (<turn bundle at P = 18+2+4·…> ∨ T)`,
   status-independent (`ukn_const`), so the same resource answers `Q 0` and `Q (-1)`.
   Stage index: the cursor after echo's four bytes-runs, i.e. at the end of
   `line_alts !!! 0`. The taint arm is what the fork wand
   `□ (riscv_kill_cred -∗ Q (-1))` injects into.
7. **child → sh.** `exit_tok γ' rv xs` rides `wait_ans` (`UserChildren.v:171-175`),
   redeemed by `child_tok γ pid Q -∗ exit_tok γ pid xs -∗ ◇ Q xs`
   (`ChildTok.gen_pay_timeless`, `ChildTok.v:730`). Today both halves are dropped
   (`UkFork.v:1141-1145`, `UkRunSys.v:2220`); sh must keep the `child_tok` and use
   `wp_uk_ecall_wait_null` at a named set. `gen_uniq_tok` (`ChildTok.v:679`)
   identifies the generation, `exit_tok_tok_ne` (`:694`) handles the orphan.
8. **sh → init.** sh's own exit payload is already `ucons_pay cn γ T`, redeemed at
   `UkInitMain.v:1440-1444` and turned back into `uinit_tok`. Adding the turn
   conjunct changes no step there.
9. **Where the turn goes when the child dies at the null store**
   (`UkSh.wp_ksh_memset_null`, `UkSh.v:1700`; alternative `line_alts !!! 2 = "$ "`):
   into `ChildTok.kill_owed gn` (`ChildTok.v:536`) — the right arm of
   `UexecRet.ukill_cred_at gn sc` — which `kexit` parks as `exit_tok` and sh's wait
   redeems. The payment fits; the **resume** does not (WART W1).
10. **When exec fails** (`line_alts !!! 1`): the turn comes back as `PinnedExec`'s
    refund; the child then prints "exec %s failed\n" (site 6) and `exit(1)`, so the
    turn must be inside the child's `Q` at that alternative's end.

## 3. `sh_deps` DELETION

`sh_deps := udepw_law 16` (`UkSh.v:435`). **49 premise sites**, all
`sh_deps -∗` / `UkSh.sh_deps -∗`, spent in exactly **two** places:
`wp_ksh_write` (`UkSh.v:907`, spent at `:942`) and, through it, `wp_kshd_putc`
(`UkShDiag.v:499`, spent at `:704`). Everything else is pass-through.

| file | premise lines | replacement |
|---|---|---|
|`UkSh.v`|907, 1378, 2383, 3102, 4101, 5919, 6301, 6514, 6788, 7056|the write bundle at the site's own cursor; `wp_ksh_write` deleted or left unused (`wp_ksh_write_chain` `:957` takes `udepwf_std`, not `sh_deps`)|
|`UkShDiag.v`|499, 1758, 2094, 2956, 3087, 3341, 3581, 4013, 4376, 4869, 5461, 6820, 6866, 7146, 7286, 7494, 7673, 7695, 7751 (19)|the chain threaded through the printf tower (W7)|
|`UkShRun.v` 1207 (`Hypothesis ush_diag_leaf`), 1235, 1473, 1764, 2846; `UkShFork.v` 254, 506, 572, 922; `UkShMain.v` 531, 685; `UkShCd.v` 412; `UkShEcho.v` 512, 792|(15)|pass-through of the bundle|
|`UShKernel.v`|474 (`sh_uexec_slot`), 626 (`sh_slot_of_kexec`); `UInitSh.v` 914|the entry constructor supplies the bundle instead|
|`UInitBoot.v`|368 (`init_cons_sup_of_sh_slot`), 514 (`echo_Hinit_boot`'s Coq premise, used at 610 and 657)|**deleted**: `echo_Hinit_boot` proves the write bundle from `eturn` + the links|
|`UInitBootAdequacy.v`|120|`Hsh_owed` becomes `(⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)` alone (no longer a conjunction)|

Init's own `udepw_law 16` is a **separate** obligation on the same lemma:
`UkInit.init_deps T := udepw_law 16 ∗ □ (T -∗ udepw_law 15) ∗ □ (T -∗ udepw_law 17)`
(`UkInit.v:571-572`), whose 16 is supplied by `init_deps_of_laws`
(`UInitBoot.v:309-313`) from the *same* `Hsh_deps` (`UInitBoot.v:610`). Plus the
three raw `udepw_law 16 -∗` in the die arms (`UkInitMain.v:171/283/395`) and the
putc/printf/vprintf tower (`UkInitPutc.v:112`, `UkInitPrintf.v:106`,
`UkInitVprintf.v:885/1218/1332`). Echo's are `UkEcho.v:969/1214/1465/1643/1794/2357`
and `UEchoKernel.v:446`, `UShEcho.v` (4 sites). **`Hsh_owed` loses `sh_deps` only
when all of these are off it.** 15 and 17 stay (bought from the supply,
`UexecExecMint.udepw_law_of_sup`, `UInitBoot.v:612/616`).

## 4. THE READ SIDE — WHAT IS OFFERED vs WHAT R2/R3 NEED

**Offered** (`read_ret k v n ws`, `EchoOut.v:2524-2537`), non-taint arm:
```
       dl_cnt v (1/2) (n + length ws)%nat
         ∗ ∃ (pops …) (dl …),
             ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
             ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
             ∗ ⌜E_index (seg_of (echoed pops))⌝ ∗ ⌜E_byte (seg_of (echoed pops))⌝
             ∗ (⌜ws = []⌝ ∨ ∃ cs0, cs_lb v cs0 ∗ E_lb v (n + length ws)%nat
                    ∗ ⌜((n + length ws) `div` length echo_line <= S (length cs0))%nat⌝)
```
plus `ein_read_byte` (`EchoOut.v:2378-2384`):
`E_byte … -> (dl ++ ws) prefix_of echoed pops -> length dl = n -> ws !! 0 = Some x
-> x.2 = echo_line !!! (n mod length echo_line)`.

**Required** by R2 (`UShLine.v:724-736`; `app-echo.md:3663-3665`, `:3001-3003`):
a conjunct of `ush_pos` reading `∃ q, n = 17 q`, from which `wp_ksh_getcmd` must
produce `UkSh.ush_rest_line f k` (`UkSh.v:5365`), i.e.
`ush_line_is f k len := len = length echo_line /\ ∀ j < len, f (k+j) = echo_line !!! j`
(`UkSh.v:213-215`).

**Verdict: it fits, per byte.** sh's gets reads at `cap = k = 1`
(`UkSh.v:2640`), so `ws` has length `dc = 1` and `ein_read_byte` applies at
`ws !! 0`. With the loop invariant `n = 17 q + i` the byte is
`echo_line !!! ((17q+i) mod 17) = echo_line !!! i` — exactly `ush_line_is`.
Three residual ties, all present:
(a) **`ws`'s byte ↔ the buffer byte** — `console_receipt`'s clean arm
(`SpecFileread.v:1129-1134`) gives `⌜length ws = dc⌝ ∗ ⌜∀ j < dc, ws !! j = sl' !! (cur+j)⌝ ∗ Rin ws`
and the unconditional per-byte ledger (`:1075-1087`)
`hs !! j = Some h /\ obs_ends_in Uart0 h b /\ M' !! (addr+j) = Some (cons_xlate b)`;
`obs_ends_in_inj` joins them.
(b) **`n` ↔ `cur`** — `read_ret` fixes `⌜length dl = n⌝`; `ush_rd_ret`
(`UShLine.v:184-195`) already returns `⌜cur = n⌝` against `upos γp n`, so the
`dl_cnt` half must sit in `ush_at` beside `upos` (`UkSh.v:1140`).
(c) **`d = 0`** is refuted by `ush_swallow_taint` (`UkSh.v:1250`).
What goes: `cons_read_pay_triv` (`WpUart.v:2498`) at `UShLine.v:332`, the drop at
`UShLine.v:559`, and `rf_in := fun _ => True` (`UShLine.v:175`). There is **no
`□ (T -∗ in_licence)` law in the tree** — the landed shape is a flat
`WpUart.in_licence -∗` (`UShLine.v:310`) plus `(⊢ in_licence)` (`UShLine.v:459`),
discharged at `UInitBoot.v:571/575/652-654`; both go with it.

## 5. THE ORDER OF EDITS

- **M1 (first green milestone) — init's banner alone.** `UkInitPutc`,
  `UkInitPrintf`, `UkInitVprintf`, `UkInit.wp_kinit_write_chain`,
  `UkInitMain.wp_kinit_start/_main` with `Tn` concrete; `init_deps_of_laws`
  keeps supplying 16 for the die arms. 6 files, one ~1300-line loop re-threaded
  (W7). `sh_deps` untouched, `Hsh_owed` unchanged. The whole design risk in one build.
- **M2 — echo.** `UkEcho` (5 lemmas), `UShEcho`, `UEchoKernel`; ~4 files,
  independent of sh.
- **M3 — the turn's transport.** `UkShRun`/`UkShDiag`/`UkShFork`/`UkShMain`/
  `UkShEcho` off `wp_uk_ecall_fork_any` + `uch_any` onto `wp_uk_ecall_fork` +
  `wp_uk_ecall_wait_null`; every `ukn_triv` site → `ukn_const` + the payload
  equation (~20 of the 74 mentions). ~12 files. **W1 and W6 bite here.**
- **M4 — sh's prompt and diagnostics.** `UkSh.v:4376`; `UkShDiag` (19 sites,
  ~3k lines). Deletes `sh_deps` from the nine sh-side files.
- **M5 — the read leaf.** `UShLine` (`rf_in`, `ush_read_sup`,
  `ush_read_recv_leaf_holds`), `UkSh.ush_at`/`ush_read_ans`, `UInitBoot`.
- **M6 — `echo_Hinit_boot` + `UInitBootAdequacy.Hsh_owed`.**

## 6. WARTS (gaps, no workarounds proposed)

- **W1 — the child's death is unpayable once its payload is linear.** SELF-KILL
  step 5's leaf `UkStore.wp_uk_store_denied` / `UkSh.wp_ksh_memset_null`
  (`UkSh.v:1702`) takes the Coq-level `(⊢ ukn_pay N (-1))`, free only at
  `ukn_triv` (`UkRun.v:197`); the same premise sits at `UkShRun.v:2504/2542/2844`,
  `UkShDiag.v:7669`, and `ushp_pay_free` in `UkShParseLex.v:173`,
  `UkShParseExec.v:121`, `UkShParseCmd.v:123`. Counter-scenario: the child holds
  `turn v P` (linear), stores through NULL, and must give the deposit
  `kill_owed gn` **and** the resume slot `X W` — which `UkStep.uk_step_obl` takes
  additively (`Kc ∧ ukc`), and the Löb resume was proved holding the turn. Step 5's
  own note names this ("a deliberate fault at a LINEAR payload … would have to move
  that first"). No resource the child can hold discharges both sides at a linear payload.
- **W2 — the short console write.** `write_cons_arms`'s middle arm
  (`SpecFilewrite.v:679-681`) is `∃ k, ⌜r = k⌝ ∗ ⌜k < n⌝ ∗ Q k`, relayed by
  `uwrite_post_cons` (`UkWriteLeaf.v:282`). Counter-scenario: init's `write(1,buf,1)`
  returns 0; the program holds `turn v P` and its *next* byte is still the P-th of
  `proc_upto`, but the program has advanced its string index — every banner byte and
  every echo byte is stuck on an arm nothing refutes. TRAP-ROWS T1's
  `~ uva_rmapped P (ua + k)` is the assumed fix; if it does not land, IO-LEAF has no
  application-side answer.
- **W3/W4 — the U tier cannot name `EchoOut`, and `Tn` is opaque.**
  `UkSh.v`, `UkInitMain.v`, `UkEcho.v` import neither `AppEcho` nor `EchoOut`
  (only `UkSh.v:130 Require Import EchoDisc`); `UConsLine.v:87` imports `AppEcho`.
  `EchoOut.v` requires nothing above `SpecConsoleintr`, so importing it into the
  program files makes no cycle — but they would then carry `!echoOutG Σ` and the
  four section equations `Hout/Hin/Htag/Hwin` (`EchoOut.v:2448-2451`). The
  alternative, an abstract bundle premise on `sh_deps`' mould, needs
  `proc_upto`/`line_alts` at the U tier anyway. Counter-scenario for doing
  neither: `wp_kinit_start` (`UkInitMain.v:2417`) takes an arbitrary `iProp Σ`
  `Tn` and `iClear`s it (`:2426`) — nothing in the U tier can turn an opaque
  `Tn` into `cons_out_chain`; same at `UInitKernel.init_boot_pay`
  (`UInitKernel.v:578-580`) and the whole kernel carry down to
  `boot_fixedGS.Wres`. No decision is recorded anywhere; the lane must make it
  before M1.
- **W5 — sh's fork/wait carries no exit accounting at all.** `Rc := emp` and
  `Q := fun _ => True` are literals inside `wp_uk_ecall_fork_any`
  (`UkFork.v:1132-1133`); the `child_tok` is discarded at `UkFork.v:1141-1145`
  ("a caller at this statement has said it will not redeem one") and the
  `uwait_ans` at `UkRunSys.v:2220`. Counter-scenario: the child exits carrying the
  turn and sh, holding `uch_any` and no token, cannot name the generation it
  reaped — `gen_uniq_tok` needs a `child_tok`. Nothing weaker recovers it.
- **W6 — `ush_at` is the lease's home and cannot also hold a turn with a boundary
  fact.** `ush_at n := upos γp n ∗ ukn_pay N (-1)` (`UkSh.v:1140`);
  `ush_rest` takes `⌜ukn_const N⌝` (`UkSh.v:5461`); `wp_ksh_exit` spends
  `ukn_pay N (-1)` (`UkSh.v:865`); `ush_read_recv_leaf_holds` is premised on
  `ukn_pay N = ucons_pay fsc_cons γp T` (`UShLine.v:283-285`). Counter-scenario:
  mid-line (after `"$ "` and three input bytes) sh's cursor is not at a line
  boundary, so a payload of the shape "turn at an alt-3 boundary" is false, yet
  `ush_at` asserts `ukn_pay N (-1)` at every loop head. The lease, the turn, the
  cursor and (§4) the `dl_cnt` half must be unbundled across `UkSh.v`'s ~5k lines
  and `UInitSh.sh_Rsh`/`ush_loop_head` — not in `brief-io-leaf.md`.
- **W7 — the chain is a linear resource inside two printf towers whose bytes are
  not literals.** init: `wp_kinit_putc`'s post is `ucallee_saved` only
  (`UkInitPutc.v:111-119`); the bytes are known in `wp_kinit_vprintf_loop`
  (`UkInitVprintf.v:1207-1235`), ~1300 lines below the caller. sh/child:
  `UkShDiag` is ~3k lines and its `%s` argument is an `ush_str` at run time
  (`UkShRun.v:1168-1176`), so `proc_upto cs0 (S n0) !! P = Some b` must be proved
  against a *runtime* string, not a rodata literal. Counter-scenario:
  `"exec %s failed\n"` with `%s = "echo"` must equal `line_alts !!! 1`'s bytes —
  provable only if the parser's token is pinned to the literal, which
  `wp_kshm_child_echo`'s `UConsLine.ush_line_is f 0 len` premise (`UkShEcho.v:786`)
  gives for the *input* line but nothing gives for the reconstructed argv string.
- **W8 — init's die arms have no turn.** On the fork-failure arm
  (`wp_kinit_main_die_df`, `UkInitMain.v:167`) `uinit_lend` has already run
  (`UkInitMain.v:1126`) and both `HQ` and `Hpos` crossed into `Rc` at the fork, so
  the round's lease — and with it the turn, if it rides `Rc` — is gone before the
  18-byte diagnostic is printed. Same on `die_dw` (`UkInitMain.v:1518`), which
  discards `Htok` (the live shell's `child_tok`). PROLOGUE-ALTS gives the *pure*
  alternative; nothing gives the *resource*.
