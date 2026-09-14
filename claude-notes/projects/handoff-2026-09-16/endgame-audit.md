# `Hsh_owed` ENDGAME AUDIT (read-only, 2026-09-14 session)

Read in `/shared/xv6iris-2-sup` at `origin/main` = `3d3f4bbfb`. **One correction to
the brief: `IO-LEAF M6a(1)` (`a72323b79`) is NOT on `origin/main`** — it is
unpushed on `lane/io-leaf` in the main checkout. I fetched it read-only into
`-sup` as `refs/audit/io-leaf` (no write to `/shared/xv6iris-2`). Its diff is
three files only: `iris/EchoLinks.v` (+464), `iris/UInitBanner.v` (+21/-…),
`iris/UShOut.v` (+133/-86). **Everything else below is identical on both.**
Lines cited as `M6a:` are from `refs/audit/io-leaf`; all others from `origin/main`.

The two open entailments: `UInitBootAdequacy.v:139-140`, consumed at `:243`,
and `UInitBoot.v:561-562` (`echo_Hinit_boot`'s first two Coq premises).
`Hsh_deps` is applied at exactly **two** places: `UInitBoot.v:674` (into
`UkInit.init_deps`' 16 via `init_deps_of_laws`, `UInitBoot.v:328-332`) and
`UInitBoot.v:774` (into sh's exec supply via `init_cons_sup_of_sh_slot`).

---

## 1. EVERY consumer of the free write law

`UkRun.udepw_law` is defined at `UkRun.v:467`; `UkSh.sh_deps := udepw_law 16`
at `UkSh.v:574`; `UkInit.init_deps T := udepw_law 16 ∗ □(T -∗ 15) ∗ □(T -∗ 17)`
at `UkInit.v:583-584`. 82 `sh_deps` mentions; 19 of them are premise sites in
`UkShDiag.v` alone. Only **four leaves actually spend it**:
`UkSh.ksh_w_of_law` (`UkSh.v:1369-1373`), `UkSh.ksh_w_of_prompt_in`'s right arm
(`UkSh.v:1462`), `UkShDiag.ksh_w1_of_law` (`UkShDiag.v:459-463`, which routes
through the first), and `UkInit.kinit_w1_of_law` (`UkInit.v:1309-1310`).
Everything else passes it down. The links are `EchoLinks.echo_link_w` (ordinary
byte of the current block), `_blk` (a *line* alternative's first byte, files
`cs`), `_pro` (a *prologue* alternative's first byte, files `ps`), `_taint`
(`EchoLinks.v:66/77/98/118` at M6a; same names and line numbers ±0 on main).

### init (`udepw_law 16` out of `init_deps`)

| site | what it prints | holds today | needs | milestone |
|---|---|---|---|---|
| `UkInitMain.v:1032` (`wp_kinit_banner`) | `"init: starting sh\n"`, 18 B, fd 1 | **round 0 PAID** via `kinit_banner0`/`UInitBanner.kinit_banner0_holds` (M6a:`UInitBanner.v:327`); rounds k>0 take the `∨ True` arm | k>0: `echo_link_w` per byte at `ps0 = replicate k 1`, `cs0`, `n0` = the count at the round start. `EchoDisc.pro_of_replicate_banner` (`EchoDisc.v:789`) and `proc_upto_round_banner_open` already exist; `UInitBanner.bnr` (M6a:`:201`) and `proc_upto0_banner` (M6a:`:138`) are hard-wired to `ps=[] cs=[] n0=0` and must be generalised | **M6b** |
| `UkInitMain.v:171` `wp_kinit_main_die_df`, reached `:1314` | `"init: fork failed\n"`, 18 B | free law through `UkInitPrintf.wp_kinit_printf` (`:667`, the explicitly-free form, `:682` spends `kinit_w1_of_law`) | `echo_link_pro` at `a = 2` (`pro_alts !!! 2 = u_forkfail`, `EchoDisc.v:266/238`) for byte 0, then `echo_link_w` ×17. init must still hold the turn here — it does not today (the fork's `Rc`/`Rt` went to the child) | **M6b** |
| `UkInitMain.v:283` `_die_de`, reached `:715` | `"init: exec sh failed\n"`, 21 B | same | `echo_link_pro` at `a = 1` (`pro_alts !!! 1 = u_execfail`) + `echo_link_w` ×20. **This arm is the CHILD's**, so the credential is the one init lent at its fork (`Rt`, `UkInit.init_exec_sup_pos`, `UkInit.v:1649-1658`) | **M6b** |
| `UkInitMain.v:395` `_die_dw`, reached `:1657` | `"init: wait returned an error\n"`, 29 B | same | **NO TRANSCRIPT ALTERNATIVE EXISTS** for it (`pro_alts` has exactly three, `line_alts` four, `EchoDisc.v:266/594`). It can never be *paid*. **DELETE IT** — see below | **M6b** |

**`die_dw` is deletable, and the work is two edits.** `UkRunSys.wp_uk_ecall_wait_null_live`
(`UkRunSys.v:2131`) already hands the caller `⌜r = (mword_of_int (-1)) -> Sc' = ∅⌝`
(`:2145`); `wp_uk_ecall_wait_null` (`:2264`) is the same leaf *with the row dropped*,
and `UkInit.wp_kinit_wait` (`UkInit.v:1796`, call at `:1836`) uses the row-less one.
Move it to `_live`, thread the pure row through `wp_kinit_wait`'s continuation
(`UkInit.v:1802-1809`), and at `UkInitMain.v:1644` (the `bge` false branch, i.e.
`ret < 0`) contradict it with the loop invariant's `⌜γsh ∈ cs⌝` (`UkInitMain.v:1140`,
in hand as `Hin`) plus the failing arm's `cs' = cs` (`UserChildren.wait_ans_m1`,
`UserChildren.v:410`). Then `wp_kinit_main_die_dw` and `LIT_WAIT` (`UkInitMain.v:159`)
go. The `wait_why` disjunction (`nullst = false ∨ cs = ∅ ∨ kill_shot`,
`UserChildren.v:381-387`) is *not* usable directly — `uwait_ans` absorbs `gn`/`nullst`
(`UexecRet.v:1035`) — which is exactly why T4's pure row exists.

### sh (`udepw_law 16` out of `sh_deps`)

* **the prompt `write(2,"$ ",2)`** — `UkSh.ush_promptw`/`ush_prompt_in`
  (`UkSh.v:1419/1433`), spent at `UkSh.ksh_w_of_prompt_in` (`:1455`). **M6a(1)
  paid it at EVERY line boundary**: `UShOut.ushpr` (M6a:`UShOut.v:194`) is indexed
  by the boundary `n` and `ksh_w_of_link_prompt` (M6a:`:293`) / `sh_prompt_pay_of_ushpr`
  (M6a:`:428`) hold at every `n`. Link: `echo_link_pro` at `a=0` or `echo_link_blk`
  at `a=2`, then `echo_link_w` for the space (`EchoLinks.echo_prompt_dollar`/`_space`).
  **What is missing is only the ROUTING**: `sh_prompt_pay_of_ushpr` *drops* the
  post (`iIntros "[$ _]"`, M6a:`UShOut.v:445`), and `ush_prompt_in` is still an
  affine entry-only input re-entered with `ush_prompt_in_triv` (`UkSh.v:1436`).
  → **M6a(2)**, plan (B) in `io-leaf-handover.md` (the `Wc`/`Wc'` section families).
* **the diagnostics** — `UkShDiag.ksh_w1` (`:452`) through the 15 `_chain` forms
  (M4b(1)); every one is instantiated today at `ksh_w1_of_law` (25 call sites).
  Three C sites, all fd 2, reached through `UkShRun.ush_diag_at` (`UkShRun.v:1154-1157`):
  - `panic(...)` at `ShSyms.panic`, format `shd_lit 0x1290` + one of the three
    literals `0x1298/0x12a0/0x12c8` — fully pinned, the byte family is writable today.
    Reached from sh's `fork1 == -1` arm → transcript `line_alts !!! 3 = "fork\n"`
    (`EchoDisc.v:598`): `echo_link_blk` at `a = 3` then `echo_link_w`.
  - `pc = 0xda` `"exec %s failed\n"` → `line_alts !!! 1`: `echo_link_blk` at `a = 1`
    + `echo_link_w`. The `%s` argument is existential in `ush_diag_res`
    (`UkShRun.v:1159-1166`) — must be pinned to `"echo"`; the parser pins the LINE
    (`UkSh.ush_line_is` / `UkShEcho.ush_line_toks_holds`, `UkShEcho.v:217`), not yet
    the token handed to the diagnostic.
  - `pc = 0x10e` `"open %s failed\n"` (redirection) and `UkShCd.wp_kshc_cd`
    `"cannot cd %s\n"` (`UkShCd.v:406-416`) → **no `line_alts` entry**: like
    `die_dw` these must be **refuted**, not paid. `cd` is refutable from the line
    fact (the arm demands `f k = 'c', 'd', ' '`, `UkShCd.v:414-416`); redirection is
    already excluded by `ush_simple` (`UkShRun.v:166-173`).
  The three `sh_deps` sites *above* the chain forms (`UkShDiag.v:8446` in
  `ush_diag_leaf_holds`, `:8626` `wp_kshr_runcmd_final`, `:8651`
  `wp_kshr_fork1_final`) cannot move without `UkShRun.ush_diag_leaf`
  (`Hypothesis`, `UkShRun.v:1194`) changing shape. → **M4b(2)**.
* **`UkSh.wp_ksh_read` (`UkSh.v:2087`) takes `sh_deps` and never uses it** — a dead
  premise (only `iIntros "#Hdp"` in the body). Free deletion today.

### sh's child / echo

* `UkShEcho.wp_kshr_exec_echo` (`:512`) and `wp_kshm_child_echo` (`:792`) take
  `sh_deps`, both under `Hc : ukn_triv N` (`:508/:782`).
* `UShEcho.echo_slot_of_kexec` (`:1202`), `sh_exec_sup_of_echo_slot` (`:1236`),
  `_closed` (`:1324`) all take `udepw_law 16` at `Q := fun _ => True` / `Pay := emp`
  (`UShEcho.v:1186`, `:1228`). These feed `UEchoKernel.echo_uexec_slot` (`:401`,
  spends at `:446` via `kecho_pay_all_of_law` at `:483`), the **generic/trivial**
  entry. The paid entry `UEchoOut.echo_uexec_slot_at` (`:747`) exists and is unused:
  it needs `echo_out_argv` (bridged by `UShEchoOut.v`), the child's fd-1 console row,
  and the `ech`/`echq` stage bundle. → **M3b core**.
* `UkEcho.kecho_w_of_law` (`:1351`), `kecho_pay_of_law` (`:1411`),
  `kecho_pay_all_of_law` (`:1425`) — the free instances of echo's per-write family;
  the paid `kecho_pay_of_link` is already used by `echo_uexec_slot_at`.
* `UShEcho.echo_writes_out` (`:1495`) is an unused anti-vacuity `Prop`.

### NOT blockers (item 4 anticipation)

`UexecCond.echo_gate_slot`/`cond_entry_slot` (`UexecCond.v:295/329`) take
`udepw_law 16` but are instantiated at `uprogSG_gen` where it is a theorem
(`UexecExecMint.v:218-221` via `UkRun.udepw_law_of_psok`, `UkRun.v:479`).
`UkCat.v:98` (`udepw_law 5 ∗ 15 ∗ 16`) is a **dead subtree** — nothing outside
`UkCat*.v` requires `UkCatMain`/`UkCatCat`. `USync*` needs no write law.

---

## 2. EVERY `∨ True` / trivial-arm workaround left in the U tier

| site | stands in for | removed by |
|---|---|---|
| `UkInitMain.v:1021-1022` `kinit_round0 := kinit_banner0 ∨ True`; left arm supplied only at `:2604`, Löb re-enters `iRight` at **`:1592`** | init's rounds k>0 have no credential | M6b |
| `UkInitMain.v:574/789/837/883/1046`, `UkInit.v:1658` `(Rt ∨ True)` | the banner's residue crossing the fork/exec | M6b |
| `UkSh.v:1433` `ush_prompt_in := (⌜ush_fd2p l⌝ ∗ ush_promptw) ∨ True`, + `ush_prompt_in_triv` (`:1436`) | every prompt but round 0's | **M6a(2)** |
| `UShKernel.v:407` `sh_prompt_at := (⌜ush_fd2p l⌝ ∗ sh_prompt_pay) ∨ True`, + `sh_prompt_at_triv` (`:410`) | sh entered on the closed-fd or taint arm | M6a(2) |
| `UInitSh.v:1075` `(⌜ush_fd2p (take NSTD fdv)⌝ ∨ True)`; `:1127/:1173/:1202` `(sh_prompt_pay ∨ True)` | init's two non-console head arms have no fd-2 row | M6a(2)/M6b |
| `UkShFork.v:320` `wp_kshr_fork1_final … (fun _ => True%I) emp%I` — **`Q := fun _ => True`, `Rc := emp`** | the child's payload and the lend | **M3b core** |
| `UkShRun.v:1855` fork1 at `Rc := emp` (`_any` form) | ditto | M3b core |
| `UkShEcho.v:508/:782` `ukn_triv N`; `UShEcho.v:1186/1228` `Q := fun _ => True`, `Pay := emp`; `UEchoKernel.v:401-483` the generic `echo_uexec_slot` | echo entered at the trivial payload | M3b core |
| Coq-level `(⊢ ukn_pay N (-1))`: `UkShMain.v:534`, `:706`; `UkShRun.v:2554`, `:2592`, `:2894`; `UkShDiag.v:8622` | "the child's exit payload is free" — false once the child holds the turn | M3b core (D2/D3; the `ushp_pay_free` triple is already **gone**, `UkShParseLex.v:173`, and `UkSh.wp_ksh_memset_null` already takes it as a *resource*, `UkSh.v:2417-2421`) |
| `UShLine.ush_read_ans_of_era` (`:795-822`) **discards** `ush_rd_era_win`'s right arm — `cs_lb`/`ps_lb`/`E_lb v (n+dc)` (`:752-760`) | `UkSh.ush_read_ans` cannot carry era facts | M6a(2) step 2 (`ush_mid` must gain `E_lb v n`, else `EchoLinks.ewc_read` cannot be spent at the boundary) |
| `UkInitMain.v:124` `Hypothesis Hpayfree : ⊢ ukn_pay N (-1)` | init's own exit | **discharged** (`ukn_pay_free_of_triv`); not owed |

---

## 3. `sh_pay_rest` / `sh_Rsh` / `ush_rest_l`

`UInitSh.v:509-514`, verbatim:
```
Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ) : iProp Σ :=
  (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ),
     ⌜ Persistent T ⌝ -∗
     ush_rest_l (PS := uprogSG_free) N γp T (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.
```
`UInitSh.v:624-625`:
```
Definition sh_Rsh : gname -> gname -> gname -> iProp Σ :=
  fun _ γd γs => (UkShLoop.ushl_dat γd ∗ usz γs (kexec_sz ElfUser.sh_elf))%I.
```
`UkSh.v:6455-6472` `ush_rest_l R := □ (∀ l, ⌜ukn_const N⌝ -∗ shk_code γt -∗
ush_jtab γt -∗ ush_loop_head R l -∗ ∀ h m f k i2 n, ⌜ush_regs m⌝ -∗ ⌜s1 = sh_buf+k⌝ -∗
⌜a5 = f k⌝ -∗ ⌜k ≤ i2 < sh_nbuf ∧ f i2 = ubyte0⌝ -∗ ⌜ush_fd0p l⌝ -∗ ush_rest_line f k -∗
ush_pstate l -∗ R -∗ ubytes γd sh_buf sh_nbuf f -∗ urun N h m 0x97a (16+(ush_Dbody+n)) -∗ WP Loop)`.

**The discharger already exists**: `UkShFork.ushf_rest_of_body` (`:959-1018`) proves
`ush_rest_l N γp T (UkShLoop.ushl_R N sz)` from — `UkShLoop.ush_line_lexable`
(discharged by `UkShEcho.ush_line_toks_holds`, `:217`), the three closed bounds
`8344 ≤ sz`, `pgroundup sz = sz`, `usz_ok (sz+65536)` (closed at `0x5000`),
`UkSh.sh_deps`, `UkRun.uxsup`, `UkSh.ush_gen_slot N T`. `ushl_R sz := ushl_dat γd ∗
usz γs sz` (`UkShLoop.v:158`) is `sh_Rsh` uncurried, and M5(3)'s R2 rename is done —
`sh_pay_rest` names `ush_rest_l`, so `UShLine.v:1164-1180`'s sketch of `sh_rest_holds`
is **stale** where it says `ush_rest`.

**The one hypothesis that is not available, and no note mentions it:**
`sh_pay_rest` quantifies `T` *internally* over every `Persistent T`, but
`ushf_rest_of_body` needs `UkSh.ush_gen_slot N T` = `□ (∀ W, T -∗ my_pay … -∗ uslot W)`
(`UkSh.v:6049-6051`) — "the taint buys a generic slot" — which is **false for an
arbitrary `T`** and is only true at `echo_taint γ`. The taint arm is reachable:
`ush_rest_line f k := (line fact) ∨ T` (`UkSh.v:6349-6353`) and the discharger
branches on it (`UkShFork.v:1000-1006`). So `sh_rest_holds` as sketched
(`UShLine.v:1164-1170`, taking `T` as a Coq parameter) **cannot have `sh_pay_rest`'s
stated type**. The fix is one of: (a) add `UkSh.ush_gen_slot N T -∗ UkRun.uxsup -∗`
inside `sh_pay_rest`'s `∀ T` (then `sh_pay_of_parts`, `UInitSh.v:547-553`, supplies
them from `echo_Hinit_boot`, where `ush_gen_slot` is already built from
`AppEcho.echo_sup_of_taint`); or (b) restate `sh_pay_rest` at a fixed `T` and
quantify `T` in `Hsh_owed`. **Rule this before R3 starts.**
Nothing else is missing: the child's payload/lend at the fork and the diagnostics'
obligations are *inside* `ush_loop_head`/`ush_rest_l`'s body and are already
discharged (at the trivial payload) by `wp_kshm_body`. **Nothing from the kernel is
needed** — `ush_rest_l`'s record premises (`ukn_const`, `shk_code`, `ush_jtab`) moved
into the obligation in SH-LINE 2b(b) and are paid by `UShKernel.sh_uexec_slot`.

---

## 4. Other blockers no note names

1. **`ksh_w` at a non-console descriptor has no discharge.** `UkSh.ksh_w`
   (`:1348`) is stated at an arbitrary `fdw`; the only non-free discharge is
   `UShOut.ksh_w_of_link_prompt`, which demands `l !! 2 = Some (FdOpen _ true
   (FdDevice CONSOLE))` (M6a:`UShOut.v:295`). On init's `ufd_l0` head arm sh's fd 2
   is CLOSED and the write produces no bytes — there is no `UkWriteLeaf` lemma for
   that arm (cf. the read side's `ush_read_sup_closed`). M4b(2)/M6a(2) needs one, or
   the arm must be refuted from the boot dance.
2. **`sh_pay_rest`'s `∀ T`** — §3 above.
3. **Assumption audit: clean.** `make audit-only`'s thirteen
   (`claude-notes/durable-notes.md:853-863`) are all from the *statement*
   (`resv_matches`, `resv_is_valid`, 7 × `PrimInt63`, 3 × `PrimString`) plus
   `functional_extensionality_dep`. None touches `udepw_law`. No `Admitted`, no
   `Axiom`, and every `Parameter` in the tree is a `Spec*_sconf` module field, not a
   U-tier assumption.
4. **Live section `Hypothesis`es in the sh/init cone**, all discharged at
   `echo_Hinit_boot` or at the program's constructor: `UkSh.v:1643/1645/1652`
   (`Pm`'s three laws), `UkSh.v:2074` (`ush_read_leaf`, discharged by
   `UShLine.ush_read_recv_leaf_holds`), `UkShRun.v:1194` (`ush_diag_leaf`,
   discharged by `UkShDiag.ush_diag_leaf_holds` — **this is the one M4b(2) must
   re-shape**), `UkShParse{Lex,Cmd,Exec,Redir,Tok}.v` `ushp_malloc_ok`,
   `UkInitMain.v:124` `Hpayfree`, `Hpsok_free` everywhere.
5. **No `Context` in the U tier is satisfiable only by the free law.** `sh_deps` /
   `init_deps` are premises, never section variables — so D1's redefinition
   (`sh_deps := echo_links`) touches no `Context`.

---

## 5. Recommended order, cones, collisions

1. **M6a(2) — the routing (plan (B) of `io-leaf-handover.md`).** *Prerequisite of
   M3b core and of M4b(2)'s payment.* Cone: `UkSh.v`, `UShLine.v`, `UShOut.v`,
   `UShKernel.v`, `UInitSh.v`, `UInitBoot.v`, `UkShLoop.v`, plus signature ripples
   in `UkShEcho/UkShCd/UkShFork/UkShRun/UkShMain`.
2. **M6b — init.** Do the `die_dw` deletion FIRST (it is self-contained: `UkInit.v`,
   `UkInitMain.v`), then the round-k banner and the two live die arms. Cone:
   `UkInit.v`, `UkInitMain.v`, `UkInitPrintf/Putc/Vprintf.v`, `UInitBanner.v`,
   `UInitBoot.v`, `UInitKernel.v`. **Collides with M6a(2)/M3b only at `UInitBoot.v`
   (`Rd`'s choice) and `UInitSh.v`.** M6b's die arms need the turn *back* in init's
   hand, which is M3b core's child payload — so land the `die_dw` deletion and the
   round-k banner early and the two die arms after M3b.
3. **M3b core.** Cone: `UkShFork.v`, `UkShRun.v`, `UkShEcho.v`, `UkShMain.v`,
   `UShEcho.v`, `UShEchoOut.v`, `UEchoOut.v`, `UkSh.v`, `UShKernel.v`, `UInitSh.v`,
   `UkShParse*.v`, **and `UkShDiag.v`** (the six `(⊢ ukn_pay N (-1))` premises).
   Blocked additionally on TRAP-ROWS-5 for the wait redemption only.
4. **M4b(2).** Cone: `UkShDiag.v`, `UkShRun.v` (`ush_diag_leaf`'s shape +
   `wp_kshr_runcmd_final`/`wp_kshr_fork1_final`), `UkShFork.v`, `UkShMain.v`,
   `UkShCd.v`, `UkShEcho.v`, + a new link-side file above `UkWriteLeaf`.
   **Heavy collision with M3b core (five shared files) — serialise them; M3b first,
   because M4b(2)'s payment needs the child's turn at each site's stage.**
5. **SH-LINE R3** (`UShLine.v`, `UInitSh.v`, `UInitBoot.v`, `UInitBootAdequacy.v`).
   Independent of 1–4 *except* for the `∀ T` restatement in `UInitSh.v`, which
   collides with M6a(2)'s edits to the same file. Can run in parallel with M6b if
   the `UInitSh.v` restatement lands first as its own small commit.

After 1–5: delete `UkSh.sh_deps` (`UkSh.v:574`) or redefine it as `echo_links` (D1),
drop `Hsh_deps`/`Hsh_rest` from `UInitBoot.v:561-562`, and delete both conjuncts at
`UInitBootAdequacy.v:139-140` (and `:243`'s `destruct`).
