E5 -- THE APPLICATION CLAIM, DESIGN PAGE (coordinator, 2026-09-15; from the Fable review of ECHO-OUT part 3, scratchpad brief-review-echo-out.md; this page REPLACES REVISIONS 4-8 of e5-design.md and app-echo.md's "E5 DESIGN OF RECORD, REVISIONS 4-7"/R8 where they conflict; it is the single source for lanes CONS-IO F and ECHO-OUT part 4).

=== 0. TWO FACTS EVERY DECISION BELOW RESTS ON ===
F1 NAMING AND REACH. `app_out`/`app_in`/`app_R`/`app_tag` are at `app_fixed`, fixed before `HR` and before any era's `uart_names` exist: they see only Σ-level cameras of the application's own, never `riscvFixedGS` or `uart_names`. A link or the shift holds exactly its stated premises plus the port claims; `Happ_echo` is a CLOSED entailment. Hence every exclusive the application needs across a kernel-side gap must be the application's OWN, and every per-era linear thing originates at the one once-per-era step that runs the ledger -- `App.Hpow`'s power-on arm (a plain bupd with `app_R` in hand) -- and is CARRIED BY THE KERNEL to where it is needed (init's boot bundle; the PLIC payload; the port invariant).
F2 THE SHIFT IS PERSISTENT AND SPLIT. `cons_echo_shift` is `□`; `in_run` is `in_append ∧ echo_link (…)`: the echo store (T1) and the log append (T2) are two fupds, and the application's spec must be total over interleavings the kernel forbids with cons.lock but never states (T1(h₂), T1(h), T2(h)) UNLESS the kernel lends it an exclusive that the first firing stores where the second firing sees it (the port claim) and the second firing is handed again. The exclusive must be the application's (F1).

=== 1. THE KERNEL SIDE (lane CONS-IO F; `-tlw`) ===
K1 `RiscvPtsto` gains ONE field `riscv_win_res : nat -> iProp Σ` (timeless; `win_res_triv := fun _ => emp`): the application's per-era ECHO WINDOW TOKEN. It rides the PLIC payload beside the receive token: `plic_payload_uart` gains `win_at j (S gen_id)` (:= `riscv_win_res (S gen_id)` at Uart0, `emp` at Uart1), carried exactly where `uart_log_hi`'s half rides (`uart_rx_writer`, the PLIC slot, uartintr -> consoleintr's contract, `ct_mark`/`ct_owed`); `cons_echo_shift` gains the premise `riscv_win_res (S gen_id) -∗` (after `obs_hist_lb h`); `in_append k h c cs Φ`'s post gains `riscv_win_res k ∗` (the token returns with the append); `in_claim_append`/`uart_inv_append` hand it back to the arm's exit; `cons_echo_shift_triv`/`in_run_of_licence`/`in_append_of_licence` return it trivially (a licence route ignores it). `echo_link`, `out_link`, `read_link`, `in_run`'s shape: UNCHANGED.
K2 `App.xv6_app` gains two fields: `app_turn : app_fixed -> nat -> iProp Σ` (init's console credential for the era) and `app_win : app_fixed -> nat -> iProp Σ`; obligations: `Hwint : Timeless (app_win A c k)`; `Hpow`'s power-ON yield becomes `app_out A c (S (obs_boots h)) [] [] ∗ app_in A c (S (obs_boots h)) [] [] [] ∗ app_turn A c (S (obs_boots h)) ∗ app_win A c (S (obs_boots h))`; `Hinit_boot` gains `app_turn A c (S gen_id) -∗` beside `app_boot A c (S gen_id) r`; `Happ_echo` gains the equation `riscv_win_res = app_win A c ->` beside the out/in/tag equations and STAYS CLOSED (no obs handle); `Happ_win_sup : app_sup … ⊢ …`? NO -- the generic route never needs the token (it returns what it is handed). `app_triv` at `fun _ _ => emp`.
K3 The carry: `power_boot_res` (milestone E's route) carries the two extra yields: `riscv_win_res (S gen)` into the boot's PLIC deposit (`plic_uslot_deposit`/`ProofMain`'s console mint beside `uart_log_hi`'s half) and the turn into `Hinit_boot`'s bundle -> `UInitKernel.init_boot_pay` (a fourth conjunct beside the console lease; the shape `app_turn` has at the U tier is the application's, threaded as an opaque `iProp` the way `T` is) -> `UkInitMain.wp_kinit_start` (held; IO-LEAF spends it at init's first banner byte). `app_xfer_boot_raw` UNTOUCHED.
K4 Nothing else: the era index, the stamps, `Htx`/`Hrx`, `read_link`, the licences, `xv6_ssupply` stay.

=== 2. THE APPLICATION SIDE (lane ECHO-OUT part 4; `-disc`) -- CLAIM-RESIDENT STATE, NO LEDGER IN ANY LINK ===
Ghosts per era `v : era_pins` = {turn (ghost_var nat), cs (mono_list nat), E (mono_list (list mobs * bv 8)), wcnt (ghost_var nat, shares ¼ out, ¼ in, ½ token)}; `era_pin k v` persistent (the ledger's pin map, its auth used ONLY at `Hpow`).
```
eout k ho acc := T ∨ ∃ v so, era_pin k v ∗ turn_auth v (pcount (o_cs so) (o_E so) (o_w so))
   ∗ cs_auth v (o_cs so) ∗ Elist_auth v (o_E so) ∗ wcnt v (1/4) (length (o_E so))
   ∗ ⌜eout_pure k ho so acc ∧ cs_len_ok so ∧ Forall (< length line_alts) (o_cs so)⌝
ein k hi pops dl := T
 ∨ ∃ v n cs0, era_pin k v ∗ wcnt v (1/4) n ∗ ⌜length (echoed pops) = n⌝                       (* settled *)
     ∗ Elist_lb v (seg_of (echoed pops)) ∗ cs_lb v cs0 ∗ ⌜ein_pure' k pops dl cs0⌝
 ∨ ∃ v n cs0, era_pin k v ∗ wcnt v (1/4) n ∗ wcnt v (1/2) n ∗ ⌜length (echoed pops) + 1 = n⌝ (* window *)
     ∗ Elist_lb v (seg_of (echoed pops)) ∗ cs_lb v cs0 ∗ ⌜ein_pure' k pops dl cs0⌝
app_win  c k := ∃ v n, era_pin k v ∗ wcnt v (1/2) n
app_turn c k := ∃ v, era_pin k v ∗ turn v 0 ∗ cs_lb v [] ∗ E_lb v 0
```
`ein_pure'` = the landed `ein_pure` minus the stage tie, plus `E_index`/`E_byte (seg_of (echoed pops))`. NO founded arm, NO seeds, NO escrow, NO adoption, NO `led_acc`: `Hpow` allocates `v`, founds both claims in their paired arms at `so = MkO [] [] []`, mints the pin, and yields the turn (to init) and the token. THE ECHO (`echo_link`: both claims + the token handed by the shift): three agreeing `wcnt` shares give `length E = n = length (echoed pops)`, the lower bound gives `seg_of (echoed pops) = E`; `Hnew'`/`Hprefixes`/`Hlt` follow from the order fact and the stamps as in the landed proof (EchoOut.v:~1793-1813); it updates all three shares to `n+1`, returns the in claim in the WINDOW arm (holding the token's ½), and the payload carries `⌜x = (open_seg h, c)⌝ ∗ Elist_lb v (E ++ [x]) ∗ cs_lb ∗ ⌜E_index/E_byte (E ++ [x])⌝`. THE APPEND (in claim only): compares the two lower bounds (same mono_list, lengths n and n+1) to get `seg_of (echoed pops) = E`, files the entry, returns to the settled arm and hands the token's ½ back (K1's post). ANY SECOND FIRING of a link of the run meets the window arm: ¼ + ½ stored plus ½ handed is 5/4 -- `ghost_var_valid_2` refutes it. WRITES touch only the out claim (`echo_write_link`/`_blk` as landed; the FIRST write is the ordinary link at `P = 0`: `turn_agree` pins the cursor at 0, `pcount_zero` gives `E = [] ∧ w = []`, so `acc = []` is DERIVED, a paired claim at `acc ≠ []` refuted purely by the writer's own cursor -- `eout_step_write_first` goes). READS touch only the in claim (`echo_read_link`; `read_ret` additionally exports `⌜E_index (seg_of (echoed pops))⌝ ∗ ⌜E_byte (seg_of (echoed pops))⌝` so SH-LINE can use `ein_read_line`). `eout_drain`, `Htx`, `echo_led_tx/rx/phi` unchanged; the ledger keeps the taint counter, the pin map (auth at `Hpow` only) and the phi conjunct.
DELETE from EchoOut.v: `istage`/`i_owed`/`ein_owed`/`stage_tie`, `in_frag`/`in_auth` and their three-halves laws, `oseed`/`iseed`/`seed_dom`/`seed_bank`/`seed_bank_on`, `era_slot`'s escrows, `era_entry`/`era_inv_acc`/`era_inv_get`/`era_full_slot`, `eout_step_write_first`, `led_taint`/`T_of_lb`, `led_acc`, `ein_op`. KEEP: sections 1-1b, `write_stage_byte`, `cs_len_ok_*`, `eout_pure_nil_stage`, the turn/cs/E ghosts, `echo_led_pow/tx/rx/phi`, `eout_step_echo/write/write_blk`, `ein_step_read`, `eout_drain`, the section-7 wrappers minus `led_acc`.
THEN (after F lands): `echo_happ_echo : ⊢ ∀ GEN XI, cons_echo_shift` (closed), the AppEcho wiring (`echo_fixed := echo_gn`; `echo_out := eout`, `echo_in := ein`, `echo_win`, `echo_turn`; `echo_Hpow` yields the four; `echo_phi := fun _ h => disc h -> Forall good_out (cycles_of h)`; delete `echo_phi_disc`/`EchoOutPure.echo_phi_of_good_out`; the eight dependents' `!echoOutG Σ`; `UInitBoot`'s two triv asserts by the taint route; `echo_Hinit_boot` holding the turn), and `UInitBootAdequacy.Hphi` closed from `echo_led_phi`.

=== 3. ORDER ===
Two lanes in parallel: CONS-IO F (K1-K4; one full build; phase 1 = statements + the PLIC/boot routes compiled, STOP AND REPORT the trusted diff) and ECHO-OUT part 4 (§2's re-cut against LOCAL copies of the two changed link statements -- `cons_echo_shift` with the token premise and `in_append` with the token in its post -- marked "replaced at F's landing"; statements first, then the proofs; STOP after the statements compile with the deletions done, report, then proofs). Then, after F lands: ECHO-OUT part 5 (`echo_happ_echo`, the AppEcho wiring, `Hphi`). Then IO-LEAF (init's first byte on the ordinary link with `app_turn`), SH-LINE R2/R3, SELF-KILL step 5.

=== 4. WITHDRAWN (for the record) ===
R4's "the application's exclusive cross-era state lives in the ledger; every link opens obsN"; R7's "adoption at init's first banner byte"; R8's "the founded arms hold the seeds"; RULINGS AFTER CONS-IO PHASE 1 (1)'s "ECHO-OUT's claim carries an append-owed state" (replaced by the token-guarded window arm). KEPT: the era number as index, the kernel's stamps, `echo_phi := disc h -> Forall good_out (cycles_of h)`, chain-first/append-last, the history-free ledger, the founding at `Hpow`.
=== 5. OWNER QUESTION (pending; proceed meanwhile) ===
Two more application-supplied per-era resources ride the kernel: `app_turn` to init via `Hinit_boot`, and `app_win` on the PLIC payload beside the receive token (a new fixed-record field `riscv_win_res`). The coordinator's calls on the review's other two questions: re-cut to the claim-resident shape (not the minimum delta); keep `cons_echo_shift` persistent with the kernel-lent token (not a linear echo justification of cons.lock).

=== 6. OWNER'S RULING (2026-09-15) AND THE DEBT TO REPAY AFTER QED ===
Both accepted AS WORKAROUNDS to get the echo application proven: (1) the turn carried to init and the
echo window token as a fifth application-chosen predicate lent in consoleintr's contract. TO COME BACK
TO, once everything is proven: (a) "this whole notion of what an application is, and what the
app-kernel interaction is in terms of adequacy" -- redesign the application record / the parameterisation
of the kernel proof; (b) "a single invariant IO instead of separate I and O" -- the split output/input
claims and the lent token are "really ugly"; merge into one application resource. Record both in the
worklist at the next landing as POST-QED REDESIGN items; do not start them before the theorem closes.

=== 7. THE ROAD-TO-QED REVIEW (2026-09-16; scratchpad tasks-review-road-to-qed.md) ===
Eight warts before Qed: W1 init's three failure diagnostics ("init: fork failed\n", "init: exec sh
failed\n", "init: wait returned an error\n") are walked today but not in the transcript -- unrefutable
(fork's -1 has no reason; exec's failure is a legitimate refund; wait's -1 is bare) -> PROLOGUE
ALTERNATIVES in EchoDisc (pure), chosen at init's 19th byte like the line alternatives; W2 the short
console write arm (`k < n`, either_copyin failure) has no reason -> a kernel row `~ uva_rmapped P
(ua + k)` on the short arm (the read's swallow pattern); W3 `read_ret` hides `dl` -> an app-side
delivered-count half `dl_cnt` in the era (ruled, sent to ECHO-OUT part 5); W4 the read's -1 arm has
no reason after 4b' -> relay the reader's `kill_shot gn` on consoleread's -1 arm and make the exit
ecall's deposit two-sided `sexit_pay f xs ∨ kill_shot gn` (the kernel refutes the shot on the
not-killed branch); W5 the resume arm at the child's null store once the child's payload carries the
turn: the deposit `kill_owed gn` (linear) ∗ the Löb slot proved with the bundle -> the LAZY-CONDITIONAL
arm `uexec_kill_arm_F X sc W f := ⌜uvis_lazy W = true⌝ -∗ X W` with the kernel discharging the
antecedent at vmfault's success arm (a pure-antecedent wand, not an ∧) -- forced the moment IO-LEAF
lands, so schedule it right after step 5; W6 sh's payload plumbing (`ush_at` carries `ukn_pay N (-1)`
as the lease's home; the turn with a boundary fact cannot live in the -1 payload mid-loop: unbundle
lease/turn/cursor across UkSh.v); W7 sh's and init's printf loops (the chain leaf is a linear resource
threaded through ~1300-line/~3k-line loop proofs, not an iApply swap); W8 `Hlt` derived inside
`echo_happ_echo`; per-byte `E_byte` for sh's gets.  ORDER: part 5 (with dl_cnt) -> step 5 at the trivial
payload -> ONE kernel lane for the rows W2 + W4(i)(ii) + W5's arm -> W1 (pure) -> IO-LEAF (init's chain
incl. printf, then sh/child/echo) -> SH-LINE R2/R3.  POST-QED: one `riscv_cons_res k h (acc, pops,
dl)` at one witness with one link family `cons_link k h ev Φ` (ev ∈ {Out b, In c cs, Read ws}; the
shift becomes one atomic event per accepted byte -> the window token, ein_pend, wcnt, app_win, the PLIC
carry all go); one application structure instantiated once; the taint not a machine field. Shape now
for cheap removal: keep ewin/wcnt confined to EchoOut.v; state the kernel rows as facts about the C;
prologue alternatives in EchoDisc only.
OWNER QUESTIONS (2026-09-16): Q1 prologue alternatives for init's diagnostics (pure weakening in O5's
spirit) vs a kernel memory-availability promise; Q2 the two kernel rows (W2, W4) before Qed vs a named
hypothesis; Q3 the lazy-conditional killing arm now vs the child's exit not carrying the turn.
OWNER'S ANSWERS (2026-09-16): Q1 YES -- init's three failure messages are allowed in the top-level trace
theorem (prologue alternatives in EchoDisc). Q2 YES -- fix the specs: the short-write reason, and the
read's -1 arm relaying `kill_shot` with the exit deposit two-sided. Q3: "on page fault, the process
should provide these two facts you name, but they should be separated by separation-logic AND" -- at a
KILLING-CAUSE trap the process offers `(the -1 deposit) ∧ (the resume continuation)` (additive
conjunction; the kernel takes the deposit if it kills, the continuation if it serves the fault); NOT
the lazy-conditional wand. Since the deposit goes down to usertrap and the continuation is kept by the
engine's loop today, the ∧ must be handed to usertrap whole and the untaken continuation comes back
through usertrap's resume post (the earlier cost sheet's (C2): `uexec_ret_F`'s non-ecall branch becomes
`ukill_cred_at gn sc ∧ X W` at a killing cause; `ukb_F`'s post gains the successor slot on the resume
arms; `usertrap_post`/`SpecUservec` relay it; the four ProofUsertrap* resume arms produce it from the
pair; `UexecApply`'s transparent round reads the slot off the kernel's post). The earlier "no ∧" ruling
applied to SYSCALLS (nothing kill-related at an ecall), not to page faults.
CORRECTION (2026-09-16, owner): a process killed while blocked in read NEVER resumes to user mode
(usertrap's post-syscall check exits it), so sh's getcmd/exit(0) after a -1-by-kill is unreachable and
nothing is paid there. T2 is: consoleread's -1 arm carries the reader's persistent `kill_shot gn`; it
rides the syscall's result to usertrap's second killed check, whose not-killed branch is REFUTED by the
flag's monotonicity; the user-level syscall post loses the kill case of the -1 arm (`r = -1 -> fd 0
closed` and the other non-kill causes only). The "two-sided exit deposit" is WITHDRAWN (a leftover of
KILL-PAY's relay design). W4 dissolves: sh never pays an exit after a -1-by-kill.
