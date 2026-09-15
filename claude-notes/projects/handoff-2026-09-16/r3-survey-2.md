# R3-SURVEY (post-step-4) -- what closes `Hsh_owed`'s second conjunct, and what stands in its way

Read-only survey in `/shared/xv6iris-2-sup`, branch `lane/r3-survey` = `origin/main`
`81107fe83` (code `7da574e81`). No file edited, no build, no Rocq query (every
fact below is read off the sources; the three that would need Rocq are listed
in §8). Line numbers are those of the checkout.

## 0. Vocabulary (plain terms, defined once)

* A WP (weakest-precondition) proof says "from these RESOURCES this code runs
  safely". A resource is a proposition of separation logic a process owns; a
  WAND `P -∗ Q` consumes `P` and yields `Q`; a PERSISTENT resource (`□ P`) can be
  copied; a LAW is a persistent wand taken as a premise low in the tree and
  proved once at the top (the application's instantiation, `UInitBoot`).
* The TAINT `T` is the application's persistent fact "the console discipline
  has been broken"; once it holds nothing more is claimed and a process may run
  arbitrary code on the GENERIC SLOT (`uslot W`: the kernel's per-process
  user-execution WP at key `W`). `AppEcho.echo_taint γ` is the instance; the
  kernel's kill credential IS the taint (`riscv_kill_cred = echo_taint γ`).
* A RECORD `N : uk_names Σ` is the ghost-name bundle a user process is stated
  over; its PAYLOAD `ukn_pay N : Z -> iProp` is what the process hands its parent
  at exit status `x`. sh's payload is CONSTANT in the status (`ukn_const N`).
* The GENERIC SLOT LAW of a record, `UkSh.ush_gen_slot N T :=
  □ (∀ W, T -∗ my_pay (uvis_gen W) (ukn_pay N) -∗ uslot W)` (UkSh.v:6376): a
  tainted process may stop running sh's code at any key. `ush_gen_run`
  (UkSh.v:6383) spends it: `ush_gen_slot -∗ T -∗ urun N h m pc avail -∗ WP`.
* The EXEC SUPPLY is what an `exec` syscall spends. `UkRun.uxsup :=
  uxsup_at (fun _ => True)`, `uxsup_at Q := □ ∀ W, sbundle_pay uslot USYS_exec Q W`
  (UkRun.v:540-546): the GENERIC one, "this process may exec ANY path at
  payload Q". `UkShEcho.sh_exec_sup_echo Q Cr` (UkShEcho.v:454) is the PINNED
  one: only `/echo`, only from the root, only for a child lent `Cr`.
* The CREDENTIAL FAMILIES: `Wc n p` (the era's write credential at input
  boundary `n` with `p` prompt bytes out; `p = 3` = the line's block still
  owed), `Wb n` (the banner-owed credential), `Pm n` (the lease's pieces the
  loop holds mid-line). At the top: `Wc := EchoLinksLine.ewc_lcred (echo_taint γ)
  γ (S gen_id)`, `Wb := UInitBanner.kinit_ban (echo_taint γ) γ`, `Pm := UShLine.ush_mid γ γp`.
* `UkSh.ush_rest_l N γp T Wc Wb Pm R` (UkSh.v:6810-6836) is the TRUSTED TAIL
  OBLIGATION: "from 0x97a (after `gets` returned), with the line fact and the
  loop's carried state `R`, the rest of main's body runs and re-enters the
  loop head". `UInitSh.sh_pay_rest Rsh := ∀ γp N T Wc Wb Pm, ⌜Persistent T⌝ -∗
  ush_rest_l N γp T Wc Wb Pm (Rsh …)` (UInitSh.v:524-531) is its closed form,
  and `Hsh_owed`'s second conjunct (UInitBootAdequacy.v:140) is `⊢ sh_pay_rest sh_Rsh`.
* `UkShFork.ushf_rest_of_body` (UkShFork.v:1021-1092) is the ONLY lemma in
  the tree proving `ush_rest_l` (grep: `wp_kshm_body`/`wp_kshf_fork`/
  `ushf_rest_of_body` have no caller outside UkShFork.v).
* An AFFINE ARM is a `∨ True` a proof may take to throw a credential away;
  lane RESIDUALS (running now in `-disc`) is killing them: (A) the fork's pid
  sub-arm, (B) the exec-seam rows, (C) the kills of every `∨ True` incl.
  `ush_wcp`'s third arm and the deletion of the affine assemblers
  `UkSh.ush_at_of_pm`/`UShLine.ush_at_of_mid`, (D) `sh_deps` made
  taint-conditional and `Hsh_owed`'s FIRST conjunct deleted.

## 1. `ushf_rest_of_body`'s premise list, and what the top cannot supply

Verbatim (UkShFork.v:1021-1053), plus the section it closes over
(UkShFork.v:93-151, 241):

```
  Section context: (N : uk_names Σ) `{Hpay : !ukn_const N} (γp : gname)
    (T : iProp Σ) `{HT : !Persistent T} (Wc : nat -> nat -> iProp Σ)
    (Wb : nat -> iProp Σ) (Pm : nat -> iProp Σ) `{!ctokG Σ} {SG : uexecSG Σ}
    `{PS : uprogSG Σ}; Hypothesis Hpsok_free : forall k, free_num k -> psok k;
    Context `{HWct : forall n p, Timeless (Wc n p)}.          (* :241, step 4 *)

  Lemma ushf_rest_of_body (sz : Z) :
    UkShLoop.ush_line_lexable ->
    8344 <= sz -> UserPtTree.pgroundup sz = sz -> usz_ok (sz + 65536) ->
    (forall i : nat, ⊢ Wc i 3%nat -∗ Wc i 0%nat) ->
    (forall i : nat, UkSh.ush_bnd i -> ⊢ Pm i -∗ Wb i -∗ UkSh.ush_at N γp i) ->
    UkSh.sh_deps -∗
    uxsup -∗
    ushf_kill_law -∗
    ushf_child_law -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkSh.ush_gen_slot N T -∗
    UkSh.ush_rest_l N γp T Wc Wb Pm (UkShLoop.ushl_R N sz).
```

For the `∀ γp N T Wc Wb Pm` that `sh_pay_rest` quantifies, the top can supply:
`ush_line_lexable` (a closed computation: `UkShEcho.ush_line_toks_holds`,
UkShEcho.v:155-160/218 plus `echo_toks_lt10` :91 -- a five-line corollary
nobody has written yet); the three bounds (closed at `sz = kexec_sz sh_elf =
0x5000`, `UShKernel.sh_kexec_sz` :159, and `sh_Rsh (ukn_t N) (ukn_d N)
(ukn_s N)` unfolds to `ushl_R N (kexec_sz sh_elf)` -- UInitSh.v:646-647 vs
UkShLoop.v:164); `Hpsok_free` (`fun k H => H` at `uprogSG_free`,
UInitBoot.v:~897); `⌜ukn_const N⌝` (NOT from outside, but the box hands it
in as its first premise, UkSh.v:6812 -- the discharge opens the box, learns
`Hc : ukn_const N`, and applies the lemma at `(Hpay := Hc)`); `sh_deps`
(`Hsh_deps` today; after RESIDUALS (D) only as `□ (echo_taint γ -∗ sh_deps)`).

The top CANNOT supply, for an arbitrary record and arbitrary families:

1. `UkSh.ush_gen_slot N T` -- (B) of the old survey, unchanged: at the top the
   generic law is `Hmint : □ ∀ R W, echo_taint γ -∗ my_pay (uvis_gen W)
   (fun _ => R) -∗ □ (riscv_kill_cred -∗ R) -∗ uslot W` (UInitBoot.v:681-691,
   from `uslot_mint_all`, UexecExecMint.v:264-268); turning it into
   `ush_gen_slot N T` needs `ukn_pay N = ucons_pay …` and the kill wand
   `ucons_pay_taint`, which exist only where the record is known:
   `UInitSh.init_exec_sup_of_sh_slot` :1198-1205 (`Hgen'`) and
   `UShKernel.sh_uexec_slot` :636-637 (`Hgen'` at `Hpayeq`).
2. `(∀ i, ush_bnd i -> ⊢ Pm i -∗ Wb i -∗ ush_at N γp i)` -- NEW since step 4
   (M4b(2) made it a premise of the DISCHARGER on purpose, UkShFork.v:1034-1038).
   `ush_at N γp i = upos γp i ∗ ukn_pay N (-1)` (UkSh.v:1739), so the
   assembler is payload-guarded: the top's `Hsh_pmwb` is `∀ γp N i, ukn_pay N =
   ucons_pay … -> …` (UInitBoot.v:807-815, from `UShLine.ush_at_of_mid_wb`
   :588-592 whose first premise is that equation). It cannot be given for an
   arbitrary `N` -- exactly (B)'s shape again.
3. `∀ n p, Timeless (Wc n p)` -- NEW since step 4 (`HWct`, UkShFork.v:241): the
   wait's redemption strips a later off the child's payload `ushf_wq np = Wc
   np 3 ∨ Wc np 0` (`gen_pay_timeless`, UkShFork.v:795, through
   `ushf_wq_timeless` :259), so `ushf_rest_of_body` closes over `HWct`
   (transitively through `wp_kshm_body` -> `wp_kshf_fork`). `sh_pay_rest`
   quantifies `Wc` with no timelessness, and UkSh.v has no such hypothesis
   (grep `Timeless` in UkSh.v: none), so the loop cannot pay it inside the box
   either. Fine at the era (`EchoLinksLine.ewc_lcred_timeless` :476, needs
   `Timeless T`; `echo_taint_timeless` AppEcho.v:~213).
4. `ushf_kill_law Wc`, `ushf_child_law Wc`, `ush_panic_law Wc Wb` -- NEW since
   step 4: facts about the ERA's families (the paid echo child runs at
   payload `ushf_wq np`, a killer pays `Wc n 0`, "fork\n" is payable from
   `Wc n 3`). Their only dischargers are at the era's links --
   `UShEchoPay.ushf_child_law_holds_at` :313-316, `ushf_kill_law_holds` :300-302
   (needs an `era_pin`), `UShPanic.ush_panic_law_holds` -- all at `Wc :=
   ewc_lcred T γ (S gen_id)`, `Wb := fun n => ∃ v, era_pin γ (S gen_id) v ∗
   ewc_ban T v n 0` (= `UInitBanner.kinit_ban T γ n` unfolded, UInitBanner.v:280-281)
   and `T` with `□ riscv_kill_cred -∗ T`. They are FALSE for some families
   (`Wc := fun _ _ => emp` makes the child law ask echo to write "hello world"
   from nothing), so no `∀ Wc Wb T` form can be proved. NOTE: none of the
   three dischargers has a consumer today (grep), and `UShEcho.sh_echo_slot`
   (:888) is built nowhere at the top yet.
5. `uxsup` -- (A) of the old survey, unchanged: no producer exists (§2).

CONCLUSION OF §1: after step 4 the obstacle is no longer only (A)/(B)/(C).
`sh_pay_rest`'s `∀ T Wc Wb Pm` is itself the obstacle: its discharger's
premises are era facts. The obligation must be DISCHARGED AT THE ERA'S FAMILIES,
i.e. `sh_pay_rest` should not be restated but deleted, and `sh_pay`'s second
conjunct `∀ γp N, ush_rest_l N γp T Wc Wb (Pm γp) (Rsh …)` (UInitSh.v:553-556,
at `sh_pay`'s own fixed `T Wc Wb Pm`) built directly in `echo_Hinit_boot`. That
is the design of §5. (App-echo.md:5602 already RULED that `sh_pay_rest` may
be restated "at the application's taint" -- deleting it is the smaller
trusted change: one conjunct fewer, no new text.)

## 2. `uxsup`

Where it is spent: `wp_kshf_fork` takes it (UkShFork.v:672) and spends it in
ONE place, the "affine arm and the taint" branch (:808-864): `uxsup_at_triv N'`
(:831) feeds the GENERIC child `UkShMain.wp_kshm_child_alloc` (:834; its
premise `uxsup_at (ukn_pay N)`), at the trivial payload. `wp_kshm_body` (:895)
and `ushf_rest_of_body` (:1042) only pass it down. The console arm never
touches it (the paid child runs on `ushf_child_law`, :749-).

Which arms reach that branch: the fork arm splits `ush_posb l 3` (UkSh.v:1851:
`(∃ n, ⌜bnd n⌝ ∗ Pm n ∗ ush_wcp l n 3) ∨ (T ∗ ush_pos)`) into the console arm
(`ush_wcp`'s first disjunct) and "the rest" (UkShFork.v:695-707). `ush_wcp l n
3`'s closed arm carries `⌜… ∧ (3 < 3)⌝` (UkSh.v:1571-1575; the guard `p < 3`)
and is refutable by `lia`; so "the rest" is exactly `ush_wcp`'s `∨ True` arm
plus the slot's TAINT arm. After RESIDUALS (C) deletes the `∨ True`, the
branch is the taint arm ALONE, with `T` in hand. So: `uxsup` is needed nowhere
off the taint arm once (C) has landed -- and, conversely, R3 CANNOT close
while `ush_wcp`'s third arm survives (its only remaining producer is the wait
re-entry's not-the-forked-generation arm, UkShFork.v:803-807, which (B)'s
exec-seam rows kill): on that arm there is neither `T` nor a producer of
`uxsup`, so the top can never pay the generic child.

Is `□ (T -∗ uxsup)` derivable at the top? NO CONSTRUCTOR EXISTS. Tree-wide,
`uxsup` has producers nowhere: UkRun.v defines it (:546) and every other hit
is a consumer (`udepw_of_uxsup` :553, `udepw_at_of_uxsup` :644, `uxsup_at_triv`
:656, `udepw_at_ref_of_uxsup` :730, `UkInit.init_exec_sup_of_uxsup` :1601,
the three UkShFork walks). What one would need: at `PS := uprogSG_free`,
`uxsup = □ ∀ W, ∃ f : sfam, ⌜sexit_pay f = (fun _ => True)⌝ ∗ sbundle_at uslot
USYS_exec f W` (UexecSG.v:588-590), and at the kernel's instance the exec
bundle is `exec_sbundle uslot f W = my_pay (uvis_gen W) (kf_xpay f) ∗
sys_exec_au_pre (MkPfam uslot (xf_Rs f)) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
(kf_xpay f) (xf_P f) (xf_Pmiss f) (xf_Fo f) (uvis_M W) a0 a1 (uvis_fd W)`
(UexecExecInst.v:468-474, selected by `xv6_sbundle` :523-525): the kernel's
exec precondition at the key -- the caller's pay fact at the family's payload,
the path-resolution claim (`xf_P`/`xf_Pmiss`) and the NEW image's slot family
`MkPfam uslot (xf_Rs f)`. Under the taint every piece is payable (the new
image's slot from `Hmint` at `R := True`; the path claims from `app_sup`,
which is the taint: `echo_sup_of_taint` AppEcho.v:1217), so a lemma
`UexecExecMint.uxsup_of_sup : app_sup -∗ □ riscv_kill_cred -∗ out_licence -∗
in_licence -∗ □ uexec_wp -∗ uxsup` on `uslot_mint_all`'s mould (:264) is the
shape; its proof needs the generic-family instance of the explicit exec
constructor (`sbundle_pay_exec_intro`, named in UexecExecInst.v:~466's
comment; the pinned twin `sbundle_pay_exec_intro_refR` is what UShEchoPay
imports from UInitSh). Its exact premise list is a Rocq question (§8).

RECOMMENDATION -- do not build it. On the taint arm the body already holds
`T` and (after §3) `ush_gen_slot N T`, so the arm can hand the run to the
generic slot AT 0x92c, exactly as the line fact's taint arm does at 0x97a
(UkShFork.v:1069-1076: `UkSh.ush_gen_run N T h m (mword_of_int 0x97a) …`).
Then `uxsup`, the generic child, the fork panic on the free law and hence
`sh_deps` all leave `wp_kshf_fork`/`wp_kshm_body`/`ushf_rest_of_body`
(the console arm's only `Hdp` use is the pid sub-arm, :741-747, which
RESIDUALS (A) kills). This is strictly less than what RESIDUALS (D) plans for
that arm ("`□ (T -∗ sh_deps)` … the fork's taint arm running the generic
child"); if (D) lands first, the follow-on lane deletes that plumbing in
UkShFork again -- a simplification, not a conflict of design.

## 3. `ush_gen_slot` (and the wb-assembler) into `ush_rest_l`'s box

OLD (UkSh.v:6810-6836, comments stripped):
```
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
          ush_bstate l -∗
          R -∗
          ubytes γd sh_buf sh_nbuf f -∗
          urun N h m (mword_of_int 0x97a) (16 + (ush_Dbody + n)) -∗
          WP (Loop : expr riscv_lang)))%I.
```
NEW (the two per-record facts the discharger cannot get from outside; the
third pure premise is `ush_at_of_pm`, which RESIDUALS (C) deletes -- so it
is REPLACED by the wb-assembler; if R3 lands before (C) it stays as a fourth):
```
  Definition ush_rest_l (R : iProp Σ) : iProp Σ :=
    (□ (∀ (l : list fdstate),
        ⌜ ukn_const N ⌝ -∗
        ⌜ forall i : nat, ⊢ ush_at i -∗ ush_lease i ⌝ -∗
        ⌜ forall i : nat, ush_bnd i -> ⊢ Pm i -∗ Wb i -∗ ush_at i ⌝ -∗
        shk_code γt -∗
        ush_jtab γt -∗
        ush_gen_slot -∗
        ush_loop_head R l -∗
        ∀ (h : CpuId) (m : regfile) (f : nat -> bv 8) (k i2 : nat) (n : nat),
          … (unchanged from OLD) …
          WP (Loop : expr riscv_lang)))%I.
```
Precedent and rule: SH-LINE 2b(b) put `⌜ukn_const N⌝`/`shk_code`/`ush_jtab`
there (UkSh.v:6773-6795: "facts only the entry can produce are premises of
the OBLIGATION"), step 3's D1 added the lease laws the same way. Both new
conjuncts are that kind of fact.

Where `wp_ksh_loop` pays them (UkSh.v:7241-7246, the box opened at :7504):
```
  Local Lemma wp_ksh_loop (R : iProp Σ) (l : list fdstate) :
    sh_deps -∗ ush_tag_law -∗ ush_prompt_law -∗ ush_rest_l R -∗
    shk_code γt -∗ ush_jtab γt -∗ ush_gen_slot -∗ ush_loop_head R l.
  …  iDestruct ("Hrest" $! l with "[%] [%] [%] Hcode Hjt Hgen IH") as "Hbody";
        [ exact Hpay | exact ush_pm_of_at | exact ush_at_of_pm_wb | ].
```
(`ush_at_of_pm_wb` is the section hypothesis at UkSh.v:1790-1792; `Hpay` is
the section's `ukn_const` instance.) `wp_ksh_main` (:7684-7690, calls the
loop at :7847) gains `ush_gen_slot -∗` and passes `Hgen`; `wp_ksh_console`
already holds `#Hgen` (:7907/:7922) and passes it at :8084/:8164; the outer
lemmas (:8187, :8468) and `UShKernel.sh_uexec_slot` (:644-656 hands `Hgen'`)
are unchanged.

What `R` is for sh, and the kill wand: `ush_gen_slot N T` is `Hmint`
specialised at the constant `R := ukn_pay N (-1) = ucons_pay cn γp T (init_rd
Rdl Wb) (-1)` (the console lease pair at this round's position ghost), with
`□ (riscv_kill_cred -∗ R)` paid by `UserConsole.ucons_pay_taint` from the
taint -- ALREADY DONE at UInitSh.v:1198-1205 (`Hgen'`), threaded as
`sh_uexec_slot`'s `□ (∀ W', T -∗ my_pay (uvis_gen W') Q -∗ uslot W')`
premise and re-keyed at :636-637. The kill wand at the top is `Hktaint : ⊢
□ riscv_kill_cred -∗ echo_taint γ` (UInitBoot.v:652-653, off `Hkill`);
`uslot_mint_all` is applied once at :681-691. Nothing new is needed for the
generic slot beyond passing `Hgen` one lemma further in.

## 4. Is a new COMPOSER file still needed?

NO re-walk, NO abstract-continuation refactor of `wp_kshf_fork`. Step 4
already made the fork arm dispatch to the paid child through
`ushf_child_law` (UkShFork.v:277-310, 749-), pinned the cwd (UkSh.v:6622-6633)
and moved the body to slot 3. So `ushf_rest_of_body` IS the composer once:
(i) its taint arm hands off generically (§2; deletes `uxsup` and `sh_deps`),
(ii) the two per-record facts come from the box (§3), and (iii) its
remaining premises -- the three era laws, `Timeless (Wc n p)`, `Wc i 3 -∗ Wc
i 0`, `ush_line_lexable`, the bounds -- are supplied by an ERA-LEVEL GLUE
LEMMA. That glue lemma is the only new thing, and it is small (~60 lines):
`UShRest.sh_rest_holds` (§5). It cannot live in UkShFork (no era) nor in
UInitBoot's own file without importing UShEchoPay's cone into the assembly;
a new leaf `iris/UShRest.v` (bare `_CoqProject` row after `UShEchoPay.v`,
:1538) imported by UInitBoot is the cleanest. (Alternative: append it to
UShEchoPay.v, whose section context is already the right one, :98-108; it
would then be stated at the spelled-out `Wb`.)

## 5. `UShRest.sh_rest_holds`, and the edits that delete the conjunct

```
(* iris/UShRest.v -- the shell's tail obligation at the era's families *)
Require Import … UkSh UkShLoop UkShFork UkShEcho UShLine UShPanic UShEcho
  UShEchoPay UInitSh UShKernel EchoOut EchoLinks EchoLinksLine UexecExecInst UexecExecMint.
Section UShRest.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.       (* UShEchoPay's list, :99-100 *)
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z} `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.

  Lemma ush_line_lexable_holds : UkShLoop.ush_line_lexable.
  (* intros f k len Hl; destruct (UkShEcho.ush_line_toks_holds f k len Hl)
     as (_ & Hns & Htk); split; [exact Hns | exists echo_toks; split;
     [exact Htk | exact echo_toks_lt10]]. *)

  Lemma sh_rest_holds (γp : gname) (N : uk_names Σ) :
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ EchoLinks.echo_links T γ -∗
      udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ v : era_pins, era_pin γ (S gen_id) v) -∗
      UkSh.ush_rest_l (PS := uprogSG_free) N γp T
        (EchoLinksLine.ewc_lcred T γ (S gen_id))
        (fun n : nat => ∃ v : era_pins, era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v n 0%nat)%I
        (UShLine.ush_mid γ γp)
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
End UShRest.
```
Proof shape: `rewrite /UInitSh.sh_Rsh UShKernel.sh_kexec_sz` (the goal's `R`
is then `UkShLoop.ushl_R N 0x5000` up to unfolding); the three era laws as
NAMED hypotheses via `iPoseProof` (never `iIntros "#…"` on the child law --
durable-notes, the bundle-intro hang; UShEchoPay.v:321-323 is the precedent):
`UShEchoPay.ushf_child_law_holds_at T γ Hkt with "Hlk Hdep Hslot"`,
`ushf_kill_law_holds T γ v Hkt with "Hpin"`, `UShPanic.ush_panic_law_holds T
γ with "Hlk"`; `Hwbl := EchoLinksLine.ewc_lcred_blk_line T γ (S gen_id)`; the
bounds by `vm_compute`/`lia` at the literal 20480; then `rewrite
/UkSh.ush_rest_l; iIntros "!>" (l) "%Hc"` to learn `ukn_const N`, and
`iPoseProof (UkShFork.ushf_rest_of_body (Hpay := Hc) (PS := uprogSG_free)
N γp T _ _ _ (fun k H => H) 0x5000 ush_line_lexable_holds … with "Hkl Hchl
Hplaw") as "#Hb"; rewrite /UkSh.ush_rest_l; iSpecialize ("Hb" $! l with
"[%]"); [exact Hc | iExact "Hb"]`. `HWct` resolves from
`EchoLinksLine.ewc_lcred_timeless` (needs `HTT`); pin `(PS :=
uprogSG_free)` on every deposit-bearing term (durable-notes 2026-09-12;
UShEchoPay's 40-minute wedge, step4-sh-report §2.5). If RESIDUALS (D) has
already given `ushf_rest_of_body` a `□ (T -∗ sh_deps)` premise and the
follow-on keeps it, add the same premise here (top: RESIDUALS' row-16
derivation; note `UexecExecMint.udepw_law_of_sup` :192-193 is stated for
15 and 17 ONLY, so row 16 under the taint is (D)'s new lemma, not an
existing one). With §2's hand-off there is no such premise.

UInitSh.v: DELETE `sh_pay_rest` (:524-531; dead once nothing owes it --
`lemma_diff` GONE, justified "discharged, not owed"); `sh_pay_of_parts`
(:564-573) NEW:
```
  Lemma sh_pay_of_parts (T : iProp Σ) `{!Persistent T}
      (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
      (Pm : gname -> nat -> iProp Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    sh_pay_state Rsh n0 -∗
    (∀ (γp : gname) (N : uk_names Σ),
       ush_rest_l (PS := uprogSG_free) N γp T Wc Wb (Pm γp)
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    UkSh.ush_tag_law T -∗ sh_pay T Wc Wb Pm Rsh n0.
```
(the middle premise IS `sh_pay`'s second conjunct, :553-556; proof is
`iSplitR; [iExact "Hst" |]; iSplitR; [iExact "Hre" | iExact "Htg"]`).

UInitBoot.v `echo_Hinit_boot` (:589-621): delete the premise `(⊢
UInitSh.sh_pay_rest UInitSh.sh_Rsh) ->` (:601) and `Hsh_rest` from `intros`
(:648); hoist the links `Hlks` (:764-765, needs only `Hout`/`Hin`) and one
era pin above `Hsh` (the pin is persistent inside `echo_turn`, :970-974
extracts it destructively at the end -- extract it non-destructively early:
`iDestruct "Hturn" as (v0) "(#Hpin0 & Htn & Hx1 & #Hcs0 & #Hps0 & Hx2)"` then
re-seal `Hturn` with `iExists v0; iFrame`); build `UShEcho.sh_echo_slot
(echo_taint γ)` from `Hinv`, `UInitSh.echo_pins_of_fs_pure … Hfs` (:843) and
`Hmint` (three `iSplitR`); at :747 replace `iApply Hsh_rest` by
```
  iIntros (γp N). rewrite /UInitBanner.kinit_ban.
  iApply (UShRest.sh_rest_holds (echo_taint γ) γ γp N Hktaint
            with "Hlks [] Hslot []"); [ iApply udep_free | iExists v0; iExact "Hpin0" ].
```
(`rewrite /UInitBanner.kinit_ban` is the precedent at :879-881 `Hsh_wbr`.)
`Require Import UShRest` beside :112-118.

UInitBootAdequacy.v `Hsh_owed` OLD (:123-140):
```
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh))
```
NEW, if R3 lands before RESIDUALS (D):
```
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         ⊢ UkSh.sh_deps (PS := uprogSG_free))
```
with :243-244 `destruct (Hsh_owed …) as (Hdeps & Hre)` -> `pose proof
(Hsh_owed HR GEN HBs HFd HIr HPav HWc HF) as Hdeps` and :251 `echo_Hinit_boot
HR GEN c r Hdeps Heq …` (drop `Hre`). The hypothesis COUNT is unchanged, so
the audit md5 stays `57f7327206c4b276d05035342fea8ecf`. NEW, if (D) landed
first (first conjunct already gone): the whole `Hsh_owed` binder, the
`destruct`, and both Coq premises of `echo_Hinit_boot` are deleted; the audit
text then changes by the one hypothesis (D) already changed it for -- print
it and explain. Either order ends with NO shell obligation on the top theorem.

## 6. Ordered edit list for the follow-on lane, collisions, and the design risk

PRECONDITION: RESIDUALS (A)+(B)+(C) landed (see §2: while `ush_wcp`'s third
arm has a producer, R3 cannot close, because the True arm reaches the fork
arm with no `T` and `uxsup` has no producer). If (B) STOPS on the seam rows,
R3 is blocked on it -- say so rather than reintroducing an arm.

1. UkSh.v -- `ush_rest_l` NEW (§3); `wp_ksh_loop` gains `ush_gen_slot -∗`,
   pays `ush_at_of_pm_wb` and `Hgen` at :7504; `wp_ksh_main` gains and passes
   it (:7684-7690, :7847); `wp_ksh_console` passes `Hgen` (:8084, :8164).
   COLLIDES with RESIDUALS (C): it deletes `ush_at_of_pm` (:1778), so the
   OLD third pure premise of `ush_rest_l` and the `exact ush_at_of_pm` at
   :7504 are (C)'s to remove; do this step on top of (C)'s text. ~20 lines;
   rebuild cone = every shell/init file above UkSh (~20 files).
2. UkShFork.v -- `wp_kshf_fork` (:638-695): drop `uxsup -∗` and `sh_deps -∗`,
   add `UkSh.ush_gen_slot N T -∗`; replace :808-864 by the taint hand-off
   (`ush_posb l 3`'s remaining arm is `T ∗ ush_pos` after (C); `iApply
   (UkSh.ush_gen_run N T h m (mword_of_int 0x92c) (16 + (80 + n)) Halo with
   "Hgen HT Hrun")`, `Halo` by `vm_compute`). `wp_kshm_body` (:866-906): the
   same three premise changes, pass-through. `ushf_rest_of_body`
   (:1021-1053): drop `sh_deps -∗ uxsup -∗`, drop the Coq premise `(∀ i, bnd
   i -> ⊢ Pm i -∗ Wb i -∗ ush_at N γp i)` and the final `ush_gen_slot N T -∗`;
   take both from the box: `iIntros (l) "%Hc %Hpm1 %Hpmwb #Hcode #Hjt #Hgen
   Hhead"` (:1066) and pass `Hpmwb`/`Hgen` down. `UkShMain.wp_kshm_child_alloc`
   keeps existing (the generic runner) but loses its last caller.
   COLLIDES with RESIDUALS (A) (:741-747 pid sub-arm, `Hdp`), (C)
   (`ush_posb_at`'s shape at :813, `Hpm2` premises) and (D) (if it threads
   `□ (T -∗ sh_deps)` into these three lemmas -- then step 2 removes it
   again). Serialize after RESIDUALS; rebase per checkpoint-2026-09-16 §6.
3. UkShEcho.v (or UShRest.v) -- `ush_line_lexable_holds` (§5), 6 lines.
4. NEW iris/UShRest.v + one bare `_CoqProject` row after `UShEchoPay.v` --
   `sh_rest_holds` (§5). No collision (new file). Watch: `(PS :=
   uprogSG_free)` on both sides of every `iApply`; laws by `iPoseProof`.
5. UInitSh.v -- delete `sh_pay_rest`; `sh_pay_of_parts` NEW (§5). RESIDUALS
   (D) also edits UInitSh (removing forwarded `sh_deps` premises of
   `init_exec_sup_of_sh_slot`/`sh_pay`/`init_sh_slot`): different lines,
   same file -- rebase, no design conflict.
6. UInitBoot.v -- the four edits of §5. RESIDUALS (D) edits the same
   function (`Hdp`'s first conjunct :712, `Hxs`'s `iApply Hsh_deps` :905,
   the premise :600): textual rebase.
7. UInitBootAdequacy.v -- `Hsh_owed` NEW (§5), :243-244, :251. RESIDUALS (D)
   edits the SAME binder (the first conjunct): whichever lands second
   deletes the binder entirely and explains the audit line.
8. Gate (checkpoint-2026-09-16 §6): `lemma_diff` GONE = `UInitSh.sh_pay_rest`
   (+ nothing else; `wp_kshf_fork`/`wp_kshm_body`/`ushf_rest_of_body` keep
   their names); audit md5 unchanged unless the whole `Hsh_owed` goes; no
   Admitted; `--check-dumps` clean; update app-echo.md "SH-LINE R3" and
   README's checkpoint pointer from `-notes`.

DESIGN RISK -- is a surprise still plausible? One, and it is this report's
own finding rather than a proof surprise: the coordinator's R3 ruling
("`sh_pay_rest`'s TEXT UNCHANGED", app-echo.md:3573-3597 and the brief's (3))
is NOT achievable after step 4 -- the era's laws, the timelessness of `Wc`
and the payload-guarded wb-assembler make the `∀ T Wc Wb Pm` form
undischargeable (§1 items 2-4). The design of §5 resolves it in the GOOD
direction (a trusted conjunct deleted, no new trusted text), but it needs
the coordinator's assent because it supersedes the ruling and the old
route (4) (`sh_rest_holds` "with `sh_pay_rest`'s text unchanged"). Everything
else is proof engineering with a precedent in the tree: the boxed
per-record facts (2b(b)/D1), the generic hand-off (`ush_gen_run` at 0x97a
and in the preamble), the `(Hpay := Hc)` re-entry into a `□` (ordinary
proofmode), the pinned instance and the linear intro of law bundles
(step4-sh-report §2.5, durable-notes). Three places to expect a MECHANICAL
stall, none a design one: the `About` of `ushf_rest_of_body` after step 2
(confirm `HWct` is in its closure -- §8), unification of `sh_Rsh …` with
`ushl_R N 0x5000` (unfold both, `rewrite sh_kexec_sz` BEFORE `iPoseProof`),
and `Wb`'s spelling (`kinit_ban` unfolded vs. `ush_panic_law_holds`'s
literal -- keep the lemma's statement at the literal, rewrite at the top).

## 7. Why the old plan's (3) ("a new pinned composer file re-walking 0x97a-0x9c0,
`wp_kshf_fork` with an abstract child continuation") is dead

Step 4 did it inside UkShFork: `wp_kshf_fork_core` (:332-420) takes the
child continuation as a `∀ N' hB mA γ', … -∗ WP` parameter, `wp_kshf_fork`'s
console arm instantiates it with `ushf_child_law` (the paid dispatch), and
the cwd is `ucwd ROOTINO` throughout (:353, :387). What is left of (A) is
one arm (the taint's) and one premise (`uxsup`), both removable in place
(§2). No file above UkShEcho needs to walk an instruction.

## 8. What needs Rocq to settle (one `--no-sync` query each, after a sync of THIS tree only)

1. `About UkShFork.ushf_rest_of_body.` -- confirm the closure lists `HWct`
   after `Hpsok_free` (step4-sh-report §3's line is cut exactly there); the
   proof path (`:795 gen_pay_timeless` via `ushf_wq_timeless :259`) says yes.
2. `Print Assumptions`-free check that `UInitSh.sh_Rsh (ukn_t N) (ukn_d N)
   (ukn_s N)` and `UkShLoop.ushl_R N (kexec_sz ElfUser.sh_elf)` are
   convertible after `unfold` (both are `ushl_dat γd ∗ usz γs …`; the
   `Section`-generalised argument order of `ushl_R` is the only doubt:
   `About UkShLoop.ushl_R`).
3. If anyone still wants `□ (T -∗ uxsup)`: `Print UexecExecInst.sys_exec_au_pre`
   and `About sbundle_pay_exec_intro` for the generic constructor's premises
   (§2) -- not needed under the recommended design.
