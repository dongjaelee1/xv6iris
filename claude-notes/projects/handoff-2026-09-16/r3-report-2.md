# Lane R3 -- report (checkout /shared/xv6iris-2-sup, branch lane/r3)

Base: origin/main `4548e9d3a` (code `d1cc70d8b` = EXEC-SEAM (D)).  Never pushed.
No `claude-notes/` edited.  ONE new file, `iris/UShRest.v`, with ONE bare
`iris/_CoqProject` row after `UShEchoPay.v`.

## 0. Vocabulary (plain concurrent-separation-logic and xv6 terms)

* A RESOURCE is a proposition of Iris's separation logic a process owns; a WAND
  `P -∗ Q` consumes `P` and yields `Q`; a PERSISTENT resource (`□ P`) can be
  copied freely; a LAW is a persistent wand taken as a premise low in the tree
  and proved once at the top of the theorem.
* A WP (weakest precondition) says "from these resources this code runs safely".
  `uslot W` is the kernel's WP for running a user process at KEY `W` -- its
  visible state: image, registers, descriptor table, cwd, generation, children
  set, pid.
* A RECORD `N : uk_names Σ` is the bundle of ghost names a user process is
  stated over; `ukn_pay N : Z -> iProp` is the PAYLOAD it hands its parent at
  exit status `x`.
* The TAINT `T` is the application's persistent fact "the console typing
  discipline has been broken".  Once it holds nothing more is claimed, and the
  process may run arbitrary code on the GENERIC SLOT.  At the echo application
  `T = AppEcho.echo_taint γ`, and the kernel's KILL CREDENTIAL is that same
  proposition.
* The CREDENTIAL FAMILIES: `Wc n p` (the era's write credential at input
  boundary `n` with `p` prompt bytes already out), `Wb n` (the BANNER-OWED
  credential a closed prompt leaves), `Pm n` (the PIECES of the console lease
  the command loop holds mid-line).
* An ERA is one power cycle; `era_pin γ k v` pins the era's ghost record.

## 1. Commits (both on lane/r3, explicit paths, gated, not pushed)

* `56aa37296` -- R3: the shell's tail obligation discharged at the echo era;
  `Hsh_owed` GONE (7 files: UkSh, UkShFork, UInitSh, UInitBoot,
  UInitBootAdequacy, NEW UShRest, _CoqProject).
* `5fb23a304` -- the theorem's own header comment (comment only, own green
  build, because a comment edit invalidates the `.vo`).

## 2. THE TRUSTED CHANGE

### UInitBootAdequacy.Hsh_owed OLD (origin/main 4548e9d3a, verbatim)
```coq
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh))
```
(EXEC-SEAM (D) had already deleted the first conjunct, `⊢ UkSh.sh_deps
(PS := uprogSG_free)`; IO-LEAF M5 the third, sh's console read leaf.)

### UInitBootAdequacy.Hsh_owed NEW
DELETED -- the whole binder, together with `pose proof (Hsh_owed HR GEN HBs HFd
HIr HPav HWc HF) as Hre` and `Hre`'s argument position in `echo_Hinit_boot`.

### `echo_adequacy_modulo_phi`'s binder list AFTER (verbatim)
```coq
  Theorem echo_adequacy_modulo_phi
      (g : gstate) (sb : FsImg.fs_sb) (nib : nat) (cov : gset Z)
      (Hgen0 : g.(ggen) = 0%nat) (Hpow0 : g.(gpow) = false)
      (Himg : fs_boot_image_wf (v_disk (g.(gdev).(dvirtio))) XV6_DISK_BYTES
                sb nib cov)
      (Hdk : fs_blocks (v_disk (g.(gdev).(dvirtio))) = fsimg_P)
      (Hsb : sb = fsimg_sb) (Hcov : cov = fsimg_cov) :
    forall (n : nat) (κs : list mobs) t2 g2,
      language.nsteps n ([PowerLoopE : language.expr riscv_lang], g)
        κs (t2, g2) ->
      (forall e2, e2 ∈ t2 -> language.reducible (Λ := riscv_lang) e2 g2)
      /\ app_phi app_echo g2 κs.
```
Every remaining hypothesis is about the MACHINE STATE the run starts from (the
power-on generation and power flag) and the DISK IMAGE (`Himg`/`Hdk`/`Hsb`/
`Hcov` say the image on the virtio disk is the tracked `mkfs` one).  Nothing
about any program is assumed.

### UInitBoot.echo_Hinit_boot
Loses the Coq premise `(⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh) ->` and the
`Hsh_rest` binder of its `intros`.  Its remaining premises are the six record
equations (`Heq`, `Htag`, `Hkill`, `Hout`, `Hin`, `Hwin`) that the top theorem
hands over -- unchanged.

## 3. `UShRest.sh_rest_holds` -- the new glue lemma (statement verbatim)

Section context = `UInitSh.v`'s binder list verbatim, plus the era:
```coq
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.

  Local Notation Wc := (EchoLinksLine.ewc_lcred T γ (S gen_id)).
  Local Notation Wbn :=
    (fun n : nat => ∃ v : era_pins,
       era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v n 0%nat)%I.
```
```coq
  Lemma sh_rest_holds (γp : gname) (N : uk_names Σ) :
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ EchoLinks.echo_links T γ -∗
      udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ v : era_pins, era_pin γ (S gen_id) v) -∗
      UkSh.ush_rest_l (PS := uprogSG_free) N γp T Wc Wbn
        (UShLine.ush_mid γ γp)
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
```
Proof shape: the three era laws by `iPoseProof` as NAMED hypotheses
(`UShEchoPay.ushf_child_law_holds_at`, `ushf_kill_law_holds`,
`UShPanic.ush_panic_law_holds`, the last pinned `(PS := uprogSG_free)`), the
obligation's box opened (`iIntros "!>" (l) "%Hc"`) so that `ukn_const N` is in
hand, then `UkShFork.ushf_rest_of_body (PS := uprogSG_free) (Hpay := Hc)` at
`sz := kexec_sz ElfUser.sh_elf` and re-specialised at the same `l`.

Two closed side lemmas in the same file (no variables in sight):
`ush_line_lexable_holds : UkShLoop.ush_line_lexable` (a five-line corollary of
E4's `UkShEcho.ush_line_toks_holds` plus `echo_toks_lt10`), and sh's three break
bounds `sh_sz_lo`/`sh_sz_al`/`sh_sz_ok`, each `rewrite UShKernel.sh_kexec_sz`
then arithmetic on the literal `0x5000`.

## 4. `UkSh.ush_rest_l`'s NEW body (verbatim, comments stripped)

```coq
  Definition ush_rest_l (R : iProp Σ) : iProp Σ :=
    (□ (∀ (l : list fdstate),
        ⌜ ukn_const N ⌝ -∗
        ⌜ forall i : nat, ⊢ ush_at i -∗ ush_lease i ⌝ -∗
        ⌜ forall i : nat, ush_bnd i -> ⊢ Pm i -∗ Wb i -∗ ush_at i ⌝ -∗   (* NEW *)
        shk_code γt -∗
        ush_jtab γt -∗
        ush_gen_slot -∗                                                  (* NEW *)
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
Both new rows make the OBLIGATION weaker (easier to discharge) and its
CONSUMER, `wp_ksh_loop`, pay: `ush_at_of_pm_wb` is that section's own
hypothesis, and `ush_gen_slot` is a new premise threaded from
`UShKernel.sh_uexec_slot`'s `Hgen'`, which the top builds from `Hmint`
(`uslot_mint_all` under the taint).  Neither is a placeholder.

## 5. Every deleted name, and where its users went

* `UInitSh.sh_pay_rest` (the ONLY `lemma_diff` GONE) -- the era-free form of the
  obligation.  Its one user was `UInitSh.sh_pay_of_parts`'s middle premise;
  that premise is now `sh_pay`'s own second conjunct spelled inline
  (`∀ γp N, ush_rest_l (PS := uprogSG_free) N γp T Wc Wb (Pm γp) (Rsh …)`), and
  its one supplier is `UShRest.sh_rest_holds`.  Its other user was the Coq
  premise of `UInitBoot.echo_Hinit_boot` and the `Hsh_owed` conjunct -- both
  deleted.
* `UInitBootAdequacy.Hsh_owed` -- a theorem binder, not a declaration, so
  `lemma_diff` does not see it.  Its `destruct`/`pose proof` and `Hre`'s
  argument slot are gone with it.
* NO lemma or definition was renamed: `wp_kshf_fork`, `wp_kshm_body`,
  `ushf_rest_of_body`, `wp_ksh_loop`, `wp_ksh_cmd_head` all keep their names
  and only lose/gain premises.
* `UkShMain.wp_kshm_child_alloc` (the generic child runner) still exists and
  still compiles; after the fork's taint arm went to the generic slot it has NO
  caller.  Kept deliberately (survey §6 step 2).
* `UkRun.uxsup` (the payload-FREE exec supply, "this process may exec any path
  at the trivial payload") is no longer consumed anywhere in the shell line;
  `UkInit.init_exec_sup_of_uxsup` is its last remaining consumer and the
  payload-PINNED `uxsup_at` family is untouched.  This matters: `uxsup` has no
  producer anywhere in the tree, so the old fork taint arm was a place the top
  could never have paid.

## 6. What actually changed in the shell walks

1. **UkSh.v** -- `ush_rest_l` as above; `wp_ksh_loop` and `wp_ksh_cmd_head` gain
   `ush_gen_slot -∗` and pay `ush_at_of_pm_wb`/`Hgen` into the box;
   `wp_ksh_console` (which already held `#Hgen`) passes it at its two calls.
2. **UkShFork.v** -- `wp_kshf_fork`'s TAINT arm (the only credential-less arm
   left after EXEC-SEAM (C)) no longer forks a generic child, walks runcmd and
   prints a fork panic on the free write law.  It hands the whole run to the
   generic slot at 0x92c:
   ```coq
       assert (Halo : is_aligned_vaddr
                        (Virtaddr (mword_of_int 0x92c : mword 64)) 2 = true)
         by (vm_compute; reflexivity).
       iApply (UkSh.ush_gen_run N T h m (mword_of_int 0x92c) (16 + (80 + n))
                 Halo with "Hgen HT Hrun").
   ```
   -- exactly the move the line fact's taint arm already makes at 0x97a.  With
   it, `□ (T -∗ UkSh.sh_deps)` and `uxsup` leave the premise lists of
   `wp_kshf_fork`, `wp_kshm_body` and `ushf_rest_of_body`, replaced by
   `UkSh.ush_gen_slot N T`.  `ushf_rest_of_body` additionally drops its Coq
   premise `(∀ i, ush_bnd i -> ⊢ Pm i -∗ Wb i -∗ ush_at N γp i)` and its
   `ush_gen_slot` premise, taking both out of the box instead.
3. **iris/UShRest.v** -- new, §3.
4. **UInitSh.v** -- `sh_pay_rest` deleted, `sh_pay_of_parts` restated.
5. **UInitBoot.v** -- premise deleted; the era pin read off `echo_turn`
   non-destructively and the turn re-sealed (`#Hpine`); the era's links
   (`Hlks`/`Hlkc`) hoisted above the shell's slot; `UShEcho.sh_echo_slot
   (echo_taint γ)` built by `sh_echo_slot_of_fs_pure_holds` from `Hinv`, `Hfs`
   and `Hmint`; `iApply Hsh_rest` replaced by
   ```coq
         iIntros (γp N). rewrite /UInitBanner.kinit_ban.
         iApply (UShRest.sh_rest_holds (echo_taint γ) γ γp N Hktaint
                   with "Hlks [] Hslot Hpine").
         iApply (udep_free).
   ```
6. **UInitBootAdequacy.v** -- §2.

## 7. The audit, in full, and every line

VM `make audit-only`, `grep -v '^make\|^cd '`, md5
`57f7327206c4b276d05035342fea8ecf` -- **UNCHANGED** from before EXEC-SEAM (D)
and from before this lane.

```
Axioms:
PrimInt63.sub : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimString.string : Set
xv6iris_extras.resv_matches : forall n : BinNums.Z, Values.mword n -> bool
xv6iris_extras.resv_is_valid : bool
PrimInt63.lsr : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lsl : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lor : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.land : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.int : Set
PrimString.get : PrimString.string -> PrimInt63.int -> PrimString.char63
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
PrimInt63.eqb : PrimInt63.int -> PrimInt63.int -> bool
PrimString.cat : PrimString.string -> PrimString.string -> PrimString.string
```

Line by line, against the same thirteen as the previous builds:

* `PrimInt63.int`, `.eqb`, `.sub`, `.lsl`, `.lsr`, `.land`, `.lor` (7) and
  `PrimString.string`, `.get`, `.cat` (3) -- Rocq PRIMITIVES, not axioms.  The
  theorem's statement names the mkfs disk image as a `PrimString`-backed
  literal; a primitive has no body, so `Print Assumptions`'s traversal lists it
  the way it lists an axiom.
* `xv6iris_extras.resv_matches`, `resv_is_valid` (2) -- the Sail model's LR/SC
  reservation hooks, left ARBITRARY BUT FIXED.  They are in the STATEMENT (the
  machine model), not the proof.
* `FunctionalExtensionality.functional_extensionality_dep` (1) -- the only thing
  from the PROOF.

Total thirteen; nothing added, nothing removed.

**Why the audit did NOT move although a hypothesis vanished.**  `Print
Assumptions` sees AXIOMS, never a theorem's own premises.  `Hsh_owed` was a
premise of `echo_adequacy_modulo_phi`, so it was invisible to the audit before
this lane and is invisible after; and the audit is run on
`SystemAdequacy.xv6_fs_adequacy_xv6Σ`, which is a different theorem entirely.
The trusted change here is REAL and is exactly "one hypothesis fewer on the
echo theorem", visible in §2's binder list -- the md5 is simply not the
instrument that measures it.  (EXEC-SEAM (D) recorded the same finding for the
first conjunct.)

## 8. Gate lines

* Build `r3-3`: `COMPILED=28 EXIT=0`; `grep -c '^Error' /tmp/r3-3.log` -> `0`.
  Confirming build `r3-4` after the comment-only commit: `COMPILED=1 EXIT=0`,
  `^Error` -> `0`.
* VM `make -f CoqMakefile -n | grep -c 'ROCQ compile'` -> `0` (both times).
* md5 of the changed files, local == VM
  (`00f2b9be30ae0b8fa7054793040a7fdc` over the six + `_CoqProject` at r3-3;
  `90ca3d4a7d1c377fbc2e3bec100b7d6d` for `UInitBootAdequacy.v` at r3-4).
* `make audit-only` md5 `57f7327206c4b276d05035342fea8ecf` -- unchanged, §7.
* `python3 tools/lemma_diff.py --ref origin/main` -> `6 file(s) checked --
  1 thing(s) to justify`: `iris/UInitSh.v  GONE  Definition sh_pay_rest`.
  Justified: DISCHARGED, not owed (§5).  No NEWAXIOM, no `Admitted`/`admit`/
  `Abort`.
* `./gcp-rocq/run-on-gcp --check-dumps` -> "the VM's tracked dumps match this
  checkout".
* `grep -c '∨ True'` over every file this lane touched -> `0` everywhere.

Build logs stay on the VM at `/tmp/r3-1.log` .. `/tmp/r3-4.log`; the `.out`
files are in this scratchpad.

## 9. What the survey (r3-survey-2.md) got wrong or stale

1. **§3/§6(1): the old third pure premise was already gone.**  The survey
   expected `ush_rest_l`'s `⌜∀ i, ush_bnd i -> ⊢ Pm i -∗ ush_at i⌝`
   (`ush_at_of_pm`) to be REPLACED by the wb-assembler.  EXEC-SEAM (C) had
   already deleted it, so the wb-assembler is an ADDED row (in the same, third,
   position) rather than a replacement.  Net effect on the box is what the
   survey intended.
2. **§3/§6(1): the lemma names moved.**  What the survey calls `wp_ksh_main`
   (":7684-7690, calls the loop at :7847") is `wp_ksh_cmd_head` in the tree;
   the real `wp_ksh_main` is the outer entry and ALREADY carried
   `ush_gen_slot`, as did `wp_ksh_console`.  So only two lemmas gained the
   premise, not three.
3. **§1/§6(2): the free write law had already become conditional.**  The three
   fork lemmas took `□ (T -∗ UkSh.sh_deps)`, not a bare `UkSh.sh_deps`
   (EXEC-SEAM (D)).  Deleted either way; §5's "if (D) lands first, add the same
   premise here" did NOT apply, exactly as §2 predicted.
4. **§5: `udep`'s instance pin is load-bearing and non-obvious.**  The survey
   writes `udep (PS := uprogSG_free)`; dropping it (my first attempt) makes the
   bare `udep` resolve at the AMBIENT generic instance `uprogSG_gen`, and the
   failure is `iSpecialize: cannot instantiate (udep -∗ …) with udep` -- two
   propositions that print identically.  The survey was right; flagging it
   because it is the single place where the printed goal is useless.
5. **§5: no `rewrite sh_kexec_sz` is needed in the goal.**  `UInitSh.sh_Rsh
   (ukn_t N) (ukn_d N) (ukn_s N)` and `UkShLoop.ushl_R N (kexec_sz sh_elf)` are
   CONVERTIBLE (both unfold to `ushl_dat (ukn_d N) ∗ usz (ukn_s N) (kexec_sz
   sh_elf)`), so applying the discharger at `sz := kexec_sz ElfUser.sh_elf` and
   closing with `iExact` crosses it.  `sh_kexec_sz` is needed only inside the
   three closed bound lemmas.  (§8 query 2 answered.)
6. **§5: the pin's name collides.**  `echo_Hinit_boot` already binds `#Hpin0`
   later on; the early extraction must use a different name (`#Hpine` here) or
   the proof dies with `iIntuitionistic: "Hpin0" not fresh`.
7. **§5: `sh_echo_slot` is one `iApply`, not a hand assembly.**
   `UShEcho.sh_echo_slot_of_fs_pure_holds` already does the projection from
   `echo_fs_pure` to `era0_echo_pins`, so the build is
   `iApply sh_echo_slot_of_fs_pure_holds` plus the three `iSplitR`s over
   `Hinv`/`Hfs`/`Hmint`.
8. **§8 query 1, answered: YES.**  `About UkShFork.ushf_rest_of_body` lists
   `{HWct}%function_scope` immediately after `Hpsok_free`, as the survey
   predicted; it is resolved here by `EchoLinksLine.ewc_lcred_timeless`, which
   is why the section needs `Timeless T`.
9. **§8 query 3 not needed** -- no `□ (T -∗ uxsup)` was built, per §2's
   recommendation.
10. **The DESIGN RISK §6 flagged is confirmed and resolved in the good
    direction.**  The coordinator's earlier ruling ("`sh_pay_rest`'s TEXT
    UNCHANGED, restated at the application's taint") is not achievable: the
    era's laws, `Timeless (Wc n p)` and the payload-guarded wb-assembler make
    any `∀ T Wc Wb Pm` form undischargeable.  Deleting the definition and the
    conjunct is strictly smaller as a trusted change -- one hypothesis fewer,
    no new trusted text.  Nothing else in §5/§6 needed a design change.

## 10. Where a successor picks up

Both commits are green and on `lane/r3`; the working tree is clean.  The echo
theorem now assumes NOTHING about any user program.  What is still open on the
app-echo lane list is unchanged by this lane: M6b (init's restart loop) and
M4b(2) (the diagnostics' payment) are about the TRACE the theorem admits, not
about its hypotheses; then the final trusted-surface document and the post-Qed
redesign.  `claude-notes/projects/app-echo.md`'s "SH-LINE R3" entry and the
README checkpoint pointer are owed from the `-notes` checkout (this lane must
not edit notes).
