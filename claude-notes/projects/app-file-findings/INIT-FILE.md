# INIT-FILE (2026-09-17) — /init's BOOT PAYMENT AT THE FILE RECORD LANDS AS FAR AS THE BANNER; `file_prog_law` IS **STOPPED** ON THREE NAMED THINGS, AND THE DEEPEST IS THAT THE DEED CANNOT BE TIED TO THE FILED BOOT STATE

Branch `app-file/program-tier`, worktree `/shared/xv6iris-3-lanes/program-tier`,
merged from `main` at `d8ffd312c` (clean; no conflicts).

**METRIC.** `grep -c "Hypothesis\|Admitted" iris/UInitFile.v`: **3 → 1**.
The three were two stale header lines and the `Admitted.` of
`file_Hinit_boot`; the header is now a description of what IS proved and
of the three blockers, and the one remaining hit is that `Admitted.`
itself, which this lane could not remove.  Why not is the whole of §3
below, and none of the three reasons is prose that a proof effort would
have dissolved: two are missing RESOURCES and one is a missing
GENERALISATION whose last conjunct is a design change.

## 1. What landed, with file:lemma

Two new files, both outside every audit cone (nothing imports them), plus
two rows of `iris/_CoqProject` and `iris/UInitFile.v`'s header.

### `iris/AppFileCons.v` — the file CLAIM's console readings

`AppEcho`'s console laws at `AppFile.file_pred`, each one application of
`AppFile.file_pred_cons` over the echo lemma.  These are exactly the
conjuncts of `UInitCons.init_cons_laws_at` whose VIEW DOES NOT MOVE, so
the accessor closes at the same `av` and the file conjunct is framed.
`FileOpen.file_cons_law` was the first of them; these are the other five.

- `file_fs_pure_acc` — `AppEcho.echo_fs_pure_acc`'s twin, and it needs no
  accessor at all: `file_pred` IS the taint or the pure half beside its
  two state conjuncts, so the reading is a destructuring.
- `file_echo_fs_pure_acc` — the same at `EchoFsPure.echo_fs_pure`, through
  `FileFsPure.file_fs_pure_echo`.  This is the one line that lets the file
  era feed `UInitSh.init_sh_slot_core` and
  `UShEcho.sh_echo_slot_of_fs_pure`, both of which are stated at
  `echo_fs_pure` as a CONSTANT and neither of which therefore needs
  generalising (`FileFsPure.v`'s header already said so; this lane is the
  first consumer).
- `file_cons_abs_law` — `AppEcho.echo_cons_abs_law`.
- `file_cons_never_law` — `AppEcho.echo_cons_never_law`.
- `file_cons_seal_step` — `AppEcho.echo_cons_seal_step`.
- `file_cons_shoot` — `AppEcho.echo_cons_shoot`.

...AND THE TWO MOVING-VIEW LEGS THAT DO GO THROUGH.  Here `file_pred_cons`
is useless — it closes only at the same `av` — so:

- `file_cons_arm` — `init_cons_laws_at`'s (d), by `AppFile.file_step_free`
  at four landed `FileDeltas` legs (`file_fs_pure_arm`,
  `cons_absent_arm_nd`, `cons_present_arm_nd`, `f_ok_arm`).
- `file_cons_mknod` — `init_cons_laws_at`'s (f), the console's OWN create:
  `AppFile.file_pred_split` → `AppEcho.echo_cons_mknod` on the echo half →
  `file_pred_join`, with the file residue carried across by
  `FileDeltas.file_fs_pure_create` and `AppFile.f_state_mono` at
  `FileDeltas.f_ok_create_other` (whose `d <> ROOTINO \/ nmn <> fname_f`
  is `FileDeltas.fname_console_ne_f`).

So SEVEN of `init_cons_laws_at`'s NINE conjuncts are discharged at the file
claim by this file; the two that are not are §3.4.

It sits above `AppFile`/`AppEcho` and below the whole open cone, on
purpose: a consumer of a console law should not have to take
`FileOpen.v`.

### `iris/UInitFileCons.v` — /init's boot payment

`UInitBoot.echo_Hinit_boot`'s assembly one application over, as far as it
goes.  It is a file of its own for `UInitBoot.v`'s measured reason:
`UInitFile.v` carries the ADEQUACY cone (it names
`UFileBootAdequacy.file_prog_law`, hence `SystemAdequacy`), and mixing
that with a proofmode-heavy u-tier assembly is what made echo's blow up
at 54 GB.  The split is `UInitBoot.v` / `UInitBootAdequacy.v`'s, with
`UInitFile.v` playing the second role.

The record equations are PARAMETERS (`FileLinks.v` and `UShRound.v`'s
shape), because the file may not name `AppFileRec.app_file` without
pulling the adequacy cone in.  Each is a `cbn` on `AppFileRec.file_ifc`'s
record literal at the caller.

- `disc_f_no_ctrl_d` — **lane SKELETON's obligation 21, closed on the file
  side.**  `UkSh.disc_no_ctrl_d`'s twin at `FileDisc.disc_f`: a
  file-disciplined history never ends in a byte that translates to 0x04.
  LINK-GEN-4 made `UkSh.ush_tag_law_at` take the discipline as a
  parameter `D`; `ush_tag_law_of_at` then asks the era for exactly this
  refutation, and it is `FileOutPure.disc_seg_f_no_ctrl_d` under
  `FileDisc.disc_f_seg` with echo's first step (0x04 is not a carriage
  return, so `ConsoleInv.cons_xlate` is the identity on it) copied
  verbatim.
- `file_tag_law_at` / `file_tag_law_holds` — `UInitBoot`'s `Htg` one
  application over: `⊢ UkSh.ush_tag_law (file_taint (fgn_cl g))` off the
  interface equation `riscv_rx_tag = FileOut.ftag g`.
- `file_f0pre_of_typed` — **lane STAGE's "the one thing", discharged.**
  `AppFile.file_boot`'s second conjunct `(f_typed c s ∨ file_taint c)` IS
  `FileLinksLine.f0pre g`, at `s0 := AppFile.dst_content s`: the typed
  witness transports because `f_typed c (Some (i,bs))` and
  `FileOut.f0_typed g (Some bs)` are the same proposition, and the purity
  side condition `FileDisc.fst_ok` comes off
  `FileDisc.fcont_ok_subseq` inside `f_bytes_typed`.
- `file_turn_pre_of_boot` — and therefore `lk_turn (file_link_inst g)
  (S gen_id)` = `FileLinksLine.fturn_pre g (S gen_id)` is
  `FileOut.fturn` BESIDE that witness.  This is where `app_boot` and
  `app_turn` meet, and it is the only place they do.  The `▷` is the
  caller's to strip (everything under it is timeless and
  `file_prog_law`'s conclusion is a `|==>`), so the lemma takes the
  stripped disjunction.
- `file_kinit_ban0` / `file_kinit_ban_law` — the banner at
  `UInitBanner`'s GENERIC lemmas at `FileLinkInst.file_link_inst`.  An
  instantiation, not a twin: `Section UInitBannerGen` is stated at
  `LinkRec` and the file instance is total.  `file_kinit_ban_law` takes
  only the console record equation, through `FileLinks.file_links_holds`.
- `file_sup_of_taint_at` / `file_taint_of_sup_at` — the two readings of
  the supply at the CLAIM equation (`AppFile.file_sup_of_taint` /
  `file_taint_of_sup`).
- `file_fs_pure_law` / `file_era0_pins_law` — the claim's pure half as a
  `□` law at `AppCfg.app_pred AppCfg.app_run`, and `FsInitPinBoot.era0_pins`
  projected out of it (`FileFsPure.file_fs_pure_echo` then `proj1`).  This
  is `PinnedExec`'s bundle premise.
- `file_init_deps_of_laws` / `file_init_deps` — /init's three deposits at
  the file taint, at `UexecExecInst.uprogSG_free`.
  `UInitBoot.init_deps_of_laws` re-proved rather than imported (six lines
  of plumbing against the whole ECHO program tier in the cone).
- `file_gen_mint` — the taint's generic slot (`UInitBoot`'s `Hmint`).
- `file_hold_head_of_boot` / `file_ban_f0w` — obligation 22's two halves;
  see §3.1.

## 2. Two things that turned out NOT to be obligations

- **`UInitKernel.init_boot_pay` needs no change for the deed** (lane
  SKELETON's obligation 22 asked for one).  It is abstract in the
  credential record, and `UShRound`'s own ruling puts the deed INSIDE the
  credential family (`Wcf I p := Wcl I p ∗ sh_hold I`).  So the deed rides
  the bundle's one linear slot as part of `cc_wbn Cr 0` — the round-0
  banner-owed credential /init holds from its entry — with no new slot and
  no edit to `UInitKernel.v`.  What obligation 22 actually costs is §3.1.
- **`UInitSh.init_sh_slot_core` and `UShEcho.sh_echo_slot_of_fs_pure` do
  not need the pure predicate parameterised.**  Both name
  `EchoFsPure.echo_fs_pure` as a constant, and the file era feeds them by
  weakening (`AppFileCons.file_echo_fs_pure_acc`), not by generalising.
  `UInitSh.init_exec_sup_of_sh_slot`, `init_sh_slot`, `sh_pay_of_parts`,
  `sh_pay_state_holds`, `UInitKernel.init_boot_con`,
  `init_cons_dance_all_{miss,hit}`, `UInitCons.init_cons_cred{,_of_*}`,
  `init_cons_fd{,_ne}` and `UShConsK.sh_open_{console,absent}_leaf_holds`
  are all already abstract enough; `UInitCons.init_cons_laws_at` is too.
  **`AppFile.file_taint c` IS `AppEcho.echo_taint c.1` definitionally and
  `AppFile.fn_cons r : echo_names`**, so the whole console dance runs at
  `T := file_taint c`, `K := cons_key (fn_cons r)`,
  `Made := cons_made (fn_cons r)` with no new credential type anywhere.

## 3. What is **STOPPED**, exactly

### 3.1 The deed cannot be tied to the era's FILED boot state — and this is the lane's own

`iris/FileLinksLine.v:1224`

```coq
Definition f0pre : iProp Σ :=
  (∃ s : fst, ⌜fst_ok s⌝ ∗ (f0_typed g s ∨ FT))%I.
```

`f0pre` is EXISTENTIAL in the state it offers, and it is what
`FileLinksLine.fhead` (`:1227`) and hence `fwc_ban`'s head arm (`:1272`)
and hence `fturn_pre` (`:1958`) carry.  `FileLinksLine.fban_step`
(`:1566`) fires `FileLinks.file_write_link_first` on the era's first
banner byte at THAT witness and produces `FileOut.f0_lb vf s0` for it —
inside `fwc_ban`'s first arm, under a fresh existential.

So /init, which put `AppFile.dst_content s_deed` into `f0pre` (that is
`file_f0pre_of_typed`), gets back a lower bound at SOME `s0` and has no
way to say it is the deed's content.  `UShRound.sh_hold`'s entire content
is `UCatOut.cat_tie cs0 s0 I s`, i.e. `dst_content s = cat_st cs0 s0 I`,
which at `I = []` is exactly `dst_content s = s0`.  Without the tie sh's
round can never establish it, and CAT-ENTRY's ruling (b) — sh reads its
deed before it prints — has nothing to read.

**THE REPAIR, named.**  Index the head by the state:

```coq
Definition f0pre_at (s0 : fst) : iProp Σ := (⌜fst_ok s0⌝ ∗ (f0_typed g s0 ∨ FT))%I.
Definition f0pre : iProp Σ := (∃ s0 : fst, f0pre_at s0)%I.
```

and carry the index through `fhead`, `fwc_ban`'s head arm and
`fturn_pre`, so that `fban_step`'s head branch can export
`f0w k s0` at the CALLER's `s0` (it already computes it —
`fecl_step_write_first` returns `f0_lb vf s0` at the named `s0`, and
`fban_step` only loses the name when it packs the result).  It is
`FileLinksLine.v` + `FileLinkInst.v` + `LinkRec`'s `lk_turn`/`lk_ban`
fields, i.e. a LINK-GEN-shaped lane, and nothing above the record moves:
`UInitBanner` never looks inside `lk_ban`.

**WHAT IS ALREADY THERE, so the repair is smaller than it looks.**
`UInitFileCons.file_ban_f0w` proves the half that does not need the
index: after the first byte the head arm of `fwc_ban` is refuted by its
own index, so what is left carries `f0w` (persistent) or the taint.  Only
the NAME is missing.

### 3.2 `UShRound.sh_hold []` is not inhabited at /init's entry — lane SH-ROUND's

`iris/UShRound.v:163`

```coq
  Definition sh_hold (I : list (bv 8)) : iProp Σ :=
    ((∃ (cs0 : list nat) (s0 : fst) (s : dst) (v : era_pins) (vf : file_era),
        fown r s ∗ ⌜UCatOut.cat_tie cs0 s0 I s⌝ ∗ f_typed (fgn_cl g) s
        ∗ era_pin (fgn_echo g) (S gen_id) v ∗ cs_lb v cs0
        ∗ file_era_pin g (S gen_id) vf ∗ f0_lb vf s0)
     ∨ T)%I.
```

`UInitKernel.init_boot_pay` (`:679`) asks /init for `cc_wbn Cr 0`, and at
the file era `cc_wb Cr` is forced to be `UShRound.Wbf` (it is what
`UInitSh.sh_pay`'s second conjunct passes to `UkSh.ush_rest_l`, and
`sh_round_holds_file` concludes at it).  So /init must produce
`Wbl [] ∗ sh_hold []` at its FIRST INSTRUCTION.  Every conjunct is in hand
there (`fturn` gives the pin, `cs_lb v []` and the era pin; `file_boot`
gives the deed and `f_typed`; `cat_tie [] s0 [] s` is `dst_content s = s0`
because `cat_st cs0 s0 [] = fst_upto cs0 s0 [] 0 = s0`) — every conjunct
but `f0_lb vf s0`, which **cannot exist**: it is a lower bound of
`f0_auth vf (opt_list (fo_f0 so))`, the stage's `fo_f0` is `None` until a
byte is written (`FileOut.fecl`'s `feout_pure` clause is an IFF), and the
only producer in the tree is `FileLinks.file_write_link_first`, fired by
the banner's first byte — strictly later.  The right disjunct is the
taint, which /init does not have and must not have (ADEQUACY's ruling:
a boot-time taint gutted the conclusion).

**THE REPAIR, named.**  `sh_hold` gains an ERA-HEAD arm:

```coq
     ∨ (⌜I = []⌝ ∗ ∃ s : dst, fown r s ∗ f_typed (fgn_cl g) s)
```

which is `UInitFileCons.file_hold_head` and is what
`file_hold_head_of_boot` produces from `AppFile.file_boot`.  It is
refuted by `I <> []` at every consumer below /init's banner, and it is
converted into the filed arm exactly once — at the banner, by §3.1's
export.  sh never sees it, because /init prints its eighteen bytes before
it forks.

### 3.3 `UInitSh.cons_cred_holds` at the file families — lane LINK-GEN's, nine items and one design change

The STATEMENT twins for free (`UserConsole.cons_cred` is fully abstract,
`UInitSh.cons_cred_holds` names no era).  The DISCHARGES do not.  The file
families are `Wcf I p := Wcl I p ∗ sh_hold I` and `Wbf I := Wbl I ∗ sh_hold I`,
i.e. the echo-shaped credential with one extra LINEAR conjunct, and only
`UShRest.sh_rest_holds_at` (`iris/UShRest.v:199`) carries such a frame
today (its `Hold` parameter is literally this).  Measured, lemma by lemma:

**Generic form exists AND carries a frame — nothing owed**

- `UShRest.sh_rest_holds_at` (`UShRest.v:199`) — its `Wc`/`Wb` ARE
  `Wcf`/`Wbf` modulo `Hold := sh_hold`.  Leans on
  `UShEchoPay.ushf_child_law_hold_at` (`:375`),
  `UShPanic.ush_panic_law_hold_at` (`:741`),
  `UShEchoPay.ush_execfail_law_wq_hold_at` (`:416`).  **Caveat:** it takes
  `St : StageRec L` and there is no file instance (only
  `StageRec.echo_stage_inst`, `StageRec.v:381`).

**Generic form exists, frame missing (each a `Hold` twin)**

| conjunct | generic form | what the frame costs |
|---|---|---|
| read leaf | `UShLine.ush_read_recv_leaf_holds_at` (`UShLine.v:1243`), instantiated as `FileReadInst.file_read_leaf_holds` (`:378`) | no frame needed (no `Wc`/`Wb`); but the conjunct is at echo's `disc_input` while the file's is `rk_disc FI file_read_inst = FileDisc.disc_input_f`, and `UInitSh.init_exec_sup_of_sh_slot` **hard-codes** `EchoDisc.disc_input` and four readings of it at `UInitSh.v:1143-1146`.  A `Dsc` parameter is owed there. |
| loop's step at the read | `UShLine.ush_mid_wc_read_t_at` (`:664`) | the deed must MOVE `I -> I ++ l ++ [wl_nl]`, so the twin needs a premise `Hold I -∗ Hold (I ++ l ++ [wl_nl])`, not a frame |
| read past a banner-owed credential | `UShLine.ush_wb_read_holds_at` (`:710`) | trivial drop (`iIntros "[Hb _]"`) |
| banner-owed ⇒ boundary | `LinkRec.lk_lcred_of_ban` (`:425`), file: `FileLinkInst.file_Hwbwc` | trivial framing (already done ad hoc at `UShRest.v:222`) |
| block-owed ⇒ boundary | `LinkRec.lk_lcred_blk_line` (`:441`), file: `FileLinkInst.file_Hwbl` | trivial framing |
| the prompt law | `UShPanic.sh_prompt_law_holds_line_at` (`:638`) | **no `Hold` form**, and it may not be a frame: `UShRound.sh_prompt_alt_of_deed` (`:240`) says the prompt byte's alternative is DECIDED by the deed.  `UShPanic` has the pattern (`ksh_w1_hold` `:718`, `ksh_w_mono_in` `:696`, `ksh_w_thread` `:706`) and this one law was left without it. |

**No generic form at all (echo-only, in `UShLine.v`)**

`ush_mid_of_at` (`:562`), `ush_at_of_mid_taint` (`:592`),
`ush_at_of_mid_wb` (`:603`), `ush_wc_inp` (`:468`) / `ush_wb_inp` (`:474`)
and their discharges `ush_wc_inp_lcred` (`:486`) / `ush_wb_inp_ban`
(`:541`), and `ush_posb_of_lend` (`:751`).  All are stated at echo's
concrete residue `rd_res` / `ush_rd_x γ` / `ush_mid γ`; the record forms
would replace those by `lk_rres L` / `lk_T L`.  **`ush_wc_inp_lcred` /
`ush_wb_inp_ban` are the load-bearing pair**: `ush_posb_of_lend`'s two
side conditions are `ush_wc_inp γ T Wcf` and `ush_wb_inp γ T Wbf`, and
neither discharge admits a linear conjunct.

**`UInitDiag.v` is echo-only end to end and needs a record field.**
`kinit_pro` (`:250`), `kinit_own_of_pro` (`:269`),
`kinit_banner_law_pro_holds` (`:281`), `kinit_execfail_law_holds`
(`:325`), `kinit_forkfail_law_holds` (`:357`) — the file imports no
`LinkRec` at all.  The blocker is structural: `LinkRec` has `lk_pro` and
`lk_line_of_pro`/`lk_ban_pro`, but **no `pdiag` field** — the
per-alternative prologue diagnostic family `EchoLinksPro.ewc_pdiag` (used
through the local `pdg`, `UInitDiag.v:152`) is not on the record.
`UInitBanner`'s generic half is what the twin would look like;
`UInitDiag` was left behind.  It matters here and not only at sh:
`UInitBoot.echo_cc` uses `UInitDiag.kinit_pro` as `cc_wp`
(`UInitBoot.v:567`), so `cons_cred_holds`'s TENTH conjunct and the whole
`kinit_ban` ↔ `cc_wbn` round trip (`Hbto`/`Hbfr`, `UInitBoot.v:1063-1080`)
inherit it.

**And one DESIGN change, not a generalisation.**
`UInitCons.init_cons_laws_at`'s UNARM conjunct (the fifth) is

```coq
  □ (∀ av0 av i, ⌜av0 !! i = None⌝ -∗ ⌜Pure av0⌝ -∗ ⌜Pv av0⌝ -∗ ⌜Pv av⌝ -∗
       app_pred app_run av -∗ app_pred app_run (delta_unarm i av))
```

and it **cannot be discharged at the file claim as stated**.
`AppFile.file_step_free`'s fourth premise is
`forall s, f_ok av s -> f_ok (delta_unarm i av) s`, and the two legs that
exist are `FileDeltas.f_ok_unarm_fresh` (`:564`, needs `f_ok av0 s`) and
`f_ok_unarm` (`:541`, needs `i <> ROOTINO` and `i` not `s`'s inum).
Neither fact is among the conjunct's pure premises and the claim cannot be
opened at `av0` inside the wand.  `FileOpen.file_unarm_commit` (`:441`,
esp. `:481`) discharges exactly this obligation elsewhere — by carrying an
`FileOpen.fclaim_facts` RECEIPT from `av0` — so the fix is to give the
conjunct that receipt (an extra `Pv0`/receipt parameter), which moves
echo's own discharge too.  Separately, the conjunct hands `⌜Pure av0⌝` =
`⌜echo_fs_pure av0⌝` while `FileDeltas.file_fs_pure_unarm_fresh` (`:780`)
needs `file_fs_pure av0`, so `Pure` has to be instantiated at
`file_fs_pure` — which then forces generalising the `UInitConsK` lemmas
that hard-wire `echo_fs_pure` (`init_cons_sup_console` `:363`,
`init_cons_mknod_fam` `:385`, `init_cons_sup_mknod` `:390`,
`init_open_console_leaf_holds` `:556`, `init_mknod_leaf_holds` `:701`).

(The ARM and MKNOD conjuncts ARE fine and are landed —
`AppFileCons.file_cons_arm` / `file_cons_mknod` — so this conjunct and
§3.4's are the only two of the nine left.)

### 3.4 `init_cons_laws_at`'s CREATE-AT-ANOTHER-NAME conjunct is FALSE at the file claim as stated

`iris/UInitCons.v:1036`

```coq
     ∗ □ (∀ (av : aview) (d : Z) (nmn : fname) (ents : gmap fname Z)
            (nl : nat) (i : Z),
            ⌜cre_pre av d nmn ents nl i (ADev CONSOLE 0)⌝ -∗
            ⌜d <> FsImg.ROOTINO \/ nmn <> fname_console⌝ -∗
            app_pred app_run av -∗
            app_pred app_run (delta_create d nmn i (ADev CONSOLE 0) av))
```

Take `d = FsImg.ROOTINO`, `nmn = fname_f` (which the side condition
permits, since `fname_f <> fname_console`) and a deed at `None`.  The
claim's file half then says `AppFile.f_absent av`, i.e.
`astep av ROOTINO fname_f = None`; after the create it is `Some i`.  So the
conjunct asks /init's mknod walk to be allowed to create a DEVICE called
`f` in the root, which the file application's claim cannot absorb.

It is NOT the same failure as §3.3's UNARM: there the premise set is too
weak to reach a landed leg, here the statement is genuinely too strong.
`FileDeltas.f_ok_create_other` (`:573`) carries the right side condition
(`d <> ROOTINO \/ nmn <> fname_f`) and `FileDeltas.node_pin_create`
(`:279`) needs none at all — `cre_pre`'s own freshness clause kills the
`nmn` case for a PRESENT deed.  Only the ABSENT-deed branch
(`name_absent_create`) needs it, and that is exactly the branch era 0 is
in.

**THE REPAIR, named.**  Conjunct (g)'s side condition becomes
`⌜d <> FsImg.ROOTINO \/ (nmn <> fname_console /\ nmn <> fname_f)⌝` (or, for
an era-generic spelling, a parameter `Other : Z -> fname -> Prop` beside
`Pure`/`Made`/`Pv`).  Echo's discharge `AppEcho.echo_cons_create_other`
ignores the extra conjunct, so `UInitCons.init_cons_laws_echo` and
`init_cons_laws_made_echo` do not move; the CONSUMER
(`UInitConsK.init_cons_sup_mknod`, `:390`) must supply it, and it can —
the name it creates is the last element of the literal path `console`.

## 4. What SH-ROUND owes, after this lane

Unchanged except for one thing, and it is §3.2: **`sh_hold` needs an
era-head arm**, or /init cannot hand the round its first credential.
`sh_round_holds_file`'s own statement is otherwise the right one — this
lane took it as the PROGRAM STREAM's single named hypothesis and did not
move it.  Its seven remaining section hypotheses (`Hopen_hand`,
`Hlexr`, `Hchild_echo`, `Hexecfail`, `Hpanic`, `Hchild_cat`,
`Hchild_redir`) are unchanged and belong to OFF-LINK, SH-MALLOC-3,
LINK-GEN, CAT-ENTRY-2 and SH-ROUND as lane SKELETON's table says.

One measurement for whoever writes `UInitFile.v`'s proof: `Admitted` under
`Proof using X` DOES discharge over `X` at section close (checked), so
`UShRound.sh_round_holds_file` is a constant taking all seven as explicit
arguments.  It therefore **cannot** be applied to close `file_prog_law`
while they are open; the hypothesis has to be declared where /init needs
it, at the instantiated statement.  That is why the brief's "take it at
its exact statement" and "`file_adequacy_closed`'s proof unchanged" cannot
both hold, and why the corollary will gain the premise on the day the
theorem lands.

## 5. Build

Whole tree green on the lane's remote tree; the two audits that could see
this lane (`make audit-file-only`, `make audit-all-only`) are unchanged,
because nothing imports `AppFileCons.v` or `UInitFileCons.v` and
`FileAssumptions.v` still requires only `UFileBootAdequacy`.  No
`Admitted` of this lane's, no new `Axiom`, `Proof using` everywhere.
