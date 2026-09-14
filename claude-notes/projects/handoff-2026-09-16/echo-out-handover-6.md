# ECHO-OUT handover 6 (lane `lane/echo-out`, checkout `/shared/xv6iris-2-disc`)

## 0. State -- PART 5 IS LANDED

`lane/echo-out` = TWO commits on `origin/main` = `7b9760e66`:
  `14de1df6b` part 5a -- `iris/EchoOut.v`, `echoOutΣ` + `subG_echoOutΣ` (+18)
  `cc76a5907` part 5  -- 11 files, +504/-613
Nothing pushed.  Working tree CLEAN.  Builds eo56-eo66; next free `eo67`.

GATE (eo66 confirming, 0 files after the rebase; eo65 was the 14-file
build of the change): zero Error, EXIT=0; `make -f CoqMakefile -n` prints
no `ROCQ compile`; `make audit-only` md5 `57f7327206c4b276d05035342fea8ecf`
(the thirteen, unchanged); `lemma_diff --ref origin/main` = 7 deletions,
all justified in the commit message; nothing Admitted; no new assumption;
`--check-dumps` clean.

## 1. What landed

- `AppEcho.echo_fixed := EchoOut.echo_gn`; `echo_cl` = the taint counter at
  0 ∗ the empty era map; `echo_birth` allocates both.
- `echo_R := EchoOut.echo_led (echo_taint γ) γ`,
  `echo_tag := EchoOut.etag (echo_taint γ)`,
  `echo_out/in/turn/win := eout/ein/eturn/ewin` at the same taint.
- Every obligation off `EchoOut`: `HR0` = `echo_led_init`, `Hpow` =
  `echo_led_pow`, `Happ_out_sup`/`Happ_in_sup` = `eout_sup`/`ein_sup_log`/
  `ein_sup_deliv` off `echo_taint_of_sup`, `Hrx` = `echo_led_rx`,
  `Happ_echo` = `echo_happ_echo` at the four equations, and `Htx` =
  `eout_drain` + `echo_led_tx` (handover 5 §7b's argument, verbatim).
- `echo_phi` in the owner's whole-history form; `Hphi` CLOSED at
  `UInitBootAdequacy` from `echo_Hphi_R` through
  `RiscvAdequacy.obs_ledger_at_phi`.
- `echoOutG Σ` REPLACES the bare `mono_natG Σ` binder in AppEcho's four
  sections and UInitCons's, and is added to UConsLine / UConsOpen /
  UInitConsK / UShConsK / UInitSh / UInitBoot (both sections) /
  UInitBootAdequacy.  Consequence: `UInitBootAdequacy`'s
  `rewrite <- Hgen in Heq, Htag, Hkill |- *` is deleted -- the two layers
  no longer both appear.
- `UInitBoot`: `Hlic`/`Hilic` are `□ (echo_taint γ -∗ out_licence)` /
  `□ (echo_taint γ -∗ in_licence)`, spent inside `Hmint` where the taint is
  in hand.
- The blocker of handover 5 §2 was RULED route (B) (app-echo.md
  `9841bbecc`): `UShLine.ush_read_sup` and `ush_read_recv_leaf_holds` are
  DELETED, and the statement the second proved is a Coq premise of
  `echo_Hinit_boot` and the third conjunct of `Hsh_owed`.

## 2. What IO-LEAF receives, and what it owes back

RECEIVES, from `echo_Hinit_boot`'s `app_turn`:
`EchoOut.eturn γ (S gen_id)` =
`∃ v, era_pin (S gen_id) v ∗ turn v 0 ∗ dl_cnt v (1/2) 0 ∗ cs_lb v []
      ∗ E_lb v 0` -- literally `EchoOut.echo_write_link`'s argument list at
`P = 0`, `n0 = 0`, `cs0 = []`, PLUS the reader's half of the delivered
count.

OWES, as the third conjunct of `UInitBootAdequacy.Hsh_owed` (survey D5/D6):
```
forall (c : app_fixed app_echo) (γp : gname)
       (N : UkRun.uk_names Σ) (l : list FdSlots.fdstate),
  UkRun.ukn_pay N = UserConsole.ucons_pay FsCfg.fsc_cons γp (echo_taint c) ->
  ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp (echo_taint c)
      FsCfg.fsc_cons l
```
The two halves of the console read's deposit are `ConsoleInv.cons_acc`
(the ring's, paid by the lease as before) and
`WpUart.cons_read_pay (S gen_id) Rin` (the application's, which is what
needs `era_pin ∗ dl_cnt v (1/2) n` on the lease and
`EchoOut.echo_read_link`).  What survives in `UShLine` for that work: the
read family `ush_read_fam`/`xfam_rd`/`ush_rd_ret`, the two `sbundle`
adapters, `ush_fd_st_console`/`ush_fd_st_closed`, `ush_count_is_cap`, and
the SHUT arm's deposit `ush_read_sup_closed` (all licence-free and
unchanged).  The deleted `ush_read_recv_leaf_holds` body is in the history
at `origin/main~` -- its receipt/minus-one/closed arms are all reusable;
only its console-arm deposit (`ush_read_sup`) has to be rebuilt.

## 3. Nothing else moved

No concrete-Σ bundle changed: `echo_adequacy_modulo_phi` is over an
abstract Σ and no closed corollary at a concrete Σ mentions `echoOutG`.
`echoOutΣ`/`subG_echoOutΣ` exist for the closed theorem when it is stated.
`in_licence_triv` and `cons_read_pay_triv` are KEPT -- the generic slot
still uses them (`SpecConsoleintr.cons_echo_shift_triv`,
`SystemAdequacy.init_boot_of_triv`, `FsAbsInvFire.fsabs_fileread_in`).

## 4. Process notes

- `EchoOut.v` is a LEAF (~15 s alone).  The cone above `AppEcho` is 12
  files (~50 s); adding `EchoOutPure` makes it 14.
- rocq-warm helper: scratchpad `dw.sh <File.v>`.  Never while a `vmbuild`
  is in flight -- `run-on-gcp` syncs and the sync drops dirty `.vo`.
- Watch the `Require Import` insertion points: several dependents have
  MULTI-LINE require comments and a naive anchor splits them (cost one
  build).
- `UInitBootAdequacy`'s `refine` bullet list is read off the elaborator,
  not guessed; closing `Hphi` did NOT change the number of goals (the
  `Htagp`/`Htagt`/`Houtt`/`Hinpt`/`Hwint` holes stay fixed by unification).
