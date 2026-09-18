# The PROGRAM STREAM — the sh/init tier's file instance

One serial lane, with the right to change any statement in the sh/init
tier.  Its exit criterion is measurable:

```
grep -c "Hypothesis\|Admitted" iris/UShRound.v
```

(design §3.7's metric is the three skeleton files together —
`iris/UEchoFile.v iris/UShRound.v iris/UInitFile.v`; at the end of this
stretch it stands at **9 + 11 + 3 = 23**, the round's eleven being this
stream's.)

| when | count | what moved |
|---|---|---|
| at the stream's start (after SH-CHILD-2, `890ebb21a`) | **19** | — |
| after the link record's five and the lexability (`606b3efae`) | **13** | `Hwbl` `Hwbwc` `Hcltaint` `Hwc` `Hwbr` `Hlexr` |
| after sh's killed child (`fbc4048eb`) | **12** | `sh_kill_law_file`'s `Admitted` |
| after the kill equation (`85d72e261`) | **11** | `Hktaint` |
| after `file_stage_inst` (`c62244638`) | **11** | (the gate for `Hexecfail`/`Hchild_echo`; the two discharges wait on RULING H) |

Append one block per stretch, newest last, each with the metric after it.

---

## SH-CHILD-2 (2026-09-17) — the lend through the seam, the exec arm at an abstract fd 1, the redirect cut's argv bytes, and the redirect child's WALK; ONE silent hang found and named

Branch `app-file/sh-redir`, merged from `main` at `d8ffd312c`.  Whole tree
green on the lane's remote tree (`--proofs -k`, `EXIT=0`, zero `Error`);
`make audit-all-only` unchanged (echo FOURTEEN, system THIRTEEN, both lists
textually identical); `make gen-ucode` prints all seven catalogs unchanged;
no `Admitted`; every new result carries `Proof using`.  Metric unchanged at
19 — this stretch is the WALK the round's `Hchild_redir` needs, not the
round's hypothesis list.

### 1. The three items, as landed

**(1) THE EXIT IS PAID FROM THE LEND.**  `UkShRedirSeam.wp_kshm_child_redir`
and `_alloc_redir` took `(⊢ ukn_pay N (-1))` — "the payload is free" —
which is exactly what a PAID child cannot supply: its payload is
`UkShFork.ushf_wq Wc I`, i.e. `Wc I 3 ∨ Wc I 0`.  Both now take

```coq
    □ (Cr -∗ ukn_pay N (-1)) -∗
    Cr -∗
```

and hand `Cr` BACK in the continuation, beside `UM2`, on the arm where
nothing was spent — the shape `UkShEcho.wp_kshm_child_echo` already had and
the shape the parser's own walks take (`UkShRedirPc.wp_kshp_parsecmd_gt`'s
`Pex`).  **The open's exit needed the same**: `UkShRedir.wp_kshr_redir_arm`
spends the payment on the "open %s failed" arm, so
`wp_kshr_redir_arm_at Pex` is that walk at the pair (the lend threaded to
the failure arm and returned on the success arm) and the landed
`wp_kshr_redir_arm` is its instance at `Pex := ukn_pay N (-1)` — the walk
itself unchanged, character for character.

**(2) THE EXEC ARM AT AN ABSTRACT fd-1 ROW.**  `UkShEcho.sh_exec_sup_echo_at
Fd1` and `wp_kshr_exec_echo_at Fd1` are echo's supply and arm with
`⌜UkSh.ush_fd1p ld⌝` replaced by `⌜Fd1 ld⌝`; the big walk is
`wp_kshr_exec_echo_at_holds` and the landed `wp_kshr_exec_echo_holds` is

```coq
    exact (wp_kshr_exec_echo_at_holds UkSh.ush_fd1p ws Q Cr Cd).
```

— by CONVERSION.  Both landed definitions keep BODIES OF THEIR OWN
(`sh_exec_sup_echo` is a copy, not an alias) because `UShEchoPay.
sh_exec_sup_echo_wq_holds` — lane LINK-GEN-3's file — does
`rewrite /UkShEcho.sh_exec_sup_echo` and then `iIntros "!>"`, which a
constant-headed alias does not answer.  `sh_exec_sup_echo_at_fd1p` is the
one-line bridge, and it unfolds BOTH sides before matching (see §2).

**(3) `echo_argv_bytes` AT THE REDIRECT CUT.**
`UkShRedirBody.echo_argv_bytes_of_redir`: at
`UkShRedirPc.ushs_nulcut (wl_toks ws) len f fe` — the symbol-free cut with
ONE MORE terminator, the file name's — every argument byte and every
argument's terminator is below `|wl_body ws| < fe`, so the extra store is
invisible to them and `UkShWords.wl_cut_in` / `wl_cut_end` carry the rest.
SH-LEX-REDIR's ruling is what makes it short: the token list is
`wl_toks ws`, echo's own.

**(4) THE WALK.**  `UkShRedirBody.wp_kshm_child_file_redir` — the redirect
child from 0x9c0 to the exec: `wp_kshm_child_alloc_redir` (parse,
`close(1)`, `open`, out at `runcmd` with the EXEC sub-tree and the
receipt) and then `wp_kshr_exec_echo_at_holds` at

```coq
  Definition ushs_fd1f (ty : fdtype) (l : list fdstate) : Prop :=
    l !! 1%nat = Some (FdOpen false true ty).
```

The open and the file supply are RESOURCE PREMISES, not hypotheses — both
are the application's and both come out of the credential family the fork
lent (`Wcf I 3 = Wcl I 3 ∗ sh_hold I`), which is where the round will get
them.

### 2. THE SILENT HANG, found and named (durable-notes' fourth shape, confirmed)

`iris/UkShEcho.v` compiled for fifty minutes with no `.vo`.  `coqc -time`
stops dead after

```
Chars 26638 - 26667 [rewrite~/sh_exec_sup_echo_at.] 0. secs
```

— i.e. in the `apply _` of

```coq
  Global Instance sh_exec_sup_echo_at_persistent Fd1 ws Q Cr :
    Persistent (sh_exec_sup_echo_at Fd1 ws Q Cr).
```

**With the body transparent and its fd-1 row a VARIABLE, the `Persistent`
search walks the whole obligation** — `udepw_at_refR` and everything under
it — and does not return.  The remedy is the one `UkSh.
ush_rest_l_persistent` already carries: name the instance the box deserves
(`apply bi.intuitionistically_persistent`).  The two other variable-headed
instances this stream added (`UkShFork.ushf_child_law_at_persistent`,
`ushf_body_law_persistent`) take it too, and
`#[local] Typeclasses Opaque sh_exec_sup_echo_at / wp_kshr_exec_echo_at`
keeps later searches in the file off their bodies.

**The method, for the next one:** kill your own worker by PID, re-run the
file under `coqc -time` redirected to a file on the VM, and read its LAST
line — the hang is in the command AFTER it.

### 3. What is left of obligation 18, and it is ONE NUMBER plus the era's step

- **THE BUDGET.**  `UkShFork.ushf_child_law_at Lp` hands the child
  `60 + (8 + (ush_Dg + n))` and the redirect walk needs
  `68 + (8 + (ush_Dg + n))`: the redirect parse is eight words deeper than
  the symbol-free one (`UkShRedirPc.wp_kshp_parsecmd_gt` asks `68 + nn`
  where `UkShParseCmd.wp_kshp_parser` asks `60 + nn`).  `UkSh.ush_Dbody`
  stays **80** by ruling; closing the gap is either `ush_Dbody := 88` with
  the fork's arithmetic following (the core is `wp_kshf_fork_core`, whose
  `2 + (ush_Dg + (66 + n))` becomes `74`, and the child law's budget a
  parameter `Dc ≤ 68` so echo's 60 stays the landed number) or eight words
  saved in the redirect parse.  **This is the only reason
  `wp_kshm_child_file_redir` is not plugged into `ushf_body_law_file`
  today.**
- **THE ERA'S STEP.**  Wrapping K1's `UEchoFile.efile_image_entry` into
  `sh_exec_sup_echo_at (ushs_fd1f ty)` is `UShEchoPay.
  sh_exec_sup_echo_wq_holds`'s file twin — the pin, the node image and the
  entry, ~60 lines naming the file application's own ghost state.  It is
  the round's, not the walk's.

### 4. The file-instance sweep, as a table (the stream's first hour)

`grep -n "EchoDisc\.\|alt_execfail\|cmd_echo\|line_alts_of\|disc_input\b\|ush_fd1p\|body_ok\|OffParked" iris/UkSh*.v iris/USh*.v iris/UInit*.v`
— 53 hits in `UkSh.v`, 16 in `UkShEcho.v`, 12 in `UkShDiag.v`, 8 in
`UShEchoPay.v`, 6 in `UShRound.v`, 5 each in `UkShFork.v`/`UShPanic.v`,
4 in `UShEcho.v`, 3 each in `UShKernel.v`/`UInitSh.v`, and singletons
below.  They are FOUR kinds, and only the last is real work:

| kind | where | what the file era needs |
|---|---|---|
| the LINE (`EchoDisc.line_ok`, `line_max`, `cmd_echo`, `body_ok`) | `UkSh` (the buffer, the receipt), `UkShEcho` (argv) | nothing: SH-CHILD's typed line carries `line_ok` at all three constructors, and `FileDisc.uline_ws LCat := wl_words cmd_cat_f` (this stream's ruling) makes the cat arm name its own words |
| the fd-1 ROW (`ush_fd1p`) | `UkSh` (the predicate and its two lemmas), `UkShEcho` (the supply, the arm), `UkShFork` (the child law's three-row premise) | DONE for the arm and the supply (item 2); the child law's `ush_fd0c/fd1p/fd2p` triple is still the console's and is what the redirect child's own law replaces |
| the DIAGNOSTIC (`alt_execfail`, `cmd_echo` inside it) | `UkShDiag` (the bytes, the law), `UkShEcho` (the child law) | LINK-GEN-4's `ush_execfail_law_wq_at dg nn`, and SH-CHILD-2's `ushf_child_law_holds_at`, which takes the carrier off the LINE SHAPE: the premise is `forall I, line_ok (last_ws I) -> dg I = alt_execfail /\ nn I = 17`, discharged inside the walk from the line fact the law already carries |
| the ALTERNATIVES (`line_alts_of`, `disc_input`) | `UShEcho`, `UShPanic`, `UShRound` | the round's own: `FileLinksLine`'s `fwc_*`/`fhead`/`fab` against LINK-GEN-3 §5's fields, which is where the stream goes next |


## THE ASSEMBLY, stretch 1 (2026-09-17) — the one number, the link record's five, the lexability and the killed child: 19 → 12

Whole tree green at every commit (`--proofs -k`, `EXIT=0`, zero `Error`).

### (a) THE ONE NUMBER — `UkSh.ush_Dbody` is 88 (`3f4a7c132`)

The body's room has to cover the DEEPEST child sh forks, and the redirect
line's parse is eight words deeper than the symbol-free one
(`UkShRedirPc.wp_kshp_parsecmd_gt` asks `68 + nn`,
`UkShParseCmd.wp_kshp_parser` asks `60 + nn`).  Restating the child's side
instead is not possible: the fork hands the child exactly the room the
parent had, so the eight have to be in `ush_Dbody`.  What carries it:

- `UkShFork.ushf_child_law_at Lp Dc` — the room is a PARAMETER now.  The
  fork hands `68 + (8 + (ush_Dg + n))` and a law at `Dc <= 68` is that same
  run at `68 - Dc + n`, so **echo's instance is `Dc := 60`, the landed
  number, and no landed walk moved**.
- `wp_kshf_fork_core`'s own accounting: `2 + (ush_Dg + (66 + n))` becomes
  `74`, and its statement is at `16 + (UkSh.ush_Dbody + n)` rather than at
  the literal.
- `UkShRedirBody`'s redirect law and body are at `Dc := 68`.

The echo tier carries the eight unspent, which costs it nothing: a child
law is `∀ n`, so more room is the same law at a bigger `n`.

### (b) SIX HYPOTHESES GO (`606b3efae`)

**`Wcl` / `Wbl` are not parameters any more.**  They are
`FileLinkInst.file_Wcl` / `file_Wbl` — lane LINK-GEN-2's record at this era
— so the five conversions the loop spends are that record's five lemmas:

| hypothesis | now |
|---|---|
| `Hwbl`, `Hwbwc`, `Hcltaint` | `FileLinkInst.file_Hwbl` / `_Hwbwc` / `_Hcltaint`, verbatim |
| `Hwc`, `Hwbr` | one destructuring each: the record states them at the PIN and the input's lower bound, and `UShLine.ush_mid_at` carries both PERSISTENTLY, so the bridge moves no resource |
| `Hlexr` | deleted — `UShLexRedir.ush_line_lexable_redir_holds`, this stream's own theorem |

### (c) THE KILLED CHILD, PROVED (`fbc4048eb`)

`sh_kill_law_file` is three lines once `Hcltaint` is a definition: the
taint is the era's, it inhabits the credential at the era's pin, and it is
`sh_hold`'s own right arm.  It takes the PIN as a premise — the
credential's pin is linear under an existential and a killed child holds
none; the round has one.

### WHAT IS LEFT, and what each is gated on

| # | item | gate |
|---|---|---|
| `Hexecfail` | `UShEchoPay.ush_execfail_law_wq_at_hold` is EXACTLY the shape `UShRound` now states, at `Hold := sh_hold` and `L := FI` | needs `file_stage_inst : StageRec FI` (the section takes `(St : StageRec L)`) and `FileLinks.file_links g` as a premise of the round |
| `Hchild_echo` | `UShEchoPay.sh_exec_sup_echo_wq_holds`'s file twin | the same `file_stage_inst`, plus the file application's pin and node image |
| `Hchild_redir` | the WALK is proved (`UkShRedirBody.wp_kshm_child_file_redir`) and the budget now lines up | the era's step: `sh_exec_sup_echo_at (ushs_fd1f ty)` out of K1's `UEchoFile.efile_image_entry` — `udepw_at_refR_of_sup` plus the file era's pin resolution, ~60 lines of the same plumbing `UShEchoPay` has for echo |
| `Hchild_cat` | `UCatKernel.cat_child_of_entry` | cat's lend, the kernel stream's |
| `Hopen_hand` | — | the kernel stream's (OFF-LINK-6) |
| `Hktaint` | the record's interface equation | free, once someone writes the projection |
| `sh_prompt_alt_of_deed`, `sh_tag_law_file`, `sh_child_law_file`, `sh_round_holds_file` | the round's own mathematics | `sh_hold`'s re-establishment across a child against `cat_tie`/`fst_after` |

**`Hktaint` is gone the way `Hcons` and `Htag` always were**: the round
takes the kill projection as a record EQUATION
(`app_taint = file_taint (fgn_cl g)`), which is what `UInitBoot` derives
beside the other two from one interface equation, and the hypothesis is
that equation read as an entailment.

**`file_stage_inst` is the single gate on two of them**, and it is a
`StageRec FI`: a `CurRec` at `FileLinksLine`'s cursor plus `sk_lend_stage`
(the era's lend opened as a stage, with `ck_alt = line_alts_of (last_ws I)
!!! 0`) and `sk_apr0`.  That is the next stretch's first item.


## (c) `file_stage_inst` — WHY IT IS NOT A MIRROR OF ECHO'S, and the four-line fix

The instance itself is SHORT, and shorter than echo's: the file era's
cursor IS `FileLinksLine.fwc_blk g k v I 0`, its step IS
`FileLinksLine.fblk_step` (which already takes `fab I a !! i = Some b` and
walks `file_links_w` / `file_links_blk`), and the lend-to-cursor step is
`fwc_lend`'s own body at `blkcs_f cs 0 0 = cs` and `P + 0 = P`.  The
alternative's bytes line up too:

```coq
  ralt_dec 0 = REcho 0,   fst_free (REcho 0) = true,
  ralt_ok (LEcho ws) (REcho 0) = (0 < 4)%nat,
  cont s l (REcho k) = line_alts_of (uline_ws l) !!! k
```

so **`fab I 0 = line_alts_of ws !!! 0` exactly when `fline I = LEcho ws`**
— the coordinator's ruling, and it is one `rewrite (fab_is …)`.

**WHAT BLOCKS IT is `StageRec.sk_lend_stage`, which is ECHO-SPECIFIC.**  It
reads

```coq
    sk_lend_stage : forall (k : nat) (v : era_pins) (I : list (bv 8)),
      ⊢ lk_lend L k v I -∗ (∃ st, ⌜ck_ok L sk_cur st (last_ws I)⌝ ∗ … ) ∨ lk_T L;
```

— **at EVERY input**.  The file era's lend exists at all three lines the
discipline admits, and at an `LEchoF` one the child writes NOTHING to the
console (`cont _ (LEchoF ws) (RFRan sel) = u_prompt`), at an `LCat` one it
writes cat's own bytes; only at `LEcho` is the block `line_alts_of ws !!! 0`.
So the field as stated says the file's redirect child prints echo's line on
the console, which is false — the instance cannot be built, and no amount
of work inside `FileLinksLine` changes that.

**THE FIX, four lines and two consumers.**  The guard the field needs is
already the one the law above it carries, and it belongs to the ERA:

1. `StageRec.CurRec` gains `ck_lineok : list (bv 8) -> Prop` — "the lines
   this cursor is about".
2. `sk_lend_stage` takes `ck_lineok I` as a premise.
3. `UkShEcho.sh_exec_sup_echo_wq_at` (a twin of the landed name, which
   keeps `⌜line_ok (last_ws I)⌝`) is guarded by the abstract
   `ck_lineok I` instead, and `UShEchoPay`'s walk passes its guard
   through to `sk_lend_stage` — the one place it is spent
   (`iris/UShEchoPay.v:194`).
4. echo's instance takes `ck_lineok := fun I => line_ok (last_ws I)` and
   its `sk_lend_stage` opens with `intros _`; the file's takes
   `ck_lineok := fun I => fline I = LEcho (last_ws I)`, which is what the
   ROUND has (its tag law reads the era's discipline) and what
   `UShEchoPay`'s walk cannot derive on its own.

With that, `file_stage_inst` is `MkStageRec FI file_cur_inst …` over
`fwc_blk` / `fblk_step` / `fwc_lend`, and it discharges BOTH `Hexecfail`
(by `UShEchoPay.ush_execfail_law_wq_at_hold FI sh_hold`, which is already
exactly the shape `UShRound` states) and `Hchild_echo` (by
`sh_exec_sup_echo_wq_at_holds` at the file guard).

**This is the next stretch's first item, and it is a STATEMENT change in
three files the program stream owns** (`StageRec.v`, `UkShEcho.v`,
`UShEchoPay.v`) plus the two instances — not a proof that can be written
against the record as it stands.


## (c) LANDED — `file_stage_inst`, and the two record fields it cost

`iris/FileLinkInst.v` now carries `file_stage_inst : StageRec FI`, and it is
SHORTER than echo's because `FileLinksLine` already had both halves: the
cursor IS `fwc_blk g k v I 0`, the step IS `fblk_step`, the lend and
`fwc_blk _ _ _ 0 0` are the same proposition (`blkcs_f cs 0 0 = cs`,
`P + 0 = P`), and the block's end is `lk_post` at
`length (fab I 0) - 2 = length (wl_line (drop 1 (last_ws I)))`
(`EchoDisc.line_alts_of_0_length`).  The model fact underneath is three
reductions:

```coq
  ralt_dec 0 = REcho 0,  fst_free (REcho 0) = true,
  ralt_ok (LEcho ws) (REcho 0) = (0 < 4)%nat,
  cont s l (REcho k) = line_alts_of (uline_ws l) !!! k
```

so `fab I 0 = line_alts_of (last_ws I) !!! 0` **at an echo line**.

**THE TWO FIELDS THE RECORD GAINED** (`StageRec.v`, and the guard threaded
through `UShEchoPay` and `UShRest`):

| field | was | now |
|---|---|---|
| `ck_lineok` | — | `list (bv 8) -> Prop`: the inputs this cursor is about |
| `sk_lend_stage` | at EVERY input | takes `ck_lineok L sk_cur I` |
| `sk_apr0` | at EVERY input | takes the same |

Both were ECHO-SPECIFIC as stated: the file era's lend exists at all three
lines its discipline admits, and at an `LEchoF` line the child writes to
the FILE (the console block is the prompt) while at an `LCat` line it
writes cat's own bytes — so a record without the guard says the redirect
child prints echo's line on the console.  echo's instance is
`ck_lineok := fun _ => True` and its two fields open with `intros _`; the
consumers (`UShEchoPay.echo_slot_of_kexec_at_at`, `ushf_child_law_hold_at`,
`sh_exec_sup_echo_wq_holds_at`, `UShRest.sh_rest_holds_at`) thread the
era's own reading of its admissible lines, and echo's callers pass `I`.

**WHY `Hexecfail` AND `Hchild_echo` DID NOT FOLLOW IMMEDIATELY.**  Both
dischargers are stated at `Wc := fun I p => lk_lcred L (S gen_id) I p ∗ Hold I`
— and RULING H reshapes the round's families to
`Wcf I p := ∃ s0, Wcl_at s0 I p ∗ sh_hold_at s0 I`, which is not of that
form (the index is existential OUTSIDE the credential).  So the two
applications wait on INIT-FILE's `_at` layer, and this stream did not prove
them against a shape that is about to move.


## `Hchild_redir`'s ERA STEP — the two things K1's entry must become, measured against the supply it has to fill

The wrapper is `UShEchoPay.sh_exec_sup_echo_wq_holds_at`'s body with the
`(E)` component replaced, and everything else about it is ALREADY the file
era's: `exec_walk_of_pin FsEchoPin.era0_echo_pins` and
`sh_echo_path_of_holds` are about **/echo's image and the pin, not about
the era**, and the round holds `UShEcho.sh_echo_slot T` at
`T := file_taint` — so `(W)` and the path come out unchanged.  Two things
do not, and both are `iris/UEchoFile.v`'s (the KERNEL stream's):

1. **The entry must be PARAMETRIC IN THE PAYLOAD.**
   `UEchoFile.efile_image_entry` concludes at
   `image_entry … (fun _ : Z => ef_exit i γo ws) (ef_pay i γo ws) uslot`,
   and `ExecEntry.image_entry`'s payload slot is `my_pay (uvis_gen W') Q`
   — which `ChildTok.my_pay_agree` makes RIGID: the generation's payload
   is what sh's fork chose, `UkShFork.ushf_wq Wcf I`, and no conversion
   moves an entry from one `Q` to another.  So the entry has to take `Q`
   with `□ (ef_exit i γo ws -∗ Q (-1))`, which is **exactly the shape K1's
   own `efile_uexec_slot_at` already has** — `efile_image_entry` is that
   lemma packaged at the identity wand, and packaging it at a parameter
   instead is a one-binder change with the same proof.  echo's side has
   had this all along (`UShEchoPay.echo_slot_of_kexec_at_at` takes `Wc`,
   `Hold` and the three conversions).

2. **The entry's `Pay` must be the one the SUPPLY hands it**, i.e.
   `UserFd.ustd (ukn_fd N') ld ∗ Cr` — because
   `ExecRun.udepw_at_refR_of_sup` gives that same resource to the entry on
   the exec path and back as the refund on the failure path.  K1's is
   `ef_pay i γo ws` (`Wq ∗ efq i γo ws []`: the deed and the fragment at
   zero), so the wrapper needs
   `□ (ustd (ukn_fd N') ld ∗ Cr -∗ ef_pay i γo ws)` — and that is the
   ROUND's to give, because at the file era **the deed rides inside the
   lend** (`Wcf I 3 = Wcl I 3 ∗ sh_hold I`, and `sh_hold` holds
   `fown r s`).  Under RULING H' it is `sh_hold_at s0 I`, same content.

So the era step is: K1 states `efile_image_entry_at Q` (change 1), the
round supplies the Pay conversion (change 2, one wand off `sh_hold_at`),
and the wrapper between them is `sh_exec_sup_echo_wq_holds_at`'s body with
`(E)` filled by K1 — about sixty lines, none of it new mathematics.
`UkShRedirBody.wp_kshm_child_file_redir` already takes exactly
`(∀ ty, K ty -∗ sh_exec_sup_echo_at (ushs_fd1f ty) ws Q Cr)` as its
premise, so the wrapper plugs straight in, and its home is a file above
`iris/UEchoFile.v` (1626) — `UkShRedirBody` is at 1571 and cannot name K1.
