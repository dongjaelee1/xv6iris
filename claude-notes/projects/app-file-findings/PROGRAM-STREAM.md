# The PROGRAM STREAM — the sh/init tier's file instance

One serial lane, with the right to change any statement in the sh/init
tier.  Its exit criterion is measurable:

```
grep -c "Hypothesis\|Admitted" iris/UShRound.v
```

| when | count |
|---|---|
| at the stream's start (after SH-CHILD-2, commit `890ebb21a`) | **19** |

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
