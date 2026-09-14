# PROLOGUE-ALTS-3 report 2 -- rebased onto INIT-DIAG, EchoLinksPro fixed

Checkout /shared/xv6iris-2-tlw, branch `lane/prologue-alts-3`.
NEW BASE: origin/main `9a1d2e638` (= `bdd9faf7f` INIT-DIAG + its notes commit).
`git rebase origin/main` applied both lane commits cleanly (no conflict; the
`_CoqProject` rows are `EchoOut.v / EchoLinks.v / EchoLinksPro.v /
EchoLinksLine.v / EchoLinksBan.v / AppEcho.v`).  Nothing pushed; tree clean.

## Commits (on top of 9a1d2e638)
- `da61f6275` PROLOGUE-ALTS-3: the banner is optional -- letter 3, the bare prompt, the
  discipline lemma (rebased `d10e4ad8a`; content unchanged).
- `fcd6e6c08` PROLOGUE-ALTS-3: EchoLinksBan (rebased `fb0d18545`; content unchanged).
- `5612d819d` PROLOGUE-ALTS-3: EchoLinksPro at the banner letter (INIT-DIAG rebase
  fix) -- `iris/EchoLinksPro.v` only.  `iris/UInitDiag.v` needed NO change
  (compiles as landed).

## What changed in iris/EchoLinksPro.v (verbatim)

Every Iris STATEMENT is textually unchanged: `ewc_pro_taint`,
`ewc_owed_of_pro`, `ewc_ban_done_pro`, `ewc_pdg`, `ewc_pdiag`,
`ewc_pdiag_taint`, `ewc_pdiag_0`, `echo_pdiag_step`, `ewc_pdiag_done_1`;
their proofs were adjusted where noted.  UInitDiag consumes only those, plus
the literals `pro_alts !!! 1/2 !! j`, which did not move.

GONE (statement false at the new `pro_of`: no default banner, and the open
round is not `replicate j 1`):
```coq
Lemma pro_of_replicate_snoc (j a : nat) :
  pro_of (replicate j 1%nat ++ [a])
  = pro_of (replicate j 1%nat) ++ pro_alts !!! a ++ pro_more a u_banner.
```
NEW in its place:
```coq
Lemma pro_of_fail_snoc (j a : nat) :
  pro_of (pro_fail j ++ [3%nat; a])
  = pro_of (pro_fail j) ++ u_banner ++ pro_alts !!! a.
```

NEW -- the round-open shape AFTER A BANNER (the obstacle the previous report
predicted for `wr_pdiag_1_of_pro`: a bare `wr_pro` only says the round is
open, i.e. its prologue is some word over the continuing letters {1,3}; it
does not place the diagnostic's bytes.  What the eighteenth banner byte
actually leaves is more, and `ewc_pro` now carries it):
```coq
Definition wr_pban (ps cs : list nat) (n P : nat) : Prop :=
  wr_pro ps cs n P
  /\ (exists j : nat,
        pro_from (pro_idx cs (n `div` length echo_line)) ps = pro_fail j ++ [3%nat]).

Lemma wr_pban_of_ban (ps cs : list nat) (n P : nat) :
  wr_ban ps cs n P -> wr_pban (ps ++ [3%nat]) cs n (P + length u_banner)%nat.
```

CHANGED (pure body):
```coq
Definition wr_pdiag (ps cs : list nat) (n P a i : nat) : Prop :=
  pro_pin ps cs n
  /\ (n `mod` length echo_line)%nat = 0%nat
  /\ (n `div` length echo_line)%nat = length cs
  /\ (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat)
  /\ (exists j : nat,
        pro_from (pro_idx cs (n `div` length echo_line)) ps
        = pro_fail j ++ [3%nat; a]                       (* was: replicate j 1%nat ++ [a] *)
        /\ P = (length (proc_upto ps cs n) + length (wr_pre cs n)
                + pro_round * j + length u_banner + i)%nat).   (* unchanged *)
```
CHANGED (premise `wr_pro` -> `wr_pban`; the conclusion is unchanged):
```coq
Lemma wr_pdiag_1_of_pro (ps cs : list nat) (n P a : nat) :
  wr_pban ps cs n P -> wr_pdiag (ps ++ [a]) cs n (S P) a 1%nat.
```
CHANGED (literals; round 1 opens with NOTHING predicted, 20 + 5 = 25):
```coq
Lemma wr_owed_ambiguous :
  wr_pro [3%nat; 0%nat] [3%nat] 17%nat 25%nat
  /\ wr_blk [3%nat; 0%nat] [] 17%nat 20%nat.
     (* was: wr_pro [0%nat] [3%nat] 17%nat 43%nat /\ wr_blk [0%nat] [] 17%nat 20%nat *)
```
CHANGED (Iris DEFINITION body; the name, arity and every lemma ABOUT it keep
their statements):
```coq
Definition ewc_pro (v : era_pins) (n : nat) : iProp Σ :=
  ((∃ ps cs P : _, ⌜wr_pban ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
      ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.        (* was: ⌜wr_pro ps cs n P⌝ *)
```
This is a STRENGTHENING of the credential /init keeps: harder to produce
(only `ewc_ban_done_pro`, i.e. the banner's eighteenth byte, produces it --
through `wr_pban_of_ban`), easier to spend.  UInitDiag never unfolds it
(`kinit_pro := ∃ v, era_pin γ (S gen_id) v ∗ EchoLinksPro.ewc_pro T v n` is
produced by `ewc_ban_done_pro` and spent by `ewc_owed_of_pro` / `ewc_pdiag_0`),
so its statements survive unchanged -- the condition the coordinator set for
threading the shape through `ewc_pro`.

Proof-only changes: `pending_n_round_wr_pre` (none), `wr_pdiag_byte` (through
`pro_of_fail_snoc`, `pro_of_fail_length`, four `lookup_app_shift`s),
`wr_pdiag_S` (none), `wr_pdiag_done_1` (`pro_fail_S` for `replicate_S_end`),
`ewc_owed_of_pro` (`left; exact (proj1 Hw)`), `ewc_ban_done_pro` (destructure
`wr_banp .. 18`, `iExists (ps' ++ [3%nat])`, `wr_pban_of_ban`),
`echo_pdiag_step` byte 0 (destructure `wr_pban`).  Header comments updated.

## GATE
Build `pa3-4` (after the rebase and the fix): COMPILED=2 (`EchoLinksPro.v`,
`UInitDiag.v` -- everything else was already built at the lane's content by
`pa3-3`), `grep -c "^Error"` = 0, EXIT=0; VM `make -f CoqMakefile -n` prints 0
`ROCQ compile`; `make audit-only | grep -v '^make\|^cd ' | md5sum` =
57f7327206c4b276d05035342fea8ecf (the thirteen); `run-on-gcp --check-dumps`
RC=0; `python3 tools/lemma_diff.py --ref origin/main` (against 9a1d2e638 =
bdd9faf7f's code): 7 GONE, no Admitted/admit/Abort, no new axiom --
`pro_of_banner` (false), `pro_of_replicate_banner`, `pro_open_replicate`,
`pro_of_replicate_length`, `pro_done_replicate` (the open round is no longer
`replicate j 1`; the `pro_fail` family replaces them), `pcount_zero` (false at
`ps = []`, no consumer), `pro_of_replicate_snoc` (false; `pro_of_fail_snoc`
replaces it).  No `Admitted` in EchoLinksPro/UInitDiag.  Local pre-checks
against the pulled `.vo`: EchoLinksPro.v 9 s, UInitDiag.v 17 s, both EXIT=0.

## Still pending, per the coordinator
The second small rebase once IO-LEAF step 3 lands on main; the one-line fixes to
re-apply then are `UShLine.v:1044` (`read_ret` pattern `& %Hbd & _`) and
`UShOut.v:129,132` (`sh_pro_stage` at `proc_upto [3%nat] []`,
`sh_space_stream` at `proc_upto [3%nat; 0%nat] []`), plus the `EchoLinksLine.v`
`ewc_ban_done_line` proof if that file moves.  Not waiting for it.
