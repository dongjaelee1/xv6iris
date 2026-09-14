# PROLOGUE-ALTS-3 report -- the banner is optional (resumed session)

Checkout /shared/xv6iris-2-tlw, branch `lane/prologue-alts-3`, base `4ab8f963f`
(= origin/main `b7c49dea2` code + one notes commit).  NOT rebased onto
`bdd9faf7f` (INIT-DIAG), per the coordinator's instruction; the expected
breakage of `iris/EchoLinksPro.v` / `iris/UInitDiag.v` is listed in section 9.

Commits: `d10e4ad8a`, `fb0d18545` (section 1).

## 0. Terms used below (plain CSL / xv6)

- *wire*: the bytes the kernel has stored to the console UART, in order.
- *transcript*: what the application predicts the wire is a prefix of.  It is
  built from a *resolution* `ps : list nat` (which prologue LETTERS init and the
  shell chose, in order) and a *choice list* `cs : list nat` (which alternative
  each typed line's block took).
- *prologue round*: the stretch of wire from a shell start (or restart) to the
  shell's prompt or init's terminal diagnostic.
- *letter*: one console write of init's or the shell's inside a round: the
  banner, the exec diagnostic, the fork diagnostic, or the prompt.
- *stage / cursor*: `P`, the number of process bytes written in the era; the
  claim's authority half (`turn_auth`) and the writer's half (`turn`) agree on
  it.  `proc_upto ps cs n` is the stream of process bytes the stage machine
  owes through block `n`; the cursor indexes it.
- *credential*: the writer's half of the cursor together with persistent lower
  bounds of `ps`/`cs` and a pure *shape* saying where the cursor stands
  (`wr_pro` = round open, next byte is a letter's first; `wr_blk` = the line's
  block is owed; `wr_ban` = round open with `j` failed sub-rounds behind, the
  banner or the bare prompt next; `wr_owed = wr_pro \/ wr_blk`).
- *taint* `T`: the persistent proposition that says the era's discipline was
  broken; every claim and credential is `... ∨ T`.

## 1. Commits

- `d10e4ad8a` PROLOGUE-ALTS-3: the banner is optional -- letter 3, the bare prompt, the
  discipline lemma (iris/EchoDisc.v, EchoOutPure.v, EchoOut.v, EchoLinks.v,
  EchoLinksLine.v, UShOut.v, UShLine.v).  Items (1), (2) and the core of (3)
  in ONE commit: they are entangled hunk-by-hunk (EchoDisc's new `pro_of`
  breaks EchoOut/EchoLinks without (2)'s changes; (3)'s `turn_lb`/`rd_stage`
  live in the same `ein`/`read_ret` hunks as (2)), so no per-item split
  would have been a green intermediate state.
- `fb0d18545` PROLOGUE-ALTS-3: EchoLinksBan -- the bare prompt and the
  discipline lemma at the tight shapes (NEW iris/EchoLinksBan.v + its
  `_CoqProject` row).
Both on `lane/prologue-alts-3` on top of `4ab8f963f`; author = the checkout's
config; working tree clean; nothing pushed.

## 2. THE TRUSTED DIFF (EchoDisc.v, the theorem's trace predicate)

The decision on the brief's "subtle point" (what an UNRESOLVED round predicts):
**an open round with nothing filed predicts NOTHING**, and **the banner is a
LETTER of its own (index 3) filed at its first byte** -- not a prefix glued onto
alternatives 0-2.  Reason: a writer's knowledge of the resolution is a
persistent LOWER BOUND (`ps_lb`), worth exactly the bytes of the letters it
names (`pro_of_mono`).  Keeping the default `pro_of [] = u_banner` while adding a
banner-less alternative would make `pro_of` NON-monotone (`pro_of [] = banner`,
`pro_of [3] = "$ "`), and every link stated at a lower bound breaks; making
`pro_of []` empty while keeping the banner as a PREFIX of 0-2 leaves init unable
to write the banner at all (no byte is predicted until the round's choice, which
init does not know while it prints the banner).  Filing the banner as a letter
resolves both: init files `3` at the banner's first byte, the shell files `0`
at its '$' -- after a banner (`[3; 0]`) or with none (`[0]`).

OLD:
```coq
Definition pro_alts : list (list (bv 8)) := [ u_prompt; u_execfail; u_forkfail ].

Definition pro_more (a : nat) (t : list (bv 8)) : list (bv 8) :=
  if decide (a = 1%nat) then t else [].

Fixpoint pro_of (ps : list nat) : list (bv 8) :=
  match ps with
  | [] => u_banner
  | a :: ps' => u_banner ++ pro_alts !!! a ++ pro_more a (pro_of ps')
  end.

Definition pro_done (ps : list nat) : Prop := Exists (fun a => a <> 1%nat) ps.
```
NEW:
```coq
Definition pro_alts : list (list (bv 8)) :=
  [ u_prompt; u_execfail; u_forkfail; u_banner ].

(* the letters that CONTINUE a round: the exec failure and the banner *)
Definition pro_cont (a : nat) : Prop := a = 1%nat \/ a = 3%nat.

Definition pro_more (a : nat) (t : list (bv 8)) : list (bv 8) :=
  if decide (pro_cont a) then t else [].

Fixpoint pro_of (ps : list nat) : list (bv 8) :=
  match ps with
  | [] => []
  | a :: ps' => pro_alts !!! a ++ pro_more a (pro_of ps')
  end.

Definition pro_done (ps : list nat) : Prop := Exists (fun a => ~ pro_cont a) ps.
```
`pro_tail` / `pro_rounds` / `pro_grp_cands` (the decidability search) follow the
same substitution `a = 1  ~>  pro_cont a`.  `expected_rel` and `disc_pt` are
TEXTUALLY UNCHANGED:
```coq
Definition expected_rel (l out : list (bv 8)) : Prop :=
  exists ps cs : list nat,
    pro_ok ps cs (length l `div` length echo_line)
    /\ Forall (fun c => c < length line_alts) cs
    /\ out `prefix_of` sess ps cs l.

Definition disc_pt (ps cs : list nat) (i : nat) (p : list mobs) : Prop :=
  sess_n ps cs i `prefix_of` obs_wire Uart0 p.
```
but their MEANING changes through `pro_of`: a settled round is now a word
`g ++ [t]` with `Forall pro_cont g` (letters 1/3 in any order) and
`t ∈ {0; 2}`.  The good run is `[3; 0]` (`pro_of_good : pro_of [3; 0] =
u_prologue`), the ruling's case is `[0]` (`pro_of_good_noban : pro_of [0] =
u_prompt`), one exec failure and a restart is `[3; 1; 3; 0]`, the fork
failure `[3; 2]`.

**WIDENING TO REPORT TO THE OWNER.**  The new predicate admits every word in
`{1,3}* {0,2}` per round, so besides the five transcripts the machine can
produce it also admits, e.g., `[3; 3; 0]` (two banners, no diagnostic between)
and `[1; 0]` (the exec diagnostic with no banner before it).  Neither happens
on the machine (init's console is open for the whole era or shut for the whole
era; with it open every letter of init's is preceded by a banner).  The
predicate is therefore WEAKER than the brief's literal design (`u_banner ++
alt` for 0-2 and bare `"$ "` for 3), which admits exactly `(banner exec)^j
(banner prompt | banner fork | "$ ")` -- itself already loose at
`j > 0`.  Tightening is possible without changing the stage machine: a
well-formedness predicate on `ps` ("3 is followed by a non-3, 1 is preceded by
3") carried as a conjunct of `pro_ok` and of `eout`'s bracket, with a premise on
`echo_link_pro`.  It is NOT done here; I judged it a ruling for the owner
(does the trusted surface need the tight shape, at the price of one more
conjunct through the claim?) rather than something to improvise in a resumed
session.  Anti-vacuity witnesses for all five machine transcripts are in
EchoDisc (`demo_*`, incl. the new `demo_seg_noban` / `demo_good_out_noban`).

The brief's question at (2) -- "if `j > 0` must the banner-less prompt be
excluded?" -- is answered by the same widening: it is ADMITTED
(`ewc_ban_pro` holds at any `j`; the transcript `(banner exec)^j "$ "` is in
the predicate).

## 3. Item (1): EchoDisc, what replaced `pro_of_banner`

`pro_of_banner` ("every prologue starts with the banner") is FALSE now and is
GONE.  Its consumers and their replacements:
- `pro_of_pos` -- was unconditional; now
  `Forall (fun a => a < length pro_alts) ps -> ps <> [] -> 0 < length (pro_of ps)`.
  Consumers: `pending_nonnil` (EchoOut; gained the premise `0 < length E`, since
  `pending ps cs [] = pro_of ps` may be empty; new `pending_nil_inv` says an
  empty block at a boundary IS the boot block), `sess_n_nonnil` (EchoOutPure;
  gained `Forall .. ps -> pro_done ps`; no consumer outside), `pcount_zero`
  (EchoOut; GONE -- false at `ps = []`, no consumer).
- `pro_of_replicate_banner` / `pro_open_replicate` (the arbitrary-round banner
  lemma's shape) -- GONE; an open round is no longer a block of 1s.  Replaced by
  the `pro_fail` family:
```coq
Definition pro_fail (j : nat) : list nat := concat (replicate j [3%nat; 1%nat]).
Lemma pro_fail_S (j : nat) : pro_fail (S j) = pro_fail j ++ [3%nat; 1%nat].
Lemma pro_fail_cont (j : nat) : Forall pro_cont (pro_fail j).
Lemma pro_done_fail (j : nat) : ~ pro_done (pro_fail j).
Lemma pro_of_fail_length (j : nat) : length (pro_of (pro_fail j)) = (pro_round * j)%nat.
Lemma pro_of_fail_banner (j i : nat) (b : bv 8) :
  u_banner !! i = Some b ->
  pro_of (pro_fail j ++ [3%nat]) !! (pro_round * j + i)%nat = Some b.
```
  and the general open-round algebra
```coq
Lemma pro_open_cont (ps : list nat) : ~ pro_done ps -> Forall pro_cont ps.
Lemma pro_of_open_app (ps z : list nat) :
  ~ pro_done ps -> pro_of (ps ++ z) = pro_of ps ++ pro_of z.
Lemma pro_of_singleton (a : nat) : pro_of [a] = pro_alts !!! a.
Lemma pro_of_open_done_lt (ps ps' : list nat) :
  ~ pro_done ps -> pro_done ps' -> ps `prefix_of` ps' ->
  Forall (fun a => (a < length pro_alts)%nat) ps' ->
  (length (pro_of ps) < length (pro_of ps'))%nat.
```
- `proc_upto_round_banner` / `proc_upto_round_banner_open` (PROLOGUE-ALTS-2):
  premise `pro_from .. ps = replicate j 1%nat` became
  `pro_from .. ps = pro_fail j ++ [3%nat]` (the banner FILED); the offset
  `length (proc_upto ps cs n) + length pre + pro_round * j + i` is unchanged.
- `pro_of_prefix_free`, `pro_of_not_done_next`, `pro_alts_head_ne_echo`,
  `pro_of_snoc_head`, `pro_tail_open_snoc`, `pro_of_open_snoc_lt`, `pro_pin_ok`
  and the canonical-form search (`pro_cands`, now over `cont_lists k` = all
  words over {1,3} of length k) are re-proved at the new definition; every
  `Forall (a < length pro_alts)` lemma now admits 3 and was checked
  (`pro_alts_prefix_det` and `pro_alts_head_ne_echo` do the 4x4 / 4 literal
  cases by `vm_compute`).  The four letters are pairwise prefix-free
  ("$ " / "init: e" / "init: f" / "init: s").

## 4. Item (2): the stage machine at the banner letter and the bare prompt

`echo_write_link_pro` (EchoOut.v) is UNCHANGED, statement and proof:
```coq
Lemma echo_write_link_pro (k : nat) (v : era_pins) (P n0 a : nat)
    (b : bv 8) (ps0 cs0 : list nat) (Φ : iProp Σ) :
  (n0 `mod` length echo_line)%nat = 0%nat ->
  (n0 = 0%nat \/ cs0 !!! (n0 `div` length echo_line - 1)%nat = 3%nat) ->
  ((n0 `div` length echo_line) <= length cs0)%nat ->
  pro_pin ps0 cs0 n0 ->
  ~ pro_done (pro_from (pro_idx cs0 (n0 `div` length echo_line)) ps0) ->
  P = length (proc_upto ps0 cs0 (S n0)) ->
  (a < length pro_alts)%nat ->
  pro_alts !!! a !! 0%nat = Some b ->
  era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
  (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T)
   -∗ Φ) -∗
  out_link Uart0 k b Φ.
```
No twin and no per-alternative stage function were needed: with "an open round
predicts nothing", `length (proc_upto ps0 cs0 (S n0))` IS the stage of the
round's next letter for every `a`, including `a = 3` (the banner) and `a = 0`
with nothing before it (the bare prompt).  The one claim-side change in
`eout_step_write_pro` is the `cs_len_ok` move: the block may now be EMPTY at
the choice byte (the boot block with nothing filed), so its premise is
`o_w so <> [] \/ length (o_E so) mod 17 <> 0 \/ length (o_E so) = 0` instead
of `o_w so <> []`.

EchoLinks, the banner-owed shape.  `wr_ban` now says the open round is exactly
the `j` failed sub-rounds, NOTHING of this sub-round filed:
```coq
Definition wr_ban (ps cs : list nat) (n P : nat) : Prop :=
  pro_pin ps cs n
  /\ (n `mod` length echo_line)%nat = 0%nat
  /\ (n `div` length echo_line)%nat = length cs
  /\ (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat)
  /\ (exists j : nat,
        pro_from (pro_idx cs (n `div` length echo_line)) ps = pro_fail j
        /\ P = (length (proc_upto ps cs n) + length (wr_pre cs n)
                + pro_round * j)%nat).
```
(OLD: `= replicate j 1%nat`, same `P`.)  Its algebra, all new or changed:
```coq
Lemma wr_ban_pro  (ps cs : list nat) (n P : nat) : wr_ban ps cs n P -> wr_pro ps cs n P.
     (* CHANGED: was  wr_ban ps cs n P -> wr_pro ps cs n (P + length u_banner) *)
Lemma wr_ban_low  (ps cs : list nat) (n P : nat) :
  wr_ban ps cs n P -> proc_upto (ps ++ [3%nat]) cs n = proc_upto ps cs n.
Lemma wr_ban_filed (ps cs : list nat) (n P : nat) :
  wr_ban ps cs n P ->
  exists j : nat,
    pro_from (pro_idx cs (n `div` length echo_line)) (ps ++ [3%nat]) = pro_fail j ++ [3%nat]
    /\ P = (length (proc_upto (ps ++ [3%nat]) cs n) + length (wr_pre cs n) + pro_round * j)%nat.
Lemma wr_ban_byte (ps cs : list nat) (n P i : nat) (b : bv 8) :
  wr_ban ps cs n P -> u_banner !! i = Some b ->
  proc_upto (ps ++ [3%nat]) cs (S n) !! (P + i)%nat = Some b.
     (* CHANGED: the stream is the FILED round's, [ps ++ [3]] *)
Lemma wr_ban_done (ps cs : list nat) (n P : nat) :
  wr_ban ps cs n P -> wr_pro (ps ++ [3%nat]) cs n (P + length u_banner)%nat.
     (* the old wr_ban_pro's role, with the banner filed *)
Lemma wr_ban_head (b : bv 8) : u_banner !! 0%nat = Some b -> pro_alts !!! 3%nat !! 0%nat = Some b.
Lemma wr_owed_round0 : wr_owed [3%nat] [] 0%nat 18%nat.   (* CHANGED: was  wr_owed [] [] 0 18 *)
```
The credential family `ewc_ban v n i` keeps its statement but its pure shape is
now indexed by whether the banner letter is filed:
```coq
Definition wr_banp (ps cs : list nat) (n P i : nat) : Prop :=
  match i with
  | O => wr_ban ps cs n P
  | S _ => exists ps' : list nat, ps = ps' ++ [3%nat] /\ wr_ban ps' cs n P
  end.
Definition ewc_ban (v : era_pins) (n : nat) (i : nat) : iProp Σ :=
  ((∃ ps cs P : _, ⌜wr_banp ps cs n P i⌝ ∗ turn v (P + i)%nat ∗ ps_lb v ps
      ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.
```
`echo_banner_step` (UNCHANGED statement) now pays byte 0 through
`echo_link_pro` at `a = 3` (filing the banner letter) and bytes 1..17 through
`echo_link_w`; `ewc_ban_done` (UNCHANGED statement) goes through `wr_ban_done`.
The bare prompt:
```coq
Lemma ewc_ban_pro (v : era_pins) (n : nat) :
  ewc_ban v n 0%nat -∗
  ((∃ ps cs P : _, ⌜wr_pro ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps ∗ cs_lb v cs ∗ E_lb v n) ∨ T).
Lemma ewc_ban_owed (v : era_pins) (n : nat) : ewc_ban v n 0%nat -∗ ewc_owed v n.
Lemma echo_prompt_dollar_ban (k : nat) (v : era_pins) (n : nat) (b : bv 8) (Φ : iProp Σ) :
  b = u_prompt !!! 0%nat ->
  era_pin γ k v -∗ echo_links -∗ ewc_ban v n 0%nat -∗ (ewc_sp v n -∗ Φ) -∗
  out_link Uart0 k b Φ.
```
so `echo_prompt_space` and `ewc_read` carry the round on unchanged.  No new
projection in `echo_links`; `echo_link_pro` pays both.  `wr_sp` / `wr_open`
needed no `a = 3` case.  Two vestigial premises were dropped (their lemmas are
true for every letter now): `pro_of_open_snoc_eq` lost `a <> 1%nat`,
`pending_n_round_snoc` lost `a <> 1%nat` (both EchoLinks-internal).  `ewc_pr`'s
`p = 0` arm was NOT widened (the coordinator's `ewc_owed v n ∨ ewc_ban v n 0`
instance at the top level is `ewc_ban_owed` away).

`turn` (the cursor) became a MONOTONE counter so the claim can publish a
persistent lower bound of it (item (3) needs it):
```coq
Definition turn      (v : era_pins) (P : nat) : iProp Σ := mono_nat_auth_own (ep_go v) (1/2) P.
Definition turn_auth (v : era_pins) (P : nat) : iProp Σ := mono_nat_auth_own (ep_go v) (1/2) P.
Definition turn_lb   (v : era_pins) (m : nat) : iProp Σ := mono_nat_lb_own (ep_go v) m.
Lemma turn_update v P P' P'' : (P <= P'')%nat -> turn v P -∗ turn_auth v P' ==∗ turn v P'' ∗ turn_auth v P''.
     (* CHANGED: gained the premise P <= P''; every caller moves the cursor by +1 *)
Lemma turn_lb_get v P : turn_auth v P -∗ turn_lb v P.
Lemma turn_lb_le v P m : turn v P -∗ turn_lb v m -∗ ⌜(m <= P)%nat⌝.
Lemma turn_lb_weaken v m m' : (m' <= m)%nat -> turn_lb v m -∗ turn_lb v m'.
```
(`era_full` changed accordingly; `turn_agree` unchanged.)

## 5. Item (3): THE DISCIPLINE LEMMA

WHAT MAKES IT TRUE (the invariant conjunct): the output claim's `acc = D cs E ++ w`
with `E` the log's echoed entries, together with `turn_auth` at the stage's own
count, means that when an echo closes block `n` the cursor stands at
`length (proc_upto ps cs (S n))` -- the WHOLE block including its prompt is on
the wire.  Nothing had to be weakened, but the fact had to be EXPORTED: the
input claim `ein` (both arms) and the pending-receipt `ein_pend` gained two
trailing conjuncts, deposited by `eout_step_echo` and handed out by
`ein_step_read`/`read_ret`:
```coq
Definition rd_stage (ps0 cs0 : list nat) (m : nat) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps0
  /\ Forall (fun i => (i < length line_alts)%nat) cs0
  /\ pro_pin ps0 cs0 m
  /\ ((m - 1) `div` length echo_line <= length cs0)%nat.

(* read_ret's non-empty arm, NEW tail: *)
  ∗ turn_lb v (length (proc_upto ps0 cs0 (n + length ws)))
  ∗ ⌜rd_stage ps0 cs0 (n + length ws)⌝
```
i.e. "the writer's cursor is at least the end of the stream of every block the
delivered bytes closed, and the reader's two bounds are good enough to compute
that stream".  The pure refutations (EchoLinks.v, outside the section):
```coq
Lemma wr_blk_read_refute (ps cs ps0 cs0 : list nat) (n P m d : nat) :
  wr_blk ps cs n P -> cs `prefix_of` cs0 ->
  (d < length (line_alts !!! (cs0 !!! length cs)))%nat ->
  (n < m)%nat -> rd_stage ps0 cs0 m ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (length (proc_upto ps0 cs0 m) <= P + d)%nat -> False.
Lemma wr_owed_read_refute (ps cs ps0 cs0 : list nat) (n P m : nat) :
  wr_owed ps cs n P -> (n < m)%nat -> rd_stage ps0 cs0 m ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (cs `prefix_of` cs0 \/ cs0 `prefix_of` cs) ->
  (length (proc_upto ps0 cs0 m) <= P)%nat -> False.
```
(the `wr_pro` arm: the reader's round at `n` is SETTLED (`pro_pin` at `m > n`)
while the writer's is open, so the reader's prologue is strictly longer
(`pro_of_open_done_lt`); the `wr_blk` arm: the block the reader closed is a
whole non-empty alternative of which the writer has `d` bytes out).  The Iris
lemmas the shell spends (EchoLinks.v, in the section; `read_ret` is
`EchoOut.read_ret T`):
```coq
Lemma ewc_owed_read_refute (k : nat) (v : era_pins) (n : nat) (ws : list (list mobs * bv 8)) :
  (0 < length ws)%nat ->
  ewc_owed v n -∗ read_ret T k v n ws -∗ T ∗ ewc_owed v n ∗ read_ret T k v n ws.
Lemma ewc_owed_read_taint (k : nat) (v : era_pins) (n : nat) (ws : list (list mobs * bv 8)) :
  (0 < length ws)%nat -> ewc_owed v n -∗ read_ret T k v n ws -∗ T.
```
and, in the NEW file `iris/EchoLinksBan.v` (requires EchoLinks AND
EchoLinksLine; its `_CoqProject` row is right after `EchoLinksLine.v`), the
same at the shell's TIGHT boundary shapes of SH-LINE-CRED:
```coq
Lemma wr_post_read_refute (ps cs ps0 cs0 : list nat) (n P m a : nat) :
  (a < 3)%nat -> wr_blk ps cs n P ->
  (blkcs cs a (length (line_alts !!! a) - 2) `prefix_of` cs0
   \/ cs0 `prefix_of` blkcs cs a (length (line_alts !!! a) - 2)) ->
  (n < m)%nat -> rd_stage ps0 cs0 m ->
  (ps `prefix_of` ps0 \/ ps0 `prefix_of` ps) ->
  (length (proc_upto ps0 cs0 m) <= P + (length (line_alts !!! a) - 2))%nat -> False.
Lemma ewc_ban_line (v : era_pins) (n : nat) :
  EchoLinks.ewc_ban T v n 0%nat -∗ EchoLinksLine.ewc_line T v n.
Lemma echo_prompt_dollar_ban (k : nat) (v : era_pins) (n : nat) (b : bv 8) (Φ : iProp Σ) :
  b = u_prompt !!! 0%nat ->
  era_pin γ k v -∗ echo_links T γ -∗ EchoLinks.ewc_ban T v n 0%nat -∗
  (EchoLinksLine.ewc_sp_t T v n -∗ Φ) -∗ out_link Uart0 k b Φ.
Lemma ewc_post_read_taint (k : nat) (v : era_pins) (n a : nat) (ws : list (list mobs * bv 8)) :
  (a < 3)%nat -> (0 < length ws)%nat ->
  EchoLinksLine.ewc_post T v n a -∗ read_ret T k v n ws -∗ T.
Lemma ewc_line_read_taint (k : nat) (v : era_pins) (n : nat) (ws : list (list mobs * bv 8)) :
  (0 < length ws)%nat -> EchoLinksLine.ewc_line T v n -∗ read_ret T k v n ws -∗ T.
Lemma ewc_ban_read_taint (k : nat) (v : era_pins) (n : nat) (ws : list (list mobs * bv 8)) :
  (0 < length ws)%nat -> EchoLinks.ewc_ban T v n 0%nat -∗ read_ret T k v n ws -∗ T.
```
In xv6 terms: a shell whose fd 2 is shut never printed its prompt, so a read on
its fd 0 that DELIVERS a byte at that boundary is the taint; the shell's
obligation "after a read at a boundary where the credential is still at p = 0,
refute the non-taint arm" is discharged by `ewc_owed_read_taint` (loose shape),
`ewc_line_read_taint` (tight shape) or `ewc_ban_read_taint` (banner-owed).

## 6. GONE / CHANGED (against base 4ab8f963f), justified

`tools/lemma_diff.py --ref 4ab8f963f`: 6 GONE, no Admitted/admit/Abort, no new
axiom.  GONE: `pro_of_banner` (false), `pro_of_replicate_banner`,
`pro_open_replicate`, `pro_of_replicate_length`, `pro_done_replicate` (the open
round is no longer `replicate j 1`; replaced by the `pro_fail` family above),
`pcount_zero` (false at `ps = []`; no consumer).  None had a consumer outside
the four Echo files.  Statements CHANGED (all listed in sections 2-5):
EchoDisc `pro_alts pro_alts_length pro_more pro_of pro_done pro_tail pro_rounds
pro_more_ne pro_of_good pro_of_pos pro_rounds_group pro_pin_ok pro_grp_cands
elem_of_pro_grp_cands pro_of_first_group pro_tail_group pro_of_group_app
demo_seg_exec demo_seg_fork demo_seg_panic`; EchoOutPure `sess_n_nonnil`;
EchoOut `pending_nonnil proc_upto_round_banner proc_upto_round_banner_open
pro_choice_round1_live turn turn_auth turn_update ein ein_pend read_ret
ein_step_read era_full`; EchoLinks `pro_of_open_snoc_eq pending_n_round_snoc
wr_ban wr_ban_pro wr_ban_byte wr_owed_round0 ewc_ban`.  `pro_more_1` is kept
(as a corollary of `pro_more_cont`).  Lemmas whose OLD statement is not
derivable (`wr_ban_pro` at `P + 18`, `wr_ban_byte` at `ps`, `wr_owed_round0` at
`[]`) are false at the new definition -- the banner is a letter the credential
has not filed yet at `wr_ban`.

## 7. One-line fixes OUTSIDE the four Echo files (for the coordinator to re-apply)

- `iris/EchoLinksLine.v`, `ewc_ban_done_line` PROOF only (statement unchanged):
  destructure `wr_banp .. 18` and use `wr_ban_done ps' cs n P` at
  `iExists (ps' ++ [3%nat]), cs, (P + length u_banner)%nat` (was `wr_ban_pro`
  at `ps`).  (6 lines changed.)
- `iris/UShLine.v:1044`: the `read_ret` destructuring pattern
  `"(#Hcs & #Hps & #HE & %Hbd)"` -> `"(#Hcs & #Hps & #HE & %Hbd & _)"` (the two
  new trailing conjuncts).
- `iris/UShOut.v:129,132` (literal anti-vacuity lemmas, no consumer):
  `sh_pro_stage : length (proc_upto [3%nat] [] (S 0%nat)) = 18%nat` (was `[]`),
  `sh_space_stream : proc_upto [3%nat; 0%nat] [] (S 0%nat) !! 19%nat = Some sh_space_b`
  (was `[0%nat]`).
- `iris/_CoqProject`: one bare row `EchoLinksBan.v` after `EchoLinksLine.v`.
No other U-tier file changed (UInitBanner compiles unchanged: `kinit_ban0_of_eturn`'s
`wr_ban_round0` and `ewc_ban_done` keep their statements).

## 8. GATE

Build `pa3-3` (`./gcp-rocq/vmbuild.sh xv6iris-2-tlw pa3-3`, after `pa3-2` red at
EchoOut.v:1438 and the previous session's `pa3-1`/`pa3-c1..c4`): COMPILED=38,
`grep -c "^Error" /tmp/pa3-3.log` = 0, EXIT=0; VM `make -f CoqMakefile -n`
prints 0 `ROCQ compile`; `make audit-only | grep -v '^make\|^cd ' | md5sum` =
57f7327206c4b276d05035342fea8ecf (the thirteen); `tools/lemma_diff.py --ref
4ab8f963f` = 6 GONE (section 6), no Admitted/admit/Abort, no new axiom (the
brief's `--ref origin/main` would list INIT-DIAG's two new files as GONE, since
this branch is not rebased); `grep Admitted` over the nine touched files: none;
no `∨ True`; `run-on-gcp --check-dumps` clean (RC=0).  Every pure literal fact
is a closed `vm_compute`/`reflexivity` lemma (`pro_of_good`, `pro_of_good_noban`,
`pro_alts_3`, `pro_alts_prefix_det`, the demo witnesses, UShOut's two).

## 9. What the coordinator receives for step 3, and the INIT-DIAG rebase

THE EXACT IRIS LEMMA to pay the shell's '$' from the banner-owed credential:
`EchoLinks.echo_prompt_dollar_ban` (loose shapes, ends in `ewc_sp v n`) or
`EchoLinksBan.echo_prompt_dollar_ban` (ends in `EchoLinksLine.ewc_sp_t T v n`,
the shell loop's own shape); or convert first with `EchoLinks.ewc_ban_owed`
(`ewc_ban v n 0 -∗ ewc_owed v n`) / `EchoLinksBan.ewc_ban_line`
(`ewc_ban T v n 0 -∗ ewc_line T v n`) and use the landed `echo_prompt_dollar` /
`echo_prompt_dollar_line`.  So the top-level `∃ v, era_pin γ k v ∗ (ewc_owed v n
∨ ewc_ban v n 0)` collapses to `ewc_owed v n` by `ewc_ban_owed` on the right arm.

THE EXACT LEMMA to refute an untainted read at an unwritten prompt:
`EchoLinks.ewc_owed_read_taint T k v n ws : 0 < length ws -> ewc_owed v n -∗
read_ret T k v n ws -∗ T` (or `ewc_owed_read_refute`, which hands everything
back), `EchoLinksBan.ewc_line_read_taint` at the tight boundary shape,
`EchoLinksBan.ewc_ban_read_taint` at the banner-owed shape.

EXPECTED BREAKAGE in `iris/EchoLinksPro.v` (INIT-DIAG, origin/main `bdd9faf7f`)
under this change -- statement (S) or proof (P):
- (P) `pro_of_replicate_snoc` -- STATEMENT FALSE now (`pro_more a u_banner`:
  no default banner) and `replicate j 1` is not the open shape.  Replace by
  `pro_of_open_app` + `pro_of_singleton`: `pro_of (g ++ [a]) = pro_of g ++
  pro_alts !!! a` for `~ pro_done g` (this is exactly `EchoLinks.pro_of_open_snoc_eq`,
  now premise-free except `~ pro_done`).
- (S) `wr_pdiag`: `pro_from .. ps = replicate j 1%nat ++ [a]` must become
  `= pro_fail j ++ [3%nat; a]` (the banner letter filed, then the diagnostic);
  the cursor formula `.. + pro_round * j + length u_banner + i` stays right
  (`pro_of_fail_length`, `pro_alts_3`).
- (P) `wr_pdiag_byte`: uses GONE `pro_of_replicate_length`; redo with
  `pro_of_open_app`, `pro_of_fail_length`, `pro_alts_3`.
- (S) `wr_pdiag_1_of_pro`: uses GONE `pro_open_replicate`.  From a bare
  `wr_pro` the open round is any word over {1,3}, so the `pro_fail j ++ [3]`
  shape is NOT derivable; the lemma needs the premise
  `pro_from (pro_idx cs (n div 17)) ps = pro_fail j ++ [3%nat]` (which is what
  `wr_ban_done` produces: `wr_ban_filed`), or `ewc_pro` should be tightened to
  carry it.  Consequently (P) `echo_pdiag_step`'s byte-0 case.
- (P) `wr_pdiag_done_1`: `replicate_S_end` -> `pro_fail_S`
  (`pro_fail (S j) = pro_fail j ++ [3%nat; 1%nat]`).
- (S) `wr_owed_ambiguous`: literals become `wr_pro [3%nat; 0%nat] [3%nat] 17%nat 25%nat
  /\ wr_blk [3%nat; 0%nat] [] 17%nat 20%nat` (round 1 opens with NOTHING
  predicted: 20 + 5 = 25, not 43).
- (P) `ewc_ban_done_pro`: `ewc_ban .. (length u_banner)` now carries
  `wr_banp .. 18 = ∃ ps', ps = ps' ++ [3] ∧ wr_ban ps' ..`; use `wr_ban_done ps'`
  at `iExists (ps' ++ [3%nat])` (the exact fix applied to
  `EchoLinksLine.ewc_ban_done_line`, section 7).
- Unaffected: `pro_alts_1_length`, `pro_alts_2_length`, `pro_round_alts`,
  `pro_alts_lt_of_lookup`, `pending_n_round_wr_pre`, `wr_pdiag_S`, `ewc_pro`,
  `ewc_owed_of_pro`, `ewc_pdiag*` statements, `ewc_pdiag_done_1` statement.
`iris/UInitDiag.v`: consumes only EchoLinksPro's Iris statements (`ewc_pro`,
`ewc_pdiag`, `ewc_pdiag_0`, `echo_pdiag_step`, `ewc_pdiag_done_1`,
`ewc_ban_done_pro`, `ewc_owed_of_pro`) and the literals `pro_alts !!! 1/2 !! j`;
nothing there breaks if EchoLinksPro keeps those statements.
`EchoLinksBan.v`'s `_CoqProject` row: it requires EchoLinksLine (for the
tight shapes), so its row goes after `EchoLinksLine.v`, NOT after
`EchoLinksPro.v`.

## 10. Process notes for a successor

- `run-on-gcp --no-sync --pull-vo` (once, ~1 GB) makes a LOCAL edit loop
  possible: `coqc -R . xv6iris -R ../model-xv6iris Riscv -R ../kernel-rocq Kernel
  -R ../user-rocq User -w -notation-overridden <F>.v` in `iris/` -- EchoOut.v
  compiles in ~20 s, EchoLinks.v in ~12 s, EchoLinksLine.v in ~25 s.  Files
  whose siblings were rebuilt on the VM since the pull fail with "inconsistent
  assumptions" (UShLine here); that is the pull's staleness, not the code.
- `lia` gives "Cannot find witness" on goals containing `n `div` length
  echo_line` with the divisor non-literal in some contexts; `rewrite Hdv` (the
  shape's own div equation) first, or state the bound on `length cs` directly.
- `iFrame "HT"` with a persistent `T` frames INTO every `_ ∨ T` in the goal and
  drops the disjunct; split by hand around `ewc_*`/`read_ret` residues.
- `iCombine` + `rewrite Qp.half_half` did not find the sum on a `mono_nat_auth_own`;
  `iAssert (mono_nat_auth_own γ 1 P) with "[H1 H2]"` via `iEval (rewrite -Qp.half_half)`
  + `iSplitL` does.
