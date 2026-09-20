(* ===================================================================== *)
(*  PipeBoth.v -- THE PIPELINE ROUND'S LEND: the block ledger, the       *)
(*  two-cursor credential family, its two byte steps, its entry and its  *)
(*  four exits, and the consumer's chain.                                *)
(*                                                                       *)
(*  Lane PIPE-2W (design app-pipe.md sections 4.3 / 4.3b, AMENDED by the *)
(*  coordinator on 2026-09-19 after SH-PIPE-ROUND-2's landed             *)
(*  [pipe_turn_one_writer]).  The pure half is [PipeBothPure.v].         *)
(*                                                                       *)
(*  WHY THE TWO-CURSOR LEASE IS THE ROUND'S LEND AND NOT THE [PBoth]     *)
(*  ARM'S.  [EchoOut.turn v P] is HALF a [mono_nat] authority, so there  *)
(*  is one console writer at a time; and sh's runcmd child forks TWICE   *)
(*  without knowing which of its children will write the round's block   *)
(*  (the left one at [PExecL], the right one at [PRan] or [PExecR], both *)
(*  at [PBoth]).  So the block credential can never be lent at the forks *)
(*  on any arm -- unless what is lent is a SHARED family with one cursor *)
(*  per child, which is what this file builds.  All four block shapes    *)
(*  come out of it: the LEFT child's console bytes are always a prefix   *)
(*  of [dg_execL], the RIGHT child's a prefix of ONE list [R] fixed at   *)
(*  its own first byte (the LINE at [PRan], [dg_execR] at [PExecR]), and *)
(*  the block written so far is [PipeBothPure.pend2 R sel].              *)
(*                                                                       *)
(*  WHAT TIES THE CLAIM TO THE FAMILY: A LEDGER OF THE BLOCK'S BYTES.    *)
(*  The round's alternative cannot be filed in [cs] at the block's first *)
(*  byte -- two writers decide the interleaving byte by byte and a       *)
(*  [mono_list] entry is immutable -- so while the block is in progress  *)
(*  the choice list is ONE SHORT and the claim reads the block off a     *)
(*  SECOND ledger instead: [blk_auth] / [blk_lb], a [mono_list] of the   *)
(*  bytes written so far.  The SPLIT ([sel], the two cursors) lives in   *)
(*  the family, not in the ledger, and that is not an accident:          *)
(*  [PipeBothPure.pend_both_not_inj] shows the block's BYTES do not      *)
(*  determine the split (the two diagnostics share their first five      *)
(*  bytes, so a six-byte block is the merge of [dg_execL]'s first six    *)
(*  AND of one left byte after [dg_execR]'s first five, and the next     *)
(*  LEFT byte differs), so a claim carrying only the bytes could not     *)
(*  decide which byte a writer at its own cursor may append -- while a   *)
(*  family carrying only the split could not be tied to the claim's own  *)
(*  [o_w].  BOTH are needed, and each covers what the other cannot.      *)
(*                                                                       *)
(*  WHERE THE LEDGER'S NAME LIVES (lanes PIPE-2W-2 / PIPE-2W-3).  The   *)
(*  claim and the two writers must MEAN THE SAME GHOST, so its gname     *)
(*  comes off the FIXED PART: [AppPipe.app_pipe]'s [app_fixed] is        *)
(*  [PipeOut.pipe_gn] -- echo's fixed part PAIRED with a gname of its    *)
(*  own, upstream's FILE application ([FileOut.file_gn]) verbatim -- and  *)
(*  the per-era record [PipeOut.pipe_era] carries the era's block ledger  *)
(*  [pe_blk] and the CURRENT ROUND's exclusive ghost [pe_cur].  A round's *)
(*  own ledger is minted when its block OPENS (a [mono_list] cannot be    *)
(*  reset) and its gname is pinned by [pe_cur] in two halves: the claim's *)
(*  non-taint arm holds one and the round's family the other, so a STALE  *)
(*  family from an earlier round cannot step ([PipeOut.cur_half_agree]),  *)
(*  and between rounds the claim holds the WHOLE ghost, which is what     *)
(*  makes the opening step exclusive ([PipeOut.cur_half_excl]).  So the   *)
(*  three claim-side steps are PROVED here ([pblk2_ecl_holds]), out of    *)
(*  [PipeOut.pecl_blk2_open] (the block's first byte, which mints the     *)
(*  round's ledger and splits the ghost), [_byte] (every further byte,    *)
(*  left or right) and [_file] (the prompt's first byte, which files the  *)
(*  round's code and rejoins the ghost).                                 *)
(*                                                                       *)
(*  THE LEDGER COSTS THE FUNCTOR LIST NOTHING: the bytes ride the era's  *)
(*  own echoed-list camera ([EchoOut.echoOutG]'s [eo_El]), so no class   *)
(*  and no functor row is added when the name arrives.                   *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map
        invariants.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import PipeDisc.
Require Import PipeDiscDec.
Require Import PipeOutPure.
Require Import PipeBothPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
(* as in PipeOut / PipeLinksLine: the Sail imports leave string_scope on
   top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S0  THE PURE BRIDGES                                                  *)
(*                                                                       *)
(*  [PipeBothPure.wr_blk2_p] and [PipeLinksLine.wr_blk_p] are the same    *)
(*  block shape read twice: the round's two writers', and the ordinary    *)
(*  block writer's.  They live in different files, so the bridge is here. *)
(* ===================================================================== *)

Lemma wr_blk2_p_blk (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) :
  wr_blk2_p ps cs I P R sel c1 c2 -> wr_blk_p ps cs I P.
Proof using.
  intros (Hne & Hr & Hq & _ & Hpin & HP & _). rewrite /wr_blk_p.
  pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
  split_and!; [exact Hpin | exact Hr | lia | exact HP].
Qed.

Lemma wr_blk_p_blk2 (ps cs : list nat) (I : list (bv 8)) (P : nat)
    (R : list (bv 8)) :
  wr_blk_p ps cs I P -> pboth_line I ->
  wr_blk2_p ps cs I P R [] 0%nat 0%nat.
Proof using.
  intros Hw Hl. pose proof (wr_blk_nonnil_p ps cs I P Hw) as Hne.
  destruct Hw as (Hpin & Hr & Hn & HP). rewrite /wr_blk2_p.
  split_and!; try done; cbn [count_true length]; lia.
Qed.

(* THE ROUND'S CODE, and the block it owes.  [pblk2_code I R sel a] is
   what the FILER proves at the prompt: the round's alternative is [a],
   the line admits it, it does not reopen the prologue, and the block it
   owes is exactly what the two cursors wrote. *)
Definition pblk2_code (I : list (bv 8)) (R : list (bv 8))
    (sel : list bool) (a : nat) : Prop :=
  palt_ok (pline_at I) (palt_of a)
  /\ palt_panic (palt_of a) = false
  /\ pcont (pline_at I) (palt_of a) = pend2 R sel ++ u_prompt.

Lemma pblk2_code_pab (I : list (bv 8)) (R : list (bv 8)) (sel : list bool)
    (a : nat) :
  pblk2_code I R sel a -> pab I a = pend2 R sel ++ u_prompt.
Proof using.
  intros (Hok & _ & Hc). by rewrite (pab_is I a Hok).
Qed.

Lemma pblk2_code_papr (I : list (bv 8)) (R : list (bv 8)) (sel : list bool)
    (a : nat) :
  pblk2_code I R sel a -> papr I a.
Proof using. intros (Hok & Hpan & _). by split. Qed.

Lemma pblk2_code_len (I : list (bv 8)) (R : list (bv 8)) (sel : list bool)
    (a : nat) (c1 c2 : nat) :
  sel_wf2 R sel -> length sel = (c1 + c2)%nat ->
  pblk2_code I R sel a ->
  length (pab I a) = S (S (c1 + c2))%nat.
Proof using.
  intros Hwf Hlen Hc.
  assert (Hup : length u_prompt = 2%nat) by (by vm_compute).
  rewrite (pblk2_code_pab I R sel a Hc) length_app.
  rewrite (pend2_length R sel Hwf) Hlen Hup. lia.
Qed.

(* ---- THE FOUR CODES, each proved from the two cursors alone ---- *)

Lemma pblk2_code_ran (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws ->
  count_true sel = 0%nat ->
  length sel = length (wl_line (drop 1 ws)) ->
  pblk2_code I (wl_line (drop 1 ws)) sel (palt_code PRan).
Proof using.
  intros Hl Hc Hlen. rewrite /pblk2_code (palt_of_code PRan) Hl.
  split_and!; [by apply palt_ok_LPipe_ran | exact palt_panic_ran |].
  rewrite (pcont_ran ws).
  by rewrite (pend2_right_only (wl_line (drop 1 ws)) sel Hc Hlen).
Qed.

Lemma pblk2_code_execL (I : list (bv 8)) (ws : list (list (bv 8)))
    (R : list (bv 8)) (sel : list bool) :
  pline_at I = LPipe ws ->
  count_true sel = length dg_execL -> length sel = length dg_execL ->
  pblk2_code I R sel (palt_code PExecL).
Proof using.
  intros Hl Hc Hlen. rewrite /pblk2_code (palt_of_code PExecL) Hl.
  split_and!; [by apply palt_ok_LPipe_execL | exact palt_panic_execL |].
  rewrite (pcont_execL ws). by rewrite (pend2_left_only R sel Hc Hlen).
Qed.

Lemma pblk2_code_execR (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws ->
  count_true sel = 0%nat -> length sel = length dg_execR ->
  pblk2_code I dg_execR sel (palt_code PExecR).
Proof using.
  intros Hl Hc Hlen. rewrite /pblk2_code (palt_of_code PExecR) Hl.
  split_and!; [by apply palt_ok_LPipe_execR | exact palt_panic_execR |].
  rewrite (pcont_execR ws).
  by rewrite (pend2_right_only dg_execR sel Hc Hlen).
Qed.

(* ...AND THE ONE PLACE A [PBoth] CODE IS EVER BUILT: out of the
   selector's length and its count of trues, both of which the two
   cursors carry. *)
Lemma pblk2_code_both (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws ->
  count_true sel = length dg_execL ->
  length sel = (length dg_execL + length dg_execR)%nat ->
  pblk2_code I dg_execR sel (palt_code (PBoth sel)).
Proof using.
  intros Hl Hc Hlen. rewrite /pblk2_code (palt_of_code (PBoth sel)) Hl.
  destruct (pend2_both_full ws sel Hc Hlen) as [Hok Hcont].
  split_and!; [exact Hok | exact (palt_panic_both sel) | exact Hcont].
Qed.

(* THE WITNESS A BYTE IS WRITTEN AGAINST.  The claim reads an UNFILED
   block against some admissible alternative of the round's line whose
   continuation the block is a prefix of ([PipeOut.pblk_open]); mid-block
   the round's own code is not decided yet -- that is the whole point of
   the ledger -- so what a byte step spends is this existential.  The
   walk knows the round's FINAL code ([pblk2_code]) and every prefix of
   the block is covered by it, [pblk2_wit_mono]. *)
Definition pblk2_wit (I R : list (bv 8)) (sel : list bool) : Prop :=
  exists a : nat,
    palt_ok (pline_at I) (palt_of a)
    /\ palt_panic (palt_of a) = false
    /\ pend2 R sel `prefix_of` pcont (pline_at I) (palt_of a).

Lemma pblk2_wit_of_code (I R : list (bv 8)) (sel : list bool) (a : nat) :
  pblk2_code I R sel a -> pblk2_wit I R sel.
Proof using.
  intros (Hok & Hpan & Hc). exists a.
  split_and!; [exact Hok | exact Hpan |].
  rewrite Hc. apply prefix_app_r. reflexivity.
Qed.

Lemma count_true_replicate_true (n : nat) :
  count_true (replicate n true) = n.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite replicate_S. cbn [count_true]. by rewrite IH.
Qed.

Lemma count_true_replicate_false (n : nat) :
  count_true (replicate n false) = 0%nat.
Proof using.
  induction n as [| n IH]; [reflexivity |].
  rewrite replicate_S. cbn [count_true]. by rewrite IH.
Qed.

(* THE PADDED SELECTOR'S LENGTH, WITH THE TWO BOUNDS ABSTRACT.  [L] and
   [R] must be VARIABLES here: with [length dg_execL] in the goal,
   [rewrite !length_app] walks into [dg_execL = wl_line dg_exec] and
   splits it into the lengths of its words, while the hypotheses keep
   [length dg_execL] whole -- and then [lia] has two different atoms for
   one number and answers "Cannot find witness". *)
Lemma length_pad (sel : list bool) (L R : nat) :
  (count_true sel <= L)%nat -> (length sel - count_true sel <= R)%nat ->
  length (sel ++ replicate (L - count_true sel) true
              ++ replicate (R - (length sel - count_true sel)) false)
  = (L + R)%nat.
Proof using.
  intros H1 H2. pose proof (count_true_le sel) as Hcle.
  rewrite !length_app !length_replicate. lia.
Qed.

Lemma pblk2_wit_mono (I R : list (bv 8)) (sel sel' : list bool) :
  sel `prefix_of` sel' -> sel_wf2 R sel' ->
  pblk2_wit I R sel' -> pblk2_wit I R sel.
Proof using.
  intros Hp Hwf (a & Hok & Hpan & Hpref). exists a.
  split_and!; [exact Hok | exact Hpan |].
  etrans; [exact (pend2_prefix R sel sel' Hp Hwf) | exact Hpref].
Qed.

(* THE [PBoth] ROUND'S WITNESS, AT EVERY WELL-FORMED SELECTOR: pad the
   selector out with the left side's remaining bytes and then the right
   side's, and the round's own [PBoth] code covers what has been written
   so far.  This is what the CONCURRENT steps (S7) spend, where the
   selector lives under the invariant's existential and no single writer
   knows it. *)
Lemma pblk2_wit_both (I : list (bv 8)) (ws : list (list (bv 8)))
    (sel : list bool) :
  pline_at I = LPipe ws -> sel_wf2 dg_execR sel ->
  pblk2_wit I dg_execR sel.
Proof using.
  intros Hl [H1 H2].
  pose proof (count_true_le sel) as Hcle.
  set (sel' := sel ++ replicate (length dg_execL - count_true sel) true
                   ++ replicate (length dg_execR
                                 - (length sel - count_true sel)) false).
  assert (Hc' : count_true sel' = length dg_execL).
  { rewrite /sel' !count_true_app count_true_replicate_true
      count_true_replicate_false. lia. }
  assert (Hlen' : length sel'
                  = (length dg_execL + length dg_execR)%nat).
  { exact (length_pad sel (length dg_execL) (length dg_execR) H1 H2). }
  apply (pblk2_wit_mono I dg_execR sel sel').
  - rewrite /sel'. by eexists.
  - rewrite /sel_wf2 Hc' Hlen'. lia.
  - exact (pblk2_wit_of_code I dg_execR sel' (palt_code (PBoth sel'))
             (pblk2_code_both I ws sel' Hl Hc' Hlen')).
Qed.

Section pipe_both.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation PT := (echo_taint γ).

  (* the record equation, as in [PipeLinks]: the port's claim IS the
     pipeline application's *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).

  Lemma pbchist_at0 (kk : nat) (hh : list mobs)
      (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = pecl g kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ================================================================= *)
  (*  S1  THE ROUND'S LEDGER lives at the CLAIM                         *)
  (*                                                                   *)
  (*  [PipeOut.rblk_auth] / [rblk_lb] at the gname minted when the      *)
  (*  block opens, and [PipeOut.cur_half] for the round it belongs to.  *)
  (*  Nothing is a parameter here any more: see the header.             *)
  (* ================================================================= *)

  (* ================================================================= *)
  (*  S2  THE TWO CURSORS                                               *)
  (*                                                                   *)
  (*  One per child, EXCLUSIVE, in halves: ONE IS LENT TO EACH CHILD AT *)
  (*  THE FORKS, which is what the round can do without knowing which   *)
  (*  child will write.                                                 *)
  (* ================================================================= *)

  Definition wcur (gc : gname) (q : Qp) (c : nat) : iProp Σ :=
    ghost_var gc q c.

  Global Instance wcur_timeless gc q c : Timeless (wcur gc q c).
  Proof using . rewrite /wcur. apply _. Qed.

  Lemma wcur_agree gc q1 q2 c1 c2 :
    wcur gc q1 c1 -∗ wcur gc q2 c2 -∗ ⌜c1 = c2⌝.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.

  Lemma wcur_update gc c1 c2 m :
    wcur gc (1/2) c1 -∗ wcur gc (1/2) c2 ==∗ wcur gc (1/2) m ∗ wcur gc (1/2) m.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iMod (ghost_var_update_halves m with "H1 H2") as "[$ $]".
  Qed.

  Lemma wcur_excl gc c1 c2 : wcur gc 1 c1 -∗ wcur gc 1 c2 -∗ False.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
  Qed.

  (* ================================================================= *)
  (*  S3  THE FAMILY                                                    *)
  (* ================================================================= *)

  (* WHAT TIES THE FAMILY TO THE CLAIM.  Before the block's first byte
     there is no round ledger yet and the claim owns the WHOLE
     current-round ghost; [sel = []] is exactly that state, and the first
     byte's step is what mints the ledger and splits the ghost.  After
     it, the family holds the writer's half AND the ledger's lower bound
     on the bytes written so far -- the half is what makes it the CURRENT
     round's family and not a stale one. *)
  Definition pblk_led (k : nat) (I R : list (bv 8)) (sel : list bool)
    : iProp Σ :=
    (⌜sel = []⌝ ∨ ∃ (w : pipe_era) (gb : gname),
        pera_pin g k w ∗ cur_half w (1/2) (nlines I - 1)%nat gb
        ∗ rblk_lb gb (pend2 R sel))%I.

  Global Instance pblk_led_timeless k I R sel :
    Timeless (pblk_led k I R sel).
  Proof using .
    rewrite /pblk_led.
    apply bi.or_timeless; [apply bi.pure_timeless |].
    apply bi.exist_timeless; intro w.
    apply bi.exist_timeless; intro gb.
    apply bi.sep_timeless; [apply pera_pin_timeless |].
    apply bi.sep_timeless;
      [apply cur_half_timeless | apply rblk_lb_timeless].
  Qed.

  Definition pwc_blk2 (k : nat) (v : era_pins) (I : list (bv 8))
      (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ ∗ ⌜wr_tail_p ps cs⌝
        ∗ turn v (P + c1 + c2)%nat ∗ ps_lb v ps ∗ cs_lb v cs
        ∗ pblk_led k I R sel ∗ inp_lb v I) ∨ PT)%I.

  (* NAME THE LEAVES, do not search: the tree carries 455 [Timeless]
     instances under transparent definitions and one [apply _] at this
     altitude tries nearly all of them ([PipeLinksLine]'s [tl_leaf]). *)
  Global Instance pwc_blk2_timeless k v I R sel c1 c2 :
    Timeless (pwc_blk2 k v I R sel c1 c2).
  Proof using .
    rewrite /pwc_blk2.
    apply bi.or_timeless; [| apply echo_taint_timeless].
    apply bi.exist_timeless; intro ps.
    apply bi.exist_timeless; intro cs.
    apply bi.exist_timeless; intro P.
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply bi.pure_timeless |].
    apply bi.sep_timeless; [apply turn_timeless |].
    apply bi.sep_timeless; [apply ps_lb_timeless |].
    apply bi.sep_timeless; [apply cs_lb_timeless |].
    apply bi.sep_timeless; [apply pblk_led_timeless | apply inp_lb_timeless].
  Qed.

  Lemma pwc_blk2_taint k v I R sel c1 c2 : PT -∗ pwc_blk2 k v I R sel c1 c2.
  Proof using . iIntros "HT". rewrite /pwc_blk2. by iRight. Qed.

  (* THE ENTRY: what sh's runcmd child holds for the round is the block
     credential at its first byte ([PipeLinksLine.pwc_lend], i.e.
     [lk_lcred]'s owed arm at an [LPipe] line); it IS the family at the
     empty selector, at ANY right-hand source. *)
  Lemma pwc_blk2_of_lend (k : nat) (v : era_pins) (I : list (bv 8))
      (R : list (bv 8)) :
    pboth_line I ->
    pwc_lend g k v I -∗ pwc_blk2 k v I R [] 0%nat 0%nat.
  Proof using .
    intros Hl. iIntros "Hc". rewrite /pwc_lend /pwc_blk2.
    iDestruct "Hc" as "[Hx | #HT]"; last by iRight.
    iDestruct "Hx" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P.
    rewrite !Nat.add_0_r. iFrame "Htn Hps Hcs HE".
    iSplitR;
      [iPureIntro; exact (wr_blk_p_blk2 ps cs I P R (proj1 Hw) Hl) |].
    iSplitR; [iPureIntro; exact (proj2 Hw) |].
    rewrite /pblk_led. by iLeft.
  Qed.

  (* ================================================================= *)
  (*  S4  WHAT THE CLAIM OWES: the three steps of the unfiled block      *)
  (*                                                                   *)
  (*  [PipeOut.pecl_step_write]'s twins at the claim's SECOND arm, in    *)
  (*  the same shape ([==∗] over [pecl], so they compose at any mask,    *)
  (*  which is what lets S7's concurrent step open an invariant around   *)
  (*  them).  These are what this lane leaves owed.                      *)
  (* ================================================================= *)

  Definition pblk2_ecl_L : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (b : bv 8),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜dg_execL !! c1 = Some b⌝ -∗ ⌜pblk2_wit I R (sel ++ [true])⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ pblk_led k I R sel -∗ inp_lb v I -∗
        pecl g k ho H ==∗
          pecl g k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat
              ∗ pblk_led k I R (sel ++ [true])) ∨ PT))%I.

  Definition pblk2_ecl_R : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (b : bv 8),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜R !! c2 = Some b⌝ -∗ ⌜Forall nodollar R⌝ -∗
        ⌜pblk2_wit I R (sel ++ [false])⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ pblk_led k I R sel -∗ inp_lb v I -∗
        pecl g k ho H ==∗
          pecl g k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat
              ∗ pblk_led k I R (sel ++ [false])) ∨ PT))%I.

  (* ...AND THE FILING, at the prompt's own first byte: the only step
     that moves [cs], and the only place a round's code is built. *)
  Definition pblk2_ecl_file : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (a : nat) (b : bv 8),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜pblk2_code I R sel a⌝ -∗ ⌜sel <> []⌝ -∗
        ⌜b = u_prompt !!! 0%nat⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ pblk_led k I R sel -∗ inp_lb v I -∗
        pecl g k ho H ==∗
          pecl g k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat ∗ cs_lb v (cs ++ [a])) ∨ PT))%I.

  Definition pblk2_ecl : iProp Σ :=
    (pblk2_ecl_L ∗ pblk2_ecl_R ∗ pblk2_ecl_file)%I.

  Global Instance pblk2_ecl_L_persistent : Persistent pblk2_ecl_L.
  Proof using . rewrite /pblk2_ecl_L. apply _. Qed.
  Global Instance pblk2_ecl_R_persistent : Persistent pblk2_ecl_R.
  Proof using . rewrite /pblk2_ecl_R. apply _. Qed.
  Global Instance pblk2_ecl_file_persistent : Persistent pblk2_ecl_file.
  Proof using . rewrite /pblk2_ecl_file. apply _. Qed.
  Global Instance pblk2_ecl_persistent : Persistent pblk2_ecl.
  Proof using .
    rewrite /pblk2_ecl.
    apply bi.sep_persistent; [apply pblk2_ecl_L_persistent |].
    apply bi.sep_persistent;
      [apply pblk2_ecl_R_persistent | apply pblk2_ecl_file_persistent].
  Qed.

  Lemma pblk2_ecl_l : pblk2_ecl -∗ pblk2_ecl_L.
  Proof using . by iIntros "($ & _ & _)". Qed.
  Lemma pblk2_ecl_r : pblk2_ecl -∗ pblk2_ecl_R.
  Proof using . by iIntros "(_ & $ & _)". Qed.
  Lemma pblk2_ecl_f : pblk2_ecl -∗ pblk2_ecl_file.
  Proof using . by iIntros "(_ & _ & $)". Qed.

  (* ----------------------------------------------------------------- *)
  (*  ...AND WHAT THE CLAIM PAYS: the three steps, at [PipeOut]'s own    *)
  (*  four.  The first byte of the block OPENS the round (mints its      *)
  (*  ledger, splits [pe_cur]); every further byte appends to that       *)
  (*  ledger under the writer's half; the prompt's first byte files the  *)
  (*  round's code and rejoins the ghost.                                *)
  (* ----------------------------------------------------------------- *)

  Lemma pblk2_ecl_L_holds : ⊢ pblk2_ecl_L.
  Proof using .
    rewrite /pblk2_ecl_L. iModIntro.
    iIntros (k v ho H I R ps cs P sel c1 c2 b).
    iIntros "%Hw %Htl %Hb %Hwit #Hpin Htn #Hps #Hcs Hled #HE Hcl".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt & _ & _).
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (_ & Hstep).
    assert (Hnd : nodollar b)
      by exact (Forall_lookup_1 _ _ _ _ dg_execL_nodollar Hb).
    destruct Hwit as (a & Hok & Hpan & Hpref).
    rewrite /pline_at in Hok, Hpan, Hpref. rewrite Hstep in Hpref.
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    iDestruct "Hled" as "[%Hnil | Hled]".
    - (* THE BLOCK'S FIRST BYTE: the round's ledger is minted here *)
      subst sel.
      assert (Hc10 : c1 = 0%nat) by (cbn [count_true] in Hcnt; lia).
      assert (Hc20 : c2 = 0%nat) by (cbn [length] in Hlen; lia).
      subst c1 c2.
      rewrite (pend2_nil R) in Hpref. cbn [app] in Hpref.
      assert (Hb0 : pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat))
                      (palt_of a) !! 0%nat = Some b).
      { destruct Hpref as [z Hz]. rewrite Hz. reflexivity. }
      assert (Hle : (nlines I <= S (length cs))%nat) by lia.
      iMod (pecl_blk2_open g k v P a b ps cs I ho H Hne Hr Hle Hpp HP
              Hok Hpan Hb0 Hnd with "Hpin [Htn] Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      (* [replace P with ...] would rewrite P inside [Htn] too -- the
         Iris context is part of the Coq goal.  Convert the INDEX. *)
      { iExactEq "Htn". f_equal. cbn [count_true]. lia. }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[Hx | #HT]"; [| by iRight].
      iDestruct "Hx" as (w gb) "(Htn & #Hpera & Hcur & #Hrlb & _ & _ & _)".
      iLeft. replace (S (P + 0 + 0))%nat with (S P) by lia. iFrame "Htn".
      rewrite /pblk_led. iRight. iExists w, gb. iFrame "Hpera Hcur".
      rewrite Hstep (pend2_nil R). cbn [app]. iFrame "Hrlb".
    - (* A FURTHER BYTE: the round's own ledger, under the writer's half *)
      iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
      iMod (pecl_blk2_byte g k v w gb P (nlines I - 1)%nat a b
              (pend2 R sel) ps cs I ho H Hne Hr eq_refl Hq Hpp HP
              Hok Hpan Hpref Hnd
              with "Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
          by (rewrite Hlb; lia). iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[(Htn & Hcur & #Hrlb') | #HT]"; [| by iRight].
      iLeft.
      replace (S (P + c1 + c2))%nat
        with (S (P + length (pend2 R sel)))%nat by (rewrite Hlb; lia).
      iFrame "Htn". rewrite /pblk_led. iRight. iExists w, gb.
      iFrame "Hpera Hcur". rewrite Hstep. iFrame "Hrlb'".
  Qed.

  Lemma pblk2_ecl_R_holds : ⊢ pblk2_ecl_R.
  Proof using .
    rewrite /pblk2_ecl_R. iModIntro.
    iIntros (k v ho H I R ps cs P sel c1 c2 b).
    iIntros "%Hw %Htl %Hb %HndR %Hwit #Hpin Htn #Hps #Hcs Hled #HE Hcl".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt & _ & _).
    pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    destruct (wr_blk2_step_R ps cs I P R sel c1 c2 b Hw Hb) as (_ & Hstep).
    assert (Hnd : nodollar b)
      by exact (Forall_lookup_1 _ _ _ _ HndR Hb).
    destruct Hwit as (a & Hok & Hpan & Hpref).
    rewrite /pline_at in Hok, Hpan, Hpref. rewrite Hstep in Hpref.
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    iDestruct "Hled" as "[%Hnil | Hled]".
    - subst sel.
      assert (Hc10 : c1 = 0%nat) by (cbn [count_true] in Hcnt; lia).
      assert (Hc20 : c2 = 0%nat) by (cbn [length] in Hlen; lia).
      subst c1 c2.
      rewrite (pend2_nil R) in Hpref. cbn [app] in Hpref.
      assert (Hb0 : pcont (pline_of (bodies_of I !!! (nlines I - 1)%nat))
                      (palt_of a) !! 0%nat = Some b).
      { destruct Hpref as [z Hz]. rewrite Hz. reflexivity. }
      assert (Hle : (nlines I <= S (length cs))%nat) by lia.
      iMod (pecl_blk2_open g k v P a b ps cs I ho H Hne Hr Hle Hpp HP
              Hok Hpan Hb0 Hnd with "Hpin [Htn] Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { replace P with (P + 0 + 0)%nat by lia. iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[Hx | #HT]"; [| by iRight].
      iDestruct "Hx" as (w gb) "(Htn & #Hpera & Hcur & #Hrlb & _ & _ & _)".
      iLeft. replace (S (P + 0 + 0))%nat with (S P) by lia. iFrame "Htn".
      rewrite /pblk_led. iRight. iExists w, gb. iFrame "Hpera Hcur".
      rewrite Hstep (pend2_nil R). cbn [app]. iFrame "Hrlb".
    - iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
      iMod (pecl_blk2_byte g k v w gb P (nlines I - 1)%nat a b
              (pend2 R sel) ps cs I ho H Hne Hr eq_refl Hq Hpp HP
              Hok Hpan Hpref Hnd
              with "Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE Hcl")
        as "(Hcl & Hret)".
      { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
          by (rewrite Hlb; lia). iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[(Htn & Hcur & #Hrlb') | #HT]"; [| by iRight].
      iLeft.
      replace (S (P + c1 + c2))%nat
        with (S (P + length (pend2 R sel)))%nat by (rewrite Hlb; lia).
      iFrame "Htn". rewrite /pblk_led. iRight. iExists w, gb.
      iFrame "Hpera Hcur". rewrite Hstep. iFrame "Hrlb'".
  Qed.

  Lemma pblk2_ecl_file_holds : ⊢ pblk2_ecl_file.
  Proof using .
    rewrite /pblk2_ecl_file. iModIntro.
    iIntros (k v ho H I R ps cs P sel c1 c2 a b).
    iIntros "%Hw %Htl %Hcode %Hnn %Hbv #Hpin Htn #Hps #Hcs Hled #HE Hcl".
    pose proof Hw as (Hne & Hr & Hq & Hline & Hpp & HP & Hlen & Hcnt & _ & _).
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    pose proof Hcode as (Hok & Hpan & Hcont).
    rewrite /pline_at in Hok, Hpan, Hcont.
    assert (Hlb : length (pend2 R sel) = (c1 + c2)%nat)
      by (rewrite (pend2_length R sel Hwf); exact Hlen).
    iDestruct "Hled" as "[%Hnil | Hled]"; [by destruct (Hnn Hnil) |].
    iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
    iMod (pecl_blk2_file g k v w gb P (nlines I - 1)%nat a b
            (pend2 R sel) ps cs I ho H Hne Hr eq_refl Hq Hpp HP
            Hok Hpan Hcont Hbv
            with "Hpin Hpera [Htn] Hcur Hrlb Hps Hcs HE Hcl")
      as "(Hcl & Hret)".
    { replace (P + length (pend2 R sel))%nat with (P + c1 + c2)%nat
        by (rewrite Hlb; lia). iExact "Htn". }
    iModIntro. iFrame "Hcl".
    iDestruct "Hret" as "[(Htn & _ & #Hcs' & _) | #HT]"; [| by iRight].
    iLeft.
    replace (S (P + c1 + c2))%nat
      with (S (P + length (pend2 R sel)))%nat by (rewrite Hlb; lia).
    iFrame "Htn Hcs'".
  Qed.

  (* THE LANE'S DEBT, PAID *)
  Lemma pblk2_ecl_holds : ⊢ pblk2_ecl.
  Proof using .
    rewrite /pblk2_ecl.
    iSplit; [iApply pblk2_ecl_L_holds |].
    iSplit; [iApply pblk2_ecl_R_holds | iApply pblk2_ecl_file_holds].
  Qed.

  (* ================================================================= *)
  (*  S5  THE TWO BYTE STEPS, at the family held LINEARLY               *)
  (*                                                                   *)
  (*  THE PREMISE IS THE TAINT LINK ALONE, not [PipeLinks.pipe_links].  *)
  (*  Introducing the six-component bundle with an intuitionistic intro *)
  (*  pattern sends the [Persistent] search into its wand chains and it *)
  (*  does not return in THIS file's cone -- durable-notes, the entry   *)
  (*  on a bundle of wands hanging the Persistent search; the same      *)
  (*  tactic is fine in [PipeLinksLine].  The taint link is             *)
  (*  [box]-headed with its own instance, so it answers at once, and it *)
  (*  is all these lemmas ever spend; a caller projects it with         *)
  (*  [PipeLinks.pipe_links_taint].                                     *)
  (* ================================================================= *)

  Lemma pblk2_step_L (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (b : bv 8) (Φ : iProp Σ) :
    dg_execL !! c1 = Some b ->
    pblk2_wit I R (sel ++ [true]) ->
    pblk2_ecl_L -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 -∗
    (pwc_blk2 k v I R (sel ++ [true]) (S c1) c2 -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hb Hwit. iIntros "#HL #Ht #Hpin Hc HΦ".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply pwc_blk2_taint. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HL" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /pwc_blk2.
    iDestruct "Hret" as "[[Htn Hled'] | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
    replace (P + S c1 + c2)%nat with (S (P + c1 + c2))%nat by lia.
    iFrame "Htn". iPureIntro. by split.
  Qed.

  Lemma pblk2_step_R (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (b : bv 8) (Φ : iProp Σ) :
    R !! c2 = Some b ->
    Forall nodollar R ->
    pblk2_wit I R (sel ++ [false]) ->
    pblk2_ecl_R -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 -∗
    (pwc_blk2 k v I R (sel ++ [false]) c1 (S c2) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hb HndR Hwit. iIntros "#HR #Ht #Hpin Hc HΦ".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply pwc_blk2_taint. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    destruct (wr_blk2_step_R ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HR" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /pwc_blk2.
    iDestruct "Hret" as "[[Htn Hled'] | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
    replace (P + c1 + S c2)%nat with (S (P + c1 + c2))%nat by lia.
    iFrame "Htn". iPureIntro. by split.
  Qed.

  (* ================================================================= *)
  (*  S6  THE EXIT: the prompt's own first byte files the round's code   *)
  (*                                                                   *)
  (*  ONE lemma at FOUR instances ([pblk2_code_ran] / [_execL] /        *)
  (*  [_execR] / [_both]).  What comes out is the ordinary block        *)
  (*  credential one byte from its end -- exactly                       *)
  (*  [PipeLinksLine.pwc_blk_sp]'s argument -- so the round rejoins the *)
  (*  shared vocabulary at [pwc_sp_t] and sh's walk continues unchanged. *)
  (* ================================================================= *)

  Lemma pblk2_exit (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (a : nat) (b : bv 8) (Φ : iProp Σ) :
    pblk2_code I R sel a ->
    sel <> [] ->
    b = u_prompt !!! 0%nat ->
    pblk2_ecl_file -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 -∗
    (pwc_sp_t g k v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hcode Hnn Hb. iIntros "#HF #Ht #Hpin Hc HΦ".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /pwc_sp_t. by iRight. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    pose proof Hw as (_ & _ & _ & _ & _ & _ & Hlen & _).
    assert (Hpapr : papr I a) by exact (pblk2_code_papr I R sel a Hcode).
    assert (Hab : length (pab I a) = S (S (c1 + c2))%nat)
      by exact (pblk2_code_len I R sel a c1 c2 Hwf Hlen Hcode).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HF" $! k v (default [] o) H I R ps cs P sel c1 c2 a b
            with "[//] [//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ".
    iDestruct "Hret" as "[[Htn #Hcs'] | #HT]";
      last by (rewrite /pwc_sp_t; iRight).
    iApply (pwc_blk_sp g k v I a Hpapr).
    rewrite /pwc_blk Hab. iLeft. iExists ps, cs, P.
    replace (S (S (c1 + c2)) - 1)%nat with (S (c1 + c2))%nat by lia.
    cbn [blkcs_p].
    replace (P + S (c1 + c2))%nat with (S (P + c1 + c2))%nat by lia.
    iFrame "Htn Hps HE Hcs'". iPureIntro.
    split; [exact (wr_blk2_p_blk ps cs I P R sel c1 c2 Hw) | exact Htl].
  Qed.

  (* ================================================================= *)
  (*  S7  THE CONCURRENT FORM: the family in an invariant, one cursor   *)
  (*      half per child                                                *)
  (*                                                                   *)
  (*  Neither child can hold the family between its own bytes, so it    *)
  (*  lives in an invariant keyed by the two cursors' gnames and each   *)
  (*  child holds half of its own cursor; the step opens the invariant  *)
  (*  INSIDE the link's own fancy update.  That is why the claim's      *)
  (*  steps (S4) are BASIC updates, and why the invariant's namespace   *)
  (*  must be disjoint from the port's.                                 *)
  (* ================================================================= *)

  Definition blk2_inv (N : namespace) (k : nat) (v : era_pins)
      (I R : list (bv 8)) (gL gR : gname) : iProp Σ :=
    inv N (∃ (sel : list bool) (c1 c2 : nat),
             pwc_blk2 k v I R sel c1 c2
             ∗ wcur gL (1/2) c1 ∗ wcur gR (1/2) c2).

  Global Instance blk2_inv_persistent N k v I R gL gR :
    Persistent (blk2_inv N k v I R gL gR).
  Proof using . rewrite /blk2_inv. apply _. Qed.

  Lemma blk2_inv_alloc (E : coPset) (N : namespace) (k : nat) (v : era_pins)
      (I R : list (bv 8)) (gL gR : gname) (sel : list bool) (c1 c2 : nat) :
    pwc_blk2 k v I R sel c1 c2 -∗ wcur gL (1/2) c1 -∗ wcur gR (1/2) c2
    ={E}=∗ blk2_inv N k v I R gL gR.
  Proof using .
    iIntros "Hf HL HR". rewrite /blk2_inv.
    iApply inv_alloc. iNext. iExists sel, c1, c2. iFrame.
  Qed.

  Lemma pblk2_cstep_L (N : namespace) (k : nat) (v : era_pins)
      (I R : list (bv 8)) (gL gR : gname) (c1 : nat) (b : bv 8)
      (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    dg_execL !! c1 = Some b ->
    (forall sel : list bool, sel_wf2 R sel -> pblk2_wit I R sel) ->
    pblk2_ecl_L -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I R gL gR -∗ wcur gL (1/2) c1 -∗
    (wcur gL (1/2) (S c1) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hns Hb Hwit. iIntros "#HL #Ht #Hpin #Hinv HcL HΦ".
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as (sel c1' c2) "(>Hf & >HgL & >HgR)".
    iDestruct (wcur_agree with "HcL HgL") as %<-.
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hx | #HT]"; last first.
    { (* the era is tainted: the claim answers any event out of its taint
         arm and the cursor moves on its own *)
      iMod (pecl_sup g k (default [] o) H (ConsLog.EvOut b) with "HT Hres")
        as "Hres".
      iMod (wcur_update gL c1 c1 (S c1) with "HcL HgL") as "[HcL HgL]".
      iMod ("Hclose" with "[HgL HgR]") as "_".
      { iNext. iExists sel, (S c1), c2. iFrame "HgL HgR".
        by iApply pwc_blk2_taint. }
      iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
      by iApply "HΦ". }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    pose proof (Hwit (sel ++ [true])
                  (wr_blk2_p_sel_wf ps cs I P R (sel ++ [true]) (S c1) c2 Hw'))
      as Hwit'.
    iMod ("HL" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iMod (wcur_update gL c1 c1 (S c1) with "HcL HgL") as "[HcL HgL]".
    iMod ("Hclose" with "[Hret HgL HgR]") as "_".
    { iNext. iExists (sel ++ [true]), (S c1), c2. iFrame "HgL HgR".
      rewrite /pwc_blk2.
      iDestruct "Hret" as "[[Htn Hled'] | #HT]"; [| by iRight].
      iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
      replace (P + S c1 + c2)%nat with (S (P + c1 + c2))%nat by lia.
      iFrame "Htn". iPureIntro. by split. }
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  Lemma pblk2_cstep_R (N : namespace) (k : nat) (v : era_pins)
      (I R : list (bv 8)) (gL gR : gname) (c2 : nat) (b : bv 8)
      (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    R !! c2 = Some b ->
    Forall nodollar R ->
    (forall sel : list bool, sel_wf2 R sel -> pblk2_wit I R sel) ->
    pblk2_ecl_R -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    blk2_inv N k v I R gL gR -∗ wcur gR (1/2) c2 -∗
    (wcur gR (1/2) (S c2) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hns Hb HndR Hwit. iIntros "#HR #Ht #Hpin #Hinv HcR HΦ".
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as (sel c1 c2') "(>Hf & >HgL & >HgR)".
    iDestruct (wcur_agree with "HcR HgR") as %<-.
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hx | #HT]"; last first.
    { iMod (pecl_sup g k (default [] o) H (ConsLog.EvOut b) with "HT Hres")
        as "Hres".
      iMod (wcur_update gR c2 c2 (S c2) with "HcR HgR") as "[HcR HgR]".
      iMod ("Hclose" with "[HgL HgR]") as "_".
      { iNext. iExists sel, c1, (S c2). iFrame "HgL HgR".
        by iApply pwc_blk2_taint. }
      iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
      by iApply "HΦ". }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & Hled & #HE)".
    destruct (wr_blk2_step_R ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    pose proof (Hwit (sel ++ [false])
                  (wr_blk2_p_sel_wf ps cs I P R (sel ++ [false]) c1 (S c2) Hw'))
      as Hwit'.
    iMod ("HR" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] [//] [//] Hpin Htn Hps Hcs Hled HE Hres")
      as "(Hres & Hret)".
    iMod (wcur_update gR c2 c2 (S c2) with "HcR HgR") as "[HcR HgR]".
    iMod ("Hclose" with "[Hret HgL HgR]") as "_".
    { iNext. iExists (sel ++ [false]), c1, (S c2). iFrame "HgL HgR".
      rewrite /pwc_blk2.
      iDestruct "Hret" as "[[Htn Hled'] | #HT]"; [| by iRight].
      iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hled'".
      replace (P + c1 + S c2)%nat with (S (P + c1 + c2))%nat by lia.
      iFrame "Htn". iPureIntro. by split. }
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* the chain composes -- [WpUart] names this lemma in a comment but
     does not state it *)
  Lemma pb_out_chain_app (i : uart_id) (k : nat) (bs1 bs2 : list (bv 8))
      (Φ : iProp Σ) :
    out_chain i k (bs1 ++ bs2) Φ = out_chain i k bs1 (out_chain i k bs2 Φ).
  Proof using .
    induction bs1 as [| b bs1 IH]; [reflexivity |].
    cbn [app out_chain]. by rewrite IH.
  Qed.

  (* ================================================================= *)
  (*  S8  THE CONSUMER'S CHAIN: a whole run of the two writers          *)
  (*                                                                   *)
  (*  From the family at any point, ANY interleaving [tail] of the two  *)
  (*  sides' remaining bytes is an [out_chain] -- the alternating run   *)
  (*  and the four one-sided runs are instances.                        *)
  (* ================================================================= *)

  Lemma pblk2_chain (k : nat) (v : era_pins) (I R : list (bv 8))
      (tail sel : list bool) (c1 c2 : nat) (Φ : iProp Σ) :
    (c1 + count_true tail <= length dg_execL)%nat ->
    (c2 + (length tail - count_true tail) <= length R)%nat ->
    (length sel = c1 + c2)%nat -> count_true sel = c1 ->
    Forall nodollar R -> pblk2_wit I R (sel ++ tail) ->
    pblk2_ecl_L -∗ pblk2_ecl_R -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 -∗
    (pwc_blk2 k v I R (sel ++ tail) (c1 + count_true tail)%nat
       (c2 + (length tail - count_true tail))%nat -∗ Φ) -∗
    out_chain Uart0 k (both_bytes2 R sel tail) Φ.
  Proof using Hcons.
    revert sel c1 c2 Φ.
    induction tail as [| [|] t IH];
      intros sel c1 c2 Φ H1 H2 Hlen Hcnt HndR Hwit;
      iIntros "#HL #HR #Ht #Hpin Hc HΦ".
    - (* nothing left to write: [sel ++ []] is not CONVERTIBLE to [sel],
         so the empty tail is closed on the continuation's own argument *)
      cbn [both_bytes2 out_chain].
      iApply "HΦ". cbn [count_true length].
      rewrite app_nil_r.
      replace (c1 + 0)%nat with c1 by lia.
      replace (c2 + (0 - 0))%nat with c2 by lia.
      iExact "Hc".
    - (* a LEFT byte, then the rest *)
      cbn [both_bytes2 count_true length] in H1, H2 |- *.
      pose proof (count_true_le t) as Hle.
      assert (Hlt : (c1 < length dg_execL)%nat) by lia.
      destruct (lookup_lt_is_Some_2 dg_execL c1 Hlt) as [b Hb].
      rewrite Hcnt (list_lookup_total_correct dg_execL c1 b Hb).
      cbn [out_chain].
      assert (Hwf' : sel_wf2 R (sel ++ true :: t)).
      { rewrite /sel_wf2 count_true_app length_app Hcnt Hlen.
        cbn [count_true length]. lia. }
      assert (HW1 : pblk2_wit I R (sel ++ [true])).
      { apply (pblk2_wit_mono I R (sel ++ [true]) (sel ++ true :: t));
          [exists t; by rewrite -app_assoc | exact Hwf' | exact Hwit]. }
      iApply (pblk2_step_L k v I R sel c1 c2 b _ Hb HW1
               with "HL Ht Hpin Hc").
      iIntros "Hc".
      (* the four premises are HOISTED, never spliced as [ltac:] into an
         application the proofmode still has evars in
         (claude-notes/optimization.md, "Inline [ltac:] in argument
         position": re-elaboration against unresolved evars can fail to
         terminate) *)
      assert (HA : (S c1 + count_true t <= length dg_execL)%nat) by lia.
      assert (HB : (c2 + (length t - count_true t) <= length R)%nat) by lia.
      assert (HC : length (sel ++ [true]) = (S c1 + c2)%nat)
        by (rewrite length_app Hlen; cbn [length]; lia).
      assert (HD : count_true (sel ++ [true]) = S c1)
        by (rewrite count_true_app Hcnt; cbn [count_true]; lia).
      assert (HE2 : pblk2_wit I R ((sel ++ [true]) ++ t))
        by (rewrite -app_assoc; exact Hwit).
      iApply (IH (sel ++ [true]) (S c1) c2 Φ HA HB HC HD HndR HE2
             with "HL HR Ht Hpin Hc [HΦ]").
      iIntros "Hc". iApply "HΦ". cbn [count_true length].
      replace (sel ++ true :: t) with ((sel ++ [true]) ++ t)
        by (by rewrite -app_assoc).
      replace (c1 + S (count_true t))%nat with (S c1 + count_true t)%nat
        by lia.
      replace (c2 + (S (length t) - S (count_true t)))%nat
        with (c2 + (length t - count_true t))%nat by lia.
      iExact "Hc".
    - (* a RIGHT byte, then the rest *)
      cbn [both_bytes2 count_true length] in H1, H2 |- *.
      pose proof (count_true_le t) as Hle.
      assert (Hlt : (c2 < length R)%nat) by lia.
      destruct (lookup_lt_is_Some_2 R c2 Hlt) as [b Hb].
      replace (length sel - count_true sel)%nat with c2 by lia.
      rewrite (list_lookup_total_correct R c2 b Hb).
      cbn [out_chain].
      assert (Hwf' : sel_wf2 R (sel ++ false :: t)).
      { rewrite /sel_wf2 count_true_app length_app Hcnt Hlen.
        cbn [count_true length]. lia. }
      assert (HW1 : pblk2_wit I R (sel ++ [false])).
      { apply (pblk2_wit_mono I R (sel ++ [false]) (sel ++ false :: t));
          [exists t; by rewrite -app_assoc | exact Hwf' | exact Hwit]. }
      iApply (pblk2_step_R k v I R sel c1 c2 b _ Hb HndR HW1
               with "HR Ht Hpin Hc").
      iIntros "Hc".
      assert (HA : (c1 + count_true t <= length dg_execL)%nat) by lia.
      assert (HB : (S c2 + (length t - count_true t) <= length R)%nat) by lia.
      assert (HC : length (sel ++ [false]) = (c1 + S c2)%nat)
        by (rewrite length_app Hlen; cbn [length]; lia).
      assert (HD : count_true (sel ++ [false]) = c1)
        by (rewrite count_true_app Hcnt; cbn [count_true]; lia).
      assert (HE2 : pblk2_wit I R ((sel ++ [false]) ++ t))
        by (rewrite -app_assoc; exact Hwit).
      iApply (IH (sel ++ [false]) c1 (S c2) Φ HA HB HC HD HndR HE2
             with "HL HR Ht Hpin Hc [HΦ]").
      iIntros "Hc". iApply "HΦ". cbn [count_true length].
      replace (sel ++ false :: t) with ((sel ++ [false]) ++ t)
        by (by rewrite -app_assoc).
      replace (c2 + (S (length t) - count_true t))%nat
        with (S c2 + (length t - count_true t))%nat by lia.
      iExact "Hc".
  Qed.

  (* ================================================================= *)
  (*  S9  THE ROUND'S LEND, END TO END                                  *)
  (*                                                                   *)
  (*  What lane SH-PIPE-ROUND-3 lends at the two forks and redeems      *)
  (*  after the two waits, on EVERY arm of the pipeline round: from the *)
  (*  round's owed block at an [LPipe] line ([pwc_lend], i.e.           *)
  (*  [lk_lcred]'s owed arm) and any interleaving of the two children's *)
  (*  bytes, the console shows exactly those bytes and the round ends   *)
  (*  at the shared prompt credential with its code filed.              *)
  (*                                                                   *)
  (*  This REPLACES the lane's original deliverable [pipe_both_law]:    *)
  (*  per the coordinator's amendment there is no [PBoth]-only law, and *)
  (*  the round lane states none.                                       *)
  (* ================================================================= *)

  Definition pipe_round_lend (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) : iProp Σ :=
    (∀ Φ : iProp Σ,
       pwc_lend g k v I -∗ (pwc_sp_t g k v I -∗ Φ) -∗
       out_chain Uart0 k (pend2 R sel ++ [u_prompt !!! 0%nat]) Φ)%I.

  Lemma pipe_round_lend_holds (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (a : nat) :
    pboth_line I ->
    (count_true sel <= length dg_execL)%nat ->
    (length sel - count_true sel <= length R)%nat ->
    Forall nodollar R ->
    sel <> [] ->
    pblk2_code I R sel a ->
    pblk2_ecl -∗ pipe_link_taint g -∗ era_pin γ k v -∗
    pipe_round_lend k v I R sel.
  Proof using Hcons.
    intros Hline H1 H2 HndR Hnn Hcode.
    iIntros "#Hecl #Ht #Hpin" (Φ) "Hlend HΦ".
    iDestruct (pblk2_ecl_l with "Hecl") as "#HL".
    iDestruct (pblk2_ecl_r with "Hecl") as "#HR".
    iDestruct (pblk2_ecl_f with "Hecl") as "#HF".
    iDestruct (pwc_blk2_of_lend k v I R Hline with "Hlend") as "Hc".
    assert (Hb : pend2 R sel = both_bytes2 R [] sel).
    { rewrite -{1}(app_nil_l sel) (both_bytes2_app R [] sel);
        [by rewrite (pend2_nil R)
         | rewrite app_nil_l /sel_wf2; split; lia]. }
    rewrite Hb (pb_out_chain_app Uart0 k (both_bytes2 R [] sel)
                  [u_prompt !!! 0%nat] Φ).
    assert (HA : (0 + count_true sel <= length dg_execL)%nat) by lia.
    assert (HB : (0 + (length sel - count_true sel) <= length R)%nat) by lia.
    assert (HW : pblk2_wit I R ([] ++ sel))
      by (rewrite app_nil_l; exact (pblk2_wit_of_code I R sel a Hcode)).
    iApply (pblk2_chain k v I R sel [] 0%nat 0%nat _ HA HB eq_refl eq_refl
              HndR HW with "HL HR Ht Hpin Hc").
    iIntros "Hc". cbn [out_chain].
    rewrite app_nil_l !Nat.add_0_l.
    iApply (pblk2_exit k v I R sel (count_true sel)
              (length sel - count_true sel)%nat a (u_prompt !!! 0%nat) Φ
              Hcode Hnn eq_refl with "HF Ht Hpin Hc HΦ").
  Qed.

End pipe_both.
