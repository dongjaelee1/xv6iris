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
(*  WHERE THE LEDGER'S NAME LIVES -- THE ONE THING THIS LANE DOES NOT    *)
(*  LAND.  The claim and the two writers must MEAN THE SAME GHOST, so    *)
(*  its gname has to come off something both sides already agree on,     *)
(*  i.e. the era pin or the fixed part.  [EchoOut.era_pins] has five     *)
(*  fields and all five are taken; a gname existentially bound inside    *)
(*  the claim cannot be named by a writer; and allocating a SECOND       *)
(*  camera at an existing gname is not available either ([own] can only  *)
(*  be created fresh, so a second resource at [ep_go v] would have to be *)
(*  allocated inside echo's era birth).  The route with a precedent is   *)
(*  upstream's FILE application: [FileOut.file_gn] pairs                 *)
(*  [AppFile.file_fixed] WITH a new gname and pins a second per-era      *)
(*  record in a map of its own.  The pipeline's twin is a [pipe_gn] and  *)
(*  a per-ROUND record (a [mono_list] cannot be reset, and the round     *)
(*  index [nlines I - 1] is on both sides, so the ledger is INDEXED BY   *)
(*  THE ROUND).  That moves [AppPipe.app_pipe]'s [app_fixed] field,      *)
(*  which is outside this lane's brief -- so the ledger's name is a      *)
(*  PARAMETER here ([gblk]) and the claim-side steps are stated, named   *)
(*  and OWED ([pblk2_ecl_L] / [pblk2_ecl_R] / [pblk2_ecl_file]), not     *)
(*  proved.  Nothing landed moves; everything above the claim is here.   *)
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
  intros Hwf Hlen Hc. rewrite (pblk2_code_pab I R sel a Hc) length_app.
  rewrite (pend2_length R sel Hwf) Hlen /u_prompt. by vm_compute.
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

Section pipe_both.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  Context (γ : echo_fixed).
  Context `{HRg : !riscvGS Σ}.

  Notation PT := (echo_taint γ).

  (* the record equation, as in [PipeLinks]: the port's claim IS the
     pipeline application's *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl γ).

  Lemma pbchist_at0 (kk : nat) (hh : list mobs)
      (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = pecl γ kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ================================================================= *)
  (*  S1  THE ROUND'S LEDGER: the block's BYTES                         *)
  (* ================================================================= *)

  Context (gblk : gname).

  Definition blk_enc (b : bv 8) : list mobs * bv 8 := ([], b).

  Definition blk_auth (pre : list (bv 8)) : iProp Σ :=
    own gblk (●ML ((blk_enc <$> pre) : list (leibnizO (list mobs * bv 8)))).
  Definition blk_lb (pre : list (bv 8)) : iProp Σ :=
    own gblk (◯ML ((blk_enc <$> pre) : list (leibnizO (list mobs * bv 8)))).

  Global Instance blk_lb_persistent pre : Persistent (blk_lb pre).
  Proof using . rewrite /blk_lb. apply _. Qed.
  Global Instance blk_lb_timeless pre : Timeless (blk_lb pre).
  Proof using . rewrite /blk_lb. apply _. Qed.
  Global Instance blk_auth_timeless pre : Timeless (blk_auth pre).
  Proof using . rewrite /blk_auth. apply _. Qed.

  Lemma blk_enc_inj (b c : bv 8) : blk_enc b = blk_enc c -> b = c.
  Proof using . rewrite /blk_enc. by intros [= <-]. Qed.

  Lemma blk_fmap_prefix_inv (l1 l2 : list (bv 8)) :
    (blk_enc <$> l1) `prefix_of` (blk_enc <$> l2) -> l1 `prefix_of` l2.
  Proof using .
    revert l2. induction l1 as [| b l1 IH]; intros l2 Hp; [apply prefix_nil |].
    destruct l2 as [| c l2].
    { exfalso. rewrite fmap_nil in Hp. apply prefix_length in Hp.
      rewrite fmap_cons in Hp. cbn [length] in Hp. lia. }
    rewrite !fmap_cons in Hp.
    pose proof (prefix_cons_inv_1 _ _ _ _ Hp) as Hhd.
    pose proof (prefix_cons_inv_2 _ _ _ _ Hp) as Htl.
    rewrite (blk_enc_inj b c Hhd). by apply prefix_cons, IH.
  Qed.

  Lemma blk_lb_get pre : blk_auth pre -∗ blk_auth pre ∗ blk_lb pre.
  Proof using .
    rewrite /blk_auth /blk_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML ((blk_enc <$> pre)
                                    : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma blk_auth_grow pre b :
    blk_auth pre ==∗ blk_auth (pre ++ [b]) ∗ blk_lb (pre ++ [b]).
  Proof using .
    rewrite /blk_auth /blk_lb. iIntros "H".
    iMod (own_update _ _ (●ML ((blk_enc <$> (pre ++ [b]))
                                 : list (leibnizO (list mobs * bv 8))))
            with "H") as "H".
    { apply mono_list_update. rewrite fmap_app. by eexists. }
    iModIntro.
    iDestruct (own_mono _ _ (◯ML ((blk_enc <$> (pre ++ [b]))
                                    : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  (* THE AGREEMENT THE CLAIM AND THE TWO WRITERS RUN ON: a writer's bound
     is a PREFIX of the ledger, and at equal LENGTH -- which is exactly
     what the era's cursor [turn] pins -- it IS the ledger. *)
  Lemma blk_lb_prefix pre pre' :
    blk_auth pre -∗ blk_lb pre' -∗ ⌜pre' `prefix_of` pre⌝.
  Proof using .
    rewrite /blk_auth /blk_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. apply mono_list_both_valid_L in Hv.
    exact (blk_fmap_prefix_inv pre' pre Hv).
  Qed.

  Lemma blk_lb_agree pre pre' :
    length pre = length pre' -> blk_auth pre -∗ blk_lb pre' -∗ ⌜pre' = pre⌝.
  Proof using .
    intros Hlen. iIntros "Ha Hl".
    iDestruct (blk_lb_prefix with "Ha Hl") as %Hp. iPureIntro.
    exact (prefix_length_eq pre' pre Hp ltac:(lia)).
  Qed.

  (* ================================================================= *)
  (*  S2  THE TWO CURSORS                                               *)
  (*                                                                   *)
  (*  One per child, EXCLUSIVE, in halves: ONE IS LENT TO EACH CHILD AT *)
  (*  THE FORKS, which is what the round can do without knowing which   *)
  (*  child will write.                                                 *)
  (* ================================================================= *)

  Definition wcur (g : gname) (q : Qp) (c : nat) : iProp Σ :=
    ghost_var g q c.

  Global Instance wcur_timeless g q c : Timeless (wcur g q c).
  Proof using . rewrite /wcur. apply _. Qed.

  Lemma wcur_agree g q1 q2 c1 c2 :
    wcur g q1 c1 -∗ wcur g q2 c2 -∗ ⌜c1 = c2⌝.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iDestruct (ghost_var_agree with "H1 H2") as %->.
  Qed.

  Lemma wcur_update g c1 c2 m :
    wcur g (1/2) c1 -∗ wcur g (1/2) c2 ==∗ wcur g (1/2) m ∗ wcur g (1/2) m.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iMod (ghost_var_update_halves m with "H1 H2") as "[$ $]".
  Qed.

  Lemma wcur_excl g c1 c2 : wcur g 1 c1 -∗ wcur g 1 c2 -∗ False.
  Proof using .
    rewrite /wcur. iIntros "H1 H2".
    by iDestruct (ghost_var_valid_2 with "H1 H2") as %[Hq _].
  Qed.

  (* ================================================================= *)
  (*  S3  THE FAMILY                                                    *)
  (* ================================================================= *)

  Definition pwc_blk2 (k : nat) (v : era_pins) (I : list (bv 8))
      (R : list (bv 8)) (sel : list bool) (c1 c2 : nat) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ ∗ ⌜wr_tail_p ps cs⌝
        ∗ turn v (P + c1 + c2)%nat ∗ ps_lb v ps ∗ cs_lb v cs
        ∗ blk_lb (pend2 R sel) ∗ inp_lb v I) ∨ PT)%I.

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
    apply bi.sep_timeless; [apply blk_lb_timeless | apply inp_lb_timeless].
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
    blk_lb [] -∗ pwc_lend γ k v I -∗ pwc_blk2 k v I R [] 0%nat 0%nat.
  Proof using .
    intros Hl. iIntros "#Hblk Hc". rewrite /pwc_lend /pwc_blk2.
    iDestruct "Hc" as "[Hx | #HT]"; last by iRight.
    iDestruct "Hx" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P.
    rewrite !Nat.add_0_r (pend2_nil R). iFrame "Htn Hps Hcs HE Hblk".
    iPureIntro. split; [| exact (proj2 Hw)].
    exact (wr_blk_p_blk2 ps cs I P R (proj1 Hw) Hl).
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
        ⌜dg_execL !! c1 = Some b⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ blk_lb (pend2 R sel) -∗ inp_lb v I -∗
        pecl γ k ho H ==∗
          pecl γ k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat
              ∗ blk_lb (pend2 R (sel ++ [true]))) ∨ PT))%I.

  Definition pblk2_ecl_R : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (b : bv 8),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜R !! c2 = Some b⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ blk_lb (pend2 R sel) -∗ inp_lb v I -∗
        pecl γ k ho H ==∗
          pecl γ k ho (ConsLog.cons_step H (ConsLog.EvOut b))
          ∗ ((turn v (S (P + c1 + c2))%nat
              ∗ blk_lb (pend2 R (sel ++ [false]))) ∨ PT))%I.

  (* ...AND THE FILING, at the prompt's own first byte: the only step
     that moves [cs], and the only place a round's code is built. *)
  Definition pblk2_ecl_file : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (ho : list mobs)
         (H : LogEntryDefs.cons_hist) (I R : list (bv 8)) (ps cs : list nat)
         (P : nat) (sel : list bool) (c1 c2 : nat) (a : nat) (b : bv 8),
        ⌜wr_blk2_p ps cs I P R sel c1 c2⌝ -∗ ⌜wr_tail_p ps cs⌝ -∗
        ⌜pblk2_code I R sel a⌝ -∗ ⌜b = u_prompt !!! 0%nat⌝ -∗
        era_pin γ k v -∗ turn v (P + c1 + c2)%nat -∗ ps_lb v ps -∗
        cs_lb v cs -∗ blk_lb (pend2 R sel) -∗ inp_lb v I -∗
        pecl γ k ho H ==∗
          pecl γ k ho (ConsLog.cons_step H (ConsLog.EvOut b))
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
  Proof using . rewrite /pblk2_ecl. apply _. Qed.

  Lemma pblk2_ecl_l : pblk2_ecl -∗ pblk2_ecl_L.
  Proof using . by iIntros "($ & _ & _)". Qed.
  Lemma pblk2_ecl_r : pblk2_ecl -∗ pblk2_ecl_R.
  Proof using . by iIntros "(_ & $ & _)". Qed.
  Lemma pblk2_ecl_f : pblk2_ecl -∗ pblk2_ecl_file.
  Proof using . by iIntros "(_ & _ & $)". Qed.

  (* ================================================================= *)
  (*  S5  THE TWO BYTE STEPS, at the family held LINEARLY               *)
  (* ================================================================= *)

  Lemma pblk2_step_L (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (b : bv 8) (Φ : iProp Σ) :
    dg_execL !! c1 = Some b ->
    pblk2_ecl_L -∗ pipe_links γ -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 -∗
    (pwc_blk2 k v I R (sel ++ [true]) (S c1) c2 -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hb. iIntros "#HL #Hlk #Hpin Hc HΦ".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply pwc_blk2_taint. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & #Hblk & #HE)".
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HL" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] Hpin Htn Hps Hcs Hblk HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /pwc_blk2.
    iDestruct "Hret" as "[[Htn #Hblk'] | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hblk'".
    replace (P + S c1 + c2)%nat with (S (P + c1 + c2))%nat by lia.
    iFrame "Htn". iPureIntro. by split.
  Qed.

  Lemma pblk2_step_R (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (b : bv 8) (Φ : iProp Σ) :
    R !! c2 = Some b ->
    pblk2_ecl_R -∗ pipe_links γ -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 -∗
    (pwc_blk2 k v I R (sel ++ [false]) c1 (S c2) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hb. iIntros "#HR #Hlk #Hpin Hc HΦ".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". by iApply pwc_blk2_taint. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & #Hblk & #HE)".
    destruct (wr_blk2_step_R ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HR" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] Hpin Htn Hps Hcs Hblk HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /pwc_blk2.
    iDestruct "Hret" as "[[Htn #Hblk'] | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hblk'".
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
    b = u_prompt !!! 0%nat ->
    pblk2_ecl_file -∗ pipe_links γ -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 -∗
    (pwc_sp_t γ k v I -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hcode Hb. iIntros "#HF #Hlk #Hpin Hc HΦ".
    iDestruct (pipe_links_taint with "Hlk") as "#Ht".
    rewrite {1}/pwc_blk2. iDestruct "Hc" as "[Hx | #HT]"; last first.
    { iApply ("Ht" $! k b Φ with "HT [HΦ]").
      iIntros "#HT'". iApply "HΦ". rewrite /pwc_sp_t. by iRight. }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & #Hblk & #HE)".
    pose proof (wr_blk2_p_sel_wf ps cs I P R sel c1 c2 Hw) as Hwf.
    pose proof Hw as (_ & _ & _ & _ & _ & _ & Hlen & _).
    assert (Hpapr : papr I a) by exact (pblk2_code_papr I R sel a Hcode).
    assert (Hab : length (pab I a) = S (S (c1 + c2))%nat)
      by exact (pblk2_code_len I R sel a c1 c2 Hwf Hlen Hcode).
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    iMod ("HF" $! k v (default [] o) H I R ps cs P sel c1 c2 a b
            with "[//] [//] [//] [//] Hpin Htn Hps Hcs Hblk HE Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
    iApply "HΦ".
    iDestruct "Hret" as "[[Htn #Hcs'] | #HT]";
      last by (rewrite /pwc_sp_t; iRight).
    iApply (pwc_blk_sp γ k v I a Hpapr).
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

  Lemma blk2_inv_alloc (N : namespace) (k : nat) (v : era_pins)
      (I R : list (bv 8)) (gL gR : gname) (sel : list bool) (c1 c2 : nat) :
    pwc_blk2 k v I R sel c1 c2 -∗ wcur gL (1/2) c1 -∗ wcur gR (1/2) c2 ==∗
      blk2_inv N k v I R gL gR.
  Proof using .
    iIntros "Hf HL HR". rewrite /blk2_inv.
    iApply inv_alloc. iNext. iExists sel, c1, c2. iFrame.
  Qed.

  Lemma pblk2_cstep_L (N : namespace) (k : nat) (v : era_pins)
      (I R : list (bv 8)) (gL gR : gname) (c1 : nat) (b : bv 8)
      (Φ : iProp Σ) :
    (↑N : coPset) ## (↑uartN Uart0 : coPset) ->
    dg_execL !! c1 = Some b ->
    pblk2_ecl_L -∗ pipe_links γ -∗ era_pin γ k v -∗
    blk2_inv N k v I R gL gR -∗ wcur gL (1/2) c1 -∗
    (wcur gL (1/2) (S c1) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hns Hb. iIntros "#HL #Hlk #Hpin #Hinv HcL HΦ".
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as (sel c1' c2) "(>Hf & >HgL & >HgR)".
    iDestruct (wcur_agree with "HcL HgL") as %<-.
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hx | #HT]"; last first.
    { (* the era is tainted: the claim answers any event out of its taint
         arm and the cursor moves on its own *)
      iMod (pecl_sup γ k (default [] o) H (ConsLog.EvOut b) with "HT Hres")
        as "Hres".
      iMod (wcur_update gL c1 c1 (S c1) with "HcL HgL") as "[HcL HgL]".
      iMod ("Hclose" with "[HgL HgR]") as "_".
      { iNext. iExists sel, (S c1), c2. iFrame "HgL HgR".
        by iApply pwc_blk2_taint. }
      iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
      by iApply "HΦ". }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & #Hblk & #HE)".
    destruct (wr_blk2_step_L ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    iMod ("HL" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] Hpin Htn Hps Hcs Hblk HE Hres")
      as "(Hres & Hret)".
    iMod (wcur_update gL c1 c1 (S c1) with "HcL HgL") as "[HcL HgL]".
    iMod ("Hclose" with "[Hret HgL HgR]") as "_".
    { iNext. iExists (sel ++ [true]), (S c1), c2. iFrame "HgL HgR".
      rewrite /pwc_blk2.
      iDestruct "Hret" as "[[Htn #Hblk'] | #HT]"; [| by iRight].
      iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hblk'".
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
    pblk2_ecl_R -∗ pipe_links γ -∗ era_pin γ k v -∗
    blk2_inv N k v I R gL gR -∗ wcur gR (1/2) c2 -∗
    (wcur gR (1/2) (S c2) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hns Hb. iIntros "#HR #Hlk #Hpin #Hinv HcR HΦ".
    rewrite /out_link. iIntros (o H) "#Hlb Hres". rewrite !pbchist_at0.
    assert (Hsub : (↑N : coPset) ⊆ (⊤ ∖ ↑uartN Uart0 : coPset)).
    { apply subseteq_difference_r; [exact Hns | apply top_subseteq]. }
    iMod (inv_acc _ N _ Hsub with "Hinv") as "[Hin Hclose]".
    iDestruct "Hin" as (sel c1 c2') "(>Hf & >HgL & >HgR)".
    iDestruct (wcur_agree with "HcR HgR") as %<-.
    rewrite {1}/pwc_blk2. iDestruct "Hf" as "[Hx | #HT]"; last first.
    { iMod (pecl_sup γ k (default [] o) H (ConsLog.EvOut b) with "HT Hres")
        as "Hres".
      iMod (wcur_update gR c2 c2 (S c2) with "HcR HgR") as "[HcR HgR]".
      iMod ("Hclose" with "[HgL HgR]") as "_".
      { iNext. iExists sel, c1, (S c2). iFrame "HgL HgR".
        by iApply pwc_blk2_taint. }
      iModIntro. iExists o. rewrite pbchist_at0. iFrame "Hlb Hres".
      by iApply "HΦ". }
    iDestruct "Hx"
      as (ps cs P) "(%Hw & %Htl & Htn & #Hps & #Hcs & #Hblk & #HE)".
    destruct (wr_blk2_step_R ps cs I P R sel c1 c2 b Hw Hb) as (Hw' & _).
    iMod ("HR" $! k v (default [] o) H I R ps cs P sel c1 c2 b
            with "[//] [//] [//] Hpin Htn Hps Hcs Hblk HE Hres")
      as "(Hres & Hret)".
    iMod (wcur_update gR c2 c2 (S c2) with "HcR HgR") as "[HcR HgR]".
    iMod ("Hclose" with "[Hret HgL HgR]") as "_".
    { iNext. iExists (sel ++ [false]), c1, (S c2). iFrame "HgL HgR".
      rewrite /pwc_blk2.
      iDestruct "Hret" as "[[Htn #Hblk'] | #HT]"; [| by iRight].
      iLeft. iExists ps, cs, P. iFrame "Hps Hcs HE Hblk'".
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
    pblk2_ecl_L -∗ pblk2_ecl_R -∗ pipe_links γ -∗ era_pin γ k v -∗
    pwc_blk2 k v I R sel c1 c2 -∗
    (pwc_blk2 k v I R (sel ++ tail) (c1 + count_true tail)%nat
       (c2 + (length tail - count_true tail))%nat -∗ Φ) -∗
    out_chain Uart0 k (both_bytes2 R sel tail) Φ.
  Proof using Hcons.
    revert sel c1 c2 Φ.
    induction tail as [| [|] t IH]; intros sel c1 c2 Φ H1 H2 Hlen Hcnt;
      iIntros "#HL #HR #Hlk #Hpin Hc HΦ".
    - cbn [both_bytes2 out_chain count_true length].
      rewrite !app_nil_r !Nat.add_0_r !Nat.sub_0_r.
      iApply ("HΦ" with "Hc").
    - (* a LEFT byte, then the rest *)
      cbn [both_bytes2 count_true length] in H1, H2 |- *.
      pose proof (count_true_le t) as Hle.
      assert (Hlt : (c1 < length dg_execL)%nat) by lia.
      destruct (lookup_lt_is_Some_2 dg_execL c1 Hlt) as [b Hb].
      rewrite Hcnt (list_lookup_total_correct dg_execL c1 b Hb).
      cbn [out_chain].
      iApply (pblk2_step_L k v I R sel c1 c2 b _ Hb with "HL Hlk Hpin Hc").
      iIntros "Hc".
      iApply (IH (sel ++ [true]) (S c1) c2 Φ
                ltac:(lia) ltac:(lia)
                ltac:(rewrite length_app Hlen; cbn [length]; lia)
                ltac:(rewrite count_true_app Hcnt; cbn [count_true]; lia)
             with "HL HR Hlk Hpin Hc [HΦ]").
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
      iApply (pblk2_step_R k v I R sel c1 c2 b _ Hb with "HR Hlk Hpin Hc").
      iIntros "Hc".
      iApply (IH (sel ++ [false]) c1 (S c2) Φ
                ltac:(lia) ltac:(lia)
                ltac:(rewrite length_app Hlen; cbn [length]; lia)
                ltac:(rewrite count_true_app Hcnt; cbn [count_true]; lia)
             with "HL HR Hlk Hpin Hc [HΦ]").
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
       blk_lb [] -∗ pwc_lend γ k v I -∗ (pwc_sp_t γ k v I -∗ Φ) -∗
       out_chain Uart0 k (pend2 R sel ++ [u_prompt !!! 0%nat]) Φ)%I.

  Lemma pipe_round_lend_holds (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (a : nat) :
    pboth_line I ->
    (count_true sel <= length dg_execL)%nat ->
    (length sel - count_true sel <= length R)%nat ->
    pblk2_code I R sel a ->
    pblk2_ecl -∗ pipe_links γ -∗ era_pin γ k v -∗
    pipe_round_lend k v I R sel.
  Proof using Hcons.
    intros Hline H1 H2 Hcode.
    iIntros "#Hecl #Hlk #Hpin" (Φ) "#Hblk0 Hlend HΦ".
    iDestruct (pblk2_ecl_l with "Hecl") as "#HL".
    iDestruct (pblk2_ecl_r with "Hecl") as "#HR".
    iDestruct (pblk2_ecl_f with "Hecl") as "#HF".
    iDestruct (pwc_blk2_of_lend k v I R Hline with "Hblk0 Hlend") as "Hc".
    assert (Hb : pend2 R sel = both_bytes2 R [] sel).
    { rewrite -{1}(app_nil_l sel) (both_bytes2_app R [] sel);
        [by rewrite (pend2_nil R)
         | rewrite app_nil_l /sel_wf2; split; lia]. }
    rewrite Hb (pb_out_chain_app Uart0 k (both_bytes2 R [] sel)
                  [u_prompt !!! 0%nat] Φ).
    iApply (pblk2_chain k v I R sel [] 0%nat 0%nat with "HL HR Hlk Hpin Hc");
      [lia | lia | done | done |].
    iIntros "Hc". cbn [out_chain].
    rewrite app_nil_l !Nat.add_0_l.
    iApply (pblk2_exit k v I R sel (count_true sel)
              (length sel - count_true sel)%nat a (u_prompt !!! 0%nat) Φ
              Hcode eq_refl with "HF Hlk Hpin Hc HΦ").
  Qed.

End pipe_both.
