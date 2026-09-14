(* EchoOut.v -- E5's APPLICATION CLAIM, THE IRIS HALF (lane ECHO-OUT).

   Design of record: the coordinator's E5 DESIGN PAGE of 2026-09-15
   (scratchpad e5-design-page.md), section 2, which REPLACES the
   ledger-anchored shape of REVISIONS 4-8: CLAIM-RESIDENT STATE, NO LEDGER
   IN ANY LINK.

   WHY THE STATE IS IN THE CLAIMS AND NOT IN THE LEDGER.  The two things
   that forced the ledger-anchored shape are both gone.  [App.Happ_boot]
   founds nothing any more (milestone E moved the founding to [App.Hpow],
   which is the ONE step per era that runs the ledger and may mint linear
   content), and [App.Happ_echo] is a CLOSED entailment with no observation
   handle, so a link fired inside the echo shift cannot reach the ledger at
   all.  So each era's authorities -- its cursor, its line choices, its
   echoed list and its window counter -- live in the PORT CLAIMS, and the
   ledger keeps only what is about the HISTORY: the taint counter, the era
   map (whose authority is spent at [echo_led_pow] and nowhere else) and
   the phi conjunct.

   THE INDEX IS THE ERA NUMBER [k := S gen_id] (ambient [RiscvLang.GenId]),
   not a ghost name: [riscv_out_res k ho acc], [riscv_in_res k ho pops dl],
   every link at [k], [app_out/app_in/app_boot A c k].  The kernel STAMPS
   every history it hands the application with [⌜obs_boots h = S gen_id⌝].
   A link at [k] therefore knows [k = obs_boots h] purely, and no history is
   ever compared against the ledger's inside a link -- which is essential,
   because the observation AUTHORITY lives in the state interpretation.

   THE SHAPE.  [eout k ho acc] is the TAINT (what the licences pay through)
   or the era's PAIRED arm, which holds the era's pin and its four
   authorities.  [ein k hi pops dl] is the taint, the SETTLED arm, or the
   WINDOW arm -- the chain-first window, between the echo's store and the
   [WpUart.in_append] that files its entry.

   THE WINDOW COUNTER AND THE KERNEL-LENT TOKEN (the page's section 1, K1).
   [WpUart.echo_link] returns the input claim at exactly the [pops]/[dl] it
   was handed, and [SpecConsoleintr.cons_echo_shift] is persistent, so the
   application's spec has to be total over interleavings the kernel forbids
   with cons.lock but never states.  The kernel therefore LENDS the
   application its own per-era exclusive -- [riscv_win_res (S gen_id)],
   which is [ewin] below -- on the PLIC payload beside the receive token; it
   is a premise of the shift and comes back in [in_append]'s post.  One
   [ghost_var nat] per era, [wcnt], carries it in QUARTERS: one in the
   output claim (at [length (o_E so)]), one in the input claim, and a HALF
   in the token.  The echo splits the half it is handed: a quarter stays in
   the input claim's window arm (which therefore holds a half) and a quarter
   travels to the append inside [ein_pend].  So
     - the three shares the echo holds agree, which is what gives it
       [seg_of (echoed pops) = o_E so] -- the tie the old [stage_tie] was;
     - the quarter the append carries AGREES with the window arm's half, so
       the append knows the arm is the one its own echo left;
     - a SECOND link of the run meets the window arm holding a half, and
       [1/4 + 1/2 + 1/2] is five quarters: [ghost_var_valid_2] refutes it.

   THE ERA'S FIRST WRITE needs no special step: [app_turn] (init's console
   credential, minted beside the claims at [echo_led_pow] and carried to
   [App.Hinit_boot] by the kernel) is the era's cursor at zero, and at
   [P = 0] the paired claim's own [turn_auth] plus [pcount_zero] DERIVE
   [o_E so = [] /\ o_w so = []], hence [acc = []].  There is no founded arm
   to refute and no seed to spend.

   WHAT THE LINKS HAND THE PROGRAM (review S9).  A writer must prove
   [pending ps cs E !! length w = Some b] without holding any authority.  It
   gets a PERSISTENT lower bound of the era's line choices ([cs_lb]) and its
   cursor; [proc_stream_pcount] turns the two into the byte owed, because the
   process bytes of an era are one stream and the cursor is a position in it.
   [echo_write_link] and [echo_read_link] hand those back, which is what
   IO-LEAF and SH-LINE consume. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
(* ...and, for section 7, the kernel's own console contracts: the links the
   application's claims are wrapped onto, and the observation invariant the
   ledger lives in.  This file is BELOW [AppEcho] and ABOVE [WpUart], which
   is where the _CoqProject entry has always said the links belong. *)
Require Import RiscvPtsto.       (* [obsN], [obs_hist_lb_o], [riscv_out_res],
                                    [riscv_in_res], [riscvGS] *)
Require Import WpUart.           (* [out_link], [read_link], [in_append],
                                    [in_run], [out_res_at], [in_res_at],
                                    [uartN] *)
Require Import TsoCtx.           (* [CurCtx]: the echo obligation's context *)
Require Import SpecConsoleintr.  (* [cons_echo_shift], which is what
                                    [App.Happ_echo] asks of the
                                    application *)
(* as in EchoDisc / EchoOutPure: the Sail imports leave string_scope on top
   and [++] would elaborate as String.append. *)
Local Open Scope list_scope.

(* ====================================================================== *)
(*  1.  THE TWO STAGES                                                     *)
(* ====================================================================== *)

(* E's HISTORIES ARE CYCLE SEGMENTS ([open_seg] of the history the byte was
   received at), not whole histories: [EchoOutPure]'s [E_index] counts with
   [ins], the discipline and [good_out] are per POWER CYCLE, and [acc]
   restarts at every era -- so instantiating [E_index] at whole histories is
   unsatisfiable from era 1 on.  Nothing in [EchoOutPure] moves: it is
   parametric in what E's first components are, and this file supplies
   segments ([EchoOutPure.open_seg_ends_in] is the one bridge). *)
Record ostage := MkO {
  o_ps : list nat;
  o_cs : list nat;
  o_E  : list (list mobs * bv 8);
  o_w  : list (bv 8);
}.
Definition ostage0 : ostage := MkO [] [] [] [].

(* the OUTPUT claim's pure fact.

   THE SAME-CYCLE FACTS LIVE HERE, AT THE CLAIM'S OWN WITNESS [ho], and not
   in the ledger (lane ECHO-OUT, section 7).  The reason is the ECHO: its
   links fire at the consputc STORES, which are later than the history the
   byte arrived at, so the ledger the shift opens is at a history the shift
   cannot name -- and no link may compare a history against the ledger's,
   because the observation AUTHORITY lives in the state interpretation.  At
   the claim's witness there is no such problem: the ECHO re-establishes the
   facts at its own [h] out of the INPUT claim's per-entry stamps, and the
   DRAIN lifts them to the run's history with [App.Htx]'s own premise
   [ho `prefix_of` h] plus the two era stamps ([EchoOutPure.
   open_seg_prefix_boots]).  The ledger is then HISTORY-FREE. *)
Definition eout_pure (k : nat) (ho : list mobs) (so : ostage)
    (acc : list (bv 8)) : Prop :=
  acc = D (o_ps so) (o_cs so) (o_E so) ++ o_w so
  /\ o_w so `prefix_of` pending (o_ps so) (o_cs so) (o_E so)
  /\ E_index (o_E so)
  /\ E_byte (o_E so)
  /\ Forall (fun a => (a < length pro_alts)%nat) (o_ps so)
  /\ pro_pin (o_ps so) (o_cs so) (length (o_E so))
  /\ Forall (fun i => (i < length line_alts)%nat) (o_cs so)
  /\ Forall (fun x => disc_seg x.1) (o_E so)
  /\ Forall (fun x => x.1 `prefix_of` open_seg ho) (o_E so)
  /\ (length (o_E so) <= length (ins (open_seg ho)))%nat
  /\ (o_E so = [] \/ obs_boots ho = k).

(* THE LEDGER'S LENGTH LAW FOR THE CHOICE LIST (REVISION 7(d)).  [cs] records
   one alternative per COMPLETED line, at index [q-1] for line [q], and it
   grows at the FIRST BYTE of that line's continuation -- which is the only
   moment at which the program knows which alternative it is taking.  So the
   list is one short exactly while the writer is standing at a block
   boundary with nothing of the block written ([o_w so = []] and
   [length (o_E so)] a multiple of the line), and the prologue (block 0)
   grows it not at all -- which the nat subtraction below says for free. *)
Definition cs_len_ok (so : ostage) : Prop :=
  length (o_cs so)
  = (if decide (o_w so = []
                /\ (length (o_E so) `mod` length echo_line)%nat = 0%nat)
     then (length (o_E so) `div` length echo_line - 1)%nat
     else (length (o_E so) `div` length echo_line)%nat).

(* ---- the three moves of [cs_len_ok], as pure arithmetic ---- *)

(* [pending] is EMPTY exactly mid-line: at a block boundary the stage owes
   the prologue or a whole alternative, and neither is empty. *)
Lemma pending_nonnil (ps cs : list nat) (E : list (list mobs * bv 8)) :
  Forall (fun i => (i < length line_alts)%nat) cs ->
  (length E `mod` length echo_line = 0)%nat ->
  pending ps cs E <> [].
Proof.
  intros HF Hm. rewrite /pending /pending_n.
  case_decide as H0.
  - pose proof (pro_of_pos ps) as Hpos. intros Hc.
    rewrite Hc in Hpos. cbn in Hpos. lia.
  - rewrite decide_True; [| exact Hm]. rewrite /alt_cont. intros Hc.
    apply app_eq_nil in Hc as [Hc _].
    exact (line_alts_nonnil _ (cs_ok_of_Forall _ HF _) Hc).
Qed.

Lemma cs_len_ok_inv (so : ostage) :
  cs_len_ok so ->
  ((o_w so = [] /\ (length (o_E so) `mod` length echo_line)%nat = 0%nat)
     /\ length (o_cs so) = (length (o_E so) `div` length echo_line - 1)%nat)
  \/ (~ (o_w so = [] /\ (length (o_E so) `mod` length echo_line)%nat = 0%nat)
     /\ length (o_cs so) = (length (o_E so) `div` length echo_line)%nat).
Proof.
  rewrite /cs_len_ok. case_decide as Hb; intros Hc.
  - left. by split.
  - right. by split.
Qed.

Lemma cs_len_ok_intro (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) :
  ((w = [] /\ (length E `mod` length echo_line)%nat = 0%nat) ->
     length cs = (length E `div` length echo_line - 1)%nat) ->
  (~ (w = [] /\ (length E `mod` length echo_line)%nat = 0%nat) ->
     length cs = (length E `div` length echo_line)%nat) ->
  cs_len_ok (MkO ps cs E w).
Proof.
  rewrite /cs_len_ok. cbn [o_ps o_cs o_E o_w]. intros H1 H2. case_decide as Hb.
  - by apply H1.
  - by apply H2.
Qed.

Lemma cs_len_ok_mid (so : ostage) :
  cs_len_ok so -> o_w so <> [] ->
  length (o_cs so) = (length (o_E so) `div` length echo_line)%nat.
Proof.
  intros Hc Hw. destruct (cs_len_ok_inv so Hc) as [[[Hw' _] _] | [_ ?]];
    [done | done].
Qed.

(* the two divisions the echo's step turns on *)
Lemma div_succ_of_mod0 (n : nat) :
  ((n + 1) `mod` length echo_line = 0)%nat ->
  (n `div` length echo_line = (n + 1) `div` length echo_line - 1)%nat.
Proof.
  pose proof echo_line_length as HL. intros Hm.
  pose proof (Nat.div_mod_eq (n + 1) (length echo_line)) as Hdm.
  rewrite Hm Nat.add_0_r in Hdm.
  set (m := ((n + 1) `div` length echo_line)%nat) in *.
  assert (Hm1 : (1 <= m)%nat) by lia.
  assert (Hn : n = ((m - 1) * length echo_line + (length echo_line - 1))%nat)
    by lia.
  rewrite Hn (Nat.div_add_l (m - 1) (length echo_line) (length echo_line - 1));
    [| lia].
  rewrite (Nat.div_small (length echo_line - 1) (length echo_line)); lia.
Qed.

Lemma div_succ_of_modn0 (n : nat) :
  ((n + 1) `mod` length echo_line <> 0)%nat ->
  (n `div` length echo_line = (n + 1) `div` length echo_line)%nat.
Proof.
  pose proof echo_line_length as HL. intros Hm.
  pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm.
  assert (Hr : (n `mod` length echo_line < length echo_line)%nat)
    by (apply Nat.mod_upper_bound; lia).
  set (q := (n `div` length echo_line)%nat) in *.
  set (r := (n `mod` length echo_line)%nat) in *.
  assert (Hrs : (r + 1 < length echo_line)%nat).
  { destruct (decide ((r + 1)%nat = length echo_line)) as [He | He]; [| lia].
    exfalso. apply Hm.
    assert (Hn1 : (n + 1)%nat = ((q + 1) * length echo_line)%nat) by lia.
    rewrite Hn1 Nat.Div0.mod_mul. reflexivity. }
  assert (Hn1 : (n + 1)%nat = (q * length echo_line + (r + 1))%nat) by lia.
  rewrite Hn1 (Nat.div_add_l q (length echo_line) (r + 1)); [| lia].
  rewrite (Nat.div_small (r + 1) (length echo_line)); lia.
Qed.

(* THE ECHO does not move the choice list: it closes the block the writer
   has just finished, and the next block's alternative is chosen by the
   WRITE that starts it. *)
Lemma cs_len_ok_echo (so : ostage) (x : list mobs * bv 8) :
  Forall (fun i => (i < length line_alts)%nat) (o_cs so) ->
  o_w so = pending (o_ps so) (o_cs so) (o_E so) ->
  cs_len_ok so ->
  cs_len_ok (MkO (o_ps so) (o_cs so) (o_E so ++ [x]) []).
Proof.
  intros HF Hw Hc.
  assert (Hq : length (o_cs so)
               = (length (o_E so) `div` length echo_line)%nat).
  { destruct (cs_len_ok_inv so Hc) as [[[Hw' Hm] _] | [_ Hq]]; [| exact Hq].
    exfalso. apply (pending_nonnil (o_ps so) (o_cs so) (o_E so) HF Hm).
    by rewrite -Hw. }
  apply cs_len_ok_intro; rewrite length_app; cbn [length]; rewrite Hq.
  - intros [_ Hm]. by apply div_succ_of_mod0.
  - intros Hne. apply div_succ_of_modn0. intros Hm. by apply Hne.
Qed.

(* A WRITE INSIDE A BLOCK does not move it either. *)
Lemma cs_len_ok_write (so : ostage) (b : bv 8) :
  cs_len_ok so ->
  (o_w so <> [] \/ (length (o_E so) `mod` length echo_line)%nat <> 0%nat
                \/ length (o_E so) = 0%nat) ->
  cs_len_ok (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])).
Proof.
  intros Hc Hcase. apply cs_len_ok_intro.
  { intros [Hw _]. exfalso.
    by destruct (app_eq_nil (o_w so) [b] Hw) as [_ Hb]. }
  intros _. destruct (cs_len_ok_inv so Hc) as [[[Hw Hm] Hq] | [_ Hq]];
    [| exact Hq].
  destruct Hcase as [Hw' | [Hm' | Hn]]; [done | done |].
  rewrite Hq Hn. by rewrite Nat.Div0.div_0_l.
Qed.

(* ...and A WRITE AT A BLOCK'S FIRST BYTE grows it by exactly one
   (REVISION 7(d)). *)
Lemma cs_len_ok_blk (so : ostage) (a : nat) (b : bv 8) :
  (length (o_E so) `mod` length echo_line)%nat = 0%nat ->
  (0 < length (o_E so))%nat ->
  o_w so = [] ->
  cs_len_ok so ->
  cs_len_ok (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) [b]).
Proof.
  pose proof echo_line_length as HL. intros Hm Hpos Hw Hc.
  destruct (cs_len_ok_inv so Hc) as [[_ Hq] | [Hne _]]; last first.
  { exfalso. by apply Hne. }
  apply cs_len_ok_intro.
  { intros [Hb _]. discriminate. }
  intros _. rewrite length_app. cbn [length]. rewrite Hq.
  assert (Hdm : length (o_E so)
                = (length echo_line
                   * (length (o_E so) `div` length echo_line))%nat).
  { pose proof (Nat.div_mod_eq (length (o_E so)) (length echo_line)) as H.
    lia. }
  assert (Hq1 : (1 <= length (o_E so) `div` length echo_line)%nat).
  { destruct ((length (o_E so) `div` length echo_line)%nat) as [| q'];
      [lia | lia]. }
  lia.
Qed.

(* THE LEDGER'S LENGTH LAW FOR THE PROLOGUE RESOLUTION -- the TWIN of
   [cs_len_ok], and what makes the prologue's CHOICE readable off the
   cursor.  [cs_len_ok] pins how many LINE alternatives have been filed by
   the writer's position; this pins how much of the OPEN ROUND's resolution
   has been.  Without it a claim whose current round is already SETTLED --
   [pro_of] one alternative longer, so [pending_n] longer and the writer's
   [o_w] a proper prefix of it -- is a perfectly consistent state, and the
   prologue-choice write cannot tell it from the one it is actually in.

   THE ROUND A STAGE STANDS IN is [ps_round]: one per line that took
   [line_alts !!! 3] (the shell's own fork panic), round 0 at the head of
   the transcript.  A block OPENS that round only at those two places
   ([ps_opens]); every other block owes no prologue at all, which is why the
   second conjunct is guarded -- unguarded it is simply false.

   THE TWO CONJUNCTS.
   (A) NOTHING IS FILED FOR A ROUND THAT HAS NOT OPENED: past the current
       round the resolution is empty.  This is what makes the block-first
       write that OPENS the next round ([line_alts !!! 3]) find it open.
   (B) EVERY ENTRY THE ROUND HAS IS ON THE WIRE: a prefix of the resolution
       that gives a SHORTER prologue than the stage's own was passed by the
       writer strictly.  Since an open prologue ends at a banner and filing
       an alternative appends at least its first byte
       ([EchoDisc.pro_of_open_snoc_lt]), this says exactly "the round is
       settled only once the writer has written past the block's banner",
       and it is what reconciles a writer's [~ pro_done] with the claim. *)
Definition ps_round (so : ostage) : nat :=
  pro_idx (o_cs so) (length (o_E so) `div` length echo_line).

Definition ps_opens (so : ostage) : Prop :=
  length (o_E so) = 0%nat
  \/ ((length (o_E so) `mod` length echo_line)%nat = 0%nat
      /\ o_cs so !!! (length (o_E so) `div` length echo_line - 1)%nat = 3%nat).

Definition ps_len_ok (so : ostage) : Prop :=
  pro_from (S (ps_round so)) (o_ps so) = []
  /\ (ps_opens so ->
      forall ps' : list nat, ps' `prefix_of` o_ps so ->
        pro_of (pro_from (ps_round so) ps')
          <> pro_of (pro_from (ps_round so) (o_ps so)) ->
        (length (pending_n ps' (o_cs so) (length (o_E so)))
         < length (o_w so))%nat).

(* the rounds a stage has NOT opened are empty in it, and stay empty as the
   index moves up -- the one consequence of (A) the three moves spend *)
Lemma ps_len_ok_empty_above (so : ostage) (R : nat) :
  ps_len_ok so -> (ps_round so <= R)%nat -> pro_from (S R) (o_ps so) = [].
Proof.
  intros [HA _] HR.
  replace (S R) with (S (ps_round so) + (R - ps_round so))%nat by lia.
  rewrite -pro_from_add HA. apply pro_from_nil.
Qed.

Lemma ps_len_ok_0 : ps_len_ok ostage0.
Proof.
  rewrite /ps_len_ok /ps_round /ostage0. cbn [o_ps o_cs o_E o_w]. split.
  - apply pro_from_nil.
  - intros _ ps' Hp Hne. exfalso. apply Hne.
    by rewrite (prefix_nil_inv ps' Hp).
Qed.

(* ---- the three moves, as [cs_len_ok_echo]/[_write]/[_blk] are ---- *)

(* A WRITE INSIDE THE BLOCK moves neither the round nor the resolution, and
   only lengthens what has been written. *)
Lemma ps_len_ok_write (so : ostage) (b : bv 8) :
  ps_len_ok so ->
  ps_len_ok (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])).
Proof.
  intros [HA HB]. rewrite /ps_len_ok /ps_round /ps_opens in HA, HB |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB |- *. split; [exact HA |].
  intros Ho ps' Hp Hne. rewrite (length_app (o_w so) [b]). cbn [length].
  pose proof (HB Ho ps' Hp Hne). lia.
Qed.

(* A WRITE AT A BLOCK'S FIRST BYTE may OPEN a round -- exactly when the
   alternative it files is 3 -- and (A) says that round is untouched. *)
Lemma ps_len_ok_blk (so : ostage) (a : nat) (b : bv 8) :
  (length (o_E so) `mod` length echo_line)%nat = 0%nat ->
  (0 < length (o_E so))%nat ->
  length (o_cs so) = (length (o_E so) `div` length echo_line - 1)%nat ->
  ps_len_ok so ->
  ps_len_ok (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) [b]).
Proof.
  pose proof echo_line_length as HL. intros Hm Hpos Hq Hok.
  pose proof Hok as [HA HB].
  rewrite /ps_len_ok /ps_round /ps_opens in HA, HB |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB |- *.
  assert (HD1 : (1 <= length (o_E so) `div` length echo_line)%nat).
  { destruct (decide (length (o_E so) `div` length echo_line = 0)%nat)
      as [Hd | Hd]; [| lia].
    exfalso.
    pose proof (Nat.div_mod_eq (length (o_E so)) (length echo_line)) as Hdm.
    rewrite Hd Hm in Hdm. lia. }
  assert (Hold : pro_idx (o_cs so) (length (o_E so) `div` length echo_line)
                 = pro_idx (o_cs so)
                     (length (o_E so) `div` length echo_line - 1)%nat).
  { replace (length (o_E so) `div` length echo_line)%nat
      with (S (length (o_E so) `div` length echo_line - 1))%nat at 1 by lia.
    apply pro_idx_Sne.
    rewrite list_lookup_total_alt
      (lookup_ge_None_2 (o_cs so)
         (length (o_E so) `div` length echo_line - 1)%nat ltac:(lia)).
    by vm_compute. }
  assert (Hnew : (pro_idx (o_cs so) (length (o_E so) `div` length echo_line)
                  <= pro_idx (o_cs so ++ [a])
                       (length (o_E so) `div` length echo_line))%nat).
  { rewrite Hold.
    replace (length (o_E so) `div` length echo_line)%nat
      with (S (length (o_E so) `div` length echo_line - 1))%nat at 2 by lia.
    rewrite pro_idx_S
      (pro_idx_app_le (o_cs so) [a]
         (length (o_E so) `div` length echo_line - 1)%nat ltac:(lia)).
    lia. }
  split.
  - apply (ps_len_ok_empty_above so); [exact Hok |].
    rewrite /ps_round. exact Hnew.
  - intros Ho ps' Hp Hne. exfalso.
    destruct Ho as [Hz | [_ H3]]; [lia |].
    assert (Ha3 : a = 3%nat).
    { rewrite list_lookup_total_alt lookup_app_r in H3; [| lia].
      rewrite Hq Nat.sub_diag in H3. by cbn in H3. }
    assert (Heq : pro_idx (o_cs so ++ [a])
                    (length (o_E so) `div` length echo_line)
                  = S (pro_idx (o_cs so) (length (o_E so) `div` length echo_line))).
    { rewrite Hold
        -(pro_idx_app_le (o_cs so) [a]
            (length (o_E so) `div` length echo_line - 1)%nat ltac:(lia)).
      replace (length (o_E so) `div` length echo_line)%nat
        with (S (length (o_E so) `div` length echo_line - 1))%nat at 1 by lia.
      apply pro_idx_S3. exact H3. }
    rewrite Heq in Hne. apply Hne.
    assert (Hnil : pro_from
                     (S (pro_idx (o_cs so)
                           (length (o_E so) `div` length echo_line))) (o_ps so)
                   = []) by exact HA.
    assert (Hnil' : pro_from
                      (S (pro_idx (o_cs so)
                            (length (o_E so) `div` length echo_line))) ps' = []).
    { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
    by rewrite Hnil Hnil'.
Qed.

(* THE ECHO closes a line; when the line it closes took alternative 3 the
   round it opens is, again, one the resolution has not touched. *)
Lemma ps_len_ok_echo (so : ostage) (x : list mobs * bv 8) :
  ps_len_ok so ->
  ps_len_ok (MkO (o_ps so) (o_cs so) (o_E so ++ [x]) []).
Proof.
  pose proof echo_line_length as HL. intros Hok. pose proof Hok as [HA HB].
  rewrite /ps_len_ok /ps_round /ps_opens in HA, HB |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB |- *.
  rewrite (length_app (o_E so) [x]). cbn [length].
  assert (Hmono : (pro_idx (o_cs so) (length (o_E so) `div` length echo_line)
                   <= pro_idx (o_cs so)
                        ((length (o_E so) + 1) `div` length echo_line))%nat).
  { apply pro_idx_mono. apply Nat.Div0.div_le_mono. lia. }
  split.
  - apply (ps_len_ok_empty_above so); [exact Hok |]. rewrite /ps_round.
    exact Hmono.
  - intros Ho ps' Hp Hne. exfalso.
    destruct Ho as [Hz | [Hm H3]]; [lia |].
    assert (Hd : (length (o_E so) `div` length echo_line
                  = (length (o_E so) + 1) `div` length echo_line - 1)%nat)
      by (by apply div_succ_of_mod0).
    assert (Hq1 : (1 <= (length (o_E so) + 1) `div` length echo_line)%nat).
    { destruct (decide ((length (o_E so) + 1) `div` length echo_line = 0)%nat)
        as [Hz | Hz]; [| lia].
      exfalso.
      pose proof (Nat.div_mod_eq (length (o_E so) + 1) (length echo_line)) as Hdm.
      rewrite Hz Hm in Hdm. lia. }
    assert (Heq : pro_idx (o_cs so) ((length (o_E so) + 1) `div` length echo_line)
                  = S (pro_idx (o_cs so)
                         (length (o_E so) `div` length echo_line))).
    { rewrite Hd.
      replace ((length (o_E so) + 1) `div` length echo_line)%nat
        with (S ((length (o_E so) + 1) `div` length echo_line - 1))%nat at 1
        by lia.
      apply pro_idx_S3. exact H3. }
    rewrite Heq in Hne. apply Hne.
    assert (Hnil : pro_from
                     (S (pro_idx (o_cs so)
                           (length (o_E so) `div` length echo_line))) (o_ps so)
                   = []) by exact HA.
    assert (Hnil' : pro_from
                      (S (pro_idx (o_cs so)
                            (length (o_E so) `div` length echo_line))) ps' = []).
    { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
    by rewrite Hnil Hnil'.
Qed.

(* ...AND THE FOURTH MOVE, the one the prologue-choice write makes: filing
   the open round's alternative CLOSES it (nothing is left over, so (A)
   holds again) and puts its first byte on the wire (so (B) does). *)
Lemma ps_len_ok_pro (so : ostage) (a : nat) (b : bv 8) :
  (ps_round so <= pro_rounds (o_ps so))%nat ->
  ~ pro_done (pro_from (ps_round so) (o_ps so)) ->
  o_w so = pending (o_ps so) (o_cs so) (o_E so) ->
  ps_len_ok so ->
  ps_len_ok (MkO (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so ++ [b])).
Proof.
  intros Hle Hnd Hw [HA HB].
  rewrite /ps_len_ok /ps_round /ps_opens in HA, HB, Hle, Hnd |- *.
  cbn [o_ps o_cs o_E o_w] in HA, HB, Hle, Hnd |- *. split.
  - replace (S (pro_idx (o_cs so) (length (o_E so) `div` length echo_line)))
      with (pro_idx (o_cs so) (length (o_E so) `div` length echo_line) + 1)%nat
      by lia.
    rewrite -pro_from_add (pro_from_snoc_le _ (o_ps so) a Hle).
    cbn [pro_from]. by apply pro_tail_open_snoc.
  - intros Ho ps' Hp Hne. rewrite (length_app (o_w so) [b]). cbn [length].
    destruct (decide (length ps' <= length (o_ps so))%nat) as [Hlen | Hlen].
    + assert (Hp2 : ps' `prefix_of` o_ps so).
      { destruct (prefix_weak_total ps' (o_ps so) (o_ps so ++ [a]) Hp
                    ltac:(by eexists)) as [H | H]; [exact H |].
        rewrite (prefix_length_eq _ _ H ltac:(lia)). reflexivity. }
      pose proof (prefix_length _ _ (pending_n_ps_mono ps' (o_ps so) (o_cs so)
                    (length (o_E so)) Hp2)) as Hlp.
      rewrite -/(pending (o_ps so) (o_cs so) (o_E so)) -Hw in Hlp. lia.
    + rewrite (prefix_length_eq ps' (o_ps so ++ [a]) Hp) in Hne;
        last by (rewrite (length_app (o_ps so) [a]); cbn [length]; lia).
      by destruct (Hne eq_refl).
Qed.

(* E's entries, read off the log: the ECHOED ones with their histories
   projected to the cycle.  [EchoOutPure.echoed] keeps the raw histories --
   which is what [read_window_prefix] is stated over -- and this is its
   cycle-relative image, which is what the stage carries. *)
Definition seg_of (l : list (list mobs * bv 8)) : list (list mobs * bv 8) :=
  (fun x => (open_seg x.1, x.2)) <$> l.

Lemma seg_of_snd (l : list (list mobs * bv 8)) : snd <$> seg_of l = snd <$> l.
Proof.
  induction l as [| x l IH]; [done |].
  change (seg_of (x :: l)) with ((open_seg x.1, x.2) :: seg_of l).
  by rewrite !fmap_cons IH.
Qed.

Lemma seg_of_app (l1 l2 : list (list mobs * bv 8)) :
  seg_of (l1 ++ l2) = seg_of l1 ++ seg_of l2.
Proof. by rewrite /seg_of fmap_app. Qed.

Lemma seg_of_length (l : list (list mobs * bv 8)) : length (seg_of l) = length l.
Proof. by rewrite /seg_of length_fmap. Qed.

(* ====================================================================== *)
(*  1b.  THE ERA'S PROCESS-BYTE CURSOR (review S2)                         *)
(* ====================================================================== *)

(* how many PROCESS bytes the transcript [D ps cs E ++ w] contains: one
   [pending_n] block per echoed input, plus what is written of the current
   block.  A [Fixpoint] from the left with the stage index as accumulator,
   for [D_from]'s reason exactly. *)
Fixpoint pcount_from (ps cs : list nat) (k : nat)
    (E : list (list mobs * bv 8)) : nat :=
  match E with
  | [] => 0%nat
  | _ :: E' => (length (pending_n ps cs k) + pcount_from ps cs (S k) E')%nat
  end.

Definition pcount (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) : nat := (pcount_from ps cs 0 E + length w)%nat.

Lemma pcount_from_app ps cs k E1 E2 :
  pcount_from ps cs k (E1 ++ E2)
  = (pcount_from ps cs k E1 + pcount_from ps cs (k + length E1) E2)%nat.
Proof.
  revert k. induction E1 as [| x E1 IH]; intros k; cbn.
  - by rewrite Nat.add_0_r.
  - rewrite IH.
    replace (S k + length E1)%nat with (k + S (length E1))%nat by lia. lia.
Qed.

(* A WRITE MOVES IT BY ONE *)
Lemma pcount_write ps cs E w b : pcount ps cs E (w ++ [b]) = S (pcount ps cs E w).
Proof. rewrite /pcount length_app /=. lia. Qed.

(* ...AND THE ECHO LEAVES IT ALONE, which is the whole point: the block the
   echo folds into [D] is exactly the [w] that was already counted. *)
Lemma pcount_echo ps cs E x w :
  w = pending ps cs E -> pcount ps cs (E ++ [x]) [] = pcount ps cs E w.
Proof.
  intros ->. rewrite /pcount pcount_from_app /pending.
  replace (0 + length E)%nat with (length E) by lia.
  cbn [pcount_from length]. lia.
Qed.

(* THE ERA'S PROCESS BYTES AS ONE STREAM: every block the stage owes, in
   order.  Spelled off [pending_n] and not off [line_alts] directly, so that
   it is DEFINITIONALLY ALIGNED with [pcount] -- [proc_upto_length] below is
   one induction, and the cursor is literally an index into this list.  Only
   the choices [cs !!! j] for [j] below the last completed line are read, so a
   mono_list LOWER BOUND of [cs] determines any prefix of it, which is what a
   writer holds. *)
Fixpoint proc_upto_from (ps cs : list nat) (k n : nat) : list (bv 8) :=
  match n with
  | 0%nat => []
  | S n' => pending_n ps cs k ++ proc_upto_from ps cs (S k) n'
  end.

Definition proc_upto (ps cs : list nat) (n : nat) : list (bv 8) :=
  proc_upto_from ps cs 0 n.

(* THE ALIGNMENT: the cursor counts exactly the bytes of this stream. *)
Lemma proc_upto_from_length ps cs k E :
  length (proc_upto_from ps cs k (length E)) = pcount_from ps cs k E.
Proof.
  revert k. induction E as [| x E IH]; intros k; cbn; [done |].
  by rewrite length_app IH.
Qed.

Lemma proc_upto_length ps cs E :
  length (proc_upto ps cs (length E)) = pcount_from ps cs 0 E.
Proof. apply proc_upto_from_length. Qed.

Lemma proc_upto_from_S ps cs k n :
  proc_upto_from ps cs k (S n) = pending_n ps cs k ++ proc_upto_from ps cs (S k) n.
Proof. reflexivity. Qed.

Lemma proc_upto_from_snoc ps cs k n :
  proc_upto_from ps cs k (S n) = proc_upto_from ps cs k n ++ pending_n ps cs (k + n).
Proof.
  revert k. induction n as [| n IH]; intros k.
  - cbn [proc_upto_from]. by rewrite app_nil_r Nat.add_0_r.
  - rewrite (proc_upto_from_S ps cs k (S n)) (IH (S k))
            (proc_upto_from_S ps cs k n) app_assoc.
    f_equal. f_equal. lia.
Qed.

Lemma proc_upto_snoc ps cs n :
  proc_upto ps cs (S n) = proc_upto ps cs n ++ pending_n ps cs n.
Proof.
  assert (H0 : (0 + n)%nat = n) by lia.
  rewrite /proc_upto (proc_upto_from_snoc ps cs 0 n). by rewrite ?H0.
Qed.

Lemma proc_upto_mono ps cs n m :
  (n <= m)%nat -> proc_upto ps cs n `prefix_of` proc_upto ps cs m.
Proof.
  intros Hnm. induction Hnm as [| m Hnm IH]; [reflexivity |].
  etrans; [exact IH |]. rewrite proc_upto_snoc. by eexists.
Qed.

(* THE CURSOR IS AN INDEX INTO IT.  Forward: what the stage owes at [length w]
   is what the stream has at [pcount]. *)
Lemma proc_upto_pcount ps cs E w b :
  pending ps cs E !! length w = Some b ->
  proc_upto ps cs (S (length E)) !! pcount ps cs E w = Some b.
Proof.
  intros Hb. rewrite proc_upto_snoc /pcount -proc_upto_length.
  rewrite lookup_app_r; [| lia].
  replace (length (proc_upto ps cs (length E)) + length w
           - length (proc_upto ps cs (length E)))%nat with (length w) by lia.
  exact Hb.
Qed.

(* ...and back, which is the direction a WRITER needs.  THE STRICTNESS
   PREMISE IS NOT DECORATION: at [length w = length (pending ps cs E)] the cursor
   indexes the FIRST byte of the NEXT block, which the stream has and the
   stage does not owe -- writing it would be writing past the continuation,
   before the echo that closes the line.  The program supplies it; see
   [eout_step_write]. *)
Lemma proc_upto_pcount_inv ps cs E w N b :
  (S (length E) <= N)%nat ->
  (length w < length (pending ps cs E))%nat ->
  proc_upto ps cs N !! pcount ps cs E w = Some b ->
  pending ps cs E !! length w = Some b.
Proof.
  intros HN Hlt Hl.
  destruct (lookup_lt_is_Some_2 (pending ps cs E) (length w) Hlt) as [b' Hb'].
  pose proof (proc_upto_pcount ps cs E w b' Hb') as Hfwd.
  assert (Heq : proc_upto ps cs N !! pcount ps cs E w = Some b')
    by (eapply prefix_lookup_Some;
        [exact Hfwd | apply (proc_upto_mono ps cs _ N HN)]).
  assert (Hbb : b = b') by congruence. by rewrite Hbb.
Qed.

(* THE CHOICES ARE READ ONLY BELOW THE LAST COMPLETED LINE, so a lower bound
   of [cs] fixes the stream (review S9) -- and the PROLOGUE a "3" block
   re-enters is read only where [ps] has already settled it, which is what
   [pro_pin] says. *)
Lemma pending_n_cs_ext ps cs0 cs k :
  cs0 `prefix_of` cs ->
  ((k `div` length echo_line) <= length cs0)%nat ->
  pending_n ps cs0 k = pending_n ps cs k.
Proof.
  intros Hp Hk. rewrite /pending_n.
  case_decide as H0; [done |].
  case_decide as Hm; [| done].
  pose proof echo_line_length as HL.
  assert (Hq : (1 <= k `div` length echo_line)%nat).
  { destruct (decide (k `div` length echo_line = 0)%nat) as [Hd | Hd]; [| lia].
    exfalso. pose proof (Nat.div_mod_eq k (length echo_line)) as Hdm.
    rewrite Hd Hm in Hdm. lia. }
  assert (Hlk : forall j, (j < k `div` length echo_line)%nat ->
                  cs0 !!! j = cs !!! j).
  { intros j Hj. destruct Hp as [z ->].
    rewrite !list_lookup_total_alt lookup_app_l; [done | lia]. }
  rewrite /alt_cont (Hlk (k `div` length echo_line - 1)%nat ltac:(lia)).
  by rewrite (pro_idx_ext cs0 cs (k `div` length echo_line) Hlk
                (k `div` length echo_line - 1)%nat ltac:(lia)).
Qed.

(* a LOWER BOUND reads the same choice wherever it reaches *)
Lemma lookup_total_prefix (cs0 cs : list nat) (i : nat) :
  cs0 `prefix_of` cs -> (i < length cs0)%nat -> cs !!! i = cs0 !!! i.
Proof.
  intros [z ->] Hi. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Lemma pending_n_cs_prefix ps0 ps cs0 cs k :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  ((k `div` length echo_line) <= length cs0)%nat ->
  (pro_idx cs0 (k `div` length echo_line) < pro_rounds ps0)%nat ->
  pending_n ps0 cs0 k = pending_n ps cs k.
Proof.
  intros Hps Hcs Hk Hr.
  rewrite (pending_n_ps_ext ps0 ps cs0 k Hps Hr).
  by apply pending_n_cs_ext.
Qed.

Lemma proc_upto_from_ext ps0 ps cs0 cs k n :
  (forall j, (k <= j)%nat -> (j < k + n)%nat -> pending_n ps0 cs0 j = pending_n ps cs j) ->
  proc_upto_from ps0 cs0 k n = proc_upto_from ps cs k n.
Proof.
  revert k. induction n as [| n IH]; intros k Hj; [done |].
  cbn [proc_upto_from]. rewrite (Hj k ltac:(lia) ltac:(lia)). f_equal.
  apply IH. intros j H1 H2. apply Hj; lia.
Qed.

(* the form the write lemma spends: a writer's lower bounds determine the
   stream as far as it can index into it *)
Lemma proc_upto_cs_prefix ps0 ps cs0 cs n :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 n ->
  (n <= length echo_line * length cs0)%nat ->
  proc_upto ps0 cs0 n = proc_upto ps cs n.
Proof.
  intros Hps Hcs Hpin Hn. rewrite /proc_upto. apply proc_upto_from_ext.
  intros j _ Hj. apply (pending_n_cs_prefix ps0 ps cs0 cs j Hps Hcs).
  - pose proof echo_line_length as HL. apply Nat.div_le_upper_bound; lia.
  - apply (pro_pin_at ps0 cs0 n j Hpin). lia.
Qed.

Lemma proc_upto_cs_mono ps0 ps cs0 cs n p b :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 n ->
  (n <= length echo_line * length cs0)%nat ->
  proc_upto ps0 cs0 n !! p = Some b -> proc_upto ps cs n !! p = Some b.
Proof.
  intros Hps Hcs Hpin Hn Hl.
  by rewrite -(proc_upto_cs_prefix ps0 ps cs0 cs n Hps Hcs Hpin Hn).
Qed.

(* THE TIGHT FORM, which is the one a writer can pay.  [proc_upto_cs_prefix]
   asks for [n <= 17 * length cs0], and at the era's FIRST block ([n = 1],
   [cs0 = []]) that is false while the conclusion is not: [pending_n ps cs 0]
   is the PROLOGUE and reads no LINE choice at all. *)
Lemma proc_upto_cs_prefix_S ps0 ps cs0 cs n0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 (S n0) ->
  ((n0 `div` length echo_line) <= length cs0)%nat ->
  proc_upto ps0 cs0 (S n0) = proc_upto ps cs (S n0).
Proof.
  intros Hps Hcs Hpin Hn. rewrite /proc_upto. apply proc_upto_from_ext.
  intros j _ Hj. apply (pending_n_cs_prefix ps0 ps cs0 cs j Hps Hcs).
  - etrans; [| exact Hn]. apply Nat.Div0.div_le_mono. lia.
  - apply (pro_pin_at ps0 cs0 (S n0) j Hpin). lia.
Qed.

(* ...AND THE ONE THE ORDINARY WRITE ACTUALLY HOLDS.  While the writer is
   inside the current block -- writing the banner of a restart's prologue,
   say -- that block's ROUND has not settled, so the stream is only a
   PREFIX of the claim's.  A prefix is all a byte lookup needs. *)
Lemma proc_upto_prefix_S ps0 ps cs0 cs n0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 n0 ->
  ((n0 `div` length echo_line) <= length cs0)%nat ->
  proc_upto ps0 cs0 (S n0) `prefix_of` proc_upto ps cs (S n0).
Proof.
  intros Hps Hcs Hpin Hn. rewrite !proc_upto_snoc.
  assert (Heq : proc_upto ps0 cs0 n0 = proc_upto ps cs n0).
  { rewrite /proc_upto. apply proc_upto_from_ext.
    intros j _ Hj. apply (pending_n_cs_prefix ps0 ps cs0 cs j Hps Hcs).
    - etrans; [| exact Hn]. apply Nat.Div0.div_le_mono. lia.
    - apply (pro_pin_at ps0 cs0 n0 j Hpin). lia. }
  rewrite Heq. apply prefix_app.
  rewrite (pending_n_cs_ext ps0 cs0 cs n0 Hcs Hn).
  by apply pending_n_ps_mono.
Qed.

(* THE BLOCK-BOUNDARY FORM (REVISION 7(d)).  At the first byte of block [q]'s
   continuation the ledger's choice list is one SHORT -- that write is what
   extends it -- so [proc_upto_cs_prefix_S] cannot be used there. *)
Lemma proc_upto_cs_prefix_pred ps0 ps cs0 cs n :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 n ->
  (((n - 1) `div` length echo_line) <= length cs0)%nat ->
  proc_upto ps0 cs0 n = proc_upto ps cs n.
Proof.
  intros Hps Hcs Hpin Hn. rewrite /proc_upto. apply proc_upto_from_ext.
  intros j _ Hj. apply (pending_n_cs_prefix ps0 ps cs0 cs j Hps Hcs).
  - etrans; [| exact Hn]. apply Nat.Div0.div_le_mono. lia.
  - apply (pro_pin_at ps0 cs0 n j Hpin). lia.
Qed.

(* the same extension law for the TRANSCRIPT and the CURSOR: both read
   [pending_n ps cs j] for [j < length E] only. *)
Lemma D_from_ext ps0 ps cs0 cs k E :
  (forall j, (k <= j)%nat -> (j < k + length E)%nat ->
     pending_n ps0 cs0 j = pending_n ps cs j) ->
  D_from ps0 cs0 k E = D_from ps cs k E.
Proof.
  revert k. induction E as [| x E IH]; intros k Hj; [done |].
  assert (Hrec : D_from ps0 cs0 (S k) E = D_from ps cs (S k) E).
  { apply IH. intros j H1 H2. apply Hj; cbn [length]; lia. }
  cbn [D_from length]. rewrite (Hj k ltac:(lia) ltac:(cbn [length]; lia)).
  by rewrite Hrec.
Qed.

Lemma pcount_from_ext ps0 ps cs0 cs k E :
  (forall j, (k <= j)%nat -> (j < k + length E)%nat ->
     pending_n ps0 cs0 j = pending_n ps cs j) ->
  pcount_from ps0 cs0 k E = pcount_from ps cs k E.
Proof.
  revert k. induction E as [| x E IH]; intros k Hj; [done |].
  assert (Hrec : pcount_from ps0 cs0 (S k) E = pcount_from ps cs (S k) E).
  { apply IH. intros j H1 H2. apply Hj; cbn [length]; lia. }
  cbn [pcount_from length].
  rewrite (Hj k ltac:(lia) ltac:(cbn [length]; lia)). by rewrite Hrec.
Qed.

Lemma cs_ext_pred ps0 ps cs0 cs n :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 n ->
  (((n - 1) `div` length echo_line) <= length cs0)%nat ->
  forall j, (0 <= j)%nat -> (j < 0 + n)%nat ->
    pending_n ps0 cs0 j = pending_n ps cs j.
Proof.
  intros Hps Hcs Hpin Hn j _ Hj.
  apply (pending_n_cs_prefix ps0 ps cs0 cs j Hps Hcs).
  - etrans; [| exact Hn]. apply Nat.Div0.div_le_mono. lia.
  - apply (pro_pin_at ps0 cs0 n j Hpin). lia.
Qed.

Lemma D_cs_prefix ps0 ps cs0 cs E :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 (length E) ->
  (((length E - 1) `div` length echo_line) <= length cs0)%nat ->
  D ps0 cs0 E = D ps cs E.
Proof.
  intros Hps Hcs Hpin Hn. rewrite /D.
  apply D_from_ext, (cs_ext_pred ps0 ps cs0 cs (length E) Hps Hcs Hpin Hn).
Qed.

Lemma pcount_cs_prefix ps0 ps cs0 cs E :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin ps0 cs0 (length E) ->
  (((length E - 1) `div` length echo_line) <= length cs0)%nat ->
  pcount_from ps0 cs0 0%nat E = pcount_from ps cs 0%nat E.
Proof.
  intros Hps Hcs Hpin Hn.
  apply pcount_from_ext, (cs_ext_pred ps0 ps cs0 cs (length E) Hps Hcs Hpin Hn).
Qed.

(* the cursor at zero pins the stage: [pending_n ps cs 0] is [u_prologue], which
   is not empty, so an echoed input already costs bytes *)
Lemma pcount_zero ps cs E w :
  pcount ps cs E w = 0%nat -> E = [] /\ w = [].
Proof.
  rewrite /pcount. intros H0.
  assert (Hw : w = []) by (apply nil_length_inv; lia).
  destruct E as [| x E]; [by split |]. exfalso.
  cbn [pcount_from] in H0.
  assert (Hp0 : pending_n ps cs 0%nat = pro_of ps) by reflexivity.
  rewrite Hp0 in H0. pose proof (pro_of_pos ps). lia.
Qed.

(* [w] stays a prefix once the byte it is owed is appended *)
Lemma prefix_snoc_lookup {A} (w l : list A) (b : A) :
  w `prefix_of` l -> l !! length w = Some b -> (w ++ [b]) `prefix_of` l.
Proof.
  intros [z ->] Hl. rewrite lookup_app_r in Hl; [| lia].
  rewrite Nat.sub_diag in Hl.
  destruct z as [| c z]; [discriminate |]. cbn in Hl. injection Hl as <-.
  exists z. by rewrite -app_assoc.
Qed.

(* THE WRITE'S WHOLE PURE ARGUMENT (the coordinator's ruling of 2026-09-14).
   The writer names [cs0] (a lower bound of the era's choices), [n0] (a lower
   bound of the era's stage index -- in the program's terms [17 q], a line
   boundary) and its cursor [P], and knows only that its byte is the [P]-th
   of the stream up to stage [S n0].  That ALONE pins the stage: the case
   [length E > n0] is refuted because the next line's first echo folds block
   [q]'s WHOLE alternative into the stream, so the cursor could not still be
   indexing inside block [q]; and at [length E = n0] the index [P] lands
   strictly inside the continuation, which is the strictness premise
   [proc_upto_pcount_inv] asks for -- so the writer never has to supply it. *)
Lemma write_stage_byte (ps0 ps cs0 cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) (n0 P : nat) (b : bv 8) :
  ps0 `prefix_of` ps ->
  pro_pin ps0 cs0 n0 ->
  cs0 `prefix_of` cs ->
  ((n0 `div` length echo_line) <= length cs0)%nat ->
  (n0 <= length E)%nat ->
  P = pcount ps cs E w ->
  proc_upto ps0 cs0 (S n0) !! P = Some b ->
  length E = n0 /\ pending ps cs E !! length w = Some b.
Proof.
  intros Hps Hpin Hp Hdiv Hn0 HP Hb.
  pose proof (prefix_lookup_Some _ _ _ _ Hb
                (proc_upto_prefix_S ps0 ps cs0 cs n0 Hps Hp Hpin Hdiv)) as Hb'.
  clear Hb. rename Hb' into Hb.
  assert (Hlt : (P < length (proc_upto ps cs (S n0)))%nat)
    by (by apply lookup_lt_Some in Hb).
  assert (HlenE : length E = n0).
  { destruct (decide (length E = n0)) as [? | Hne]; [done | exfalso].
    assert (HSn : (S n0 <= length E)%nat) by lia.
    pose proof (proc_upto_mono ps cs (S n0) (length E) HSn) as Hpre.
    apply prefix_length in Hpre.
    rewrite (proc_upto_length ps cs E) in Hpre.
    rewrite HP /pcount in Hlt. lia. }
  split; [exact HlenE |].
  rewrite -HlenE in Hb, Hlt.
  assert (Hstrict : (length w < length (pending ps cs E))%nat).
  { rewrite proc_upto_snoc length_app (proc_upto_length ps cs E) in Hlt.
    rewrite HP /pcount in Hlt. rewrite /pending. lia. }
  eapply (proc_upto_pcount_inv ps cs E w (S (length E)) b);
    [lia | exact Hstrict | by rewrite -HP].
Qed.

(* ====================================================================== *)
(*  1c.  THE BANNER OF AN ARBITRARY PROLOGUE ROUND                         *)
(* ====================================================================== *)

(* WHAT INIT'S RESTART LOOP PAYS THE WRITE LINK WITH.  Init prints the
   banner at the head of EVERY round: round 0 at boot, and one more each
   time the shell dies on its own [fork1] panic ([line_alts !!! 3]) or its
   child fails to exec ([pro_alts !!! 1], which re-enters the SAME round).
   [echo_write_link] asks for [proc_upto ps0 cs0 (S n0) !! P = Some b]; this
   discharges it at an ARBITRARY round, off two facts the loop has: the
   block's SHAPE (its panic line, if any, and then this round's prologue --
   [EchoOutPure.pending_n_round_pre] supplies it from the round-opening
   premise) and the round's resolution so far, which while the round is open
   is a block of [1]s ([EchoDisc.pro_open_replicate]).  No [vm_compute]: [j]
   and the round index are variables. *)
Lemma proc_upto_round_banner (ps cs : list nat) (n j i : nat)
      (pre : list (bv 8)) (b : bv 8) :
  pending_n ps cs n
  = pre ++ pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps) ->
  pro_from (pro_idx cs (n `div` length echo_line)) ps = replicate j 1%nat ->
  u_banner !! i = Some b ->
  proc_upto ps cs (S n)
    !! (length (proc_upto ps cs n) + length pre + pro_round * j + i)%nat
  = Some b.
Proof.
  intros Hshape Hopen Hb.
  rewrite proc_upto_snoc Hshape Hopen.
  replace (length (proc_upto ps cs n) + length pre + pro_round * j + i)%nat
    with (length (proc_upto ps cs n) + (length pre + (pro_round * j + i)))%nat
    by lia.
  rewrite (lookup_app_shift (proc_upto ps cs n)) (lookup_app_shift pre).
  by apply pro_of_replicate_banner.
Qed.

(* ...and the same with the block's shape read off the round-opening premise
   itself, which is the form the loop applies. *)
Lemma proc_upto_round_banner_open (ps cs : list nat) (n j i : nat) (b : bv 8) :
  (n `mod` length echo_line)%nat = 0%nat ->
  (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
  pro_from (pro_idx cs (n `div` length echo_line)) ps = replicate j 1%nat ->
  u_banner !! i = Some b ->
  proc_upto ps cs (S n)
    !! (length (proc_upto ps cs n)
        + length (if decide (n = 0%nat) then [] else line_alts !!! 3%nat)
        + pro_round * j + i)%nat
  = Some b.
Proof.
  intros Hm Ho Hopen Hb.
  apply (proc_upto_round_banner ps cs n j i _ b);
    [by apply pending_n_round_pre | exact Hopen | exact Hb].
Qed.

(* ANTI-VACUITY.  The prologue-choice link's premises are SATISFIABLE AT
   ROUND 1 -- the round init opens after the shell's own [fork1] panic.  One
   line has been echoed and took [line_alts !!! 3] ("fork\n"), the boot
   round settled with the prompt ([ps0 = [0]]), and the writer stands at the
   choice byte 43 process bytes into the era: 20 for [u_prologue], 5 for the
   panic line and 18 for the new round's banner. *)
Lemma pro_choice_round1_live :
  (17 `mod` length echo_line)%nat = 0%nat
  /\ (17%nat = 0%nat
      \/ [3%nat] !!! (17 `div` length echo_line - 1)%nat = 3%nat)
  /\ ((17 `div` length echo_line) <= length [3%nat])%nat
  /\ pro_pin [0%nat] [3%nat] 17
  /\ ~ pro_done (pro_from (pro_idx [3%nat] (17 `div` length echo_line)) [0%nat])
  /\ length (proc_upto [0%nat] [3%nat] (S 17)) = 43%nat
  /\ (0 < length pro_alts)%nat
  /\ (exists b : bv 8, pro_alts !!! 0%nat !! 0%nat = Some b).
Proof.
  pose proof echo_line_length as HL. split_and!.
  - by rewrite HL.
  - right. by rewrite HL.
  - rewrite HL. cbn [length]. vm_compute (17 `div` 17)%nat. lia.
  - intros q Hq. rewrite HL in Hq.
    assert (q = 0%nat) by lia. subst q. vm_compute. lia.
  - rewrite HL.
    assert (Hz : pro_from (pro_idx [3%nat] (17 `div` 17)) [0%nat] = [])
      by (by vm_compute).
    rewrite Hz. intros H. by apply Exists_nil in H.
  - by vm_compute.
  - rewrite pro_alts_length. lia.
  - destruct (pro_alts !!! 0%nat) as [| c t] eqn:Hz;
      [ vm_compute in Hz; discriminate | exists c; reflexivity ].
Qed.

(* the INPUT claim's pure fact, in BOTH its arms (the settled one and the
   chain-first window): the log's own account of the era, plus the two index
   laws for the entries the log has echoed and the bound on the era's line
   choices that a READER hands on to a later block-first WRITE.

   IT IS THE SAME PROPOSITION IN BOTH ARMS.  What separates them is the
   window counter -- [length (echoed pops)] in the settled arm, one more in
   the window arm -- and nothing pure: the entry the window owes is named by
   [ein_pend] below, which the echo hands to the append, and never by the
   port's own claim.  That is what makes the DROP arm ([cs = []], which does
   not move [echoed pops]) leave both arms exactly where they stood.

   [E_index]/[E_byte] ARE HERE and not only in the output claim because
   SH-LINE reads the line off the READ's window ([ein_read_line]) and holds
   no output claim: [read_ret] exports them. *)
Definition ein_pure (k : nat) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) (cs0 : list nat) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg (open_seg (le_hist e)))
  /\ (forall e, e ∈ pops -> obs_boots (le_hist e) = k)
  /\ dl `prefix_of` echoed pops
  /\ E_index (seg_of (echoed pops))
  /\ E_byte (seg_of (echoed pops))
  /\ ((length (echoed pops) `div` length echo_line) <= S (length cs0))%nat.

Lemma epu_removelast_prefix {A} (l : list A) : removelast l `prefix_of` l.
Proof.
  induction l as [| x l IH]; [done |].
  destruct l as [| y l']; [apply prefix_nil |].
  change (removelast (x :: y :: l')) with (x :: removelast (y :: l')).
  by apply prefix_cons.
Qed.

Lemma epu_lookup_nil_absurd {A} (j : nat) (x : A) :
  ([] : list A) !! j = Some x -> False.
Proof. intros Hx. apply lookup_lt_Some in Hx. cbn in Hx. lia. Qed.

Lemma eout_pure_0 k ho : eout_pure k ho ostage0 [].
Proof.
  rewrite /eout_pure /ostage0. cbn [o_ps o_cs o_E o_w]. split_and!.
  - rewrite D_nil. done.
  - rewrite pending_nil. apply prefix_nil.
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
  - constructor.
  - intros q Hq. cbn [length] in Hq. lia.
  - constructor.
  - constructor.
  - constructor.
  - cbn [length]. lia.
  - by left.
Qed.

Lemma cs_len_ok_0 : cs_len_ok ostage0.
Proof.
  rewrite /ostage0. apply (cs_len_ok_intro [] [] []); intros _;
    cbn [length]; by rewrite Nat.Div0.div_0_l.
Qed.

Lemma log_ok_nil : log_ok [].
Proof.
  split.
  - intros e He. by apply elem_of_nil in He.
  - intros i e1 e2 H1 H2. destruct (epu_lookup_nil_absurd i e1 H1).
Qed.

Lemma echoed_nil : echoed [] = [].
Proof. rewrite /echoed. by rewrite filter_nil. Qed.
Lemma ein_pure_0 k : ein_pure k [] [] [].
Proof.
  rewrite /ein_pure. split_and!.
  - exact log_ok_nil.
  - intros e He. by apply elem_of_nil in He.
  - intros e He. by apply elem_of_nil in He.
  - apply prefix_nil.
  - intros j x Hx. rewrite /seg_of echoed_nil fmap_nil in Hx.
    destruct (epu_lookup_nil_absurd j x Hx).
  - intros j x Hx. rewrite /seg_of echoed_nil fmap_nil in Hx.
    destruct (epu_lookup_nil_absurd j x Hx).
  - rewrite echoed_nil. cbn [length]. rewrite Nat.Div0.div_0_l. lia.
Qed.

(* ---- how the log's echoed slice moves at an append ---- *)
Lemma echoed_snoc_yes (pops : list log_entry) (e : log_entry) :
  log_echoed e ->
  echoed (pops ++ [e]) = echoed pops ++ [(le_hist e, le_byte e)].
Proof.
  intros He. induction pops as [| a l IH].
  - cbn [app]. rewrite /echoed (epu_filter_cons_T log_echoed e [] He).
    by rewrite filter_nil.
  - cbn [app]. rewrite /echoed in IH |- *.
    destruct (decide (log_echoed a)) as [Ha | Ha].
    + rewrite !(epu_filter_cons_T log_echoed a _ Ha) !fmap_cons.
      by rewrite IH.
    + rewrite !(epu_filter_cons_F log_echoed a _ Ha). by rewrite IH.
Qed.

Lemma echoed_snoc_no (pops : list log_entry) (e : log_entry) :
  ~ log_echoed e -> echoed (pops ++ [e]) = echoed pops.
Proof.
  intros He. induction pops as [| a l IH].
  - cbn [app]. rewrite /echoed (epu_filter_cons_F log_echoed e [] He).
    by rewrite filter_nil.
  - cbn [app]. rewrite /echoed in IH |- *.
    destruct (decide (log_echoed a)) as [Ha | Ha].
    + rewrite !(epu_filter_cons_T log_echoed a _ Ha) !fmap_cons.
      by rewrite IH.
    + rewrite !(epu_filter_cons_F log_echoed a _ Ha). by rewrite IH.
Qed.

(* a dropped byte is not an echoed entry: [[]] is not [[echo_of c]] *)
Lemma log_echoed_nil_no (h : list mobs) (c : bv 8) :
  ~ log_echoed (h, c, []).
Proof. rewrite /log_echoed /le_echo /le_byte /=. discriminate. Qed.

Lemma log_echoed_echo (h : list mobs) (c : bv 8) :
  log_echoed (h, c, [echo_of c]).
Proof. by rewrite /log_echoed /le_echo /le_byte /=. Qed.

(* AN OUTPUT CLAIM AT [acc = []] STANDS AT THE START OF ITS ERA.  Nothing
   but the empty stage has an empty transcript: the first echo folds the
   whole PROLOGUE into [D], and the prologue is not empty. *)
Lemma eout_pure_nil_stage (k : nat) (ho : list mobs) (so : ostage) :
  eout_pure k ho so [] -> pcount (o_ps so) (o_cs so) (o_E so) (o_w so) = 0%nat.
Proof.
  intros (Hacc & _).
  assert (Hlen : (length (D (o_ps so) (o_cs so) (o_E so)) + length (o_w so))%nat = 0%nat)
    by (rewrite -length_app -Hacc; reflexivity).
  destruct (o_E so) as [| y E1] eqn:HE.
  - rewrite /pcount. cbn [pcount_from]. lia.
  - exfalso.
    assert (HD : D (o_ps so) (o_cs so) (y :: E1)
                 = pro_of (o_ps so)
                   ++ ([echo_of y.2] ++ D_from (o_ps so) (o_cs so) 1%nat E1))
      by reflexivity.
    assert (Hup : (0 < length (D (o_ps so) (o_cs so) (y :: E1)))%nat).
    { rewrite HD length_app. pose proof (pro_of_pos (o_ps so)). lia. }
    lia.
Qed.

(* THE ECHO'S OWN ENTRY IS NOT IN THE LOG, and that is a PURE fact about the
   two histories: [WpUart.in_append]'s order premise puts every logged
   history strictly below [h], the era stamps put the two in one cycle, and
   an [open_seg] can only grow when the history does.  This is what refutes
   the SETTLED arm at the append (an arm that says the entry has already
   been filed) and it is [open_seg_prefix_boots] with the strictness kept. *)
Lemma open_seg_hist_ext (h1 h2 : list mobs) :
  hist_ext h1 h2 -> obs_boots h1 = obs_boots h2 ->
  trace_shape h2 true -> hist_ext (open_seg h1) (open_seg h2).
Proof.
  intros [[k Hk] Hlt] Hb Hsh. subst h2.
  assert (Hk0 : obs_boots k = 0%nat)
    by (rewrite obs_boots_app in Hb; lia).
  rewrite /trace_shape foldl_app in Hsh.
  destruct (foldl obs_step (Some false) h1) as [st |] eqn:Hst; last first.
  { rewrite epu_foldl_obs_step_none in Hsh. discriminate. }
  destruct (epu_no_power_of_boots k st Hk0 Hsh) as [_ HF].
  rewrite (open_seg_io h1 k HF). split; [by eexists |].
  rewrite length_app. rewrite length_app in Hlt. lia.
Qed.

(* A PREFIX THAT STOPS SHORT OF THE LAST EVENT. *)
Lemma prefix_snoc_lt {A : Type} (l1 l2 : list A) (x : A) :
  l1 `prefix_of` (l2 ++ [x]) -> (length l1 <= length l2)%nat ->
  l1 `prefix_of` l2.
Proof.
  intros Hp Hlen.
  assert (Hl1 : l1 = take (length l1) l2).
  { rewrite -(take_app_le l2 [x] (length l1) Hlen).
    destruct Hp as [z Hz]. rewrite Hz. by rewrite take_app_length. }
  rewrite Hl1. apply prefix_take.
Qed.

(* THE ECHO'S ONE CALLER-OWED PREMISE, AND WHERE IT COMES FROM.  [Hlt] says
   the echoes the era has already LOGGED answer inputs strictly below this
   one.  It is not a fact the claim states: it is the ORDER PREMISE the
   kernel hands the echo, read against the log's own index law.  The last
   logged entry's segment is a STRICT prefix of this one
   ([open_seg_hist_ext]) and this one ENDS in the input, so the entry's
   segment stops short of that input and carries strictly fewer of them. *)
Lemma echoed_lt_ins (k : nat) (h : list mobs) (c : bv 8)
    (pops : list log_entry) (dl : list (list mobs * bv 8)) (cs0 : list nat) :
  trace_shape h true -> obs_boots h = k -> obs_ends_in Uart0 h c ->
  (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
  ein_pure k pops dl cs0 ->
  (length (echoed pops) < length (ins (open_seg h)))%nat.
Proof.
  intros Hsh Hk Hends Hord (Hlog & Hdsc & Hstamp & Hdlp & Hidx & Hbyte & Hbnd).
  destruct (open_seg_ends_in h c Hends) as [h0 Hh0].
  assert (Hlen0 : length (ins (open_seg h)) = S (length (ins h0))).
  { rewrite Hh0 ins_app ins_in length_app. cbn [length]. lia. }
  destruct (decide (length (echoed pops) = 0%nat)) as [Hz | Hz]; [lia |].
  destruct (lookup_lt_is_Some_2 (echoed pops)
              ((length (echoed pops) - 1)%nat) ltac:(lia)) as [y Hy].
  assert (Hsy : seg_of (echoed pops) !! ((length (echoed pops) - 1)%nat)
                = Some (open_seg y.1, y.2))
    by (by rewrite /seg_of list_lookup_fmap Hy).
  destruct (Hidx _ _ Hsy) as [_ Hylen]. cbn [fst] in Hylen.
  assert (Hyin : y ∈ echoed pops) by (by eapply elem_of_list_lookup_2).
  destruct (echoed_elem_inv pops y Hyin) as (e & He & _ & Hye).
  assert (Hoe : open_seg (le_hist e) = open_seg y.1) by (by rewrite -Hye).
  destruct (open_seg_hist_ext (le_hist e) h (Hord e He)
              (eq_trans (Hstamp e He) (eq_sym Hk)) Hsh) as [Hpre Hlt2].
  rewrite Hoe Hh0 in Hpre. rewrite Hoe Hh0 length_app in Hlt2.
  cbn [length] in Hlt2.
  pose proof (prefix_snoc_lt (open_seg y.1) h0 (ObsUartIn Uart0 c) Hpre
                ltac:(lia)) as Hp0.
  pose proof (prefix_length _ _ (ins_prefix_of _ _ Hp0)) as Hle.
  rewrite Hylen in Hle. lia.
Qed.

(* ====================================================================== *)
(*  2.  THE GHOST NAMES AT THE FIXED PART                                  *)
(* ====================================================================== *)

(* [AppEcho.echo_fixed] becomes this record.  [eg_taint] is the landed
   counter and nothing about it moves; [eg_pin] is the ERA MAP, whose
   AUTHORITY is spent at exactly one place -- the ledger's power-on step,
   which allocates the era's ghosts and mints its pin.  No link touches it,
   which is what lets every link run without the ledger. *)
Record echo_gn := MkEchoGn {
  eg_taint : gname;   (* mono_nat: 0 while disciplined, 1 after -- LANDED *)
  eg_pin   : gname;   (* ghost_map nat era_pins: the era NUMBER's ghosts *)
}.

(* the ghosts of ONE era.  ALL FOUR LIVE IN THE CLAIMS (the design page's
   CLAIM-RESIDENT shape): the ledger holds none of them, and the pin below
   is the persistent name by which a claim, a writer and a reader mean the
   same era. *)
Record era_pins := MkPins {
  ep_go  : gname;   (* ghost_var nat: the era's PROCESS-BYTE CURSOR; the
                       output claim holds one half as [turn_auth], a writer
                       (init, through [app_turn]) the other *)
  ep_gcs : gname;   (* mono_list nat: the era's line choices; the output
                       claim holds the authority, everyone else a lower
                       bound *)
  ep_gps : gname;   (* mono_list nat: the era's PROLOGUE choices, in wire
                       order -- one per round of init's restart loop, the
                       first round at the boot and one more after every
                       line that took [line_alts !!! 3] (the shell's own
                       fork panic).  Same shape as [ep_gcs]: the output
                       claim holds the authority, a writer a lower bound *)
  ep_gE  : gname;   (* mono_list (list mobs * bv 8): the era's ECHOED LIST;
                       the output claim holds the authority, the input claim
                       a lower bound at the log's own slice *)
  ep_gw  : gname;   (* ghost_var nat: the WINDOW COUNTER, in four quarters:
                       one in the output claim, one in the input claim, two
                       in the kernel-lent token [ewin] *)
  ep_gdl : gname;   (* ghost_var nat: the DELIVERED COUNT, in two halves --
                       one in the input claim at [length dl], one in the
                       READER's hand.  A read hands its half over and gets
                       it back advanced, and the agreement inside the link
                       is what tells the reader WHERE in the line its window
                       fell: [read_link] hides the invariant's [dl], and
                       [ein_read_line]/[ein_read_byte] cannot run without
                       it. *)
}.

(* THE ERA MAP'S BOUND.  Every era the ledger has ever founded is at most
   the boot count of the ledger's own history, so the era a POWER-ON starts
   -- [S (obs_boots h)] -- is absent from the map and the insert is legal.
   This is the only thing in the ledger besides the taint counter and the
   phi conjunct that reads the history, and no LINK reads it. *)
Definition pin_dom {A : Type} (M : gmap nat A) (n : nat) : Prop :=
  forall k, is_Some (M !! k) -> (k <= n)%nat.

Lemma pin_dom_empty {A : Type} (n : nat) : pin_dom (∅ : gmap nat A) n.
Proof. intros k [x Hx]. by rewrite lookup_empty in Hx. Qed.

Lemma pin_dom_absent {A : Type} (M : gmap nat A) (n : nat) :
  pin_dom M n -> M !! (S n) = None.
Proof.
  intros Hd. destruct (M !! S n) as [x |] eqn:Hx; [| reflexivity].
  exfalso. specialize (Hd (S n) (ex_intro _ x Hx)). lia.
Qed.

Lemma pin_dom_insert {A : Type} (M : gmap nat A) (n : nat) (a : A) :
  pin_dom M n -> pin_dom (<[S n := a]> M) (S n).
Proof.
  intros Hd k Hk. destruct (decide (k = S n)) as [-> | Hne]; [lia |].
  rewrite lookup_insert_ne in Hk; [| lia]. specialize (Hd k Hk). lia.
Qed.

Class echoOutG (Σ : gFunctors) := EchoOutG {
  eo_mono_nat : mono_natG Σ;
  eo_turn     : ghost_varG Σ nat;
  eo_pin      : ghost_mapG Σ nat era_pins;
  eo_cs       : inG Σ (mono_listR (leibnizO nat));
  eo_El       : inG Σ (mono_listR (leibnizO (list mobs * bv 8)));
}.
#[global] Existing Instances eo_mono_nat eo_turn eo_pin eo_cs eo_El.

(* THE FUNCTOR BUNDLE, and the standard [subG] instance (lane ECHO-OUT part
   5).  [AppEcho] and everything above it takes [echoOutG Σ] as a section
   context; a CLOSED corollary that instantiates
   [App.xv6_app_adequacy] at a CONCRETE [Σ] discharges the class from its own
   bundle by this instance -- exactly as every other Iris library does.  The
   only closed corollaries in the tree today are the TRIVIAL application's
   ([SystemAdequacy.xv6_trace_adequacy] and its siblings, at [xv6Σ]), which
   never mention this class, so nothing in the tree needs [echoOutΣ] yet;
   it exists so that the echo's closed theorem can be stated without
   re-opening this file. *)
Definition echoOutΣ : gFunctors :=
  #[ mono_natΣ; ghost_varΣ nat; ghost_mapΣ nat era_pins;
     GFunctor (mono_listR (leibnizO nat));
     GFunctor (mono_listR (leibnizO (list mobs * bv 8))) ].

Global Instance subG_echoOutΣ {Σ} : subG echoOutΣ Σ -> echoOutG Σ.
Proof. solve_inG. Qed.

Section echo_out.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  (* THE TAINT, ABSTRACTLY.  [AppEcho.echo_taint] is [mono_nat_lb_own
     (eg_taint γ) 1]; this file takes it as a parameter so that it sits
     BELOW [AppEcho] and the two claims can be read without the era-0 pin
     cone. *)
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.


  (* ---- the era's ghosts, keyed by the ERA NUMBER ---- *)

  (* PERSISTENT: era [k]'s ghosts.  Keyed by the era NUMBER, so a claim at
     [k] and a writer agree on which ghosts they mean by function
     application, and no injectivity obligation arises anywhere. *)
  Definition era_pin (k : nat) (v : era_pins) : iProp Σ :=
    ghost_map_elem (eg_pin γ) k DfracDiscarded v.

  Global Instance era_pin_persistent k v : Persistent (era_pin k v).
  Proof. rewrite /era_pin. apply _. Qed.
  Global Instance era_pin_timeless k v : Timeless (era_pin k v).
  Proof. rewrite /era_pin. apply _. Qed.

  Lemma era_pin_agree k v v' : era_pin k v -∗ era_pin k v' -∗ ⌜v = v'⌝.
  Proof.
    rewrite /era_pin. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. exact Heq.
  Qed.

  (* THE CURSOR: the era's process-byte count, in two halves.  The OUTPUT
     CLAIM holds one ([turn_auth], always at the stage's own [pcount]); the
     other travels in the programs' payloads (init's [app_turn], then fork
     [Rc], exit/wait [Q]).  THE ECHO NEVER TOUCHES IT ([pcount_echo]). *)
  Definition turn (v : era_pins) (P : nat) : iProp Σ :=
    ghost_var (ep_go v) (1/2) P.
  Definition turn_auth (v : era_pins) (P : nat) : iProp Σ :=
    ghost_var (ep_go v) (1/2) P.

  Global Instance turn_timeless v P : Timeless (turn v P).
  Proof. rewrite /turn. apply _. Qed.
  Global Instance turn_auth_timeless v P : Timeless (turn_auth v P).
  Proof. rewrite /turn_auth. apply _. Qed.

  Lemma turn_agree v P P' : turn v P -∗ turn_auth v P' -∗ ⌜P = P'⌝.
  Proof.
    rewrite /turn /turn_auth. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. iPureIntro. exact Heq.
  Qed.

  Lemma turn_update v P P' P'' :
    turn v P -∗ turn_auth v P' ==∗ turn v P'' ∗ turn_auth v P''.
  Proof.
    rewrite /turn /turn_auth. iIntros "H1 H2".
    iMod (ghost_var_update_halves P'' with "H1 H2") as "[H1 H2]".
    iModIntro. iFrame "H1 H2".
  Qed.

  (* THE LINE CHOICES, as a monotone list: the output claim holds the
     authority, a writer holds a persistent lower bound (review S9). *)
  Definition cs_auth (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gcs v) (●ML (l : list (leibnizO nat))).
  Definition cs_lb (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gcs v) (◯ML (l : list (leibnizO nat))).

  Global Instance cs_lb_persistent v l : Persistent (cs_lb v l).
  Proof. rewrite /cs_lb. apply _. Qed.
  Global Instance cs_lb_timeless v l : Timeless (cs_lb v l).
  Proof. rewrite /cs_lb. apply _. Qed.
  Global Instance cs_auth_timeless v l : Timeless (cs_auth v l).
  Proof. rewrite /cs_auth. apply _. Qed.

  Lemma cs_lb_get v l : cs_auth v l -∗ cs_auth v l ∗ cs_lb v l.
  Proof.
    rewrite /cs_auth /cs_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML (l : list (leibnizO nat))) with "H")
      as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma cs_auth_grow v l a :
    cs_auth v l ==∗ cs_auth v (l ++ [a]) ∗ cs_lb v (l ++ [a]).
  Proof.
    rewrite /cs_auth /cs_lb. iIntros "H".
    iMod (own_update _ _ (●ML ((l ++ [a]) : list (leibnizO nat)))
            with "H") as "H".
    { apply mono_list_update. by eexists. }
    iModIntro. iDestruct (own_mono _ _ (◯ML ((l ++ [a]) : list (leibnizO nat)))
                            with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma cs_lb_prefix v l l' : cs_auth v l -∗ cs_lb v l' -∗ ⌜l' `prefix_of` l⌝.
  Proof.
    rewrite /cs_auth /cs_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  (* THE PROLOGUE CHOICES, the same monotone list one round later: the
     output claim holds the authority, a writer a persistent lower bound.
     A writer's bound is worth a PREFIX of the stream and not an equality
     while the round it is standing in has not settled ([pro_pin],
     [proc_upto_prefix_S]) -- which is exactly the difference between the
     banner and the byte that chooses. *)
  Definition ps_auth (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gps v) (●ML (l : list (leibnizO nat))).
  Definition ps_lb (v : era_pins) (l : list nat) : iProp Σ :=
    own (ep_gps v) (◯ML (l : list (leibnizO nat))).

  Global Instance ps_lb_persistent v l : Persistent (ps_lb v l).
  Proof. rewrite /ps_lb. apply _. Qed.
  Global Instance ps_lb_timeless v l : Timeless (ps_lb v l).
  Proof. rewrite /ps_lb. apply _. Qed.
  Global Instance ps_auth_timeless v l : Timeless (ps_auth v l).
  Proof. rewrite /ps_auth. apply _. Qed.

  Lemma ps_lb_get v l : ps_auth v l -∗ ps_auth v l ∗ ps_lb v l.
  Proof.
    rewrite /ps_auth /ps_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML (l : list (leibnizO nat))) with "H")
      as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma ps_auth_grow v l a :
    ps_auth v l ==∗ ps_auth v (l ++ [a]) ∗ ps_lb v (l ++ [a]).
  Proof.
    rewrite /ps_auth /ps_lb. iIntros "H".
    iMod (own_update _ _ (●ML ((l ++ [a]) : list (leibnizO nat)))
            with "H") as "H".
    { apply mono_list_update. by eexists. }
    iModIntro. iDestruct (own_mono _ _ (◯ML ((l ++ [a]) : list (leibnizO nat)))
                            with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma ps_lb_prefix v l l' : ps_auth v l -∗ ps_lb v l' -∗ ⌜l' `prefix_of` l⌝.
  Proof.
    rewrite /ps_auth /ps_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  (* THE ERA'S ECHOED LIST, as a monotone list of ENTRIES (and no longer a
     mono_nat of its length).  The OUTPUT claim holds the authority; the
     INPUT claim holds a lower bound AT THE LOG'S OWN SLICE
     ([seg_of (echoed pops)]), and that bound -- read against the authority
     at the echo, and against the append's own carried bound at the append
     -- is what ties the log to the era's stage now that no ledger sees
     both.  A writer's [E_lb] is still just its LENGTH. *)
  Definition Elist_auth (v : era_pins) (E : list (list mobs * bv 8)) : iProp Σ :=
    own (ep_gE v) (●ML (E : list (leibnizO (list mobs * bv 8)))).
  Definition Elist_lb (v : era_pins) (E : list (list mobs * bv 8)) : iProp Σ :=
    own (ep_gE v) (◯ML (E : list (leibnizO (list mobs * bv 8)))).

  Global Instance Elist_lb_persistent v E : Persistent (Elist_lb v E).
  Proof. rewrite /Elist_lb. apply _. Qed.
  Global Instance Elist_lb_timeless v E : Timeless (Elist_lb v E).
  Proof. rewrite /Elist_lb. apply _. Qed.
  Global Instance Elist_auth_timeless v E : Timeless (Elist_auth v E).
  Proof. rewrite /Elist_auth. apply _. Qed.

  Lemma Elist_lb_get v E : Elist_auth v E -∗ Elist_auth v E ∗ Elist_lb v E.
  Proof.
    rewrite /Elist_auth /Elist_lb. iIntros "H".
    iDestruct (own_mono _ _ (◯ML (E : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma Elist_auth_grow v E x :
    Elist_auth v E ==∗ Elist_auth v (E ++ [x]) ∗ Elist_lb v (E ++ [x]).
  Proof.
    rewrite /Elist_auth /Elist_lb. iIntros "H".
    iMod (own_update _ _
            (●ML ((E ++ [x]) : list (leibnizO (list mobs * bv 8))))
            with "H") as "H".
    { apply mono_list_update. by eexists. }
    iModIntro.
    iDestruct (own_mono _ _
                 (◯ML ((E ++ [x]) : list (leibnizO (list mobs * bv 8))))
                 with "H") as "#Hl"; [apply mono_list_included |].
    iFrame "H Hl".
  Qed.

  Lemma Elist_prefix v E E' :
    Elist_auth v E -∗ Elist_lb v E' -∗ ⌜E' `prefix_of` E⌝.
  Proof.
    rewrite /Elist_auth /Elist_lb. iIntros "Ha Hl".
    iDestruct (own_valid_2 with "Ha Hl") as %Hv.
    iPureIntro. by apply mono_list_both_valid_L in Hv.
  Qed.

  (* TWO LOWER BOUNDS OF ONE ERA'S LIST ARE COMPARABLE, and that -- with the
     two lengths, which the window counter supplies -- is the whole of the
     append's tie to its own echo. *)
  Lemma Elist_lb_cmp v E1 E2 :
    Elist_lb v E1 -∗ Elist_lb v E2 -∗
      ⌜E1 `prefix_of` E2 \/ E2 `prefix_of` E1⌝.
  Proof.
    rewrite /Elist_lb. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro. by apply mono_list_lb_op_valid_L in Hv.
  Qed.

  Lemma Elist_lb_weaken v E E' :
    E' `prefix_of` E -> Elist_lb v E -∗ Elist_lb v E'.
  Proof.
    intros Hp. rewrite /Elist_lb. iApply own_mono.
    apply mono_list_lb_mono. exact Hp.
  Qed.

  (* THE WRITER'S BOUND is the LENGTH of a lower bound, which is all a
     program can name: it knows [17 q], never the entries. *)
  Definition E_lb (v : era_pins) (n : nat) : iProp Σ :=
    (∃ E : list (list mobs * bv 8), Elist_lb v E ∗ ⌜length E = n⌝)%I.

  Global Instance E_lb_persistent v n : Persistent (E_lb v n).
  Proof. rewrite /E_lb. apply _. Qed.
  Global Instance E_lb_timeless v n : Timeless (E_lb v n).
  Proof. rewrite /E_lb. apply _. Qed.

  Lemma E_lb_of_lb v E n :
    (n <= length E)%nat -> Elist_lb v E -∗ E_lb v n.
  Proof.
    intros Hn. iIntros "H".
    iDestruct (Elist_lb_weaken v E (take n E) (prefix_take E n) with "H")
      as "H'".
    iExists (take n E). iFrame "H'". iPureIntro. by rewrite length_take_le.
  Qed.

  (* THE LAW THE WRITE SPENDS: the lower bound never exceeds the length. *)
  Lemma E_lb_le v E n : Elist_auth v E -∗ E_lb v n -∗ ⌜(n <= length E)%nat⌝.
  Proof.
    iIntros "Ha Hl". iDestruct "Hl" as (E') "[Hl %Hlen]".
    iDestruct (Elist_prefix with "Ha Hl") as %Hp.
    iPureIntro. rewrite -Hlen. by apply prefix_length.
  Qed.

  (* THE WINDOW COUNTER, in quarters (see the file header). *)
  Definition wcnt (v : era_pins) (q : Qp) (n : nat) : iProp Σ :=
    ghost_var (ep_gw v) q n.

  Global Instance wcnt_timeless v q n : Timeless (wcnt v q n).
  Proof. rewrite /wcnt. apply _. Qed.

  Lemma wcnt_agree v q1 q2 n1 n2 :
    wcnt v q1 n1 -∗ wcnt v q2 n2 -∗ ⌜n1 = n2⌝.
  Proof.
    rewrite /wcnt. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. iPureIntro. exact Heq.
  Qed.

  Lemma wcnt_split v q1 q2 n :
    wcnt v (q1 + q2)%Qp n -∗ wcnt v q1 n ∗ wcnt v q2 n.
  Proof. rewrite /wcnt. iApply ghost_var_split. Qed.

  Lemma wcnt_join v q1 q2 n :
    wcnt v q1 n -∗ wcnt v q2 n -∗ wcnt v (q1 + q2)%Qp n.
  Proof.
    rewrite /wcnt. iIntros "H1 H2". iCombine "H1 H2" as "H". iExact "H".
  Qed.

  Lemma wcnt_update3 v q1 q2 q3 n1 n2 n3 m :
    (q1 + q2 + q3 = 1)%Qp ->
    wcnt v q1 n1 -∗ wcnt v q2 n2 -∗ wcnt v q3 n3 ==∗
      wcnt v q1 m ∗ wcnt v q2 m ∗ wcnt v q3 m.
  Proof.
    intros Hq. iIntros "H1 H2 H3".
    iDestruct (wcnt_agree with "H1 H2") as %<-.
    iDestruct (wcnt_agree with "H1 H3") as %<-.
    iDestruct (wcnt_join v q2 q3 n1 with "H2 H3") as "H23".
    rewrite /wcnt.
    iMod (ghost_var_update_2 m with "H1 H23") as "[$ H23]";
      [by rewrite Qp.add_assoc |].
    iModIntro. iApply (wcnt_split v q2 q3 m with "H23").
  Qed.

  (* THE DELIVERED COUNT, in two halves: the input claim's and the
     reader's. *)
  Definition dl_cnt (v : era_pins) (q : Qp) (n : nat) : iProp Σ :=
    ghost_var (ep_gdl v) q n.

  Global Instance dl_cnt_timeless v q n : Timeless (dl_cnt v q n).
  Proof. rewrite /dl_cnt. apply _. Qed.

  Lemma dl_cnt_agree v q1 q2 n1 n2 :
    dl_cnt v q1 n1 -∗ dl_cnt v q2 n2 -∗ ⌜n1 = n2⌝.
  Proof.
    rewrite /dl_cnt. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. iPureIntro. exact Heq.
  Qed.

  Lemma dl_cnt_update v n1 n2 m :
    dl_cnt v (1/2) n1 -∗ dl_cnt v (1/2) n2 ==∗
      dl_cnt v (1/2) m ∗ dl_cnt v (1/2) m.
  Proof.
    rewrite /dl_cnt. iIntros "H1 H2".
    by iMod (ghost_var_update_halves m with "H1 H2") as "[$ $]".
  Qed.

  (* FIVE QUARTERS ARE IMPOSSIBLE, and that is what refutes a SECOND link of
     the run: the window arm holds a half, the token another half, and the
     output claim the last quarter. *)
  Lemma wcnt_over v n1 n2 n3 :
    wcnt v (1/4) n1 -∗ wcnt v (1/2) n2 -∗ wcnt v (1/2) n3 -∗ False.
  Proof.
    rewrite /wcnt. iIntros "H1 H2 H3".
    iDestruct (ghost_var_agree with "H2 H3") as %<-.
    iCombine "H2 H3" as "H".
    iDestruct (ghost_var_valid_2 with "H H1") as %[Hq _].
    iPureIntro. revert Hq. apply Qp.not_add_le_l.
  Qed.

  (* ====================================================================== *)
  (*  3.  THE TWO PORT CLAIMS, AT THE ERA NUMBER                            *)
  (* ====================================================================== *)

  (* THE OUTPUT CLAIM holds the era's FOUR AUTHORITIES (design page, section
     2): the cursor's other half, the choice list, the echoed list, and one
     quarter of the window counter at the stage's own length.  There is no
     FRESH arm any more: the era's claims are founded ONCE, at the ledger's
     power-on step ([echo_led_pow]), which is also where the pin is minted
     and the cursor's writer-half leaves as [eturn]. *)
  Definition eout (k : nat) (ho : list mobs) (acc : list (bv 8)) : iProp Σ :=
    ( T
    ∨ ∃ (v : era_pins) (so : ostage),
        era_pin k v
        ∗ turn_auth v (pcount (o_ps so) (o_cs so) (o_E so) (o_w so))
        ∗ cs_auth v (o_cs so)
        ∗ ps_auth v (o_ps so)
        ∗ Elist_auth v (o_E so)
        ∗ wcnt v (1/4) (length (o_E so))
        ∗ ⌜eout_pure k ho so acc /\ cs_len_ok so /\ ps_len_ok so
           /\ Forall (fun i => (i < length line_alts)%nat) (o_cs so)⌝)%I.

  (* THE INPUT CLAIM has TWO non-taint arms, and they differ only in the
     window counter: SETTLED (the log and the era's echoed list agree) and
     the chain-first WINDOW (the echo's byte is on the wire, its log entry
     still owed, so the era's list is one ahead).  The window arm holds a
     HALF -- its own quarter plus a quarter of the token the kernel lent the
     shift -- so a second link of the run, which arrives holding the whole
     half-token, meets five quarters. *)
  Definition ein (k : nat) (hi : list mobs) (pops : list log_entry)
      (dl : list (list mobs * bv 8)) : iProp Σ :=
    ( T
    ∨ (∃ (v : era_pins) (n : nat) (cs0 ps0 : list nat),
         era_pin k v ∗ wcnt v (1/4) n ∗ dl_cnt v (1/2) (length dl)
         ∗ ⌜length (echoed pops) = n⌝
         ∗ Elist_lb v (seg_of (echoed pops)) ∗ cs_lb v cs0 ∗ ps_lb v ps0
         ∗ ⌜ein_pure k pops dl cs0⌝)
    ∨ (∃ (v : era_pins) (n : nat) (cs0 ps0 : list nat),
         era_pin k v ∗ wcnt v (1/2) n ∗ dl_cnt v (1/2) (length dl)
         ∗ ⌜(length (echoed pops) + 1)%nat = n⌝
         ∗ Elist_lb v (seg_of (echoed pops)) ∗ cs_lb v cs0 ∗ ps_lb v ps0
         ∗ ⌜ein_pure k pops dl cs0⌝))%I.

  (* THE ECHO WINDOW TOKEN -- [RiscvPtsto.riscv_win_res] once lane CONS-IO F
     lands, and [App.app_win A c] on the record.  It rides the PLIC payload
     beside the receive token, is a premise of [cons_echo_shift], and comes
     back in [in_append]'s post.  ITS TAINT ARM is what a licence route and
     an already-tainted era pay through: once the discipline is broken every
     claim is free, and so is the token. *)
  Definition ewin (k : nat) : iProp Σ :=
    (T ∨ ∃ (v : era_pins) (n : nat), era_pin k v ∗ wcnt v (1/2) n)%I.

  (* INIT'S CONSOLE CREDENTIAL for the era -- [App.app_turn A c], carried by
     the kernel from [App.Hpow] to [App.Hinit_boot].  It is the era's cursor
     at ZERO with the two bounds a write spends, which is exactly
     [echo_write_link]'s argument list at [P = 0]: no special first-write
     step exists, because at [P = 0] the claim's own [turn_auth] and
     [pcount_zero] DERIVE [acc = []]. *)
  Definition eturn (k : nat) : iProp Σ :=
    (∃ v : era_pins,
       era_pin k v ∗ turn v 0%nat ∗ dl_cnt v (1/2) 0%nat
       ∗ cs_lb v [] ∗ ps_lb v [] ∗ E_lb v 0%nat)%I.

  (* THE TAG -- [App.app_tag A c], and [AppEcho.echo_tag γ] with the taint
     abstracted, which is what [Happ_echo]'s tag equation says.  It is what
     the kernel hands the shift about the history the byte arrived at: the
     machine is on, and either the console is still disciplined or the
     application has already been paid off. *)
  Definition etag (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜disc h⌝ ∨ T))%I.

  Global Instance etag_persistent h : Persistent (etag h).
  Proof. rewrite /etag. apply _. Qed.
  Global Instance etag_timeless h : Timeless (etag h).
  Proof. rewrite /etag. apply _. Qed.

  Global Instance eout_timeless k ho acc : Timeless (eout k ho acc).
  Proof. rewrite /eout. apply _. Qed.
  Global Instance ein_timeless k hi pops dl : Timeless (ein k hi pops dl).
  Proof. rewrite /ein. apply _. Qed.
  Global Instance ewin_timeless k : Timeless (ewin k).
  Proof. rewrite /ewin. apply _. Qed.
  Global Instance eturn_timeless k : Timeless (eturn k).
  Proof. rewrite /eturn. apply _. Qed.

  (* ---- THE LICENCES ([App.Happ_out_sup] / [Happ_in_sup]) ---- *)
  Lemma eout_of_taint k ho acc : T -∗ eout k ho acc.
  Proof. iIntros "HT". rewrite /eout. iLeft. iExact "HT". Qed.

  Lemma ein_of_taint k ho pops dl : T -∗ ein k ho pops dl.
  Proof. iIntros "HT". rewrite /ein. iLeft. iExact "HT". Qed.

  Lemma ewin_of_taint k : T -∗ ewin k.
  Proof. iIntros "HT". rewrite /ewin. iLeft. iExact "HT". Qed.

  Lemma eout_sup k ho acc b : T -∗ eout k ho acc ==∗ eout k ho (acc ++ [b]).
  Proof.
    iIntros "#HT _". iModIntro.
    iApply (eout_of_taint k ho (acc ++ [b])). iExact "HT".
  Qed.

  Lemma ein_sup_log k ho pops dl e :
    T -∗ ein k ho pops dl ==∗ ein k ho (pops ++ [e]) dl.
  Proof.
    iIntros "#HT _". iModIntro.
    iApply (ein_of_taint k ho (pops ++ [e]) dl). iExact "HT".
  Qed.

  Lemma ein_sup_deliv k ho pops dl ws :
    T -∗ ein k ho pops dl ==∗ ein k ho pops (dl ++ ws).
  Proof.
    iIntros "#HT _". iModIntro.
    iApply (ein_of_taint k ho pops (dl ++ ws)). iExact "HT".
  Qed.

  (* ====================================================================== *)
  (*  4.  THE LEDGER                                                        *)
  (* ====================================================================== *)

  (* WHAT IS LEFT OF IT.  The era machine is gone: an era's state is in its
     claims, and no link opens the ledger at all.  What stays is what is
     about the HISTORY -- the taint counter, the phi conjunct -- plus the
     ERA MAP, whose authority is spent at exactly one place, the power-on
     step below, which allocates the era's ghosts and mints its pin. *)
  Definition pin_map (h : list mobs) : iProp Σ :=
    (∃ Mp : gmap nat era_pins,
       ghost_map_auth (eg_pin γ) 1 Mp ∗ ⌜pin_dom Mp (obs_boots h)⌝)%I.

  Global Instance pin_map_timeless h : Timeless (pin_map h).
  Proof. rewrite /pin_map. apply _. Qed.

  (* an event that starts no era leaves the map exactly where it was *)
  Lemma pin_map_step (h : list mobs) (e : mobs) :
    obs_boots [e] = 0%nat -> pin_map h -∗ pin_map (h ++ [e]).
  Proof.
    intros He. rewrite /pin_map obs_boots_app He Nat.add_0_r. by iIntros "$".
  Qed.

  (* ...and the POWER-ON mints the era's pin.  The insert is legal because
     the map's bound says every era ever founded is at most [obs_boots h],
     and this one is [S] of it. *)
  Lemma pin_map_on (h : list mobs) (v : era_pins) :
    pin_map h ==∗
      pin_map (h ++ [ObsPowerOn]) ∗ era_pin (S (obs_boots h)) v.
  Proof.
    rewrite /pin_map /era_pin obs_boots_app. cbn [obs_boots].
    rewrite Nat.add_1_r.
    iIntros "H". iDestruct "H" as (Mp) "[Hm %Hd]".
    iMod (ghost_map_insert_persist (S (obs_boots h)) v
            (pin_dom_absent _ _ Hd) with "Hm") as "[Hm #Hpin]".
    iModIntro. iFrame "Hpin". iExists _. iFrame "Hm".
    iPureIntro. by apply pin_dom_insert.
  Qed.

  (* ---- THE ERA'S GHOSTS AT FULL OWNERSHIP, and their split into the two
         claims, init's credential and the kernel's token ---- *)
  Definition era_full (v : era_pins) : iProp Σ :=
    (ghost_var (ep_go v) 1 0%nat ∗ cs_auth v [] ∗ ps_auth v [] ∗ Elist_auth v []
     ∗ ghost_var (ep_gw v) 1 0%nat ∗ ghost_var (ep_gdl v) 1 0%nat)%I.

  Global Instance era_full_timeless v : Timeless (era_full v).
  Proof. rewrite /era_full. apply _. Qed.

  Lemma era_full_alloc : ⊢ |==> ∃ v : era_pins, era_full v.
  Proof.
    iMod (ghost_var_alloc 0%nat) as (go) "Ht".
    iMod (own_alloc (●ML ([] : list (leibnizO nat)))) as (gcs) "Hcs";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO nat)))) as (gps) "Hps";
      [apply mono_list_auth_valid |].
    iMod (own_alloc (●ML ([] : list (leibnizO (list mobs * bv 8)))))
      as (gE) "HE"; [apply mono_list_auth_valid |].
    iMod (ghost_var_alloc 0%nat) as (gw) "Hw".
    iMod (ghost_var_alloc 0%nat) as (gdl) "Hdl".
    iModIntro. iExists (MkPins go gcs gps gE gw gdl).
    rewrite /era_full /cs_auth /ps_auth /Elist_auth /=.
    iFrame "Ht Hcs Hps HE Hw Hdl".
  Qed.

  Lemma pcount_nil (ps cs : list nat) : pcount ps cs [] [] = 0%nat.
  Proof. reflexivity. Qed.

  Lemma seg_of_echoed_nil : seg_of (echoed []) = [].
  Proof. by rewrite echoed_nil /seg_of fmap_nil. Qed.

  (* THE FOUNDING, as a resource split: the era's four ghosts become the two
     port claims at the start of their era, init's console credential, and
     the kernel's window token. *)
  Lemma era_full_split (k : nat) (v : era_pins) :
    era_pin k v -∗ era_full v -∗
      eout k [] [] ∗ ein k [] [] [] ∗ eturn k ∗ ewin k.
  Proof.
    iIntros "#Hpin (Ht & Hcs & Hps & HE & Hw & Hdl)".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct (ghost_var_split with "Ht") as "[Ht1 Ht2]".
    iEval (rewrite -Qp.half_half) in "Hdl".
    iDestruct (ghost_var_split with "Hdl") as "[Hdl1 Hdl2]".
    iEval (rewrite -Qp.half_half) in "Hw".
    iDestruct (ghost_var_split with "Hw") as "[Hw12 Hwh]".
    iEval (rewrite -Qp.quarter_quarter) in "Hw12".
    iDestruct (ghost_var_split with "Hw12") as "[Hw1 Hw2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (Elist_lb_get with "HE") as "[HE #HElb]".
    iSplitL "Ht1 Hcs Hps HE Hw1".
    { rewrite /eout. iRight. iExists v, ostage0.
      cbn [o_ps o_cs o_E o_w ostage0 length]. rewrite pcount_nil.
      iFrame "Hpin Ht1 Hcs Hps HE Hw1". iPureIntro. split_and!.
      - exact (eout_pure_0 k []).
      - exact cs_len_ok_0.
      - exact ps_len_ok_0.
      - constructor. }
    iSplitL "Hw2 Hdl1".
    { rewrite /ein. iRight. iLeft. iExists v, 0%nat, [], [].
      rewrite seg_of_echoed_nil echoed_nil. cbn [length].
      iFrame "Hpin Hw2 Hdl1 HElb Hcslb Hpslb". iPureIntro.
      split; [reflexivity | exact (ein_pure_0 k)]. }
    iSplitL "Ht2 Hdl2".
    { rewrite /eturn. iExists v. iFrame "Hpin Ht2 Hdl2 Hcslb Hpslb".
      iApply (E_lb_of_lb v [] 0%nat); [cbn; lia | iExact "HElb"]. }
    rewrite /ewin. iRight. iExists v, 0%nat. iFrame "Hpin Hwh".
  Qed.

  (* ...and THE WHOLE LEDGER, which is what [AppEcho.echo_R] becomes. *)
  Definition echo_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint γ) 1 (if decide (disc h) then 0%nat else 1%nat)
     ∗ pin_map h
     ∗ (⌜Forall good_out (cycles_of h)⌝ ∨ T))%I.

  Global Instance echo_led_timeless h : Timeless (echo_led h).
  Proof. rewrite /echo_led. apply _. Qed.

  (* WHAT THE BIRTH STEP YIELDS, i.e. what [AppEcho.echo_cl] becomes:
     [AppEcho.echo_birth] is two [own_alloc]s and this. *)
  Lemma echo_led_init :
    mono_nat_auth_own (eg_taint γ) 1 0%nat -∗
    ghost_map_auth (eg_pin γ) 1 (∅ : gmap nat era_pins) -∗
    echo_led [].
  Proof.
    iIntros "Ht Hm". rewrite /echo_led /pin_map.
    rewrite decide_True; [| exact disc_nil].
    iFrame "Ht".
    iSplitL "Hm".
    { iExists ∅. iFrame "Hm". iPureIntro. apply pin_dom_empty. }
    iLeft. iPureIntro. rewrite /cycles_of /cycles_rev /=. constructor.
  Qed.
  (* ====================================================================== *)
  (*  5.  THE LEDGER'S STEPS                                                *)
  (* ====================================================================== *)

  (* AN EVENT THAT PUTS NOTHING ON THE CONSOLE'S WIRE cannot falsify a cycle
     that was good: the wire is unchanged and [sess_n] only grows with the
     input count. *)
  Lemma good_out_step (seg : list mobs) (e : mobs) :
    obs_wire Uart0 [e] = [] -> good_out seg -> good_out (seg ++ [e]).
  Proof.
    intros He Hg. rewrite /good_out obs_wire_app He app_nil_r.
    apply (expected_rel_ins_mono (ins seg)); [| exact Hg].
    rewrite ins_app length_app. lia.
  Qed.

  Lemma obs_wire_in (i : uart_id) (b : bv 8) : obs_wire Uart0 [ObsUartIn i b] = [].
  Proof. by destruct i. Qed.

  Lemma obs_wire_out_other (i : uart_id) (b : bv 8) :
    i <> Uart0 -> obs_wire Uart0 [ObsUartOut i b] = [].
  Proof. intros Hi. destruct i; [by destruct Hi | done]. Qed.

  Lemma io_singleton (e : mobs) :
    is_io e = true -> Forall (fun x => is_io x = true) [e].
  Proof. intros He. constructor; [exact He | constructor]. Qed.

  (* THE MACHINE IS OFF AFTER A PowerOff, which is what makes [era_live]'s
     guarded conjunct vacuous there. *)
  Lemma trace_shape_off (h : list mobs) :
    trace_shape (h ++ [ObsPowerOff]) true -> False.
  Proof.
    rewrite /trace_shape foldl_app.
    destruct (foldl obs_step (Some false) h) as [[|] |]; by cbn.
  Qed.

  Lemma phi_step_io (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> obs_wire Uart0 [e] = [] ->
    Forall good_out (cycles_of h) -> Forall good_out (cycles_of (h ++ [e])).
  Proof.
    intros Hsh Hio Hw HF.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs Hlast].
    apply Forall_app. split; [exact Hcs |].
    rewrite Forall_singleton in Hlast. rewrite Forall_singleton.
    apply good_out_step; [exact Hw | exact Hlast].
  Qed.

  Lemma phi_step_cons (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true ->
    good_out (open_seg h ++ [e]) ->
    Forall good_out (cycles_of h) -> Forall good_out (cycles_of (h ++ [e])).
  Proof.
    intros Hsh Hio Hgo HF.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite H2. rewrite H1 in HF. apply Forall_app in HF as [Hcs _].
    apply Forall_app. split; [exact Hcs |].
    rewrite Forall_singleton. exact Hgo.
  Qed.

  (* THE POWER STEP -- AND THE FOUNDING OF THE ERA'S CLAIMS, ITS CURSOR AND
     ITS TOKEN (design page, section 2).  This is [App.Hpow]'s shape exactly:
     the on-arm allocates the era's four ghosts, mints its pin in the era map
     and splits the ghosts into the two port claims, init's console
     credential and the kernel's window token, at the era number
     [S (obs_boots h)] -- which [ObsTrace.obs_boots_app] makes the boot count
     of the POST-event history, i.e. the number the kernel's own stamp reads
     at every history of the new era.

     THIS IS THE ONLY STEP THAT TOUCHES THE ERA MAP'S AUTHORITY, which is
     what lets every link run without the ledger. *)
  Lemma echo_led_pow (h : list mobs) (on : bool) :
    echo_led h ==∗
      echo_led (h ++ [if on then ObsPowerOff else ObsPowerOn])
      ∗ (if on then emp
         else eout (S (obs_boots h)) [] [] ∗ ein (S (obs_boots h)) [] [] []
              ∗ eturn (S (obs_boots h)) ∗ ewin (S (obs_boots h))).
  Proof.
    iIntros "(Ht & Hpm & Hphi)". rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_power h on)).
    destruct on.
    - iDestruct (pin_map_step h ObsPowerOff eq_refl with "Hpm") as "Hpm".
      iModIntro. iSplitR ""; [| done]. iFrame "Ht Hpm".
      rewrite cycles_of_off. iExact "Hphi".
    - iMod era_full_alloc as (v) "Hfull".
      iMod (pin_map_on h v with "Hpm") as "[Hpm #Hpin]".
      iDestruct (era_full_split (S (obs_boots h)) v with "Hpin Hfull")
        as "(Hout & Hin & Hturn & Hwin)".
      iModIntro. iSplitR "Hout Hin Hturn Hwin".
      + iFrame "Ht Hpm".
        rewrite cycles_of_on.
        iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
        iLeft. iPureIntro. apply Forall_app. split; [exact Hg |].
        apply Forall_singleton. exact good_out_nil.
      + iFrame "Hout Hin Hturn Hwin".
  Qed.

  (* ...AND THE KERNEL'S OWN PORT COSTS NOTHING: [good_out] reads the
     CONSOLE's wire, so a byte on the other UART cannot falsify a cycle that
     was good ([phi_step_io]).  That is why the caller owes the segment's
     goodness only at [Uart0]. *)
  Lemma echo_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (T ∨ ⌜i = Uart0 -> good_out (open_seg h ++ [ObsUartOut i b])⌝) -∗
    echo_led h ==∗ echo_led (h ++ [ObsUartOut i b]).
  Proof.
    intros Hsh. iIntros "Hgo (Hcnt & Hpm & Hphi)".
    iDestruct (pin_map_step h (ObsUartOut i b) eq_refl with "Hpm") as "Hpm".
    rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_out h i b Hsh)).
    iModIntro. iFrame "Hcnt Hpm".
    iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
    iDestruct "Hgo" as "[HT | %Hgo]"; [by iRight |].
    iLeft. iPureIntro. destruct i.
    - exact (phi_step_cons h (ObsUartOut Uart0 b) Hsh eq_refl
               (Hgo eq_refl) Hg).
    - exact (phi_step_io h (ObsUartOut Uart1 b) Hsh eq_refl
               (obs_wire_out_other Uart1 b ltac:(discriminate)) Hg).
  Qed.

  Lemma echo_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    echo_led h ==∗
      echo_led (h ++ [ObsUartIn i b])
      ∗ (⌜disc (h ++ [ObsUartIn i b])⌝ ∨ mono_nat_lb_own (eg_taint γ) 1).
  Proof.
    intros Hsh. iIntros "(Hcnt & Hpm & Hphi)".
    iDestruct (pin_map_step h (ObsUartIn i b) eq_refl with "Hpm") as "Hpm".
    iAssert (⌜Forall good_out (cycles_of (h ++ [ObsUartIn i b]))⌝ ∨ T)%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
      iLeft. iPureIntro.
      apply (phi_step_io h (ObsUartIn i b) Hsh eq_refl (obs_wire_in i b) Hg). }
    rewrite /echo_led.
    destruct (decide (disc (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; last first.
      { destruct i;
          [ exact (disc_in h b Hsh Hd')
          | exact (proj1 (disc_other h (ObsUartIn Uart1 b) eq_refl I Hsh) Hd') ]. }
      iModIntro. iFrame "Hcnt Hpm Hphi". iLeft. iPureIntro. exact Hd'.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (disc h)); lia |].
      iModIntro. iFrame "Hcnt Hpm Hphi". iRight. iExact "Hlb".
  Qed.

  (* PHI's read at the end of the run, in the OWNER's form: the guard is the
     WHOLE history's discipline.  Once the taint is set [disc] is false
     forever ([EchoDisc.disc_prefix]), so the ledger's disjunction is exactly
     this implication. *)
  Lemma echo_led_phi (h : list mobs) :
    (T -∗ mono_nat_lb_own (eg_taint γ) 1) -∗
    echo_led h -∗ ⌜disc h -> Forall good_out (cycles_of h)⌝.
  Proof.
    iIntros "HTT (Hcnt & _ & [%Hg | HT'])".
    { iPureIntro. by intros _. }
    iDestruct ("HTT" with "HT'") as "Hlb".
    iDestruct (mono_nat_lb_own_valid with "Hcnt Hlb") as %[_ Hle].
    iPureIntro. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
  Qed.

  (* ====================================================================== *)
  (*  6.  THE STEPS THE LINKS SPEND                                         *)
  (* ====================================================================== *)

  (* NO STEP TAKES THE LEDGER.  Every authority an era has is in its claims,
     so a link opens the port invariant and nothing else -- which is what
     makes [App.Happ_echo] a CLOSED entailment (design page, F1). *)

  (* THE APPEND THE ECHO OWES, handed from [eout_step_echo] to
     [ein_step_append] inside the shift's own proof (it is not a port claim
     and the kernel never sees it).  It carries
       - a QUARTER of the window counter, split off the half the kernel lent
         the shift: it agrees with the half the window arm holds, which is
         how the append knows the arm is the one its own echo left;
       - a lower bound of the era's echoed list ENDING IN ITS OWN ENTRY, so
         that comparing it against the arm's bound (same monotone list, one
         entry shorter) says the arm owes exactly [(open_seg h, c)];
       - the two index laws for that list and the choice bound, which is
         what the settled arm the append rebuilds needs. *)
  Definition ein_pend (k : nat) (h : list mobs) (c : bv 8) : iProp Σ :=
    (T ∨ ∃ (v : era_pins) (n : nat) (El : list (list mobs * bv 8))
           (cs0 ps0 : list nat),
        era_pin k v ∗ wcnt v (1/4) n
        ∗ Elist_lb v (El ++ [(open_seg h, c)]) ∗ cs_lb v cs0 ∗ ps_lb v ps0
        ∗ ⌜(length El + 1)%nat = n⌝
        ∗ ⌜E_index (El ++ [(open_seg h, c)])⌝
        ∗ ⌜E_byte (El ++ [(open_seg h, c)])⌝
        ∗ ⌜(n `div` length echo_line <= S (length cs0))%nat⌝)%I.

  Global Instance ein_pend_timeless k h c : Timeless (ein_pend k h c).
  Proof. rewrite /ein_pend. apply _. Qed.

  (* ...and the claim's side of it: the pure fact is in both non-taint arms,
     so the echo's caller reads it off whatever arm it meets, and a tainted
     claim owes nothing. *)
  Lemma ein_lt (k : nat) (h : list mobs) (c : bv 8) (hi : list mobs)
      (pops : list log_entry) (dl : list (list mobs * bv 8)) :
    trace_shape h true -> obs_boots h = k -> obs_ends_in Uart0 h c ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    ein k hi pops dl -∗
      ein k hi pops dl
      ∗ (T ∨ ⌜(length (echoed pops) < length (ins (open_seg h)))%nat⌝).
  Proof.
    intros Hsh Hk Hends Hord. iIntros "Hin".
    iDestruct "Hin" as "[#HT | [Hs | Hwn]]".
    - iSplitR; [by iApply ein_of_taint | by iLeft].
    - iDestruct "Hs" as (v n cs0 ps0)
        "(#Hpin & Hwc & Hdl & %Hn & #HElb & #Hcslb & #Hpslb & %Hp)".
      iSplitL "Hwc Hdl".
      { rewrite /ein. iRight. iLeft. iExists v, n, cs0, ps0.
        iFrame "Hpin Hwc Hdl HElb Hcslb Hpslb". by iPureIntro. }
      iRight. iPureIntro.
      exact (echoed_lt_ins k h c pops dl cs0 Hsh Hk Hends Hord Hp).
    - iDestruct "Hwn" as (v n cs0 ps0)
        "(#Hpin & Hwc & Hdl & %Hn & #HElb & #Hcslb & #Hpslb & %Hp)".
      iSplitL "Hwc Hdl".
      { rewrite /ein. iRight. iRight. iExists v, n, cs0, ps0.
        iFrame "Hpin Hwc Hdl HElb Hcslb Hpslb". by iPureIntro. }
      iRight. iPureIntro.
      exact (echoed_lt_ins k h c pops dl cs0 Hsh Hk Hends Hord Hp).
  Qed.

  (* (E) THE ECHO SHIFT's core step, at the STORE arm: the byte goes out, the
     era's echoed list gains the entry, and the input claim comes back AT THE
     SAME [pops]/[dl] -- which is what [WpUart.echo_link] demands -- in its
     WINDOW arm.  The cursor is UNTOUCHED ([pcount_echo]), which is what lets
     this close with the writer absent (review S2).

     WHAT IT IS HANDED AND WHY.  [ewin k] is the kernel's per-era token
     ([riscv_win_res (S gen_id)], a premise of [cons_echo_shift] once lane
     CONS-IO F lands).  Its half plus the two claims' quarters are the whole
     of the window counter, so the three values AGREE: the era's echoed list
     is exactly as long as the log's echoed slice, and the input claim's
     lower bound then pins [seg_of (echoed pops) = o_E so].  That is the tie
     the old ledger's [stage_tie] was, and it is what re-establishes the
     output claim's same-cycle facts at the new witness [h]: the log's
     entries are below [h] ([Hord]) and carry the era's stamp, and two
     histories of one era with the machine on lie in one cycle
     ([EchoOutPure.open_seg_prefix_boots]).

     A SECOND FIRING IS REFUTED, not handled: it arrives with the token's
     half again and meets the window arm's half beside the output claim's
     quarter -- five quarters ([wcnt_over]).

     THE ONE CALLER-OWED PREMISE.  [Hlt] says the echoes the era has already
     LOGGED answer inputs strictly below this one; it holds at every call
     site -- [SpecConsoleintr.cons_echo_shift] fires once per accepted byte,
     at the history the byte arrived at. *)
  Lemma eout_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho hi : list mobs) (acc : list (bv 8))
      (pops : list log_entry) (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` acc ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    (length (echoed pops) < length (ins (open_seg h)))%nat ->
    ewin k -∗ eout k ho acc -∗ ein k hi pops dl ==∗
      eout k h (acc ++ [echo_of c]) ∗ ein k hi pops dl ∗ ein_pend k h c.
  Proof.
    intros Hdisc Hsh Hk Hends Hwire Hord Hlt. subst k.
    iIntros "Hwin Hout Hin".
    (* ANY taint -- the token's, either claim's -- pays outright *)
    iAssert (□ (T -∗ eout (obs_boots h) h (acc ++ [echo_of c])
                    ∗ ein (obs_boots h) hi pops dl
                    ∗ ein_pend (obs_boots h) h c))%I as "#Htaint".
    { iIntros "!> #HT". iSplitR; [by iApply eout_of_taint |].
      iSplitR; [by iApply ein_of_taint | by iLeft]. }
    iDestruct "Hwin" as "[#HT | Hwin]"; [iModIntro; by iApply "Htaint" |].
    iDestruct "Hout" as "[#HT | Hout]"; [iModIntro; by iApply "Htaint" |].
    iDestruct "Hin" as "[#HT | Hin]"; [iModIntro; by iApply "Htaint" |].
    iDestruct "Hwin" as (vw nw) "[#Hpinw Hww]".
    iDestruct "Hout" as (v so) "(#Hpin & Hta & Hcs & Hps & HE & Hwo & %Hall)".
    iDestruct (era_pin_agree with "Hpinw Hpin") as %->.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hcsb).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3).
    (* A SECOND FIRING meets the window arm: five quarters *)
    iDestruct "Hin" as "[Hs | Hwn]"; last first.
    { iDestruct "Hwn" as (v2 n2 cs2 ps2) "(#Hpin2 & Hw2 & _)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (wcnt_over with "Hwo Hw2 Hww") as "[]". }
    iDestruct "Hs" as (v2 n2 cs0 ps0i)
      "(#Hpin2 & Hwi & Hdli & %Hn2 & #HElbi & #Hcslbi & #Hpslbi & %Hpi)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    destruct Hpi as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi).
    (* THE THREE AGREEING SHARES, and with them the tie to the log *)
    iDestruct (wcnt_agree with "Hwo Hwi") as %Hoi.
    iDestruct (wcnt_agree with "Hwo Hww") as %How.
    iDestruct (Elist_prefix with "HE HElbi") as %Hprefi.
    assert (Hseg : seg_of (echoed pops) = o_E so).
    { apply prefix_length_eq; [exact Hprefi |].
      rewrite seg_of_length. lia. }
    (* the byte's own facts, as in the landed proof *)
    pose proof (disc_seg'_open_seg h Hsh Hdisc) as Hd'.
    pose proof (disc_seg'_proj _ Hd') as Hdseg.
    pose proof (open_seg_ends_in h c Hends) as Hends'.
    destruct (disc_seg'_pt_last (open_seg h) c Hd' Hends')
      as (ps' & cs' & Hok' & Hcs'b & Hlow').
    assert (Hprefixes : Forall (fun x => x.1 `prefix_of` open_seg h) (o_E so)).
    { rewrite -Hseg.
      apply Forall_lookup_2. intros j x Hx.
      rewrite /seg_of list_lookup_fmap in Hx.
      destruct (echoed pops !! j) as [y |] eqn:Hy; [| discriminate].
      cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [fst].
      assert (Hyin : y ∈ echoed pops) by (by eapply elem_of_list_lookup_2).
      destruct (echoed_elem_inv pops y Hyin) as (e & He & _ & Hye).
      apply open_seg_prefix_boots.
      - rewrite -Hye. cbn [fst]. by destruct (Hord e He) as [Hpre _].
      - rewrite -Hye. cbn [fst]. exact (Hstamp e He).
      - exact Hsh. }
    assert (Hnew' : forall x, x ∈ o_E so -> hist_ext x.1 (open_seg h)).
    { intros x Hx. apply elem_of_list_lookup in Hx as [jj Hj].
      destruct (Hidx jj x Hj) as [Hxe Hxlen].
      pose proof (Forall_lookup_1 _ _ _ _ Hprefixes Hj) as Hpx.
      apply lookup_lt_Some in Hj.
      split; [exact Hpx |].
      destruct Hpx as [z Hz]. destruct z as [| a z'].
      - exfalso. rewrite app_nil_r in Hz. rewrite -Hz in Hxlen. lia.
      - rewrite Hz length_app /=. lia. }
    assert (Hup : obs_wire Uart0 (open_seg h)
                  `prefix_of` (D (o_ps so) (o_cs so) (o_E so) ++ o_w so))
      by (rewrite -Hacc; exact Hwire).
    assert (Hbelow : sess_n ps' cs' (length (ins (open_seg h)) - 1)
                     `prefix_of` sess_n (o_ps so) (o_cs so) (length (o_E so))).
    { etrans; [exact Hlow' |]. etrans; [exact Hup |].
      by apply D_stage_prefix. }
    destruct (sess_n_prefix_det (o_ps so) ps' (o_cs so) cs'
                (length (ins (open_seg h)) - 1) (length (o_E so))
                Hpsb Hok' Hcsb' Hcs'b Hpin Hbelow) as (_ & Hokso & Heq).
    assert (Hlow : sess_n (o_ps so) (o_cs so) (length (ins (open_seg h)) - 1)
                   `prefix_of` obs_wire Uart0 (open_seg h)).
    { rewrite -Heq. exact Hlow'. }
    destruct (D2_next_input (o_ps so) (o_cs so) (o_E so) (o_w so)
                (obs_wire Uart0 (open_seg h)) (open_seg h) c
                (length (ins (open_seg h)))
                Hbyte Hidx Hnew' Hends' eq_refl Hwpre Hlow Hup)
      as [Hmeq Hweq].
    assert (Hbc : c = echo_line
                        !!! ((length (o_E so) `mod` length echo_line)%nat)).
    { rewrite (disc_seg_last_byte (open_seg h) c Hdseg Hends').
      by rewrite Hmeq Nat.sub_succ Nat.sub_0_r. }
    (* the two INDEX LAWS at the new entry, which the receipt carries on *)
    assert (Hidx2 : E_index (o_E so ++ [(open_seg h, c)])).
    { intros jj y Hy.
      destruct (decide (jj < length (o_E so))%nat) as [Hj | Hj].
      { rewrite lookup_app_l in Hy; [| lia]. by apply Hidx. }
      rewrite lookup_app_r in Hy; [| lia].
      assert (Hjj : jj = length (o_E so)).
      { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
      subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
      injection Hy as <-. cbn [fst snd]. split; [exact Hends' | lia]. }
    assert (Hbyte2 : E_byte (o_E so ++ [(open_seg h, c)])).
    { intros jj y Hy.
      destruct (decide (jj < length (o_E so))%nat) as [Hj | Hj].
      { rewrite lookup_app_l in Hy; [| lia]. by apply Hbyte. }
      rewrite lookup_app_r in Hy; [| lia].
      assert (Hjj : jj = length (o_E so)).
      { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
      subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
      injection Hy as <-. cbn [snd]. exact Hbc. }
    (* the CHOICE BOUND the append will hand on, off the new stage's
       [cs_len_ok] *)
    pose proof (cs_len_ok_echo so (open_seg h, c) Hcsb Hweq Hcsl) as Hcsl2.
    assert (Hbnd2 : (S (length (o_E so)) `div` length echo_line
                     <= S (length (o_cs so)))%nat).
    { pose proof echo_line_length as HLL.
      destruct (cs_len_ok_inv (MkO (o_ps so) (o_cs so) (o_E so ++ [(open_seg h, c)]) [])
                  Hcsl2) as [[_ Hq] | [_ Hq]];
        cbn [o_ps o_cs o_E o_w] in Hq; rewrite length_app in Hq;
        cbn [length] in Hq;
        replace (length (o_E so) + 1)%nat with (S (length (o_E so))) in Hq
          by lia; lia. }
    (* the ghost moves *)
    iMod (Elist_auth_grow v (o_E so) (open_seg h, c) with "HE")
      as "[HE #HElb2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iMod (wcnt_update3 v (1/4) (1/4) (1/2) (length (o_E so)) n2 nw
            (S (length (o_E so)))
            ltac:(by rewrite Qp.quarter_quarter Qp.half_half)
            with "Hwo Hwi Hww") as "(Hwo & Hwi & Hww)".
    iDestruct (wcnt_split v (1/4) (1/4) (S (length (o_E so)))
                 with "[Hww]") as "[Hwa Hwp]".
    { rewrite Qp.quarter_quarter. iExact "Hww". }
    iDestruct (wcnt_join v (1/4) (1/4) (S (length (o_E so)))
                 with "Hwi Hwa") as "Hwarm".
    iEval (rewrite Qp.quarter_quarter) in "Hwarm".
    iModIntro.
    iSplitL "Hta Hcs Hps HE Hwo".
    { rewrite /eout. iRight.
      iExists v, (MkO (o_ps so) (o_cs so) (o_E so ++ [(open_seg h, c)]) []).
      cbn [o_ps o_cs o_E o_w]. rewrite length_app. cbn [length].
      replace (length (o_E so) + 1)%nat with (S (length (o_E so))) by lia.
      rewrite (pcount_echo (o_ps so) (o_cs so) (o_E so) (open_seg h, c) (o_w so) Hweq).
      iFrame "Hpin Hta Hcs Hps HE Hwo". iPureIntro. split_and!.
      - rewrite /eout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        + rewrite Hacc Hweq (D_app (o_ps so) (o_cs so) (o_E so) (open_seg h, c)).
          cbn [snd]. by rewrite app_nil_r app_assoc.
        + apply prefix_nil.
        + exact Hidx2.
        + exact Hbyte2.
        + exact Hpsb.
        + (* the echo closes the block, so the round it read is now BELOW
             the stage -- and [sess_n_prefix_det] has just settled it *)
          intros q Hq. rewrite length_app in Hq. cbn [length] in Hq.
          destruct (decide (length echo_line * q < length (o_E so))%nat)
            as [Hltq | Hgeq]; [by apply Hpin |].
          pose proof echo_line_length as HLL.
          assert (Heq17 : (length echo_line * q = length (o_E so))%nat) by lia.
          assert (Hqe : (length (o_E so) `div` length echo_line)%nat = q).
          { rewrite -Heq17 Nat.mul_comm. apply Nat.div_mul. lia. }
          rewrite -Hqe. destruct Hokso as [_ Hokso].
          rewrite Hmeq Nat.sub_succ Nat.sub_0_r in Hokso. exact Hokso.
        + exact Hcsb'.
        + rewrite Forall_app. split; [exact Hdsc |].
          rewrite Forall_singleton. cbn. exact Hdseg.
        + rewrite Forall_app. split; [exact Hprefixes |].
          rewrite Forall_singleton. cbn [fst]. reflexivity.
        + rewrite length_app. cbn [length]. lia.
        + by right.
      - exact Hcsl2.
      - exact (ps_len_ok_echo so (open_seg h, c) Hpsl).
      - exact Hcsb. }
    iSplitL "Hwarm Hdli".
    { rewrite /ein. iRight. iRight.
      iExists v, (S (length (o_E so))), cs0, ps0i.
      iFrame "Hpin Hwarm Hdli HElbi Hcslbi Hpslbi". iPureIntro. split.
      - lia.
      - rewrite /ein_pure. by split_and!. }
    rewrite /ein_pend. iRight.
    iExists v, (S (length (o_E so))), (o_E so), (o_cs so), (o_ps so).
    iFrame "Hpin Hwp HElb2 Hcslb Hpslb". iPureIntro. split_and!.
    - lia.
    - exact Hidx2.
    - exact Hbyte2.
    - exact Hbnd2.
  Qed.

  (* ...and the LOG's side, fired after the chain ([WpUart.in_append]).  It
     takes the window the echo opened and the port's own claim, files the
     entry, returns the claim SETTLED and gives the kernel its token back
     (which is [in_append]'s post once lane CONS-IO F lands).

     IT IS TOTAL OVER THE THREE ARMS.  The WINDOW arm is the one its own echo
     left: the arm's half and the receipt's quarter agree, so the arm's log
     is one shorter than the receipt's bound and the two bounds -- prefixes
     of one monotone list -- say the arm owes exactly [(open_seg h, c)].  The
     SETTLED arm is REFUTED: the two bounds then have the SAME length, so the
     entry would already be in [pops], and [in_append]'s own order premise
     plus the era stamps put every logged history's segment STRICTLY below
     [open_seg h] ([open_seg_hist_ext]).  The TAINT arm pays outright, token
     included. *)
  Lemma ein_step_append (k : nat) (h hi : list mobs) (c : bv 8)
      (pops : list log_entry) (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    ein_pend k h c -∗ ein k hi pops dl ==∗
      ein k h (pops ++ [(h, c, [echo_of c])]) dl ∗ ewin k.
  Proof.
    intros Hdisc Hsh Hk Hends Hord. subst k. iIntros "Hpend Hin".
    iDestruct "Hpend" as "[#HT | Hpd]".
    { iModIntro. iSplitL "Hin";
        [by iApply ein_of_taint | by iApply ewin_of_taint]. }
    iDestruct "Hpd" as (v n El cs0 ps0)
      "(#Hpin & Hwq & #HElbp & #Hcslbp & #Hpslbp & %Hlen & %Hidxp & %Hbytep
        & %Hbndp)".
    iDestruct "Hin" as "[#HT | [Hs | Hwn]]".
    { iModIntro. iSplitL "Hwq";
        [by iApply ein_of_taint | by iApply ewin_of_taint]. }
    - (* THE SETTLED ARM IS REFUTED: the entry would already be logged, and
         [in_append]'s own order premise puts every logged history's segment
         STRICTLY below this one *)
      iDestruct "Hs" as (v2 n2 cs2 ps2)
        "(#Hpin2 & Hw2 & Hdl2 & %Hn2 & #HElb2 & #Hcslb2 & #Hpslb2 & %Hp2)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (wcnt_agree with "Hwq Hw2") as %Hnn.
      destruct Hp2 as (Hlog & Hdsc & Hstamp & Hdlp & Hidx2 & Hbyte2 & Hbnd2).
      iDestruct (Elist_lb_cmp with "HElb2 HElbp") as %Hcmp.
      iExFalso.
      assert (Hlens : length (seg_of (echoed pops))
                      = length (El ++ [(open_seg h, c)])).
      { rewrite seg_of_length length_app. cbn [length]. lia. }
      assert (Hseg : seg_of (echoed pops) = El ++ [(open_seg h, c)]).
      { destruct Hcmp as [Hc | Hc]; [apply prefix_length_eq; [exact Hc | lia]
                                    | symmetry; apply prefix_length_eq;
                                      [exact Hc | lia]]. }
      assert (Hlk : seg_of (echoed pops) !! (length El)
                    = Some (open_seg h, c)).
      { rewrite Hseg lookup_app_r; [| lia].
        by rewrite Nat.sub_diag. }
      rewrite /seg_of list_lookup_fmap in Hlk.
      destruct (echoed pops !! length El) as [y |] eqn:Hy; [| discriminate].
      destruct y as [yh yb]. cbn in Hlk. injection Hlk as Hlk1 Hlk2.
      assert (Hyin : (yh, yb) ∈ echoed pops)
        by (by eapply elem_of_list_lookup_2).
      destruct (echoed_elem_inv pops (yh, yb) Hyin) as (e & He & _ & Hye).
      assert (Hoseg : open_seg (le_hist e) = open_seg h).
      { injection Hye as Hye1 Hye2. by rewrite Hye1. }
      destruct (open_seg_hist_ext (le_hist e) h (Hord e He)
                  (Hstamp e He) Hsh) as [_ Hlt2].
      rewrite Hoseg in Hlt2. iPureIntro. lia.
    - (* THE WINDOW ARM is the one this receipt's own echo left: the arm's
         half and the receipt's quarter AGREE *)
      iDestruct "Hwn" as (v2 n2 cs2 ps2)
        "(#Hpin2 & Hw2 & Hdl2 & %Hn2 & #HElb2 & #Hcslb2 & #Hpslb2 & %Hp2)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (wcnt_agree with "Hwq Hw2") as %Hnn.
      destruct Hp2 as (Hlog & Hdsc & Hstamp & Hdlp & Hidx2 & Hbyte2 & Hbnd2).
      iDestruct (Elist_lb_cmp with "HElb2 HElbp") as %Hcmp.
      assert (Hlens : length (seg_of (echoed pops)) = length El).
      { rewrite seg_of_length. lia. }
      assert (Hseg : seg_of (echoed pops) = El).
      { destruct Hcmp as [Hc | Hc].
        - destruct Hc as [z Hz]. symmetry.
          destruct (app_inj_1 El (seg_of (echoed pops))
                      [(open_seg h, c)] z ltac:(lia) Hz) as [Heq _].
          exact Heq.
        - exfalso. apply prefix_length in Hc.
          rewrite length_app in Hc. cbn [length] in Hc. lia. }
      (* the new log slice, and the entry it files *)
      assert (Hech : echoed (pops ++ [(h, c, [echo_of c])])
                     = echoed pops ++ [(h, c)]).
      { rewrite (echoed_snoc_yes pops (h, c, [echo_of c])
                   (log_echoed_echo h c)).
        by rewrite /le_hist /le_byte /=. }
      assert (Hsegn : seg_of (echoed (pops ++ [(h, c, [echo_of c])]))
                      = El ++ [(open_seg h, c)]).
      { by rewrite Hech seg_of_app Hseg. }
      assert (Hlenn : length (echoed (pops ++ [(h, c, [echo_of c])])) = n).
      { rewrite Hech length_app. cbn [length].
        rewrite -seg_of_length Hseg. lia. }
      (* the fractions: the arm's half plus the receipt's quarter, split
         back into the settled arm's quarter and the kernel's token *)
      iDestruct (wcnt_join v (1/4) (1/2) n with "Hwq [Hw2]") as "Hw".
      { rewrite Hnn. iExact "Hw2". }
      iDestruct (wcnt_split v (1/4) (1/2) n with "Hw") as "[Hwi Hwt]".
      iModIntro. iSplitL "Hwi Hdl2".
      + rewrite /ein. iRight. iLeft. iExists v, n, cs0, ps0.
        rewrite Hsegn. iFrame "Hpin Hwi Hdl2 HElbp Hcslbp Hpslbp". iPureIntro.
        split; [exact Hlenn |]. rewrite /ein_pure Hech. split_and!.
        * apply cl_log_ok_snoc; [exact Hlog | exact Hends | | ].
          { rewrite /le_byte /le_echo /=. by right; left. }
          { intros e' He'. by apply Hord. }
        * intros e He. apply elem_of_app in He as [He | He];
            [by apply Hdsc |].
          apply elem_of_list_singleton in He as ->.
          rewrite /le_hist /=. exact (disc_seg_open_seg h Hsh Hdisc).
        * intros e He. apply elem_of_app in He as [He | He];
            [by apply Hstamp |].
          apply elem_of_list_singleton in He as ->. by rewrite /le_hist /=.
        * destruct Hdlp as [z ->]. eexists. by rewrite -app_assoc.
        * rewrite -Hech Hsegn. exact Hidxp.
        * rewrite -Hech Hsegn. exact Hbytep.
        * rewrite -Hech Hlenn. exact Hbndp.
      + rewrite /ewin. iRight. iExists v, n. iFrame "Hpin Hwt".
  Qed.

  (* ...and the DROP arm ([cs = []], and the run that stops before echoing):
     no window was opened, the token was never split, and [echoed pops] does
     not move -- so BOTH arms of the claim stand exactly where they were and
     the caller hands the kernel back the very token it was lent. *)
  Lemma ein_step_append_drop (k : nat) (h : list mobs) (c : bv 8)
      (hi : list mobs) (pops : list log_entry)
      (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    ein k hi pops dl -∗ ein k h (pops ++ [(h, c, [])]) dl.
  Proof.
    intros Hdisc Hsh Hk Hends Hord. subst k. iIntros "Hin".
    assert (Hech : echoed (pops ++ [(h, c, [])]) = echoed pops)
      by (apply echoed_snoc_no, log_echoed_nil_no).
    assert (Hpure' : forall cs0, ein_pure (obs_boots h) pops dl cs0 ->
              ein_pure (obs_boots h) (pops ++ [(h, c, [])]) dl cs0).
    { intros cs0 (Hlog & Hdsc & Hstamp & Hdlp & Hidx & Hbyte & Hbnd).
      rewrite /ein_pure Hech. split_and!.
      - apply cl_log_ok_snoc; [exact Hlog | exact Hends | | ].
        + rewrite /le_byte /le_echo /=. by left.
        + intros e' He'. by apply Hord.
      - intros e He. apply elem_of_app in He as [He | He]; [by apply Hdsc |].
        apply elem_of_list_singleton in He as ->.
        rewrite /le_hist /=. exact (disc_seg_open_seg h Hsh Hdisc).
      - intros e He. apply elem_of_app in He as [He | He];
          [by apply Hstamp |].
        apply elem_of_list_singleton in He as ->. by rewrite /le_hist /=.
      - exact Hdlp.
      - exact Hidx.
      - exact Hbyte.
      - exact Hbnd. }
    iDestruct "Hin" as "[#HT | [Hs | Hwn]]".
    - by iApply ein_of_taint.
    - iDestruct "Hs" as (v n cs0 ps0)
        "(#Hpin & Hw & Hdl & %Hn & #HElb & #Hcslb & #Hpslb & %Hp)".
      rewrite /ein. iRight. iLeft. iExists v, n, cs0, ps0.
      rewrite Hech. iFrame "Hpin Hw Hdl HElb Hcslb Hpslb". iPureIntro.
      split; [exact Hn | by apply Hpure'].
    - iDestruct "Hwn" as (v n cs0 ps0)
        "(#Hpin & Hw & Hdl & %Hn & #HElb & #Hcslb & #Hpslb & %Hp)".
      rewrite /ein. iRight. iRight. iExists v, n, cs0, ps0.
      rewrite Hech. iFrame "Hpin Hw Hdl HElb Hcslb Hpslb". iPureIntro.
      split; [exact Hn | by apply Hpure'].
  Qed.

  (* (W) THE WRITE, INSIDE A BLOCK.  What the writer brings: the era's pin,
     its cursor, a PERSISTENT lower bound of the line choices and one of the
     era's STAGE INDEX (review S9), and the Coq-level fact that its byte is
     the [P]-th of the era's process stream up to stage [S n0].  What it gets
     back: the cursor advanced and the two bounds, so the next write is paid
     the same way.

     THE ERA'S FIRST BYTE GOES THROUGH THIS LEMMA TOO, at [P = 0] with
     [n0 = 0] and [cs0 = []]: the claim's own [turn_auth] agrees with the
     writer's cursor, [pcount_zero] gives [o_E so = [] /\ o_w so = []], and
     the transcript is then [D ps cs [] ++ [] = []].  So [acc = []] is DERIVED
     from the writer's credential and nothing has to refute a claim at
     [acc <> []]: there is no separate adoption step and no seed. *)
  Lemma eout_step_write (k : nat) (v : era_pins) (P n0 : nat) (b : bv 8)
      (ps0 cs0 : list nat) (ho : list mobs) (acc : list (bv 8)) :
    ((n0 `div` length echo_line) <= length cs0)%nat ->
    pro_pin ps0 cs0 n0 ->
    proc_upto ps0 cs0 (S n0) !! P = Some b ->
    era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
    eout k ho acc ==∗
      eout k ho (acc ++ [b])
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T).
  Proof.
    intros Hdiv Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #HElb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro.
      iSplitR; [by iApply eout_of_taint | by iRight]. }
    iDestruct "Hp" as (v2 so) "(#Hpin2 & Hta & Hcs & Hps & HE & Hwo & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hcsb).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (E_lb_le with "HE HElb") as %Hn0.
    destruct (write_stage_byte ps0 (o_ps so) cs0 (o_cs so) (o_E so) (o_w so)
                n0 P b Hpsp Hpin0 Hcsp Hdiv Hn0 HP Hb) as [HlenE Hnext].
    (* the choice list stays put: at a block's first byte the claim's list
       is one short of what [Hdiv] asks for *)
    assert (Hcase : o_w so <> []
                    \/ (length (o_E so) `mod` length echo_line)%nat <> 0%nat
                    \/ length (o_E so) = 0%nat).
    { destruct (decide (o_w so = [])) as [Hw | Hw]; [| by left].
      destruct (decide ((length (o_E so) `mod` length echo_line)%nat = 0%nat))
        as [Hm | Hm]; [| by right; left].
      right; right.
      destruct (cs_len_ok_inv so Hcsl) as [[_ Hq] | [Hne _]]; last first.
      { exfalso. by apply Hne. }
      destruct (decide (length (o_E so) = 0%nat)) as [Hz | Hz]; [exact Hz |].
      exfalso.
      pose proof (prefix_length _ _ Hcsp) as Hlen0.
      pose proof echo_line_length as HLL.
      assert (Hdm : length (o_E so)
                    = (length echo_line
                       * (length (o_E so) `div` length echo_line))%nat).
      { pose proof (Nat.div_mod_eq (length (o_E so)) (length echo_line)) as Hx.
        lia. }
      assert (Hq1 : (1 <= length (o_E so) `div` length echo_line)%nat).
      { destruct ((length (o_E so) `div` length echo_line)%nat) as [| q'];
          [lia | lia]. }
      rewrite -HlenE in Hdiv. lia. }
    iMod (turn_update v P (pcount (o_ps so) (o_cs so) (o_E so) (o_w so)) (S P)
            with "Ht Hta") as "[Ht Hta]".
    iModIntro. iSplitR "Ht".
    - rewrite /eout. iRight.
      iExists v, (MkO (o_ps so) (o_cs so) (o_E so) (o_w so ++ [b])).
      cbn [o_ps o_cs o_E o_w]. rewrite pcount_write -HP.
      iFrame "Hpin Hta Hcs Hps HE Hwo". iPureIntro. split_and!.
      + rewrite /eout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        * by rewrite Hacc app_assoc.
        * by apply prefix_snoc_lookup.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpin.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
      + exact (cs_len_ok_write so b Hcsl Hcase).
      + exact (ps_len_ok_write so b Hpsl).
      + exact Hcsb.
    - iLeft. iFrame "Ht Hpslb Hcslb HElb".
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE (REVISION 7(d)).  The choice of
     continuation is the PROGRAM's knowledge -- sh knows whether it is about
     to print "hello world" or the exec failure -- and it is readable off the
     wire because the four alternatives begin with four distinct bytes
     ([EchoOutPure.line_alts_head_det]).  So the writer supplies the
     alternative's INDEX beside its first byte, and the step files it: the
     claim's list grows from [q-1] to [q] at stage [17 q], and every later
     byte of the block goes through [eout_step_write] against the lower bound
     this returns.  The PROLOGUE (block 0) is not a choice and grows nothing
     -- which is why [0 < n0] is a premise here. *)
  Lemma eout_step_write_blk (k : nat) (v : era_pins) (P n0 a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (ho : list mobs) (acc : list (bv 8)) :
    (0 < n0)%nat ->
    (n0 `mod` length echo_line)%nat = 0%nat ->
    ((n0 `div` length echo_line) <= S (length cs0))%nat ->
    pro_pin ps0 cs0 n0 ->
    P = length (proc_upto ps0 cs0 n0) ->
    (a < length line_alts)%nat ->
    line_alts !!! a !! 0%nat = Some b ->
    era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
    eout k ho acc ==∗
      eout k ho (acc ++ [b])
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ E_lb v n0) ∨ T).
  Proof.
    intros Hpos Hmod Hdiv Hpin0 HPeq Halt Hhead.
    pose proof echo_line_length as HLL.
    assert (Hd1 : ((n0 - 1) `div` length echo_line
                   = n0 `div` length echo_line - 1)%nat).
    { assert (Hn1 : n0 = ((n0 - 1) + 1)%nat) by lia.
      rewrite {2}Hn1. apply div_succ_of_mod0. rewrite -Hn1. exact Hmod. }
    iIntros "#Hpin Ht #Hpslb #Hcslb #HElb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro.
      iSplitR; [by iApply eout_of_taint | by iRight]. }
    iDestruct "Hp" as (v2 so) "(#Hpin2 & Hta & Hcs & Hps & HE & Hwo & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hcsb).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (E_lb_le with "HE HElb") as %Hn0.
    (* the stream up to stage [n0] is the same under the writer's bounds *)
    assert (Hstream : proc_upto ps0 cs0 n0 = proc_upto (o_ps so) (o_cs so) n0).
    { apply (proc_upto_cs_prefix_pred ps0 (o_ps so) cs0 (o_cs so) n0
               Hpsp Hcsp Hpin0). lia. }
    (* the era's stage is exactly [n0]: a further echo would have folded this
       block's WHOLE alternative into the stream, past the cursor *)
    assert (HlenE : length (o_E so) = n0).
    { destruct (decide (length (o_E so) = n0)) as [? | Hne]; [done | exfalso].
      assert (HSn : (S n0 <= length (o_E so))%nat) by lia.
      pose proof (proc_upto_mono (o_ps so) (o_cs so) (S n0) (length (o_E so)) HSn)
        as Hpre.
      apply prefix_length in Hpre.
      rewrite (proc_upto_length (o_ps so) (o_cs so) (o_E so)) in Hpre.
      rewrite (proc_upto_snoc (o_ps so) (o_cs so) n0) length_app -Hstream in Hpre.
      assert (Hne0 : pending_n (o_ps so) (o_cs so) n0 <> []).
      { rewrite /pending_n. rewrite decide_False; [| lia].
        rewrite decide_True; [| exact Hmod]. rewrite /alt_cont. intros Hc.
        apply app_eq_nil in Hc as [Hc _].
        exact (line_alts_nonnil _ (cs_ok_of_Forall _ Hcsb _) Hc). }
      assert (Hlen1 : (1 <= length (pending_n (o_ps so) (o_cs so) n0))%nat).
      { destruct (pending_n (o_ps so) (o_cs so) n0); [done | cbn; lia]. }
      rewrite /pcount in HP. lia. }
    (* ...and the writer stands at the block's first byte *)
    assert (Hwnil : o_w so = []).
    { assert (Hz : length (o_w so) = 0%nat).
      { rewrite /pcount in HP.
        rewrite -(proc_upto_length (o_ps so) (o_cs so) (o_E so)) in HP.
        rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    (* the claim's list is one short, so the writer's bound IS the list *)
    destruct (cs_len_ok_inv so Hcsl) as [[_ Hq] | [Hne _]]; last first.
    { exfalso. apply Hne. split; [exact Hwnil | by rewrite HlenE]. }
    rewrite HlenE in Hq.
    assert (Hcs0 : cs0 = o_cs so).
    { pose proof (prefix_length _ _ Hcsp) as Hle.
      destruct Hcsp as [z Hz]. rewrite Hz.
      assert (Hzn : z = []).
      { apply nil_length_inv. rewrite Hz length_app in Hle |- *.
        rewrite Hz length_app in Hq. lia. }
      by rewrite Hzn app_nil_r. }
    (* the byte the stage owes at the block's first position *)
    assert (Hidx0 : (o_cs so ++ [a]) !!! (n0 `div` length echo_line - 1)%nat
                    = a).
    { rewrite list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hq Nat.sub_diag. reflexivity. }
    assert (Hpend : pending (o_ps so) (o_cs so ++ [a]) (o_E so) !! 0%nat
                    = Some b).
    { rewrite /pending /pending_n HlenE. rewrite decide_False; [| lia].
      rewrite decide_True; [| exact Hmod]. rewrite /alt_cont Hidx0.
      rewrite lookup_app_l; [exact Hhead |].
      destruct (line_alts !!! a) as [| z zs] eqn:Hz;
        [ exfalso; exact (line_alts_nonnil a Halt Hz) | cbn; lia ]. }
    (* THE NEW CHOICE IS NOT READ BELOW STAGE [n0]: neither by the
       transcript nor by the cursor, and the PROLOGUE rounds do not move
       either ([pro_idx_app_le] at the blocks the stage has passed). *)
    assert (Hpinq : pro_pin (o_ps so) (o_cs so ++ [a]) (length (o_E so))).
    { intros qq Hqq. rewrite pro_idx_app_le; [by apply Hpin |].
      pose proof echo_line_length as HL.
      rewrite HlenE in Hqq. rewrite Hq.
      pose proof (Nat.div_mod_eq n0 (length echo_line)) as Hdm.
      rewrite Hmod Nat.add_0_r in Hdm. nia. }
    assert (HD : D (o_ps so) (o_cs so ++ [a]) (o_E so)
                 = D (o_ps so) (o_cs so) (o_E so)).
    { symmetry. apply (D_cs_prefix (o_ps so) (o_ps so) (o_cs so)
                         (o_cs so ++ [a]) (o_E so));
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE. lia. }
    assert (HPc : pcount_from (o_ps so) (o_cs so ++ [a]) 0%nat (o_E so)
                  = pcount_from (o_ps so) (o_cs so) 0%nat (o_E so)).
    { symmetry. apply (pcount_cs_prefix (o_ps so) (o_ps so) (o_cs so)
                         (o_cs so ++ [a]) (o_E so));
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE. lia. }
    assert (Hpc2 : pcount (o_ps so) (o_cs so ++ [a]) (o_E so) [b] = S P).
    { rewrite /pcount HPc. cbn [length]. rewrite /pcount Hwnil in HP.
      cbn [length] in HP. lia. }
    iMod (turn_update v P (pcount (o_ps so) (o_cs so) (o_E so) (o_w so)) (S P)
            with "Ht Hta") as "[Ht Hta]".
    iMod (cs_auth_grow v (o_cs so) a with "Hcs") as "[Hcs #Hcslb2]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb2]".
    iModIntro. iSplitR "Ht".
    - rewrite /eout. iRight.
      iExists v, (MkO (o_ps so) (o_cs so ++ [a]) (o_E so) [b]).
      cbn [o_ps o_cs o_E o_w]. rewrite Hpc2.
      iFrame "Hpin Hta Hcs Hps HE Hwo". iPureIntro. split_and!.
      + rewrite /eout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        * rewrite Hacc Hwnil app_nil_r HD. reflexivity.
        * apply (prefix_snoc_lookup [] _ b); [apply prefix_nil |].
          by rewrite -Hpend.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpinq.
        * rewrite Forall_app. split; [exact Hcsb' |].
          by rewrite Forall_singleton.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
      + apply (cs_len_ok_blk so a b); [by rewrite HlenE | lia | exact Hwnil
                                      | exact Hcsl].
      + apply (ps_len_ok_blk so a b);
          [by rewrite HlenE | lia | by rewrite HlenE | exact Hpsl].
      + rewrite Forall_app. split; [exact Hcsb |].
        by rewrite Forall_singleton.
    - iLeft. rewrite Hcs0. iFrame "Ht HElb Hcslb2 Hpslb".
  Qed.

  (* (W-pro) THE WRITE AT A PROLOGUE ROUND'S CHOICE BYTE -- byte 19 of the
     round, the one just past its banner.  Init has printed the banner and
     forked; the byte it puts out next is the first of "$ " (the child
     execs and sh prompts), of "init: exec sh failed\n" (the child could
     not exec, so the round runs again) or of "init: fork failed\n" (the
     round, and the wire, end there).  Which one is INIT'S OWN knowledge,
     and the step FILES it: the claim's resolution list grows by one and
     the bound that comes back has the entry in it -- the exact twin of
     what [eout_step_write_blk] does for a LINE alternative.

     THE ROUND-OPENING PREMISE IS NOT DECORATION.  A block whose line took
     an alternative other than 3 owes no prologue at all, and this link
     must not fire there; [n0 = 0] is the boot round and
     [cs0 !!! (n0/17 - 1) = 3] the round init opens after the shell's own
     fork panic.

     WHAT RECONCILES THE WRITER WITH THE CLAIM.  The writer knows only
     [~ pro_done] of ITS OWN [ps0]; the claim holds the authority, and a
     resolution whose round has ALREADY settled has a longer [pending_n]
     with the writer's [o_w] a proper prefix of it.  [ps_len_ok] is what
     rules that out: (B) says every entry the round has is already on the
     wire, so at the writer's cursor the two resolutions have the same
     prologue, hence ([EchoDisc.pro_of_prefix_free]) the claim's round is
     open too, and ([EchoDisc.pro_of_open_app_inj]) the two lists are
     EQUAL -- which is what makes [ps_lb v (ps0 ++ [a])] payable.

     AT [n0 = 0], [cs0 = []] THIS IS PHASE 1'S FORM exactly:
     [P = length (pro_of ps0)] and [~ pro_done ps0]. *)
  Lemma eout_step_write_pro (k : nat) (v : era_pins) (P n0 a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (ho : list mobs) (acc : list (bv 8)) :
    (n0 `mod` length echo_line)%nat = 0%nat ->
    (n0 = 0%nat \/ cs0 !!! (n0 `div` length echo_line - 1)%nat = 3%nat) ->
    ((n0 `div` length echo_line) <= length cs0)%nat ->
    pro_pin ps0 cs0 n0 ->
    ~ pro_done (pro_from (pro_idx cs0 (n0 `div` length echo_line)) ps0) ->
    P = length (proc_upto ps0 cs0 (S n0)) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
    eout k ho acc ==∗
      eout k ho (acc ++ [b])
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T).
  Proof.
    intros Hmod Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    pose proof echo_line_length as HLL.
    iIntros "#Hpin Ht #Hpslb #Hcslb #HElb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [by iApply eout_of_taint | by iRight]. }
    iDestruct "Hp" as (v2 so) "(#Hpin2 & Hta & Hcs & Hps & HE & Hwo & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hcsb).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (E_lb_le with "HE HElb") as %Hn0.
    (* ---- the writer's own list is bounded, and its round index is the
           claim's ---- *)
    assert (Hpsb0 : Forall (fun x => (x < length pro_alts)%nat) ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2. by apply Forall_app in Hpsb2 as [? _]. }
    assert (Hidxeq : pro_idx (o_cs so) (n0 `div` length echo_line)
                     = pro_idx cs0 (n0 `div` length echo_line)).
    { symmetry. apply (pro_idx_ext cs0 (o_cs so) (n0 `div` length echo_line));
        [| lia].
      intros j Hj. symmetry.
      apply (lookup_total_prefix cs0 (o_cs so) j Hcsp). lia. }
    rewrite -Hidxeq in Hnd.
    assert (HopenC : n0 = 0%nat
                     \/ o_cs so !!! (n0 `div` length echo_line - 1)%nat = 3%nat).
    { destruct (decide (n0 = 0%nat)) as [Hz | Hne]; [by left | right].
      assert (Hd1 : (1 <= n0 `div` length echo_line)%nat).
      { destruct (decide (n0 `div` length echo_line = 0)%nat) as [Hd | Hd];
          [| lia].
        exfalso. pose proof (Nat.div_mod_eq n0 (length echo_line)) as Hdm.
        rewrite Hd Hmod in Hdm. lia. }
      destruct Hopen as [Hz | H3]; [by destruct (Hne Hz) |].
      rewrite (lookup_total_prefix cs0 (o_cs so) _ Hcsp); [exact H3 | lia]. }
    (* ---- the stream and the block below the writer's cursor ---- *)
    assert (Hstream : proc_upto ps0 cs0 n0 = proc_upto (o_ps so) (o_cs so) n0).
    { apply (proc_upto_cs_prefix_pred ps0 (o_ps so) cs0 (o_cs so) n0
               Hpsp Hcsp Hpin0).
      assert (Hle3 : ((n0 - 1) `div` length echo_line
                      <= n0 `div` length echo_line)%nat)
        by (apply Nat.Div0.div_le_mono; lia).
      lia. }
    assert (Hpend0 : pending_n ps0 cs0 n0 = pending_n ps0 (o_cs so) n0)
      by (apply (pending_n_cs_ext ps0 cs0 (o_cs so) n0 Hcsp Hdiv)).
    assert (Hpmono : pending_n ps0 (o_cs so) n0
                     `prefix_of` pending_n (o_ps so) (o_cs so) n0)
      by (by apply pending_n_ps_mono).
    assert (HPval : P = (length (proc_upto ps0 cs0 n0)
                         + length (pending_n ps0 cs0 n0))%nat).
    { rewrite HPeq proc_upto_snoc.
      by rewrite (length_app (proc_upto ps0 cs0 n0) (pending_n ps0 cs0 n0)). }
    rewrite /pcount in HP.
    rewrite -(proc_upto_length (o_ps so) (o_cs so) (o_E so)) in HP.
    (* ---- the era's stage IS [n0]: a further echo would have folded this
           block into the stream, and the round it read would be SETTLED,
           which the writer's own [~ pro_done] refutes ---- *)
    assert (HlenE : length (o_E so) = n0).
    { destruct (decide (length (o_E so) = n0)) as [? | Hne]; [done | exfalso].
      assert (HSn : (S n0 <= length (o_E so))%nat) by lia.
      pose proof (proc_upto_mono (o_ps so) (o_cs so) (S n0) (length (o_E so)) HSn)
        as Hpre.
      apply prefix_length in Hpre.
      rewrite (proc_upto_snoc (o_ps so) (o_cs so) n0)
              (length_app (proc_upto (o_ps so) (o_cs so) n0)
                 (pending_n (o_ps so) (o_cs so) n0)) -Hstream in Hpre.
      pose proof (prefix_length _ _ Hpmono) as Hlp. rewrite -Hpend0 in Hlp.
      assert (Hpe : pending_n ps0 (o_cs so) n0
                    = pending_n (o_ps so) (o_cs so) n0).
      { apply prefix_length_eq; [exact Hpmono | rewrite -Hpend0; lia]. }
      pose proof (pending_n_round_det ps0 (o_ps so) (o_cs so) n0 Hmod HopenC Hpe)
        as Hpro.
      assert (Hdone : pro_done (pro_from
                        (pro_idx (o_cs so) (n0 `div` length echo_line))
                        (o_ps so))).
      { apply pro_from_done.
        apply (pro_pin_at (o_ps so) (o_cs so) (length (o_E so)) n0 Hpin). lia. }
      apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (pro_idx (o_cs so) (n0 `div` length echo_line)) ps0)
                  (pro_from (pro_idx (o_cs so) (n0 `div` length echo_line))
                     (o_ps so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hpro; reflexivity)) as [Hd _].
      exact Hd. }
    (* ---- so the writer stands at the END of the block's OPEN prologue ---- *)
    assert (Hlenw : length (o_w so) = length (pending_n ps0 cs0 n0)).
    { rewrite HlenE -Hstream in HP. lia. }
    assert (Hweq : o_w so = pending_n ps0 (o_cs so) n0).
    { assert (Hw1 : o_w so `prefix_of` pending_n (o_ps so) (o_cs so) n0)
        by (rewrite -HlenE; exact Hwpre).
      assert (Hlen2 : length (o_w so) = length (pending_n ps0 (o_cs so) n0))
        by (rewrite -Hpend0; exact Hlenw).
      destruct (prefix_weak_total (o_w so) (pending_n ps0 (o_cs so) n0)
                  (pending_n (o_ps so) (o_cs so) n0) Hw1 Hpmono) as [H | H].
      - apply prefix_length_eq; [exact H | lia].
      - symmetry. apply prefix_length_eq; [exact H | lia]. }
    assert (Hopens : ps_opens so).
    { rewrite /ps_opens HlenE.
      destruct HopenC as [Hz | H3]; [by left | by right]. }
    (* ---- the CLAIM'S round is the writer's, still open, and its
           resolution is the writer's list ---- *)
    pose proof Hpsl as [HpsA HpsB].
    assert (Hproeq : pro_of (pro_from
                       (pro_idx (o_cs so) (n0 `div` length echo_line)) ps0)
                     = pro_of (pro_from
                         (pro_idx (o_cs so) (n0 `div` length echo_line))
                         (o_ps so))).
    { destruct (decide (pro_of (pro_from
                          (pro_idx (o_cs so) (n0 `div` length echo_line)) ps0)
                        = pro_of (pro_from
                            (pro_idx (o_cs so) (n0 `div` length echo_line))
                            (o_ps so)))) as [Heq | Hne]; [exact Heq | exfalso].
      pose proof (HpsB Hopens ps0 Hpsp) as Hlt.
      rewrite /ps_round HlenE in Hlt.
      pose proof (Hlt Hne) as Hlt2. rewrite Hpend0 in Hlenw. lia. }
    assert (Hndps : ~ pro_done (pro_from
                      (pro_idx (o_cs so) (n0 `div` length echo_line))
                      (o_ps so))).
    { intros Hdone. apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (pro_idx (o_cs so) (n0 `div` length echo_line)) ps0)
                  (pro_from (pro_idx (o_cs so) (n0 `div` length echo_line))
                     (o_ps so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hproeq; reflexivity)) as [Hd _].
      exact Hd. }
    assert (Hround0 : (pro_idx (o_cs so) (n0 `div` length echo_line)
                       <= pro_rounds ps0)%nat).
    { rewrite Hidxeq. by apply (pro_pin_round_le ps0 cs0 n0 Hmod Hopen Hpin0). }
    assert (Hpseq : o_ps so = ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2.
      assert (Hzb : Forall (fun x => (x < length pro_alts)%nat) z)
        by (by apply Forall_app in Hpsb2 as [_ ?]).
      pose proof Hproeq as Hpe2. rewrite Hz in Hpe2.
      rewrite (pro_from_app_le _ ps0 z Hround0) in Hpe2.
      assert (Hzn : z = []).
      { apply (pro_of_open_app_inj _ z Hnd Hzb). by rewrite -Hpe2. }
      rewrite Hz Hzn. by rewrite app_nil_r. }
    assert (HRle : (pro_idx (o_cs so) (n0 `div` length echo_line)
                    <= pro_rounds (o_ps so))%nat) by (rewrite Hpseq; exact Hround0).
    (* ---- the byte the block owes at the writer's position ---- *)
    assert (Hshape2 : pending_n (o_ps so ++ [a]) (o_cs so) n0
                      = (if decide (n0 = 0%nat) then [] else line_alts !!! 3%nat)
                        ++ pro_of (pro_from (pro_idx (o_cs so)
                             (n0 `div` length echo_line)) (o_ps so ++ [a])))
      by (apply pending_n_round_pre; [exact Hmod | exact HopenC]).
    assert (Hshape : pending_n (o_ps so) (o_cs so) n0
                     = (if decide (n0 = 0%nat) then [] else line_alts !!! 3%nat)
                       ++ pro_of (pro_from (pro_idx (o_cs so)
                            (n0 `div` length echo_line)) (o_ps so)))
      by (apply pending_n_round_pre; [exact Hmod | exact HopenC]).
    assert (Hpendb : pending_n (o_ps so ++ [a]) (o_cs so) n0 !! length (o_w so)
                     = Some b).
    { pose proof (pro_of_snoc_head
                    (pro_from (pro_idx (o_cs so)
                       (n0 `div` length echo_line)) (o_ps so)) a b Hndps Hhead)
        as Hph.
      assert (Hpre3' :
        ((if decide (n0 = 0%nat) then [] else line_alts !!! 3%nat)
         ++ (pro_of (pro_from (pro_idx (o_cs so)
                       (n0 `div` length echo_line)) (o_ps so)) ++ [b]))
        `prefix_of` pending_n (o_ps so ++ [a]) (o_cs so) n0).
      { rewrite Hshape2 (pro_from_snoc_le _ (o_ps so) a HRle).
        by apply prefix_app. }
      assert (Hwl : length (o_w so)
                    = (length (if decide (n0 = 0%nat)
                               then [] else line_alts !!! 3%nat)
                       + length (pro_of (pro_from (pro_idx (o_cs so)
                           (n0 `div` length echo_line)) (o_ps so))))%nat).
      { rewrite Hweq -Hpseq Hshape.
        by rewrite (length_app
                      (if decide (n0 = 0%nat) then [] else line_alts !!! 3%nat)
                      (pro_of (pro_from (pro_idx (o_cs so)
                         (n0 `div` length echo_line)) (o_ps so)))). }
      rewrite Hwl. eapply prefix_lookup_Some; [| exact Hpre3'].
      rewrite (lookup_app_shift
                 (if decide (n0 = 0%nat) then [] else line_alts !!! 3%nat)).
      replace (length (pro_of (pro_from (pro_idx (o_cs so)
                 (n0 `div` length echo_line)) (o_ps so))))
        with (length (pro_of (pro_from (pro_idx (o_cs so)
                 (n0 `div` length echo_line)) (o_ps so))) + 0)%nat by lia.
      by rewrite (lookup_app_shift
                    (pro_of (pro_from (pro_idx (o_cs so)
                       (n0 `div` length echo_line)) (o_ps so)))). }
    (* ---- and the block is not empty, so the choice list stays put ---- *)
    assert (Hwnil : o_w so <> []).
    { rewrite Hweq -Hpseq.
      pose proof (pending_nonnil (o_ps so) (o_cs so) (o_E so) Hcsb
                    ltac:(rewrite HlenE; exact Hmod)) as Hne.
      rewrite /pending HlenE in Hne. exact Hne. }
    (* ---- the transcript and the cursor do not read the new entry ---- *)
    assert (HD : D (o_ps so ++ [a]) (o_cs so) (o_E so)
                 = D (o_ps so) (o_cs so) (o_E so)).
    { symmetry. apply (D_ps_ext (o_ps so) (o_ps so ++ [a]) (o_cs so) (o_E so));
        [by eexists | exact Hpin]. }
    assert (HPc : pcount_from (o_ps so ++ [a]) (o_cs so) 0%nat (o_E so)
                  = pcount_from (o_ps so) (o_cs so) 0%nat (o_E so)).
    { symmetry.
      apply (pcount_cs_prefix (o_ps so) (o_ps so ++ [a]) (o_cs so) (o_cs so)
               (o_E so)); [by eexists | reflexivity | exact Hpin |].
      rewrite HlenE.
      assert (Hle2 : (length cs0 <= length (o_cs so))%nat)
        by (by apply prefix_length).
      assert (Hle3 : ((n0 - 1) `div` length echo_line
                      <= n0 `div` length echo_line)%nat)
        by (apply Nat.Div0.div_le_mono; lia).
      lia. }
    assert (Hpc2 : pcount (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so ++ [b])
                   = S P).
    { rewrite /pcount HPc (length_app (o_w so) [b]). cbn [length].
      rewrite -(proc_upto_length (o_ps so) (o_cs so) (o_E so)). lia. }
    iMod (turn_update v P (pcount (o_ps so) (o_cs so) (o_E so) (o_w so)) (S P)
            with "Ht Hta") as "[Ht Hta]".
    iMod (ps_auth_grow v (o_ps so) a with "Hps") as "[Hps #Hpslb2]".
    iModIntro. iSplitR "Ht".
    - rewrite /eout. iRight.
      iExists v, (MkO (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so ++ [b])).
      cbn [o_ps o_cs o_E o_w]. rewrite Hpc2.
      iFrame "Hpin Hta Hcs Hps HE Hwo". iPureIntro. split_and!.
      + rewrite /eout_pure. cbn [o_ps o_cs o_E o_w]. split_and!.
        * rewrite Hacc HD. by rewrite app_assoc.
        * apply prefix_snoc_lookup.
          { etrans; [exact Hwpre |]. rewrite /pending.
            by apply pending_n_ps_mono; eexists. }
          { rewrite /pending HlenE. exact Hpendb. }
        * exact Hidx.
        * exact Hbyte.
        * rewrite Forall_app. split; [exact Hpsb | by rewrite Forall_singleton].
        * apply (pro_pin_mono (o_ps so) (o_ps so ++ [a])); [by eexists | exact Hpin].
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
      + apply (cs_len_ok_write
                 (MkO (o_ps so ++ [a]) (o_cs so) (o_E so) (o_w so)) b);
          [exact Hcsl | by left].
      + apply (ps_len_ok_pro so a b);
          [ rewrite /ps_round HlenE; exact HRle
          | rewrite /ps_round HlenE; exact Hndps
          | rewrite /pending HlenE Hweq; by rewrite -Hpseq
          | exact (conj HpsA HpsB) ].
      + exact Hcsb.
    - iLeft. rewrite -Hpseq. iFrame "Ht Hpslb2 Hcslb HElb".
  Qed.

  (* (R) THE READ.  [ws] is the window the read CONSUMED; [read_ok] is what
     [WpUart.read_link] hands over.  What it gives back: the pure prefix fact
     SH-LINE turns into the line, THE TWO INDEX LAWS for the log's echoed
     slice (which is what [ein_read_line] needs and no reader could otherwise
     supply), and -- for a reader that will go on to write, which is sh --
     the era's pin and the two bounds (review S9), the stage one at the
     window's far end, which at a line boundary is the [17 q] the writer
     needs, and the CHOICE bound the block-first write asks for.

     NOTHING MOVES: the claim is rebuilt in the arm it arrived in (the window
     arm's counter and the settled arm's alike), so this is an entailment and
     not an update. *)
  (* the read's whole pure account, shared by the two non-taint arms: they
     carry the SAME [ein_pure], so the read never has to know which one it
     met. *)
  Lemma ein_read_pure (k : nat) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (cs0 : list nat) :
    read_ok pops dl ws -> ein_pure k pops dl cs0 ->
    (dl ++ ws) `prefix_of` echoed pops
    /\ ein_pure k pops (dl ++ ws) cs0
    /\ ((length (dl ++ ws)) `div` length echo_line <= S (length cs0))%nat.
  Proof.
    intros Hread (Hlog & Hdisc & Hstamp & Hdlp & Hidx & Hbyte & Hbnd).
    assert (Hnoer : forall e, e ∈ pops -> cons_erase (le_byte e) = false).
    { intros e He. eapply disc_seg_no_erase; [by apply Hdisc |].
      apply open_seg_ends_in. by apply (proj1 (proj1 Hlog e He)). }
    assert (Hpref : (dl ++ ws) `prefix_of` echoed pops)
      by (eapply read_window_prefix;
          [exact Hlog | exact Hread | exact Hnoer | exact Hdlp]).
    split; [exact Hpref |]. split.
    - rewrite /ein_pure. split_and!;
        [exact Hlog | exact Hdisc | exact Hstamp | exact Hpref | exact Hidx
         | exact Hbyte | exact Hbnd].
    - etrans; [| exact Hbnd]. apply Nat.Div0.div_le_mono.
      by apply prefix_length.
  Qed.

  Lemma ein_step_read (k : nat) (v : era_pins) (n : nat) (hi : list mobs)
      (pops : list log_entry) (dl ws : list (list mobs * bv 8)) :
    read_ok pops dl ws ->
    era_pin k v -∗ dl_cnt v (1/2) n -∗ ein k hi pops dl ==∗
      ein k hi pops (dl ++ ws)
      ∗ ((T ∗ dl_cnt v (1/2) n)
         ∨ dl_cnt v (1/2) (n + length ws)%nat
           ∗ ⌜length dl = n⌝
           ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
           ∗ ⌜E_index (seg_of (echoed pops))⌝
           ∗ ⌜E_byte (seg_of (echoed pops))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ cs0 ps0 : list nat,
                  cs_lb v cs0 ∗ ps_lb v ps0 ∗ E_lb v (n + length ws)%nat
                  ∗ ⌜((n + length ws) `div` length echo_line
                      <= S (length cs0))%nat⌝)).
  Proof.
    intros Hread. iIntros "#Hpinr Hdlr Hcl".
    iDestruct "Hcl" as "[#HT | [Hs | Hwn]]".
    - iModIntro. iSplitR; [by iApply ein_of_taint |]. iLeft. by iFrame "Hdlr".
    - iDestruct "Hs" as (v2 n2 cs0 ps0)
        "(#Hpin & Hw & Hdl & %Hn & #HElb & #Hcslb & #Hpslb & %Hp)".
      iDestruct (era_pin_agree with "Hpin Hpinr") as %->.
      iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
      pose proof Hp as Hp2.
      destruct Hp2 as (_ & _ & _ & _ & Hidx & Hbyte & _).
      destruct (ein_read_pure k pops dl ws cs0 Hread Hp)
        as (Hpref & Hp' & Hbnd').
      iMod (dl_cnt_update v (length dl) n (n + length ws)%nat
              with "Hdl Hdlr") as "[Hdl Hdlr]".
      iModIntro. iSplitL "Hw Hdl".
      { rewrite /ein. iRight. iLeft. iExists v, n2, cs0, ps0.
        rewrite length_app Hdleq. iFrame "Hpin Hw Hdl HElb Hcslb Hpslb".
        iPureIntro. by split. }
      iRight. iFrame "Hdlr".
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iRight. iExists cs0, ps0. iFrame "Hcslb Hpslb". iSplitR "".
      + iApply (E_lb_of_lb v (seg_of (echoed pops)) (n + length ws)%nat);
          [rewrite seg_of_length; pose proof (prefix_length _ _ Hpref) as HL;
           rewrite length_app in HL; lia | iExact "HElb"].
      + iPureIntro. rewrite -Hdleq -length_app. exact Hbnd'.
    - iDestruct "Hwn" as (v2 n2 cs0 ps0)
        "(#Hpin & Hw & Hdl & %Hn & #HElb & #Hcslb & #Hpslb & %Hp)".
      iDestruct (era_pin_agree with "Hpin Hpinr") as %->.
      iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
      pose proof Hp as Hp2.
      destruct Hp2 as (_ & _ & _ & _ & Hidx & Hbyte & _).
      destruct (ein_read_pure k pops dl ws cs0 Hread Hp)
        as (Hpref & Hp' & Hbnd').
      iMod (dl_cnt_update v (length dl) n (n + length ws)%nat
              with "Hdl Hdlr") as "[Hdl Hdlr]".
      iModIntro. iSplitL "Hw Hdl".
      { rewrite /ein. iRight. iRight. iExists v, n2, cs0, ps0.
        rewrite length_app Hdleq. iFrame "Hpin Hw Hdl HElb Hcslb Hpslb".
        iPureIntro. by split. }
      iRight. iFrame "Hdlr".
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
      iRight. iExists cs0, ps0. iFrame "Hcslb Hpslb". iSplitR "".
      + iApply (E_lb_of_lb v (seg_of (echoed pops)) (n + length ws)%nat);
          [rewrite seg_of_length; pose proof (prefix_length _ _ Hpref) as HL;
           rewrite length_app in HL; lia | iExact "HElb"].
      + iPureIntro. rewrite -Hdleq -length_app. exact Hbnd'.
  Qed.

  (* ...and the LINE, which is what SH-LINE reads off it.  Its [E_byte]
     premise is now an EXPORT of the read ([read_ret]), which is what the
     landed shape (stated over the input stage's own [i_E]) could not be. *)
  Lemma ein_read_line (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (q : nat) :
    E_byte (seg_of (echoed pops)) ->
    (dl ++ ws) `prefix_of` echoed pops ->
    length dl = (length echo_line * q)%nat ->
    length ws = length echo_line ->
    snd <$> ws = echo_line.
  Proof.
    intros HE Hp Hdl Hws.
    rewrite -(seg_of_snd ws).
    apply (read_window_line (seg_of (echoed pops)) (seg_of dl) (seg_of ws) q).
    - exact HE.
    - rewrite -seg_of_app. destruct Hp as [z Hz]. rewrite Hz.
      exists (seg_of z). by rewrite seg_of_app.
    - by rewrite seg_of_length.
    - by rewrite seg_of_length.
  Qed.

  (* ...AND THE PER-BYTE FORM, which is what sh's [gets] reads: one byte at
     a time, placed by the reader's own delivered count.  [read_ret]'s
     [⌜length dl = n⌝] is what makes [n] usable here at all -- the link
     hides the invariant's [dl]. *)
  Lemma ein_read_byte (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (n : nat) (x : list mobs * bv 8) :
    E_byte (seg_of (echoed pops)) ->
    (dl ++ ws) `prefix_of` echoed pops ->
    length dl = n ->
    ws !! 0%nat = Some x ->
    x.2 = echo_line !!! (n `mod` length echo_line)%nat.
  Proof.
    intros HE Hp Hdl Hx.
    assert (Hlk : (dl ++ ws) !! n = Some x).
    { rewrite lookup_app_r; [| lia]. rewrite Hdl Nat.sub_diag. exact Hx. }
    assert (Hek : echoed pops !! n = Some x)
      by (by eapply prefix_lookup_Some).
    assert (Hsk : seg_of (echoed pops) !! n = Some (open_seg x.1, x.2))
      by (by rewrite /seg_of list_lookup_fmap Hek).
    pose proof (HE n _ Hsk) as Hb. cbn [snd] in Hb. exact Hb.
  Qed.

  (* (L) THE DRAIN ([App.Htx]).  The claim's own same-cycle facts are at its
     WITNESS [ho]; [App.Htx] supplies [ho `prefix_of` h] and the era stamp at
     [h], the claim carries the stamp at [ho], and
     [EchoOutPure.open_seg_prefix_boots] puts the two segments in one cycle.
     [EchoOutPure.good_out_of_stage] then turns the stage into [good_out]. *)
  Lemma eout_drain (k : nat) (h ho : list mobs)
      (acc : list (bv 8)) (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` acc ->
    eout k ho acc -∗ eout k ho acc ∗ (T ∨ ⌜good_out seg⌝).
  Proof.
    intros Hsh Hk Hpre Hins Hwire. subst k. rewrite /eout.
    iIntros "Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    - iSplitR; [iLeft; iExact "HT" | iLeft; iExact "HT"].
    - iDestruct "Hp" as (v so) "(#Hpin & Hta & Hcs & Hps & HE & Hwo & %Hall)".
      pose proof Hall as Hall2.
      destruct Hall2 as (Hpure & Hcsl & Hpsl & Hcsb).
      destruct Hpure as (Hacc & Hwp & Hidx & Hbyte & Hpsb & Hpin & Hcs' & Hdsc
                         & Hpre1 & Hpre2 & Hpre3).
      iSplitL "Hta Hcs Hps HE Hwo".
      { iRight. iExists v, so. iFrame "Hpin Hta Hcs Hps HE Hwo". by iPureIntro. }
      iRight. iPureIntro.
      assert (Hlen : (length (o_E so) <= length (ins seg))%nat).
      { rewrite Hins. destruct Hpre3 as [HEnil | Hbo].
        - rewrite HEnil. cbn [length]. lia.
        - etrans; [exact Hpre2 |]. apply prefix_length, ins_prefix_of.
          apply open_seg_prefix_boots;
            [exact Hpre | by rewrite Hbo | exact Hsh]. }
      apply (good_out_of_stage (o_ps so) (o_cs so) (o_E so) (o_w so) seg
               Hpsb Hcs' Hbyte Hpin Hwp).
      + rewrite -Hacc. exact Hwire.
      + exact Hlen.
  Qed.

  (* ==================================================================== *)
  (*  7.  THE LINKS: the claims wrapped onto the kernel's own console      *)
  (*      contracts                                                       *)
  (*                                                                      *)
  (*  A link runs at [⊤ ∖ ↑uartN Uart0] -- the store's device node opens   *)
  (*  the port invariant and the ghost step runs inside it.  IT OPENS      *)
  (*  NOTHING ELSE: every authority the era has is in the claim the link   *)
  (*  is handed, so no link reaches the application's ledger and           *)
  (*  [App.Happ_echo] stays a CLOSED entailment.                           *)
  (* ==================================================================== *)
  Section echo_links.
    Context `{HRg : !riscvGS Σ}.

    (* the two record equations, as section parameters: [App.Happ_echo] and
       [App.Hinit_boot] hand them over at the [boot_fixedGS] literal *)
    Context (Hout : @riscv_out_res Σ (@riscv_fixedGS Σ HRg) = eout).
    Context (Hin : @riscv_in_res Σ (@riscv_fixedGS Σ HRg) = ein).
    Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = etag).
    Context (Hwin : @riscv_win_res Σ (@riscv_fixedGS Σ HRg) = ewin).

    Lemma out_res_at0 (kk : nat) (hh : list mobs) (aa : list (bv 8)) :
      out_res_at Uart0 kk hh aa = eout kk hh aa.
    Proof. rewrite /out_res_at. by rewrite Hout. Qed.

    Lemma in_res_at0 (kk : nat) (hh : list mobs) (pp : list log_entry)
        (dd : list (list mobs * bv 8)) :
      in_res_at Uart0 kk hh pp dd = ein kk hh pp dd.
    Proof. rewrite /in_res_at. by rewrite Hin. Qed.

    (* (W) THE WRITE LINK, INSIDE A BLOCK.  What IO-LEAF spends per byte: the
       era's pin, its cursor and the two persistent bounds, plus the
       Coq-level fact that the byte is the [P]-th of the era's process stream
       up to stage [S n0].  What it gets back in [Φ] is the cursor advanced
       and the same two bounds -- or the taint, if the claim was already off
       the discipline when the byte went out.

       INIT'S FIRST BANNER BYTE IS THIS LINK at [P = 0], [n0 = 0],
       [cs0 = []]: [app_turn] ([eturn]) is exactly its argument list.

       THE WITNESS IS NOT MOVED: a process byte answers no input, so the
       claim stays at the history it was read at. *)
    Lemma echo_write_link (k : nat) (v : era_pins) (P n0 : nat) (b : bv 8)
        (ps0 cs0 : list nat) (Φ : iProp Σ) :
      ((n0 `div` length echo_line) <= length cs0)%nat ->
      pro_pin ps0 cs0 n0 ->
      proc_upto ps0 cs0 (S n0) !! P = Some b ->
      era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
      (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T) -∗ Φ) -∗
      out_link Uart0 k b Φ.
    Proof.
      intros Hdiv Hpin0 Hb.
      iIntros "#Hpin Ht #Hpslb #Hcslb #HElb HΦ" (o acc) "#Hlb Hres".
      rewrite !out_res_at0.
      iMod (eout_step_write k v P n0 b ps0 cs0 (default [] o) acc
              Hdiv Hpin0 Hb with "Hpin Ht Hpslb Hcslb HElb Hres")
        as "(Hres & Hret)".
      iModIntro. iExists o. rewrite out_res_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
    Qed.

    (* (W'') THE TAINT ROUTE.  Once the era is off the discipline every
       claim is free, so a link costs nothing: the program tower spends
       this when an earlier link of the same string handed back the taint
       instead of the cursor. *)
    Lemma echo_write_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
      T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ.
    Proof.
      iIntros "#HT HΦ" (o acc) "#Hlb Hres".
      rewrite !out_res_at0.
      iModIntro. iExists o. rewrite out_res_at0.
      iSplitR; [iExact "Hlb" |]. iSplitR; [by iApply eout_of_taint |].
      by iApply "HΦ".
    Qed.

    (* (W') THE WRITE LINK AT A BLOCK'S FIRST BYTE.  The alternative's INDEX
       is the program's own knowledge and the step files it, so the bound
       that comes back has grown by one. *)
    Lemma echo_write_link_blk (k : nat) (v : era_pins) (P n0 a : nat)
        (b : bv 8) (ps0 cs0 : list nat) (Φ : iProp Σ) :
      (0 < n0)%nat ->
      (n0 `mod` length echo_line)%nat = 0%nat ->
      ((n0 `div` length echo_line) <= S (length cs0))%nat ->
      pro_pin ps0 cs0 n0 ->
      P = length (proc_upto ps0 cs0 n0) ->
      (a < length line_alts)%nat ->
      line_alts !!! a !! 0%nat = Some b ->
      era_pin k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
      (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ E_lb v n0) ∨ T)
       -∗ Φ) -∗
      out_link Uart0 k b Φ.
    Proof.
      intros Hpos Hmod Hdiv Hpin0 HPeq Halt Hhead.
      iIntros "#Hpin Ht #Hpslb #Hcslb #HElb HΦ" (o acc) "#Hlb Hres".
      rewrite !out_res_at0.
      iMod (eout_step_write_blk k v P n0 a b ps0 cs0 (default [] o) acc
              Hpos Hmod Hdiv Hpin0 HPeq Halt Hhead
              with "Hpin Ht Hpslb Hcslb HElb Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite out_res_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
    Qed.

    (* (W-pro) THE WRITE LINK AT A PROLOGUE ROUND'S CHOICE BYTE.  Init's
       own knowledge of which of the three alternatives it is taking, filed
       into the claim; the bound that comes back has the entry in it, and
       the rest of the alternative goes out through [echo_write_link]
       against that bound.  At [n0 = 0], [cs0 = []] this is exactly the
       era's FIRST choice, at [P = length (pro_of ps0)]. *)
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
    Proof.
      intros Hmod Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
      iIntros "#Hpin Ht #Hpslb #Hcslb #HElb HΦ" (o acc) "#Hlb Hres".
      rewrite !out_res_at0.
      iMod (eout_step_write_pro k v P n0 a b ps0 cs0 (default [] o) acc
              Hmod Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
              with "Hpin Ht Hpslb Hcslb HElb Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite out_res_at0. iFrame "Hlb Hres".
      by iApply "HΦ".
    Qed.

    (* (R) THE READ LINK.  [ws] is the window the read CONSUMED and
       [ConsLog.read_ok] is the kernel's whole pure account of it.  What the
       reader gets back, at the log the invariant actually held: the PREFIX
       fact and the two INDEX LAWS SH-LINE turns into the line
       ([ein_read_line]), and -- for a non-empty window -- the era's pin with
       the two bounds a later WRITE spends, the stage one at the window's far
       end (which at a line boundary is the [17 q] the block-first write asks
       for) and the CHOICE bound beside it. *)
    Definition read_ret (k : nat) (v : era_pins) (n : nat)
        (ws : list (list mobs * bv 8)) : iProp Σ :=
      ((T ∗ dl_cnt v (1/2) n)
       ∨ dl_cnt v (1/2) (n + length ws)%nat
         ∗ ∃ (pops : list log_entry) (dl : list (list mobs * bv 8)),
             ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
             ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
             ∗ ⌜E_index (seg_of (echoed pops))⌝
             ∗ ⌜E_byte (seg_of (echoed pops))⌝
             ∗ (⌜ws = []⌝
                ∨ ∃ cs0 ps0 : list nat,
                    cs_lb v cs0 ∗ ps_lb v ps0 ∗ E_lb v (n + length ws)%nat
                    ∗ ⌜((n + length ws) `div` length echo_line
                        <= S (length cs0))%nat⌝))%I.

    Lemma echo_read_link (k : nat) (v : era_pins) (n : nat)
        (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
      era_pin k v -∗ dl_cnt v (1/2) n -∗ (read_ret k v n ws -∗ Φ) -∗
      read_link k ws Φ.
    Proof.
      iIntros "#Hpin Hdlr HΦ" (o pops dl) "#Hlb Hres %Hread".
      rewrite !in_res_at0.
      iMod (ein_step_read k v n (default [] o) pops dl ws Hread
              with "Hpin Hdlr Hres") as "(Hres & Hret)".
      iModIntro. iExists o. rewrite in_res_at0. iFrame "Hlb Hres".
      iApply "HΦ". rewrite /read_ret.
      iDestruct "Hret" as "[Ht | (Hdlr & %Hdl & %Hpref & %Hidx & %Hbyte
                                 & Hrest)]"; [by iLeft |].
      iRight. iFrame "Hdlr". iExists pops, dl. iFrame "Hrest".
      iPureIntro. by split_and!.
    Qed.

    (* THE KERNEL'S TOKEN IS THE APPLICATION'S, by [App.Happ_echo]'s fourth
       equation (lane CONS-IO milestone F).  [riscv_win_res (S gen_id)] on
       [SpecConsoleintr.cons_echo_shift]'s premise and [riscv_win_res k] in
       [WpUart.in_append]'s post are [ewin] -- the window counter's half,
       which the echo splits and the append gives back. *)
    Lemma win_res0 (kk : nat) : riscv_win_res kk = ewin kk.
    Proof. by rewrite Hwin. Qed.

    (* ================================================================== *)
    (*  THE ECHO SHIFT ITSELF -- [App.Happ_echo], a CLOSED entailment.     *)
    (*                                                                    *)
    (*  It is the totality table of part 4's report, run as a proof: the   *)
    (*  taint arms (the tag's, the token's, either claim's), the window    *)
    (*  arm's five quarters, the settled arm's tie at the echo and its     *)
    (*  refutation at the append, and the DROP arm at every early stop of  *)
    (*  the run.  Nothing here opens an invariant of the application's:    *)
    (*  every authority the era has arrives inside the claim the link      *)
    (*  hands over.                                                       *)
    (* ================================================================== *)

    (* ---- the licence route: once tainted, every link of the run is free,
            the kernel's token included ---- *)
    Lemma echo_link_of_taint (k : nat) (h : list mobs) (b : bv 8)
        (Φ : iProp Σ) :
      T -∗ Φ -∗ echo_link k h b Φ.
    Proof.
      iIntros "#HT HΦ" (o o' acc pops dl)
        "#Hlb Hres #Hlb' Hires %Hord %Hwire".
      iModIntro. iExists o. rewrite !out_res_at0 !in_res_at0.
      iSplitR "HΦ"; [iExact "Hlb" |].
      iSplitR "HΦ"; [by iApply eout_of_taint |].
      iSplitR "HΦ"; [iExact "Hlb'" |].
      iSplitR "HΦ"; [by iApply ein_of_taint | iExact "HΦ"].
    Qed.

    Lemma in_append_of_taint (k : nat) (h : list mobs) (c : bv 8)
        (cs : list (bv 8)) (Φ : iProp Σ) :
      T -∗ Φ -∗ in_append k h c cs Φ.
    Proof.
      iIntros "#HT HΦ" (o pops dl) "#Hlb Hres %Hord".
      iModIntro. iExists o. rewrite !in_res_at0 Hwin.
      iSplitR "HΦ"; [iExact "Hlb" |].
      iSplitR "HΦ"; [by iApply ein_of_taint |].
      iSplitR "HΦ"; [by iApply ewin_of_taint | iExact "HΦ"].
    Qed.

    Lemma in_run_of_taint (k : nat) (h : list mobs) (c : bv 8)
        (bs : list (bv 8)) :
      forall (pre : list (bv 8)) (Φ : iProp Σ),
        T -∗ Φ -∗ in_run k h c pre bs Φ.
    Proof.
      induction bs as [| b bs IH]; iIntros (pre Φ) "#HT HΦ".
      - by iApply in_append_of_taint.
      - cbn [in_run]. iSplit.
        + by iApply in_append_of_taint.
        + iApply (echo_link_of_taint with "HT [HΦ]").
          by iApply (IH (pre ++ [b]) Φ with "HT HΦ").
    Qed.

    (* ---- the disciplined route, one lemma per arm of [in_run] ---- *)

    (* THE APPEND AFTER AN EARLY STOP: the kernel took [in_run]'s left
       conjunct, so nothing was echoed and the entry is [(h, c, [])].  The
       token was never split and goes straight back. *)
    Lemma in_append_drop (k : nat) (h : list mobs) (c : bv 8)
        (Φ : iProp Σ) :
      disc h -> trace_shape h true -> obs_boots h = k ->
      obs_ends_in Uart0 h c ->
      obs_hist_lb h -∗ ewin k -∗ Φ -∗ in_append k h c [] Φ.
    Proof.
      intros Hdisc Hsh Hk Hends.
      iIntros "#Hlbh Hwin HΦ" (o pops dl) "#Hlb Hres %Hord".
      iEval (rewrite in_res_at0) in "Hres".
      iDestruct (ein_step_append_drop k h c (default [] o) pops dl
                   Hdisc Hsh Hk Hends Hord with "Hres") as "Hres".
      iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
      rewrite in_res_at0 Hwin.
      iSplitR "Hres Hwin HΦ"; [iExact "Hlbh" |].
      iSplitR "Hwin HΦ"; [iExact "Hres" |].
      iSplitL "Hwin"; [iExact "Hwin" | iExact "HΦ"].
    Qed.

    (* ...AND AFTER THE ECHO: the receipt names the entry, the claim's
       window arm owes exactly it, and the token comes back. *)
    Lemma in_append_echo (k : nat) (h : list mobs) (c : bv 8)
        (Φ : iProp Σ) :
      disc h -> trace_shape h true -> obs_boots h = k ->
      obs_ends_in Uart0 h c ->
      obs_hist_lb h -∗ ein_pend k h c -∗ Φ -∗
      in_append k h c [echo_of c] Φ.
    Proof.
      intros Hdisc Hsh Hk Hends.
      iIntros "#Hlbh Hpend HΦ" (o pops dl) "#Hlb Hres %Hord".
      iEval (rewrite in_res_at0) in "Hres".
      iMod (ein_step_append k h (default [] o) c pops dl
              Hdisc Hsh Hk Hends Hord with "Hpend Hres") as "[Hres Hwin]".
      iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
      rewrite in_res_at0 Hwin.
      iSplitR "Hres Hwin HΦ"; [iExact "Hlbh" |].
      iSplitR "Hwin HΦ"; [iExact "Hres" |].
      iSplitL "Hwin"; [iExact "Hwin" | iExact "HΦ"].
    Qed.

    (* THE ECHO'S OWN LINK.  The caller-owed premise [Hlt] is read off the
       input claim it is handed ([ein_lt]) -- a tainted claim owes nothing
       and pays through the taint arms instead. *)
    Lemma echo_link_echo (k : nat) (h : list mobs) (c : bv 8)
        (Φ : iProp Σ) :
      disc h -> trace_shape h true -> obs_boots h = k ->
      obs_ends_in Uart0 h c ->
      obs_hist_lb h -∗ ewin k -∗ (ein_pend k h c -∗ Φ) -∗
      echo_link k h (echo_of c) Φ.
    Proof.
      intros Hdisc Hsh Hk Hends.
      iIntros "#Hlbh Hwin HΦ" (o o' acc pops dl)
        "#Hlb Hres #Hlb' Hires %Hord %Hwire".
      iEval (rewrite out_res_at0) in "Hres".
      iEval (rewrite in_res_at0) in "Hires".
      iDestruct (ein_lt k h c (default [] o') pops dl Hsh Hk Hends Hord
                   with "Hires") as "[Hires Hlt]".
      iDestruct "Hlt" as "[#HT | %Hlt]".
      { iModIntro. iExists o. rewrite !out_res_at0 !in_res_at0.
        iSplitR "HΦ"; [iExact "Hlb" |].
        iSplitR "HΦ"; [by iApply eout_of_taint |].
        iSplitR "HΦ"; [iExact "Hlb'" |].
        iSplitR "HΦ"; [by iApply ein_of_taint |].
        iApply "HΦ". rewrite /ein_pend. by iLeft. }
      iMod (eout_step_echo k h c (default [] o) (default [] o') acc pops dl
              Hdisc Hsh Hk Hends Hwire Hord Hlt
              with "Hwin Hres Hires") as "(Hres & Hires & Hpend)".
      iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
      rewrite out_res_at0 in_res_at0.
      iSplitR "Hres Hires Hpend HΦ"; [iExact "Hlbh" |].
      iSplitR "Hires Hpend HΦ"; [iExact "Hres" |].
      iSplitR "Hires Hpend HΦ"; [iExact "Hlb'" |].
      iSplitR "Hpend HΦ"; [iExact "Hires" |].
      by iApply "HΦ".
    Qed.

    (* [App.Happ_echo], modulo lane CONS-IO F's two contracts. *)
    Lemma echo_happ_echo :
      ⊢ ∀ (GEN : GenId) (XI : CurCtx),
          @SpecConsoleintr.cons_echo_shift Σ HRg GEN XI.
    Proof.
      iIntros (GEN XI).
      rewrite /SpecConsoleintr.cons_echo_shift Htag Hwin.
      iIntros "!>" (h c cs Φ) "%Hends %Hk %Hcs #Htg #Hlbh Hwin HΦ".
      iDestruct "Htg" as "[%Hsh [%Hdisc | #HT]]"; last first.
      { (* THE TAINT ROUTE, at every arm and every length of the run *)
        by iApply (in_run_of_taint with "HT HΦ"). }
      destruct Hcs as [Hnil | [Hech | [Herase _]]].
      - (* A DROPPED BYTE is an accepted byte: the log records it at [cs = []] *)
        subst cs. cbn [in_run].
        by iApply (in_append_drop with "Hlbh Hwin HΦ").
      - (* THE ECHO: the byte first, the entry last, stoppable before either *)
        subst cs. cbn [in_run]. iSplit.
        + by iApply (in_append_drop with "Hlbh Hwin HΦ").
        + iApply (echo_link_echo (S gen_id) h c with "Hlbh Hwin [HΦ]");
            [exact Hdisc | exact Hsh | exact Hk | exact Hends |].
          iIntros "Hpend". cbn [in_run].
          by iApply (in_append_echo with "Hlbh Hpend HΦ").
      - (* THE ERASE ARMS cannot fire under the discipline *)
        exfalso.
        pose proof (disc_seg_no_erase (open_seg h) c
                      (disc_seg_open_seg h Hsh Hdisc)
                      (open_seg_ends_in h c Hends)) as Hno.
        rewrite Hno in Herase. discriminate.
    Qed.
  End echo_links.

End echo_out.
