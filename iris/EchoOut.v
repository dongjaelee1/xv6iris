(* EchoOut.v -- E5's APPLICATION CLAIM, THE IRIS HALF (lane ECHO-OUT).

   Design of record: claude-notes/projects/app-echo.md, "E5 -- THE CONSOLE
   I/O CLAIM: DESIGN OF RECORD", read with the coordinator's LEDGER-ANCHORED
   ruling, its ERA-NUMBER index convergence and the review's S1/S2/S3/S4/S9
   (2026-09-13), and the owner's correction to [echo_phi].

   WHY THE STATE IS IN THE LEDGER AND NOT IN THE CLAIMS.  [App.Happ_boot] --
   [SystemAdequacy.app_xfer_boot_raw] -- is fired ONCE PER POWER-ON, its only
   input is the durable claim (which the same shift DUPLICATES), and it is a
   plain [==∗], so no invariant may be opened inside it and no auth is
   reachable there.  Therefore [app_out c k [] []] and [app_in c k [] [] []]
   have to be re-mintable at EVERY era out of nothing: NO EXCLUSIVE GHOST AT
   THE FIXED PART MAY APPEAR IN EITHER CLAIM, and pairing by an existential
   name in the claim against a half in [app_boot] would never agree.  So the
   claims are pure-plus-a-fragment and the pairing is done LAZILY BY THE
   LEDGER at the era's first link.  The ledger is [AppEcho.echo_R], the
   application's own resource inside the observation invariant; it persists
   across power cycles and already sees every power event.

   THE INDEX IS THE ERA NUMBER [k := S gen_id] (ambient [RiscvLang.GenId]),
   not a ghost name: [riscv_out_res k ho acc], [riscv_in_res k ho pops dl],
   every link at [k], [app_out/app_in/app_boot A c k], the founding [∀ k]
   (lane CONS-IO).  The kernel STAMPS every history it hands the application
   with [⌜obs_boots h = S gen_id⌝] -- on [Hpow]'s power-on arm, on
   [Htx]/[Hrx], in the receive column's per-byte entry and as a premise of
   [cons_echo_shift].  Consequences, all of them simplifications: the pin map
   is keyed by [k]; adoption is INSERT-IF-ABSENT (no freshness token is
   needed, and a second first-link of the same era finds the pin present and
   uses it); a link at [k] knows [k = obs_boots h] purely, so no history is
   ever compared against the ledger's inside a link -- which is essential,
   because the observation AUTHORITY lives in the state interpretation and
   not in the observation invariant.

   THE SHAPE.  Each port claim is one of
     - the TAINT (what the licences pay through), or
     - FRESH: nothing has happened in this era yet (the arm the transport
       founds, from nothing; an input before the banner is undisciplined, so
       the fresh arm can only be left through the taint or through a write),
     - PAIRED: the era's persistent pin, one half of that era's OWN stage
       ghost, and either the era's pure fact or [era_closed k].
   [era_closed] is kept for the one case the lemmas admit but the proof tree
   never produces: a link at [k] applied to a claim of a dead era.

   TWO STAGES, NOT ONE (review S1).  A write moves [o_w] with only the output
   claim in hand and [WpUart.in_append] moves [pops] with only the input
   claim in hand, so one shared ghost value could not stay in step -- and
   putting one ghost's half in BOTH claims plus the ledger is three halves of
   one [ghost_var], which is unsatisfiable and makes every lemma about the
   paired state vacuous.  So: [gso] carries [(cs, E, w)], half in [eout] and
   half in the ledger; [gsi] carries [(E, owed)], half in [ein] and half in
   the ledger; each ghost has EXACTLY TWO halves, and [era_alloc] below is
   the anti-vacuity witness that the paired state is inhabited.  The echo --
   the only step that moves [E] -- holds both claims, because
   [WpUart.echo_link] passes the input claim through.

   THE CURSOR IS MONOTONE (review S2).  It counts the PROCESS bytes written
   in this era ([pcount]), not the position inside the current continuation:
   the echo sets [o_w := []] with the writer absent, so a cursor the shift
   had to reset could never be moved.  [pcount] is unchanged by the echo
   (which fires only at [w = pending cs E], exactly the bytes the echo folds
   into [D]) and incremented by one at a write, so the shift never touches
   it.

   WHAT THE LINKS HAND THE PROGRAM (review S9).  A writer must prove
   [pending cs E !! length w = Some b] without holding any stage half.  It
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
  o_cs : list nat;
  o_E  : list (list mobs * bv 8);
  o_w  : list (bv 8);
}.

(* [i_owed] is the CHAIN-FIRST window (RULINGS AFTER CONS-IO PHASE 1, (1)):
   between the echo's [out_link]s and the [in_append] that files the entry,
   [i_E] is ONE ENTRY AHEAD of [echoed pops]. *)
Record istage := MkI {
  i_E    : list (list mobs * bv 8);
  i_owed : bool;
}.

Definition ostage0 : ostage := MkO [] [] [].
Definition istage0 : istage := MkI [] false.

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
  acc = D (o_cs so) (o_E so) ++ o_w so
  /\ o_w so `prefix_of` pending (o_cs so) (o_E so)
  /\ E_index (o_E so)
  /\ E_byte (o_E so)
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
Lemma pending_nonnil (cs : list nat) (E : list (list mobs * bv 8)) :
  Forall (fun i => (i < length line_alts)%nat) cs ->
  (length E `mod` length echo_line = 0)%nat ->
  pending cs E <> [].
Proof.
  intros HF Hm. rewrite /pending /pending_n.
  case_decide as H0.
  - pose proof u_prologue_pos. intros Hc. rewrite Hc in H. cbn in H. lia.
  - rewrite decide_True; [| exact Hm].
    apply line_alts_nonnil, (cs_ok_of_Forall _ HF).
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

Lemma cs_len_ok_intro (cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) :
  ((w = [] /\ (length E `mod` length echo_line)%nat = 0%nat) ->
     length cs = (length E `div` length echo_line - 1)%nat) ->
  (~ (w = [] /\ (length E `mod` length echo_line)%nat = 0%nat) ->
     length cs = (length E `div` length echo_line)%nat) ->
  cs_len_ok (MkO cs E w).
Proof.
  rewrite /cs_len_ok. cbn [o_cs o_E o_w]. intros H1 H2. case_decide as Hb.
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
  o_w so = pending (o_cs so) (o_E so) ->
  cs_len_ok so ->
  cs_len_ok (MkO (o_cs so) (o_E so ++ [x]) []).
Proof.
  intros HF Hw Hc.
  assert (Hq : length (o_cs so)
               = (length (o_E so) `div` length echo_line)%nat).
  { destruct (cs_len_ok_inv so Hc) as [[[Hw' Hm] _] | [_ Hq]]; [| exact Hq].
    exfalso. apply (pending_nonnil (o_cs so) (o_E so) HF Hm).
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
  cs_len_ok (MkO (o_cs so) (o_E so) (o_w so ++ [b])).
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
  cs_len_ok (MkO (o_cs so ++ [a]) (o_E so) [b]).
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

(* how many PROCESS bytes the transcript [D cs E ++ w] contains: one
   [pending_n] block per echoed input, plus what is written of the current
   block.  A [Fixpoint] from the left with the stage index as accumulator,
   for [D_from]'s reason exactly. *)
Fixpoint pcount_from (cs : list nat) (k : nat)
    (E : list (list mobs * bv 8)) : nat :=
  match E with
  | [] => 0%nat
  | _ :: E' => (length (pending_n cs k) + pcount_from cs (S k) E')%nat
  end.

Definition pcount (cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) : nat := (pcount_from cs 0 E + length w)%nat.

Lemma pcount_from_app cs k E1 E2 :
  pcount_from cs k (E1 ++ E2)
  = (pcount_from cs k E1 + pcount_from cs (k + length E1) E2)%nat.
Proof.
  revert k. induction E1 as [| x E1 IH]; intros k; cbn.
  - by rewrite Nat.add_0_r.
  - rewrite IH.
    replace (S k + length E1)%nat with (k + S (length E1))%nat by lia. lia.
Qed.

(* A WRITE MOVES IT BY ONE *)
Lemma pcount_write cs E w b : pcount cs E (w ++ [b]) = S (pcount cs E w).
Proof. rewrite /pcount length_app /=. lia. Qed.

(* ...AND THE ECHO LEAVES IT ALONE, which is the whole point: the block the
   echo folds into [D] is exactly the [w] that was already counted. *)
Lemma pcount_echo cs E x w :
  w = pending cs E -> pcount cs (E ++ [x]) [] = pcount cs E w.
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
Fixpoint proc_upto_from (cs : list nat) (k n : nat) : list (bv 8) :=
  match n with
  | 0%nat => []
  | S n' => pending_n cs k ++ proc_upto_from cs (S k) n'
  end.

Definition proc_upto (cs : list nat) (n : nat) : list (bv 8) :=
  proc_upto_from cs 0 n.

(* THE ALIGNMENT: the cursor counts exactly the bytes of this stream. *)
Lemma proc_upto_from_length cs k E :
  length (proc_upto_from cs k (length E)) = pcount_from cs k E.
Proof.
  revert k. induction E as [| x E IH]; intros k; cbn; [done |].
  by rewrite length_app IH.
Qed.

Lemma proc_upto_length cs E :
  length (proc_upto cs (length E)) = pcount_from cs 0 E.
Proof. apply proc_upto_from_length. Qed.

Lemma proc_upto_from_S cs k n :
  proc_upto_from cs k (S n) = pending_n cs k ++ proc_upto_from cs (S k) n.
Proof. reflexivity. Qed.

Lemma proc_upto_from_snoc cs k n :
  proc_upto_from cs k (S n) = proc_upto_from cs k n ++ pending_n cs (k + n).
Proof.
  revert k. induction n as [| n IH]; intros k.
  - cbn [proc_upto_from]. by rewrite app_nil_r Nat.add_0_r.
  - rewrite (proc_upto_from_S cs k (S n)) (IH (S k))
            (proc_upto_from_S cs k n) app_assoc.
    f_equal. f_equal. lia.
Qed.

Lemma proc_upto_snoc cs n :
  proc_upto cs (S n) = proc_upto cs n ++ pending_n cs n.
Proof.
  assert (H0 : (0 + n)%nat = n) by lia.
  rewrite /proc_upto (proc_upto_from_snoc cs 0 n). by rewrite ?H0.
Qed.

Lemma proc_upto_mono cs n m :
  (n <= m)%nat -> proc_upto cs n `prefix_of` proc_upto cs m.
Proof.
  intros Hnm. induction Hnm as [| m Hnm IH]; [reflexivity |].
  etrans; [exact IH |]. rewrite proc_upto_snoc. by eexists.
Qed.

(* THE CURSOR IS AN INDEX INTO IT.  Forward: what the stage owes at [length w]
   is what the stream has at [pcount]. *)
Lemma proc_upto_pcount cs E w b :
  pending cs E !! length w = Some b ->
  proc_upto cs (S (length E)) !! pcount cs E w = Some b.
Proof.
  intros Hb. rewrite proc_upto_snoc /pcount -proc_upto_length.
  rewrite lookup_app_r; [| lia].
  replace (length (proc_upto cs (length E)) + length w
           - length (proc_upto cs (length E)))%nat with (length w) by lia.
  exact Hb.
Qed.

(* ...and back, which is the direction a WRITER needs.  THE STRICTNESS
   PREMISE IS NOT DECORATION: at [length w = length (pending cs E)] the cursor
   indexes the FIRST byte of the NEXT block, which the stream has and the
   stage does not owe -- writing it would be writing past the continuation,
   before the echo that closes the line.  The program supplies it; see
   [eout_step_write]. *)
Lemma proc_upto_pcount_inv cs E w N b :
  (S (length E) <= N)%nat ->
  (length w < length (pending cs E))%nat ->
  proc_upto cs N !! pcount cs E w = Some b ->
  pending cs E !! length w = Some b.
Proof.
  intros HN Hlt Hl.
  destruct (lookup_lt_is_Some_2 (pending cs E) (length w) Hlt) as [b' Hb'].
  pose proof (proc_upto_pcount cs E w b' Hb') as Hfwd.
  assert (Heq : proc_upto cs N !! pcount cs E w = Some b')
    by (eapply prefix_lookup_Some;
        [exact Hfwd | apply (proc_upto_mono cs _ N HN)]).
  assert (Hbb : b = b') by congruence. by rewrite Hbb.
Qed.

(* THE CHOICES ARE READ ONLY BELOW THE LAST COMPLETED LINE, so a lower bound
   of [cs] fixes the stream (review S9). *)
Lemma pending_n_cs_prefix cs0 cs k :
  cs0 `prefix_of` cs ->
  ((k `div` length echo_line) <= length cs0)%nat ->
  pending_n cs0 k = pending_n cs k.
Proof.
  intros [z ->] Hk. rewrite /pending_n.
  case_decide as H0; [done |].
  case_decide as Hm; [| done].
  pose proof echo_line_length as HL.
  assert (Hq : (1 <= k `div` length echo_line)%nat).
  { destruct (decide (k `div` length echo_line = 0)%nat) as [Hd | Hd]; [| lia].
    exfalso. pose proof (Nat.div_mod_eq k (length echo_line)) as Hdm.
    rewrite Hd Hm in Hdm. lia. }
  f_equal.
  rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Lemma proc_upto_from_ext cs0 cs k n :
  (forall j, (k <= j)%nat -> (j < k + n)%nat -> pending_n cs0 j = pending_n cs j) ->
  proc_upto_from cs0 k n = proc_upto_from cs k n.
Proof.
  revert k. induction n as [| n IH]; intros k Hj; [done |].
  cbn [proc_upto_from]. rewrite (Hj k ltac:(lia) ltac:(lia)). f_equal.
  apply IH. intros j H1 H2. apply Hj; lia.
Qed.

(* the form the write lemma spends: a writer's lower bound of the choices
   determines the stream as far as it can index into it *)
Lemma proc_upto_cs_prefix cs0 cs n :
  cs0 `prefix_of` cs ->
  (n <= length echo_line * length cs0)%nat ->
  proc_upto cs0 n = proc_upto cs n.
Proof.
  intros Hp Hn. rewrite /proc_upto. apply proc_upto_from_ext.
  intros j _ Hj. apply (pending_n_cs_prefix cs0 cs j Hp).
  pose proof echo_line_length as HL.
  apply Nat.div_le_upper_bound; lia.
Qed.

Lemma proc_upto_cs_mono cs0 cs n p b :
  cs0 `prefix_of` cs ->
  (n <= length echo_line * length cs0)%nat ->
  proc_upto cs0 n !! p = Some b -> proc_upto cs n !! p = Some b.
Proof. intros Hp Hn Hl. by rewrite -(proc_upto_cs_prefix cs0 cs n Hp Hn). Qed.

(* THE TIGHT FORM, which is the one a writer can pay.  [proc_upto_cs_prefix]
   asks for [n <= 17 * length cs0], and at the era's FIRST block ([n = 1],
   [cs0 = []]) that is false while the conclusion is not: [pending_n cs 0] is
   [u_prologue] and reads no choice at all.  What the stream up to stage
   [S n0] actually reads is [j `div` 17] for [j <= n0]. *)
Lemma proc_upto_cs_prefix_S cs0 cs n0 :
  cs0 `prefix_of` cs ->
  ((n0 `div` length echo_line) <= length cs0)%nat ->
  proc_upto cs0 (S n0) = proc_upto cs (S n0).
Proof.
  intros Hp Hn. rewrite /proc_upto. apply proc_upto_from_ext.
  intros j _ Hj. apply (pending_n_cs_prefix cs0 cs j Hp).
  etrans; [| exact Hn]. apply Nat.Div0.div_le_mono. lia.
Qed.

(* THE BLOCK-BOUNDARY FORM (REVISION 7(d)).  At the first byte of block [q]'s
   continuation the ledger's choice list is one SHORT -- that write is what
   extends it -- so [proc_upto_cs_prefix_S] cannot be used there.  What the
   stream up to stage [n] reads is [j `div` 17] for [j < n], i.e. at most
   [(n-1) `div` 17]. *)
Lemma proc_upto_cs_prefix_pred cs0 cs n :
  cs0 `prefix_of` cs ->
  (((n - 1) `div` length echo_line) <= length cs0)%nat ->
  proc_upto cs0 n = proc_upto cs n.
Proof.
  intros Hp Hn. rewrite /proc_upto. apply proc_upto_from_ext.
  intros j _ Hj. apply (pending_n_cs_prefix cs0 cs j Hp).
  etrans; [| exact Hn]. apply Nat.Div0.div_le_mono. lia.
Qed.

(* the same extension law for the TRANSCRIPT and the CURSOR: both read
   [pending_n cs j] for [j < length E] only, so a lower bound of [cs] that
   reaches the last COMPLETED line determines them.  This is what makes the
   block-boundary write sound: appending the new line's alternative to [cs]
   moves [pending cs E] and nothing else. *)
Lemma D_from_ext cs0 cs k E :
  (forall j, (k <= j)%nat -> (j < k + length E)%nat ->
     pending_n cs0 j = pending_n cs j) ->
  D_from cs0 k E = D_from cs k E.
Proof.
  revert k. induction E as [| x E IH]; intros k Hj; [done |].
  assert (Hrec : D_from cs0 (S k) E = D_from cs (S k) E).
  { apply IH. intros j H1 H2. apply Hj; cbn [length]; lia. }
  cbn [D_from length]. rewrite (Hj k ltac:(lia) ltac:(cbn [length]; lia)).
  by rewrite Hrec.
Qed.

Lemma pcount_from_ext cs0 cs k E :
  (forall j, (k <= j)%nat -> (j < k + length E)%nat ->
     pending_n cs0 j = pending_n cs j) ->
  pcount_from cs0 k E = pcount_from cs k E.
Proof.
  revert k. induction E as [| x E IH]; intros k Hj; [done |].
  assert (Hrec : pcount_from cs0 (S k) E = pcount_from cs (S k) E).
  { apply IH. intros j H1 H2. apply Hj; cbn [length]; lia. }
  cbn [pcount_from length].
  rewrite (Hj k ltac:(lia) ltac:(cbn [length]; lia)). by rewrite Hrec.
Qed.

Lemma cs_ext_pred cs0 cs n :
  cs0 `prefix_of` cs ->
  (((n - 1) `div` length echo_line) <= length cs0)%nat ->
  forall j, (0 <= j)%nat -> (j < 0 + n)%nat ->
    pending_n cs0 j = pending_n cs j.
Proof.
  intros Hp Hn j _ Hj. apply (pending_n_cs_prefix cs0 cs j Hp).
  etrans; [| exact Hn]. apply Nat.Div0.div_le_mono. lia.
Qed.

Lemma D_cs_prefix cs0 cs E :
  cs0 `prefix_of` cs ->
  (((length E - 1) `div` length echo_line) <= length cs0)%nat ->
  D cs0 E = D cs E.
Proof.
  intros Hp Hn. rewrite /D.
  apply D_from_ext, (cs_ext_pred cs0 cs (length E) Hp Hn).
Qed.

Lemma pcount_cs_prefix cs0 cs E :
  cs0 `prefix_of` cs ->
  (((length E - 1) `div` length echo_line) <= length cs0)%nat ->
  pcount_from cs0 0%nat E = pcount_from cs 0%nat E.
Proof.
  intros Hp Hn.
  apply pcount_from_ext, (cs_ext_pred cs0 cs (length E) Hp Hn).
Qed.

(* the cursor at zero pins the stage: [pending_n cs 0] is [u_prologue], which
   is not empty, so an echoed input already costs bytes *)
Lemma pcount_zero cs E w :
  pcount cs E w = 0%nat -> E = [] /\ w = [].
Proof.
  rewrite /pcount. intros H0.
  assert (Hw : w = []) by (apply nil_length_inv; lia).
  destruct E as [| x E]; [by split |]. exfalso.
  cbn [pcount_from] in H0.
  assert (Hp0 : pending_n cs 0%nat = u_prologue) by reflexivity.
  rewrite Hp0 in H0. pose proof u_prologue_pos. lia.
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
Lemma write_stage_byte (cs0 cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) (n0 P : nat) (b : bv 8) :
  cs0 `prefix_of` cs ->
  ((n0 `div` length echo_line) <= length cs0)%nat ->
  (n0 <= length E)%nat ->
  P = pcount cs E w ->
  proc_upto cs0 (S n0) !! P = Some b ->
  length E = n0 /\ pending cs E !! length w = Some b.
Proof.
  intros Hp Hdiv Hn0 HP Hb.
  rewrite (proc_upto_cs_prefix_S cs0 cs n0 Hp Hdiv) in Hb.
  assert (Hlt : (P < length (proc_upto cs (S n0)))%nat)
    by (by apply lookup_lt_Some in Hb).
  assert (HlenE : length E = n0).
  { destruct (decide (length E = n0)) as [? | Hne]; [done | exfalso].
    assert (HSn : (S n0 <= length E)%nat) by lia.
    pose proof (proc_upto_mono cs (S n0) (length E) HSn) as Hpre.
    apply prefix_length in Hpre.
    rewrite (proc_upto_length cs E) in Hpre.
    rewrite HP /pcount in Hlt. lia. }
  split; [exact HlenE |].
  rewrite -HlenE in Hb, Hlt.
  assert (Hstrict : (length w < length (pending cs E))%nat).
  { rewrite proc_upto_snoc length_app (proc_upto_length cs E) in Hlt.
    rewrite HP /pcount in Hlt. rewrite /pending. lia. }
  eapply (proc_upto_pcount_inv cs E w (S (length E)) b);
    [lia | exact Hstrict | by rewrite -HP].
Qed.

(* THE ARM THE TRANSPORT FOUNDS, at every era, from nothing: NOTHING HAS
   BEEN ECHOED YET.  It is the successor of the first cut's [pops = [] /\
   dl = []], and the reason it is stated over [echoed pops] and not over
   [pops] is [ein_step_append]'s DROP arm: a dropped input ([cs = []]) does
   not move [echoed], so the drop arm leaves this standing and needs no
   ghost at all.  The era's input pairing is then taken at exactly one
   place -- the first ECHO -- which is where the ledger's escrow hands it
   over, and that single hand-over is what makes the two states of the
   claim (founded / paired) line up with a PURE condition on the ledger's
   own stage ([o_E so = []]).  See the handover's item 3 on why a claim
   whose founded arm is pure and whose paired arm is exclusive can only be
   made to work that way. *)
Definition ein_fresh (k : nat) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg (open_seg (le_hist e)))
  /\ (forall e, e ∈ pops -> obs_boots (le_hist e) = k)
  /\ echoed pops = []
  /\ dl = [].

(* the INPUT claim's pure fact, in the SETTLED state.  [i_owed si = false]
   is not a side condition but the state this claim describes: the CHAIN-
   FIRST window -- the echo on the wire, its log entry still owed -- belongs
   to [ein_owed] below, which is what [eout_step_echo] hands the
   [WpUart.in_append] that follows it in the same run.  So the port's own
   claim is never seen mid-window, and there the log and the era's stage
   agree exactly. *)
Definition ein_pure (k : nat) (si : istage) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg (open_seg (le_hist e)))
  /\ (forall e, e ∈ pops -> obs_boots (le_hist e) = k)
  /\ dl `prefix_of` echoed pops
  /\ i_owed si = false
  /\ seg_of (echoed pops) = i_E si.

(* ...and the OWED window's, naming the entry the append is about to file *)
Definition ein_owed (k : nat) (si : istage) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) (x : list mobs * bv 8) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg (open_seg (le_hist e)))
  /\ (forall e, e ∈ pops -> obs_boots (le_hist e) = k)
  /\ dl `prefix_of` echoed pops
  /\ i_owed si = true
  /\ i_E si = seg_of (echoed pops) ++ [x].

(* ...and the LEDGER's tie between them: one [E], and the owed window is the
   only place the two may disagree. *)
Definition stage_tie (so : ostage) (si : istage) : Prop :=
  i_E si = o_E so.

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
  rewrite /eout_pure /ostage0. cbn [o_cs o_E o_w]. split_and!.
  - rewrite D_nil. done.
  - rewrite pending_nil. apply prefix_nil.
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
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

Lemma ein_pure_0 k : ein_pure k istage0 [] [].
Proof.
  rewrite /ein_pure /istage0. cbn [i_E i_owed]. split_and!.
  - exact log_ok_nil.
  - intros e He. by apply elem_of_nil in He.
  - intros e He. by apply elem_of_nil in He.
  - apply prefix_nil.
  - reflexivity.
  - rewrite /seg_of echoed_nil. by rewrite fmap_nil.
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

Lemma ein_fresh_0 k : ein_fresh k [] [].
Proof.
  rewrite /ein_fresh. split_and!.
  - exact log_ok_nil.
  - intros e He. by apply elem_of_nil in He.
  - intros e He. by apply elem_of_nil in He.
  - exact echoed_nil.
  - reflexivity.
Qed.

Lemma stage_tie_0 : stage_tie ostage0 istage0.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(*  2.  THE GHOST NAMES AT THE FIXED PART                                  *)
(* ====================================================================== *)

(* [AppEcho.echo_fixed] becomes this record.  [eg_taint] is the landed
   counter and nothing about it moves; the other two are ECHO-OUT's.  All
   three are allocated by [AppEcho.echo_birth]. *)
Record echo_gn := MkEchoGn {
  eg_taint : gname;   (* mono_nat: 0 while disciplined, 1 after -- LANDED *)
  eg_pin   : gname;   (* ghost_map nat era_pins: the era NUMBER's ghosts *)
}.

(* the ghosts of one era.  [ep_gcs] is the line choices as a mono_list, and
   it is there only so that a WRITER can hold a persistent lower bound
   (review S9): the stage halves are spoken for. *)
Record era_pins := MkPins {
  ep_gso : gname;
  ep_gsi : gname;
  ep_go  : gname;
  ep_gcs : gname;
  ep_gE  : gname;   (* mono_nat: the era's STAGE INDEX [length (o_E so)] *)
}.

Class echoOutG (Σ : gFunctors) := EchoOutG {
  eo_mono_nat : mono_natG Σ;
  eo_ostage   : ghost_varG Σ ostage;
  eo_istage   : ghost_varG Σ istage;
  eo_turn     : ghost_varG Σ nat;
  eo_pin      : ghost_mapG Σ nat era_pins;
  eo_cs       : inG Σ (mono_listR (leibnizO nat));
}.
#[global] Existing Instances eo_mono_nat eo_ostage eo_istage eo_turn
  eo_pin eo_cs.

Section echo_out.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  (* THE TAINT, ABSTRACTLY.  [AppEcho.echo_taint] is [mono_nat_lb_own
     (eg_taint γ) 1]; this file takes it as a parameter so that it sits
     BELOW [AppEcho] and the two claims can be read without the era-0 pin
     cone. *)
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.

  (* THE ERA'S ADOPTION TOKEN, ABSTRACTLY (REVISION 7(a); lane CONS-IO
     milestone D).  The kernel mints ONE token per generation and lends it to
     init in the boot bundle; it is what makes the era's ADOPTION -- the
     first verified write, which inserts the era's ghosts into the ledger --
     happen at most once.  Only its EXCLUSIVITY is used, and only against the
     copy the ledger keeps for every era it has already adopted: that is what
     makes the insert an INSERT-IF-ABSENT with no bound on the map's keys and
     hence with no comparison of the ledger's history against anything.

     It is a section parameter so that this file stays independent of the
     kernel's construction; [AppEcho] discharges the hypothesis at the
     instantiation. *)
  Context (era_tok : nat -> iProp Σ).
  Context (era_tok_excl : forall k, era_tok k -∗ era_tok k -∗ False).
  Context (era_tok_timeless : forall k, Timeless (era_tok k)).
  #[local] Existing Instance era_tok_timeless.

  (* ---- the era's ghosts, keyed by the ERA NUMBER ---- *)

  (* PERSISTENT: era [k]'s ghosts.  Keyed by the era NUMBER, so a claim at
     [k] and the ledger agree on which ghosts they mean by function
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

  (* the two stages, EACH with exactly two halves (review S1) *)
  Definition out_frag (v : era_pins) (so : ostage) : iProp Σ :=
    ghost_var (ep_gso v) (1/2) so.
  Definition out_auth (v : era_pins) (so : ostage) : iProp Σ :=
    ghost_var (ep_gso v) (1/2) so.
  Definition in_frag (v : era_pins) (si : istage) : iProp Σ :=
    ghost_var (ep_gsi v) (1/2) si.
  Definition in_auth (v : era_pins) (si : istage) : iProp Σ :=
    ghost_var (ep_gsi v) (1/2) si.

  Global Instance out_frag_timeless v so : Timeless (out_frag v so).
  Proof. rewrite /out_frag. apply _. Qed.
  Global Instance out_auth_timeless v so : Timeless (out_auth v so).
  Proof. rewrite /out_auth. apply _. Qed.
  Global Instance in_frag_timeless v si : Timeless (in_frag v si).
  Proof. rewrite /in_frag. apply _. Qed.
  Global Instance in_auth_timeless v si : Timeless (in_auth v si).
  Proof. rewrite /in_auth. apply _. Qed.

  Lemma out_agree v so so' : out_frag v so -∗ out_auth v so' -∗ ⌜so = so'⌝.
  Proof.
    rewrite /out_frag /out_auth. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. iPureIntro. exact Heq.
  Qed.

  Lemma out_update v so so' so'' :
    out_frag v so -∗ out_auth v so' ==∗ out_frag v so'' ∗ out_auth v so''.
  Proof.
    rewrite /out_frag /out_auth. iIntros "H1 H2".
    iMod (ghost_var_update_halves so'' with "H1 H2") as "[H1 H2]".
    iModIntro. iFrame "H1 H2".
  Qed.

  Lemma in_agree v si si' : in_frag v si -∗ in_auth v si' -∗ ⌜si = si'⌝.
  Proof.
    rewrite /in_frag /in_auth. iIntros "H1 H2".
    iDestruct (ghost_var_agree with "H1 H2") as %Heq. iPureIntro. exact Heq.
  Qed.

  Lemma in_update v si si' si'' :
    in_frag v si -∗ in_auth v si' ==∗ in_frag v si'' ∗ in_auth v si''.
  Proof.
    rewrite /in_frag /in_auth. iIntros "H1 H2".
    iMod (ghost_var_update_halves si'' with "H1 H2") as "[H1 H2]".
    iModIntro. iFrame "H1 H2".
  Qed.

  (* THE CURSOR: the era's process-byte count.  Half travels in the
     programs' payloads (fork [Rc], exit/wait [Q]), half sits in the ledger,
     and the ECHO NEVER TOUCHES IT ([pcount_echo]). *)
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

  (* THE LINE CHOICES, as a monotone list: the ledger holds the authority,
     a writer holds a persistent lower bound (review S9). *)
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

  (* THE ERA'S STAGE INDEX, monotone: the ledger holds the authority, a
     writer holds a persistent lower bound.  This is the fourth name in
     [era_pins] and the coordinator's ruling of 2026-09-14: it is what makes
     [eout_step_write]'s strictness premise PURE.  With [E_lb v n0] and the
     program's own [n0 = 17 q] (a line boundary) the byte the program owes
     is inside block [q]'s alternative and nowhere else -- see the proof of
     [eout_step_write], where [length E > n0] is refuted because the next
     line's first echo folds block [q]'s WHOLE alternative into the stream
     and the cursor could not still be indexing inside it. *)
  Definition E_auth (v : era_pins) (n : nat) : iProp Σ :=
    mono_nat_auth_own (ep_gE v) 1 n.
  Definition E_lb (v : era_pins) (n : nat) : iProp Σ :=
    mono_nat_lb_own (ep_gE v) n.

  Global Instance E_lb_persistent v n : Persistent (E_lb v n).
  Proof. rewrite /E_lb. apply _. Qed.
  Global Instance E_lb_timeless v n : Timeless (E_lb v n).
  Proof. rewrite /E_lb. apply _. Qed.
  Global Instance E_auth_timeless v n : Timeless (E_auth v n).
  Proof. rewrite /E_auth. apply _. Qed.

  Lemma E_lb_get v n : E_auth v n -∗ E_auth v n ∗ E_lb v n.
  Proof.
    rewrite /E_auth /E_lb. iIntros "H".
    iDestruct (mono_nat_lb_own_get with "H") as "#Hl". iFrame "H Hl".
  Qed.

  (* THE LAW THE WRITE SPENDS: the lower bound never exceeds the length. *)
  Lemma E_lb_le v n m : E_auth v n -∗ E_lb v m -∗ ⌜(m <= n)%nat⌝.
  Proof.
    rewrite /E_auth /E_lb. iIntros "Ha Hl".
    iDestruct (mono_nat_lb_own_valid with "Ha Hl") as %[_ ?]. by iPureIntro.
  Qed.

  Lemma E_auth_grow v n m :
    (n <= m)%nat -> E_auth v n ==∗ E_auth v m ∗ E_lb v m.
  Proof.
    intros Hle. rewrite /E_auth /E_lb. iIntros "Ha".
    by iMod (mono_nat_own_update m with "Ha") as "[$ $]"; [lia |].
  Qed.

  (* ====================================================================== *)
  (*  3.  THE TWO PORT CLAIMS, AT THE ERA NUMBER                            *)
  (* ====================================================================== *)

  Definition eout (k : nat) (ho : list mobs) (acc : list (bv 8)) : iProp Σ :=
    ( T
    ∨ ⌜acc = []⌝
    ∨ ∃ (v : era_pins) (so : ostage),
        era_pin k v ∗ out_frag v so ∗ ⌜eout_pure k ho so acc⌝)%I.

  Definition ein (k : nat) (ho : list mobs) (pops : list log_entry)
      (dl : list (list mobs * bv 8)) : iProp Σ :=
    ( T
    ∨ ⌜ein_fresh k pops dl⌝
    ∨ ∃ (v : era_pins) (si : istage),
        era_pin k v ∗ in_frag v si ∗ ⌜ein_pure k si pops dl⌝)%I.

  Global Instance eout_timeless k ho acc : Timeless (eout k ho acc).
  Proof. rewrite /eout. apply bi.or_timeless; [apply _|]. apply _. Qed.
  Global Instance ein_timeless k ho pops dl : Timeless (ein k ho pops dl).
  Proof. rewrite /ein. apply bi.or_timeless; [apply _|]. apply _. Qed.

  (* ---- THE FOUNDING ([App.Happ_boot], through
         [SystemAdequacy.app_xfer_boot_raw_out]) ----
     The FRESH arm, from nothing and at EVERY era number: the transport
     keeps the shape it has and [AppEcho.echo_Happ_boot] does not move. *)
  Lemma eout_founded k : ⊢ eout k [] [].
  Proof. rewrite /eout. iRight. iLeft. iPureIntro. reflexivity. Qed.

  Lemma ein_founded k : ⊢ ein k [] [] [].
  Proof. rewrite /ein. iRight. iLeft. iPureIntro. exact (ein_fresh_0 k). Qed.

  (* ---- THE LICENCES ([App.Happ_out_sup] / [Happ_in_sup]) ---- *)
  Lemma eout_of_taint k ho acc : T -∗ eout k ho acc.
  Proof. iIntros "HT". rewrite /eout. iLeft. iExact "HT". Qed.

  Lemma ein_of_taint k ho pops dl : T -∗ ein k ho pops dl.
  Proof. iIntros "HT". rewrite /ein. iLeft. iExact "HT". Qed.

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
  (*  4.  THE LEDGER'S ERA MACHINE                                          *)
  (* ====================================================================== *)

  (* THE LEDGER IS HISTORY-FREE, AND THERE IS NO "CURRENT ERA".

     Everything an era's slot says is about its STAGE; the only facts that
     mention a history -- the same-cycle ones -- travel in the port claims,
     at the claim's OWN witness ([eout_pure]).  That is what makes section 7
     possible: the ECHO's links fire at the consputc stores, long after the
     history the byte arrived at, so a lemma that needed the ledger to be AT
     that history could never be applied; and a lemma that needed the ledger
     to know which era is current would have to compare the ledger's history
     against the link's, which no link can do (the observation AUTHORITY
     lives in the state interpretation).

     So an era's slot is created at its ADOPTION and stays for good, a link
     at [k] finds its era through the pin map and nothing else, and a stale
     era's writer meets its own era's slot exactly as it did while the era
     ran.  Nothing has to be retired at a power event, and [era_closed] --
     the arm the first cut kept for a link at a dead era -- is gone.

     THE TWO ESCROWS.  Each port claim has a FOUNDED arm (which the
     transport must produce from nothing, so it cannot hold a ghost) and a
     PAIRED arm (which holds one half of the era's stage).  The ledger
     therefore holds the claim's half in escrow exactly while the claim may
     still be founded, and hands it over in the step that leaves the founded
     arm:
       - the output claim leaves [acc = []] at the era's FIRST PROCESS BYTE,
         which is [P = 0 -> P = 1] -- and that is the ADOPTION;
       - the input claim leaves [echoed pops = []] at the era's FIRST ECHO,
         which is [o_E so = [] -> o_E so = [x]].
     The output escrow carries the era's TURN as well, because the first
     write is also where the writer's cursor is born. *)
  Definition era_slot (v : era_pins) (so : ostage) (si : istage)
      (P : nat) : iProp Σ :=
    (out_auth v so ∗ in_auth v si
     ∗ (match P with
        | 0%nat => out_frag v so ∗ turn v P
        | S _ => True
        end)
     ∗ (match length (o_E so) with
        | 0%nat => in_frag v si
        | S _ => True
        end)
     ∗ turn_auth v P
     ∗ cs_auth v (o_cs so)
     ∗ E_auth v (length (o_E so))
     ∗ ⌜P = pcount (o_cs so) (o_E so) (o_w so)⌝
     ∗ ⌜stage_tie so si⌝
     ∗ ⌜Forall (fun i => (i < length line_alts)%nat) (o_cs so)⌝
     ∗ ⌜cs_len_ok so⌝)%I.

  Global Instance era_slot_timeless v so si P :
    Timeless (era_slot v so si P).
  Proof.
    rewrite /era_slot. destruct P; destruct (length (o_E so)); apply _.
  Qed.

  (* ONE ADOPTED ERA: its slot, and the TOKEN that was spent to adopt it.
     Keeping the token is what makes the adoption's insert an
     INSERT-IF-ABSENT: a second adopter at [k] brings the kernel's token for
     [k] and the ledger already has it. *)
  Definition era_entry (k : nat) (v : era_pins) : iProp Σ :=
    (era_tok k ∗ ∃ so si P, era_slot v so si P)%I.

  Global Instance era_entry_timeless k v : Timeless (era_entry k v).
  Proof. rewrite /era_entry. apply _. Qed.

  Definition era_inv : iProp Σ :=
    (∃ Mp : gmap nat era_pins,
       ghost_map_auth (eg_pin γ) 1 Mp
       ∗ ([∗ map] k ↦ v ∈ Mp, era_entry k v))%I.

  Global Instance era_inv_timeless : Timeless era_inv.
  Proof. rewrite /era_inv. apply _. Qed.

  (* THE ACCESSOR every link spends: the era's slot, and the promise to put
     one back. *)
  Lemma era_inv_acc (k : nat) (v : era_pins) :
    era_pin k v -∗ era_inv -∗
      ∃ so si P, era_slot v so si P
        ∗ (∀ so' si' P', era_slot v so' si' P' -∗ era_inv).
  Proof.
    iIntros "#Hpin H". iDestruct "H" as (Mp) "[Hm Hbig]".
    iDestruct (ghost_map_lookup with "Hm Hpin") as %Hlk.
    iDestruct (big_sepM_lookup_acc _ _ k v Hlk with "Hbig") as "[Hent Hback]".
    iDestruct "Hent" as "[Htok Hslot]".
    iDestruct "Hslot" as (so si P) "Hslot".
    iExists so, si, P. iFrame "Hslot".
    iIntros (so' si' P') "Hslot'". iExists Mp. iFrame "Hm".
    iApply "Hback". iFrame "Htok". iExists so', si', P'. iFrame "Hslot'".
  Qed.

  (* ...and THE ADOPTION's own step (REVISION 7(c)): the era's ghosts go in
     at [k] against its token, which the ledger then keeps. *)
  Lemma era_inv_insert (k : nat) (v : era_pins) (so : ostage) (si : istage)
      (P : nat) :
    era_tok k -∗ era_slot v so si P -∗ era_inv ==∗ era_pin k v ∗ era_inv.
  Proof.
    iIntros "Htok Hslot H". iDestruct "H" as (Mp) "[Hm Hbig]".
    destruct (Mp !! k) as [v' |] eqn:Hlk.
    { iDestruct (big_sepM_lookup_acc _ _ k v' Hlk with "Hbig")
        as "[[Htok' _] _]".
      iDestruct (era_tok_excl k with "Htok Htok'") as "[]". }
    iMod (ghost_map_insert_persist k v Hlk with "Hm") as "[Hm #Hpin]".
    iModIntro. iFrame "Hpin". iExists (<[k := v]> Mp). iFrame "Hm".
    iApply (big_sepM_insert _ _ k v Hlk).
    iSplitR "Hbig"; [| iExact "Hbig"].
    iFrame "Htok". iExists so, si, P. iFrame "Hslot".
  Qed.

  (* THE ERA'S GHOSTS AT FULL OWNERSHIP (REVISION 7(b)): what the transport's
     founding allocates into [app_boot], and what its holder brings to the
     era's first write. *)
  Definition era_full (v : era_pins) : iProp Σ :=
    (ghost_var (ep_gso v) 1 ostage0 ∗ ghost_var (ep_gsi v) 1 istage0
     ∗ ghost_var (ep_go v) 1 0%nat
     ∗ own (ep_gcs v) (●ML ([] : list (leibnizO nat)))
     ∗ mono_nat_auth_own (ep_gE v) 1 0%nat)%I.

  Global Instance era_full_timeless v : Timeless (era_full v).
  Proof. rewrite /era_full. apply _. Qed.

  Lemma era_full_alloc : ⊢ |==> ∃ v : era_pins, era_full v.
  Proof.
    iMod (ghost_var_alloc ostage0) as (gso) "Ho".
    iMod (ghost_var_alloc istage0) as (gsi) "Hi".
    iMod (ghost_var_alloc 0%nat) as (go) "Ht".
    iMod (own_alloc (●ML ([] : list (leibnizO nat)))) as (gcs) "Hcs";
      [apply mono_list_auth_valid |].
    iMod (mono_nat_own_alloc 0%nat) as (gE) "[HE _]".
    iModIntro. iExists (MkPins gso gsi go gcs gE).
    rewrite /era_full /=. iFrame "Ho Hi Ht Hcs HE".
  Qed.

  (* ...and its split into the ledger's slot, which is the anti-vacuity
     witness as well (review S1): the paired state is INHABITED. *)
  Lemma era_full_slot (v : era_pins) :
    era_full v -∗ era_slot v ostage0 istage0 0%nat.
  Proof.
    rewrite /era_full /era_slot /out_auth /in_auth /out_frag /in_frag
            /turn /turn_auth /cs_auth /E_auth.
    iIntros "(Ho & Hi & Ht & Hcs & HE)".
    iEval (rewrite -Qp.half_half) in "Ho".
    iDestruct (ghost_var_split with "Ho") as "[Ho1 Ho2]".
    iEval (rewrite -Qp.half_half) in "Hi".
    iDestruct (ghost_var_split with "Hi") as "[Hi1 Hi2]".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct (ghost_var_split with "Ht") as "[Ht1 Ht2]".
    cbn [o_cs o_E o_w ostage0 length].
    iFrame "Ho1 Hi1 Ho2 Ht1 Hi2 Ht2 Hcs HE".
    iPureIntro. split_and!.
    - reflexivity.
    - exact stage_tie_0.
    - constructor.
    - exact cs_len_ok_0.
  Qed.

  (* ...and THE WHOLE LEDGER, which is what [AppEcho.echo_R] becomes. *)
  Definition echo_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint γ) 1 (if decide (disc h) then 0%nat else 1%nat)
     ∗ era_inv
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
    iIntros "Ht Hm". rewrite /echo_led /era_inv.
    rewrite decide_True; [| exact disc_nil].
    iFrame "Ht".
    iSplitL "Hm".
    - iExists ∅. iFrame "Hm". by rewrite big_sepM_empty.
    - iLeft. iPureIntro. rewrite /cycles_of /cycles_rev /=. constructor.
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
    intros He (cs & Hcs & Hpre). exists cs. split; [exact Hcs |].
    rewrite obs_wire_app He app_nil_r.
    rewrite /sess ins_app length_app.
    etrans; [exact Hpre |]. apply sess_n_mono. lia.
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


  Lemma echo_led_pow (h : list mobs) (on : bool) :
    echo_led h ==∗ echo_led (h ++ [if on then ObsPowerOff else ObsPowerOn]).
  Proof.
    iIntros "(Ht & He & Hphi)". rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_power h on)).
    iFrame "Ht".
    destruct on.
    - iModIntro. iFrame "He".
      rewrite cycles_of_off. iExact "Hphi".
    - iModIntro. iFrame "He".
      rewrite cycles_of_on.
      iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
      iLeft. iPureIntro. apply Forall_app. split; [exact Hg |].
      apply Forall_singleton. exists []. split; [constructor |].
      rewrite /sess /= sess_n_0. cbn [obs_wire]. apply prefix_nil.
  Qed.

  Lemma echo_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (T ∨ ⌜good_out (open_seg h ++ [ObsUartOut i b])⌝) -∗
    echo_led h ==∗ echo_led (h ++ [ObsUartOut i b]).
  Proof.
    intros Hsh. iIntros "Hgo (Hcnt & He & Hphi)".
    rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_out h i b Hsh)).
    iModIntro. iFrame "Hcnt He".
    iDestruct "Hphi" as "[%Hg | HT]"; [| by iRight].
    iDestruct "Hgo" as "[HT | %Hgo]"; [by iRight |].
    iLeft. iPureIntro. by apply phi_step_cons.
  Qed.

  Lemma echo_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    echo_led h ==∗
      echo_led (h ++ [ObsUartIn i b])
      ∗ (⌜disc (h ++ [ObsUartIn i b])⌝ ∨ mono_nat_lb_own (eg_taint γ) 1).
  Proof.
    intros Hsh. iIntros "(Hcnt & He & Hphi)".
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
      iModIntro. iFrame "Hcnt He Hphi". iLeft. iPureIntro. exact Hd'.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (disc h)); lia |].
      iModIntro. iFrame "Hcnt He Hphi". iRight. iExact "Hlb".
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

  (* THE LEDGER'S HISTORY IS NOT THE LINK'S.  Every step below takes the
     ledger at an ARBITRARY [hl] and gives it back there: the ledger is
     history-free except for its taint counter and its [phi] conjunct, and
     no link moves either.  That is what lets section 7 open [obsN] inside a
     link -- the echo's links fire at the consputc STORES, at a history the
     shift cannot name, and no link may compare a history against the
     ledger's, because the observation AUTHORITY lives in the state
     interpretation. *)

  (* THE TAINT, READ OFF THE LEDGER.  A link that meets an UNDISCIPLINED
     ledger is free: the counter is already up, so the taint is minted and
     every claim's taint arm absorbs the step.  [T_of_lb] is the converse of
     the [T -∗ lb] the callers already hand over, and [AppEcho] discharges
     it by [iIntros "$"] -- [echo_taint] IS that lower bound. *)
  Context (T_of_lb : mono_nat_lb_own (eg_taint γ) 1 -∗ T).

  Lemma led_taint (hl : list mobs) :
    ¬ disc hl -> echo_led hl -∗ echo_led hl ∗ T.
  Proof.
    intros Hd. rewrite /echo_led (decide_False _ _ Hd).
    iIntros "(Hcnt & He & Hphi)".
    iDestruct (mono_nat_lb_own_get with "Hcnt") as "#Hlb".
    iDestruct (T_of_lb with "Hlb") as "#HT".
    iFrame "Hcnt He Hphi HT".
  Qed.

  (* the input claim OPENED at the era's pin, in the CHAIN-FIRST window.
     [WpUart.in_run] is chain-first and append-last, and the application
     chains the two steps itself, so this is what [eout_step_echo] hands
     [ein_step_append].  It is NOT [ein]: between the echo and the append
     the log is one entry behind the era's stage, and the port's own claim
     has no arm for that -- which is exactly what keeps [ein]'s two arms
     lined up with the ledger's escrow ([era_slot]). *)
  Definition ein_op (k : nat) (h : list mobs) (c : bv 8)
      (pops : list log_entry) (dl : list (list mobs * bv 8)) : iProp Σ :=
    (T ∨ ∃ (v : era_pins) (si : istage),
        era_pin k v ∗ in_frag v si
        ∗ ⌜ein_owed k si pops dl (open_seg h, c)⌝)%I.

  (* (E) THE ECHO SHIFT's core step, at the STORE arm: the byte goes out,
     the era's stage gains the entry and the input claim is opened for the
     append that follows.  The cursor is UNTOUCHED ([pcount_echo]), which is
     what lets this close with the writer absent (review S2).

     WHAT THE ECHO RE-ESTABLISHES, and how.  The output claim's same-cycle
     facts are stated at the claim's OWN witness, and this step moves that
     witness to [h] -- so it has to show that every entry the era has
     already echoed is a prefix of THIS cycle's segment.  It reads that off
     the INPUT side: the log's entries are below [h] ([Hord]) and carry the
     era's stamp ([ein_pure]), and two histories of one era with the machine
     on lie in one cycle ([EchoOutPure.open_seg_prefix_boots]).

     THE TWO CALLER-OWED PREMISES.  [Hlt] says the echoes the era has
     already LOGGED answer inputs strictly below this one, and [Hpro] says
     that if the era has logged none then nothing of it is on the wire yet.
     Both hold at every call site -- [SpecConsoleintr.cons_echo_shift] fires
     once per accepted byte, at the history the byte arrived at. *)
  Lemma eout_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho hi hl : list mobs) (acc : list (bv 8))
      (pops : list log_entry) (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` acc ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    (length (echoed pops) < length (ins (open_seg h)))%nat ->
    (echoed pops = [] -> acc `prefix_of` u_prologue) ->
    □ (T -∗ mono_nat_lb_own (eg_taint γ) 1) -∗
    echo_led hl -∗ eout k ho acc -∗ ein k hi pops dl ==∗
      echo_led hl ∗ eout k h (acc ++ [echo_of c]) ∗ ein_op k h c pops dl.
  Proof.
    intros Hdisc Hsh Hk Hends Hwire Hord Hlt Hpro. subst k.
    iIntros "#HTT Hled Hout Hin".
    (* an UNDISCIPLINED ledger pays outright *)
    destruct (decide (disc hl)) as [Hdl | Hdl]; last first.
    { iDestruct (led_taint hl Hdl with "Hled") as "[Hled #HT]".
      iModIntro. iFrame "Hled". iSplitR.
      - by iApply eout_of_taint.
      - rewrite /ein_op. by iLeft. }
    pose proof (disc_seg'_open_seg h Hsh Hdisc) as Hd'.
    pose proof (disc_seg'_proj _ Hd') as Hdseg.
    pose proof (open_seg_ends_in h c Hends) as Hends'.
    destruct (disc_seg'_pt_last (open_seg h) c Hd' Hends')
      as (cs' & Hcs'b & Hlow').
    assert (Hm1 : (1 <= length (ins (open_seg h)))%nat).
    { destruct Hends' as [h0 Hh0]. rewrite Hh0 ins_app ins_in length_app /=.
      lia. }
    rewrite /echo_led !(decide_True 0%nat 1%nat Hdl).
    iDestruct "Hled" as "(Hcnt & Hera & Hphi)".
    (* under the discipline the taint is impossible *)
    iAssert (□ (T -∗ mono_nat_auth_own (eg_taint γ) 1 0%nat -∗ False))%I
      as "#Hno".
    { iIntros "!> HT Hc". iDestruct ("HTT" with "HT") as "#Hlb".
      iDestruct (mono_nat_lb_own_valid with "Hc Hlb") as %[_ Hle]. lia. }
    iDestruct "Hout" as "[HT | Hout]".
    { iDestruct ("Hno" with "HT Hcnt") as "[]". }
    (* the founded OUTPUT arm is refuted: the discipline already put the
       prologue on the wire, and an empty [acc] cannot hold it *)
    iDestruct "Hout" as "[%Hnil | Hp]".
    { rewrite Hnil in Hwire. apply prefix_nil_inv in Hwire.
      rewrite Hwire in Hlow'. apply prefix_nil_inv in Hlow'.
      by destruct (sess_n_nonnil cs' (length (ins (open_seg h)) - 1) Hlow'). }
    iDestruct "Hp" as (v so) "(#Hpin & Hfrag & %Hpure)".
    iDestruct (era_inv_acc (obs_boots h) v with "Hpin Hera")
      as (so2 si P) "[Hslot Hback]".
    rewrite /era_slot.
    iDestruct "Hslot" as "(Ho & Hi & Hoe & Hie & Hta & Hcs & HE & Hpures)".
    iDestruct (out_agree with "Hfrag Ho") as %Heqso. subst so2.
    iDestruct "Hpures" as "(%HP & %Htie & %Hcsb & %Hcsl)".
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hcsb' & Hdsc & _ & _ & _).
    (* the input claim's half, and the log's tie to the era's stage *)
    iDestruct "Hin" as "[HT | Hin]".
    { iDestruct ("Hno" with "HT Hcnt") as "[]". }
    iAssert (in_frag v si ∗ ⌜i_E si = seg_of (echoed pops)⌝ ∗ ⌜log_ok pops⌝
             ∗ ⌜forall e, e ∈ pops -> disc_seg (open_seg (le_hist e))⌝
             ∗ ⌜forall e, e ∈ pops -> obs_boots (le_hist e) = obs_boots h⌝
             ∗ ⌜dl `prefix_of` echoed pops⌝
             ∗ ⌜(length (o_E so) < length (ins (open_seg h)))%nat⌝
             ∗ in_auth v si)%I
      with "[Hin Hie Hi]"
      as "(Hifrag & %Hie1 & %Hlog & %Hdsc2 & %Hstamp & %Hdlp & %HElt & Hi)".
    { iDestruct "Hin" as "[%Hfr | Hp2]".
      - destruct Hfr as (Hlog & Hdsc2 & Hstamp & Hech & Hdlnil).
        (* nothing logged: by [Hpro] the era has echoed nothing either *)
        assert (HEnil : o_E so = []).
        { pose proof (prefix_length _ _ (Hpro Hech)) as Hle.
          rewrite Hacc length_app in Hle.
          destruct (o_E so) as [| y E1] eqn:HEeq; [reflexivity | exfalso].
          rewrite ?HEeq in Hle.
          assert (HD : D (o_cs so) (y :: E1)
                       = u_prologue ++ ([echo_of y.2]
                                        ++ D_from (o_cs so) 1%nat E1))
            by reflexivity.
          rewrite HD !length_app in Hle. cbn [length] in Hle. lia. }
        rewrite HEnil. cbn [length].
        iFrame "Hie Hi". iPureIntro. split_and!.
        + rewrite /stage_tie in Htie. rewrite Htie HEnil Hech.
          by rewrite /seg_of fmap_nil.
        + exact Hlog.
        + exact Hdsc2.
        + exact Hstamp.
        + rewrite Hdlnil. apply prefix_nil.
        + lia.
      - iDestruct "Hp2" as (v2 si2) "(#Hpin2 & Hifrag & %Hp3)".
        iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
        iDestruct (in_agree with "Hifrag Hi") as %Heqsi. subst si2.
        destruct Hp3 as (Hlog & Hdsc2 & Hstamp & Hdlp & Hno2 & Hseg).
        iFrame "Hifrag Hi". iPureIntro. split_and!;
          [by rewrite Hseg | exact Hlog | exact Hdsc2 | exact Hstamp
           | exact Hdlp |].
        rewrite /stage_tie in Htie. rewrite -Htie -Hseg seg_of_length.
        exact Hlt. }
    (* THE SAME-CYCLE FACTS, re-established at [h] off the INPUT side *)
    assert (Hprefixes : Forall (fun x => x.1 `prefix_of` open_seg h) (o_E so)).
    { rewrite /stage_tie in Htie. rewrite -Htie Hie1.
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
                  `prefix_of` (D (o_cs so) (o_E so) ++ o_w so))
      by (rewrite -Hacc; exact Hwire).
    assert (Hlow : sess_n (o_cs so) (length (ins (open_seg h)) - 1)
                   `prefix_of` obs_wire Uart0 (open_seg h)).
    { destruct (sess_n_prefix_det (o_cs so) cs'
                  (length (ins (open_seg h)) - 1) (length (o_E so))
                  Hcsb' Hcs'b) as [_ Heq].
      { etrans; [exact Hlow' |]. etrans; [exact Hup |].
        by apply D_stage_prefix. }
      rewrite -Heq. exact Hlow'. }
    destruct (D2_next_input (o_cs so) (o_E so) (o_w so)
                (obs_wire Uart0 (open_seg h)) (open_seg h) c
                (length (ins (open_seg h)))
                Hbyte Hidx Hnew' Hends' eq_refl Hwpre Hlow Hup)
      as [Hmeq Hweq].
    (* the cursor is not at zero: the prologue is owed before the first echo *)
    destruct P as [| P'].
    { exfalso. destruct (pcount_zero _ _ _ (eq_sym HP)) as [HEnil Hwnil].
      rewrite HEnil pending_nil Hwnil in Hweq.
      pose proof u_prologue_pos as Hp. rewrite -Hweq in Hp. cbn in Hp. lia. }
    (* the byte's own facts *)
    assert (Hbc : c = echo_line !!! ((length (o_E so) `mod` length echo_line)%nat)).
    { rewrite (disc_seg_last_byte (open_seg h) c Hdseg Hends').
      by rewrite Hmeq Nat.sub_succ Nat.sub_0_r. }
    iMod (out_update v so so
            (MkO (o_cs so) (o_E so ++ [(open_seg h, c)]) [])
            with "Hfrag Ho") as "[Hfrag Ho]".
    iMod (in_update v si si (MkI (i_E si ++ [(open_seg h, c)]) true)
            with "Hifrag Hi") as "[Hifrag Hi]".
    iMod (E_auth_grow v (length (o_E so))
            (length (o_E so ++ [(open_seg h, c)]))
            ltac:(rewrite length_app /=; lia) with "HE") as "[HE _]".
    iModIntro. iSplitR "Hfrag Hifrag".
    - iFrame "Hcnt Hphi".
      iApply ("Hback" $! (MkO (o_cs so) (o_E so ++ [(open_seg h, c)]) [])
                      (MkI (i_E si ++ [(open_seg h, c)]) true) (S P')).
      rewrite /era_slot. cbn [o_cs o_E o_w i_E i_owed].
      rewrite length_app. cbn [length].
      replace (length (o_E so) + 1)%nat with (S (length (o_E so))) by lia.
      iFrame "Ho Hi Hta Hcs HE". iPureIntro. split_and!.
      + rewrite (pcount_echo (o_cs so) (o_E so) (open_seg h, c) (o_w so) Hweq).
        exact HP.
      + rewrite /stage_tie. cbn [i_E o_E].
        rewrite /stage_tie in Htie. by rewrite Htie.
      + exact Hcsb.
      + exact (cs_len_ok_echo so (open_seg h, c) Hcsb Hweq Hcsl).
    - iSplitL "Hfrag".
      + iRight. iRight.
        iExists v, (MkO (o_cs so) (o_E so ++ [(open_seg h, c)]) []).
        iFrame "Hpin Hfrag". iPureIntro.
        rewrite /eout_pure. cbn [o_cs o_E o_w]. split_and!.
        * rewrite Hacc Hweq (D_app (o_cs so) (o_E so) (open_seg h, c)).
          cbn [snd]. by rewrite app_nil_r app_assoc.
        * apply prefix_nil.
        * intros jj y Hy.
          destruct (decide (jj < length (o_E so))%nat) as [Hj | Hj].
          { rewrite lookup_app_l in Hy; [| lia]. by apply Hidx. }
          rewrite lookup_app_r in Hy; [| lia].
          assert (Hjj : jj = length (o_E so)).
          { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
          subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
          injection Hy as <-. cbn [fst snd]. split; [exact Hends' | lia].
        * intros jj y Hy.
          destruct (decide (jj < length (o_E so))%nat) as [Hj | Hj].
          { rewrite lookup_app_l in Hy; [| lia]. by apply Hbyte. }
          rewrite lookup_app_r in Hy; [| lia].
          assert (Hjj : jj = length (o_E so)).
          { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
          subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
          injection Hy as <-. cbn [snd]. exact Hbc.
        * exact Hcsb'.
        * rewrite Forall_app. split; [exact Hdsc |].
          rewrite Forall_singleton. cbn. exact Hdseg.
        * rewrite Forall_app. split; [exact Hprefixes |].
          rewrite Forall_singleton. cbn [fst]. reflexivity.
        * rewrite length_app. cbn [length]. lia.
        * by right.
      + iRight. iExists v, (MkI (i_E si ++ [(open_seg h, c)]) true).
        iFrame "Hpin Hifrag". iPureIntro.
        rewrite /ein_owed. cbn [i_E i_owed]. split_and!;
          [exact Hlog | exact Hdsc2 | exact Hstamp | exact Hdlp
           | reflexivity |].
        by rewrite Hie1.
  Qed.

  (* ...and the LOG's side, fired after the chain ([WpUart.in_append]).  The
     ECHOED arm takes the window [eout_step_echo] opened; the DROP arm takes
     the port's own claim, because the kernel may stop the run before the
     echo ([WpUart.in_run]'s left conjunct) and then no window was opened. *)
  Lemma ein_step_append (k : nat) (h hl : list mobs) (c : bv 8)
      (pops : list log_entry) (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    echo_led hl -∗ ein_op k h c pops dl ==∗
      echo_led hl ∗ ein k h (pops ++ [(h, c, [echo_of c])]) dl.
  Proof.
    intros Hdisc Hsh Hk Hends Hord. subst k. iIntros "Hled Hop".
    iDestruct "Hop" as "[#HT | Hp]".
    { iModIntro. iFrame "Hled". by iApply ein_of_taint. }
    iDestruct "Hp" as (v si) "(#Hpin & Hifrag & %Howed)".
    destruct Howed as (Hlog & Hdsc & Hstamp & Hdlp & Hno & Hie1).
    rewrite /echo_led. iDestruct "Hled" as "(Hcnt & Hera & Hphi)".
    iDestruct (era_inv_acc (obs_boots h) v with "Hpin Hera")
      as (so si2 P) "[Hslot Hback]".
    rewrite /era_slot.
    iDestruct "Hslot" as "(Ho & Hi & Hoe & Hie & Hta & Hcs & HE & Hpures)".
    iDestruct (in_agree with "Hifrag Hi") as %Heqsi. subst si2.
    iDestruct "Hpures" as "(%HP & %Htie & %Hcsb & %Hcsl)".
    (* the era's stage is not empty here, so the ledger's escrow is spent *)
    assert (HEne : length (o_E so) = S (length (seg_of (echoed pops)))).
    { rewrite /stage_tie in Htie. rewrite -Htie Hie1 length_app /=. lia. }
    destruct (length (o_E so)) as [| nE] eqn:HL; [exfalso; lia |].
    iMod (in_update v si si (MkI (i_E si) false) with "Hifrag Hi")
      as "[Hifrag Hi]".
    iModIntro. iSplitR "Hifrag".
    - iFrame "Hcnt Hphi".
      iApply ("Hback" $! so (MkI (i_E si) false) P).
      rewrite /era_slot HL.
      iFrame "Ho Hi Hoe Hta Hcs HE". iPureIntro. split_and!.
      + exact HP.
      + rewrite /stage_tie. cbn [i_E]. by rewrite /stage_tie in Htie.
      + exact Hcsb.
      + exact Hcsl.
    - iRight. iRight. iExists v, (MkI (i_E si) false).
      iFrame "Hpin Hifrag". iPureIntro.
      rewrite /ein_pure. cbn [i_E i_owed]. split_and!.
      + apply cl_log_ok_snoc; [exact Hlog | exact Hends | | ].
        * rewrite /le_byte /le_echo /=. by right; left.
        * intros e' He'. by apply Hord.
      + intros e He. apply elem_of_app in He as [He | He];
          [by apply Hdsc |].
        apply elem_of_list_singleton in He as ->.
        rewrite /le_hist /=. exact (disc_seg_open_seg h Hsh Hdisc).
      + intros e He. apply elem_of_app in He as [He | He];
          [by apply Hstamp |].
        apply elem_of_list_singleton in He as ->. by rewrite /le_hist /=.
      + rewrite (echoed_snoc_yes pops (h, c, [echo_of c])
                   (log_echoed_echo h c)).
        destruct Hdlp as [z ->]. eexists. by rewrite -app_assoc.
      + reflexivity.
      + rewrite (echoed_snoc_yes pops (h, c, [echo_of c])
                   (log_echoed_echo h c)).
        rewrite seg_of_app Hie1. by rewrite /seg_of /le_hist /le_byte /=.
  Qed.

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
    intros Hdisc Hsh Hk Hends Hord. iIntros "Hin".
    assert (Hlog' : forall (l : list log_entry), log_ok l ->
              (forall e, e ∈ l -> hist_ext (le_hist e) h) ->
              log_ok (l ++ [(h, c, [])])).
    { intros l Hl Ho. apply cl_log_ok_snoc; [exact Hl | exact Hends | | ].
      - rewrite /le_byte /le_echo /=. by left.
      - intros e' He'. by apply Ho. }
    assert (Hdsc' : forall (l : list log_entry),
              (forall e, e ∈ l -> disc_seg (open_seg (le_hist e))) ->
              forall e, e ∈ l ++ [(h, c, [])] ->
                disc_seg (open_seg (le_hist e))).
    { intros l Hd e He. apply elem_of_app in He as [He | He];
        [by apply Hd |].
      apply elem_of_list_singleton in He as ->.
      rewrite /le_hist /=. exact (disc_seg_open_seg h Hsh Hdisc). }
    assert (Hst' : forall (l : list log_entry),
              (forall e, e ∈ l -> obs_boots (le_hist e) = k) ->
              forall e, e ∈ l ++ [(h, c, [])] -> obs_boots (le_hist e) = k).
    { intros l Hd e He. apply elem_of_app in He as [He | He];
        [by apply Hd |].
      apply elem_of_list_singleton in He as ->. by rewrite /le_hist /=. }
    assert (Hech' : echoed (pops ++ [(h, c, [])]) = echoed pops)
      by (apply echoed_snoc_no, log_echoed_nil_no).
    iDestruct "Hin" as "[#HT | [%Hfr | Hp]]".
    - by iApply ein_of_taint.
    - destruct Hfr as (Hlog & Hdsc & Hstamp & Hech & Hdlnil).
      iRight. iLeft. iPureIntro. rewrite /ein_fresh. split_and!.
      + by apply Hlog'.
      + by apply Hdsc'.
      + by apply Hst'.
      + by rewrite Hech'.
      + exact Hdlnil.
    - iDestruct "Hp" as (v si) "(#Hpin & Hifrag & %Hp3)".
      iRight. iRight. iExists v, si. iFrame "Hpin Hifrag".
      destruct Hp3 as (Hlog & Hdsc & Hstamp & Hdlp & Hno & Hseg).
      iPureIntro. rewrite /ein_pure. split_and!.
      + by apply Hlog'.
      + by apply Hdsc'.
      + by apply Hst'.
      + by rewrite Hech'.
      + exact Hno.
      + by rewrite Hech'.
  Qed.

  (* (W) THE WRITE, INSIDE A BLOCK.  What the writer brings: the era's pin,
     its cursor, a PERSISTENT lower bound of the line choices and one of the
     era's STAGE INDEX (review S9), and the Coq-level fact that its byte is
     the [P]-th of the era's process stream up to stage [S n0].  What it
     gets back: the cursor advanced and the two bounds, so the next write is
     paid the same way.

     THE STRICTNESS IS NOT A PREMISE.  With [E_lb v n0] the ledger EXPOSES
     the stage index, and [write_stage_byte] derives both the stage
     ([length E = n0]) and the strictness from
     [proc_upto cs0 (S n0) !! P = Some b] alone.

     THE CHOICE LIST IS NOT MOVED HERE.  [Hdiv] asks the writer's lower
     bound to reach block [n0 / 17], and the ledger's own [cs_len_ok] says
     the list is one SHORT of that exactly at a block's first byte -- so
     this form is simply not applicable there, and [eout_step_write_blk]
     below is.

     [Hfresh] IS THE ONE THING THE LEDGER CANNOT SEE.  The output claim's
     FOUNDED arm ([acc = []]) is PURE -- it has to be, because
     [App.Happ_boot] mints it from nothing at every era -- so nothing in it
     distinguishes "this era has not written yet" from "this claim's half of
     the era's stage was dropped".  The ledger closes the first case with an
     escrow at [P = 0]; the second is impossible in the tree and unprovable
     in the logic.  See the handover: the fix is for the transport's
     founding to consume the era token, which would let the founded arm
     carry it. *)
  Lemma eout_step_write (k : nat) (v : era_pins) (P n0 : nat) (b : bv 8)
      (cs0 : list nat) (ho hl : list mobs) (acc : list (bv 8)) :
    ((n0 `div` length echo_line) <= length cs0)%nat ->
    proc_upto cs0 (S n0) !! P = Some b ->
    (acc = [] -> P = 0%nat) ->
    era_pin k v -∗ turn v P -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
    echo_led hl -∗ eout k ho acc ==∗
      echo_led hl ∗ eout k ho (acc ++ [b])
      ∗ ((turn v (S P) ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T).
  Proof.
    intros Hdiv Hb Hfresh.
    iIntros "#Hpin Ht #Hcslb #HElb Hled Hcl".
    rewrite /echo_led. iDestruct "Hled" as "(Hcnt & Hera & Hphi)".
    iDestruct (era_inv_acc k v with "Hpin Hera") as (so si Pl) "[Hslot Hback]".
    rewrite /era_slot.
    iDestruct "Hslot" as "(Ho & Hi & Hoe & Hie & Hta & Hcs & HE & Hpures)".
    iDestruct (turn_agree with "Ht Hta") as %Heqp. subst Pl.
    iDestruct "Hpures" as "(%HP & %Htie & %Hcsb & %Hcsl)".
    (* the TAINT arm pays outright and moves nothing *)
    iDestruct "Hcl" as "[#HT | Hcl]".
    { iModIntro. iSplitR "".
      - iFrame "Hcnt Hphi". iApply ("Hback" $! so si P).
        rewrite /era_slot. iFrame "Ho Hi Hoe Hie Hta Hcs HE".
        iPureIntro. by split_and!.
      - iSplitR; [by iApply eout_of_taint | by iRight]. }
    (* ...otherwise the era's own half of the stage comes out: from the
       claim if it is paired, and from the ledger's escrow if it is not *)
    iAssert (out_frag v so ∗ ⌜eout_pure k ho so acc⌝ ∗ turn v P
             ∗ out_auth v so)%I
      with "[Hcl Hoe Ht Ho]" as "(Hfrag & %Hpure & Ht & Ho)".
    { destruct P as [| P'].
      - iDestruct "Hoe" as "[Hof Hto]".
        iDestruct "Hcl" as "[%Hfr | Hp]".
        + (* founded: the escrow is the claim's half, and the ledger's stage
             is at the start because the cursor is *)
          destruct (pcount_zero _ _ _ (eq_sym HP)) as [HEnil Hwnil].
          iFrame "Hof Ht Ho". iPureIntro.
          rewrite /eout_pure HEnil Hwnil. split_and!.
          * by rewrite D_nil app_nil_r.
          * apply prefix_nil.
          * intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
          * intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
          * exact Hcsb.
          * constructor.
          * constructor.
          * cbn [length]. lia.
          * by left.
        + iDestruct "Hp" as (v2 so2) "(#Hpin2 & Hfrag & %Hpure)".
          iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
          iDestruct (out_agree with "Hfrag Ho") as %<-.
          iFrame "Hfrag Ht Ho". by iPureIntro.
      - iDestruct "Hcl" as "[%Hfr | Hp]".
        + exfalso. specialize (Hfresh Hfr). lia.
        + iDestruct "Hp" as (v2 so2) "(#Hpin2 & Hfrag & %Hpure)".
          iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
          iDestruct (out_agree with "Hfrag Ho") as %<-.
          iFrame "Hfrag Ht Ho". by iPureIntro. }
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hcsb' & Hdsc & Hpre1
                       & Hpre2 & Hpre3).
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (E_lb_le with "HE HElb") as %Hn0.
    destruct (write_stage_byte cs0 (o_cs so) (o_E so) (o_w so) n0 P b
                Hcsp Hdiv Hn0 HP Hb) as [HlenE Hnext].
    (* the choice list stays put: at a block's first byte the ledger's list
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
    iMod (out_update v so so (MkO (o_cs so) (o_E so) (o_w so ++ [b]))
            with "Hfrag Ho") as "[Hfrag Ho]".
    iMod (turn_update v P P (S P) with "Ht Hta") as "[Ht Hta]".
    iModIntro.
    iSplitR "Hfrag Ht".
    - iFrame "Hcnt Hphi".
      iApply ("Hback" $! (MkO (o_cs so) (o_E so) (o_w so ++ [b])) si (S P)).
      rewrite /era_slot. cbn [o_cs o_E o_w].
      iFrame "Ho Hi Hie Hta Hcs HE".
      iPureIntro. split_and!;
        [| exact Htie | exact Hcsb | exact (cs_len_ok_write so b Hcsl Hcase)].
      rewrite pcount_write. by rewrite HP.
    - iSplitL "Hfrag".
      + iRight. iRight.
        iExists v, (MkO (o_cs so) (o_E so) (o_w so ++ [b])).
        iFrame "Hpin Hfrag". iPureIntro.
        rewrite /eout_pure. cbn [o_cs o_E o_w]. split_and!.
        * by rewrite Hacc app_assoc.
        * by apply prefix_snoc_lookup.
        * exact Hidx.
        * exact Hbyte.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
      + iLeft. iFrame "Ht Hcslb HElb".
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE (REVISION 7(d)).  The choice of
     continuation is the PROGRAM's knowledge -- sh knows whether it is about
     to print "hello world" or the exec failure -- and it is readable off
     the wire because the four alternatives begin with four distinct bytes
     ([EchoOutPure.line_alts_head_det]).  So the writer supplies the
     alternative's INDEX beside its first byte, and the step files it: the
     ledger's list grows from [q-1] to [q] at stage [17 q], and every later
     byte of the block goes through [eout_step_write] against the lower
     bound this returns.  The PROLOGUE (block 0) is not a choice and grows
     nothing -- which is why [0 < n0] is a premise here. *)
  Lemma eout_step_write_blk (k : nat) (v : era_pins) (P n0 a : nat)
      (b : bv 8) (cs0 : list nat) (ho hl : list mobs) (acc : list (bv 8)) :
    (0 < n0)%nat ->
    (n0 `mod` length echo_line)%nat = 0%nat ->
    ((n0 `div` length echo_line) <= S (length cs0))%nat ->
    P = length (proc_upto cs0 n0) ->
    (a < length line_alts)%nat ->
    line_alts !!! a !! 0%nat = Some b ->
    (acc = [] -> P = 0%nat) ->
    era_pin k v -∗ turn v P -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
    echo_led hl -∗ eout k ho acc ==∗
      echo_led hl ∗ eout k ho (acc ++ [b])
      ∗ ((turn v (S P) ∗ cs_lb v (cs0 ++ [a]) ∗ E_lb v n0) ∨ T).
  Proof.
    intros Hpos Hmod Hdiv HPeq Halt Hhead Hfresh.
    pose proof echo_line_length as HLL.
    assert (Hd1 : ((n0 - 1) `div` length echo_line
                   = n0 `div` length echo_line - 1)%nat).
    { assert (Hn1 : n0 = ((n0 - 1) + 1)%nat) by lia.
      rewrite {2}Hn1. apply div_succ_of_mod0. rewrite -Hn1. exact Hmod. }
    iIntros "#Hpin Ht #Hcslb #HElb Hled Hcl".
    rewrite /echo_led. iDestruct "Hled" as "(Hcnt & Hera & Hphi)".
    iDestruct (era_inv_acc k v with "Hpin Hera") as (so si Pl) "[Hslot Hback]".
    rewrite /era_slot.
    iDestruct "Hslot" as "(Ho & Hi & Hoe & Hie & Hta & Hcs & HE & Hpures)".
    iDestruct (turn_agree with "Ht Hta") as %Heqp. subst Pl.
    iDestruct "Hpures" as "(%HP & %Htie & %Hcsb & %Hcsl)".
    (* the TAINT arm pays outright and moves nothing *)
    iDestruct "Hcl" as "[#HT | Hcl]".
    { iModIntro. iSplitR "".
      - iFrame "Hcnt Hphi". iApply ("Hback" $! so si P).
        rewrite /era_slot. iFrame "Ho Hi Hoe Hie Hta Hcs HE".
        iPureIntro. by split_and!.
      - iSplitR; [by iApply eout_of_taint | by iRight]. }
    (* the era's cursor is past the prologue, so the claim is PAIRED *)
    assert (HPpos : (0 < P)%nat).
    { rewrite HPeq. destruct n0 as [| n0']; [lia |].
      rewrite /proc_upto (proc_upto_from_S cs0 0%nat n0') length_app.
      pose proof u_prologue_pos as Hu.
      change (pending_n cs0 0%nat) with u_prologue. lia. }
    iDestruct "Hcl" as "[%Hfr | Hp]".
    { exfalso. specialize (Hfresh Hfr). lia. }
    iDestruct "Hp" as (v2 so2) "(#Hpin2 & Hfrag & %Hpure)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (out_agree with "Hfrag Ho") as %->.
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hcsb' & Hdsc & Hpre1
                       & Hpre2 & Hpre3).
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (E_lb_le with "HE HElb") as %Hn0.
    (* the stream up to stage [n0] is the same under the writer's bound *)
    assert (Hstream : proc_upto cs0 n0 = proc_upto (o_cs so) n0).
    { apply (proc_upto_cs_prefix_pred cs0 (o_cs so) n0 Hcsp).
      lia. }
    (* the era's stage is exactly [n0]: a further echo would have folded this
       block's WHOLE alternative into the stream, past the cursor *)
    assert (HlenE : length (o_E so) = n0).
    { destruct (decide (length (o_E so) = n0)) as [? | Hne]; [done | exfalso].
      assert (HSn : (S n0 <= length (o_E so))%nat) by lia.
      pose proof (proc_upto_mono (o_cs so) (S n0) (length (o_E so)) HSn)
        as Hpre.
      apply prefix_length in Hpre.
      rewrite (proc_upto_length (o_cs so) (o_E so)) in Hpre.
      rewrite (proc_upto_snoc (o_cs so) n0) length_app -Hstream in Hpre.
      assert (Hne0 : pending_n (o_cs so) n0 <> []).
      { rewrite /pending_n. rewrite decide_False; [| lia].
        rewrite decide_True; [| exact Hmod].
        apply line_alts_nonnil, (cs_ok_of_Forall _ Hcsb). }
      assert (Hlen1 : (1 <= length (pending_n (o_cs so) n0))%nat).
      { destruct (pending_n (o_cs so) n0); [done | cbn; lia]. }
      rewrite /pcount in HP. lia. }
    (* ...and the writer stands at the block's first byte *)
    assert (Hwnil : o_w so = []).
    { assert (Hz : length (o_w so) = 0%nat).
      { rewrite /pcount in HP.
        rewrite -(proc_upto_length (o_cs so) (o_E so)) in HP.
        rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    (* the ledger's list is one short, so the writer's bound IS the list *)
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
    assert (Hpend : pending (o_cs so ++ [a]) (o_E so) !! 0%nat = Some b).
    { rewrite /pending /pending_n HlenE. rewrite decide_False; [| lia].
      rewrite decide_True; [| exact Hmod]. by rewrite Hidx0. }
    (* the transcript below stage [n0] does not read the new choice *)
    assert (HD : D (o_cs so ++ [a]) (o_E so) = D (o_cs so) (o_E so)).
    { symmetry. apply (D_cs_prefix (o_cs so) (o_cs so ++ [a]) (o_E so));
        [by eexists |].
      rewrite HlenE. lia. }
    assert (HPc : pcount_from (o_cs so ++ [a]) 0%nat (o_E so)
                  = pcount_from (o_cs so) 0%nat (o_E so)).
    { symmetry. apply (pcount_cs_prefix (o_cs so) (o_cs so ++ [a]) (o_E so));
        [by eexists |].
      rewrite HlenE. lia. }
    iMod (out_update v so so (MkO (o_cs so ++ [a]) (o_E so) [b])
            with "Hfrag Ho") as "[Hfrag Ho]".
    iMod (turn_update v P P (S P) with "Ht Hta") as "[Ht Hta]".
    iMod (cs_auth_grow v (o_cs so) a with "Hcs") as "[Hcs #Hcslb2]".
    iModIntro.
    iSplitR "Hfrag Ht".
    - iFrame "Hcnt Hphi".
      iApply ("Hback" $! (MkO (o_cs so ++ [a]) (o_E so) [b]) si (S P)).
      rewrite /era_slot. cbn [o_cs o_E o_w].
      iFrame "Ho Hi Hie Hta Hcs HE".
      iPureIntro. split_and!.
      + rewrite /pcount HPc. cbn [length]. rewrite /pcount Hwnil in HP.
        cbn [length] in HP. lia.
      + exact Htie.
      + rewrite Forall_app. split; [exact Hcsb |].
        by rewrite Forall_singleton.
      + apply (cs_len_ok_blk so a b); [by rewrite HlenE | lia | exact Hwnil
                                      | exact Hcsl].
    - iSplitL "Hfrag".
      + iRight. iRight.
        iExists v, (MkO (o_cs so ++ [a]) (o_E so) [b]).
        iFrame "Hpin Hfrag". iPureIntro.
        rewrite /eout_pure. cbn [o_cs o_E o_w]. split_and!.
        * rewrite Hacc Hwnil app_nil_r HD. reflexivity.
        * apply (prefix_snoc_lookup [] _ b); [apply prefix_nil |].
          by rewrite -Hpend.
        * exact Hidx.
        * exact Hbyte.
        * rewrite Forall_app. split; [exact Hcsb' |].
          by rewrite Forall_singleton.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
      + iLeft. rewrite Hcs0. iFrame "Ht HElb Hcslb2".
  Qed.

  (* (W'') THE ERA'S ADOPTION, which is its FIRST verified write (REVISION
     7(c)).  The writer -- init -- brings the era's TOKEN and the era's
     ghosts at FULL ownership, both out of the boot bundle the transport
     founded, and the step files them in the ledger against the token: a
     second adopter at [k] would need the same token, and the ledger keeps
     the one it consumed.  The port's claim is in its FOUNDED arm here (a
     PAIRED one would put [k] in the map already, which the token refutes),
     so no correlation between [app_boot] and the claim is needed anywhere.

     WHAT COMES BACK is the era's PIN -- persistent, and from here on the
     name by which the claim and every writer mean the same era -- with the
     cursor at one and the two bounds at the start. *)
  Lemma eout_step_write_adopt (k : nat) (v : era_pins) (b : bv 8)
      (ho hl : list mobs) (acc : list (bv 8)) :
    u_prologue !! 0%nat = Some b ->
    era_tok k -∗ era_full v -∗
    echo_led hl -∗ eout k ho acc ==∗
      echo_led hl ∗ eout k ho (acc ++ [b])
      ∗ ((era_pin k v ∗ turn v 1%nat ∗ cs_lb v [] ∗ E_lb v 0%nat) ∨ T).
  Proof.
    intros Hb. iIntros "Htok Hfull Hled Hcl".
    rewrite /echo_led. iDestruct "Hled" as "(Hcnt & Hera & Hphi)".
    iDestruct "Hcl" as "[#HT | Hcl]".
    { iModIntro. iFrame "Hcnt Hera Hphi".
      iSplitR; [by iApply eout_of_taint | by iRight]. }
    iDestruct "Hcl" as "[%Hfr | Hp]"; last first.
    { (* a PAIRED claim would mean [k] is already adopted, and the ledger
         then holds the token this writer is carrying *)
      iDestruct "Hp" as (v2 so2) "(#Hpin2 & _ & _)".
      iDestruct "Hera" as (Mp) "[Hm Hbig]".
      iDestruct (ghost_map_lookup with "Hm Hpin2") as %Hlk.
      iDestruct (big_sepM_lookup_acc _ _ k v2 Hlk with "Hbig")
        as "[[Htok' _] _]".
      iDestruct (era_tok_excl k with "Htok Htok'") as "[]". }
    subst acc.
    (* the era's ghosts, split into the ledger's slot and what comes back *)
    rewrite /era_full.
    iDestruct "Hfull" as "(Ho & Hi & Ht & Hcs & HE)".
    iMod (ghost_var_update (MkO [] [] [b]) with "Ho") as "Ho".
    iMod (ghost_var_update 1%nat with "Ht") as "Ht".
    rewrite /out_auth /out_frag /in_auth /in_frag /turn /turn_auth
            /cs_auth /E_auth.
    iEval (rewrite -Qp.half_half) in "Ho".
    iDestruct (ghost_var_split with "Ho") as "[Ho1 Ho2]".
    iEval (rewrite -Qp.half_half) in "Hi".
    iDestruct (ghost_var_split with "Hi") as "[Hi1 Hi2]".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct (ghost_var_split with "Ht") as "[Ht1 Ht2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (E_lb_get with "HE") as "[HE #HElb]".
    iMod (era_inv_insert k v (MkO [] [] [b]) istage0 1%nat
            with "Htok [Ho1 Hi1 Hi2 Ht1 Hcs HE] Hera") as "[#Hpin Hera]".
    { rewrite /era_slot /out_auth /in_auth /in_frag.
      cbn [o_cs o_E o_w length].
      iFrame "Ho1 Hi1 Hi2 Ht1 Hcs HE". iPureIntro. split_and!.
      - by rewrite /pcount /=.
      - reflexivity.
      - constructor.
      - apply (cs_len_ok_intro [] [] [b]); [by intros [Hw _] |].
        intros _. cbn [length]. by rewrite Nat.Div0.div_0_l. }
    iModIntro. iFrame "Hcnt Hera Hphi".
    iSplitL "Ho2".
    - iRight. iRight. iExists v, (MkO [] [] [b]).
      iFrame "Hpin Ho2". iPureIntro.
      rewrite /eout_pure. cbn [o_cs o_E o_w]. split_and!.
      + by rewrite D_nil.
      + rewrite pending_nil. apply (prefix_snoc_lookup [] _ b);
          [apply prefix_nil | exact Hb].
      + intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
      + intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
      + constructor.
      + constructor.
      + constructor.
      + cbn [length]. lia.
      + by left.
    - iLeft. iFrame "Hpin Ht2 Hcslb HElb".
  Qed.

  (* (R) THE READ.  [ws] is the window the read CONSUMED; [read_ok] is what
     [WpUart.read_link] hands over.  What it gives back: the pure prefix fact
     SH-LINE turns into the line, and -- for a reader that will go on to
     write, which is sh -- the era's pin and the two bounds (review S9),
     the stage one at the window's far end, which at a line boundary is the
     [17 q] the writer needs, and the CHOICE bound the block-first write
     asks for.

     THE EMPTY WINDOW HAS NO CREDENTIALS, and cannot: a read that consumed
     nothing may meet a claim still in its FOUNDED arm, which holds no
     ghost.  SH-LINE reads seventeen bytes, so it takes the third
     disjunct. *)
  Lemma ein_step_read (k : nat) (hi hl : list mobs) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) :
    read_ok pops dl ws ->
    echo_led hl -∗ ein k hi pops dl ==∗
      echo_led hl ∗ ein k hi pops (dl ++ ws)
      ∗ (T ∨ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
              ∗ (⌜ws = []⌝
                 ∨ ∃ (v : era_pins) (cs0 : list nat),
                     era_pin k v ∗ cs_lb v cs0
                     ∗ E_lb v (length (dl ++ ws))
                     ∗ ⌜((length (dl ++ ws)) `div` length echo_line
                         <= S (length cs0))%nat⌝)).
  Proof.
    intros Hread. iIntros "Hled Hcl".
    iDestruct "Hcl" as "[#HT | [%Hfr | Hp]]".
    - iModIntro. iFrame "Hled".
      iSplitR; [by iApply ein_of_taint | by iLeft].
    - (* FOUNDED: nothing has been echoed, so the window is empty *)
      destruct Hfr as (Hlog & Hdisc & Hstamp & Hech & Hdlnil).
      assert (Hws : ws = []).
      { destruct ws as [| p ws']; [done | exfalso].
        destruct Hread as (Hin & _).
        destruct (Hin p ltac:(apply elem_of_cons; by left))
          as (e & He & Hpe & Hech').
        assert (Hp : p ∈ echoed pops)
          by (rewrite -Hpe; by apply echoed_elem).
        rewrite Hech in Hp. by apply elem_of_nil in Hp. }
      subst ws. subst dl. rewrite app_nil_r.
      iModIntro. iFrame "Hled". iSplitR.
      + iRight. iLeft. iPureIntro. by rewrite /ein_fresh.
      + iRight. iSplit; [| iLeft; by iPureIntro].
        iPureIntro. apply prefix_nil.
    - (* PAIRED *)
      iDestruct "Hp" as (v si) "(#Hpin & Hfrag & %Hpure)".
      rewrite /echo_led. iDestruct "Hled" as "(Hcnt & Hera & Hphi)".
      iDestruct (era_inv_acc k v with "Hpin Hera")
        as (so si2 P) "[Hslot Hback]".
      rewrite /era_slot.
      iDestruct "Hslot" as
        "(Ho & Hi & Hoe & Hie & Hta & Hcs & HE & Hpures)".
      iDestruct (in_agree with "Hfrag Hi") as %Heqs. subst si2.
      iDestruct "Hpures" as "(%HP & %Htie & %Hcsb & %Hcsl)".
      destruct Hpure as (Hlog & Hdisc & Hstamp & Hdlp & Hno & Hseg).
      assert (Hnoer : forall e, e ∈ pops -> cons_erase (le_byte e) = false).
      { intros e He. eapply disc_seg_no_erase; [by apply Hdisc |].
        apply open_seg_ends_in. by apply (proj1 (proj1 Hlog e He)). }
      assert (Hpref : (dl ++ ws) `prefix_of` echoed pops)
        by (eapply read_window_prefix; [exact Hlog | exact Hread
                                       | exact Hnoer | exact Hdlp]).
      iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
      iDestruct (E_lb_get with "HE") as "[HE #HElb]".
      assert (Hlenle : (length (dl ++ ws) <= length (o_E so))%nat).
      { apply prefix_length in Hpref.
        assert (Hsl : length (echoed pops) = length (seg_of (echoed pops)))
          by (by rewrite seg_of_length).
        rewrite Hseg in Hsl. rewrite /stage_tie in Htie. rewrite -Htie. lia. }
      iAssert (E_lb v (length (dl ++ ws))) as "#HElb2".
      { rewrite /E_lb.
        iApply (mono_nat_lb_own_le (length (dl ++ ws)) with "HElb"). lia. }
      (* THE CHOICE BOUND the block-first write asks for *)
      assert (Hcsbnd : ((length (dl ++ ws)) `div` length echo_line
                        <= S (length (o_cs so)))%nat).
      { pose proof echo_line_length as HLL.
        assert (Hmono : ((length (dl ++ ws)) `div` length echo_line
                         <= length (o_E so) `div` length echo_line)%nat)
          by (apply Nat.Div0.div_le_mono; lia).
        destruct (cs_len_ok_inv so Hcsl) as [[_ Hq] | [_ Hq]]; lia. }
      iModIntro. iSplitR "Hfrag".
      + iFrame "Hcnt Hphi". iApply ("Hback" $! so si P).
        rewrite /era_slot. iFrame "Ho Hi Hoe Hie Hta Hcs HE".
        iPureIntro. by split_and!.
      + iSplitL "Hfrag".
        * iRight. iRight. iExists v, si. iFrame "Hpin Hfrag".
          iPureIntro. by split_and!.
        * iRight. iSplit; [by iPureIntro |]. iRight.
          iExists v, (o_cs so). iFrame "Hpin Hcslb HElb2".
          by iPureIntro.
  Qed.

  (* ...and the LINE, which is what SH-LINE reads off it. *)
  Lemma ein_read_line (k : nat) (si : istage) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (q : nat) :
    ein_pure k si pops dl ->
    E_byte (i_E si) ->
    (dl ++ ws) `prefix_of` echoed pops ->
    length dl = (length echo_line * q)%nat ->
    length ws = length echo_line ->
    snd <$> ws = echo_line.
  Proof.
    intros (_ & _ & _ & _ & _ & Hseg) HE Hp Hdl Hws.
    rewrite -(seg_of_snd ws).
    apply (read_window_line (i_E si) (seg_of dl) (seg_of ws) q).
    - exact HE.
    - rewrite -seg_of_app -Hseg. destruct Hp as [z Hz]. rewrite Hz.
      exists (seg_of z). by rewrite seg_of_app.
    - by rewrite seg_of_length.
    - by rewrite seg_of_length.
  Qed.

  (* (L) THE DRAIN ([App.Htx]).  The claim's own same-cycle facts are at its
     WITNESS [ho]; [App.Htx] supplies [ho `prefix_of` h] and the era stamp at
     [h], the claim carries the stamp at [ho], and
     [EchoOutPure.open_seg_prefix_boots] puts the two segments in one cycle.
     [EchoOutPure.good_out_of_stage] then turns the stage into [good_out].
     THE LEDGER IS NOT NEEDED HERE AT ALL. *)
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
    iDestruct "Hcl" as "[#HT | [%Hnil | Hp]]".
    - iSplitR; [iLeft; iExact "HT" | iLeft; iExact "HT"].
    - iSplitR.
      + iRight. iLeft. by iPureIntro.
      + iRight. iPureIntro.
        assert (Hw : obs_wire Uart0 seg = []).
        { rewrite Hnil in Hwire. by apply prefix_nil_inv in Hwire. }
        exists []. split; [constructor |].
        rewrite /sess Hw. apply prefix_nil.
    - iDestruct "Hp" as (v so) "(#Hpin & Hfrag & %Hpure)".
      pose proof Hpure as Hpure2.
      destruct Hpure2 as (Hacc & Hw & Hidx & Hbyte & Hcs' & Hdsc & Hpre1
                         & Hpre2 & Hpre3).
      iSplitL "Hfrag".
      { iRight. iRight. iExists v, so. iFrame "Hpin Hfrag".
        by iPureIntro. }
      iRight. iPureIntro.
      assert (Hlen : (length (o_E so) <= length (ins seg))%nat).
      { rewrite Hins. destruct Hpre3 as [HEnil | Hbo].
        - rewrite HEnil. cbn [length]. lia.
        - etrans; [exact Hpre2 |]. apply prefix_length, ins_prefix_of.
          apply open_seg_prefix_boots; [exact Hpre | by rewrite Hbo | exact Hsh]. }
      apply (good_out_of_stage (o_cs so) (o_E so) (o_w so) seg Hcs' Hbyte Hw).
      + rewrite -Hacc. exact Hwire.
      + exact Hlen.
  Qed.

End echo_out.
