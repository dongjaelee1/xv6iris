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

(* the OUTPUT claim's pure fact *)
Definition eout_pure (so : ostage) (acc : list (bv 8)) : Prop :=
  acc = D (o_cs so) (o_E so) ++ o_w so
  /\ o_w so `prefix_of` pending (o_cs so) (o_E so)
  /\ E_index (o_E so)
  /\ E_byte (o_E so)
  /\ Forall (fun i => (i < length line_alts)%nat) (o_cs so)
  /\ Forall (fun x => disc_seg x.1) (o_E so).

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

(* the cursor at zero pins the stage: [pending_n cs 0] is [u_prologue], which
   is not empty, so an echoed input already costs bytes *)
Lemma u_prologue_pos : (0 < length u_prologue)%nat.
Proof. vm_compute. lia. Qed.

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
Definition ein_fresh (pops : list log_entry)
    (dl : list (list mobs * bv 8)) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg (open_seg (le_hist e)))
  /\ echoed pops = []
  /\ dl = [].

(* the INPUT claim's pure fact *)
Definition ein_pure (si : istage) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg (open_seg (le_hist e)))
  /\ dl `prefix_of` echoed pops
  /\ seg_of (echoed pops)
     = (if i_owed si then removelast (i_E si) else i_E si).

(* ...and the LEDGER's tie between them: one [E], and the owed window is the
   only place the two may disagree. *)
Definition stage_tie (so : ostage) (si : istage) : Prop :=
  i_E si = o_E so.

Lemma epu_lookup_nil_absurd {A} (j : nat) (x : A) :
  ([] : list A) !! j = Some x -> False.
Proof. intros Hx. apply lookup_lt_Some in Hx. cbn in Hx. lia. Qed.

Lemma eout_pure_0 : eout_pure ostage0 [].
Proof.
  rewrite /eout_pure /ostage0. cbn [o_cs o_E o_w]. split_and!.
  - rewrite D_nil. done.
  - rewrite pending_nil. apply prefix_nil.
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
  - intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
  - constructor.
  - constructor.
Qed.

Lemma log_ok_nil : log_ok [].
Proof.
  split.
  - intros e He. by apply elem_of_nil in He.
  - intros i e1 e2 H1 H2. destruct (epu_lookup_nil_absurd i e1 H1).
Qed.

Lemma echoed_nil : echoed [] = [].
Proof. rewrite /echoed. by rewrite filter_nil. Qed.

Lemma ein_pure_0 : ein_pure istage0 [] [].
Proof.
  rewrite /ein_pure /istage0. cbn [i_E i_owed]. split_and!.
  - exact log_ok_nil.
  - intros e He. by apply elem_of_nil in He.
  - apply prefix_nil.
  - rewrite /seg_of echoed_nil. by rewrite fmap_nil.
Qed.

Lemma ein_fresh_0 : ein_fresh [] [].
Proof.
  rewrite /ein_fresh. split_and!.
  - exact log_ok_nil.
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
  eg_era   : gname;   (* mono_nat: the era counter, pinned to [obs_boots h] *)
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

  (* ...and the era counter, whose lower bound says "era k is over".  The
     ledger's counter is [obs_boots h], which the kernel's stamp pins to
     [S gen_id]. *)
  Definition era_closed (k : nat) : iProp Σ := mono_nat_lb_own (eg_era γ) (S k).
  Definition era_auth (k : nat) : iProp Σ := mono_nat_auth_own (eg_era γ) 1 k.

  Global Instance era_closed_persistent k : Persistent (era_closed k).
  Proof. rewrite /era_closed. apply _. Qed.
  Global Instance era_closed_timeless k : Timeless (era_closed k).
  Proof. rewrite /era_closed. apply _. Qed.
  Global Instance era_auth_timeless k : Timeless (era_auth k).
  Proof. rewrite /era_auth. apply _. Qed.

  Lemma era_closed_now k : era_auth k -∗ era_closed k -∗ False.
  Proof.
    rewrite /era_auth /era_closed. iIntros "Ha Hlb".
    iDestruct (mono_nat_lb_own_valid with "Ha Hlb") as %[_ Hle]. lia.
  Qed.

  Lemma era_closed_of_lt k k' : (k < k')%nat -> era_auth k' -∗ era_closed k.
  Proof.
    intros Hlt. rewrite /era_auth /era_closed. iIntros "Ha".
    iDestruct (mono_nat_lb_own_get with "Ha") as "#Hlb".
    iApply (mono_nat_lb_own_le (S k) with "Hlb"). lia.
  Qed.

  Lemma era_auth_grow k k' : (k <= k')%nat -> era_auth k ==∗ era_auth k'.
  Proof.
    intros Hle. rewrite /era_auth. iIntros "Ha".
    by iMod (mono_nat_own_update k' with "Ha") as "[$ _]".
  Qed.

  (* ====================================================================== *)
  (*  3.  THE TWO PORT CLAIMS, AT THE ERA NUMBER                            *)
  (* ====================================================================== *)

  Definition eout (k : nat) (ho : list mobs) (acc : list (bv 8)) : iProp Σ :=
    ( T
    ∨ ⌜acc = []⌝
    ∨ ∃ (v : era_pins) (so : ostage),
        era_pin k v ∗ out_frag v so ∗
        (era_closed k ∨ ⌜eout_pure so acc⌝))%I.

  Definition ein (k : nat) (ho : list mobs) (pops : list log_entry)
      (dl : list (list mobs * bv 8)) : iProp Σ :=
    ( T
    ∨ ⌜ein_fresh pops dl⌝
    ∨ ∃ (v : era_pins) (si : istage),
        era_pin k v ∗ in_frag v si ∗
        (era_closed k ∨ ⌜ein_pure si pops dl⌝))%I.

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
  Proof. rewrite /ein. iRight. iLeft. iPureIntro. exact ein_fresh_0. Qed.

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

  (* WHAT A DEAD ERA LEAVES BEHIND: its CURSOR's other half, and nothing
     else.  A link at a dead era's number re-establishes the claim through
     [era_closed], so the stage authorities are not needed -- but a write
     still has to hand its own cursor back, and this is where that era's
     half is. *)
  Definition era_dead (v : era_pins) : iProp Σ :=
    (∃ P : nat, turn_auth v P)%I.

  Global Instance era_dead_timeless v : Timeless (era_dead v).
  Proof. rewrite /era_dead. apply _. Qed.

  (* THE CURRENT ERA'S PAIRING, or [None] before this era's first link.  The
     era's number is the ledger's own [obs_boots h], which the kernel's stamp
     pins to [S gen_id].  [esc] is the input claim's half, held in escrow
     until ITS first link: the output claim always pairs first, because under
     the discipline the banner is on the wire before any input is accepted. *)
  (* THE TWO ESCROWS, and why their conditions are PURE.  Each port claim
     has a FOUNDED arm (which the transport must produce from nothing, so it
     cannot hold a ghost) and a PAIRED arm (which holds one half of the
     era's stage).  The ledger therefore has to be able to say WHICH arm the
     claim is in -- otherwise a step that meets the founded arm cannot
     produce the paired one, and a claim that dropped its half is
     indistinguishable from a founded one.  It can, because each claim
     leaves its founded arm at exactly one event, and that event is visible
     in the LEDGER's own stage:
       - the output claim leaves [acc = []] at the era's FIRST PROCESS BYTE,
         which is [P = 0 -> P = 1];
       - the input claim leaves [echoed pops = []] at the era's FIRST ECHO,
         which is [o_E so = [] -> o_E so = [x]].
     So the ledger holds the claim's half in escrow exactly while the
     condition holds, and hands it over in the step that breaks it.  The
     output escrow carries the era's TURN as well, because the first write
     is also where the writer's cursor is born. *)
  Definition era_live (v : era_pins) (so : ostage) (si : istage)
      (P : nat) (h : list mobs) : iProp Σ :=
    (out_auth v so ∗ in_auth v si
     ∗ (match P with
        | 0%nat => out_frag v so ∗ turn v P
        | S _ => True
        end)
     ∗ (match o_E so with
        | [] => in_frag v si
        | _ :: _ => True
        end)
     ∗ turn_auth v P
     ∗ cs_auth v (o_cs so)
     ∗ E_auth v (length (o_E so))
     ∗ ⌜P = pcount (o_cs so) (o_E so) (o_w so)⌝
     ∗ ⌜stage_tie so si⌝
     ∗ ⌜Forall (fun i => (i < length line_alts)%nat) (o_cs so)⌝
     (* THE SAME-CYCLE FACTS, GUARDED BY THE POWER STATE.  [open_seg] resets
        at a power event while the era's stage does not, so the guard is what
        lets a PowerOff leave the pairing in place: with the machine off the
        antecedent is false ([trace_shape_off]) and the conjunct says nothing.
        Every consumer -- the echo and the drain -- holds [trace_shape h true]
        anyway. *)
     ∗ ⌜trace_shape h true ->
          Forall (fun x => x.1 `prefix_of` open_seg h) (o_E so)
          /\ (length (o_E so) <= length (ins (open_seg h)))%nat⌝)%I.

  Global Instance era_live_timeless v so si P h :
    Timeless (era_live v so si P h).
  Proof.
    rewrite /era_live. destruct P; destruct (o_E so); apply _.
  Qed.

  Definition era_inv (h : list mobs) : iProp Σ :=
    (∃ (Mp : gmap nat era_pins) (cur : option era_pins),
       ghost_map_auth (eg_pin γ) 1 Mp
       ∗ era_auth (obs_boots h)
       ∗ ([∗ map] k ↦ v ∈ (match cur with
                           | None => Mp
                           | Some _ => delete (obs_boots h) Mp
                           end), era_dead v)
       ∗ ⌜forall k v, Mp !! k = Some v ->
            match cur with
            | Some _ => (k <= obs_boots h)%nat
            | None => (k < obs_boots h)%nat
            end⌝
       ∗ match cur with
         | None => True
         | Some v =>
             ⌜Mp !! obs_boots h = Some v⌝ ∗ era_pin (obs_boots h) v ∗
             ∃ so si P, era_live v so si P h
         end)%I.

  Global Instance era_inv_timeless h : Timeless (era_inv h).
  Proof.
    rewrite /era_inv. apply bi.exist_timeless. intros Mp.
    apply bi.exist_timeless. intros cur. destruct cur; apply _.
  Qed.

  (* ANTI-VACUITY (review S1): the paired state is INHABITED.  This is also
     the allocation half of the era's adoption. *)
  Lemma era_alloc (h : list mobs) :
    ⊢ |==> ∃ v : era_pins, era_live v ostage0 istage0 0%nat h.
  Proof.
    iMod (ghost_var_alloc ostage0) as (gso) "Ho".
    iMod (ghost_var_alloc istage0) as (gsi) "Hi".
    iMod (ghost_var_alloc 0%nat) as (go) "Ht".
    iMod (own_alloc (●ML ([] : list (leibnizO nat)))) as (gcs) "Hcs";
      [apply mono_list_auth_valid |].
    iMod (mono_nat_own_alloc 0%nat) as (gE) "[HE _]".
    set (v := MkPins gso gsi go gcs gE).
    iEval (rewrite -Qp.half_half) in "Ho".
    iDestruct (ghost_var_split with "Ho") as "[Ho1 Ho2]".
    iEval (rewrite -Qp.half_half) in "Hi".
    iDestruct (ghost_var_split with "Hi") as "[Hi1 Hi2]".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct (ghost_var_split with "Ht") as "[Ht1 Ht2]".
    iModIntro. iExists v. rewrite /era_live /out_auth /in_auth /in_frag
      /turn /turn_auth /cs_auth /E_auth /out_frag /=.
    iFrame "Ho1 Hi1 Hi2 Ht1 Ht2 Hcs HE Ho2".
    iPureIntro. split_and!.
    - reflexivity.
    - exact stage_tie_0.
    - constructor.
    - intros _. cbn [o_E ostage0]. split; [constructor | lia].
  Qed.

  (* ...and THE WHOLE LEDGER, which is what [AppEcho.echo_R] becomes. *)
  Definition echo_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint γ) 1 (if decide (disc h) then 0%nat else 1%nat)
     ∗ era_inv h
     ∗ (⌜Forall good_out (cycles_of h)⌝ ∨ T))%I.

  Global Instance echo_led_timeless h : Timeless (echo_led h).
  Proof. rewrite /echo_led. apply _. Qed.

  (* WHAT THE BIRTH STEP YIELDS, i.e. what [AppEcho.echo_cl] becomes:
     [AppEcho.echo_birth] is three [own_alloc]s and this. *)
  Lemma echo_led_init :
    mono_nat_auth_own (eg_taint γ) 1 0%nat -∗
    mono_nat_auth_own (eg_era γ) 1 0%nat -∗
    ghost_map_auth (eg_pin γ) 1 (∅ : gmap nat era_pins) -∗
    echo_led [].
  Proof.
    iIntros "Ht He Hm". rewrite /echo_led /era_inv /era_auth.
    rewrite decide_True; [| exact disc_nil].
    iFrame "Ht".
    iSplitL "He Hm".
    - iExists ∅, None. cbn [obs_boots]. iFrame "Hm He".
      rewrite big_sepM_empty.
      iSplit; [done |]. iSplit; [| done].
      iPureIntro. intros k v Hv. by rewrite lookup_empty in Hv.
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

  (* THE ERA MACHINE ACROSS AN I/O EVENT: [obs_boots] does not move, and only
     [era_live]'s two same-cycle facts mention the history -- both monotone
     in the open segment. *)
  Lemma era_inv_io (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> era_inv h -∗ era_inv (h ++ [e]).
  Proof.
    intros Hsh Hio. rewrite /era_inv. iIntros "H".
    iDestruct "H" as (Mp cur) "(Hm & Hk & Hdead & %Hdom & Hcur)".
    assert (Hb : obs_boots (h ++ [e]) = obs_boots h).
    { rewrite obs_boots_app (obs_boots_io [e] (io_singleton e Hio)). lia. }
    rewrite Hb. iExists Mp, cur. iFrame "Hm Hk Hdead".
    iSplit; [by iPureIntro |].
    destruct cur as [v |]; [| iExact "Hcur"].
    iDestruct "Hcur" as "(%Hge & #Hpin & Hlive)".
    iSplit; [by iPureIntro |]. iFrame "Hpin".
    iDestruct "Hlive" as (so si P) "Hlive". iExists so, si, P.
    rewrite /era_live.
    iDestruct "Hlive" as
      "(Ho & Hi & Hoe & Hie & Ht & Hcs & HE & %HP & %Htie & %Hcsb & %Hpre)".
    iFrame "Ho Hi Hoe Hie Ht Hcs HE".
    rewrite (open_seg_io h [e] (io_singleton e Hio)).
    destruct (Hpre Hsh) as [Hpre1 Hpre2].
    iPureIntro. split_and!; [exact HP | exact Htie | exact Hcsb |].
    intros _. split.
    - rewrite Forall_forall in Hpre1. rewrite Forall_forall.
      intros x Hx. destruct (Hpre1 x Hx) as [z Hz].
      exists (z ++ [e]). rewrite Hz. by rewrite app_assoc.
    - rewrite ins_app length_app. lia.
  Qed.

  (* THE POWER EVENTS.  A PowerOff leaves the pairing in place -- the era's
     stage is still the truth about [acc], and the guarded same-cycle
     conjunct goes vacuous with the machine off.  A PowerOn RETIRES it: the
     era number grows, the cursor's other half joins the dead ones, and the
     machine goes unpaired, which is what makes the next era's adoption an
     INSERT-IF-ABSENT at a strictly larger number.  That the number DOES grow
     at a PowerOn -- and hence that a dead era can never be adopted again --
     is the kernel's stamp [⌜obs_boots h = S gen_id⌝] read on this arm. *)
  Lemma era_inv_off (h : list mobs) :
    era_inv h -∗ era_inv (h ++ [ObsPowerOff]).
  Proof.
    rewrite /era_inv. iIntros "H".
    iDestruct "H" as (Mp cur) "(Hm & Hk & Hdead & %Hdom & Hcur)".
    assert (Hb : obs_boots (h ++ [ObsPowerOff]) = obs_boots h)
      by (rewrite obs_boots_app /=; lia).
    rewrite Hb. iExists Mp, cur. iFrame "Hm Hk Hdead".
    iSplit; [by iPureIntro |].
    destruct cur as [v |]; [| iExact "Hcur"].
    iDestruct "Hcur" as "(%Hge & #Hpin & Hlive)".
    iSplit; [by iPureIntro |]. iFrame "Hpin".
    iDestruct "Hlive" as (so si P) "Hlive". iExists so, si, P.
    rewrite /era_live.
    iDestruct "Hlive" as
      "(Ho & Hi & Hoe & Hie & Ht & Hcs & HE & %HP & %Htie & %Hcsb & _)".
    iFrame "Ho Hi Hoe Hie Ht Hcs HE". iPureIntro.
    split_and!; [exact HP | exact Htie | exact Hcsb |].
    intros Hsh. destruct (trace_shape_off h Hsh).
  Qed.

  Lemma era_inv_on (h : list mobs) :
    era_inv h ==∗ era_inv (h ++ [ObsPowerOn]).
  Proof.
    rewrite /era_inv. iIntros "H".
    iDestruct "H" as (Mp cur) "(Hm & Hk & Hdead & %Hdom & Hcur)".
    assert (Hb : obs_boots (h ++ [ObsPowerOn]) = S (obs_boots h))
      by (rewrite obs_boots_app /=; lia).
    iMod (era_auth_grow (obs_boots h) (obs_boots (h ++ [ObsPowerOn]))
            ltac:(lia) with "Hk") as "Hk".
    rewrite Hb.
    destruct cur as [v |].
    - iDestruct "Hcur" as "(%Hge & _ & Hlive)".
      iDestruct "Hlive" as (so si P) "Hlive". rewrite /era_live.
      iDestruct "Hlive" as "(_ & _ & _ & _ & Ht & _)".
      iModIntro. iExists Mp, None. iFrame "Hm Hk".
      iSplitL "Hdead Ht".
      + rewrite (big_sepM_delete _ Mp (obs_boots h) v Hge).
        iSplitL "Ht"; [by iExists P | iExact "Hdead"].
      + iSplit; [| done]. iPureIntro. intros k' v' Hv'.
        specialize (Hdom k' v' Hv'). lia.
    - iModIntro. iExists Mp, None. iFrame "Hm Hk Hdead".
      iSplit; [| done]. iPureIntro. intros k' v' Hv'.
      specialize (Hdom k' v' Hv'). lia.
  Qed.

  Lemma echo_led_pow (h : list mobs) (on : bool) :
    echo_led h ==∗ echo_led (h ++ [if on then ObsPowerOff else ObsPowerOn]).
  Proof.
    iIntros "(Ht & He & Hphi)". rewrite /echo_led.
    rewrite (decide_ext _ (disc h) 0%nat 1%nat (disc_power h on)).
    iFrame "Ht".
    destruct on.
    - iDestruct (era_inv_off h with "He") as "He". iModIntro. iFrame "He".
      rewrite cycles_of_off. iExact "Hphi".
    - iMod (era_inv_on h with "He") as "He". iModIntro. iFrame "He".
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
    iDestruct (era_inv_io h (ObsUartOut i b) Hsh eq_refl with "He") as "He".
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
    iDestruct (era_inv_io h (ObsUartIn i b) Hsh eq_refl with "He") as "He".
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

  (* (E) THE ECHO SHIFT's core step, at the STORE arm: the byte goes out and
     [i_owed] is raised; [ein_step_append] lowers it.  The cursor is
     UNTOUCHED ([pcount_echo]), which is what lets this close with the writer
     absent (review S2). *)
  Lemma eout_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho hi : list mobs) (acc : list (bv 8))
      (pops : list log_entry) (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` acc ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    echo_led h -∗ eout k ho acc -∗ ein k hi pops dl ==∗
      echo_led h ∗ eout k h (acc ++ [echo_of c]) ∗ ein k hi pops dl.
  Proof.
  Admitted.

  (* ...and the LOG's side, fired after the chain ([WpUart.in_append]). *)
  Lemma ein_step_append (k : nat) (h : list mobs) (c : bv 8)
      (cs : list (bv 8)) (hi : list mobs) (pops : list log_entry)
      (dl : list (list mobs * bv 8)) :
    disc h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    cons_echo c cs ->
    (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
    echo_led h -∗ ein k hi pops dl ==∗
      echo_led h ∗ ein k h (pops ++ [(h, c, cs)]) dl.
  Proof.
  Admitted.

  (* (W) THE WRITE.  What the writer brings: the era's pin, its cursor, a
     PERSISTENT lower bound of the line choices and one of the era's STAGE
     INDEX (review S9 and the coordinator's ruling of 2026-09-14), and the
     Coq-level fact that its byte is the [P]-th of the era's process stream
     up to stage [S n0].  What it gets back: the cursor advanced and the two
     bounds, so the next write is paid the same way.

     THE STRICTNESS IS NOT A PREMISE ANY MORE.  The first cut asked the
     writer for [length w < length (pending cs E)], which it cannot state --
     it does not know [w].  With [E_lb v n0] the ledger EXPOSES the stage
     index, and [write_stage_byte] derives both the stage ([length E = n0])
     and the strictness from [proc_upto cs0 (S n0) !! P = Some b] alone.

     [Hfresh] IS THE ONE THING THE LEDGER CANNOT SEE.  The output claim's
     FOUNDED arm ([acc = []]) is PURE -- it has to be, because
     [App.Happ_boot] mints it from nothing at every era -- so nothing in it
     distinguishes "this era has not written yet" from "this claim's half of
     the era's stage was dropped".  The ledger closes the first case with an
     escrow at [P = 0] (see [era_live]); the second is impossible in the
     tree and unprovable in the logic, and [Hfresh] -- "a fresh claim means a
     cursor at zero" -- is exactly its negation.  It is discharged outright
     at the era's first write and is owed by section 7's wrapper otherwise;
     see the handover. *)
  Lemma eout_step_write (k : nat) (v : era_pins) (P n0 : nat) (b : bv 8)
      (cs0 : list nat) (ho : list mobs) (acc : list (bv 8))
      (h : list mobs) :
    obs_boots h = k ->
    ((n0 `div` length echo_line) <= length cs0)%nat ->
    proc_upto cs0 (S n0) !! P = Some b ->
    (acc = [] -> P = 0%nat) ->
    era_pin k v -∗ turn v P -∗ cs_lb v cs0 -∗ E_lb v n0 -∗
    echo_led h -∗ eout k ho acc ==∗
      echo_led h ∗ eout k ho (acc ++ [b])
      ∗ ((turn v (S P) ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T).
  Proof.
    intros Hk Hdiv Hb Hfresh. subst k.
    iIntros "#Hpin Ht #Hcslb #HElb Hled Hcl".
    rewrite /echo_led. iDestruct "Hled" as "(Hcnt & Hera & Hphi)".
    rewrite /era_inv.
    iDestruct "Hera" as (Mp cur) "(Hm & Hka & Hdead & %Hdom & Hcur)".
    iDestruct (ghost_map_lookup with "Hm Hpin") as %Hlk.
    destruct cur as [v' |]; last first.
    { exfalso. specialize (Hdom _ _ Hlk). lia. }
    iDestruct "Hcur" as "(%Hge & #Hpin' & Hlive)".
    assert (Hvv : v' = v) by (rewrite Hlk in Hge; by injection Hge).
    subst v'.
    iDestruct "Hlive" as (so si Pl) "Hlive". rewrite /era_live.
    iDestruct "Hlive" as
      "(Ho & Hi & Hoe & Hie & Hta & Hcs & HE & Hpures)".
    iDestruct (turn_agree with "Ht Hta") as %Heqp. subst Pl.
    iDestruct "Hpures" as "(%HP & %Htie & %Hcsb & %Hpre)".
    (* the TAINT arm pays outright and moves nothing *)
    iDestruct "Hcl" as "[#HT | Hcl]".
    { iModIntro. iSplitR "".
      - iFrame "Hcnt Hphi". iExists Mp, (Some v). iFrame "Hm Hka Hdead".
        iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
        iFrame "Hpin". iExists so, si, P. rewrite /era_live.
        iFrame "Ho Hi Hoe Hie Hta Hcs HE". iPureIntro. by split_and!.
      - iSplitR; [by iApply eout_of_taint | by iRight]. }
    (* ...otherwise the era's own half of the stage comes out: from the
       claim if it is paired, and from the ledger's escrow if it is not *)
    iAssert (out_frag v so ∗ ⌜eout_pure so acc⌝ ∗ turn v P
             ∗ out_auth v so ∗ era_auth (obs_boots h))%I
      with "[Hcl Hoe Ht Ho Hka]" as "(Hfrag & %Hpure & Ht & Ho & Hka)".
    { destruct P as [| P'].
      - iDestruct "Hoe" as "[Hof Hto]".
        iDestruct "Hcl" as "[%Hfr | Hp]".
        + (* founded: the escrow is the claim's half, and the ledger's stage
             is at the start because the cursor is *)
          destruct (pcount_zero _ _ _ (eq_sym HP)) as [HEnil Hwnil].
          iFrame "Hof Ht Ho Hka". iPureIntro.
          rewrite /eout_pure HEnil Hwnil. split_and!.
          * by rewrite D_nil app_nil_r.
          * apply prefix_nil.
          * intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
          * intros j x Hx. destruct (epu_lookup_nil_absurd j x Hx).
          * exact Hcsb.
          * constructor.
        + iDestruct "Hp" as (v2 so2) "(#Hpin2 & Hfrag & Hrest)".
          iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
          iDestruct (out_agree with "Hfrag Ho") as %<-.
          iDestruct "Hrest" as "[#Hclo | %Hpure]".
          { iDestruct (era_closed_now with "Hka Hclo") as "[]". }
          iFrame "Hfrag Ht Ho Hka". by iPureIntro.
      - iDestruct "Hcl" as "[%Hfr | Hp]".
        + exfalso. specialize (Hfresh Hfr). lia.
        + iDestruct "Hp" as (v2 so2) "(#Hpin2 & Hfrag & Hrest)".
          iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
          iDestruct (out_agree with "Hfrag Ho") as %<-.
          iDestruct "Hrest" as "[#Hclo | %Hpure]".
          { iDestruct (era_closed_now with "Hka Hclo") as "[]". }
          iFrame "Hfrag Ht Ho Hka". by iPureIntro. }
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hcsb' & Hdsc).
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (E_lb_le with "HE HElb") as %Hn0.
    destruct (write_stage_byte cs0 (o_cs so) (o_E so) (o_w so) n0 P b
                Hcsp Hdiv Hn0 HP Hb) as [HlenE Hnext].
    iMod (out_update v so so (MkO (o_cs so) (o_E so) (o_w so ++ [b]))
            with "Hfrag Ho") as "[Hfrag Ho]".
    iMod (turn_update v P P (S P) with "Ht Hta") as "[Ht Hta]".
    iModIntro.
    iSplitR "Hfrag Ht".
    - iFrame "Hcnt Hphi". iExists Mp, (Some v). iFrame "Hm Hka Hdead".
      iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
      iFrame "Hpin". iExists (MkO (o_cs so) (o_E so) (o_w so ++ [b])), si, (S P).
      rewrite /era_live. cbn [o_cs o_E o_w].
      iFrame "Ho Hi Hie Hta Hcs HE".
      iPureIntro. split_and!; [| exact Htie | exact Hcsb | exact Hpre].
      rewrite pcount_write. by rewrite HP.
    - iSplitL "Hfrag".
      + iRight. iRight.
        iExists v, (MkO (o_cs so) (o_E so) (o_w so ++ [b])).
        iFrame "Hpin Hfrag". iRight. iPureIntro.
        rewrite /eout_pure. cbn [o_cs o_E o_w]. split_and!.
        * by rewrite Hacc app_assoc.
        * by apply prefix_snoc_lookup.
        * exact Hidx.
        * exact Hbyte.
        * exact Hcsb'.
        * exact Hdsc.
      + iLeft. iFrame "Ht Hcslb HElb".
  Qed.

  (* (R) THE READ.  [ws] is the window the read CONSUMED; [read_ok] is what
     [WpUart.read_link] hands over.  What it gives the program (review S9):
     the pure prefix fact SH-LINE turns into the line, and the era's pin and
     choice lower bound, which is what a reader that will later write needs. *)
  Lemma ein_step_read (k : nat) (hi : list mobs) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (h : list mobs) :
    read_ok pops dl ws ->
    echo_led h -∗ ein k hi pops dl ==∗
      echo_led h ∗ ein k hi pops (dl ++ ws)
      ∗ (T ∨ ∃ (v : era_pins) (cs0 : list nat),
             ⌜(dl ++ ws) `prefix_of` echoed pops⌝ ∗ era_pin k v ∗ cs_lb v cs0).
  Proof.
  Admitted.

  (* ...and the LINE, which is what SH-LINE reads off it. *)
  Lemma ein_read_line (si : istage) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (q : nat) :
    ein_pure si pops dl ->
    i_owed si = false ->
    E_byte (i_E si) ->
    (dl ++ ws) `prefix_of` echoed pops ->
    length dl = (length echo_line * q)%nat ->
    length ws = length echo_line ->
    snd <$> ws = echo_line.
  Proof.
    intros (_ & _ & _ & Hseg) Hno HE Hp Hdl Hws.
    rewrite Hno in Hseg.
    rewrite -(seg_of_snd ws).
    apply (read_window_line (i_E si) (seg_of dl) (seg_of ws) q).
    - exact HE.
    - rewrite -seg_of_app -Hseg. destruct Hp as [z Hz]. rewrite Hz.
      exists (seg_of z). by rewrite seg_of_app.
    - by rewrite seg_of_length.
    - by rewrite seg_of_length.
  Qed.

  (* (L) THE LEDGER STEP AT THE DRAIN ([App.Htx]).  [obs_boots h = k] is the
     kernel's stamp, so the claim is the CURRENT era's by the index and the
     ledger's pin at [k] is the current pairing -- no history comparison, no
     currency token.  [EchoOutPure.good_out_of_stage] then turns the stage
     into [good_out], with the same-cycle side condition read off
     [era_live]'s two pure conjuncts. *)
  Lemma echo_led_drain (k : nat) (h : list mobs) (ho : list mobs)
      (acc : list (bv 8)) (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` acc ->
    echo_led h -∗ eout k ho acc -∗
      echo_led h ∗ eout k ho acc ∗ (T ∨ ⌜good_out seg⌝).
  Proof.
    intros Hsh Hk Hins Hwire. subst k. iIntros "Hled Hcl".
    rewrite /eout.
    iDestruct "Hcl" as "[#HT | [%Hnil | Hp]]".
    - iFrame "Hled". iSplitR; [iLeft; iExact "HT" | iLeft; iExact "HT"].
    - iFrame "Hled". iSplitR.
      + iRight. iLeft. by iPureIntro.
      + iRight. iPureIntro.
        assert (Hw : obs_wire Uart0 seg = []).
        { rewrite Hnil in Hwire. by apply prefix_nil_inv in Hwire. }
        exists []. split; [constructor |].
        rewrite /sess Hw. apply prefix_nil.
    - iDestruct "Hp" as (v so) "(#Hpin & Hfrag & Hrest)".
      rewrite /echo_led. iDestruct "Hled" as "(Hcnt & Hera & Hphi)".
      rewrite /era_inv.
      iDestruct "Hera" as (Mp cur) "(Hm & Hka & Hdead & %Hdom & Hcur)".
      iDestruct (ghost_map_lookup with "Hm Hpin") as %Hlk.
      destruct cur as [v' |]; last first.
      { exfalso. specialize (Hdom _ _ Hlk). lia. }
      iDestruct "Hcur" as "(%Hge & #Hpin' & Hlive)".
      iDestruct "Hlive" as (so' si P) "Hlive".
      rewrite /era_live.
      iDestruct "Hlive" as
        "(Ho & Hi & Hoe & Hie & Ht & Hcs & HE & %HP & %Htie & %Hcsb & %Hpre)".
      assert (Hvv : v = v') by (rewrite Hlk in Hge; by injection Hge).
      subst v'.
      iDestruct (out_agree with "Hfrag Ho") as %<-.
      iAssert (⌜eout_pure so acc⌝)%I with "[Hrest Hka]" as "%Hpure".
      { iDestruct "Hrest" as "[#Hcl | $]".
        iDestruct (era_closed_now with "Hka Hcl") as "[]". }
      destruct Hpure as (Hacc & Hw & Hidx & Hbyte & Hcs' & Hdsc).
      destruct (Hpre Hsh) as [_ Hlen].
      iSplitL "Hcnt Hm Hka Hdead Ho Hi Hoe Hie Ht Hcs HE Hphi".
      { iFrame "Hcnt Hphi". iExists Mp, (Some v). iFrame "Hm Hka Hdead".
        iSplit; [by iPureIntro |]. iSplit; [by iPureIntro |].
        iFrame "Hpin". iExists so, si, P. rewrite /era_live.
        iFrame "Ho Hi Hoe Hie Ht Hcs HE". iPureIntro. split_and!;
          [exact HP | exact Htie | exact Hcsb | exact Hpre]. }
      iSplitL "Hfrag".
      { iRight. iRight. iExists v, so. iFrame "Hpin Hfrag". iRight.
        iPureIntro. by split_and!. }
      iRight. iPureIntro.
      apply (good_out_of_stage (o_cs so) (o_E so) (o_w so) seg Hcs' Hbyte Hw).
      + rewrite -Hacc. exact Hwire.
      + rewrite Hins. exact Hlen.
  Qed.

End echo_out.
