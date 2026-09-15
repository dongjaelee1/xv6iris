(* EchoOutPure.v -- THE PURE HALF OF E5's APPLICATION CLAIM.

   Design of record: claude-notes/projects/app-echo.md, "E5 -- THE CONSOLE
   I/O CLAIM: DESIGN OF RECORD" (the claim's pure conjuncts and the three
   arguments (E), (R), (W)).  This file is Iris-free list algebra over
   [EchoDisc] and [ConsLog], so that the Iris lane (ECHO-OUT) only has to
   APPLY lemmas.

   THE STAGE MACHINE.  The claim's data is the list [E] of ECHOED inputs:
   [E]'s j-th entry is the pair (history, byte) of input j+1, and the
   kernel put [echo_of c] on the wire for it.  The console's accepted
   bytes are then

     acc = D cs E ++ w      with   w `prefix_of` pending cs E

   where [D cs E] is the transcript DUE after E's last echo and
   [pending cs E] is the PROCESS output owed at that stage (init's banner
   and sh's first prompt before any input; the completed line's
   continuation at a line boundary; nothing mid-line -- mid-line a process
   byte is forbidden outright, which is what makes the discipline's rate
   bound bite).  [cs] resolves the per-line alternatives, exactly as in
   [EchoDisc.sess_n].

   THE FOUR FACTS, in the order the Iris claim spends them:
     F1  the stage is below the session   ([D_pending_sess], [D_stage_prefix])
     F2  the next echo is the next input  ([D2_next_input])
     F3  the read window is a slice of E  ([read_window_prefix],
                                           [read_window_line])
     F4  PHI's pure part                  ([good_out_of_stage]) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import EchoDisc.
Require Import ConsLog.
(* as in EchoDisc: a pure file does not inherit ssreflect's [rewrite] from
   the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  TWO BORROWED LEMMAS                                                *)
(*                                                                        *)
(*  The periodicity lemmas this file reads ([star_prefix_lookup] and its   *)
(*  two steps) are [EchoDisc]'s since lane ECHO-PURE moved them there.     *)
(*  What is still borrowed is the cycle a history's last input lives in:   *)
(*  it is an [ObsTrace]-level fact and belongs there, but the only copy    *)
(*  today is [UkSh]'s, far above this file.                               *)
(* ====================================================================== *)

(* ...and the cycle a history's last input lives in, copied from
   [UkSh.ush_cycles_snoc_in] for the same reason (that file is above this
   one; the fact is [ObsTrace]'s and belongs there). *)
Lemma epu_elem_of_rev_head {A} (x : A) (l : list A) : x ∈ rev (x :: l).
Proof. cbn. apply elem_of_app. right. by apply elem_of_list_singleton. Qed.

Lemma epu_cycles_snoc_in (h : list mobs) (b : bv 8) :
  exists s0 : list mobs,
    (s0 ++ [ObsUartIn Uart0 b])%list ∈ cycles_of (h ++ [ObsUartIn Uart0 b])%list.
Proof.
  rewrite /cycles_of cycles_rev_app.
  destruct (cycles_rev h) as [| c cs] eqn:Hc.
  - exists []. exact (epu_elem_of_rev_head ([] ++ [ObsUartIn Uart0 b])%list []).
  - exists c. exact (epu_elem_of_rev_head (c ++ [ObsUartIn Uart0 b])%list cs).
Qed.

(* ====================================================================== *)
(*  1.  THE BYTES OF THE LINE                                              *)
(* ====================================================================== *)

(* [echo_of] is the identity off '\r' *)
Lemma echo_of_other (c : bv 8) :
  c <> (mword_of_int 13 : mword 8) -> echo_of c = c.
Proof.
  intro Hne. rewrite /echo_of.
  destruct (eq_vec (c : mword 8) (mword_of_int 13 : mword 8)) eqn:He;
    [ | reflexivity ].
  exfalso. apply Hne. by apply eq_vec_true_iff in He.
Qed.

(* [echo_line] ends in '\n', not '\r', and holds neither '\r', nor any of
   the three erase bytes, nor ^D: decided at the literal, seventeen bytes.
   The third clause is what refutes the READ PATH'S SWALLOW arm (a leading
   ^D pops a byte and delivers nothing); the erase clause refutes the gap
   clause's erase disjunct. *)
(* a byte is not a given one when its NUMBER is not -- the step that lets
   every refutation below be [lia] against [echo_line_byte_val] *)
Local Lemma echo_byte_ne (c : bv 8) (z : Z) :
  bv_unsigned c <> z ->
  bv_unsigned (mword_of_int z : mword 8) = z ->
  eq_vec (c : mword 8) (mword_of_int z : mword 8) = false.
Proof.
  intros Hne Hz. apply eq_vec_false_iff. intro Hq.
  apply (f_equal bv_unsigned) in Hq. rewrite Hz in Hq. exact (Hne Hq).
Qed.

Lemma echo_line_bytes_ok (c : bv 8) :
  c ∈ echo_line ->
  c <> (mword_of_int 13 : mword 8) /\ cons_erase c = false
  /\ bv_unsigned c <> 4%Z.
Proof.
  intro Hc. pose proof (echo_line_byte_val c Hc) as Hv.
  split_and!.
  - intro Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
      [lia | by vm_compute].
  - rewrite /cons_erase.
    rewrite (echo_byte_ne c 21 ltac:(lia) ltac:(by vm_compute)).
    rewrite (echo_byte_ne c 8 ltac:(lia) ltac:(by vm_compute)).
    rewrite (echo_byte_ne c 127 ltac:(lia) ltac:(by vm_compute)).
    reflexivity.
  - lia.
Qed.

(* THE ECHO OF A LINE BYTE IS THE BYTE ITSELF -- which is why [D]'s
   [echo_of c] and [sess_n]'s [echo_line] byte are the same thing. *)
Lemma echo_of_echo_line (c : bv 8) : c ∈ echo_line -> echo_of c = c.
Proof. intro Hc. apply echo_of_other, (echo_line_bytes_ok c Hc). Qed.

Lemma cons_erase_echo_line (c : bv 8) : c ∈ echo_line -> cons_erase c = false.
Proof. intro Hc. apply (echo_line_bytes_ok c Hc). Qed.

Lemma no_ctrl_d_echo_line (c : bv 8) : c ∈ echo_line -> bv_unsigned c <> 4%Z.
Proof. intro Hc. apply (echo_line_bytes_ok c Hc). Qed.

(* THE BYTE A DISCIPLINED HISTORY ENDS IN is the line byte its POSITION
   calls for -- D3 read at one index. *)
Lemma disc_seg_last_byte (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c ->
  c = echo_line !!! ((length (ins h) - 1) `mod` length echo_line).
Proof.
  intros Hd [h0 ->].
  rewrite /disc_seg ins_app ins_in in Hd. rewrite ins_app ins_in.
  set (k := length (ins h0)).
  assert (Hlk : (ins h0 ++ [c]) !! k = Some c).
  { by rewrite lookup_app_r ?Nat.sub_diag. }
  assert (Hlt : k < length (ins h0 ++ [c]))
    by (rewrite length_app /=; lia).
  pose proof (star_prefix_lookup echo_line (ins h0 ++ [c]) k Hd
                echo_line_pos Hlt) as Hp.
  rewrite Hlk in Hp. rewrite length_app /= Nat.add_sub.
  assert (Hr : k `mod` length echo_line < length echo_line)
    by (apply Nat.mod_upper_bound; pose proof echo_line_pos; lia).
  rewrite (list_lookup_total_alt echo_line) -Hp //.
Qed.

Lemma disc_seg_in_echo_line (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> c ∈ echo_line.
Proof.
  intros Hd He. rewrite (disc_seg_last_byte h c Hd He).
  apply elem_of_list_lookup_2 with ((length (ins h) - 1) `mod` length echo_line).
  rewrite -list_lookup_lookup_total_lt //.
  apply Nat.mod_upper_bound. pose proof echo_line_pos. lia.
Qed.

(* the refutation the read contract's erase disjunct needs *)
Lemma disc_seg_no_erase (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> cons_erase c = false.
Proof.
  intros Hd He. apply cons_erase_echo_line, (disc_seg_in_echo_line h c Hd He).
Qed.

(* ...and the same for the read path's SWALLOW arm.  The kernel tests
   [cons_xlate b] against 0x04 and [cons_xlate] is the identity off '\r'
   ([UkSh.disc_no_ctrl_d] is that bridge); this is its pure half, which is
   all a file below ConsoleInv can say. *)
Lemma disc_seg_no_ctrl_d (h : list mobs) (c : bv 8) :
  disc_seg h -> obs_ends_in Uart0 h c -> bv_unsigned c <> 4%Z.
Proof.
  intros Hd He. apply no_ctrl_d_echo_line, (disc_seg_in_echo_line h c Hd He).
Qed.

Lemma disc_no_erase (h : list mobs) (c : bv 8) :
  disc h -> obs_ends_in Uart0 h c -> cons_erase c = false.
Proof.
  intros Hdisc [h0 ->].
  destruct (epu_cycles_snoc_in h0 c) as (s0 & Hin).
  apply elem_of_list_lookup in Hin as [i Hi].
  pose proof (disc_seg'_proj _ (Forall_lookup_1 _ _ _ _ Hdisc Hi)) as Hseg.
  eapply disc_seg_no_erase; [exact Hseg | apply obs_ends_in_snoc].
Qed.

(* THE OPEN CYCLE OF A DISCIPLINED HISTORY KEEPS D3 -- the one step from
   the whole-history discipline to the segment the claim is stated over. *)
Lemma disc_seg_open_seg (h : list mobs) :
  trace_shape h true -> disc h -> disc_seg (open_seg h).
Proof.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply elem_of_list_lookup in Hin as [i Hi].
  exact (disc_seg'_proj _ (Forall_lookup_1 _ _ _ _ Hd Hi)).
Qed.

(* ...AND THE BYTE COMES WITH IT.  Lane ECHO-OUT stores E's histories as
   CYCLE SEGMENTS (the discipline, [good_out] and [acc] are all per power
   cycle, so [E_index]'s [ins] must count the cycle's inputs and not the
   run's), and this is what turns the shift's [obs_ends_in] at the whole
   history into the one at the segment. *)
Lemma open_seg_ends_in (h : list mobs) (c : bv 8) :
  obs_ends_in Uart0 h c -> obs_ends_in Uart0 (open_seg h) c.
Proof.
  intros [h0 ->].
  rewrite (open_seg_io h0 [ObsUartIn Uart0 c]); [| by repeat constructor].
  apply obs_ends_in_snoc.
Qed.

(* ====================================================================== *)
(*  2.  THE STAGE MACHINE: [pending] AND [D]                               *)
(* ====================================================================== *)

(* THE PROCESS OUTPUT OWED AFTER [n] ECHOED INPUTS.  Before any input it is
   init's banner and sh's first prompt ([u_prologue]); after the '\n' echo
   that completes line [q] it is that line's continuation, indexed exactly
   as [EchoDisc.alt_blk] indexes it ([line_alts !!! (cs !!! (q-1))], with
   [q = n / 17]); mid-line it is nothing.  It reads only [n], because
   [sess_n] does. *)
Definition pending_n (ps cs : list nat) (n : nat) : list (bv 8) :=
  if decide (n = 0) then pro_of ps
  else if decide (n `mod` length echo_line = 0)
       then alt_cont ps cs (n `div` length echo_line - 1)
       else [].

Definition pending (ps cs : list nat) (E : list (list mobs * bv 8))
  : list (bv 8) := pending_n ps cs (length E).

(* THE TRANSCRIPT DUE AFTER E's LAST ECHO.  The note's law is a RIGHT
   append ([D cs (E ++ [(h,c)]) = D cs E ++ pending cs E ++ [echo_of c]]),
   but a [Fixpoint] on the right does not reduce under [cbn] on an opaque
   tail and a [Fixpoint] on [length E] cannot see the bytes.  So the
   definition is structural on [E] FROM THE LEFT with the stage index as an
   accumulator: [cbn] reduces it on every [x :: E'], and the note's law is
   [D_app] below, one line off [D_from_app]. *)
Fixpoint D_from (ps cs : list nat) (k : nat) (E : list (list mobs * bv 8))
  : list (bv 8) :=
  match E with
  | [] => []
  | x :: E' => pending_n ps cs k ++ [echo_of x.2] ++ D_from ps cs (S k) E'
  end.

Definition D (ps cs : list nat) (E : list (list mobs * bv 8)) : list (bv 8) :=
  D_from ps cs 0 E.

Lemma D_nil ps cs : D ps cs [] = [].
Proof. reflexivity. Qed.

Lemma pending_nil ps cs : pending ps cs [] = pro_of ps.
Proof. reflexivity. Qed.

(* the two extension laws the stage spends: a block STRICTLY BELOW the
   current stage reads a round that has settled, so a lower bound of [ps]
   already determines it. *)
Lemma pending_n_ps_ext ps ps' cs k :
  ps `prefix_of` ps' ->
  (pro_idx cs (k `div` length echo_line) < pro_rounds ps)%nat ->
  pending_n ps cs k = pending_n ps' cs k.
Proof.
  intros Hp Hr. rewrite /pending_n. case_decide as H0.
  { subst k. apply (pro_of_from_done_ext 0%nat); [exact Hp |].
    move: Hr. by rewrite Nat.Div0.div_0_l. }
  case_decide as Hm; [| done].
  rewrite /alt_cont. f_equal. case_decide as H3; [| done].
  pose proof echo_line_pos as HL.
  assert (Hq : (1 <= k `div` length echo_line)%nat).
  { destruct (decide (k `div` length echo_line = 0)%nat) as [Hd | Hd]; [| lia].
    exfalso. pose proof (Nat.div_mod_eq k (length echo_line)) as Hdm.
    rewrite Hd Hm in Hdm. lia. }
  assert (Hs : S (pro_idx cs (k `div` length echo_line - 1))
               = pro_idx cs (k `div` length echo_line)).
  { replace (k `div` length echo_line)%nat
      with (S (k `div` length echo_line - 1))%nat at 2 by lia.
    symmetry. apply pro_idx_S3.
    replace (S (k `div` length echo_line - 1) - 1)%nat
      with (k `div` length echo_line - 1)%nat by lia.
    exact H3. }
  rewrite Hs. by apply pro_of_from_done_ext.
Qed.

Lemma pending_n_ps_mono ps ps' cs k :
  ps `prefix_of` ps' -> pending_n ps cs k `prefix_of` pending_n ps' cs k.
Proof.
  intros Hp. rewrite /pending_n. case_decide as H0.
  { by apply pro_of_mono. }
  case_decide as Hm; [| reflexivity].
  rewrite /alt_cont. apply prefix_app. case_decide as H3; [| reflexivity].
  by apply pro_of_from_mono.
Qed.

(* THE ROUND-OPENING BLOCK'S SHAPE.  A block that OPENS a prologue round --
   the head of the transcript ([n = 0]), or a line whose continuation was
   the shell's own fork panic ([line_alts !!! 3]) -- owes the panic line, if
   any, and then THAT ROUND'S PROLOGUE.  Every OTHER block owes no prologue
   at all, which is why the round-opening disjunction is a premise and not
   decoration: without it the equation below is simply false. *)
Lemma pending_n_round_pre (ps cs : list nat) (n : nat) :
  (n `mod` length echo_line)%nat = 0%nat ->
  (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
  pending_n ps cs n
  = (if decide (n = 0%nat) then [] else line_alts !!! 3%nat)
    ++ pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps).
Proof.
  intros Hm Hopen. rewrite /pending_n. case_decide as H0.
  - subst n. rewrite Nat.Div0.div_0_l. by cbn [pro_idx pro_from app].
  - rewrite decide_True; [| exact Hm].
    assert (H3 : cs !!! (n `div` length echo_line - 1)%nat = 3%nat).
    { destruct Hopen as [Hn | H3]; [by destruct (H0 Hn) | exact H3]. }
    pose proof echo_line_pos as HL.
    assert (Hq : (1 <= n `div` length echo_line)%nat).
    { destruct (decide (n `div` length echo_line = 0)%nat) as [Hd | Hd]; [| lia].
      exfalso. pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm.
      rewrite Hd Hm in Hdm. lia. }
    assert (Hs : S (pro_idx cs (n `div` length echo_line - 1))
                 = pro_idx cs (n `div` length echo_line)).
    { replace (n `div` length echo_line)%nat
        with (S (n `div` length echo_line - 1))%nat at 2 by lia.
      symmetry. apply pro_idx_S3.
      replace (S (n `div` length echo_line - 1) - 1)%nat
        with (n `div` length echo_line - 1)%nat by lia.
      exact H3. }
    rewrite /alt_cont H3 Hs. reflexivity.
Qed.

(* A ROUND-OPENING BLOCK STANDS AT A ROUND THE STAGE HAS ALREADY REACHED:
   the block below it is settled ([pro_pin]) and this one is the next, so
   the round's index never runs past what the resolution has resolved.  This
   is the LOWER bound on [pro_rounds] the prologue-choice write pairs with
   the upper bound its own [~ pro_done] gives. *)
Lemma pro_pin_round_le (ps cs : list nat) (n : nat) :
  (n `mod` length echo_line)%nat = 0%nat ->
  (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
  pro_pin ps cs n ->
  (pro_idx cs (n `div` length echo_line) <= pro_rounds ps)%nat.
Proof.
  pose proof echo_line_pos as HL. intros Hm Ho Hpin.
  destruct (decide (n = 0%nat)) as [-> | Hn0].
  { rewrite Nat.Div0.div_0_l. cbn [pro_idx]. lia. }
  assert (H3 : cs !!! (n `div` length echo_line - 1)%nat = 3%nat).
  { destruct Ho as [Hz | H3]; [by destruct (Hn0 Hz) | exact H3]. }
  assert (Hq : (1 <= n `div` length echo_line)%nat).
  { destruct (decide (n `div` length echo_line = 0)%nat) as [Hd | Hd]; [| lia].
    exfalso. pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm.
    rewrite Hd Hm in Hdm. lia. }
  assert (Hs : S (pro_idx cs (n `div` length echo_line - 1))
               = pro_idx cs (n `div` length echo_line)).
  { replace (n `div` length echo_line)%nat
      with (S (n `div` length echo_line - 1))%nat at 2 by lia.
    symmetry. apply pro_idx_S3.
    replace (S (n `div` length echo_line - 1) - 1)%nat
      with (n `div` length echo_line - 1)%nat by lia.
    exact H3. }
  rewrite -Hs.
  assert (Hlt : (length echo_line * (n `div` length echo_line - 1) < n)%nat).
  { pose proof (Nat.div_mod_eq n (length echo_line)) as Hdm.
    rewrite Hm Nat.add_0_r in Hdm. nia. }
  pose proof (Hpin (n `div` length echo_line - 1)%nat Hlt). lia.
Qed.

(* ...so two resolutions that owe the SAME round-opening block agree on that
   round's prologue.  This is the fact the prologue-choice write reconciles
   its own [ps0] against the claim's authority with. *)
Lemma pending_n_round_det (ps ps' cs : list nat) (n : nat) :
  (n `mod` length echo_line)%nat = 0%nat ->
  (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
  pending_n ps cs n = pending_n ps' cs n ->
  pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps)
  = pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps').
Proof.
  intros Hm Hopen Heq.
  rewrite (pending_n_round_pre ps cs n Hm Hopen) in Heq.
  rewrite (pending_n_round_pre ps' cs n Hm Hopen) in Heq.
  by apply app_inv_head in Heq.
Qed.

Lemma D_from_pending_ext ps ps' cs k E :
  (forall j, (k <= j)%nat -> (j < k + length E)%nat ->
     pending_n ps cs j = pending_n ps' cs j) ->
  D_from ps cs k E = D_from ps' cs k E.
Proof.
  revert k. induction E as [| x E IH]; intros k Hj; [done |].
  cbn [D_from length]. rewrite (Hj k ltac:(lia) ltac:(cbn [length]; lia)).
  f_equal. f_equal. apply IH. intros j H1 H2. apply Hj; cbn [length]; lia.
Qed.

Lemma D_ps_ext ps ps' cs E :
  ps `prefix_of` ps' -> pro_pin ps cs (length E) -> D ps cs E = D ps' cs E.
Proof.
  intros Hp Hpin. rewrite /D. apply D_from_pending_ext.
  intros j _ Hj. apply (pending_n_ps_ext ps ps' cs j Hp).
  apply (pro_pin_at ps cs (length E) j Hpin). lia.
Qed.

Lemma D_from_app ps cs k E1 E2 :
  D_from ps cs k (E1 ++ E2)
  = D_from ps cs k E1 ++ D_from ps cs (k + length E1) E2.
Proof.
  revert k. induction E1 as [|x E1 IH]; intros k; cbn.
  - by rewrite Nat.add_0_r.
  - rewrite IH -!app_assoc.
    replace (S k + length E1) with (k + S (length E1)) by lia.
    reflexivity.
Qed.

(* THE NOTE'S LAW, verbatim *)
Lemma D_app ps cs E x :
  D ps cs (E ++ [x]) = D ps cs E ++ pending ps cs E ++ [echo_of x.2].
Proof.
  rewrite /D /pending D_from_app /=. by rewrite ?app_nil_r.
Qed.

(* ====================================================================== *)
(*  3.  WHAT THE CLAIM SAYS ABOUT [E]                                      *)
(* ====================================================================== *)

(* E's INDEX LAW, as the design states it: E's j-th entry is input j+1, and
   its byte is the one its history ends in. *)
Definition E_index (E : list (list mobs * bv 8)) : Prop :=
  forall (j : nat) (x : list mobs * bv 8),
    E !! j = Some x -> obs_ends_in Uart0 x.1 x.2 /\ length (ins x.1) = S j.

(* E's CONTENT LAW: E's j-th byte is the line byte position j calls for.
   THIS IS THE HYPOTHESIS F1 TURNS ON and the note does not list it: [D]
   records the bytes actually echoed and [sess_n] records [echo_line]'s, so
   without it [D cs E] and [sess_n cs (length E)] are unrelated.  It is not
   a new assumption -- it is D3 read at one index ([E_byte_of_disc]) -- but
   it has to be NAMED, because F1 is stated at stages where the discipline
   itself is not in scope. *)
Definition E_byte (E : list (list mobs * bv 8)) : Prop :=
  forall (j : nat) (x : list mobs * bv 8),
    E !! j = Some x -> x.2 = echo_line !!! (j `mod` length echo_line).

Lemma E_byte_of_disc (E : list (list mobs * bv 8)) :
  E_index E ->
  (forall j x, E !! j = Some x -> disc_seg x.1) ->
  E_byte E.
Proof.
  intros Hidx Hd j x Hx.
  destruct (Hidx j x Hx) as [Hends Hlen].
  rewrite (disc_seg_last_byte x.1 x.2 (Hd j x Hx) Hends) Hlen.
  by rewrite Nat.sub_succ Nat.sub_0_r.
Qed.

(* ...and the form [D] consumes *)
Lemma E_byte_echo (E : list (list mobs * bv 8)) (j : nat) (x : list mobs * bv 8) :
  E_byte E -> E !! j = Some x ->
  echo_of x.2 = echo_line !!! (j `mod` length echo_line).
Proof.
  intros HE Hx. rewrite (HE j x Hx). apply echo_of_echo_line.
  apply elem_of_list_lookup_2 with (j `mod` length echo_line).
  rewrite -list_lookup_lookup_total_lt //.
  apply Nat.mod_upper_bound. pose proof echo_line_pos. lia.
Qed.

Lemma E_byte_take (E : list (list mobs * bv 8)) (n : nat) :
  E_byte E -> E_byte (take n E).
Proof.
  intros HE j x Hx. apply lookup_take_Some in Hx as [Hx _]. by apply HE.
Qed.

Lemma E_index_take (E : list (list mobs * bv 8)) (n : nat) :
  E_index E -> E_index (take n E).
Proof.
  intros HE j x Hx. apply lookup_take_Some in Hx as [Hx _]. by apply HE.
Qed.

(* ====================================================================== *)
(*  4.  F1 -- THE STAGE IS BELOW THE SESSION                               *)
(* ====================================================================== *)

(* [sess_n] grows by at least one byte per input.  This is what refutes
   "the input got ahead of the echo" in F2, and [EchoDisc.sess_n_mono] is
   only the non-strict half. *)
Lemma sess_n_length_step ps cs n :
  length (sess_n ps cs n) < length (sess_n ps cs (S n)).
Proof.
  (* through [EchoDisc]'s length lemmas and not [length_app]: the line is
     a JOIN now, and [!length_app] would take [length echo_line] apart *)
  rewrite !sess_n_length.
  pose proof echo_line_pos as HL.
  destruct (div_mod_succ n (length echo_line) echo_line_pos)
    as [(Hm & Hd & Hr)|(Hm & Hd)]; rewrite Hm Hd.
  - rewrite alt_seq_S_length.
    pose proof (Nat.mod_upper_bound n (length echo_line) ltac:(lia)).
    lia.
  - pose proof (Nat.mod_upper_bound n (length echo_line) ltac:(lia)).
    lia.
Qed.

Lemma sess_n_length_lt ps cs n m :
  n < m -> length (sess_n ps cs n) < length (sess_n ps cs m).
Proof.
  intros Hnm. induction Hnm as [|m Hnm IH].
  - apply sess_n_length_step.
  - etrans; [exact IH | apply sess_n_length_step].
Qed.

(* F1, THE BOUNDARY EQUATION.  Stated at EVERY stage, not only at a line
   boundary: mid-line [pending] is empty and the equation is the statement
   that the echoes so far ARE the line's prefix.  The note asks for it at
   [length E = 17 q]; that is the instance the claim spends, but the
   induction needs the general one anyway. *)
Lemma E_byte_app_l (E : list (list mobs * bv 8)) (x : list mobs * bv 8) :
  E_byte (E ++ [x]) -> E_byte E.
Proof.
  intros HE j y Hy. apply HE. rewrite lookup_app_l; [exact Hy|].
  by eapply lookup_lt_Some.
Qed.

Lemma D_pending_sess (ps cs : list nat) (E : list (list mobs * bv 8)) :
  E_byte E -> D ps cs E ++ pending ps cs E = sess_n ps cs (length E).
Proof.
  induction E as [|x E IH] using rev_ind; intros HE.
  - by rewrite D_nil pending_nil /= sess_n_0.
  - pose proof echo_line_pos as HL.
    pose proof (E_byte_echo (E ++ [x]) (length E) x HE
                  ltac:(rewrite lookup_app_r;
                        [ by rewrite Nat.sub_diag | lia ])) as Hb.
    pose proof (Nat.mod_upper_bound (length E) (length echo_line)
                  ltac:(lia)) as Hub.
    set (n := length E) in *.
    assert (Hlen : length (E ++ [x]) = S n) by (rewrite length_app /=; lia).
    (* the byte the echo adds is [echo_line]'s next *)
    assert (Htk : take (n `mod` length echo_line) echo_line
                    ++ [echo_line !!! (n `mod` length echo_line)]
                  = take (S (n `mod` length echo_line)) echo_line).
    { rewrite (take_S_r echo_line _ (echo_line !!! (n `mod` length echo_line)));
        [done|]. by rewrite -list_lookup_lookup_total_lt. }
    assert (HtkK : forall K : list (bv 8),
              take (n `mod` length echo_line) echo_line
                ++ [echo_line !!! (n `mod` length echo_line)] ++ K
              = take (S (n `mod` length echo_line)) echo_line ++ K).
    { intros K. by rewrite app_assoc Htk. }
    rewrite D_app (app_assoc (D ps cs E) (pending ps cs E) [echo_of x.2]).
    rewrite (IH (E_byte_app_l _ _ HE)) Hb /pending Hlen.
    destruct (div_mod_succ n (length echo_line) echo_line_pos)
      as [(Hm & Hd & Hr)|(Hm & Hd)].
    + (* a line just completed: the echo closes [echo_line] and the
         continuation of line [n / 17] is what is owed next *)
      assert (Hp : pending_n ps cs (S n)
                   = alt_cont ps cs (n `div` length echo_line)).
      { rewrite /pending_n. case_decide as H1; [exfalso; lia|].
        case_decide as H2; [|exfalso; exact (H2 Hm)].
        by rewrite Hd Nat.sub_succ Nat.sub_0_r. }
      rewrite Hp /sess_n Hm Hd alt_seq_S /alt_blk take_0 app_nil_r -!app_assoc.
      rewrite HtkK Hr.
      replace (S (length echo_line - 1)) with (length echo_line) by lia.
      by rewrite take_ge; [|lia].
    + (* mid-line: nothing is owed, and the echo extends the take *)
      assert (Hp : pending_n ps cs (S n) = []).
      { rewrite /pending_n. case_decide as H1; [exfalso; lia|].
        case_decide as H2; [exfalso; rewrite Hm in H2; lia|done]. }
      rewrite Hp /sess_n Hm Hd app_nil_r -!app_assoc. by rewrite Htk.
Qed.

(* F1, AS THE CLAIM USES IT *)
Lemma D_stage_prefix (ps cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) :
  E_byte E -> w `prefix_of` pending ps cs E ->
  (D ps cs E ++ w) `prefix_of` sess_n ps cs (length E).
Proof.
  intros HE Hw. rewrite -(D_pending_sess ps cs E HE).
  by apply prefix_app, Hw.
Qed.

(* the third side condition the note lists, [sess_n cs n ⊑ sess_n cs m] for
   [n <= m], IS [EchoDisc.sess_n_mono] and is not restated here. *)

(* ====================================================================== *)
(*  5.  F2 -- THE NEXT ECHO IS THE NEXT INPUT                              *)
(* ====================================================================== *)

(* TWO PREFIX-COMPARABLE HISTORIES THAT END IN THE SAME INPUT NUMBER ARE
   EQUAL.  The note asks for this by name; it is what turns "the byte is
   already logged" into a contradiction with the log-order fact. *)
Lemma ins_hist_agree (h1 h2 : list mobs) (c1 c2 : bv 8) :
  h1 `prefix_of` h2 ->
  obs_ends_in Uart0 h1 c1 -> obs_ends_in Uart0 h2 c2 ->
  length (ins h1) = length (ins h2) -> h1 = h2.
Proof.
  intros [k ->] He1 He2 Hlen.
  rewrite ins_app length_app in Hlen.
  assert (Hk : ins k = []) by (apply nil_length_inv; lia).
  destruct k as [|e k _] using rev_ind; [by rewrite app_nil_r|].
  exfalso. destruct He2 as [h0 Hh0].
  rewrite app_assoc in Hh0.
  apply app_inj_tail in Hh0 as [_ ->].
  rewrite ins_app ins_in in Hk. by apply app_eq_nil in Hk as [_ ?].
Qed.

(* F2.  The wire is abstract ([W]) so that the Iris lane may instantiate it
   with [obs_wire Uart0 (open_seg h)] or with [obs_wire Uart0 h]; the two
   hypotheses about it are the discipline's LOWER bound at this input
   ([EchoDisc.disc_pt cs (m-1)], D1/D2) and the claim's UPPER bound.

   HYPOTHESES THE NOTE DOES NOT LIST: [E_byte E] (F1 turns on it), and
   [Hnew] -- the new input's history strictly extends every logged one.
   [Hnew] is the kernel's own log-order fact (the design: "the kernel
   proves [h] is strictly above every history already in [pops]"), and
   without it nothing refutes [m <= length E]: an adversary log that
   records the SAME input twice satisfies every other hypothesis. *)
Lemma prefix_app_cancel {A} (k a b : list A) :
  (k ++ a) `prefix_of` (k ++ b) -> a `prefix_of` b.
Proof.
  intros [z Hz]. exists z. rewrite -app_assoc in Hz. by apply app_inv_head in Hz.
Qed.

Lemma hist_ext_irrefl (h : list mobs) : hist_ext h h -> False.
Proof. intros [_ Hl]. lia. Qed.

Lemma D2_next_input (ps cs : list nat) (E : list (list mobs * bv 8))
      (w W : list (bv 8)) (h : list mobs) (c : bv 8) (m : nat) :
  E_byte E -> E_index E ->
  (forall x, x ∈ E -> hist_ext x.1 h) ->
  obs_ends_in Uart0 h c ->
  length (ins h) = m ->
  w `prefix_of` pending ps cs E ->
  sess_n ps cs (m - 1) `prefix_of` W ->
  W `prefix_of` (D ps cs E ++ w) ->
  m = S (length E) /\ w = pending ps cs E.
Proof.
  intros HEb HEi Hnew Hends Hm Hw Hlow Hup.
  assert (Hm1 : 1 <= m).
  { destruct Hends as [h0 ->]. rewrite -Hm ins_app ins_in length_app /=. lia. }
  (* the discipline's lower bound and the claim's upper bound meet *)
  assert (Hboth : sess_n ps cs (m - 1) `prefix_of` sess_n ps cs (length E)).
  { etrans; [exact Hlow|]. etrans; [exact Hup|]. by apply D_stage_prefix. }
  (* the input cannot have got AHEAD of the echo: [sess_n] grows per input *)
  assert (Hle : m - 1 <= length E).
  { destruct (decide (m - 1 <= length E)) as [?|Hgt]; [done|exfalso].
    apply prefix_length in Hboth.
    pose proof (sess_n_length_lt ps cs (length E) (m - 1) ltac:(lia)). lia. }
  (* ...nor can it be one the log already has: the histories would agree *)
  assert (Heq : m - 1 = length E).
  { destruct (decide (m - 1 = length E)) as [?|Hne]; [done|exfalso].
    assert (Hlt : m - 1 < length E) by lia.
    destruct (lookup_lt_is_Some_2 E (m - 1) Hlt) as [x Hx].
    destruct (HEi (m - 1) x Hx) as [Hxe Hxlen].
    assert (Hxin : x ∈ E) by (by eapply elem_of_list_lookup_2).
    destruct (Hnew x Hxin) as [Hpre Hlen'].
    assert (Hsame : x.1 = h).
    { eapply ins_hist_agree; [exact Hpre|exact Hxe|exact Hends|]. lia. }
    rewrite Hsame in Hlen'. lia. }
  split; [lia|].
  apply (anti_symm prefix); [exact Hw|].
  eapply (prefix_app_cancel (D ps cs E)).
  rewrite (D_pending_sess ps cs E HEb) -Heq.
  etrans; [exact Hlow|exact Hup].
Qed.

(* ====================================================================== *)
(*  6.  F3 -- THE READ WINDOW IS A SLICE OF [E]                            *)
(* ====================================================================== *)

(* the entries a read may hand out: the ECHOED ones, in log order *)
Definition echoed (pops : list log_entry) : list (list mobs * bv 8) :=
  (fun e => (le_hist e, le_byte e)) <$> filter log_echoed pops.

Lemma echoed_lookup (pops : list log_entry) (j : nat) (x : list mobs * bv 8) :
  echoed pops !! j = Some x ->
  exists e, e ∈ pops /\ log_echoed e /\ (le_hist e, le_byte e) = x.
Proof.
  rewrite /echoed list_lookup_fmap fmap_Some.
  intros (e & He & ->). exists e. split; [|split; [|reflexivity]].
  - apply elem_of_list_lookup_2 in He. by apply elem_of_list_filter in He as [_ ?].
  - apply elem_of_list_lookup_2 in He. by apply elem_of_list_filter in He as [? _].
Qed.

Lemma echoed_elem (pops : list log_entry) (e : log_entry) :
  e ∈ pops -> log_echoed e -> (le_hist e, le_byte e) ∈ echoed pops.
Proof.
  intros Hin Hec. rewrite /echoed. apply elem_of_list_fmap.
  exists e. split; [reflexivity|]. by apply elem_of_list_filter.
Qed.

(* A FILTER KEEPS A STRICT ORDER ON THE INDICES.  The general step behind
   "[echoed pops] is history-ordered because [pops] is". *)
Lemma epu_filter_cons_T {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (a : A) (l : list A) : P a -> filter P (a :: l) = a :: filter P l.
Proof. intro Hp. rewrite filter_cons. case_decide; [done|contradiction]. Qed.

Lemma epu_filter_cons_F {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (a : A) (l : list A) : ~ P a -> filter P (a :: l) = filter P l.
Proof. intro Hp. rewrite filter_cons. case_decide; [contradiction|done]. Qed.

Lemma filter_strict_order {A} (P : A -> Prop) `{!forall x, Decision (P x)}
      (R : A -> A -> Prop) (l : list A) :
  (forall i j x y, i < j -> l !! i = Some x -> l !! j = Some y -> R x y) ->
  (forall i j x y, i < j -> filter P l !! i = Some x ->
                   filter P l !! j = Some y -> R x y).
Proof.
  induction l as [|a l IH]; intros Hl i j x y Hij Hx Hy.
  { rewrite filter_nil in Hx. by rewrite lookup_nil in Hx. }
  assert (Hl' : forall i j x y, i < j -> l !! i = Some x -> l !! j = Some y -> R x y).
  { intros i' j' x' y' Hij' Hx' Hy'. by eapply (Hl (S i') (S j')); [lia| |]. }
  destruct (decide (P a)) as [Hpa|Hpa].
  - rewrite (epu_filter_cons_T P a l Hpa) in Hx, Hy.
    destruct i as [|i].
    + cbn in Hx. simplify_eq.
      destruct j as [|j]; [lia|]. cbn in Hy.
      assert (Hin : y ∈ l).
      { apply elem_of_list_lookup_2 in Hy.
        by apply elem_of_list_filter in Hy as [_ ?]. }
      apply elem_of_list_lookup in Hin as [n Hn].
      by eapply (Hl 0%nat (S n)); [lia| |].
    + destruct j as [|j]; [lia|]. cbn in Hx, Hy.
      apply (IH Hl' i j x y); [lia|exact Hx|exact Hy].
  - rewrite (epu_filter_cons_F P a l Hpa) in Hx, Hy.
    by eapply IH; [exact Hl'|exact Hij| |].
Qed.

Lemma echoed_order (pops : list log_entry) (i j : nat)
      (x y : list mobs * bv 8) :
  log_ok pops -> i < j ->
  echoed pops !! i = Some x -> echoed pops !! j = Some y ->
  hist_ext x.1 y.1.
Proof.
  intros Hlog Hij Hx Hy.
  rewrite /echoed list_lookup_fmap fmap_Some in Hx.
  destruct Hx as (e1 & He1 & ->).
  rewrite /echoed list_lookup_fmap fmap_Some in Hy.
  destruct Hy as (e2 & He2 & ->). cbn.
  eapply (filter_strict_order log_echoed
            (fun a b => hist_ext (le_hist a) (le_hist b)) pops);
    [ |exact Hij|exact He1|exact He2].
  intros i' j' a b Hij' Ha Hb. by eapply log_ok_lt.
Qed.

(* ---- what refutes an entry in a gap ---- *)

Lemma hist_ext_nil_of_ends (h : list mobs) (c : bv 8) :
  obs_ends_in Uart0 h c -> hist_ext [] h.
Proof.
  intros [h0 ->]. split; [apply prefix_nil|]. rewrite length_app /=. lia.
Qed.

Lemma echoed_elem_inv (pops : list log_entry) (y : list mobs * bv 8) :
  y ∈ echoed pops ->
  exists e, e ∈ pops /\ log_echoed e /\ (le_hist e, le_byte e) = y.
Proof.
  rewrite /echoed. intros Hy. apply elem_of_list_fmap in Hy as (e & -> & He).
  apply elem_of_list_filter in He as [Hec Hin]. by exists e.
Qed.

(* NO LOGGED BYTE IS AN ERASE CHARACTER, under the discipline -- which
   kills the gap clause's second disjunct outright *)
Lemma pops_no_erase (pops : list log_entry) :
  log_ok pops -> (forall e, e ∈ pops -> disc_seg (le_hist e)) ->
  forall e, e ∈ pops -> cons_erase (le_byte e) = false.
Proof.
  intros [Hends _] Hdisc e He.
  eapply disc_seg_no_erase; [by apply Hdisc|by apply (proj1 (Hends e He))].
Qed.

(* ...so NO ECHOED ENTRY LIES STRICTLY INSIDE A GAP *)
(* ...SO NO ECHOED ENTRY LIES STRICTLY INSIDE A GAP.  The premise is the ONE
   consequence of the discipline this argument uses -- [pops_no_erase] is its
   producer -- and not the discipline itself: lane ECHO-OUT's claim carries
   the discipline of each entry's CYCLE SEGMENT, from which the whole
   history's [disc_seg] does not follow, while the no-erase fact does
   ([disc_seg_no_erase] at the segment). *)
Lemma no_echoed_between (pops : list log_entry) (h1 h2 : list mobs)
      (y : list mobs * bv 8) :
  log_ok pops -> (forall e, e ∈ pops -> cons_erase (le_byte e) = false) ->
  gap_ok pops h1 h2 ->
  y ∈ echoed pops -> hist_ext h1 y.1 -> hist_ext y.1 h2 -> False.
Proof.
  intros Hlog Hnoer Hgap Hy H1 H2.
  destruct (echoed_elem_inv pops y Hy) as (e & Hein & Hech & Heq).
  assert (Hh : le_hist e = y.1) by (by rewrite -Heq).
  destruct Hgap as [Hleft|(e' & He'in & _ & _ & Herase)].
  - apply (log_echoed_nonnil e Hech). apply (Hleft e Hein); by rewrite Hh.
  - rewrite (Hnoer e' He'in) in Herase. discriminate.
Qed.

(* F3(a): THE CONSUMED INPUTS ARE AN INITIAL SEGMENT OF THE ECHOED ONES.

   [ws] is the window the read path CONSUMED, not the window it delivered:
   the kernel has two exits that pop a byte and hand it to nobody (a
   leading ^D, and a copy-out fault), so the delivered bytes are a PREFIX
   of [ws] of some length [d].  F3(a) is about the consumed window, which
   is the one [read_ok] speaks of; the swallow is refuted separately (^D is
   not a byte of [echo_line]: [disc_seg_no_ctrl_d]) and enters F3(c) as the
   named hypothesis [d = length ws].

   THE LOG-TO-[E] IDENTIFICATION LIVES HERE AND ONLY HERE.  F1 and F2 are
   stated over an abstract [E] on purpose: the kernel appends the log entry
   AFTER the echo's out_links, so between the two the claim's [E] is one
   entry AHEAD of [echoed pops] and no lemma may assume they agree.

   HYPOTHESES THE NOTE DOES NOT LIST.  (1) The no-erase fact is needed for
   EVERY entry of [pops], not only for [ws]'s: the gap clause's erase
   disjunct names an arbitrary LOG entry, which need not have been consumed,
   and the only thing that refutes it is that a disciplined input byte is a
   byte of [echo_line] and no erase byte is.  It is the DISCIPLINE'S
   consequence and not the discipline ([pops_no_erase] is the producer, and
   [disc_seg_no_erase] is it at a cycle segment, which is the form lane
   ECHO-OUT's claim carries).  (2) [log_ok pops]
   is what makes [echoed pops] history-ordered, so that "no log entry
   strictly between two consecutive consumed ones" is a statement about
   INDICES.  Both hold on the Iris side -- [disc] is prefix-closed, so
   every history in the log is disciplined once the current one is -- but
   neither is in the note's list. *)
Lemma read_window_prefix (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) :
  log_ok pops ->
  read_ok pops dl ws ->
  (forall e, e ∈ pops -> cons_erase (le_byte e) = false) ->
  dl `prefix_of` echoed pops ->
  (dl ++ ws) `prefix_of` echoed pops.
Proof.
  intros Hlog (Hin & Hchain & Hgap0 & Hgap) Hnoer Hdl.
  (* the consumed list agrees with [echoed pops] index by index, by strong
     induction on the index (the bound [N] is the induction's measure) *)
  assert (Hpt : forall N k, k < N -> k < length (dl ++ ws) ->
                  echoed pops !! k = (dl ++ ws) !! k).
  { induction N as [|N IHN]; intros k HkN Hk; [lia|].
    destruct ((dl ++ ws) !! k) as [p|] eqn:Hp;
      [|exfalso; apply lookup_ge_None_1 in Hp; lia].
    destruct (decide (k < length dl)) as [Hkl|Hkl].
    { (* below [dl]: [dl] is already an initial segment *)
      destruct Hdl as [z Hz]. rewrite Hz.
      rewrite lookup_app_l; last exact Hkl.
      rewrite lookup_app_l in Hp; last exact Hkl. exact Hp. }
    (* at or above [dl]: [p] is an entry of [ws], hence an echoed entry *)
    assert (Hpin : p ∈ ws).
    { rewrite lookup_app_r in Hp; [|lia]. by eapply elem_of_list_lookup_2. }
    destruct (Hin p Hpin) as (ep & Hepin & Hepeq & Hepech).
    assert (HpE : p ∈ echoed pops).
    { rewrite -Hepeq. by apply echoed_elem. }
    apply elem_of_list_lookup in HpE as [n Hn].
    assert (Hnk : n = k).
    { destruct (decide (n < k)) as [Hlt|Hge].
      - (* the same entry twice in the consumed list: the chain forbids it *)
        exfalso. rewrite (IHN n ltac:(lia) ltac:(lia)) in Hn.
        destruct p as [hp cp].
        eapply hist_ext_irrefl, (hist_chain_lt _ n k); [exact Hchain|lia| |];
          [exact Hn|exact Hp].
      - destruct (decide (k < n)) as [Hlt|?]; [|lia]. exfalso.
        (* an echoed entry sits strictly inside the gap the read left *)
        assert (Hy : is_Some (echoed pops !! k)).
        { apply lookup_lt_is_Some. apply lookup_lt_Some in Hn. lia. }
        destruct Hy as [y Hy].
        assert (Hyp : hist_ext y.1 p.1)
          by (eapply echoed_order; [exact Hlog|exact Hlt|exact Hy|exact Hn]).
        assert (HyE : y ∈ echoed pops) by (by eapply elem_of_list_lookup_2).
        destruct k as [|k'].
        + destruct p as [hp cp].
          eapply (no_echoed_between pops [] hp y);
            [exact Hlog|exact Hnoer|by eapply Hgap0|exact HyE| |exact Hyp].
          destruct (echoed_elem_inv pops y HyE) as (ey & Heyin & _ & Heyeq).
          rewrite -Heyeq /=.
          eapply hist_ext_nil_of_ends.
          by apply (proj1 (proj1 Hlog ey Heyin)).
        + assert (Hp' : is_Some ((dl ++ ws) !! k')) by (apply lookup_lt_is_Some; lia).
          destruct Hp' as [p' Hp'].
          assert (HE' : echoed pops !! k' = Some p')
            by (rewrite (IHN k' ltac:(lia) ltac:(lia)); exact Hp').
          destruct p as [hp cp]. destruct p' as [hp' cp'].
          eapply (no_echoed_between pops hp' hp y);
            [exact Hlog|exact Hnoer|by eapply Hgap|exact HyE| |exact Hyp].
          apply (echoed_order pops k' (S k') (hp', cp') y);
            [exact Hlog|lia|exact HE'|exact Hy]. }
    by rewrite Hnk in Hn. }
  (* pointwise agreement over the whole consumed list IS the prefix *)
  assert (Hle : length (dl ++ ws) <= length (echoed pops)).
  { destruct (decide (length (dl ++ ws) = 0)) as [H0|Hne]; [lia|].
    destruct ((dl ++ ws) !! (length (dl ++ ws) - 1)) as [p|] eqn:Hp;
      [|apply lookup_ge_None_1 in Hp; lia].
    pose proof (Hpt (length (dl ++ ws)) (length (dl ++ ws) - 1)
                  ltac:(lia) ltac:(lia)) as Hq.
    rewrite Hp in Hq. apply lookup_lt_Some in Hq. lia. }
  assert (Heq : take (length (dl ++ ws)) (echoed pops) = dl ++ ws).
  { apply list_eq. intros k.
    destruct (decide (k < length (dl ++ ws))) as [Hk|Hk].
    - rewrite lookup_take; [|exact Hk]. by eapply (Hpt (S k)); [lia|].
    - rewrite lookup_take_ge; [|lia]. symmetry. apply lookup_ge_None_2. lia. }
  exists (drop (length (dl ++ ws)) (echoed pops)).
  by rewrite -{1}(take_drop (length (dl ++ ws)) (echoed pops)) Heq.
Qed.

(* F3(b): A SEVENTEEN-BYTE CONSUMED WINDOW AT A LINE BOUNDARY IS THE LINE.
   Stated over an abstract [E] so that ECHO-OUT may chain it off F3(a) with
   [E := echoed pops], or off the claim's own [E] when the two agree. *)
Lemma read_window_line (E : list (list mobs * bv 8))
      (dl ws : list (list mobs * bv 8)) (q : nat) :
  E_byte E ->
  (dl ++ ws) `prefix_of` E ->
  length dl = length echo_line * q ->
  length ws = length echo_line ->
  snd <$> ws = echo_line.
Proof.
  intros HE Hp Hdl Hws.
  pose proof echo_line_pos as HL.
  apply list_eq. intros k.
  destruct (decide (k < length echo_line)) as [Hk|Hk].
  - destruct (lookup_lt_is_Some_2 ws k ltac:(lia)) as [x Hwk].
    rewrite list_lookup_fmap Hwk /=.
    assert (Hak : (dl ++ ws) !! (length dl + k) = Some x).
    { rewrite lookup_app_r; [|lia].
      by replace (length dl + k - length dl) with k by lia. }
    assert (HEk : E !! (length dl + k) = Some x).
    { destruct Hp as [z ->]. rewrite lookup_app_l; [exact Hak|].
      by eapply lookup_lt_Some. }
    assert (Hmod : (length dl + k) `mod` length echo_line = k).
    { rewrite Hdl.
      replace (length echo_line * q + k) with (k + q * length echo_line) by lia.
      rewrite Nat.Div0.mod_add. by apply Nat.mod_small. }
    rewrite (HE _ _ HEk) Hmod.
    by rewrite (list_lookup_lookup_total_lt echo_line k Hk).
  - rewrite list_lookup_fmap (lookup_ge_None_2 ws k ltac:(lia)) /=.
    symmetry. apply lookup_ge_None_2. lia.
Qed.

(* F3(c): ...AND THAT IS WHAT THE PROCESS GOT, once no byte was swallowed.
   [d] is the number of bytes the read actually delivered; [Hd] is the "no
   swallow" fact, which the application pays with [disc_seg_no_ctrl_d] (the
   ^D exit) and with the copy-out fault's own refutation. *)
Lemma read_delivered_line (E : list (list mobs * bv 8))
      (dl ws : list (list mobs * bv 8)) (q d : nat) :
  E_byte E ->
  (dl ++ ws) `prefix_of` E ->
  length dl = length echo_line * q ->
  length ws = length echo_line ->
  d = length ws ->
  snd <$> take d ws = echo_line.
Proof.
  intros HE Hp Hdl Hws Hd.
  rewrite Hd take_ge; [|lia].
  by eapply read_window_line.
Qed.

(* ====================================================================== *)
(*  7.  F4 -- PHI's PURE PART                                              *)
(* ====================================================================== *)

(* THE CLAIM GIVES [good_out] AT THE SEGMENT.  [Forall (< length line_alts)
   cs] is needed HERE and not in F1 -- [expected_rel] quantifies over a
   BOUNDED choice list, while [D] and [sess_n] index [cs] with the same
   total [!!!] and agree out of range.  [length cs = length E / 17] is not
   needed at all, for the same reason. *)
Lemma good_out_of_stage (ps cs : list nat) (E : list (list mobs * bv 8))
      (w : list (bv 8)) (seg : list mobs) :
  Forall (fun a => a < length pro_alts) ps ->
  Forall (fun i => i < length line_alts) cs ->
  E_byte E ->
  pro_pin ps cs (length E) ->
  w `prefix_of` pending ps cs E ->
  obs_wire Uart0 seg `prefix_of` (D ps cs E ++ w) ->
  length E <= length (ins seg) ->
  good_out seg.
Proof.
  intros Hps Hcs HE Hpin Hw Hwire Hlen.
  (* THE WITNESS IS THE STAGE'S RESOLUTION PADDED WITH ONE TERMINATED ROUND:
     the stage may be standing mid-prologue, and [expected_rel] quantifies
     over a SETTLED one.  Padding moves no round the stage has read. *)
  set (ps' := (ps ++ replicate (S (length (ins seg))) 0%nat)%list).
  assert (Hpp : ps `prefix_of` ps') by (rewrite /ps'; by eexists).
  exists ps', cs. split.
  { apply pro_ok_pad; [exact Hps |].
    pose proof echo_line_pos as HL.
    apply Nat.Div0.div_le_upper_bound. nia. }
  split; [exact Hcs|].
  rewrite /sess. etrans; [exact Hwire|].
  rewrite (D_ps_ext ps ps' cs E Hpp Hpin).
  etrans; [| by apply (sess_n_mono ps' cs (length E) (length (ins seg)))].
  apply (D_stage_prefix ps' cs E w HE).
  etrans; [exact Hw |]. rewrite /pending. by apply pending_n_ps_mono.
Qed.

(* WHAT IS NO LONGER HERE: [echo_phi_of_good_out], the weakening from
   [Forall good_out (cycles_of h)] to the PER-CYCLE GUARDED form
   [Forall (fun seg => disc_seg' seg -> good_out seg) (cycles_of h)].
   [AppEcho.echo_phi] WAS that guarded form; since lane ECHO-OUT part 5 it
   is the owner's WHOLE-HISTORY implication [disc h -> Forall good_out
   (cycles_of h)] ("there is no per-cycle form -- once we get taint in one
   era, it's tainted forever"), which the ledger pays directly
   ([EchoOut.echo_led_phi]).  Nothing bridges to the guarded shape any
   more, and nothing ever used this lemma. *)

(* ====================================================================== *)
(*  8.  THE CHOICES ARE READABLE OFF THE WIRE                              *)
(*                                                                        *)
(*  Lane ECHO-OUT needs D2's LOWER bound at the CLAIM's choice list, and   *)
(*  the discipline supplies it at ITS OWN existential witness              *)
(*  ([EchoDisc.disc_seg'] is [∃ cs, ... disc_pt cs i p]).  The two lists   *)
(*  are different objects, and F2 is stated at one list on purpose: it     *)
(*  compares [sess_n cs (m-1)] with [sess_n cs (length E)] by LENGTH, and  *)
(*  across two lists that comparison is simply false -- the alternatives   *)
(*  have different lengths, so [sess_n cs' 34] can be shorter than         *)
(*  [sess_n cs 17].                                                        *)
(*                                                                        *)
(*  What rescues it is the note's own remark about [line_alts] (EchoDisc,  *)
(*  the O5 ruling): the four alternatives begin with 'h', 'e', '$', 'f',   *)
(*  PAIRWISE DISTINCT, so the resolution is readable off the wire.  Hence  *)
(*  two session transcripts that are prefix-comparable AGREE, and the      *)
(*  discipline's witness may be replaced by the claim's wherever both are  *)
(*  below one wire.  That is [sess_n_prefix_det].                          *)
(* ====================================================================== *)

Lemma line_alts_nonnil (a : nat) :
  a < length line_alts -> line_alts !!! a <> [].
Proof.
  rewrite line_alts_length. intros Ha.
  destruct a as [|[|[|[|a]]]]; try lia; vm_compute; discriminate.
Qed.

(* THE WHOLE-BLOCK READING, as on the prologue side
   ([EchoDisc.pro_alts_prefix_det]): the four alternatives are PAIRWISE
   PREFIX-FREE, so a wire that carries one of them carries no other.

   IT USED TO BE A ONE-BYTE READING -- the four heads are 'h', 'e', '$',
   'f' -- and that is a property of what echo happens to print.  At an
   arbitrary line it fails: a wire showing "fork\n" could be echo printing
   the word [fork] or sh's own fork1 panicking, and one showing
   "exec echo failed\n$ " could be echo printing those three words or the
   child failing to exec.  In BOTH cases the observer genuinely cannot
   tell, so the claim has to exclude them -- and prefix-freeness excludes
   exactly those two outputs and nothing else, where distinct heads would
   have excluded every line whose first printed word begins with 'e' or
   'f'.  The exclusion belongs to sh's diagnostics, not to any letter.

   DECIDABLE, so it is a computation at any given line and a premise once
   the word list becomes a parameter. *)
Lemma line_alts_prefix_det (a b : nat) :
  a < length line_alts -> b < length line_alts ->
  line_alts !!! a `prefix_of` line_alts !!! b -> a = b.
Proof.
  rewrite line_alts_length. intros Ha Hb.
  destruct a as [|[|[|[|a]]]]; destruct b as [|[|[|[|b]]]]; try lia;
    try reflexivity;
    intros H; exfalso; revert H;
    apply (bool_decide_unpack _); vm_compute; exact I.
Qed.

(* out of range [!!!] reads [0], which IS in range, so this is the honest
   hypothesis and it follows from the [Forall] both sides carry *)
Definition cs_ok (cs : list nat) : Prop :=
  forall i, cs !!! i < length line_alts.

Lemma cs_ok_of_Forall cs :
  Forall (fun x => x < length line_alts) cs -> cs_ok cs.
Proof.
  intros HF i. destruct (decide (i < length cs)) as [Hi|Hi].
  - destruct (lookup_lt_is_Some_2 cs i Hi) as [x Hx].
    rewrite (list_lookup_total_correct cs i x Hx).
    exact (Forall_lookup_1 _ _ _ _ HF Hx).
  - rewrite list_lookup_total_alt (lookup_ge_None_2 cs i ltac:(lia)) /=.
    pose proof line_alts_length. lia.
Qed.

Lemma lookup_total_drop {A} `{!Inhabited A} (n i : nat) (l : list A) :
  drop n l !!! i = l !!! (n + i).
Proof. by rewrite !list_lookup_total_alt lookup_drop. Qed.

Lemma cs_ok_drop cs n : cs_ok cs -> cs_ok (drop n cs).
Proof. intros H i. rewrite lookup_total_drop. apply H. Qed.

(* THE ROUND POINTER MOVES WITH THE DROP: dropping [n] lines drops the
   [pro_idx cs n] prologue rounds those lines opened. *)
Lemma pro_idx_add cs n i :
  pro_idx cs (n + i) = (pro_idx cs n + pro_idx (drop n cs) i)%nat.
Proof.
  induction i as [| i IH]; [rewrite Nat.add_0_r; cbn [pro_idx]; lia |].
  rewrite Nat.add_succ_r !pro_idx_S IH lookup_total_drop.
  case_decide; lia.
Qed.

Lemma alt_blk_drop ps cs n i :
  alt_blk (pro_from (pro_idx cs n) ps) (drop n cs) i = alt_blk ps cs (n + i).
Proof.
  rewrite /alt_blk /alt_cont !lookup_total_drop. f_equal. f_equal.
  case_decide as H3; [| done].
  rewrite pro_from_add pro_idx_add. f_equal. f_equal. lia.
Qed.

Lemma alt_seq_cons ps cs q :
  alt_seq ps cs (S q)
  = alt_blk ps cs 0 ++ alt_seq (pro_from (pro_idx cs 1) ps) (drop 1 cs) q.
Proof.
  rewrite /alt_seq.
  replace (List.seq 0 (S q)) with (0 :: List.seq 1 q) by reflexivity.
  rewrite fmap_cons concat_cons. f_equal.
  rewrite -List.seq_shift -list_fmap_compose.
  f_equal. apply list_fmap_ext.
  intros i x Hx. rewrite /compose. by rewrite (alt_blk_drop ps cs 1 x).
Qed.

Lemma alt_blk_length ps cs i : 0 < length (alt_blk ps cs i).
Proof.
  rewrite /alt_blk length_app. pose proof echo_line_pos. lia.
Qed.

Lemma alt_seq_cons_assoc ps cs q (t : list (bv 8)) :
  alt_seq ps cs (S q) ++ t
  = echo_line ++ (alt_cont ps cs 0%nat
                  ++ (alt_seq (pro_from (pro_idx cs 1%nat) ps) (drop 1 cs) q ++ t)).
Proof.
  rewrite alt_seq_cons /alt_blk.
  rewrite -(app_assoc echo_line (alt_cont ps cs 0%nat)
              (alt_seq (pro_from (pro_idx cs 1%nat) ps) (drop 1 cs) q)).
  rewrite -(app_assoc echo_line
              (alt_cont ps cs 0%nat
               ++ alt_seq (pro_from (pro_idx cs 1%nat) ps) (drop 1 cs) q) t).
  by rewrite -(app_assoc (alt_cont ps cs 0%nat)
                 (alt_seq (pro_from (pro_idx cs 1%nat) ps) (drop 1 cs) q) t).
Qed.

(* whatever follows a block on the wire begins with [echo_line]'s first
   byte: it is either the next block (which begins with the echo) or the
   line in progress (a prefix of [echo_line]). *)
Lemma alt_seq_app_head ps cs q (t : list (bv 8)) (b : bv 8) :
  t `prefix_of` echo_line ->
  (alt_seq ps cs q ++ t) !! 0%nat = Some b -> echo_line !! 0%nat = Some b.
Proof.
  intros Ht Hb. destruct q as [| q].
  - rewrite alt_seq_0 app_nil_l in Hb.
    eapply prefix_lookup_Some; [exact Hb | exact Ht].
  - rewrite alt_seq_cons -app_assoc /alt_blk -app_assoc in Hb.
    rewrite lookup_app_l in Hb; [exact Hb |].
    pose proof echo_line_pos. lia.
Qed.

(* THE BLOCK STEP: two continuations below ONE wire are the same
   continuation.  BOTH halves come off PREFIX-FREENESS now -- the LINE
   choice from [line_alts_prefix_det] and, when that choice is the shell's
   own fork panic, the RESTART'S PROLOGUE from
   [EchoDisc.pro_of_prefix_free], which also FORCES the unprimed round
   settled: that is how the stage learns its own prologue is complete. *)
Lemma alt_cont_prefix_det (ps ps' cs cs' : list nat) (X X' : list (bv 8)) :
  cs_ok cs -> cs_ok cs' ->
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  Forall (fun a => (a < length pro_alts)%nat) ps' ->
  (cs' !!! 0%nat = 3%nat -> (1 < pro_rounds ps')%nat) ->
  (forall b, X !! 0%nat = Some b -> echo_line !! 0%nat = Some b) ->
  (alt_cont ps' cs' 0%nat ++ X') `prefix_of` (alt_cont ps cs 0%nat ++ X) ->
  cs' !!! 0%nat = cs !!! 0%nat
  /\ (cs !!! 0%nat = 3%nat -> (1 < pro_rounds ps)%nat)
  /\ alt_cont ps' cs' 0%nat = alt_cont ps cs 0%nat
  /\ X' `prefix_of` X.
Proof.
  intros Hcs Hcs' Hps Hps' Hset HX Hp.
  rewrite /alt_cont -!app_assoc in Hp.
  (* the two alternatives are comparable below the wire, so they are the
     same one -- [EchoDisc.pro_of_prefix_free]'s step, at the line *)
  assert (Hlcmp : line_alts !!! (cs' !!! 0%nat)
                   `prefix_of` line_alts !!! (cs !!! 0%nat)
                 \/ line_alts !!! (cs !!! 0%nat)
                      `prefix_of` line_alts !!! (cs' !!! 0%nat)).
  { eapply prefix_weak_total;
      [ etrans; [apply prefix_app_r; reflexivity | exact Hp]
      | apply prefix_app_r; reflexivity ]. }
  assert (Hhd : cs' !!! 0%nat = cs !!! 0%nat).
  { destruct Hlcmp as [Hc | Hc];
      [ exact (line_alts_prefix_det _ _ (Hcs' 0%nat) (Hcs 0%nat) Hc)
      | symmetry;
        exact (line_alts_prefix_det _ _ (Hcs 0%nat) (Hcs' 0%nat) Hc) ]. }
  rewrite Hhd in Hp. apply prefix_app_inv in Hp.
  cbn [pro_idx] in Hp |- *. rewrite Hhd.
  case_decide as H3.
  - assert (Hd' : pro_done (pro_from 1%nat ps')).
    { apply pro_from_done, Hset. by rewrite Hhd. }
    pose proof (pro_from_Forall _ 1%nat ps Hps) as HFA.
    pose proof (pro_from_Forall _ 1%nat ps' Hps') as HFB.
    assert (Hcmp : pro_of (pro_from 1%nat ps') `prefix_of` pro_of (pro_from 1%nat ps)).
    { destruct (prefix_weak_total (pro_of (pro_from 1%nat ps'))
                  (pro_of (pro_from 1%nat ps))
                  (pro_of (pro_from 1%nat ps) ++ X)
                  ltac:(etrans; [apply prefix_app_r; reflexivity | exact Hp])
                  ltac:(apply prefix_app_r; reflexivity)) as [H | H]; [exact H |].
      (* the other way round: either the stage's own prologue has settled
         (and then they are the same), or it stands open at a banner -- and
         the byte the wire has there is [echo_line]'s, which no alternative
         begins with ([EchoDisc.pro_of_not_done_next]). *)
      destruct (decide (pro_done (pro_from 1%nat ps))) as [HdA | HdA].
      - destruct (pro_of_prefix_free (pro_from 1%nat ps') (pro_from 1%nat ps)
                    HFB HFA HdA H) as [_ Heq]. by rewrite Heq.
      - exfalso.
        assert (Hne : pro_of (pro_from 1%nat ps) <> pro_of (pro_from 1%nat ps')).
        { intros Heq. apply HdA.
          destruct (pro_of_prefix_free (pro_from 1%nat ps) (pro_from 1%nat ps')
                      HFA HFB Hd' ltac:(rewrite Heq; reflexivity)) as [Hd _].
          exact Hd. }
        assert (Hlt : (length (pro_of (pro_from 1%nat ps))
                       < length (pro_of (pro_from 1%nat ps')))%nat).
        { pose proof (prefix_length _ _ H) as Hle.
          destruct (decide (length (pro_of (pro_from 1%nat ps))
                            = length (pro_of (pro_from 1%nat ps')))%nat)
            as [Heq | Hne2]; [| lia].
          exfalso. apply Hne. apply (prefix_length_eq _ _ H). lia. }
        destruct (lookup_lt_is_Some_2 (pro_of (pro_from 1%nat ps'))
                    (length (pro_of (pro_from 1%nat ps))) Hlt) as [b Hb].
        assert (HBAX : pro_of (pro_from 1%nat ps')
                       `prefix_of` (pro_of (pro_from 1%nat ps) ++ X))
          by (etrans; [apply prefix_app_r; reflexivity | exact Hp]).
        assert (Hbx : (pro_of (pro_from 1%nat ps) ++ X)
                        !! length (pro_of (pro_from 1%nat ps)) = Some b)
          by (eapply prefix_lookup_Some; [exact Hb | exact HBAX]).
        rewrite lookup_app_r in Hbx; [| lia].
        rewrite Nat.sub_diag in Hbx.
        destruct (pro_of_not_done_next (pro_from 1%nat ps) (pro_from 1%nat ps')
                    b HFB HdA H Hb) as (aa & Haa & Hah).
        exact (pro_alts_head_ne_echo aa b Haa Hah (HX b Hbx)). }
    destruct (pro_of_prefix_free (pro_from 1%nat ps) (pro_from 1%nat ps')
                HFA HFB Hd' Hcmp) as [Hd Heq].
    rewrite Heq in Hp. apply prefix_app_inv in Hp.
    split; [by rewrite ?Hhd |].
    split; [intros _; by apply pro_from_done |].
    split; [| exact Hp].
    rewrite /alt_cont Hhd. cbn [pro_idx]. by rewrite Heq.
  - rewrite !app_nil_l in Hp.
    split; [by rewrite ?Hhd |]. split; [by intros ? |].
    split; [| exact Hp].
    rewrite /alt_cont Hhd. case_decide as H4; [by destruct (H3 H4) | reflexivity].
Qed.

(* THE STEP: two block sequences below one wire have the same blocks. *)
Lemma alt_seq_prefix_det (q' : nat) :
  forall (ps ps' cs cs' : list nat) (q : nat) (t' t : list (bv 8)),
    Forall (fun a => (a < length pro_alts)%nat) ps ->
    Forall (fun a => (a < length pro_alts)%nat) ps' ->
    (pro_idx cs' q' < pro_rounds ps')%nat ->
    (0 < pro_rounds ps)%nat ->
    cs_ok cs -> cs_ok cs' ->
    t' `prefix_of` echo_line -> t `prefix_of` echo_line ->
    (alt_seq ps' cs' q' ++ t') `prefix_of` (alt_seq ps cs q ++ t) ->
    (q' <= q)%nat /\ (pro_idx cs q' < pro_rounds ps)%nat
    /\ alt_seq ps' cs' q' = alt_seq ps cs q'.
Proof.
  induction q' as [| n IH];
    intros ps ps' cs cs' q t' t Hps Hps' Hlt' Hpos Hcs Hcs' Ht' Ht Hpre.
  { split; [lia |]. split; [cbn [pro_idx]; lia | reflexivity]. }
  pose proof echo_line_pos as HL.
  assert (Hp' : 0 < length (line_alts !!! (cs' !!! 0%nat))).
  { destruct (line_alts !!! (cs' !!! 0%nat)) as [| z zs] eqn:Hz;
      [ exfalso; exact (line_alts_nonnil _ (Hcs' 0%nat) Hz) | cbn; lia ]. }
  destruct q as [| p].
  { exfalso.
    rewrite alt_seq_0 app_nil_l alt_seq_cons_assoc in Hpre.
    apply prefix_length in Hpre. apply prefix_length in Ht.
    (* PINNED, as everywhere a session's length is taken apart: a bare
       [!length_app] would split [length echo_line] too *)
    rewrite /alt_cont (length_app echo_line _)
      (length_app (line_alts !!! _ ++ _) _) (length_app (line_alts !!! _) _)
      in Hpre.
    lia. }
  rewrite !alt_seq_cons_assoc in Hpre.
  apply prefix_app_inv in Hpre.
  assert (Hset : cs' !!! 0%nat = 3%nat -> (1 < pro_rounds ps')%nat).
  { intros H3. eapply Nat.le_lt_trans; [| exact Hlt'].
    rewrite -(pro_idx_S3 cs' 0%nat H3). apply pro_idx_mono. lia. }
  destruct (alt_cont_prefix_det ps ps' cs cs' _ _ Hcs Hcs' Hps Hps' Hset
              (fun b Hb => alt_seq_app_head _ _ p t b Ht Hb) Hpre)
    as (Hhd & Hround1 & Hcont & Hrest).
  assert (Hidx1 : pro_idx cs' 1%nat = pro_idx cs 1%nat).
  { rewrite !pro_idx_S. by rewrite Hhd. }
  assert (Hlt1 : (pro_idx cs 1%nat < pro_rounds ps)%nat).
  { destruct (decide (cs !!! 0%nat = 3%nat)) as [H3 | H3].
    - rewrite (pro_idx_S3 cs 0%nat H3). cbn [pro_idx]. by apply Hround1.
    - rewrite (pro_idx_Sne cs 0%nat H3). cbn [pro_idx]. lia. }
  destruct (IH (pro_from (pro_idx cs 1%nat) ps) (pro_from (pro_idx cs' 1%nat) ps')
              (drop 1 cs) (drop 1 cs') p t' t
              (pro_from_Forall _ _ ps Hps) (pro_from_Forall _ _ ps' Hps'))
    as (Hle & Hrd & Heq).
  { rewrite pro_rounds_from.
    pose proof (pro_idx_add cs' 1%nat n) as Hadd.
    replace (1 + n)%nat with (S n) in Hadd by lia. lia. }
  { rewrite pro_rounds_from. lia. }
  { by apply cs_ok_drop. }
  { by apply cs_ok_drop. }
  { exact Ht'. }
  { exact Ht. }
  { exact Hrest. }
  split; [lia |]. split.
  { pose proof (pro_idx_add cs 1%nat n) as Hadd.
    replace (1 + n)%nat with (S n) in Hadd by lia.
    rewrite pro_rounds_from in Hrd. lia. }
  rewrite alt_seq_cons (alt_seq_cons ps cs n) Heq /alt_blk Hcont.
  reflexivity.
Qed.

(* ...AND THE SESSION TRANSCRIPTS THEMSELVES.  This is what lets lane
   ECHO-OUT feed [D2_next_input] the discipline's bound at the CLAIM's
   choice list. *)
Lemma div_lt_of_div_lt (i j p : nat) :
  0 < p -> i `div` p < j `div` p -> i < j.
Proof.
  intros Hp Hlt.
  pose proof (Nat.div_mod_eq i p) as Hi.
  pose proof (Nat.div_mod_eq j p) as Hj.
  pose proof (Nat.mod_upper_bound i p ltac:(lia)) as Hm.
  assert (Hs : p * S (i `div` p) <= p * (j `div` p))
    by (apply Nat.mul_le_mono_l; lia).
  rewrite Nat.mul_succ_r in Hs. lia.
Qed.

Lemma sess_n_prefix_det (ps ps' cs cs' : list nat) (i j : nat) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  pro_ok ps' cs' (i `div` length echo_line) ->
  Forall (fun x => x < length line_alts) cs ->
  Forall (fun x => x < length line_alts) cs' ->
  pro_pin ps cs j ->
  sess_n ps' cs' i `prefix_of` sess_n ps cs j ->
  (i <= j)%nat /\ pro_ok ps cs (i `div` length echo_line)
  /\ sess_n ps' cs' i = sess_n ps cs i.
Proof.
  intros Hps [Hps' Hlt'] Hcs Hcs' Hpin Hpre.
  pose proof (cs_ok_of_Forall _ Hcs) as Hok.
  pose proof (cs_ok_of_Forall _ Hcs') as Hok'.
  pose proof echo_line_pos as HL.
  assert (Hd' : pro_done ps') by (apply pro_done_rounds; lia).
  (* the PROLOGUES: below one wire, and the primed one is settled, so they
     are the same prologue and the unprimed one is settled too *)
  assert (Hpre0 : pro_of ps' `prefix_of` pro_of ps).
  { destruct (decide (j = 0%nat)) as [-> | Hj].
    - rewrite sess_n_0 in Hpre. etrans; [| exact Hpre].
      rewrite /sess_n. by apply prefix_app_r.
    - assert (Hd : pro_done ps).
      { apply pro_done_rounds.
        pose proof (pro_pin_at ps cs j 0%nat Hpin ltac:(lia)) as H0.
        rewrite Nat.Div0.div_0_l in H0. cbn [pro_idx] in H0. lia. }
      assert (H1 : pro_of ps' `prefix_of` sess_n ps cs j).
      { etrans; [| exact Hpre]. rewrite /sess_n. by apply prefix_app_r. }
      assert (H2 : pro_of ps `prefix_of` sess_n ps cs j)
        by (rewrite /sess_n; by apply prefix_app_r).
      destruct (prefix_weak_total _ _ _ H1 H2) as [H | H]; [exact H |].
      destruct (pro_of_prefix_free ps' ps Hps' Hps Hd H) as [_ Heq].
      by rewrite Heq. }
  destruct (pro_of_prefix_free ps ps' Hps Hps' Hd' Hpre0) as [Hdps Heq0].
  rewrite /sess_n Heq0 in Hpre. apply prefix_app_inv in Hpre.
  assert (Ht' : take (i `mod` length echo_line) echo_line `prefix_of` echo_line)
    by apply prefix_take.
  assert (Ht : take (j `mod` length echo_line) echo_line `prefix_of` echo_line)
    by apply prefix_take.
  destruct (alt_seq_prefix_det (i `div` length echo_line) ps ps' cs cs'
              (j `div` length echo_line) _ _ Hps Hps' Hlt'
              ltac:(by apply pro_done_rounds) Hok Hok' Ht' Ht Hpre)
    as (Hqle & Hround & Hqeq).
  assert (Hsess : sess_n ps' cs' i = sess_n ps cs i)
    by (rewrite /sess_n Heq0 Hqeq; reflexivity).
  split; [| split; [by split | exact Hsess]].
  destruct (decide (i `div` length echo_line < j `div` length echo_line))
    as [Hlt | Hnlt].
  - pose proof (div_lt_of_div_lt i j (length echo_line) ltac:(lia) Hlt). lia.
  - assert (Hqe : i `div` length echo_line = j `div` length echo_line) by lia.
    rewrite Hqeq Hqe in Hpre. apply prefix_app_inv in Hpre.
    apply prefix_length in Hpre. rewrite !length_take in Hpre.
    pose proof (Nat.div_mod_eq i (length echo_line)) as Hi.
    pose proof (Nat.div_mod_eq j (length echo_line)) as Hj.
    pose proof (Nat.mod_upper_bound i (length echo_line) ltac:(lia)).
    pose proof (Nat.mod_upper_bound j (length echo_line) ltac:(lia)).
    rewrite Hqe in Hi. lia.
Qed.

(* the open cycle's FULL discipline, not only D3 -- [disc_seg_open_seg]'s
   twin, and the one lane ECHO-OUT's echo step spends *)
Lemma disc_seg'_open_seg (h : list mobs) :
  trace_shape h true -> disc h -> disc_seg' (open_seg h).
Proof.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply elem_of_list_lookup in Hin as [i Hi].
  exact (Forall_lookup_1 _ _ _ _ Hd Hi).
Qed.

(* THE DISCIPLINE'S LOWER BOUND AT THE OPEN CYCLE'S LAST INPUT: D1/D2 read
   off [disc_seg'] at one index, which is what F2's [Hlow] is.  The choice
   list is the DISCIPLINE's; [sess_n_prefix_det] is what moves the bound to
   the claim's. *)
Lemma disc_seg'_pt_last (seg : list mobs) (c : bv 8) :
  disc_seg' seg -> obs_ends_in Uart0 seg c ->
  exists ps' cs' : list nat,
    pro_ok ps' cs' ((length (ins seg) - 1) `div` length echo_line)
    /\ Forall (fun x => x < length line_alts) cs'
    /\ sess_n ps' cs' (length (ins seg) - 1) `prefix_of` obs_wire Uart0 seg.
Proof.
  intros [Hd (ps & cs & Hlen & Hf & Hall)] [seg0 ->].
  exists ps, cs.
  assert (Hip : in_pres (seg0 ++ [ObsUartIn Uart0 c]) !! (length (ins seg0))
                = Some seg0).
  { rewrite in_pres_in lookup_app_r in_pres_length ?Nat.sub_diag //. }
  destruct (Hall _ _ Hip) as [Hok Hpt]. rewrite /disc_pt in Hpt.
  rewrite ins_app ins_in length_app /=.
  replace (length (ins seg0) + 1 - 1)%nat with (length (ins seg0)) by lia.
  split; [exact Hok |]. split; [exact Hf |].
  etrans; [exact Hpt |]. rewrite obs_wire_app. by eexists.
Qed.

(* [sess_n] is never empty once round 0 has settled: it begins with the
   prologue, and a settled prologue has at least its ending letter's bytes
   (an OPEN round with nothing filed predicts nothing, so the resolution
   has to be settled) *)
Lemma u_prologue_pos : 0 < length u_prologue.
Proof. vm_compute. lia. Qed.

Lemma sess_n_nonnil (ps cs : list nat) (n : nat) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> pro_done ps ->
  sess_n ps cs n <> [].
Proof.
  intros HF Hd. intros H.
  apply (f_equal length) in H. rewrite sess_n_length /= in H.
  assert (Hne : ps <> []) by (intros ->; by apply Exists_nil in Hd).
  pose proof (pro_of_pos ps HF Hne). lia.
Qed.

(* ====================================================================== *)
(*  10.  THE SAME-CYCLE BRIDGE (lane ECHO-OUT, section 7)                  *)
(*                                                                        *)
(*  The claims record their same-cycle facts at their OWN witness history  *)
(*  [ho]; the ledger's drain reads them at the run's history [h], and the  *)
(*  kernel supplies [ho `prefix_of` h] ([App.Htx]) and the era stamp at    *)
(*  both ends.  What is missing is the step from "a prefix, at the same    *)
(*  boot count" to "a prefix of the OPEN SEGMENT" -- and that is exactly   *)
(*  where the boot count earns its keep: a suffix with no PowerOn in it    *)
(*  cannot contain a PowerOff either, because the machine is ON at the     *)
(*  end and only a PowerOn turns it back on.                              *)
(* ====================================================================== *)

Lemma epu_foldl_obs_step_none (h : list mobs) :
  foldl obs_step None h = None.
Proof. induction h as [| e h IH]; [done |]. by cbn. Qed.

Lemma epu_no_power_of_boots (h : list mobs) (st : bool) :
  obs_boots h = 0%nat ->
  foldl obs_step (Some st) h = Some true ->
  st = true /\ Forall (fun e => is_io e = true) h.
Proof.
  revert st. induction h as [| e h IH]; intros st Hb Hf.
  - cbn in Hf. injection Hf as ->. split; [reflexivity | constructor].
  - destruct e as [i b | i b | |]; cbn in Hb.
    + cbn in Hf. destruct st.
      * destruct (IH true Hb Hf) as [_ HF].
        split; [reflexivity | by constructor].
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
    + cbn in Hf. destruct st.
      * destruct (IH true Hb Hf) as [_ HF].
        split; [reflexivity | by constructor].
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
    + (* ObsPowerOn *) lia.
    + (* ObsPowerOff *)
      cbn in Hf. destruct st.
      * destruct (IH false Hb Hf) as [Habs _]. discriminate.
      * rewrite epu_foldl_obs_step_none in Hf. discriminate.
Qed.

Lemma open_seg_prefix_boots (h1 h2 : list mobs) :
  h1 `prefix_of` h2 -> obs_boots h1 = obs_boots h2 ->
  trace_shape h2 true -> open_seg h1 `prefix_of` open_seg h2.
Proof.
  intros [k ->] Hb Hsh.
  assert (Hk : obs_boots k = 0%nat)
    by (rewrite obs_boots_app in Hb; lia).
  rewrite /trace_shape foldl_app in Hsh.
  destruct (foldl obs_step (Some false) h1) as [st |] eqn:Hst; last first.
  { rewrite epu_foldl_obs_step_none in Hsh. discriminate. }
  destruct (epu_no_power_of_boots k st Hk Hsh) as [_ HF].
  rewrite (open_seg_io h1 k HF). by eexists.
Qed.

Lemma ins_prefix_of (s1 s2 : list mobs) :
  s1 `prefix_of` s2 -> ins s1 `prefix_of` ins s2.
Proof. intros [z ->]. rewrite ins_app. by eexists. Qed.
