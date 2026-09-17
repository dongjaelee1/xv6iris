(* FileOutPure.v -- THE FILE APPLICATION'S STAGE MACHINE, PURE.

   Design of record: claude-notes/design/app-file.md section 4 ("The console
   side"), deliverable 1.  This file is [EchoOutPure.v]'s twin at
   [FileDisc.sessf]: the same stage machine, with the ERA'S BOOT FILE STATE
   threaded through every block.  Iris-free, over [FileDisc]/[EchoDisc]/
   [ConsLog], so the Iris lane only has to APPLY lemmas.

   WHAT CHANGES, AND WHAT DOES NOT.

   - [pending_f ps cs f0 I] and [D_f ps cs f0 E] are [EchoOutPure.pending_at]
     and [D] with the era's boot state carried.  The state is an
     [option fst]: [None] means "the era has not filed its boot state yet",
     which is the state the stage is born in and which -- by the claim's own
     [feout_pure] -- only ever occurs at the EMPTY stage, where the boot
     state is not read.  [f0_st] reads it as a state.
   - the range condition that was [Forall (fun c => c < 4) cs] is
     [alts_pre I cs]: every entry the choice list HAS is an alternative the
     LINE AT THAT INDEX admits.  It is a pointwise condition and not
     [FileDisc.alts_ok], because the list runs one short at a block boundary
     (a program files its alternative at the block's FIRST byte, which is
     after the echo that completed the line).  [alts_pad] fills it out, which
     is what lets the determinacy theorem -- stated at a FULL resolution --
     be applied to a stage standing at a boundary.
   - [EchoOutPure]'s [cs_ok] is gone with it: out of range [!!!] reads [0],
     which decodes to [FileDisc.REcho 0], and THAT IS NOT AN ALTERNATIVE A
     [cat f] LINE ADMITS.  So no total condition on [cs] can replace it, and
     the padding is the honest fix.
   - the prologue counter is [FileDisc.pro_idx_f] (it counts [RFFork] and
     [RCFork] beside [REcho 3]) and the side condition is [pro_ok_f] /
     [pro_pin_f].

   TWO BOOT STATES, NOT ONE.  [FileDisc.sessf_prefix_det] fixes one boot
   state for both witnesses; the claim needs the DISCIPLINE's witness (which
   the tag hands over, at a state the trace predicate chose existentially)
   compared against ITS OWN (which init filed off the deed).  There is no
   reason for the two to be equal, and none is needed:
   [FileDisc.alt_seq_f_prefix_det] already takes the two states apart, and
   [sessf_prefix_det2] below is [sessf_prefix_det] at two of them.  The
   conclusion is an equality of BYTES, which is all the claim ever spends.

   THE DISCIPLINE'S CLOSURE LAWS are here too ([disc_f_out], [disc_f_in],
   [disc_f_power], [disc_f_other], [disc_f_prefix]): [FileDisc] landed
   [disc_input_f]'s full set and none of [disc_f]'s, and the ledger's three
   steps are stated at exactly these. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import ObsTrace.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import FileDisc.
(* as in EchoDisc / EchoOutPure: a pure file does not inherit ssreflect's
   [rewrite] from the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* [FileState.fst] shadows the pair projection, so NOTHING below writes
   [x.1]: the histories of E's entries are read with [Datatypes.fst].
   [snd] is untouched. *)
Local Notation ehist := (@Datatypes.fst (list mobs) (bv 8)).

(* ====================================================================== *)
(*  1.  THE BYTES OF A DISCIPLINED FILE-APPLICATION INPUT                  *)
(* ====================================================================== *)

(* every byte of a disciplined input is a body byte, a '>' or the newline --
   [EchoDisc.disc_input_byte] with [fbody_byte] where [wl_body_byte] was *)
Lemma disc_input_f_byte (I : list (bv 8)) (b : bv 8) :
  disc_input_f I -> b ∈ I -> fbody_byte b \/ b = wl_nl.
Proof using.
  intros Hd Hin. pose proof Hd as (Hb & Hr & _).
  rewrite (wl_cut_join I) in Hin.
  apply elem_of_app in Hin as [Hin | Hin].
  - destruct (join_elem_of (bodies_of I) b Hin) as [-> | (l & Hl & Hbl)];
      [by right | left].
    apply elem_of_list_lookup in Hl as [k Hk].
    pose proof (fbody_ok_bytes l (disc_input_f_body I k l Hd Hk)) as Hfb.
    exact (proj1 (Forall_forall _ _) Hfb b Hbl).
  - left. exact (proj1 (Forall_forall _ _) Hr b Hin).
Qed.

Lemma wl_gt_val : bv_unsigned wl_gt = 62%Z.
Proof using. by vm_compute. Qed.

(* [EchoOutPure.echo_byte_ne] is [Local]; this is that step, which is what
   turns every refutation below into one [lia] against the byte reading *)
Local Lemma fop_byte_ne (c : bv 8) (z : Z) :
  bv_unsigned c <> z ->
  bv_unsigned (mword_of_int z : mword 8) = z ->
  eq_vec (c : mword 8) (mword_of_int z : mword 8) = false.
Proof using.
  intros Hne Hz. apply eq_vec_false_iff. intro Hq.
  apply (f_equal bv_unsigned) in Hq. rewrite Hz in Hq. exact (Hne Hq).
Qed.

Lemma disc_input_f_byte_val (I : list (bv 8)) (b : bv 8) :
  disc_input_f I -> b ∈ I ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z \/ bv_unsigned b = 62%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof using.
  intros Hd Hin. destruct (disc_input_f_byte I b Hd Hin) as [[[Ha | ->] | ->] | ->].
  - destruct Ha as [H | [H | H]];
      [ right; right; right; by left
      | right; right; right; right; by left
      | right; right; right; right; by right ].
  - right. left. exact wl_sp_val.
  - right. right. left. exact wl_gt_val.
  - left. exact wl_nl_val.
Qed.

(* A DISCIPLINED INPUT HOLDS NO '\r', NO ERASE BYTE AND NO ^D, exactly as
   [EchoOutPure.disc_byte_ok] says for the echo application: the third
   clause refutes the read path's SWALLOW arm and the second the gap
   clause's erase disjunct. *)
Lemma disc_byte_ok_f (I : list (bv 8)) (c : bv 8) :
  disc_input_f I -> c ∈ I ->
  c <> (mword_of_int 13 : mword 8) /\ cons_erase c = false
  /\ bv_unsigned c <> 4%Z.
Proof using.
  intros Hd Hc. pose proof (disc_input_f_byte_val I c Hd Hc) as Hv.
  split_and!.
  - intro Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
      [lia | by vm_compute].
  - rewrite /cons_erase.
    rewrite (fop_byte_ne c 21 ltac:(lia) ltac:(by vm_compute)).
    rewrite (fop_byte_ne c 8 ltac:(lia) ltac:(by vm_compute)).
    rewrite (fop_byte_ne c 127 ltac:(lia) ltac:(by vm_compute)).
    reflexivity.
  - lia.
Qed.

Lemma echo_of_disc_f (I : list (bv 8)) (c : bv 8) :
  disc_input_f I -> c ∈ I -> echo_of c = c.
Proof using. intros Hd Hc. apply echo_of_other, (disc_byte_ok_f I c Hd Hc). Qed.

Lemma disc_seg_f_last_in (h : list mobs) (c : bv 8) :
  disc_seg_f h -> obs_ends_in Uart0 h c -> c ∈ ins h.
Proof using.
  intros _ [h0 ->]. rewrite ins_app ins_in.
  apply elem_of_app. right. apply elem_of_list_here.
Qed.

Lemma disc_seg_f_no_erase (h : list mobs) (c : bv 8) :
  disc_seg_f h -> obs_ends_in Uart0 h c -> cons_erase c = false.
Proof using.
  intros Hd He.
  apply (disc_byte_ok_f (ins h) c Hd (disc_seg_f_last_in h c Hd He)).
Qed.

Lemma disc_seg_f_no_ctrl_d (h : list mobs) (c : bv 8) :
  disc_seg_f h -> obs_ends_in Uart0 h c -> bv_unsigned c <> 4%Z.
Proof using.
  intros Hd He.
  apply (disc_byte_ok_f (ins h) c Hd (disc_seg_f_last_in h c Hd He)).
Qed.

(* ====================================================================== *)
(*  1b.  THE DISCIPLINE'S CLOSURE LAWS                                     *)
(*                                                                        *)
(*  [FileDisc] landed [disc_input_f]'s full set and none of [disc_f]'s.    *)
(*  The ledger's power, output and input steps are stated at exactly       *)
(*  these, on [EchoDisc.disc_other]/[disc_out]/[disc_power]/[disc_in]'s    *)
(*  own statements.                                                        *)
(* ====================================================================== *)

(* the choice list restricted to the lines a PREFIX of the input has *)
Lemma lines_of_prefix (I I' : list (bv 8)) :
  I `prefix_of` I' -> lines_of I `prefix_of` lines_of I'.
Proof using.
  intros Hp. destruct (bodies_of_prefix I I' Hp) as [z Hz].
  rewrite /lines_of Hz fmap_app. by eexists.
Qed.

Lemma lines_of_length (I : list (bv 8)) : length (lines_of I) = nlines I.
Proof using. by rewrite /lines_of length_fmap. Qed.

Lemma alts_ok_take (I I' : list (bv 8)) (cs : list nat) :
  I' `prefix_of` I -> alts_ok I cs -> alts_ok I' (take (nlines I') cs).
Proof using.
  intros Hp Ha.
  pose proof (alts_ok_length I cs Ha) as Hlen.
  assert (Hle : (nlines I' <= nlines I)%nat) by (by apply nlines_prefix).
  assert (Hl' : lines_of I' = take (nlines I') (lines_of I)).
  { destruct (lines_of_prefix I' I Hp) as [z Hz].
    rewrite Hz take_app_length'; [reflexivity | by rewrite lines_of_length]. }
  rewrite /alts_ok Hl'. apply Forall2_take. exact Ha.
Qed.

Lemma disc_seg_f'_other (s : fst) (seg : list mobs) (e : mobs) :
  not_cons_in e -> disc_seg_f' s (seg ++ [e]) <-> disc_seg_f' s seg.
Proof using.
  intro He.
  assert (Hi : in_pres (seg ++ [e]) = in_pres seg)
    by (by apply in_pres_snoc_other).
  assert (Hn : ins (seg ++ [e]) = ins seg)
    by (rewrite ins_app (ins_snoc_other e He) app_nil_r; reflexivity).
  rewrite /disc_seg_f' /disc_seg_f Hi Hn. done.
Qed.

Lemma disc_seg_f'_out (s : fst) (seg : list mobs) (i : uart_id) (b : bv 8) :
  disc_seg_f' s (seg ++ [ObsUartOut i b]) <-> disc_seg_f' s seg.
Proof using. apply disc_seg_f'_other. by destruct i. Qed.

Lemma disc_f_other (h : list mobs) (e : mobs) :
  is_io e = true -> not_cons_in e -> trace_shape h true ->
  disc_f (h ++ [e]) <-> disc_f h.
Proof using.
  intros Hio He Hsh.
  destruct (cycles_of_io h [e] Hsh) as (cs & Hc & Hc'); [by constructor |].
  rewrite /disc_f Hc Hc' !Forall_app !Forall_singleton.
  assert (Hiff : (exists s : fst, fst_ok s /\ disc_seg_f' s (open_seg h ++ [e]))
                 <-> (exists s : fst, fst_ok s /\ disc_seg_f' s (open_seg h))).
  { split; intros (s & Hs & Hd); exists s; split; [exact Hs | | exact Hs |];
      by apply (disc_seg_f'_other s (open_seg h) e He). }
  rewrite Hiff. done.
Qed.

Lemma disc_f_out (h : list mobs) (i : uart_id) (b : bv 8) :
  trace_shape h true -> disc_f (h ++ [ObsUartOut i b]) <-> disc_f h.
Proof using.
  intro Hsh. apply disc_f_other; [by destruct i | by destruct i | exact Hsh].
Qed.

Lemma disc_f_power (h : list mobs) (on : bool) :
  disc_f (h ++ [if on then ObsPowerOff else ObsPowerOn]) <-> disc_f h.
Proof using.
  rewrite /disc_f. destruct on.
  - by rewrite cycles_of_off.
  - rewrite cycles_of_on Forall_app Forall_singleton.
    split; [by intros [? _] |].
    intros ?. split; [done |]. exists None. split; [exact I |].
    exact (disc_seg_f'_nil None).
Qed.

(* THE INPUT STEP.  [EchoDisc.disc_seg'_in]'s twin: dropping the last input
   byte drops at most one line, so the witness resolution is TRUNCATED --
   [FileDisc.sessf_take] then says the shorter transcript is the same
   bytes, and [alts_ok_take] that the truncation is still a resolution. *)
Lemma disc_seg_f'_in (s : fst) (seg : list mobs) (b : bv 8) :
  disc_seg_f' s (seg ++ [ObsUartIn Uart0 b]) -> disc_seg_f' s seg.
Proof using.
  intros [Hd (ps & cs & Hl & Hall)].
  rewrite /disc_seg_f ins_app ins_in in Hd.
  rewrite ins_app ins_in in Hl.
  assert (Hpre : ins seg `prefix_of` (ins seg ++ [b])) by (by eexists).
  assert (Hle : (nlines (ins seg) <= nlines (ins seg ++ [b]))%nat)
    by (by apply nlines_prefix).
  split; [exact (disc_input_f_prefix _ _ Hpre Hd) |].
  exists ps, (take (nlines (ins seg)) cs).
  split; [exact (alts_ok_take _ _ cs Hpre Hl) |].
  intros p Hp.
  assert (Hpin : p ∈ in_pres (seg ++ [ObsUartIn Uart0 b])).
  { rewrite in_pres_in. apply elem_of_app. by left. }
  destruct (Hall p Hpin) as [[HF Hlt] Hpt].
  assert (Hplt : (nlines (ins p) <= nlines (ins seg))%nat).
  { apply nlines_prefix, ins_prefix.
    exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp). }
  split.
  - rewrite /pro_ok_f. split; [exact HF |].
    rewrite (pro_idx_f_ext (take (nlines (ins seg)) cs) cs (nlines (ins p)));
      [exact Hlt | | lia].
    intros j Hj. rewrite list_lookup_total_alt lookup_take; [| lia].
    by rewrite -list_lookup_total_alt.
  - rewrite /disc_pt_f (sessf_take ps cs s (ins p) _ Hplt). exact Hpt.
Qed.

Lemma disc_f_in (h : list mobs) (b : bv 8) :
  trace_shape h true -> disc_f (h ++ [ObsUartIn Uart0 b]) -> disc_f h.
Proof using.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartIn Uart0 b] Hsh) as (cs & Hc & Hc');
    [by constructor |].
  rewrite /disc_f Hc Hc' !Forall_app !Forall_singleton.
  intros [Hall (s & Hs & Hseg)]. split; [exact Hall |].
  exists s. split; [exact Hs | exact (disc_seg_f'_in s _ _ Hseg)].
Qed.

Lemma disc_f_snoc (h : list mobs) (e : mobs) : disc_f (h ++ [e]) -> disc_f h.
Proof using.
  rewrite /disc_f /cycles_of !Forall_rev_iff cycles_rev_app /=.
  destruct e as [i b | i b | |]; cbn.
  - destruct (cycles_rev h) as [| c cs]; [by intros _ |].
    rewrite !Forall_cons. intros [(s & Hs & Hseg) Hall].
    split; [| exact Hall]. exists s. split; [exact Hs |].
    destruct i.
    + exact (disc_seg_f'_in s c b Hseg).
    + apply (disc_seg_f'_other s c (ObsUartIn Uart1 b) I). exact Hseg.
  - destruct (cycles_rev h) as [| c cs]; [by intros _ |].
    rewrite !Forall_cons. intros [(s & Hs & Hseg) Hall].
    split; [| exact Hall]. exists s. split; [exact Hs |].
    apply (disc_seg_f'_out s c i b). exact Hseg.
  - rewrite Forall_cons. by intros [_ ?].
  - done.
Qed.

Lemma disc_f_prefix (h' h : list mobs) :
  h' `prefix_of` h -> disc_f h -> disc_f h'.
Proof using.
  intros [k ->]. induction k as [| e k IH] using rev_ind; intros Hd.
  - by rewrite app_nil_r in Hd.
  - apply IH. rewrite app_assoc in Hd. exact (disc_f_snoc _ _ Hd).
Qed.

(* the open cycle of a disciplined history keeps D3, and the whole per-cycle
   discipline with its boot state -- [EchoOutPure.disc_seg_open_seg] and
   [disc_seg'_open_seg]'s twins *)
Lemma disc_seg_f'_open_seg (h : list mobs) :
  trace_shape h true -> disc_f h ->
  exists s : fst, fst_ok s /\ disc_seg_f' s (open_seg h).
Proof using.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply elem_of_list_lookup in Hin as [i Hi].
  exact (Forall_lookup_1 _ _ _ _ Hd Hi).
Qed.

Lemma disc_seg_f_open_seg (h : list mobs) :
  trace_shape h true -> disc_f h -> disc_seg_f (open_seg h).
Proof using.
  intros Hsh Hd. destruct (disc_seg_f'_open_seg h Hsh Hd) as (s & _ & Hs & _).
  exact Hs.
Qed.

(* ====================================================================== *)
(*  2.  THE STAGE MACHINE: [pending_f] AND [D_f]                           *)
(* ====================================================================== *)

(* the era's boot state, as the stage carries it: [None] until the era's
   first process byte files it.  Read as a state it is [FileDisc]'s absent
   file -- which is only ever read at the empty stage, where the claim's
   [feout_pure] pins the stage's input and written bytes to be empty. *)
Definition f0_st (f0 : option fst) : fst := default None f0.

Lemma f0_st_some (s : fst) : f0_st (Some s) = s.
Proof using. reflexivity. Qed.

Definition pending_at_f (ps cs : list nat) (f0 : option fst)
    (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then pro_of ps
  else if decide (rest_of I = [])
       then alt_cont_f ps cs (f0_st f0) (bodies_of I) (nlines I - 1) else [].

Definition pending_f (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) : list (bv 8) :=
  pending_at_f ps cs f0 (snd <$> E).

(* THE TRANSCRIPT DUE AFTER E's LAST ECHO.  [EchoOutPure.D_from]'s twin --
   structural on [E] from the LEFT with the input read so far as the
   accumulator, for the same reason ([cbn] reduces it on every [x :: E']). *)
Fixpoint D_from_f (ps cs : list nat) (f0 : option fst) (pre : list (bv 8))
    (E : list (list mobs * bv 8)) : list (bv 8) :=
  match E with
  | [] => []
  | x :: E' => pending_at_f ps cs f0 pre ++ [echo_of x.2]
               ++ D_from_f ps cs f0 (pre ++ [x.2]) E'
  end.

Definition D_f (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) : list (bv 8) := D_from_f ps cs f0 [] E.

Lemma D_f_nil ps cs f0 : D_f ps cs f0 [] = [].
Proof using. reflexivity. Qed.

Lemma pending_at_f_nil ps cs f0 : pending_at_f ps cs f0 [] = pro_of ps.
Proof using.
  rewrite /pending_at_f. case_decide as H; [done | by destruct (H eq_refl)].
Qed.

Lemma pending_f_nil ps cs f0 : pending_f ps cs f0 [] = pro_of ps.
Proof using. rewrite /pending_f fmap_nil. exact (pending_at_f_nil ps cs f0). Qed.

(* the round pointer a block-opening stage stands at *)
Lemma pro_idx_f_nlines (cs : list nat) (I : list (bv 8)) :
  I <> [] -> rest_of I = [] ->
  ralt_panic (ralt_at cs (nlines I - 1)) = true ->
  S (pro_idx_f cs (nlines I - 1)) = pro_idx_f cs (nlines I).
Proof using.
  intros H0 Hm H3. pose proof (nlines_pos_of_rest_nil I H0 Hm) as Hq.
  replace (nlines I) with (S (nlines I - 1))%nat at 2 by lia.
  symmetry. by apply pro_idx_f_Sp.
Qed.

Lemma pending_at_f_ps_ext ps ps' cs f0 I :
  ps `prefix_of` ps' ->
  (pro_idx_f cs (nlines I) < pro_rounds ps)%nat ->
  pending_at_f ps cs f0 I = pending_at_f ps' cs f0 I.
Proof using.
  intros Hp Hr. rewrite /pending_at_f. case_decide as H0.
  { subst I. apply (pro_of_from_done_ext 0%nat); [exact Hp |].
    rewrite nlines_nil in Hr. cbn [pro_idx_f] in Hr. exact Hr. }
  case_decide as Hm; [| done].
  rewrite /alt_cont_f. f_equal.
  destruct (ralt_panic (ralt_at cs (nlines I - 1))) eqn:H3; [| done].
  rewrite (pro_idx_f_nlines cs I H0 Hm H3).
  by apply pro_of_from_done_ext.
Qed.

Lemma pending_at_f_ps_mono ps ps' cs f0 I :
  ps `prefix_of` ps' -> pending_at_f ps cs f0 I `prefix_of` pending_at_f ps' cs f0 I.
Proof using.
  intros Hp. rewrite /pending_at_f. case_decide as H0.
  { by apply pro_of_mono. }
  case_decide as Hm; [| reflexivity].
  rewrite /alt_cont_f. apply prefix_app.
  destruct (ralt_panic (ralt_at cs (nlines I - 1))); [| reflexivity].
  by apply pro_of_from_mono.
Qed.

Lemma pending_f_ps_mono ps ps' cs f0 E :
  ps `prefix_of` ps' -> pending_f ps cs f0 E `prefix_of` pending_f ps' cs f0 E.
Proof using. intro Hp. by apply pending_at_f_ps_mono. Qed.

(* THE ROUND-OPENING BLOCK'S SHAPE, [EchoOutPure.pending_at_round_pre]'s
   twin: the panic line (a CONSTANT) and then that round's prologue. *)
Lemma pending_at_f_round_pre (ps cs : list nat) (f0 : option fst)
    (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)) = true) ->
  pending_at_f ps cs f0 I
  = (if decide (I = []) then [] else alt_panic)
    ++ pro_of (pro_from (pro_idx_f cs (nlines I)) ps).
Proof using.
  intros Hm Hopen. rewrite /pending_at_f. case_decide as H0.
  - subst I. rewrite nlines_nil. by cbn [pro_idx_f pro_from app].
  - rewrite decide_True; [| exact Hm].
    assert (H3 : ralt_panic (ralt_at cs (nlines I - 1)) = true)
      by (destruct Hopen as [Hn | H3]; [by destruct (H0 Hn) | exact H3]).
    rewrite /alt_cont_f H3 (pro_idx_f_nlines cs I H0 Hm H3).
    by rewrite (cont_panic _ _ _ H3).
Qed.

Lemma pro_pin_f_round_le (ps cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)) = true) ->
  pro_pin_f ps cs I ->
  (pro_idx_f cs (nlines I) <= pro_rounds ps)%nat.
Proof using.
  intros Hm Ho Hpin. destruct (decide (I = [])) as [-> | Hn0].
  { rewrite nlines_nil. cbn [pro_idx_f]. lia. }
  assert (H3 : ralt_panic (ralt_at cs (nlines I - 1)) = true)
    by (destruct Ho as [Hz | H3]; [by destruct (Hn0 Hz) | exact H3]).
  pose proof (nlines_pos_of_rest_nil I Hn0 Hm) as Hq.
  pose proof (pro_idx_f_nlines cs I Hn0 Hm H3) as Hs.
  assert (Hlt : (nlines I - 1 < nstarted I)%nat)
    by (pose proof (nlines_le_nstarted I); lia).
  pose proof (Hpin (nlines I - 1)%nat Hlt). lia.
Qed.

Lemma pending_at_f_round_det (ps ps' cs : list nat) (f0 : option fst)
    (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)) = true) ->
  pending_at_f ps cs f0 I = pending_at_f ps' cs f0 I ->
  pro_of (pro_from (pro_idx_f cs (nlines I)) ps)
  = pro_of (pro_from (pro_idx_f cs (nlines I)) ps').
Proof using.
  intros Hm Hopen Heq.
  rewrite (pending_at_f_round_pre ps cs f0 I Hm Hopen) in Heq.
  rewrite (pending_at_f_round_pre ps' cs f0 I Hm Hopen) in Heq.
  by apply app_inv_head in Heq.
Qed.

(* ---- the append laws ---- *)

Lemma D_from_f_pending_ext ps ps' cs f0 pre E :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ (snd <$> E) ->
     J <> pre ++ (snd <$> E) ->
     pending_at_f ps cs f0 J = pending_at_f ps' cs f0 J) ->
  D_from_f ps cs f0 pre E = D_from_f ps' cs f0 pre E.
Proof using.
  revert pre. induction E as [| x E IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [x.2]) ++ (snd <$> E) = pre ++ (snd <$> (x :: E)))
    by (by rewrite fmap_cons epu_app_snoc).
  assert (Hhere : pending_at_f ps cs f0 pre = pending_at_f ps' cs f0 pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - rewrite fmap_cons. apply (epu_app_cons_ne pre x.2 (snd <$> E)). }
  cbn [D_from_f]. rewrite Hhere. do 2 f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma D_f_ps_ext ps ps' cs f0 E :
  ps `prefix_of` ps' -> pro_pin_f ps cs (snd <$> E) ->
  D_f ps cs f0 E = D_f ps' cs f0 E.
Proof using.
  intros Hp Hpin. rewrite /D_f. apply D_from_f_pending_ext.
  intros J H1 H2 H3. rewrite app_nil_l in H2, H3.
  apply (pending_at_f_ps_ext ps ps' cs f0 J Hp).
  apply Hpin. exact (nstarted_strict J (snd <$> E) H2 H3).
Qed.

Lemma D_from_f_app ps cs f0 pre E1 E2 :
  D_from_f ps cs f0 pre (E1 ++ E2)
  = D_from_f ps cs f0 pre E1 ++ D_from_f ps cs f0 (pre ++ (snd <$> E1)) E2.
Proof using.
  revert pre. induction E1 as [| x E1 IH]; intros pre.
  - cbn [D_from_f app]. by rewrite fmap_nil app_nil_r.
  - change ((x :: E1) ++ E2) with (x :: (E1 ++ E2)).
    cbn [D_from_f]. rewrite (IH (pre ++ [x.2])) fmap_cons epu_app_snoc.
    by rewrite -!app_assoc.
Qed.

Lemma D_f_app ps cs f0 E x :
  D_f ps cs f0 (E ++ [x]) = D_f ps cs f0 E ++ pending_f ps cs f0 E ++ [echo_of x.2].
Proof using.
  rewrite /D_f /pending_f D_from_f_app app_nil_l /=. by rewrite ?app_nil_r.
Qed.

(* ====================================================================== *)
(*  3.  WHAT THE CLAIM SAYS ABOUT [E]                                      *)
(* ====================================================================== *)

(* E's INDEX LAW is [EchoOutPure.E_index] verbatim (it names no discipline);
   its CONTENT LAW is D3 for the file application. *)
Definition E_disc_f (E : list (list mobs * bv 8)) : Prop :=
  disc_input_f (snd <$> E).

Lemma E_disc_f_take (E : list (list mobs * bv 8)) (n : nat) :
  E_disc_f E -> E_disc_f (take n E).
Proof using.
  rewrite /E_disc_f. intro HE.
  exact (disc_input_f_prefix _ _ (epu_fmap_prefix snd _ _ (prefix_take _ _)) HE).
Qed.

Lemma E_disc_f_app_l (E : list (list mobs * bv 8)) (x : list mobs * bv 8) :
  E_disc_f (E ++ [x]) -> E_disc_f E.
Proof using.
  rewrite /E_disc_f fmap_app. intro H.
  exact (disc_input_f_prefix _ _ ltac:(by eexists) H).
Qed.

Lemma E_disc_f_echo (E : list (list mobs * bv 8)) (j : nat)
    (x : list mobs * bv 8) :
  E_disc_f E -> E !! j = Some x -> echo_of x.2 = x.2.
Proof using.
  intros HE Hx. apply (echo_of_disc_f (snd <$> E) x.2 HE).
  apply elem_of_list_lookup_2 with j. by rewrite list_lookup_fmap Hx.
Qed.

Lemma E_disc_f_of_hist (E : list (list mobs * bv 8)) (Sg : list mobs) :
  E_index E ->
  (forall j x, E !! j = Some x -> ehist x `prefix_of` Sg) ->
  disc_input_f (ins Sg) -> E_disc_f E.
Proof using.
  intros Hidx Hpre Hd.
  pose proof (E_length_le_hist E Sg Hidx Hpre) as Hlen.
  rewrite /E_disc_f (E_bytes_of_hist E Sg Hidx Hpre Hlen).
  exact (disc_input_f_prefix _ _ (prefix_take _ _) Hd).
Qed.

(* ====================================================================== *)
(*  4.  F1 -- THE STAGE IS BELOW THE SESSION                               *)
(* ====================================================================== *)

Lemma D_f_pending_sessf (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) :
  E_disc_f E ->
  D_f ps cs f0 E ++ pending_f ps cs f0 E = sessf ps cs (f0_st f0) (snd <$> E).
Proof using.
  induction E as [| x E IH] using rev_ind; intros HE.
  - by rewrite D_f_nil pending_f_nil app_nil_l fmap_nil sessf_nil.
  - pose proof (E_disc_f_app_l E x HE) as HE0.
    pose proof (IH HE0) as IH'. rewrite /pending_f in IH'.
    assert (Hb : echo_of x.2 = x.2).
    { apply (E_disc_f_echo (E ++ [x]) (length E) x HE).
      rewrite lookup_app_r; [by rewrite Nat.sub_diag | lia]. }
    assert (Hfm : (snd <$> (E ++ [x])) = (snd <$> E) ++ [x.2])
      by (by rewrite fmap_app).
    rewrite D_f_app /pending_f Hfm Hb.
    rewrite (app_assoc (D_f ps cs f0 E) (pending_at_f ps cs f0 (snd <$> E)) [x.2])
            IH'.
    destruct (decide (x.2 = wl_nl)) as [Hnl | Hnl].
    + assert (Hp : pending_at_f ps cs f0 ((snd <$> E) ++ [x.2])
                   = alt_cont_f ps cs (f0_st f0)
                       (bodies_of (snd <$> E) ++ [rest_of (snd <$> E)])
                       (nlines (snd <$> E))).
      { rewrite Hnl /pending_at_f. case_decide as H1.
        { exfalso. apply (f_equal length) in H1.
          rewrite (length_app (snd <$> E) [wl_nl]) in H1.
          cbn [length] in H1. lia. }
        rewrite decide_True; [| exact (rest_of_snoc_nl (snd <$> E))].
        rewrite bodies_of_snoc_nl nlines_snoc_nl.
        by replace (S (nlines (snd <$> E)) - 1)%nat
          with (nlines (snd <$> E)) by lia. }
      rewrite Hp Hnl sessf_snoc_nl.
      by rewrite -(app_assoc (sessf ps cs (f0_st f0) (snd <$> E)) [wl_nl] _).
    + assert (Hp : pending_at_f ps cs f0 ((snd <$> E) ++ [x.2]) = []).
      { rewrite /pending_at_f. case_decide as H1.
        { exfalso. apply (f_equal length) in H1.
          rewrite (length_app (snd <$> E) [x.2]) in H1.
          cbn [length] in H1. lia. }
        rewrite decide_False; [done |].
        rewrite (rest_of_snoc_other (snd <$> E) x.2 Hnl).
        intro Hq. apply (f_equal length) in Hq.
        rewrite (length_app (rest_of (snd <$> E)) [x.2]) in Hq.
        cbn [length] in Hq. lia. }
      rewrite Hp app_nil_r (sessf_snoc_other ps cs (f0_st f0) (snd <$> E) x.2 Hnl).
      reflexivity.
Qed.

Lemma D_f_stage_prefix (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) (w : list (bv 8)) :
  E_disc_f E -> w `prefix_of` pending_f ps cs f0 E ->
  (D_f ps cs f0 E ++ w) `prefix_of` sessf ps cs (f0_st f0) (snd <$> E).
Proof using.
  intros HE Hw. rewrite -(D_f_pending_sessf ps cs f0 E HE).
  by apply prefix_app, Hw.
Qed.

(* ====================================================================== *)
(*  5.  F2 -- THE NEXT ECHO IS THE NEXT INPUT                              *)
(* ====================================================================== *)

(* the session grows STRICTLY with the input -- [EchoDisc.sess_length_lt]'s
   twin, which [FileDisc] does not state *)
Lemma sessf_length_step (ps cs : list nat) (s : fst) (I : list (bv 8))
    (b : bv 8) :
  (length (sessf ps cs s I) < length (sessf ps cs s (I ++ [b])))%nat.
Proof using.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite sessf_snoc_nl length_app. cbn [length]. lia.
  - rewrite (sessf_snoc_other ps cs s I b Hb) length_app. cbn [length]. lia.
Qed.

Lemma sessf_length_lt (ps cs : list nat) (s : fst) (I I' : list (bv 8)) :
  I `prefix_of` I' -> I <> I' ->
  (length (sessf ps cs s I) < length (sessf ps cs s I'))%nat.
Proof using.
  intros [k Hk] Hne. destruct k as [| b k].
  { exfalso. apply Hne. by rewrite Hk app_nil_r. }
  assert (Hp : (I ++ [b]) `prefix_of` I')
    by (exists k; by rewrite Hk -app_assoc).
  pose proof (prefix_length _ _ (sessf_mono ps cs s _ _ Hp)) as Hle.
  pose proof (sessf_length_step ps cs s I b). lia.
Qed.

(* F2, [EchoOutPure.D2_next_input]'s twin at the file session. *)
Lemma D2_next_input_f (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) (w W : list (bv 8)) (h : list mobs)
    (c : bv 8) (m : nat) :
  E_disc_f E -> E_index E ->
  (forall x, x ∈ E -> hist_ext (ehist x) h) ->
  obs_ends_in Uart0 h c ->
  length (ins h) = m ->
  w `prefix_of` pending_f ps cs f0 E ->
  sessf ps cs (f0_st f0) (take (m - 1)%nat (ins h)) `prefix_of` W ->
  W `prefix_of` (D_f ps cs f0 E ++ w) ->
  m = S (length E) /\ w = pending_f ps cs f0 E.
Proof using.
  intros HEb HEi Hnew Hends Hm Hw Hlow Hup.
  assert (Hm1 : (1 <= m)%nat).
  { destruct Hends as [h0 Hh0]. rewrite -Hm Hh0 ins_app ins_in.
    rewrite (length_app (ins h0) [c]). cbn [length]. lia. }
  assert (Hprefix : forall j x, E !! j = Some x -> ehist x `prefix_of` h).
  { intros j x Hx. apply (Hnew x). by eapply elem_of_list_lookup_2. }
  pose proof (E_length_le_hist E h HEi Hprefix) as HlenE.
  pose proof (E_bytes_of_hist E h HEi Hprefix HlenE) as HEq.
  assert (Hboth : sessf ps cs (f0_st f0) (take (m - 1)%nat (ins h))
                  `prefix_of` sessf ps cs (f0_st f0) (take (length E) (ins h))).
  { rewrite -HEq. etrans; [exact Hlow |]. etrans; [exact Hup |].
    by apply D_f_stage_prefix. }
  assert (Hle : (m - 1 <= length E)%nat).
  { destruct (decide (m - 1 <= length E)%nat) as [? | Hgt]; [done | exfalso].
    apply prefix_length in Hboth.
    assert (Hpr : take (length E) (ins h) `prefix_of` take (m - 1)%nat (ins h))
      by (apply prefix_take_le; lia).
    assert (Hne : take (length E) (ins h) <> take (m - 1)%nat (ins h)).
    { intro Hq. apply (f_equal length) in Hq.
      rewrite !length_take in Hq. lia. }
    pose proof (sessf_length_lt ps cs (f0_st f0) (take (length E) (ins h))
                  (take (m - 1)%nat (ins h)) Hpr Hne). lia. }
  assert (Heq : (m - 1)%nat = length E).
  { destruct (decide ((m - 1)%nat = length E)) as [? | Hne]; [done | exfalso].
    assert (Hlt : (m - 1 < length E)%nat) by lia.
    destruct (lookup_lt_is_Some_2 E (m - 1)%nat Hlt) as [x Hx].
    destruct (HEi (m - 1)%nat x Hx) as [Hxe Hxlen].
    assert (Hxin : x ∈ E) by (by eapply elem_of_list_lookup_2).
    destruct (Hnew x Hxin) as [Hpre Hlen'].
    assert (Hsame : ehist x = h).
    { eapply ins_hist_agree; [exact Hpre | exact Hxe | exact Hends |]. lia. }
    rewrite Hsame in Hlen'. lia. }
  split; [lia |].
  apply (anti_symm prefix); [exact Hw |].
  eapply (prefix_app_cancel (D_f ps cs f0 E)).
  rewrite (D_f_pending_sessf ps cs f0 E HEb) HEq -Heq.
  etrans; [exact Hlow | exact Hup].
Qed.

(* ====================================================================== *)
(*  6.  THE CHOICE LIST: A POINTWISE RANGE CONDITION, AND ITS PADDING      *)
(* ====================================================================== *)

(* WHAT THE STAGE CARRIES.  [FileDisc.alts_ok] is a [Forall2] against ALL of
   [lines_of I] and so pins [length cs = nlines I]; the stage's list runs one
   short at a block boundary, so what it carries is this pointwise reading. *)
Definition alts_pre (I : list (bv 8)) (cs : list nat) : Prop :=
  forall (i : nat) (c : nat),
    cs !! i = Some c ->
    (i < nlines I)%nat
    /\ ralt_ok (uline_of (bodies_of I !!! i)) (ralt_dec c).

Lemma alts_pre_nil I : alts_pre I [].
Proof using. intros i c Hc. by rewrite lookup_nil in Hc. Qed.

Lemma alts_pre_le I cs : alts_pre I cs -> (length cs <= nlines I)%nat.
Proof using.
  intros H. destruct (decide (length cs = 0)%nat) as [Hz | Hz]; [lia |].
  destruct (lookup_lt_is_Some_2 cs (length cs - 1)%nat ltac:(lia)) as [c Hc].
  destruct (H _ c Hc) as [Hlt _]. lia.
Qed.

Lemma alts_pre_at I cs i :
  alts_pre I cs -> (i < length cs)%nat ->
  ralt_ok (uline_of (bodies_of I !!! i)) (ralt_at cs i).
Proof using.
  intros H Hi. destruct (lookup_lt_is_Some_2 cs i Hi) as [c Hc].
  rewrite /ralt_at (list_lookup_total_correct cs i c Hc).
  exact (proj2 (H i c Hc)).
Qed.

Lemma alts_pre_of_alts_ok I cs : alts_ok I cs -> alts_pre I cs.
Proof using.
  intros Ha i c Hc.
  destruct (Forall2_lookup_r _ _ _ _ _ Ha Hc) as (l & Hl & Hok).
  rewrite /lines_of list_lookup_fmap in Hl.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
  cbn in Hl. injection Hl as <-.
  rewrite (list_lookup_total_correct _ _ _ Hb).
  split; [| exact Hok]. rewrite /nlines. by eapply lookup_lt_Some.
Qed.

(* the input GROWS and the entries keep their meaning: a completed line's
   body is the same body in every longer input *)
Lemma alts_pre_mono I I' cs :
  I `prefix_of` I' -> alts_pre I cs -> alts_pre I' cs.
Proof using.
  intros Hp H i c Hc. destruct (H i c Hc) as [Hi Hok].
  destruct (bodies_of_prefix I I' Hp) as [z Hz].
  split; [rewrite /nlines Hz length_app; rewrite /nlines in Hi; lia |].
  rewrite Hz list_lookup_total_alt lookup_app_l;
    [| rewrite /nlines in Hi; lia].
  by rewrite -list_lookup_total_alt.
Qed.

Lemma alts_pre_snoc I cs a :
  alts_pre I cs -> (length cs < nlines I)%nat ->
  ralt_ok (uline_of (bodies_of I !!! length cs)) (ralt_dec a) ->
  alts_pre I (cs ++ [a]).
Proof using.
  intros H Hlt Hok i c Hc.
  destruct (decide (i < length cs)%nat) as [Hi | Hi].
  - rewrite lookup_app_l in Hc; [| lia]. exact (H i c Hc).
  - rewrite lookup_app_r in Hc; [| lia].
    assert (Hie : i = length cs).
    { apply lookup_lt_Some in Hc. cbn [length] in Hc. lia. }
    subst i. rewrite Nat.sub_diag in Hc. cbn in Hc. injection Hc as <-.
    by split.
Qed.

(* THE DEFAULT ALTERNATIVE: every line shape admits one, which is what makes
   a partial resolution paddable *)
Definition ralt_def (l : uline) : nat :=
  match l with
  | LEcho _ => 0%nat
  | LEchoF _ => ralt_enc RFExec
  | LCat => ralt_enc RCRan
  end.

Lemma ralt_def_ok (l : uline) : ralt_ok l (ralt_dec (ralt_def l)).
Proof using.
  destruct l as [ws | ws |]; cbn [ralt_def].
  - rewrite (ralt_dec_lt4 0%nat ltac:(lia)). rewrite /ralt_ok. lia.
  - by rewrite ralt_dec_enc.
  - by rewrite ralt_dec_enc.
Qed.

Definition alts_pad (I : list (bv 8)) (cs : list nat) : list nat :=
  cs ++ (ralt_def <$> drop (length cs) (lines_of I)).

Lemma alts_pad_prefix I cs : cs `prefix_of` alts_pad I cs.
Proof using. rewrite /alts_pad. by eexists. Qed.

Lemma alts_pad_take I cs : take (length cs) (alts_pad I cs) = cs.
Proof using. rewrite /alts_pad. by rewrite take_app_length. Qed.

Lemma alts_pad_length I cs :
  (length cs <= nlines I)%nat -> length (alts_pad I cs) = nlines I.
Proof using.
  intro Hle. rewrite /alts_pad length_app length_fmap length_drop
    lines_of_length. lia.
Qed.

Lemma alts_pad_ok I cs :
  alts_pre I cs -> alts_ok I (alts_pad I cs).
Proof using.
  intros H. pose proof (alts_pre_le I cs H) as Hle.
  rewrite /alts_ok /alts_pad.
  rewrite -{1}(take_drop (length cs) (lines_of I)).
  apply Forall2_app.
  - apply Forall2_same_length_lookup_2.
    { rewrite length_take lines_of_length. lia. }
    intros i l c Hl Hc.
    apply lookup_take_Some in Hl as [Hl _].
    rewrite /lines_of list_lookup_fmap in Hl.
    destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
    cbn in Hl. injection Hl as <-.
    pose proof (proj2 (H i c Hc)) as Hok.
    by rewrite (list_lookup_total_correct _ _ _ Hb) in Hok.
  - apply Forall2_fmap_r. apply Forall_Forall2_diag.
    apply Forall_forall. intros l _. exact (ralt_def_ok l).
Qed.

(* ====================================================================== *)
(*  6b.  THE ERA'S PROCESS-BYTE CURSOR, AT THE FILE SESSION                *)
(*                                                                        *)
(*  [EchoOut]'s section 1b, moved down here because it is pure and because *)
(*  the claim file is long enough without it.                              *)
(* ====================================================================== *)

Fixpoint proc_before_from_f (ps cs : list nat) (f0 : option fst)
    (pre I : list (bv 8)) : list (bv 8) :=
  match I with
  | [] => []
  | b :: I' => pending_at_f ps cs f0 pre
               ++ proc_before_from_f ps cs f0 (pre ++ [b]) I'
  end.

Definition proc_before_f (ps cs : list nat) (f0 : option fst)
    (I : list (bv 8)) : list (bv 8) := proc_before_from_f ps cs f0 [] I.

Definition proc_stream_f (ps cs : list nat) (f0 : option fst)
    (I : list (bv 8)) : list (bv 8) :=
  proc_before_f ps cs f0 I ++ pending_at_f ps cs f0 I.

Lemma proc_before_f_nil ps cs f0 : proc_before_f ps cs f0 [] = [].
Proof using. reflexivity. Qed.

Lemma proc_before_from_f_app ps cs f0 pre I1 I2 :
  proc_before_from_f ps cs f0 pre (I1 ++ I2)
  = proc_before_from_f ps cs f0 pre I1
    ++ proc_before_from_f ps cs f0 (pre ++ I1) I2.
Proof using.
  revert pre. induction I1 as [| b I1 IH]; intros pre.
  - cbn [proc_before_from_f app]. by rewrite app_nil_r.
  - cbn [app proc_before_from_f]. rewrite IH app_assoc.
    by rewrite epu_app_snoc.
Qed.

Lemma proc_before_f_app ps cs f0 I k :
  proc_before_f ps cs f0 (I ++ k)
  = proc_before_f ps cs f0 I ++ proc_before_from_f ps cs f0 I k.
Proof using. rewrite /proc_before_f proc_before_from_f_app. by cbn [app]. Qed.

Lemma proc_before_f_snoc ps cs f0 I b :
  proc_before_f ps cs f0 (I ++ [b]) = proc_stream_f ps cs f0 I.
Proof using.
  rewrite proc_before_f_app /proc_stream_f. cbn [proc_before_from_f].
  by rewrite app_nil_r.
Qed.

Lemma proc_before_f_prefix ps cs f0 I I' :
  I `prefix_of` I' ->
  proc_before_f ps cs f0 I `prefix_of` proc_before_f ps cs f0 I'.
Proof using. intros [z ->]. rewrite proc_before_f_app. by eexists. Qed.

Lemma proc_stream_f_before ps cs f0 I I' :
  I `prefix_of` I' -> I <> I' ->
  proc_stream_f ps cs f0 I `prefix_of` proc_before_f ps cs f0 I'.
Proof using.
  intros [z Hz] Hne. destruct z as [| b z].
  { exfalso. apply Hne. by rewrite Hz app_nil_r. }
  rewrite Hz proc_before_f_app /proc_stream_f. cbn [proc_before_from_f].
  rewrite app_assoc. by eexists.
Qed.

Lemma proc_stream_f_mono ps cs f0 I I' :
  I `prefix_of` I' ->
  proc_stream_f ps cs f0 I `prefix_of` proc_stream_f ps cs f0 I'.
Proof using.
  intros Hp. destruct (decide (I = I')) as [-> | Hne]; [reflexivity |].
  etrans; [exact (proc_stream_f_before ps cs f0 I I' Hp Hne) |].
  rewrite /proc_stream_f. by eexists.
Qed.

Definition pcount_f (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) (w : list (bv 8)) : nat :=
  (length (proc_before_f ps cs f0 (snd <$> E)) + length w)%nat.

Lemma pcount_f_write ps cs f0 E w b :
  pcount_f ps cs f0 E (w ++ [b]) = S (pcount_f ps cs f0 E w).
Proof using. rewrite /pcount_f length_app /=. lia. Qed.

Lemma pcount_f_echo ps cs f0 E x w :
  w = pending_f ps cs f0 E ->
  pcount_f ps cs f0 (E ++ [x]) [] = pcount_f ps cs f0 E w.
Proof using.
  intros ->. rewrite /pcount_f fmap_app /=.
  rewrite (proc_before_f_snoc ps cs f0 (snd <$> E) x.2)
          /proc_stream_f /pending_f.
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma proc_stream_f_pcount ps cs f0 E w b :
  pending_f ps cs f0 E !! length w = Some b ->
  proc_stream_f ps cs f0 (snd <$> E) !! pcount_f ps cs f0 E w = Some b.
Proof using.
  intros Hb. rewrite /proc_stream_f /pcount_f lookup_app_r; [| lia].
  replace (length (proc_before_f ps cs f0 (snd <$> E)) + length w
           - length (proc_before_f ps cs f0 (snd <$> E)))%nat
    with (length w) by lia.
  exact Hb.
Qed.

Lemma proc_stream_f_pcount_inv ps cs f0 E w I b :
  (snd <$> E) `prefix_of` I ->
  (length w < length (pending_f ps cs f0 E))%nat ->
  proc_stream_f ps cs f0 I !! pcount_f ps cs f0 E w = Some b ->
  pending_f ps cs f0 E !! length w = Some b.
Proof using.
  intros HI Hlt Hl.
  destruct (lookup_lt_is_Some_2 (pending_f ps cs f0 E) (length w) Hlt)
    as [b' Hb'].
  pose proof (proc_stream_f_pcount ps cs f0 E w b' Hb') as Hfwd.
  assert (Heq : proc_stream_f ps cs f0 I !! pcount_f ps cs f0 E w = Some b')
    by (eapply prefix_lookup_Some;
        [exact Hfwd | by apply proc_stream_f_mono]).
  assert (Hbb : b = b') by congruence. by rewrite Hbb.
Qed.

(* ====================================================================== *)
(*  6c.  SMALL LIST FACTS [EchoOut.v] ALSO STATES                          *)
(*                                                                        *)
(*  They are pure and sit ABOVE this file (in [EchoOut.v]), which this     *)
(*  file must not import: the claim's cone would drag [WpUart] into a      *)
(*  logic-free file.  Copied with an [fop_] prefix; if [EchoOut.v] is ever *)
(*  opened for another reason they belong in [EchoOutPure.v] and both      *)
(*  copies should go.                                                      *)
(* ====================================================================== *)

Lemma fop_snoc_cases {A} (l : list A) : l = [] \/ exists u x, l = u ++ [x].
Proof using.
  induction l as [| a l IH]; [by left |]. right.
  destruct IH as [-> | (u & x & ->)].
  - by exists [], a.
  - by exists (a :: u), x.
Qed.

Lemma fop_removelast_take {A} (l : list A) :
  removelast l = take (length l - 1)%nat l.
Proof using.
  induction l as [| a l IH]; [done |].
  destruct l as [| b l']; [reflexivity |].
  change (removelast (a :: b :: l')) with (a :: removelast (b :: l')).
  rewrite IH.
  replace (length (a :: b :: l') - 1)%nat with (S (length (b :: l') - 1)%nat)
    by (cbn [length]; lia).
  reflexivity.
Qed.

Lemma fop_removelast_prefix {A} (l : list A) : removelast l `prefix_of` l.
Proof using. rewrite fop_removelast_take. apply prefix_take. Qed.

Lemma fop_prefix_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> removelast l `prefix_of` removelast l'.
Proof using.
  intros Hp. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Ht : take (length l - 1)%nat l = take (length l - 1)%nat l').
  { destruct Hp as [z ->].
    rewrite (take_app_le l z (length l - 1)%nat); [done | lia]. }
  rewrite !fop_removelast_take Ht. apply prefix_take_le. lia.
Qed.

Lemma fop_prefix_of_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> l <> l' -> l `prefix_of` removelast l'.
Proof using.
  intros Hp Hne. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Hlt : (length l < length l')%nat).
  { destruct (decide (length l = length l')) as [He | He]; [| lia].
    exfalso. exact (Hne (prefix_length_eq _ _ Hp ltac:(lia))). }
  assert (Hl : l = take (length l) l').
  { destruct Hp as [z ->]. by rewrite take_app_length. }
  rewrite fop_removelast_take {1}Hl. apply prefix_take_le. lia.
Qed.

Lemma fop_nlines_removelast (I : list (bv 8)) :
  rest_of I = [] -> nlines (removelast I) = (nlines I - 1)%nat.
Proof using.
  intros Hr. destruct (fop_snoc_cases I) as [-> | (u & x & ->)].
  - cbn [removelast]. rewrite nlines_nil. lia.
  - destruct (decide (x = wl_nl)) as [-> | Hx].
    + rewrite epu_removelast_snoc nlines_snoc_nl. lia.
    + exfalso. rewrite (rest_of_snoc_other u x Hx) in Hr.
      by destruct (app_eq_nil (rest_of u) [x] Hr) as [_ Hb].
Qed.

Lemma fop_nstarted_rest_nil (I : list (bv 8)) :
  rest_of I = [] -> nstarted I = nlines I.
Proof using.
  intros Hr. rewrite /nstarted Hr. case_decide as Hd;
    [lia | by destruct (Hd eq_refl)].
Qed.

Lemma fop_nstarted_snoc (I : list (bv 8)) (b : bv 8) :
  nstarted (I ++ [b]) = S (nlines I).
Proof using.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - apply nstarted_snoc_nl.
  - by apply nstarted_snoc_other.
Qed.

Lemma fop_last_ws_lta (I : list (bv 8)) :
  last_ws I = wl_words (bodies_of I !!! (nlines I - 1)%nat).
Proof using.
  rewrite /last_ws list_lookup_total_alt last_lookup /nlines Nat.sub_1_r.
  reflexivity.
Qed.

Lemma fop_lta_prefix (cs0 cs : list nat) (i : nat) :
  cs0 `prefix_of` cs -> (i < length cs0)%nat -> cs !!! i = cs0 !!! i.
Proof using.
  intros [z ->] Hi. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Lemma fop_prefix_snoc_lookup {A} (w l : list A) (b : A) :
  w `prefix_of` l -> l !! length w = Some b -> (w ++ [b]) `prefix_of` l.
Proof using.
  intros [z ->] Hl. rewrite lookup_app_r in Hl; [| lia].
  rewrite Nat.sub_diag in Hl.
  destruct z as [| c z]; [discriminate |]. cbn in Hl. injection Hl as <-.
  exists z. by rewrite -app_assoc.
Qed.

(* ====================================================================== *)
(*  6d.  A WRITER'S LOWER BOUNDS DETERMINE THE STREAM                      *)
(* ====================================================================== *)

Lemma pending_at_f_cs_ext ps cs0 cs f0 I :
  cs0 `prefix_of` cs -> (nlines I <= length cs0)%nat ->
  pending_at_f ps cs0 f0 I = pending_at_f ps cs f0 I.
Proof using.
  intros Hp Hn. rewrite /pending_at_f.
  case_decide as H0; [done |].
  case_decide as Hr; [| done].
  pose proof (nlines_pos_of_rest_nil I H0 Hr) as Hpos.
  assert (Hlk : forall j, (j < nlines I)%nat -> cs0 !!! j = cs !!! j).
  { intros j Hj. symmetry. apply (fop_lta_prefix cs0 cs j Hp). lia. }
  rewrite /alt_cont_f /ralt_at (Hlk (nlines I - 1)%nat ltac:(lia)).
  rewrite (fst_upto_ext cs0 cs (f0_st f0) (bodies_of I) (bodies_of I)
             (nlines I - 1)%nat ltac:(intros j Hj; apply Hlk; lia)
             ltac:(intros j Hj; reflexivity)).
  by rewrite (pro_idx_f_ext cs0 cs (nlines I) Hlk (nlines I - 1)%nat
                ltac:(lia)).
Qed.

Lemma pending_at_f_cs_prefix ps0 ps cs0 cs f0 I :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  (nlines I <= length cs0)%nat ->
  (pro_idx_f cs0 (nlines I) < pro_rounds ps0)%nat ->
  pending_at_f ps0 cs0 f0 I = pending_at_f ps cs f0 I.
Proof using.
  intros Hps Hcs Hn Hr.
  rewrite (pending_at_f_ps_ext ps0 ps cs0 f0 I Hps Hr).
  by apply pending_at_f_cs_ext.
Qed.

Lemma pending_at_f_stage_ext ps0 ps cs0 cs f0 I0 J :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin_f ps0 cs0 I0 ->
  (nlines (removelast I0) <= length cs0)%nat ->
  J `prefix_of` I0 -> J <> I0 ->
  pending_at_f ps0 cs0 f0 J = pending_at_f ps cs f0 J.
Proof using.
  intros Hps Hcs Hpin Hn HJ Hne.
  assert (Hjl : (nlines J <= length cs0)%nat).
  { etrans; [| exact Hn].
    apply nlines_prefix, (fop_prefix_of_removelast J I0 HJ Hne). }
  apply (pending_at_f_cs_prefix ps0 ps cs0 cs f0 J Hps Hcs Hjl).
  apply Hpin. exact (nstarted_strict J I0 HJ Hne).
Qed.

Lemma proc_before_from_f_ext ps0 ps cs0 cs f0 pre I :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ I -> J <> pre ++ I ->
     pending_at_f ps0 cs0 f0 J = pending_at_f ps cs f0 J) ->
  proc_before_from_f ps0 cs0 f0 pre I = proc_before_from_f ps cs f0 pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [b]) ++ I = pre ++ b :: I) by apply epu_app_snoc.
  assert (Hhere : pending_at_f ps0 cs0 f0 pre = pending_at_f ps cs f0 pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - apply (epu_app_cons_ne pre b I). }
  cbn [proc_before_from_f]. rewrite Hhere. f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma proc_before_f_ext ps0 ps cs0 cs f0 I :
  (forall J, J `prefix_of` I -> J <> I ->
     pending_at_f ps0 cs0 f0 J = pending_at_f ps cs f0 J) ->
  proc_before_f ps0 cs0 f0 I = proc_before_f ps cs f0 I.
Proof using.
  intros Hj. rewrite /proc_before_f. apply proc_before_from_f_ext.
  intros J _ H2 H3. rewrite app_nil_l in H2, H3. by apply Hj.
Qed.

Lemma proc_before_f_cs_prefix ps0 ps cs0 cs f0 I0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin_f ps0 cs0 I0 ->
  (nlines (removelast I0) <= length cs0)%nat ->
  proc_before_f ps0 cs0 f0 I0 = proc_before_f ps cs f0 I0.
Proof using.
  intros Hps Hcs Hpin Hn. apply proc_before_f_ext.
  intros J HJ Hne.
  exact (pending_at_f_stage_ext ps0 ps cs0 cs f0 I0 J Hps Hcs Hpin Hn HJ Hne).
Qed.

Lemma pcount_f_cs_prefix ps0 ps cs0 cs f0 E w :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  pro_pin_f ps0 cs0 (snd <$> E) ->
  (nlines (removelast (snd <$> E)) <= length cs0)%nat ->
  pcount_f ps0 cs0 f0 E w = pcount_f ps cs f0 E w.
Proof using.
  intros Hps Hcs Hpin Hn. rewrite /pcount_f.
  by rewrite (proc_before_f_cs_prefix ps0 ps cs0 cs f0 (snd <$> E)
                Hps Hcs Hpin Hn).
Qed.

Lemma proc_stream_f_prefix ps0 ps cs0 cs f0 I0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin_f ps0 cs0 I0 ->
  (nlines I0 <= length cs0)%nat ->
  proc_stream_f ps0 cs0 f0 I0 `prefix_of` proc_stream_f ps cs f0 I0.
Proof using.
  intros Hps Hcs Hpin Hn.
  assert (Hb : proc_before_f ps0 cs0 f0 I0 = proc_before_f ps cs f0 I0).
  { apply (proc_before_f_cs_prefix ps0 ps cs0 cs f0 I0 Hps Hcs Hpin).
    etrans; [apply nlines_prefix, fop_removelast_prefix | exact Hn]. }
  rewrite /proc_stream_f Hb. apply prefix_app.
  rewrite (pending_at_f_cs_ext ps0 cs0 cs f0 I0 Hcs Hn).
  by apply pending_at_f_ps_mono.
Qed.

Lemma D_from_f_ext ps0 ps cs0 cs f0 pre E :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ (snd <$> E) ->
     J <> pre ++ (snd <$> E) ->
     pending_at_f ps0 cs0 f0 J = pending_at_f ps cs f0 J) ->
  D_from_f ps0 cs0 f0 pre E = D_from_f ps cs f0 pre E.
Proof using.
  revert pre. induction E as [| x E IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [x.2]) ++ (snd <$> E) = pre ++ (snd <$> (x :: E)))
    by (by rewrite fmap_cons epu_app_snoc).
  assert (Hhere : pending_at_f ps0 cs0 f0 pre = pending_at_f ps cs f0 pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - rewrite fmap_cons. apply (epu_app_cons_ne pre x.2 (snd <$> E)). }
  cbn [D_from_f]. rewrite Hhere. do 2 f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma D_f_cs_prefix ps0 ps cs0 cs f0 E :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  pro_pin_f ps0 cs0 (snd <$> E) ->
  (nlines (removelast (snd <$> E)) <= length cs0)%nat ->
  D_f ps0 cs0 f0 E = D_f ps cs f0 E.
Proof using.
  intros Hps Hcs Hpin Hn. rewrite /D_f. apply D_from_f_ext.
  intros J _ H2 H3. rewrite app_nil_l in H2, H3.
  exact (pending_at_f_stage_ext ps0 ps cs0 cs f0 (snd <$> E) J
           Hps Hcs Hpin Hn H2 H3).
Qed.

(* THE WRITE'S WHOLE PURE ARGUMENT, [EchoOut.write_stage_byte]'s twin: the
   writer names lower bounds of the era's choices, its INPUT and its cursor,
   and knows only that its byte is the [P]-th of the stream through [I0].
   That alone pins the stage. *)
Lemma write_stage_byte_f (ps0 ps cs0 cs : list nat) (f0 : option fst)
      (E : list (list mobs * bv 8)) (w I0 : list (bv 8)) (P : nat) (b : bv 8) :
  ps0 `prefix_of` ps ->
  pro_pin_f ps0 cs0 I0 ->
  cs0 `prefix_of` cs ->
  (nlines I0 <= length cs0)%nat ->
  I0 `prefix_of` (snd <$> E) ->
  P = pcount_f ps cs f0 E w ->
  proc_stream_f ps0 cs0 f0 I0 !! P = Some b ->
  (snd <$> E) = I0 /\ pending_f ps cs f0 E !! length w = Some b.
Proof using.
  intros Hps Hpin Hcs Hn HI HP Hb.
  pose proof (prefix_lookup_Some _ _ _ _ Hb
                (proc_stream_f_prefix ps0 ps cs0 cs f0 I0 Hps Hcs Hpin Hn))
    as Hb'.
  clear Hb. rename Hb' into Hb.
  assert (Hlt : (P < length (proc_stream_f ps cs f0 I0))%nat)
    by (by apply lookup_lt_Some in Hb).
  assert (HlenE : (snd <$> E) = I0).
  { destruct (decide ((snd <$> E) = I0)) as [? | Hne]; [done | exfalso].
    pose proof (proc_stream_f_before ps cs f0 I0 (snd <$> E) HI
                  ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
    apply prefix_length in Hpre. rewrite HP /pcount_f in Hlt. lia. }
  split; [exact HlenE |].
  rewrite -HlenE in Hb, Hlt.
  assert (Hstrict : (length w < length (pending_f ps cs f0 E))%nat).
  { rewrite /proc_stream_f length_app in Hlt.
    rewrite HP /pcount_f in Hlt. rewrite /pending_f. lia. }
  eapply (proc_stream_f_pcount_inv ps cs f0 E w (snd <$> E) b);
    [reflexivity | exact Hstrict | by rewrite -HP].
Qed.

(* ====================================================================== *)
(*  6e.  THE BANNER OF AN ARBITRARY PROLOGUE ROUND                         *)
(* ====================================================================== *)

Lemma proc_stream_f_round_banner (ps cs : list nat) (f0 : option fst)
      (I : list (bv 8)) (j i : nat) (pre : list (bv 8)) (b : bv 8) :
  pending_at_f ps cs f0 I
  = pre ++ pro_of (pro_from (pro_idx_f cs (nlines I)) ps) ->
  pro_from (pro_idx_f cs (nlines I)) ps = pro_fail j ++ [3%nat] ->
  u_banner !! i = Some b ->
  proc_stream_f ps cs f0 I
    !! (length (proc_before_f ps cs f0 I) + length pre + pro_round * j + i)%nat
  = Some b.
Proof using.
  intros Hshape Hopen Hb.
  rewrite /proc_stream_f Hshape Hopen.
  replace (length (proc_before_f ps cs f0 I) + length pre + pro_round * j + i)%nat
    with (length (proc_before_f ps cs f0 I)
          + (length pre + (pro_round * j + i)))%nat by lia.
  rewrite (lookup_app_shift (proc_before_f ps cs f0 I)) (lookup_app_shift pre).
  by apply pro_of_fail_banner.
Qed.

Lemma proc_stream_f_round_banner_open (ps cs : list nat) (f0 : option fst)
      (I : list (bv 8)) (j i : nat) (b : bv 8) :
  rest_of I = [] ->
  (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)) = true) ->
  pro_from (pro_idx_f cs (nlines I)) ps = pro_fail j ++ [3%nat] ->
  u_banner !! i = Some b ->
  proc_stream_f ps cs f0 I
    !! (length (proc_before_f ps cs f0 I)
        + length (if decide (I = []) then [] else alt_panic)
        + pro_round * j + i)%nat
  = Some b.
Proof using.
  intros Hr Ho Hopen Hb.
  apply (proc_stream_f_round_banner ps cs f0 I j i _ b);
    [by apply pending_at_f_round_pre | exact Hopen | exact Hb].
Qed.

(* ====================================================================== *)
(*  7.  F4 -- PHI's PURE PART                                              *)
(* ====================================================================== *)

Lemma pro_ok_f_pad ps cs m d :
  Forall (fun x => (x < length pro_alts)%nat) ps -> (m <= d)%nat ->
  pro_ok_f (ps ++ replicate (S d) 0%nat) cs m.
Proof using.
  intros HF Hm. split.
  - apply Forall_app. split; [exact HF |].
    apply Forall_forall. intros x Hx. apply elem_of_replicate in Hx as [-> _].
    rewrite pro_alts_length. lia.
  - rewrite pro_rounds_app pro_rounds_replicate_0.
    pose proof (pro_idx_f_le cs m). lia.
Qed.

Lemma pro_pin_f_mono ps ps' cs I :
  ps `prefix_of` ps' -> pro_pin_f ps cs I -> pro_pin_f ps' cs I.
Proof using.
  intros [z ->] Hpin q Hq. pose proof (Hpin q Hq) as H.
  rewrite pro_rounds_app. lia.
Qed.

(* THE CLAIM GIVES [good_out_f] AT THE SEGMENT, at the stage's OWN boot
   state.  Two premises replace [EchoOutPure.good_out_of_stage]'s
   [Forall (< 4) cs]: the range condition is pointwise ([alts_pre]) and the
   resolution is PADDED to a full one, and the two length rows are
   [EchoOut.cs_len_ok]'s two readings -- "every completed line below the
   last has an entry" and "either the last one does too, or nothing of its
   block is written". *)
Lemma good_out_f_of_stage (ps cs : list nat) (f0 : option fst)
      (E : list (list mobs * bv 8)) (w : list (bv 8)) (seg : list mobs) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  alts_pre (ins seg) cs ->
  (nlines (removelast (snd <$> E)) <= length cs)%nat ->
  ((nlines (snd <$> E) <= length cs)%nat \/ w = []) ->
  E_disc_f E ->
  pro_pin_f ps cs (snd <$> E) ->
  w `prefix_of` pending_f ps cs f0 E ->
  obs_wire Uart0 seg `prefix_of` (D_f ps cs f0 E ++ w) ->
  (snd <$> E) `prefix_of` ins seg ->
  good_out_f (f0_st f0) seg.
Proof using.
  intros Hps Hao Hrl Hlast HE Hpin Hw Hwire Hinp.
  set (ps' := (ps ++ replicate (S (nlines (ins seg))) 0%nat)%list).
  set (cs' := alts_pad (ins seg) cs).
  assert (Hpp : ps `prefix_of` ps') by (rewrite /ps'; by eexists).
  assert (Hcc : cs `prefix_of` cs') by apply alts_pad_prefix.
  assert (Hpin' : pro_pin_f ps' cs (snd <$> E))
    by exact (pro_pin_f_mono ps ps' cs _ Hpp Hpin).
  exists ps', cs'. split.
  { apply pro_ok_f_pad; [exact Hps | lia]. }
  split; [exact (alts_pad_ok (ins seg) cs Hao) |].
  etrans; [exact Hwire |].
  rewrite (D_f_ps_ext ps ps' cs f0 E Hpp Hpin).
  rewrite (D_f_cs_prefix ps' ps' cs cs' f0 E ltac:(reflexivity) Hcc Hpin' Hrl).
  assert (Hw' : w `prefix_of` pending_f ps' cs' f0 E).
  { destruct Hlast as [Hle | ->]; [| apply prefix_nil].
    etrans; [exact Hw |].
    etrans; [exact (pending_f_ps_mono ps ps' cs f0 E Hpp) |].
    rewrite /pending_f (pending_at_f_cs_ext ps' cs cs' f0 (snd <$> E) Hcc Hle).
    reflexivity. }
  etrans; [exact (D_f_stage_prefix ps' cs' f0 E w HE Hw') |].
  by apply (sessf_mono ps' cs' (f0_st f0) (snd <$> E) (ins seg)).
Qed.

(* ====================================================================== *)
(*  8.  DETERMINACY AT TWO BOOT STATES                                     *)
(*                                                                        *)
(*  [FileDisc.sessf_prefix_det] fixes ONE boot state for both witnesses.   *)
(*  The claim compares the DISCIPLINE's witness -- whose state the trace    *)
(*  predicate chose existentially -- against ITS OWN, filed off the deed,   *)
(*  and the two have no reason to be equal.  They do not have to be:        *)
(*  [FileDisc.alt_seq_f_prefix_det] already takes the two apart (a          *)
(*  non-panic alternative's output is a '$'-free run followed by the         *)
(*  prompt WHATEVER the file holds), so this is that lemma's own            *)
(*  conclusion lifted to the session.                                      *)
(* ====================================================================== *)
Lemma sessf_prefix_det2 (ps ps' cs cs' : list nat) (s s' : fst)
    (I' I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  pro_ok_f ps' cs' (nlines I') ->
  alts_ok I cs -> alts_ok I' cs' ->
  pro_pin_f ps cs I -> disc_input_f I -> disc_input_f I' ->
  fst_ok s -> fst_ok s' ->
  sessf ps' cs' s' I' `prefix_of` sessf ps cs s I ->
  I' `prefix_of` I /\ pro_ok_f ps cs (nlines I')
  /\ sessf ps' cs' s' I' = sessf ps cs s I'.
Proof using.
  intros Hps [Hps' Hlt'] Hcs Hcs' Hpin Hd Hd' Hs Hs' Hpre.
  assert (Hdone' : pro_done ps') by (apply pro_done_rounds; lia).
  assert (Hpre0 : pro_of ps' `prefix_of` pro_of ps).
  { destruct (decide (I = [])) as [HI0 | HI].
    - rewrite HI0 sessf_nil in Hpre. etrans; [| exact Hpre].
      rewrite /sessf. by apply prefix_app_r.
    - assert (HdA : pro_done ps).
      { apply pro_done_rounds.
        pose proof (Hpin 0%nat (nstarted_pos I HI)) as H0.
        cbn [pro_idx_f] in H0. lia. }
      assert (H1 : pro_of ps' `prefix_of` sessf ps cs s I).
      { etrans; [| exact Hpre]. rewrite /sessf. by apply prefix_app_r. }
      assert (H2 : pro_of ps `prefix_of` sessf ps cs s I)
        by (rewrite /sessf; by apply prefix_app_r).
      destruct (prefix_weak_total _ _ _ H1 H2) as [H | H]; [exact H |].
      destruct (pro_of_prefix_free ps' ps Hps' Hps HdA H) as [_ Heq].
      by rewrite Heq. }
  destruct (pro_of_prefix_free ps ps' Hps Hps' Hdone' Hpre0) as [Hdps Heq0].
  assert (Hpos : (0 < pro_rounds ps)%nat) by (by apply pro_done_rounds).
  rewrite /sessf Heq0 in Hpre. apply wl_prefix_app_cancel in Hpre.
  assert (Hbelow : forall i, (i < nlines I)%nat ->
            (pro_idx_f cs i < pro_rounds ps)%nat).
  { intros i Hi. apply Hpin. pose proof (nlines_le_nstarted I). lia. }
  assert (Htlast : rest_of I <> [] ->
            (pro_idx_f cs (nlines I) < pro_rounds ps)%nat).
  { intros Hne. apply Hpin. rewrite /nstarted.
    case_decide as Hz; [by destruct (Hne Hz) | lia]. }
  assert (Hlb' : (nlines I' <= length (bodies_of I'))%nat)
    by (rewrite /nlines; lia).
  assert (Hlb : (nlines I <= length (bodies_of I))%nat)
    by (rewrite /nlines; lia).
  assert (Hline : forall i, (i < nlines I)%nat ->
            uline_ok (uline_of (bodies_of I !!! i)))
    by (intros i Hi; exact (proj1 (disc_input_f_at I i Hd Hi))).
  assert (Hokc : forall i, (i < nlines I)%nat ->
            ralt_ok (uline_of (bodies_of I !!! i)) (ralt_at cs i))
    by (intros i Hi; exact (FileDisc.alts_ok_at I cs i Hcs Hi)).
  assert (Hokc' : forall i, (i < nlines I')%nat ->
            ralt_ok (uline_of (bodies_of I' !!! i)) (ralt_at cs' i))
    by (intros i Hi; exact (FileDisc.alts_ok_at I' cs' i Hcs' Hi)).
  destruct (alt_seq_f_prefix_det (nlines I') ps ps' cs cs' s s'
              (bodies_of I) (bodies_of I') (nlines I) (rest_of I') (rest_of I)
              Hps Hps' Hlt' Hpos Hbelow Htlast Hlb' Hlb Hs Hs'
              Hline Hokc Hokc'
              (wl_cut_bodies_nonl I) (wl_cut_bodies_nonl I')
              (wl_cut_rest_nonl I') (wl_cut_rest_nonl I) Hpre)
    as (Hqle & Htk & Hround & Hseq & Hteq & Htlt).
  assert (HI' : I' `prefix_of` I).
  { apply wl_cut_prefix_of.
    - assert (Hb' : bodies_of I' = take (nlines I') (bodies_of I))
        by (rewrite -Htk take_ge; [reflexivity | rewrite /nlines; lia]).
      rewrite Hb'. apply prefix_take.
    - exact Hteq.
    - exact Htlt. }
  split; [exact HI' |]. split; [split; [exact Hps | exact Hround] |].
  rewrite /sessf Heq0. do 2 f_equal. rewrite Hseq.
  apply alt_seq_f_bs_ext. intros j Hj. symmetry.
  exact (fd_lta_take_eq (bodies_of I) (bodies_of I') (nlines I') j Htk Hj).
Qed.

(* THE DISCIPLINE'S LOWER BOUND AT THE OPEN CYCLE'S LAST INPUT, at the
   cycle's own boot state: D1/D2 read off [disc_seg_f'] at the wire the last
   byte was typed on.  [EchoOutPure.disc_seg'_pt_last]'s twin. *)
Lemma disc_seg_f'_pt_last (s : fst) (seg : list mobs) (c : bv 8) :
  disc_seg_f' s seg -> obs_ends_in Uart0 seg c ->
  exists ps' cs' : list nat,
    pro_ok_f ps' cs' (nlines (removelast (ins seg)))
    /\ alts_ok (removelast (ins seg)) cs'
    /\ sessf ps' cs' s (removelast (ins seg)) `prefix_of` obs_wire Uart0 seg.
Proof using.
  intros [Hd (ps & cs & Hao & Hall)] [seg0 ->].
  assert (Hip : seg0 ∈ in_pres (seg0 ++ [ObsUartIn Uart0 c])).
  { rewrite in_pres_in. apply elem_of_app. right. apply elem_of_list_here. }
  destruct (Hall _ Hip) as [Hok Hpt]. rewrite /disc_pt_f in Hpt.
  rewrite ins_app ins_in epu_removelast_snoc.
  assert (Hpr : ins seg0 `prefix_of` ins (seg0 ++ [ObsUartIn Uart0 c])).
  { rewrite ins_app ins_in. by eexists. }
  assert (Hle : (nlines (ins seg0) <= nlines (ins seg0 ++ [c]))%nat)
    by (apply nlines_prefix; by eexists).
  exists ps, (take (nlines (ins seg0)) cs).
  assert (Heq : sessf ps (take (nlines (ins seg0)) cs) s (ins seg0)
                = sessf ps cs s (ins seg0))
    by (apply sessf_take; lia).
  split.
  { destruct Hok as [HF Hlt]. split; [exact HF |].
    rewrite (pro_idx_f_ext (take (nlines (ins seg0)) cs) cs
               (nlines (ins seg0))); [exact Hlt | | lia].
    intros j Hj. rewrite list_lookup_total_alt lookup_take; [| lia].
    by rewrite -list_lookup_total_alt. }
  split.
  { exact (alts_ok_take _ _ cs Hpr Hao). }
  rewrite Heq. etrans; [exact Hpt |]. rewrite obs_wire_app. by eexists.
Qed.

(* [sessf] is never empty once round 0 has settled *)
Lemma sessf_nonnil (ps cs : list nat) (s : fst) (I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> pro_done ps ->
  sessf ps cs s I <> [].
Proof using.
  intros HF Hd H. rewrite /sessf in H.
  apply app_eq_nil in H as [H _].
  assert (Hne : ps <> []) by (intros ->; by apply Exists_nil in Hd).
  pose proof (pro_of_pos ps HF Hne) as Hpos. rewrite H in Hpos.
  cbn [length] in Hpos. lia.
Qed.

(* ====================================================================== *)
(*  9.  THE STAGE RECORD, AND THE TWO LENGTH LAWS                          *)
(*                                                                        *)
(*  [EchoOut.ostage] with ONE VALUE MORE: the era's boot file state.       *)
(*  Both length laws ([cs_len_ok_f], [ps_len_ok_f]) and the stage's whole  *)
(*  pure account ([feout_pure]) are pure, so they live here and the claim  *)
(*  file only has to own the resources.                                    *)
(* ====================================================================== *)

Record fostage := MkFO {
  fo_ps : list nat;
  fo_cs : list nat;
  fo_E  : list (list mobs * bv 8);
  fo_w  : list (bv 8);
  fo_f0 : option fst;
}.
Definition fostage0 : fostage := MkFO [] [] [] [] None.

(* out of range the choice list reads 0, which decodes to [REcho 0] -- an
   alternative whose output is never empty, whatever the line is *)
Lemma ralt_at_ge (cs : list nat) (i : nat) :
  (length cs <= i)%nat -> ralt_at cs i = REcho 0%nat.
Proof using.
  intro Hi.
  assert (Hz : cs !!! i = 0%nat).
  { rewrite list_lookup_total_alt (lookup_ge_None_2 cs i Hi). reflexivity. }
  rewrite /ralt_at Hz. apply ralt_dec_lt4. lia.
Qed.

Lemma ralt_panic_ge (cs : list nat) (i : nat) :
  (length cs <= i)%nat -> ralt_panic (ralt_at cs i) = false.
Proof using. intro Hi. rewrite (ralt_at_ge cs i Hi). by vm_compute. Qed.

Lemma pro_idx_f_app_le (cs z : list nat) (q : nat) :
  (q <= length cs)%nat -> pro_idx_f (cs ++ z) q = pro_idx_f cs q.
Proof using.
  intro Hq. apply (pro_idx_f_ext (cs ++ z) cs q); [| lia].
  intros j Hj. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

(* NO ALTERNATIVE PRINTS NOTHING.  Every constant one carries at least the
   prompt or its own newline, [RCRan]'s content is closed by the prompt, and
   an [REcho k] is nonempty for [k < 4] -- which covers both an alternative
   a line ADMITS and the out-of-range reading. *)
Lemma cont_nonnil (s : fst) (l : uline) (a : ralt) :
  ralt_ok l a \/ a = REcho 0%nat -> cont s l a <> [].
Proof using.
  intro Ha.
  assert (Hpr : u_prompt <> []).
  { pose proof u_prompt_pos as Hup.
    destruct u_prompt as [| z zs]; [cbn [length] in Hup; lia | done]. }
  assert (Hex : alt_execfail <> []) by (by vm_compute).
  assert (Hop : alt_openfail <> []) by (by vm_compute).
  assert (Hpa : alt_panic <> []) by (by vm_compute).
  assert (Hca : alt_catopen <> []) by (by vm_compute).
  assert (Hec : alt_execcat <> []) by (by vm_compute).
  destruct a as [k | sel | | | | | | | | | |]; rewrite /cont.
  - assert (Hk : (k < 4)%nat).
    { destruct Ha as [Ha | Heq]; [| injection Heq as <-; lia].
      destruct l as [ws | ws |]; [exact Ha | by destruct Ha | by destruct Ha]. }
    exact (line_alts_of_nonnil (uline_ws l) k Hk).
  - exact Hpr.
  - exact Hex.
  - exact Hop.
  - exact Hop.
  - exact Hpr.
  - exact Hpa.
  - destruct s as [bs |]; [| exact Hca].
    intro Hq. by destruct (app_eq_nil bs u_prompt Hq) as [_ Hb].
  - exact Hca.
  - exact Hec.
  - exact Hpr.
  - exact Hpa.
Qed.

Lemma pending_at_f_nonnil (ps cs : list nat) (f0 : option fst)
    (I : list (bv 8)) :
  alts_pre I cs -> I <> [] -> rest_of I = [] ->
  pending_at_f ps cs f0 I <> [].
Proof using.
  intros Hao Hne Hr. rewrite /pending_at_f.
  rewrite decide_False; [| exact Hne]. rewrite decide_True; [| exact Hr].
  rewrite /alt_cont_f. intros Hc. apply app_eq_nil in Hc as [Hc _].
  revert Hc. apply cont_nonnil.
  destruct (decide (nlines I - 1 < length cs)%nat) as [Hlt | Hge].
  - left. exact (alts_pre_at I cs _ Hao Hlt).
  - right. apply ralt_at_ge. lia.
Qed.

Lemma pending_f_nonnil (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) :
  alts_pre (snd <$> E) cs -> (snd <$> E) <> [] ->
  rest_of (snd <$> E) = [] -> pending_f ps cs f0 E <> [].
Proof using. rewrite /pending_f. apply pending_at_f_nonnil. Qed.

Lemma pending_f_nil_inv (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) :
  alts_pre (snd <$> E) cs -> rest_of (snd <$> E) = [] ->
  pending_f ps cs f0 E = [] -> (snd <$> E) = [].
Proof using.
  intros Hao Hr Hnil.
  destruct (decide ((snd <$> E) = [])) as [? | Hne]; [done | exfalso].
  exact (pending_f_nonnil ps cs f0 E Hao Hne Hr Hnil).
Qed.

(* ---- the choice list's length law ---- *)

Definition cs_len_ok_f (so : fostage) : Prop :=
  length (fo_cs so)
  = (if decide (fo_w so = [] /\ rest_of (snd <$> fo_E so) = [])
     then (nlines (snd <$> fo_E so) - 1)%nat
     else nlines (snd <$> fo_E so)).

Lemma cs_len_ok_f_inv (so : fostage) :
  cs_len_ok_f so ->
  ((fo_w so = [] /\ rest_of (snd <$> fo_E so) = [])
     /\ length (fo_cs so) = (nlines (snd <$> fo_E so) - 1)%nat)
  \/ (~ (fo_w so = [] /\ rest_of (snd <$> fo_E so) = [])
     /\ length (fo_cs so) = nlines (snd <$> fo_E so)).
Proof using.
  rewrite /cs_len_ok_f. case_decide as Hb; intros Hc.
  - left. by split.
  - right. by split.
Qed.

Lemma cs_len_ok_f_intro (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) (f0 : option fst) :
  ((w = [] /\ rest_of (snd <$> E) = []) ->
     length cs = (nlines (snd <$> E) - 1)%nat) ->
  (~ (w = [] /\ rest_of (snd <$> E) = []) ->
     length cs = nlines (snd <$> E)) ->
  cs_len_ok_f (MkFO ps cs E w f0).
Proof using.
  rewrite /cs_len_ok_f. cbn [fo_ps fo_cs fo_E fo_w fo_f0].
  intros H1 H2. case_decide as Hb; [by apply H1 | by apply H2].
Qed.

Lemma cs_len_ok_f_mid (so : fostage) :
  cs_len_ok_f so -> fo_w so <> [] ->
  length (fo_cs so) = nlines (snd <$> fo_E so).
Proof using.
  intros Hc Hw. destruct (cs_len_ok_f_inv so Hc) as [[[Hw' _] _] | [_ ?]];
    [done | done].
Qed.

Lemma cs_len_ok_f_echo (so : fostage) (x : list mobs * bv 8) :
  alts_pre (snd <$> fo_E so) (fo_cs so) ->
  fo_w so = pending_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so) ->
  cs_len_ok_f so ->
  cs_len_ok_f (MkFO (fo_ps so) (fo_cs so) (fo_E so ++ [x]) [] (fo_f0 so)).
Proof using.
  intros Hao Hw Hc.
  assert (Hq : length (fo_cs so) = nlines (snd <$> fo_E so)).
  { destruct (cs_len_ok_f_inv so Hc) as [[[Hw' Hm] Hq] | [_ Hq]]; [| exact Hq].
    pose proof (pending_f_nil_inv (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)
                  Hao Hm ltac:(by rewrite -Hw)) as Hz.
    rewrite Hz in Hq |- *. rewrite nlines_nil in Hq |- *. lia. }
  apply cs_len_ok_f_intro; rewrite fmap_app /= Hq.
  - intros [_ Hm]. destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
    + rewrite Hx nlines_snoc_nl. lia.
    + exfalso. rewrite (rest_of_snoc_other _ _ Hx) in Hm.
      by destruct (app_eq_nil (rest_of (snd <$> fo_E so)) [x.2] Hm) as [_ Hb].
  - intros Hne. destruct (decide (x.2 = wl_nl)) as [Hx | Hx].
    + exfalso. apply Hne. split; [reflexivity |].
      rewrite Hx. apply rest_of_snoc_nl.
    + by rewrite (nlines_snoc_other _ _ Hx).
Qed.

Lemma cs_len_ok_f_write (so : fostage) (b : bv 8) :
  cs_len_ok_f so ->
  (fo_w so <> [] \/ rest_of (snd <$> fo_E so) <> [] \/ (snd <$> fo_E so) = []) ->
  cs_len_ok_f (MkFO (fo_ps so) (fo_cs so) (fo_E so) (fo_w so ++ [b]) (fo_f0 so)).
Proof using.
  intros Hc Hcase. apply cs_len_ok_f_intro.
  { intros [Hw _]. exfalso.
    by destruct (app_eq_nil (fo_w so) [b] Hw) as [_ Hb]. }
  intros _. destruct (cs_len_ok_f_inv so Hc) as [[[Hw Hm] Hq] | [_ Hq]];
    [| exact Hq].
  destruct Hcase as [Hw' | [Hm' | Hn]]; [done | done |].
  rewrite Hq Hn nlines_nil. lia.
Qed.

Lemma cs_len_ok_f_blk (so : fostage) (a : nat) (b : bv 8) :
  rest_of (snd <$> fo_E so) = [] ->
  (snd <$> fo_E so) <> [] ->
  fo_w so = [] ->
  cs_len_ok_f so ->
  cs_len_ok_f (MkFO (fo_ps so) (fo_cs so ++ [a]) (fo_E so) [b] (fo_f0 so)).
Proof using.
  intros Hr Hne Hw Hc.
  pose proof (nlines_pos_of_rest_nil (snd <$> fo_E so) Hne Hr) as Hpos.
  destruct (cs_len_ok_f_inv so Hc) as [[_ Hq] | [Hne' _]]; last first.
  { exfalso. by apply Hne'. }
  apply cs_len_ok_f_intro.
  { intros [Hb _]. discriminate. }
  intros _. rewrite length_app. cbn [length]. rewrite Hq. lia.
Qed.

Lemma cs_len_ok_f_0 : cs_len_ok_f fostage0.
Proof using.
  rewrite /fostage0. apply (cs_len_ok_f_intro [] [] [] [] None); intros _;
    cbn [length]; rewrite fmap_nil nlines_nil; lia.
Qed.

(* ---- the prologue resolution's length law ---- *)

Definition ps_round_f (so : fostage) : nat :=
  pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so)).

Definition ps_opens_f (so : fostage) : Prop :=
  (snd <$> fo_E so) = []
  \/ (rest_of (snd <$> fo_E so) = []
      /\ ralt_panic (ralt_at (fo_cs so)
                       (nlines (snd <$> fo_E so) - 1)%nat) = true).

Definition ps_len_ok_f (so : fostage) : Prop :=
  pro_from (S (ps_round_f so)) (fo_ps so) = []
  /\ (ps_opens_f so ->
      forall ps' : list nat, ps' `prefix_of` fo_ps so ->
        pro_of (pro_from (ps_round_f so) ps')
          <> pro_of (pro_from (ps_round_f so) (fo_ps so)) ->
        (length (pending_at_f ps' (fo_cs so) (fo_f0 so) (snd <$> fo_E so))
         < length (fo_w so))%nat).

Lemma ps_len_ok_f_empty_above (so : fostage) (R : nat) :
  ps_len_ok_f so -> (ps_round_f so <= R)%nat -> pro_from (S R) (fo_ps so) = [].
Proof using.
  intros [HA _] HR.
  replace (S R) with (S (ps_round_f so) + (R - ps_round_f so))%nat by lia.
  rewrite -pro_from_add HA. apply pro_from_nil.
Qed.

Lemma ps_len_ok_f_0 : ps_len_ok_f fostage0.
Proof using.
  rewrite /ps_len_ok_f /ps_round_f /fostage0.
  cbn [fo_ps fo_cs fo_E fo_w fo_f0]. split.
  - apply pro_from_nil.
  - intros _ ps' Hp Hne. exfalso. apply Hne.
    by rewrite (prefix_nil_inv ps' Hp).
Qed.

Lemma ps_len_ok_f_write (so : fostage) (b : bv 8) :
  ps_len_ok_f so ->
  ps_len_ok_f (MkFO (fo_ps so) (fo_cs so) (fo_E so) (fo_w so ++ [b]) (fo_f0 so)).
Proof using.
  intros [HA HB]. rewrite /ps_len_ok_f /ps_round_f /ps_opens_f in HA, HB |- *.
  cbn [fo_ps fo_cs fo_E fo_w fo_f0] in HA, HB |- *. split; [exact HA |].
  intros Ho ps' Hp Hne. rewrite (length_app (fo_w so) [b]). cbn [length].
  pose proof (HB Ho ps' Hp Hne). lia.
Qed.

Lemma ps_len_ok_f_blk (so : fostage) (a : nat) (b : bv 8) :
  rest_of (snd <$> fo_E so) = [] ->
  (snd <$> fo_E so) <> [] ->
  length (fo_cs so) = (nlines (snd <$> fo_E so) - 1)%nat ->
  ps_len_ok_f so ->
  ps_len_ok_f (MkFO (fo_ps so) (fo_cs so ++ [a]) (fo_E so) [b] (fo_f0 so)).
Proof using.
  intros Hr Hne Hq Hok.
  pose proof (nlines_pos_of_rest_nil (snd <$> fo_E so) Hne Hr) as Hpos.
  pose proof Hok as [HA HB].
  rewrite /ps_len_ok_f /ps_round_f /ps_opens_f in HA, HB |- *.
  cbn [fo_ps fo_cs fo_E fo_w fo_f0] in HA, HB |- *.
  assert (Hold : pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))
                 = pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so) - 1)%nat).
  { replace (nlines (snd <$> fo_E so))
      with (S (nlines (snd <$> fo_E so) - 1))%nat at 1 by lia.
    apply pro_idx_f_Sn. apply ralt_panic_ge. lia. }
  assert (Hnew : (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))
                  <= pro_idx_f (fo_cs so ++ [a])
                       (nlines (snd <$> fo_E so)))%nat).
  { rewrite Hold.
    replace (nlines (snd <$> fo_E so))
      with (S (nlines (snd <$> fo_E so) - 1))%nat at 2 by lia.
    rewrite pro_idx_f_S
      (pro_idx_f_app_le (fo_cs so) [a] (nlines (snd <$> fo_E so) - 1)%nat
         ltac:(lia)).
    destruct (ralt_panic _); lia. }
  split.
  - apply (ps_len_ok_f_empty_above so); [exact Hok |].
    rewrite /ps_round_f. exact Hnew.
  - intros Ho ps' Hp Hne2. exfalso.
    destruct Ho as [Hz | [_ H3]]; [by destruct (Hne Hz) |].
    assert (Ha3 : ralt_panic (ralt_dec a) = true).
    { rewrite /ralt_at list_lookup_total_alt lookup_app_r in H3; [| lia].
      rewrite Hq Nat.sub_diag in H3. by cbn in H3. }
    assert (Heq : pro_idx_f (fo_cs so ++ [a]) (nlines (snd <$> fo_E so))
                  = S (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so)))).
    { rewrite Hold
        -(pro_idx_f_app_le (fo_cs so) [a] (nlines (snd <$> fo_E so) - 1)%nat
            ltac:(lia)).
      replace (nlines (snd <$> fo_E so))
        with (S (nlines (snd <$> fo_E so) - 1))%nat at 1 by lia.
      apply pro_idx_f_Sp.
      rewrite /ralt_at list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hq Nat.sub_diag. by cbn. }
    rewrite Heq in Hne2. apply Hne2.
    assert (Hnil : pro_from
                     (S (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))))
                     (fo_ps so) = []) by exact HA.
    assert (Hnil' : pro_from
                      (S (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))))
                      ps' = []).
    { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
    by rewrite Hnil Hnil'.
Qed.

Lemma ps_len_ok_f_echo (so : fostage) (x : list mobs * bv 8) :
  ps_len_ok_f so ->
  ps_len_ok_f (MkFO (fo_ps so) (fo_cs so) (fo_E so ++ [x]) [] (fo_f0 so)).
Proof using.
  intros Hok. pose proof Hok as [HA HB].
  rewrite /ps_len_ok_f /ps_round_f /ps_opens_f in HA, HB |- *.
  cbn [fo_ps fo_cs fo_E fo_w fo_f0] in HA, HB |- *.
  rewrite fmap_app /=.
  assert (Hmono : (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))
                   <= pro_idx_f (fo_cs so)
                        (nlines ((snd <$> fo_E so) ++ [x.2])))%nat)
    by (apply pro_idx_f_mono, nlines_app_le).
  split.
  - apply (ps_len_ok_f_empty_above so); [exact Hok |].
    rewrite /ps_round_f. exact Hmono.
  - intros Ho ps' Hp Hne. exfalso.
    destruct Ho as [Hz | [Hr H3]].
    { by destruct (app_eq_nil (snd <$> fo_E so) [x.2] Hz) as [_ Hb]. }
    assert (Hx : x.2 = wl_nl).
    { destruct (decide (x.2 = wl_nl)) as [Hx | Hx]; [exact Hx | exfalso].
      rewrite (rest_of_snoc_other (snd <$> fo_E so) x.2 Hx) in Hr.
      by destruct (app_eq_nil (rest_of (snd <$> fo_E so)) [x.2] Hr) as [_ Hb]. }
    rewrite Hx (nlines_snoc_nl (snd <$> fo_E so)) in H3.
    rewrite Hx (nlines_snoc_nl (snd <$> fo_E so)) in Hne.
    replace (S (nlines (snd <$> fo_E so)) - 1)%nat
      with (nlines (snd <$> fo_E so)) in H3 by lia.
    assert (Heq : pro_idx_f (fo_cs so) (S (nlines (snd <$> fo_E so)))
                  = S (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))))
      by (apply pro_idx_f_Sp; exact H3).
    rewrite Heq in Hne. apply Hne.
    assert (Hnil : pro_from
                     (S (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))))
                     (fo_ps so) = []) by exact HA.
    assert (Hnil' : pro_from
                      (S (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))))
                      ps' = []).
    { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
    by rewrite Hnil Hnil'.
Qed.

Lemma ps_len_ok_f_pro (so : fostage) (a : nat) (b : bv 8) :
  (ps_round_f so <= pro_rounds (fo_ps so))%nat ->
  ~ pro_done (pro_from (ps_round_f so) (fo_ps so)) ->
  fo_w so = pending_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so) ->
  ps_len_ok_f so ->
  ps_len_ok_f (MkFO (fo_ps so ++ [a]) (fo_cs so) (fo_E so)
                 (fo_w so ++ [b]) (fo_f0 so)).
Proof using.
  intros Hle Hnd Hw [HA HB].
  rewrite /ps_len_ok_f /ps_round_f /ps_opens_f in HA, HB, Hle, Hnd |- *.
  cbn [fo_ps fo_cs fo_E fo_w fo_f0] in HA, HB, Hle, Hnd |- *. split.
  - replace (S (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))))
      with (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so)) + 1)%nat by lia.
    rewrite -pro_from_add (pro_from_snoc_le _ (fo_ps so) a Hle).
    cbn [pro_from]. by apply pro_tail_open_snoc.
  - intros Ho ps' Hp Hne. rewrite (length_app (fo_w so) [b]). cbn [length].
    destruct (decide (length ps' <= length (fo_ps so))%nat) as [Hlen | Hlen].
    + assert (Hp2 : ps' `prefix_of` fo_ps so).
      { destruct (prefix_weak_total ps' (fo_ps so) (fo_ps so ++ [a]) Hp
                    ltac:(by eexists)) as [H | H]; [exact H |].
        rewrite (prefix_length_eq _ _ H ltac:(lia)). reflexivity. }
      pose proof (prefix_length _ _ (pending_at_f_ps_mono ps' (fo_ps so)
                    (fo_cs so) (fo_f0 so) (snd <$> fo_E so) Hp2)) as Hlp.
      rewrite -/(pending_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)) -Hw
        in Hlp. lia.
    + rewrite (prefix_length_eq ps' (fo_ps so ++ [a]) Hp) in Hne;
        last by (rewrite (length_app (fo_ps so) [a]); cbn [length]; lia).
      by destruct (Hne eq_refl).
Qed.

(* ====================================================================== *)
(*  10.  THE STAGE'S WHOLE PURE ACCOUNT                                    *)
(* ====================================================================== *)

Definition feout_pure (k : nat) (ho : list mobs) (so : fostage)
    (acc : list (bv 8)) : Prop :=
  acc = D_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so) ++ fo_w so
  /\ fo_w so `prefix_of` pending_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)
  /\ E_index (fo_E so)
  /\ E_disc_f (fo_E so)
  /\ Forall (fun a => (a < length pro_alts)%nat) (fo_ps so)
  /\ pro_pin_f (fo_ps so) (fo_cs so) (snd <$> fo_E so)
  /\ alts_pre (snd <$> fo_E so) (fo_cs so)
  /\ Forall (fun x => disc_seg_f (ehist x)) (fo_E so)
  /\ Forall (fun x => ehist x `prefix_of` open_seg ho) (fo_E so)
  /\ (length (fo_E so) <= length (ins (open_seg ho)))%nat
  /\ (fo_E so = [] \/ obs_boots ho = k)
  (* THE TWO CLAUSES THE FILE ADDS.  The first is design section 4.1's
     "[o_f0] is [None] until the era's first process byte": the era's boot
     state is not read before it is filed, and the discipline puts no input
     before init's banner.  The second is what the determinacy argument
     spends -- a file holds a content, never junk. *)
  /\ (fo_f0 so = None <-> (fo_E so = [] /\ fo_w so = []))
  /\ fst_ok (f0_st (fo_f0 so)).

Lemma feout_pure_0 k ho : feout_pure k ho fostage0 [].
Proof using.
  rewrite /feout_pure /fostage0. cbn [fo_ps fo_cs fo_E fo_w fo_f0].
  split_and!.
  - rewrite D_f_nil. done.
  - rewrite pending_f_nil. apply prefix_nil.
  - intros j x Hx. by rewrite lookup_nil in Hx.
  - rewrite /E_disc_f fmap_nil. exact disc_input_f_nil.
  - constructor.
  - rewrite fmap_nil. intros q Hq. rewrite nstarted_nil in Hq. lia.
  - apply alts_pre_nil.
  - constructor.
  - constructor.
  - cbn [length]. lia.
  - by left.
  - split; [by intros _ | by intros _].
  - exact I.
Qed.

(* the era's stream opens with the block the EMPTY input owes, so a stage
   whose input is nonempty has already owed the whole prologue *)
Lemma proc_before_f_head (ps cs : list nat) (f0 : option fst)
    (I : list (bv 8)) :
  I <> [] ->
  pending_at_f ps cs f0 [] `prefix_of` proc_before_f ps cs f0 I.
Proof using.
  destruct I as [| b I']; [done |]. intros _.
  rewrite /proc_before_f. cbn [proc_before_from_f]. by eexists.
Qed.

(* ---- THE PADDING MOVES NO PROLOGUE ROUND.  [pro_idx_f] reads the choice
       list only through [ralt_panic], and neither the out-of-range reading
       ([REcho 0]) nor any default alternative panics -- so a stage's round
       index is the same at its own list and at the padded one. ---- *)
Lemma ralt_panic_def (l : uline) : ralt_panic (ralt_dec (ralt_def l)) = false.
Proof using.
  destruct l as [ws | ws |]; cbn [ralt_def].
  - rewrite (ralt_dec_lt4 0%nat ltac:(lia)). by vm_compute.
  - rewrite ralt_dec_enc. by vm_compute.
  - rewrite ralt_dec_enc. by vm_compute.
Qed.

Lemma pro_idx_f_ext_panic (cs1 cs2 : list nat) (q : nat) :
  (forall j, (j < q)%nat ->
     ralt_panic (ralt_at cs1 j) = ralt_panic (ralt_at cs2 j)) ->
  forall j, (j <= q)%nat -> pro_idx_f cs1 j = pro_idx_f cs2 j.
Proof using.
  intros Hj j. induction j as [| j IH]; intros Hjq; [done |].
  rewrite !pro_idx_f_S IH; [| lia]. by rewrite (Hj j ltac:(lia)).
Qed.

Lemma alts_pad_panic (I : list (bv 8)) (cs : list nat) (j : nat) :
  (j < nlines I)%nat ->
  ralt_panic (ralt_at (alts_pad I cs) j) = ralt_panic (ralt_at cs j).
Proof using.
  intros Hj. destruct (decide (j < length cs)%nat) as [Hlt | Hge].
  - by rewrite /ralt_at (fop_lta_prefix cs (alts_pad I cs) j
                           (alts_pad_prefix I cs) Hlt).
  - rewrite (ralt_panic_ge cs j ltac:(lia)).
    destruct (decide (j < length (alts_pad I cs))%nat) as [Hlt2 | Hge2];
      last first.
    { by rewrite (ralt_panic_ge (alts_pad I cs) j ltac:(lia)). }
    (* inside the PAD: the entry is the line's default alternative *)
    assert (Hjl : (j < length (lines_of I))%nat)
      by (rewrite lines_of_length; lia).
    destruct (lookup_lt_is_Some_2 (lines_of I) j Hjl) as [l Hl].
    assert (Hlk : alts_pad I cs !!! j = ralt_def l).
    { rewrite /alts_pad list_lookup_total_alt lookup_app_r; [| lia].
      rewrite list_lookup_fmap lookup_drop.
      replace (length cs + (j - length cs))%nat with j by lia.
      by rewrite Hl. }
    rewrite /ralt_at Hlk. exact (ralt_panic_def _).
Qed.

Lemma alts_pad_pro_idx (I : list (bv 8)) (cs : list nat) (q : nat) :
  (q <= nlines I)%nat -> pro_idx_f (alts_pad I cs) q = pro_idx_f cs q.
Proof using.
  intro Hq. apply (pro_idx_f_ext_panic (alts_pad I cs) cs (nlines I));
    [| exact Hq].
  intros j Hj. exact (alts_pad_panic I cs j Hj).
Qed.

(* THE STAGE'S TRANSCRIPT AT A FULL RESOLUTION.  [FileDisc.sessf_prefix_det]
   and [good_out_f] are stated at an [alts_ok] -- a resolution with one
   entry per completed line -- and the stage's list runs one short at a
   block boundary.  This packages the padding: the padded list agrees with
   the stage's wherever the stage reads it, and the stage's transcript is
   below the padded session. *)
Lemma stage_sessf_pad (ps cs : list nat) (f0 : option fst)
    (E : list (list mobs * bv 8)) (w : list (bv 8)) :
  alts_pre (snd <$> E) cs ->
  (nlines (removelast (snd <$> E)) <= length cs)%nat ->
  ((nlines (snd <$> E) <= length cs)%nat \/ w = []) ->
  E_disc_f E ->
  pro_pin_f ps cs (snd <$> E) ->
  w `prefix_of` pending_f ps cs f0 E ->
  alts_ok (snd <$> E) (alts_pad (snd <$> E) cs)
  /\ pro_pin_f ps (alts_pad (snd <$> E) cs) (snd <$> E)
  /\ D_f ps cs f0 E = D_f ps (alts_pad (snd <$> E) cs) f0 E
  /\ w `prefix_of` pending_f ps (alts_pad (snd <$> E) cs) f0 E
  /\ (D_f ps cs f0 E ++ w)
       `prefix_of` sessf ps (alts_pad (snd <$> E) cs) (f0_st f0) (snd <$> E).
Proof using.
  intros Hao Hrl Hlast HE Hpin Hw.
  set (cs' := alts_pad (snd <$> E) cs).
  assert (Hcc : cs `prefix_of` cs') by apply alts_pad_prefix.
  assert (Hok : alts_ok (snd <$> E) cs') by exact (alts_pad_ok _ cs Hao).
  assert (Hpin' : pro_pin_f ps cs' (snd <$> E)).
  { intros q Hq.
    assert (Hqle : (q <= nlines (snd <$> E))%nat).
    { pose proof (nstarted_le_S (snd <$> E)). lia. }
    rewrite /cs' (alts_pad_pro_idx (snd <$> E) cs q Hqle). by apply Hpin. }
  assert (HD : D_f ps cs f0 E = D_f ps cs' f0 E)
    by (apply (D_f_cs_prefix ps ps cs cs' f0 E ltac:(reflexivity) Hcc Hpin Hrl)).
  assert (Hw' : w `prefix_of` pending_f ps cs' f0 E).
  { destruct Hlast as [Hle | ->]; [| apply prefix_nil].
    rewrite /pending_f
      -(pending_at_f_cs_ext ps cs cs' f0 (snd <$> E) Hcc Hle). exact Hw. }
  split_and!; [exact Hok | exact Hpin' | exact HD | exact Hw' |].
  rewrite HD. exact (D_f_stage_prefix ps cs' f0 E w HE Hw').
Qed.

(* past the choice list's end the round pointer stops moving: every entry
   there reads [REcho 0], which does not panic *)
Lemma pro_idx_f_ge (cs : list nat) (q q' : nat) :
  (length cs <= q)%nat -> (q <= q')%nat -> pro_idx_f cs q' = pro_idx_f cs q.
Proof using.
  intros Hle Hq. induction q' as [| q' IH].
  - assert (Hz : q = 0%nat) by lia. by subst q.
  - destruct (decide (q = S q')) as [-> | Hne]; [reflexivity |].
    rewrite pro_idx_f_S (IH ltac:(lia)) (ralt_panic_ge cs q' ltac:(lia)). lia.
Qed.

(* AN EVENT THAT PUTS NOTHING ON THE CONSOLE'S WIRE cannot falsify a cycle
   that was good -- [EchoOut.good_out_step]'s twin.  It needs one more move
   than the echo one: the extended input may have one more COMPLETE LINE,
   and [FileDisc.alts_ok] demands an entry per line, so the resolution is
   padded.  The padding moves no prologue round ([alts_pad_pro_idx]) and
   changes no block the shorter input had ([alts_pad_take] through
   [FileDisc.sessf_take]), so the same [ps] still answers. *)
Lemma good_out_f_step (s : fst) (seg : list mobs) (e : mobs) :
  obs_wire Uart0 [e] = [] -> good_out_f s seg -> good_out_f s (seg ++ [e]).
Proof using.
  intros He (ps & cs & [Hpsb Hlt] & Hao & Hwire).
  set (I := ins seg). set (I' := ins (seg ++ [e])).
  assert (HII : I `prefix_of` I') by (rewrite /I /I' ins_app; by eexists).
  assert (Hlen : length cs = nlines I) by exact (alts_ok_length _ _ Hao).
  assert (Hnl : (nlines I <= nlines I')%nat) by (by apply nlines_prefix).
  set (cs' := alts_pad I' cs).
  exists ps, cs'. split.
  { split; [exact Hpsb |].
    rewrite /cs' (alts_pad_pro_idx I' cs (nlines I') ltac:(lia)).
    (* the pad is read only past the shorter input's last line, and a
       default alternative never panics *)
    rewrite (pro_idx_f_ge cs (nlines I) (nlines I') ltac:(lia) Hnl).
    exact Hlt. }
  split.
  { rewrite /cs'. apply alts_pad_ok.
    apply (alts_pre_mono I I'); [exact HII | exact (alts_pre_of_alts_ok _ _ Hao)]. }
  rewrite /I' obs_wire_app He app_nil_r.
  etrans; [exact Hwire |].
  assert (Hcut : sessf ps cs s I = sessf ps cs' s I).
  { rewrite -{1}(alts_pad_take I' cs) -/cs'.
    apply sessf_take. lia. }
  rewrite Hcut. by apply sessf_mono.
Qed.
