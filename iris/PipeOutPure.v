(* PipeOutPure.v -- THE PIPELINE APPLICATION'S STAGE MACHINE, PURE.

   Design of record: claude-notes/design/app-pipe.md section 4.1, lane
   PIPE-STAGE, deliverable 1.  This file is [EchoOutPure.v]'s twin at
   [PipeDisc.sessp] -- the same stage machine over the pipeline session --
   and it is SIMPLER than upstream's [FileOutPure.v], because a pipe dies
   with its era: there is NO per-era extra state, no boot value, no typed
   witness, and nothing to thread.  Where [FileOutPure] carries [fo_f0]
   through every block, this file carries nothing.

   WHAT CHANGES FROM [EchoOutPure], AND WHAT DOES NOT.

   - [pending_at_p ps cs I] and [D_p ps cs E] are [EchoOutPure.pending_at]
     and [D] at [PipeDisc.alt_cont_p]; the append laws, F1 and F2 are that
     file's, lemma for lemma.
   - the range condition that was [Forall (fun c => c < 4) cs] is
     [alts_pre_p I cs]: every entry the choice list HAS is an alternative
     the LINE AT THAT INDEX admits.  It is POINTWISE and not
     [PipeDisc.alts_ok_p], because the list runs one short at a block
     boundary (a program files its alternative at the block's FIRST byte,
     which is after the echo that completed the line).  [alts_pad_p] fills
     it out, which is what lets the determinacy theorem -- stated at a FULL
     resolution -- be applied to a stage standing at a boundary.
   - [EchoOutPure]'s [cs_ok] HAS NO TWIN, for upstream's reason exactly:
     out of range [!!!] reads [0], which decodes to [PipeDisc.PEcho 0], and
     [palt_ok (LPipe ws) (PEcho 0)] is FALSE (after PIPE-MODEL-2's ruling
     only [PEcho 3] joins a pipeline line's alternatives).  So no total
     condition on [cs] can replace it and the padding is the honest fix --
     the same route [FileOutPure] took at [ralt_ok].
   - the prologue counter is [PipeDisc.pro_idx_p] (it counts [palt_panic],
     i.e. [PEcho 3], at EITHER line shape) and the side condition is
     [pro_ok_p] / [pro_pin_p].
   - F3 is [EchoOutPure.read_window_prefix] VERBATIM: it is about the log
     and the echoed entries and names no discipline.

   DETERMINACY NEEDS NO SECOND WITNESS.  [FileOutPure.sessf_prefix_det2]
   exists only because a file's transcript reads the era's BOOT STATE, and
   the discipline's witness for it and the claim's own have no reason to be
   equal.  A pipeline round reads no state at all, so
   [PipeDisc.sessp_prefix_det] IS the lemma the stage spends;
   [sessp_prefix_det2] below is its restatement under the brief's name and
   is proved by [exact].  (Reported as such.)

   THE DISCIPLINE'S CLOSURE LAWS are here too ([disc_p_out], [disc_p_in],
   [disc_p_power], [disc_p_other], [disc_p_prefix]): [PipeDisc] landed
   [disc_input_p]'s full set and, of [disc_p]'s, only [disc_p_nil] and
   [disc_p_seg]; the ledger's three steps are stated at exactly these. *)
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
Require Import PipeDisc.
(* as in EchoDisc / EchoOutPure: a pure file does not inherit ssreflect's
   [rewrite] from the proofmode, so it is imported by name *)
From stdpp Require Import ssreflect.
Local Open Scope nat_scope.

(* ====================================================================== *)
(*  0.  SMALL LIST FACTS [EchoOut.v] ALSO STATES                           *)
(*                                                                        *)
(*  They are pure and sit ABOVE this file (in [EchoOut.v]), which this     *)
(*  file must not import: the claim's cone would drag [WpUart] into a      *)
(*  logic-free file.  Copied with a [pop_] prefix, exactly as             *)
(*  [FileOutPure] copies them with [fop_].                                 *)
(* ====================================================================== *)

Lemma pop_app_nonnil_r {A} (u v : list A) : v <> [] -> u ++ v <> [].
Proof using.
  intros Hv Hq. apply Hv. by destruct (app_eq_nil u v Hq) as [_ Hb].
Qed.

Lemma pop_snoc_cases {A} (l : list A) : l = [] \/ exists u x, l = u ++ [x].
Proof using.
  induction l as [| a l IH]; [by left |]. right.
  destruct IH as [-> | (u & x & ->)].
  - by exists [], a.
  - by exists (a :: u), x.
Qed.

Lemma pop_removelast_take {A} (l : list A) :
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

Lemma pop_removelast_prefix {A} (l : list A) : removelast l `prefix_of` l.
Proof using. rewrite pop_removelast_take. apply prefix_take. Qed.

Lemma pop_prefix_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> removelast l `prefix_of` removelast l'.
Proof using.
  intros Hp. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Ht : take (length l - 1)%nat l = take (length l - 1)%nat l').
  { destruct Hp as [z ->].
    rewrite (take_app_le l z (length l - 1)%nat); [done | lia]. }
  rewrite !pop_removelast_take Ht. apply prefix_take_le. lia.
Qed.

Lemma pop_prefix_of_removelast {A} (l l' : list A) :
  l `prefix_of` l' -> l <> l' -> l `prefix_of` removelast l'.
Proof using.
  intros Hp Hne. pose proof (prefix_length _ _ Hp) as Hlen.
  assert (Hlt : (length l < length l')%nat).
  { destruct (decide (length l = length l')) as [He | He]; [| lia].
    exfalso. exact (Hne (prefix_length_eq _ _ Hp ltac:(lia))). }
  assert (Hl : l = take (length l) l').
  { destruct Hp as [z ->]. by rewrite take_app_length. }
  rewrite pop_removelast_take {1}Hl. apply prefix_take_le. lia.
Qed.

Lemma pop_nlines_removelast (I : list (bv 8)) :
  rest_of I = [] -> nlines (removelast I) = (nlines I - 1)%nat.
Proof using.
  intros Hr. destruct (pop_snoc_cases I) as [-> | (u & x & ->)].
  - cbn [removelast]. rewrite nlines_nil. lia.
  - destruct (decide (x = wl_nl)) as [-> | Hx].
    + rewrite epu_removelast_snoc nlines_snoc_nl. lia.
    + exfalso. rewrite (rest_of_snoc_other u x Hx) in Hr.
      by destruct (app_eq_nil (rest_of u) [x] Hr) as [_ Hb].
Qed.

Lemma pop_nstarted_rest_nil (I : list (bv 8)) :
  rest_of I = [] -> nstarted I = nlines I.
Proof using.
  intros Hr. rewrite /nstarted Hr. case_decide as Hd;
    [lia | by destruct (Hd eq_refl)].
Qed.

Lemma pop_nstarted_snoc (I : list (bv 8)) (b : bv 8) :
  nstarted (I ++ [b]) = S (nlines I).
Proof using.
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - apply nstarted_snoc_nl.
  - by apply nstarted_snoc_other.
Qed.

Lemma pop_lta_prefix (cs0 cs : list nat) (i : nat) :
  cs0 `prefix_of` cs -> (i < length cs0)%nat -> cs !!! i = cs0 !!! i.
Proof using.
  intros [z ->] Hi. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Lemma pop_prefix_snoc_lookup {A} (w l : list A) (b : A) :
  w `prefix_of` l -> l !! length w = Some b -> (w ++ [b]) `prefix_of` l.
Proof using.
  intros [z ->] Hl. rewrite lookup_app_r in Hl; [| lia].
  rewrite Nat.sub_diag in Hl.
  destruct z as [| c z]; [discriminate |]. cbn in Hl. injection Hl as <-.
  exists z. by rewrite -app_assoc.
Qed.

(* ====================================================================== *)
(*  1.  THE BYTES OF A DISCIPLINED PIPELINE INPUT                          *)
(* ====================================================================== *)

(* every byte of a disciplined input is a body byte, a '|' or the newline --
   [EchoDisc.disc_input_byte] with [PipeDisc.pbody_byte] where
   [wl_body_byte] was *)
Lemma disc_input_p_byte (I : list (bv 8)) (b : bv 8) :
  disc_input_p I -> b ∈ I -> pbody_byte b \/ b = wl_nl.
Proof using.
  intros Hd Hin. pose proof Hd as (Hb & Hr & _).
  rewrite (wl_cut_join I) in Hin.
  apply elem_of_app in Hin as [Hin | Hin].
  - destruct (join_elem_of (bodies_of I) b Hin) as [-> | (l & Hl & Hbl)];
      [by right | left].
    apply elem_of_list_lookup in Hl as [k Hk].
    pose proof (pbody_ok_bytes l (disc_input_p_body I k l Hd Hk)) as Hfb.
    exact (proj1 (Forall_forall _ _) Hfb b Hbl).
  - left. exact (proj1 (Forall_forall _ _) Hr b Hin).
Qed.

Lemma wl_bar_val : bv_unsigned wl_bar = 124%Z.
Proof using. by vm_compute. Qed.

(* [EchoOutPure.echo_byte_ne] is [Local]; this is that step, which is what
   turns every refutation below into one [lia] against the byte reading *)
Local Lemma pop_byte_ne (c : bv 8) (z : Z) :
  bv_unsigned c <> z ->
  bv_unsigned (mword_of_int z : mword 8) = z ->
  eq_vec (c : mword 8) (mword_of_int z : mword 8) = false.
Proof using.
  intros Hne Hz. apply eq_vec_false_iff. intro Hq.
  apply (f_equal bv_unsigned) in Hq. rewrite Hz in Hq. exact (Hne Hq).
Qed.

Lemma disc_input_p_byte_val (I : list (bv 8)) (b : bv 8) :
  disc_input_p I -> b ∈ I ->
  bv_unsigned b = 10%Z \/ bv_unsigned b = 32%Z \/ bv_unsigned b = 124%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof using.
  intros Hd Hin.
  destruct (disc_input_p_byte I b Hd Hin) as [[[Ha | ->] | ->] | ->].
  - destruct Ha as [H | [H | H]];
      [ right; right; right; by left
      | right; right; right; right; by left
      | right; right; right; right; by right ].
  - right. left. exact wl_sp_val.
  - right. right. left. exact wl_bar_val.
  - left. exact wl_nl_val.
Qed.

(* A DISCIPLINED INPUT HOLDS NO '\r', NO ERASE BYTE AND NO ^D, exactly as
   [EchoOutPure.disc_byte_ok] says for the echo application: the third
   clause refutes the read path's SWALLOW arm and the second the gap
   clause's erase disjunct. *)
Lemma disc_byte_ok_p (I : list (bv 8)) (c : bv 8) :
  disc_input_p I -> c ∈ I ->
  c <> (mword_of_int 13 : mword 8) /\ cons_erase c = false
  /\ bv_unsigned c <> 4%Z.
Proof using.
  intros Hd Hc. pose proof (disc_input_p_byte_val I c Hd Hc) as Hv.
  split_and!.
  - intro Hq. apply (f_equal bv_unsigned) in Hq.
    rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
      [lia | by vm_compute].
  - rewrite /cons_erase.
    rewrite (pop_byte_ne c 21 ltac:(lia) ltac:(by vm_compute)).
    rewrite (pop_byte_ne c 8 ltac:(lia) ltac:(by vm_compute)).
    rewrite (pop_byte_ne c 127 ltac:(lia) ltac:(by vm_compute)).
    reflexivity.
  - lia.
Qed.

Lemma echo_of_disc_p (I : list (bv 8)) (c : bv 8) :
  disc_input_p I -> c ∈ I -> echo_of c = c.
Proof using. intros Hd Hc. apply echo_of_other, (disc_byte_ok_p I c Hd Hc). Qed.

Lemma disc_seg_p_last_in (h : list mobs) (c : bv 8) :
  disc_seg_p h -> obs_ends_in Uart0 h c -> c ∈ ins h.
Proof using.
  intros _ [h0 ->]. rewrite ins_app ins_in.
  apply elem_of_app. right. apply elem_of_list_here.
Qed.

Lemma disc_seg_p_no_erase (h : list mobs) (c : bv 8) :
  disc_seg_p h -> obs_ends_in Uart0 h c -> cons_erase c = false.
Proof using.
  intros Hd He.
  apply (disc_byte_ok_p (ins h) c Hd (disc_seg_p_last_in h c Hd He)).
Qed.

Lemma disc_seg_p_no_ctrl_d (h : list mobs) (c : bv 8) :
  disc_seg_p h -> obs_ends_in Uart0 h c -> bv_unsigned c <> 4%Z.
Proof using.
  intros Hd He.
  apply (disc_byte_ok_p (ins h) c Hd (disc_seg_p_last_in h c Hd He)).
Qed.

(* ====================================================================== *)
(*  1b.  THE DISCIPLINE'S CLOSURE LAWS                                     *)
(* ====================================================================== *)

Lemma plines_of_prefix (I I' : list (bv 8)) :
  I `prefix_of` I' -> plines_of I `prefix_of` plines_of I'.
Proof using.
  intros Hp. destruct (bodies_of_prefix I I' Hp) as [z Hz].
  rewrite /plines_of Hz fmap_app. by eexists.
Qed.

Lemma plines_of_length (I : list (bv 8)) : length (plines_of I) = nlines I.
Proof using. by rewrite /plines_of length_fmap. Qed.

Lemma alts_ok_p_take (I I' : list (bv 8)) (cs : list nat) :
  I' `prefix_of` I -> alts_ok_p I cs -> alts_ok_p I' (take (nlines I') cs).
Proof using.
  intros Hp Ha.
  pose proof (alts_ok_p_length I cs Ha) as Hlen.
  assert (Hle : (nlines I' <= nlines I)%nat) by (by apply nlines_prefix).
  assert (Hl' : plines_of I' = take (nlines I') (plines_of I)).
  { destruct (plines_of_prefix I' I Hp) as [z Hz].
    rewrite Hz take_app_length'; [reflexivity | by rewrite plines_of_length]. }
  rewrite /alts_ok_p Hl'. apply Forall2_take. exact Ha.
Qed.

Lemma disc_seg_p'_other (seg : list mobs) (e : mobs) :
  not_cons_in e -> disc_seg_p' (seg ++ [e]) <-> disc_seg_p' seg.
Proof using.
  intro He.
  assert (Hi : in_pres (seg ++ [e]) = in_pres seg)
    by (by apply in_pres_snoc_other).
  assert (Hn : ins (seg ++ [e]) = ins seg)
    by (rewrite ins_app (ins_snoc_other e He) app_nil_r; reflexivity).
  rewrite /disc_seg_p' /disc_seg_p Hi Hn. done.
Qed.

Lemma disc_seg_p'_out (seg : list mobs) (i : uart_id) (b : bv 8) :
  disc_seg_p' (seg ++ [ObsUartOut i b]) <-> disc_seg_p' seg.
Proof using. apply disc_seg_p'_other. by destruct i. Qed.

Lemma disc_p_other (h : list mobs) (e : mobs) :
  is_io e = true -> not_cons_in e -> trace_shape h true ->
  disc_p (h ++ [e]) <-> disc_p h.
Proof using.
  intros Hio He Hsh.
  destruct (cycles_of_io h [e] Hsh) as (cs & Hc & Hc'); [by constructor |].
  rewrite /disc_p Hc Hc' !Forall_app !Forall_singleton
          (disc_seg_p'_other _ _ He). done.
Qed.

Lemma disc_p_out (h : list mobs) (i : uart_id) (b : bv 8) :
  trace_shape h true -> disc_p (h ++ [ObsUartOut i b]) <-> disc_p h.
Proof using.
  intro Hsh. apply disc_p_other; [by destruct i | by destruct i | exact Hsh].
Qed.

Lemma disc_p_power (h : list mobs) (on : bool) :
  disc_p (h ++ [if on then ObsPowerOff else ObsPowerOn]) <-> disc_p h.
Proof using.
  rewrite /disc_p. destruct on.
  - by rewrite cycles_of_off.
  - rewrite cycles_of_on Forall_app Forall_singleton.
    split; [by intros [? _] |].
    intros ?. split; [done | exact disc_seg_p'_nil].
Qed.

(* THE INPUT STEP.  [EchoDisc.disc_seg'_in]'s twin: dropping the last input
   byte drops at most one line, so the witness resolution is TRUNCATED --
   [PipeDisc.sessp_take] then says the shorter transcript is the same
   bytes, and [alts_ok_p_take] that the truncation is still a resolution. *)
(* ---- D4 AT AN INPUT PREFIX IS VACUOUS ------------------------------- *)

(* THE ONE CLOSURE LAW D4 NEEDS, and it is the strongest form: at a
   STRICTLY SHORTER input no round can be terminal at all, because D4's
   conclusion asks for the input to END at that round.  One more byte was
   typed, so either it opened a partial line ([rest_of <> []]) or it
   closed one ([nlines] grew) -- and either way the round D4 fired at is
   not the input's last.  This is what every consumer spends: it is how
   the claim refutes the next input at the terminal round, and how the
   truncations below keep the discipline prefix-closed. *)
Lemma d4_p_snoc_vacuous (cs : list nat) (I : list (bv 8)) (b : bv 8)
    (i : nat) :
  d4_p cs (I ++ [b]) -> (i < nlines I)%nat ->
  pmergeable (pcont (pline_of (bodies_of (I ++ [b]) !!! i))
               (palt_at cs i)) ->
  False.
Proof using.
  intros Hd4 Hi Hm.
  assert (Hle : (nlines I <= nlines (I ++ [b]))%nat)
    by (apply nlines_prefix; by eexists).
  destruct (d4_p_at cs (I ++ [b]) i Hd4 ltac:(lia) Hm) as [Hn Hr].
  destruct (decide (b = wl_nl)) as [-> | Hb].
  - rewrite nlines_snoc_nl in Hn. lia.
  - rewrite (rest_of_snoc_other I b Hb) in Hr.
    by apply app_nil in Hr as [_ Hb2].
Qed.

(* ...and the same reading at the TRUNCATED resolution the prefix
   carries.  This is the exact premise [PipeDisc.sessp_prefix_det] asks
   of the DISCIPLINE's side. *)
Lemma d4_p_nomerge_snoc (cs : list nat) (I : list (bv 8)) (b : bv 8) :
  alts_ok_p (I ++ [b]) cs -> d4_p cs (I ++ [b]) ->
  forall i, (i < nlines I)%nat ->
    ~ pmergeable (pcont (pline_of (bodies_of I !!! i))
                    (palt_at (take (nlines I) cs) i)).
Proof using.
  intros Hao Hd4 i Hi Hm.
  assert (Hle : (nlines I <= nlines (I ++ [b]))%nat)
    by (apply nlines_prefix; by eexists).
  assert (Hlen : length cs = nlines (I ++ [b]))
    by exact (alts_ok_p_length _ _ Hao).
  assert (Hpa : palt_at (take (nlines I) cs) i = palt_at cs i).
  { rewrite /palt_at. f_equal. symmetry.
    apply (pop_lta_prefix (take (nlines I) cs) cs i (prefix_take _ _)).
    rewrite length_take. lia. }
  assert (Hbod : bodies_of (I ++ [b]) !!! i = bodies_of I !!! i).
  { destruct (bodies_of_prefix I (I ++ [b]) ltac:(by eexists)) as [z Hz].
    rewrite Hz !list_lookup_total_alt lookup_app_l;
      [reflexivity | rewrite /nlines in Hi; lia]. }
  rewrite Hpa in Hm. rewrite -Hbod in Hm.
  exact (d4_p_snoc_vacuous cs I b i Hd4 Hi Hm).
Qed.

Lemma d4_p_take_snoc (cs : list nat) (I : list (bv 8)) (b : bv 8) :
  alts_ok_p (I ++ [b]) cs -> d4_p cs (I ++ [b]) ->
  d4_p (take (nlines I) cs) I.
Proof using.
  intros Hao Hd4. apply d4_p_intro. intros i Hi Hm.
  by destruct (d4_p_nomerge_snoc cs I b Hao Hd4 i Hi Hm).
Qed.

Lemma disc_seg_p'_in (seg : list mobs) (b : bv 8) :
  disc_seg_p' (seg ++ [ObsUartIn Uart0 b]) -> disc_seg_p' seg.
Proof using.
  intros [Hd (ps & cs & Hl & Hd4 & Hall)].
  rewrite /disc_seg_p ins_app ins_in in Hd.
  rewrite ins_app ins_in in Hl, Hd4.
  assert (Hpre : ins seg `prefix_of` (ins seg ++ [b])) by (by eexists).
  assert (Hle : (nlines (ins seg) <= nlines (ins seg ++ [b]))%nat)
    by (by apply nlines_prefix).
  split; [exact (disc_input_p_prefix _ _ Hpre Hd) |].
  exists ps, (take (nlines (ins seg)) cs).
  split; [exact (alts_ok_p_take _ _ cs Hpre Hl) |].
  split; [exact (d4_p_take_snoc cs (ins seg) b Hl Hd4) |].
  intros p Hp.
  assert (Hpin : p ∈ in_pres (seg ++ [ObsUartIn Uart0 b])).
  { rewrite in_pres_in. apply elem_of_app. by left. }
  destruct (Hall p Hpin) as [[HF Hlt] Hpt].
  assert (Hplt : (nlines (ins p) <= nlines (ins seg))%nat).
  { apply nlines_prefix, ins_prefix.
    exact (proj1 (Forall_forall _ _) (in_pres_prefix_all seg) p Hp). }
  split.
  - rewrite /pro_ok_p. split; [exact HF |].
    by rewrite (pro_idx_p_take cs _ (nlines (ins p)) Hplt).
  - rewrite /disc_pt_p (sessp_take ps cs (ins p) _ Hplt). exact Hpt.
Qed.

Lemma disc_p_in (h : list mobs) (b : bv 8) :
  trace_shape h true -> disc_p (h ++ [ObsUartIn Uart0 b]) -> disc_p h.
Proof using.
  intros Hsh.
  destruct (cycles_of_io h [ObsUartIn Uart0 b] Hsh) as (cs & Hc & Hc');
    [by constructor |].
  rewrite /disc_p Hc Hc' !Forall_app !Forall_singleton.
  intros [Hall Hseg]. split; [exact Hall | exact (disc_seg_p'_in _ _ Hseg)].
Qed.

Lemma disc_p_snoc (h : list mobs) (e : mobs) : disc_p (h ++ [e]) -> disc_p h.
Proof using.
  rewrite /disc_p /cycles_of !Forall_rev_iff cycles_rev_app /=.
  destruct e as [i b | i b | |]; cbn.
  - destruct (cycles_rev h) as [| c cs]; [by intros _ |].
    rewrite !Forall_cons. intros [Hseg Hall]. split; [| exact Hall].
    destruct i.
    + exact (disc_seg_p'_in c b Hseg).
    + apply (disc_seg_p'_other c (ObsUartIn Uart1 b) I). exact Hseg.
  - destruct (cycles_rev h) as [| c cs]; [by intros _ |].
    rewrite !Forall_cons. intros [Hseg Hall]. split; [| exact Hall].
    apply (disc_seg_p'_out c i b). exact Hseg.
  - rewrite Forall_cons. by intros [_ ?].
  - done.
Qed.

Lemma disc_p_prefix (h' h : list mobs) :
  h' `prefix_of` h -> disc_p h -> disc_p h'.
Proof using.
  intros [k ->]. induction k as [| e k IH] using rev_ind; intros Hd.
  - by rewrite app_nil_r in Hd.
  - apply IH. rewrite app_assoc in Hd. exact (disc_p_snoc _ _ Hd).
Qed.

(* the open cycle of a disciplined history keeps D3, and the whole
   per-cycle discipline -- [EchoOutPure.disc_seg_open_seg] and
   [disc_seg'_open_seg]'s twins *)
Lemma disc_seg_p'_open_seg (h : list mobs) :
  trace_shape h true -> disc_p h -> disc_seg_p' (open_seg h).
Proof using.
  intros Hsh Hd.
  destruct (trace_shape_cycles h Hsh) as (cs & Hcs).
  assert (Hin : open_seg h ∈ cycles_of h)
    by (rewrite /cycles_of Hcs; apply epu_elem_of_rev_head).
  apply elem_of_list_lookup in Hin as [i Hi].
  exact (Forall_lookup_1 _ _ _ _ Hd Hi).
Qed.

Lemma disc_seg_p_open_seg (h : list mobs) :
  trace_shape h true -> disc_p h -> disc_seg_p (open_seg h).
Proof using.
  intros Hsh Hd. exact (proj1 (disc_seg_p'_open_seg h Hsh Hd)).
Qed.

(* ====================================================================== *)
(*  2.  THE STAGE MACHINE: [pending_at_p] AND [D_p]                        *)
(* ====================================================================== *)

Definition pending_at_p (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  if decide (I = []) then pro_of ps
  else if decide (rest_of I = [])
       then alt_cont_p ps cs (bodies_of I) (nlines I - 1) else [].

Definition pending_p (ps cs : list nat) (E : list (list mobs * bv 8))
  : list (bv 8) := pending_at_p ps cs (snd <$> E).

(* THE TRANSCRIPT DUE AFTER E's LAST ECHO.  [EchoOutPure.D_from]'s twin --
   structural on [E] from the LEFT with the input read so far as the
   accumulator, for the same reason ([cbn] reduces it on every [x :: E']). *)
Fixpoint D_from_p (ps cs : list nat) (pre : list (bv 8))
    (E : list (list mobs * bv 8)) : list (bv 8) :=
  match E with
  | [] => []
  | x :: E' => pending_at_p ps cs pre ++ [echo_of x.2]
               ++ D_from_p ps cs (pre ++ [x.2]) E'
  end.

Definition D_p (ps cs : list nat) (E : list (list mobs * bv 8))
  : list (bv 8) := D_from_p ps cs [] E.

Lemma D_p_nil ps cs : D_p ps cs [] = [].
Proof using. reflexivity. Qed.

Lemma pending_at_p_nil ps cs : pending_at_p ps cs [] = pro_of ps.
Proof using.
  rewrite /pending_at_p. case_decide as H; [done | by destruct (H eq_refl)].
Qed.

Lemma pending_p_nil ps cs : pending_p ps cs [] = pro_of ps.
Proof using. rewrite /pending_p fmap_nil. exact (pending_at_p_nil ps cs). Qed.

(* the round pointer a block-opening stage stands at *)
Lemma pro_idx_p_nlines (cs : list nat) (I : list (bv 8)) :
  I <> [] -> rest_of I = [] ->
  palt_panic (palt_at cs (nlines I - 1)) = true ->
  S (pro_idx_p cs (nlines I - 1)) = pro_idx_p cs (nlines I).
Proof using.
  intros H0 Hm H3. pose proof (nlines_pos_of_rest_nil I H0 Hm) as Hq.
  replace (nlines I) with (S (nlines I - 1))%nat at 2 by lia.
  symmetry. by apply pro_idx_p_Sp.
Qed.

Lemma pending_at_p_ps_ext ps ps' cs I :
  ps `prefix_of` ps' ->
  (pro_idx_p cs (nlines I) < pro_rounds ps)%nat ->
  pending_at_p ps cs I = pending_at_p ps' cs I.
Proof using.
  intros Hp Hr. rewrite /pending_at_p. case_decide as H0.
  { subst I. apply (pro_of_from_done_ext 0%nat); [exact Hp |].
    rewrite nlines_nil in Hr. cbn [pro_idx_p] in Hr. exact Hr. }
  case_decide as Hm; [| done].
  rewrite /alt_cont_p. f_equal.
  destruct (palt_panic (palt_at cs (nlines I - 1))) eqn:H3; [| done].
  rewrite (pro_idx_p_nlines cs I H0 Hm H3).
  by apply pro_of_from_done_ext.
Qed.

Lemma pending_at_p_ps_mono ps ps' cs I :
  ps `prefix_of` ps' ->
  pending_at_p ps cs I `prefix_of` pending_at_p ps' cs I.
Proof using.
  intros Hp. rewrite /pending_at_p. case_decide as H0.
  { by apply pro_of_mono. }
  case_decide as Hm; [| reflexivity].
  rewrite /alt_cont_p. apply prefix_app.
  destruct (palt_panic (palt_at cs (nlines I - 1))); [| reflexivity].
  by apply pro_of_from_mono.
Qed.

Lemma pending_p_ps_mono ps ps' cs E :
  ps `prefix_of` ps' -> pending_p ps cs E `prefix_of` pending_p ps' cs E.
Proof using. intro Hp. by apply pending_at_p_ps_mono. Qed.

(* THE ROUND-OPENING BLOCK'S SHAPE, [EchoOutPure.pending_at_round_pre]'s
   twin: the panic line (a CONSTANT) and then that round's prologue. *)
Lemma pending_at_p_round_pre (ps cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ palt_panic (palt_at cs (nlines I - 1)) = true) ->
  pending_at_p ps cs I
  = (if decide (I = []) then [] else alt_panic)
    ++ pro_of (pro_from (pro_idx_p cs (nlines I)) ps).
Proof using.
  intros Hm Hopen. rewrite /pending_at_p. case_decide as H0.
  - subst I. rewrite nlines_nil. by cbn [pro_idx_p pro_from app].
  - rewrite decide_True; [| exact Hm].
    assert (H3 : palt_panic (palt_at cs (nlines I - 1)) = true)
      by (destruct Hopen as [Hn | H3]; [by destruct (H0 Hn) | exact H3]).
    rewrite /alt_cont_p H3 (pro_idx_p_nlines cs I H0 Hm H3).
    by rewrite (pcont_panic _ _ H3).
Qed.

Lemma pro_pin_p_round_le (ps cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ palt_panic (palt_at cs (nlines I - 1)) = true) ->
  pro_pin_p ps cs I ->
  (pro_idx_p cs (nlines I) <= pro_rounds ps)%nat.
Proof using.
  intros Hm Ho Hpin. destruct (decide (I = [])) as [-> | Hn0].
  { rewrite nlines_nil. cbn [pro_idx_p]. lia. }
  assert (H3 : palt_panic (palt_at cs (nlines I - 1)) = true)
    by (destruct Ho as [Hz | H3]; [by destruct (Hn0 Hz) | exact H3]).
  pose proof (nlines_pos_of_rest_nil I Hn0 Hm) as Hq.
  pose proof (pro_idx_p_nlines cs I Hn0 Hm H3) as Hs.
  assert (Hlt : (nlines I - 1 < nstarted I)%nat)
    by (pose proof (nlines_le_nstarted I); lia).
  pose proof (Hpin (nlines I - 1)%nat Hlt). lia.
Qed.

Lemma pending_at_p_round_det (ps ps' cs : list nat) (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ palt_panic (palt_at cs (nlines I - 1)) = true) ->
  pending_at_p ps cs I = pending_at_p ps' cs I ->
  pro_of (pro_from (pro_idx_p cs (nlines I)) ps)
  = pro_of (pro_from (pro_idx_p cs (nlines I)) ps').
Proof using.
  intros Hm Hopen Heq.
  rewrite (pending_at_p_round_pre ps cs I Hm Hopen) in Heq.
  rewrite (pending_at_p_round_pre ps' cs I Hm Hopen) in Heq.
  by apply app_inv_head in Heq.
Qed.

(* ---- the append laws ---- *)

Lemma D_from_p_pending_ext ps ps' cs pre E :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ (snd <$> E) ->
     J <> pre ++ (snd <$> E) ->
     pending_at_p ps cs J = pending_at_p ps' cs J) ->
  D_from_p ps cs pre E = D_from_p ps' cs pre E.
Proof using.
  revert pre. induction E as [| x E IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [x.2]) ++ (snd <$> E) = pre ++ (snd <$> (x :: E)))
    by (by rewrite fmap_cons epu_app_snoc).
  assert (Hhere : pending_at_p ps cs pre = pending_at_p ps' cs pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - rewrite fmap_cons. apply (epu_app_cons_ne pre x.2 (snd <$> E)). }
  cbn [D_from_p]. rewrite Hhere. do 2 f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma D_p_ps_ext ps ps' cs E :
  ps `prefix_of` ps' -> pro_pin_p ps cs (snd <$> E) ->
  D_p ps cs E = D_p ps' cs E.
Proof using.
  intros Hp Hpin. rewrite /D_p. apply D_from_p_pending_ext.
  intros J H1 H2 H3. rewrite app_nil_l in H2, H3.
  apply (pending_at_p_ps_ext ps ps' cs J Hp).
  apply Hpin. exact (nstarted_strict J (snd <$> E) H2 H3).
Qed.

Lemma D_from_p_app ps cs pre E1 E2 :
  D_from_p ps cs pre (E1 ++ E2)
  = D_from_p ps cs pre E1 ++ D_from_p ps cs (pre ++ (snd <$> E1)) E2.
Proof using.
  revert pre. induction E1 as [| x E1 IH]; intros pre.
  - cbn [D_from_p app]. by rewrite fmap_nil app_nil_r.
  - change ((x :: E1) ++ E2) with (x :: (E1 ++ E2)).
    cbn [D_from_p]. rewrite (IH (pre ++ [x.2])) fmap_cons epu_app_snoc.
    by rewrite -!app_assoc.
Qed.

Lemma D_p_app ps cs E x :
  D_p ps cs (E ++ [x]) = D_p ps cs E ++ pending_p ps cs E ++ [echo_of x.2].
Proof using.
  rewrite /D_p /pending_p D_from_p_app app_nil_l /=. by rewrite ?app_nil_r.
Qed.

(* ====================================================================== *)
(*  3.  WHAT THE CLAIM SAYS ABOUT [E]                                      *)
(* ====================================================================== *)

(* E's INDEX LAW is [EchoOutPure.E_index] verbatim (it names no
   discipline); its CONTENT LAW is D3 for the pipeline application. *)
Definition E_disc_p (E : list (list mobs * bv 8)) : Prop :=
  disc_input_p (snd <$> E).

Lemma E_disc_p_take (E : list (list mobs * bv 8)) (n : nat) :
  E_disc_p E -> E_disc_p (take n E).
Proof using.
  rewrite /E_disc_p. intro HE.
  exact (disc_input_p_prefix _ _ (epu_fmap_prefix snd _ _ (prefix_take _ _)) HE).
Qed.

Lemma E_disc_p_app_l (E : list (list mobs * bv 8)) (x : list mobs * bv 8) :
  E_disc_p (E ++ [x]) -> E_disc_p E.
Proof using.
  rewrite /E_disc_p fmap_app. intro H.
  exact (disc_input_p_prefix _ _ ltac:(by eexists) H).
Qed.

Lemma E_disc_p_echo (E : list (list mobs * bv 8)) (j : nat)
    (x : list mobs * bv 8) :
  E_disc_p E -> E !! j = Some x -> echo_of x.2 = x.2.
Proof using.
  intros HE Hx. apply (echo_of_disc_p (snd <$> E) x.2 HE).
  apply elem_of_list_lookup_2 with j. by rewrite list_lookup_fmap Hx.
Qed.

Lemma E_disc_p_of_hist (E : list (list mobs * bv 8)) (Sg : list mobs) :
  E_index E ->
  (forall j x, E !! j = Some x -> x.1 `prefix_of` Sg) ->
  disc_input_p (ins Sg) -> E_disc_p E.
Proof using.
  intros Hidx Hpre Hd.
  pose proof (E_length_le_hist E Sg Hidx Hpre) as Hlen.
  rewrite /E_disc_p (E_bytes_of_hist E Sg Hidx Hpre Hlen).
  exact (disc_input_p_prefix _ _ (prefix_take _ _) Hd).
Qed.

(* ====================================================================== *)
(*  4.  F1 -- THE STAGE IS BELOW THE SESSION                               *)
(* ====================================================================== *)

Lemma D_p_pending_sessp (ps cs : list nat)
    (E : list (list mobs * bv 8)) :
  E_disc_p E ->
  D_p ps cs E ++ pending_p ps cs E = sessp ps cs (snd <$> E).
Proof using.
  induction E as [| x E IH] using rev_ind; intros HE.
  - by rewrite D_p_nil pending_p_nil app_nil_l fmap_nil sessp_nil.
  - pose proof (E_disc_p_app_l E x HE) as HE0.
    pose proof (IH HE0) as IH'. rewrite /pending_p in IH'.
    assert (Hb : echo_of x.2 = x.2).
    { apply (E_disc_p_echo (E ++ [x]) (length E) x HE).
      rewrite lookup_app_r; [by rewrite Nat.sub_diag | lia]. }
    assert (Hfm : (snd <$> (E ++ [x])) = (snd <$> E) ++ [x.2])
      by (by rewrite fmap_app).
    rewrite D_p_app /pending_p Hfm Hb.
    rewrite (app_assoc (D_p ps cs E) (pending_at_p ps cs (snd <$> E)) [x.2])
            IH'.
    destruct (decide (x.2 = wl_nl)) as [Hnl | Hnl].
    + assert (Hp : pending_at_p ps cs ((snd <$> E) ++ [x.2])
                   = alt_cont_p ps cs
                       (bodies_of (snd <$> E) ++ [rest_of (snd <$> E)])
                       (nlines (snd <$> E))).
      { rewrite Hnl /pending_at_p. case_decide as H1.
        { exfalso. apply (f_equal length) in H1.
          rewrite (length_app (snd <$> E) [wl_nl]) in H1.
          cbn [length] in H1. lia. }
        rewrite decide_True; [| exact (rest_of_snoc_nl (snd <$> E))].
        rewrite bodies_of_snoc_nl nlines_snoc_nl.
        by replace (S (nlines (snd <$> E)) - 1)%nat
          with (nlines (snd <$> E)) by lia. }
      rewrite Hp Hnl sessp_snoc_nl.
      by rewrite -(app_assoc (sessp ps cs (snd <$> E)) [wl_nl] _).
    + assert (Hp : pending_at_p ps cs ((snd <$> E) ++ [x.2]) = []).
      { rewrite /pending_at_p. case_decide as H1.
        { exfalso. apply (f_equal length) in H1.
          rewrite (length_app (snd <$> E) [x.2]) in H1.
          cbn [length] in H1. lia. }
        rewrite decide_False; [done |].
        rewrite (rest_of_snoc_other (snd <$> E) x.2 Hnl).
        intro Hq. apply (f_equal length) in Hq.
        rewrite (length_app (rest_of (snd <$> E)) [x.2]) in Hq.
        cbn [length] in Hq. lia. }
      rewrite Hp app_nil_r (sessp_snoc_other ps cs (snd <$> E) x.2 Hnl).
      reflexivity.
Qed.

Lemma D_p_stage_prefix (ps cs : list nat)
    (E : list (list mobs * bv 8)) (w : list (bv 8)) :
  E_disc_p E -> w `prefix_of` pending_p ps cs E ->
  (D_p ps cs E ++ w) `prefix_of` sessp ps cs (snd <$> E).
Proof using.
  intros HE Hw. rewrite -(D_p_pending_sessp ps cs E HE).
  by apply prefix_app, Hw.
Qed.

(* ====================================================================== *)
(*  5.  F2 -- THE NEXT ECHO IS THE NEXT INPUT                              *)
(* ====================================================================== *)

Lemma sessp_length_lt (ps cs : list nat) (I I' : list (bv 8)) :
  I `prefix_of` I' -> I <> I' ->
  (length (sessp ps cs I) < length (sessp ps cs I'))%nat.
Proof using.
  intros [k Hk] Hne. destruct k as [| b k].
  { exfalso. apply Hne. by rewrite Hk app_nil_r. }
  assert (Hp : (I ++ [b]) `prefix_of` I')
    by (exists k; by rewrite Hk -app_assoc).
  pose proof (sessp_length_le ps cs _ _ Hp) as Hle.
  pose proof (sessp_length_step ps cs I b). lia.
Qed.

(* F2 at the pipeline session, under the per-byte rule D2 this application
   keeps ([EchoOutPure.next_input_of_complete] is the echo application's,
   where the count of echoed inputs is a kernel premise instead). *)
Lemma D2_next_input_p (ps cs : list nat)
    (E : list (list mobs * bv 8)) (w W : list (bv 8)) (h : list mobs)
    (c : bv 8) (m : nat) :
  E_disc_p E -> E_index E ->
  (forall x, x ∈ E -> hist_ext x.1 h) ->
  obs_ends_in Uart0 h c ->
  length (ins h) = m ->
  w `prefix_of` pending_p ps cs E ->
  sessp ps cs (take (m - 1)%nat (ins h)) `prefix_of` W ->
  W `prefix_of` (D_p ps cs E ++ w) ->
  m = S (length E) /\ w = pending_p ps cs E.
Proof using.
  intros HEb HEi Hnew Hends Hm Hw Hlow Hup.
  assert (Hm1 : (1 <= m)%nat).
  { destruct Hends as [h0 Hh0]. rewrite -Hm Hh0 ins_app ins_in.
    rewrite (length_app (ins h0) [c]). cbn [length]. lia. }
  assert (Hprefix : forall j x, E !! j = Some x -> x.1 `prefix_of` h).
  { intros j x Hx. apply (Hnew x). by eapply elem_of_list_lookup_2. }
  pose proof (E_length_le_hist E h HEi Hprefix) as HlenE.
  pose proof (E_bytes_of_hist E h HEi Hprefix HlenE) as HEq.
  assert (Hboth : sessp ps cs (take (m - 1)%nat (ins h))
                  `prefix_of` sessp ps cs (take (length E) (ins h))).
  { rewrite -HEq. etrans; [exact Hlow |]. etrans; [exact Hup |].
    by apply D_p_stage_prefix. }
  assert (Hle : (m - 1 <= length E)%nat).
  { destruct (decide (m - 1 <= length E)%nat) as [? | Hgt]; [done | exfalso].
    apply prefix_length in Hboth.
    assert (Hpr : take (length E) (ins h) `prefix_of` take (m - 1)%nat (ins h))
      by (apply prefix_take_le; lia).
    assert (Hne : take (length E) (ins h) <> take (m - 1)%nat (ins h)).
    { intro Hq. apply (f_equal length) in Hq.
      rewrite !length_take in Hq. lia. }
    pose proof (sessp_length_lt ps cs (take (length E) (ins h))
                  (take (m - 1)%nat (ins h)) Hpr Hne). lia. }
  assert (Heq : (m - 1)%nat = length E).
  { destruct (decide ((m - 1)%nat = length E)) as [? | Hne]; [done | exfalso].
    assert (Hlt : (m - 1 < length E)%nat) by lia.
    destruct (lookup_lt_is_Some_2 E (m - 1)%nat Hlt) as [x Hx].
    destruct (HEi (m - 1)%nat x Hx) as [Hxe Hxlen].
    assert (Hxin : x ∈ E) by (by eapply elem_of_list_lookup_2).
    destruct (Hnew x Hxin) as [Hpre Hlen'].
    assert (Hsame : x.1 = h).
    { eapply ins_hist_agree; [exact Hpre | exact Hxe | exact Hends |]. lia. }
    rewrite Hsame in Hlen'. lia. }
  split; [lia |].
  apply (anti_symm prefix); [exact Hw |].
  eapply (prefix_app_cancel (D_p ps cs E)).
  rewrite (D_p_pending_sessp ps cs E HEb) HEq -Heq.
  etrans; [exact Hlow | exact Hup].
Qed.

(* ====================================================================== *)
(*  6.  THE CHOICE LIST: A POINTWISE RANGE CONDITION, AND ITS PADDING      *)
(* ====================================================================== *)

Definition alts_pre_p (I : list (bv 8)) (cs : list nat) : Prop :=
  forall (i : nat) (c : nat),
    cs !! i = Some c ->
    (i < nlines I)%nat
    /\ palt_ok (pline_of (bodies_of I !!! i)) (palt_of c).

Lemma alts_pre_p_nil I : alts_pre_p I [].
Proof using. intros i c Hc. by rewrite lookup_nil in Hc. Qed.

Lemma alts_pre_p_le I cs : alts_pre_p I cs -> (length cs <= nlines I)%nat.
Proof using.
  intros H. destruct (decide (length cs = 0)%nat) as [Hz | Hz]; [lia |].
  destruct (lookup_lt_is_Some_2 cs (length cs - 1)%nat ltac:(lia)) as [c Hc].
  destruct (H _ c Hc) as [Hlt _]. lia.
Qed.

Lemma alts_pre_p_at I cs i :
  alts_pre_p I cs -> (i < length cs)%nat ->
  palt_ok (pline_of (bodies_of I !!! i)) (palt_at cs i).
Proof using.
  intros H Hi. destruct (lookup_lt_is_Some_2 cs i Hi) as [c Hc].
  rewrite /palt_at (list_lookup_total_correct cs i c Hc).
  exact (proj2 (H i c Hc)).
Qed.

Lemma alts_pre_p_of_alts_ok I cs : alts_ok_p I cs -> alts_pre_p I cs.
Proof using.
  intros Ha i c Hc.
  destruct (Forall2_lookup_r _ _ _ _ _ Ha Hc) as (l & Hl & Hok).
  rewrite /plines_of list_lookup_fmap in Hl.
  destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
  cbn in Hl. injection Hl as <-.
  rewrite (list_lookup_total_correct _ _ _ Hb).
  split; [| exact Hok]. rewrite /nlines. by eapply lookup_lt_Some.
Qed.

Lemma alts_pre_p_mono I I' cs :
  I `prefix_of` I' -> alts_pre_p I cs -> alts_pre_p I' cs.
Proof using.
  intros Hp H i c Hc. destruct (H i c Hc) as [Hi Hok].
  destruct (bodies_of_prefix I I' Hp) as [z Hz].
  split; [rewrite /nlines Hz length_app; rewrite /nlines in Hi; lia |].
  rewrite Hz list_lookup_total_alt lookup_app_l;
    [| rewrite /nlines in Hi; lia].
  by rewrite -list_lookup_total_alt.
Qed.

Lemma alts_pre_p_snoc I cs a :
  alts_pre_p I cs -> (length cs < nlines I)%nat ->
  palt_ok (pline_of (bodies_of I !!! length cs)) (palt_of a) ->
  alts_pre_p I (cs ++ [a]).
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

(* THE DEFAULT ALTERNATIVE: every line shape admits one, which is what
   makes a partial resolution paddable.  An [LEcho] line takes [PEcho 0]
   (its own good alternative); an [LPipe] line takes [PRan] -- the code is
   [4], one past the echo application's four. *)
Definition palt_def (l : pline) : nat :=
  match l with LEcho _ => 0%nat | LPipe _ => palt_code PRan end.

Lemma palt_def_ok (l : pline) : palt_ok l (palt_of (palt_def l)).
Proof using.
  destruct l as [ws | ws]; cbn [palt_def].
  - rewrite (palt_of_lt4 0%nat ltac:(lia)). rewrite /palt_ok. lia.
  - rewrite palt_of_code. exact I.
Qed.

Lemma palt_panic_def (l : pline) : palt_panic (palt_of (palt_def l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [palt_def].
  - rewrite (palt_of_lt4 0%nat ltac:(lia)). by vm_compute.
  - rewrite palt_of_code. reflexivity.
Qed.

Definition alts_pad_p (I : list (bv 8)) (cs : list nat) : list nat :=
  cs ++ (palt_def <$> drop (length cs) (plines_of I)).

(* A RESOLUTION THAT IS ALREADY FULL IS ITS OWN PADDING. *)
Lemma alts_pad_p_full (I : list (bv 8)) (cs : list nat) :
  length cs = nlines I -> alts_pad_p I cs = cs.
Proof using.
  intro H. rewrite /alts_pad_p drop_ge; [by rewrite fmap_nil app_nil_r |].
  rewrite plines_of_length. lia.
Qed.

(* ...AND THE DEFAULT IS NEVER THE TERMINAL ROUND, which is what lets the
   claim's padded resolution carry D4's unprimed reading for free. *)
Lemma palt_isforkS_def (l : pline) :
  palt_isforkS (palt_of (palt_def l)) = false.
Proof using.
  destruct l as [ws | ws]; cbn [palt_def].
  - rewrite (palt_of_lt4 0%nat ltac:(lia)). reflexivity.
  - rewrite palt_of_code. reflexivity.
Qed.

Lemma alts_pad_p_prefix I cs : cs `prefix_of` alts_pad_p I cs.
Proof using. rewrite /alts_pad_p. by eexists. Qed.

Lemma alts_pad_p_take I cs : take (length cs) (alts_pad_p I cs) = cs.
Proof using. rewrite /alts_pad_p. by rewrite take_app_length. Qed.

Lemma alts_pad_p_length I cs :
  (length cs <= nlines I)%nat -> length (alts_pad_p I cs) = nlines I.
Proof using.
  intro Hle. rewrite /alts_pad_p length_app length_fmap length_drop
    plines_of_length. lia.
Qed.

Lemma alts_pad_p_ok I cs :
  alts_pre_p I cs -> alts_ok_p I (alts_pad_p I cs).
Proof using.
  intros H. pose proof (alts_pre_p_le I cs H) as Hle.
  rewrite /alts_ok_p /alts_pad_p.
  rewrite -{1}(take_drop (length cs) (plines_of I)).
  apply Forall2_app.
  - apply Forall2_same_length_lookup_2.
    { rewrite length_take plines_of_length. lia. }
    intros i l c Hl Hc.
    apply lookup_take_Some in Hl as [Hl _].
    rewrite /plines_of list_lookup_fmap in Hl.
    destruct (bodies_of I !! i) as [b |] eqn:Hb; [| discriminate].
    cbn in Hl. injection Hl as <-.
    pose proof (proj2 (H i c Hc)) as Hok.
    by rewrite (list_lookup_total_correct _ _ _ Hb) in Hok.
  - apply Forall2_fmap_r. apply Forall_Forall2_diag.
    apply Forall_forall. intros l _. exact (palt_def_ok l).
Qed.

(* ---- out of range, and past the choice list's end ---- *)

Lemma palt_at_ge (cs : list nat) (i : nat) :
  (length cs <= i)%nat -> palt_at cs i = PEcho 0%nat.
Proof using.
  intro Hi.
  assert (Hz : cs !!! i = 0%nat).
  { rewrite list_lookup_total_alt (lookup_ge_None_2 cs i Hi). reflexivity. }
  rewrite /palt_at Hz. apply palt_of_lt4. lia.
Qed.

Lemma palt_panic_ge (cs : list nat) (i : nat) :
  (length cs <= i)%nat -> palt_panic (palt_at cs i) = false.
Proof using. intro Hi. rewrite (palt_at_ge cs i Hi). by vm_compute. Qed.

Lemma pro_idx_p_app_le (cs z : list nat) (q : nat) :
  (q <= length cs)%nat -> pro_idx_p (cs ++ z) q = pro_idx_p cs q.
Proof using.
  intro Hq. apply (pro_idx_p_ext (cs ++ z) cs q); [| lia].
  intros j Hj. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

(* past the choice list's end the round pointer stops moving: every entry
   there reads [PEcho 0], which does not panic *)
Lemma pro_idx_p_ge (cs : list nat) (q q' : nat) :
  (length cs <= q)%nat -> (q <= q')%nat -> pro_idx_p cs q' = pro_idx_p cs q.
Proof using.
  intros Hle Hq. induction q' as [| q' IH].
  - assert (Hz : q = 0%nat) by lia. by subst q.
  - destruct (decide (q = S q')) as [-> | Hne]; [reflexivity |].
    rewrite pro_idx_p_S (IH ltac:(lia)) (palt_panic_ge cs q' ltac:(lia)). lia.
Qed.

(* NO ALTERNATIVE PRINTS NOTHING.  Every constant one ends in the prompt,
   [PRan]'s content is closed by it, and a [PEcho k] is nonempty for
   [k < 4] -- which covers both an alternative a line ADMITS (at either
   shape, [PEcho 3] included) and the out-of-range reading. *)
Lemma pcont_nonnil (l : pline) (a : palt) :
  palt_ok l a \/ a = PEcho 0%nat -> pcont l a <> [].
Proof using.
  intro Ha.
  assert (Hpr : u_prompt <> []).
  { pose proof u_prompt_pos as Hup.
    destruct u_prompt as [| z zs]; [cbn [length] in Hup; lia | done]. }
  destruct a as [k | | | | sel | | sel |]; rewrite /pcont.
  - assert (Hk : (k < 4)%nat).
    { destruct Ha as [Ha | Heq]; [| injection Heq as <-; lia].
      destruct l as [ws | ws]; [exact Ha | rewrite /palt_ok in Ha; lia]. }
    exact (line_alts_of_nonnil (pline_ws l) k Hk).
  - by apply pop_app_nonnil_r.
  - rewrite /alt_execL. by apply pop_app_nonnil_r.
  - rewrite /alt_execR. by apply pop_app_nonnil_r.
  - by apply pop_app_nonnil_r.
  - rewrite /alt_pipe. by apply pop_app_nonnil_r.
  - (* THE TERMINAL ROUND'S BLOCK IS NONEMPTY because [palt_ok] refuses
       the empty selector: a fork-failure round that has printed nothing
       is not a round the claim has opened.  (Design section 4.3h's
       "[PForkS []] is the old [PFork]" would break this lemma, and with
       it every [pending_p] length argument below.) *)
    assert (Hok : palt_ok l (PForkS sel)).
    { destruct Ha as [Ha | Heq]; [exact Ha | discriminate Heq]. }
    destruct l as [ws | ws]; [by destruct Hok |].
    destruct Hok as (Hne & H1 & H2). intro Hq.
    apply (f_equal length) in Hq.
    rewrite (pmerge_length sel dg_execL alt_forkc H1 H2) in Hq.
    cbn [length] in Hq. by destruct sel.
  - exact Hpr.
Qed.

Lemma pending_at_p_nonnil (ps cs : list nat) (I : list (bv 8)) :
  alts_pre_p I cs -> I <> [] -> rest_of I = [] ->
  pending_at_p ps cs I <> [].
Proof using.
  intros Hao Hne Hr. rewrite /pending_at_p.
  rewrite decide_False; [| exact Hne]. rewrite decide_True; [| exact Hr].
  rewrite /alt_cont_p. intros Hc. apply app_eq_nil in Hc as [Hc _].
  revert Hc. apply pcont_nonnil.
  destruct (decide (nlines I - 1 < length cs)%nat) as [Hlt | Hge].
  - left. exact (alts_pre_p_at I cs _ Hao Hlt).
  - right. apply palt_at_ge. lia.
Qed.

(* ...AND THE FORM A WRITER ACTUALLY HOLDS.  A writer names a lower bound
   [I0] of the era's input and the range condition it carries is the
   CLAIM's, at the era's WHOLE input -- and [alts_pre_p] is monotone the
   other way, so the condition at [I0] does not follow.  What does follow is
   the only reading [pending_at_p] takes: the entry at the last completed
   line, whose BODY is the same body in the longer input. *)
Lemma alts_pre_p_at_prefix (I I' : list (bv 8)) (cs : list nat) (i : nat) :
  I `prefix_of` I' -> alts_pre_p I' cs ->
  (i < length cs)%nat -> (i < nlines I)%nat ->
  palt_ok (pline_of (bodies_of I !!! i)) (palt_at cs i).
Proof using.
  intros Hp H Hi Hn.
  pose proof (alts_pre_p_at I' cs i H Hi) as Hok.
  destruct (bodies_of_prefix I I' Hp) as [z Hz].
  rewrite Hz !list_lookup_total_alt lookup_app_l in Hok;
    [| rewrite /nlines in Hn; lia].
  by rewrite -!list_lookup_total_alt in Hok.
Qed.

Lemma pending_at_p_nonnil_pre (ps cs : list nat) (I I' : list (bv 8)) :
  I `prefix_of` I' -> alts_pre_p I' cs -> I <> [] -> rest_of I = [] ->
  pending_at_p ps cs I <> [].
Proof using.
  intros Hp Hao Hne Hr. rewrite /pending_at_p.
  rewrite decide_False; [| exact Hne]. rewrite decide_True; [| exact Hr].
  rewrite /alt_cont_p. intros Hc. apply app_eq_nil in Hc as [Hc _].
  pose proof (nlines_pos_of_rest_nil I Hne Hr) as Hpos.
  revert Hc. apply pcont_nonnil.
  destruct (decide (nlines I - 1 < length cs)%nat) as [Hlt | Hge].
  - left. exact (alts_pre_p_at_prefix I I' cs _ Hp Hao Hlt ltac:(lia)).
  - right. apply palt_at_ge. lia.
Qed.

Lemma pending_p_nonnil (ps cs : list nat) (E : list (list mobs * bv 8)) :
  alts_pre_p (snd <$> E) cs -> (snd <$> E) <> [] ->
  rest_of (snd <$> E) = [] -> pending_p ps cs E <> [].
Proof using. rewrite /pending_p. apply pending_at_p_nonnil. Qed.

Lemma pending_p_nil_inv (ps cs : list nat) (E : list (list mobs * bv 8)) :
  alts_pre_p (snd <$> E) cs -> rest_of (snd <$> E) = [] ->
  pending_p ps cs E = [] -> (snd <$> E) = [].
Proof using.
  intros Hao Hr Hnil.
  destruct (decide ((snd <$> E) = [])) as [? | Hne]; [done | exfalso].
  exact (pending_p_nonnil ps cs E Hao Hne Hr Hnil).
Qed.

(* ====================================================================== *)
(*  6b.  THE ERA'S PROCESS-BYTE CURSOR, AT THE PIPELINE SESSION            *)
(* ====================================================================== *)

Fixpoint proc_before_from_p (ps cs : list nat) (pre I : list (bv 8))
  : list (bv 8) :=
  match I with
  | [] => []
  | b :: I' => pending_at_p ps cs pre ++ proc_before_from_p ps cs (pre ++ [b]) I'
  end.

Definition proc_before_p (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  proc_before_from_p ps cs [] I.

Definition proc_stream_p (ps cs : list nat) (I : list (bv 8)) : list (bv 8) :=
  proc_before_p ps cs I ++ pending_at_p ps cs I.

Lemma proc_before_p_nil ps cs : proc_before_p ps cs [] = [].
Proof using. reflexivity. Qed.

Lemma proc_before_from_p_app ps cs pre I1 I2 :
  proc_before_from_p ps cs pre (I1 ++ I2)
  = proc_before_from_p ps cs pre I1
    ++ proc_before_from_p ps cs (pre ++ I1) I2.
Proof using.
  revert pre. induction I1 as [| b I1 IH]; intros pre.
  - cbn [proc_before_from_p app]. by rewrite app_nil_r.
  - cbn [app proc_before_from_p]. rewrite IH app_assoc.
    by rewrite epu_app_snoc.
Qed.

Lemma proc_before_p_app ps cs I k :
  proc_before_p ps cs (I ++ k)
  = proc_before_p ps cs I ++ proc_before_from_p ps cs I k.
Proof using. rewrite /proc_before_p proc_before_from_p_app. by cbn [app]. Qed.

Lemma proc_before_p_snoc ps cs I b :
  proc_before_p ps cs (I ++ [b]) = proc_stream_p ps cs I.
Proof using.
  rewrite proc_before_p_app /proc_stream_p. cbn [proc_before_from_p].
  by rewrite app_nil_r.
Qed.

Lemma proc_before_p_prefix ps cs I I' :
  I `prefix_of` I' ->
  proc_before_p ps cs I `prefix_of` proc_before_p ps cs I'.
Proof using. intros [z ->]. rewrite proc_before_p_app. by eexists. Qed.

Lemma proc_stream_p_before ps cs I I' :
  I `prefix_of` I' -> I <> I' ->
  proc_stream_p ps cs I `prefix_of` proc_before_p ps cs I'.
Proof using.
  intros [z Hz] Hne. destruct z as [| b z].
  { exfalso. apply Hne. by rewrite Hz app_nil_r. }
  rewrite Hz proc_before_p_app /proc_stream_p. cbn [proc_before_from_p].
  rewrite app_assoc. by eexists.
Qed.

Lemma proc_stream_p_mono ps cs I I' :
  I `prefix_of` I' ->
  proc_stream_p ps cs I `prefix_of` proc_stream_p ps cs I'.
Proof using.
  intros Hp. destruct (decide (I = I')) as [-> | Hne]; [reflexivity |].
  etrans; [exact (proc_stream_p_before ps cs I I' Hp Hne) |].
  rewrite /proc_stream_p. by eexists.
Qed.

Definition pcount_p (ps cs : list nat) (E : list (list mobs * bv 8))
    (w : list (bv 8)) : nat :=
  (length (proc_before_p ps cs (snd <$> E)) + length w)%nat.

Lemma pcount_p_write ps cs E w b :
  pcount_p ps cs E (w ++ [b]) = S (pcount_p ps cs E w).
Proof using. rewrite /pcount_p length_app /=. lia. Qed.

Lemma pcount_p_echo ps cs E x w :
  w = pending_p ps cs E -> pcount_p ps cs (E ++ [x]) [] = pcount_p ps cs E w.
Proof using.
  intros ->. rewrite /pcount_p fmap_app /=.
  rewrite (proc_before_p_snoc ps cs (snd <$> E) x.2)
          /proc_stream_p /pending_p.
  rewrite length_app. cbn [length]. lia.
Qed.

Lemma proc_stream_p_pcount ps cs E w b :
  pending_p ps cs E !! length w = Some b ->
  proc_stream_p ps cs (snd <$> E) !! pcount_p ps cs E w = Some b.
Proof using.
  intros Hb. rewrite /proc_stream_p /pcount_p lookup_app_r; [| lia].
  replace (length (proc_before_p ps cs (snd <$> E)) + length w
           - length (proc_before_p ps cs (snd <$> E)))%nat
    with (length w) by lia.
  exact Hb.
Qed.

Lemma proc_stream_p_pcount_inv ps cs E w I b :
  (snd <$> E) `prefix_of` I ->
  (length w < length (pending_p ps cs E))%nat ->
  proc_stream_p ps cs I !! pcount_p ps cs E w = Some b ->
  pending_p ps cs E !! length w = Some b.
Proof using.
  intros HI Hlt Hl.
  destruct (lookup_lt_is_Some_2 (pending_p ps cs E) (length w) Hlt)
    as [b' Hb'].
  pose proof (proc_stream_p_pcount ps cs E w b' Hb') as Hfwd.
  assert (Heq : proc_stream_p ps cs I !! pcount_p ps cs E w = Some b')
    by (eapply prefix_lookup_Some;
        [exact Hfwd | by apply proc_stream_p_mono]).
  assert (Hbb : b = b') by congruence. by rewrite Hbb.
Qed.

(* ====================================================================== *)
(*  6d.  A WRITER'S LOWER BOUNDS DETERMINE THE STREAM                      *)
(* ====================================================================== *)

Lemma pending_at_p_cs_ext ps cs0 cs I :
  cs0 `prefix_of` cs -> (nlines I <= length cs0)%nat ->
  pending_at_p ps cs0 I = pending_at_p ps cs I.
Proof using.
  intros Hp Hn. rewrite /pending_at_p.
  case_decide as H0; [done |].
  case_decide as Hr; [| done].
  pose proof (nlines_pos_of_rest_nil I H0 Hr) as Hpos.
  assert (Hlk : forall j, (j < nlines I)%nat -> cs0 !!! j = cs !!! j).
  { intros j Hj. symmetry. apply (pop_lta_prefix cs0 cs j Hp). lia. }
  rewrite /alt_cont_p /palt_at (Hlk (nlines I - 1)%nat ltac:(lia)).
  by rewrite (pro_idx_p_ext cs0 cs (nlines I) Hlk (nlines I - 1)%nat
                ltac:(lia)).
Qed.

Lemma pending_at_p_cs_prefix ps0 ps cs0 cs I :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  (nlines I <= length cs0)%nat ->
  (pro_idx_p cs0 (nlines I) < pro_rounds ps0)%nat ->
  pending_at_p ps0 cs0 I = pending_at_p ps cs I.
Proof using.
  intros Hps Hcs Hn Hr.
  rewrite (pending_at_p_ps_ext ps0 ps cs0 I Hps Hr).
  by apply pending_at_p_cs_ext.
Qed.

Lemma pending_at_p_stage_ext ps0 ps cs0 cs I0 J :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin_p ps0 cs0 I0 ->
  (nlines (removelast I0) <= length cs0)%nat ->
  J `prefix_of` I0 -> J <> I0 ->
  pending_at_p ps0 cs0 J = pending_at_p ps cs J.
Proof using.
  intros Hps Hcs Hpin Hn HJ Hne.
  assert (Hjl : (nlines J <= length cs0)%nat).
  { etrans; [| exact Hn].
    apply nlines_prefix, (pop_prefix_of_removelast J I0 HJ Hne). }
  apply (pending_at_p_cs_prefix ps0 ps cs0 cs J Hps Hcs Hjl).
  apply Hpin. exact (nstarted_strict J I0 HJ Hne).
Qed.

Lemma proc_before_from_p_ext ps0 ps cs0 cs pre I :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ I -> J <> pre ++ I ->
     pending_at_p ps0 cs0 J = pending_at_p ps cs J) ->
  proc_before_from_p ps0 cs0 pre I = proc_before_from_p ps cs pre I.
Proof using.
  revert pre. induction I as [| b I IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [b]) ++ I = pre ++ b :: I) by apply epu_app_snoc.
  assert (Hhere : pending_at_p ps0 cs0 pre = pending_at_p ps cs pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - apply (epu_app_cons_ne pre b I). }
  cbn [proc_before_from_p]. rewrite Hhere. f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma proc_before_p_ext ps0 ps cs0 cs I :
  (forall J, J `prefix_of` I -> J <> I ->
     pending_at_p ps0 cs0 J = pending_at_p ps cs J) ->
  proc_before_p ps0 cs0 I = proc_before_p ps cs I.
Proof using.
  intros Hj. rewrite /proc_before_p. apply proc_before_from_p_ext.
  intros J _ H2 H3. rewrite app_nil_l in H2, H3. by apply Hj.
Qed.

(* ...and the PROLOGUE list's, which a prologue round's own choice byte
   spends: every block BELOW the round the stage stands in has settled
   ([pro_pin_p]), so extending the resolution moves none of them. *)
Lemma proc_before_p_ps_ext ps ps' cs I :
  ps `prefix_of` ps' -> pro_pin_p ps cs I ->
  proc_before_p ps cs I = proc_before_p ps' cs I.
Proof using.
  intros Hp Hpin. apply proc_before_p_ext. intros J HJ Hne.
  apply (pending_at_p_ps_ext ps ps' cs J Hp).
  apply Hpin. exact (nstarted_strict J I HJ Hne).
Qed.

Lemma proc_before_p_cs_prefix ps0 ps cs0 cs I0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin_p ps0 cs0 I0 ->
  (nlines (removelast I0) <= length cs0)%nat ->
  proc_before_p ps0 cs0 I0 = proc_before_p ps cs I0.
Proof using.
  intros Hps Hcs Hpin Hn. apply proc_before_p_ext.
  intros J HJ Hne.
  exact (pending_at_p_stage_ext ps0 ps cs0 cs I0 J Hps Hcs Hpin Hn HJ Hne).
Qed.

Lemma pcount_p_cs_prefix ps0 ps cs0 cs E w :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  pro_pin_p ps0 cs0 (snd <$> E) ->
  (nlines (removelast (snd <$> E)) <= length cs0)%nat ->
  pcount_p ps0 cs0 E w = pcount_p ps cs E w.
Proof using.
  intros Hps Hcs Hpin Hn. rewrite /pcount_p.
  by rewrite (proc_before_p_cs_prefix ps0 ps cs0 cs (snd <$> E)
                Hps Hcs Hpin Hn).
Qed.

Lemma proc_stream_p_prefix ps0 ps cs0 cs I0 :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs -> pro_pin_p ps0 cs0 I0 ->
  (nlines I0 <= length cs0)%nat ->
  proc_stream_p ps0 cs0 I0 `prefix_of` proc_stream_p ps cs I0.
Proof using.
  intros Hps Hcs Hpin Hn.
  assert (Hb : proc_before_p ps0 cs0 I0 = proc_before_p ps cs I0).
  { apply (proc_before_p_cs_prefix ps0 ps cs0 cs I0 Hps Hcs Hpin).
    etrans; [apply nlines_prefix, pop_removelast_prefix | exact Hn]. }
  rewrite /proc_stream_p Hb. apply prefix_app.
  rewrite (pending_at_p_cs_ext ps0 cs0 cs I0 Hcs Hn).
  by apply pending_at_p_ps_mono.
Qed.

Lemma D_from_p_ext ps0 ps cs0 cs pre E :
  (forall J, pre `prefix_of` J -> J `prefix_of` pre ++ (snd <$> E) ->
     J <> pre ++ (snd <$> E) ->
     pending_at_p ps0 cs0 J = pending_at_p ps cs J) ->
  D_from_p ps0 cs0 pre E = D_from_p ps cs pre E.
Proof using.
  revert pre. induction E as [| x E IH]; intros pre Hj; [done |].
  assert (Hshape : (pre ++ [x.2]) ++ (snd <$> E) = pre ++ (snd <$> (x :: E)))
    by (by rewrite fmap_cons epu_app_snoc).
  assert (Hhere : pending_at_p ps0 cs0 pre = pending_at_p ps cs pre).
  { apply Hj.
    - reflexivity.
    - by eexists.
    - rewrite fmap_cons. apply (epu_app_cons_ne pre x.2 (snd <$> E)). }
  cbn [D_from_p]. rewrite Hhere. do 2 f_equal.
  apply IH. intros J H1 H2 H3. apply Hj.
  - etrans; [| exact H1]. by eexists.
  - rewrite -Hshape. exact H2.
  - rewrite -Hshape. exact H3.
Qed.

Lemma D_p_cs_prefix ps0 ps cs0 cs E :
  ps0 `prefix_of` ps -> cs0 `prefix_of` cs ->
  pro_pin_p ps0 cs0 (snd <$> E) ->
  (nlines (removelast (snd <$> E)) <= length cs0)%nat ->
  D_p ps0 cs0 E = D_p ps cs E.
Proof using.
  intros Hps Hcs Hpin Hn. rewrite /D_p. apply D_from_p_ext.
  intros J _ H2 H3. rewrite app_nil_l in H2, H3.
  exact (pending_at_p_stage_ext ps0 ps cs0 cs (snd <$> E) J
           Hps Hcs Hpin Hn H2 H3).
Qed.

(* THE WRITE'S WHOLE PURE ARGUMENT, [EchoOut.write_stage_byte]'s twin: the
   writer names lower bounds of the era's choices, its INPUT and its
   cursor, and knows only that its byte is the [P]-th of the stream through
   [I0].  That alone pins the stage. *)
Lemma write_stage_byte_p (ps0 ps cs0 cs : list nat)
      (E : list (list mobs * bv 8)) (w I0 : list (bv 8)) (P : nat) (b : bv 8) :
  ps0 `prefix_of` ps ->
  pro_pin_p ps0 cs0 I0 ->
  cs0 `prefix_of` cs ->
  (nlines I0 <= length cs0)%nat ->
  I0 `prefix_of` (snd <$> E) ->
  P = pcount_p ps cs E w ->
  proc_stream_p ps0 cs0 I0 !! P = Some b ->
  (snd <$> E) = I0 /\ pending_p ps cs E !! length w = Some b.
Proof using.
  intros Hps Hpin Hcs Hn HI HP Hb.
  pose proof (prefix_lookup_Some _ _ _ _ Hb
                (proc_stream_p_prefix ps0 ps cs0 cs I0 Hps Hcs Hpin Hn))
    as Hb'.
  clear Hb. rename Hb' into Hb.
  assert (Hlt : (P < length (proc_stream_p ps cs I0))%nat)
    by (by apply lookup_lt_Some in Hb).
  assert (HlenE : (snd <$> E) = I0).
  { destruct (decide ((snd <$> E) = I0)) as [? | Hne]; [done | exfalso].
    pose proof (proc_stream_p_before ps cs I0 (snd <$> E) HI
                  ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
    apply prefix_length in Hpre. rewrite HP /pcount_p in Hlt. lia. }
  split; [exact HlenE |].
  rewrite -HlenE in Hb, Hlt.
  assert (Hstrict : (length w < length (pending_p ps cs E))%nat).
  { rewrite /proc_stream_p length_app in Hlt.
    rewrite HP /pcount_p in Hlt. rewrite /pending_p. lia. }
  eapply (proc_stream_p_pcount_inv ps cs E w (snd <$> E) b);
    [reflexivity | exact Hstrict | by rewrite -HP].
Qed.

(* ====================================================================== *)
(*  6e.  THE BANNER OF AN ARBITRARY PROLOGUE ROUND                         *)
(* ====================================================================== *)

Lemma proc_stream_p_round_banner (ps cs : list nat) (I : list (bv 8))
      (j i : nat) (pre : list (bv 8)) (b : bv 8) :
  pending_at_p ps cs I
  = pre ++ pro_of (pro_from (pro_idx_p cs (nlines I)) ps) ->
  pro_from (pro_idx_p cs (nlines I)) ps = pro_fail j ++ [3%nat] ->
  u_banner !! i = Some b ->
  proc_stream_p ps cs I
    !! (length (proc_before_p ps cs I) + length pre + pro_round * j + i)%nat
  = Some b.
Proof using.
  intros Hshape Hopen Hb.
  rewrite /proc_stream_p Hshape Hopen.
  replace (length (proc_before_p ps cs I) + length pre + pro_round * j + i)%nat
    with (length (proc_before_p ps cs I)
          + (length pre + (pro_round * j + i)))%nat by lia.
  rewrite (lookup_app_shift (proc_before_p ps cs I)) (lookup_app_shift pre).
  by apply pro_of_fail_banner.
Qed.

Lemma proc_stream_p_round_banner_open (ps cs : list nat) (I : list (bv 8))
      (j i : nat) (b : bv 8) :
  rest_of I = [] ->
  (I = [] \/ palt_panic (palt_at cs (nlines I - 1)) = true) ->
  pro_from (pro_idx_p cs (nlines I)) ps = pro_fail j ++ [3%nat] ->
  u_banner !! i = Some b ->
  proc_stream_p ps cs I
    !! (length (proc_before_p ps cs I)
        + length (if decide (I = []) then [] else alt_panic)
        + pro_round * j + i)%nat
  = Some b.
Proof using.
  intros Hr Ho Hopen Hb.
  apply (proc_stream_p_round_banner ps cs I j i _ b);
    [by apply pending_at_p_round_pre | exact Hopen | exact Hb].
Qed.

(* ====================================================================== *)
(*  7.  F4 -- PHI's PURE PART                                              *)
(* ====================================================================== *)

Lemma pro_ok_p_pad ps cs m d :
  Forall (fun x => (x < length pro_alts)%nat) ps -> (m <= d)%nat ->
  pro_ok_p (ps ++ replicate (S d) 0%nat) cs m.
Proof using.
  intros HF Hm. split.
  - apply Forall_app. split; [exact HF |].
    apply Forall_forall. intros x Hx. apply elem_of_replicate in Hx as [-> _].
    rewrite pro_alts_length. lia.
  - rewrite pro_rounds_app pro_rounds_replicate_0.
    pose proof (pro_idx_p_le cs m). lia.
Qed.

Lemma pro_pin_p_mono ps ps' cs I :
  ps `prefix_of` ps' -> pro_pin_p ps cs I -> pro_pin_p ps' cs I.
Proof using.
  intros [z ->] Hpin q Hq. pose proof (Hpin q Hq) as H.
  rewrite pro_rounds_app. lia.
Qed.

Lemma pro_pin_p_prefix ps cs I I' :
  I' `prefix_of` I -> pro_pin_p ps cs I -> pro_pin_p ps cs I'.
Proof using.
  intros Hp Hpin q Hq. apply Hpin.
  pose proof (nstarted_prefix I' I Hp). lia.
Qed.

(* THE CLAIM GIVES [good_out_p] AT THE SEGMENT.  Two premises replace
   [EchoOutPure.good_out_of_stage]'s [Forall (< 4) cs]: the range condition
   is pointwise ([alts_pre_p]) and the resolution is PADDED to a full one;
   the two length rows are [EchoOut.cs_len_ok]'s two readings. *)
Lemma good_out_p_of_stage (ps cs : list nat)
      (E : list (list mobs * bv 8)) (w : list (bv 8)) (seg : list mobs) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  alts_pre_p (ins seg) cs ->
  (nlines (removelast (snd <$> E)) <= length cs)%nat ->
  ((nlines (snd <$> E) <= length cs)%nat \/ w = []) ->
  E_disc_p E ->
  pro_pin_p ps cs (snd <$> E) ->
  w `prefix_of` pending_p ps cs E ->
  obs_wire Uart0 seg `prefix_of` (D_p ps cs E ++ w) ->
  (snd <$> E) `prefix_of` ins seg ->
  good_out_p seg.
Proof using.
  intros Hps Hao Hrl Hlast HE Hpin Hw Hwire Hinp.
  set (ps' := (ps ++ replicate (S (nlines (ins seg))) 0%nat)%list).
  set (cs' := alts_pad_p (ins seg) cs).
  assert (Hpp : ps `prefix_of` ps') by (rewrite /ps'; by eexists).
  assert (Hcc : cs `prefix_of` cs') by apply alts_pad_p_prefix.
  assert (Hpin' : pro_pin_p ps' cs (snd <$> E))
    by exact (pro_pin_p_mono ps ps' cs _ Hpp Hpin).
  exists ps', cs'. split.
  { apply pro_ok_p_pad; [exact Hps | lia]. }
  split; [exact (alts_pad_p_ok (ins seg) cs Hao) |].
  etrans; [exact Hwire |].
  rewrite (D_p_ps_ext ps ps' cs E Hpp Hpin).
  rewrite (D_p_cs_prefix ps' ps' cs cs' E ltac:(reflexivity) Hcc Hpin' Hrl).
  assert (Hw' : w `prefix_of` pending_p ps' cs' E).
  { destruct Hlast as [Hle | ->]; [| apply prefix_nil].
    etrans; [exact Hw |].
    etrans; [exact (pending_p_ps_mono ps ps' cs E Hpp) |].
    rewrite /pending_p (pending_at_p_cs_ext ps' cs cs' (snd <$> E) Hcc Hle).
    reflexivity. }
  etrans; [exact (D_p_stage_prefix ps' cs' E w HE Hw') |].
  by apply (sessp_mono ps' cs' (snd <$> E) (ins seg)).
Qed.

(* ---- THE PADDING MOVES NO PROLOGUE ROUND.  [pro_idx_p] reads the choice
       list only through [palt_panic], and neither the out-of-range reading
       ([PEcho 0]) nor any default alternative panics. ---- *)
Lemma pro_idx_p_ext_panic (cs1 cs2 : list nat) (q : nat) :
  (forall j, (j < q)%nat ->
     palt_panic (palt_at cs1 j) = palt_panic (palt_at cs2 j)) ->
  forall j, (j <= q)%nat -> pro_idx_p cs1 j = pro_idx_p cs2 j.
Proof using.
  intros Hj j. induction j as [| j IH]; intros Hjq; [done |].
  rewrite !pro_idx_p_S IH; [| lia]. by rewrite (Hj j ltac:(lia)).
Qed.

Lemma alts_pad_p_panic (I : list (bv 8)) (cs : list nat) (j : nat) :
  (j < nlines I)%nat ->
  palt_panic (palt_at (alts_pad_p I cs) j) = palt_panic (palt_at cs j).
Proof using.
  intros Hj. destruct (decide (j < length cs)%nat) as [Hlt | Hge].
  - by rewrite /palt_at (pop_lta_prefix cs (alts_pad_p I cs) j
                           (alts_pad_p_prefix I cs) Hlt).
  - rewrite (palt_panic_ge cs j ltac:(lia)).
    destruct (decide (j < length (alts_pad_p I cs))%nat) as [Hlt2 | Hge2];
      last first.
    { by rewrite (palt_panic_ge (alts_pad_p I cs) j ltac:(lia)). }
    assert (Hjl : (j < length (plines_of I))%nat)
      by (rewrite plines_of_length; lia).
    destruct (lookup_lt_is_Some_2 (plines_of I) j Hjl) as [l Hl].
    assert (Hlk : alts_pad_p I cs !!! j = palt_def l).
    { rewrite /alts_pad_p list_lookup_total_alt lookup_app_r; [| lia].
      rewrite list_lookup_fmap lookup_drop.
      replace (length cs + (j - length cs))%nat with j by lia.
      by rewrite Hl. }
    rewrite /palt_at Hlk. exact (palt_panic_def _).
Qed.

(* the same reading at [palt_isforkS]: a padded resolution is terminal
   nowhere the stage's own one is not *)
Lemma alts_pad_p_isforkS (I : list (bv 8)) (cs : list nat) (i : nat) :
  Forall (fun c => palt_isforkS (palt_of c) = false) cs ->
  palt_isforkS (palt_at (alts_pad_p I cs) i) = false.
Proof using.
  intro HF. destruct (decide (i < length cs)%nat) as [Hlt | Hge].
  - rewrite /palt_at (pop_lta_prefix cs (alts_pad_p I cs) i
                        (alts_pad_p_prefix I cs) Hlt).
    destruct (lookup_lt_is_Some_2 cs i Hlt) as [c Hc].
    rewrite (list_lookup_total_correct cs i c Hc).
    exact (Forall_lookup_1 _ _ _ _ HF Hc).
  - destruct (decide (i < length (alts_pad_p I cs))%nat) as [Hlt2 | Hge2];
      last first.
    { rewrite (palt_at_ge (alts_pad_p I cs) i ltac:(lia)). reflexivity. }
    rewrite /alts_pad_p length_app length_fmap length_drop
            plines_of_length in Hlt2.
    assert (Hjl : (i < length (plines_of I))%nat)
      by (rewrite plines_of_length; lia).
    destruct (lookup_lt_is_Some_2 (plines_of I) i Hjl) as [l Hl].
    assert (Hlk : alts_pad_p I cs !!! i = palt_def l).
    { rewrite /alts_pad_p list_lookup_total_alt lookup_app_r; [| lia].
      rewrite list_lookup_fmap lookup_drop.
      replace (length cs + (i - length cs))%nat with i by lia.
      by rewrite Hl. }
    rewrite /palt_at Hlk. exact (palt_isforkS_def l).
Qed.

Lemma alts_pad_p_pro_idx (I : list (bv 8)) (cs : list nat) (q : nat) :
  (q <= nlines I)%nat -> pro_idx_p (alts_pad_p I cs) q = pro_idx_p cs q.
Proof using.
  intro Hq. apply (pro_idx_p_ext_panic (alts_pad_p I cs) cs (nlines I));
    [| exact Hq].
  intros j Hj. exact (alts_pad_p_panic I cs j Hj).
Qed.

(* THE STAGE'S TRANSCRIPT AT A FULL RESOLUTION: the padded list agrees with
   the stage's wherever the stage reads it, and the stage's transcript is
   below the padded session. *)
Lemma stage_sessp_pad (ps cs : list nat)
    (E : list (list mobs * bv 8)) (w : list (bv 8)) :
  alts_pre_p (snd <$> E) cs ->
  (nlines (removelast (snd <$> E)) <= length cs)%nat ->
  ((nlines (snd <$> E) <= length cs)%nat \/ w = []) ->
  E_disc_p E ->
  pro_pin_p ps cs (snd <$> E) ->
  w `prefix_of` pending_p ps cs E ->
  alts_ok_p (snd <$> E) (alts_pad_p (snd <$> E) cs)
  /\ pro_pin_p ps (alts_pad_p (snd <$> E) cs) (snd <$> E)
  /\ D_p ps cs E = D_p ps (alts_pad_p (snd <$> E) cs) E
  /\ w `prefix_of` pending_p ps (alts_pad_p (snd <$> E) cs) E
  /\ (D_p ps cs E ++ w)
       `prefix_of` sessp ps (alts_pad_p (snd <$> E) cs) (snd <$> E).
Proof using.
  intros Hao Hrl Hlast HE Hpin Hw.
  set (cs' := alts_pad_p (snd <$> E) cs).
  assert (Hcc : cs `prefix_of` cs') by apply alts_pad_p_prefix.
  assert (Hok : alts_ok_p (snd <$> E) cs') by exact (alts_pad_p_ok _ cs Hao).
  assert (Hpin' : pro_pin_p ps cs' (snd <$> E)).
  { intros q Hq.
    assert (Hqle : (q <= nlines (snd <$> E))%nat).
    { pose proof (nstarted_le_S (snd <$> E)). lia. }
    rewrite /cs' (alts_pad_p_pro_idx (snd <$> E) cs q Hqle). by apply Hpin. }
  assert (HD : D_p ps cs E = D_p ps cs' E)
    by (apply (D_p_cs_prefix ps ps cs cs' E ltac:(reflexivity) Hcc Hpin Hrl)).
  assert (Hw' : w `prefix_of` pending_p ps cs' E).
  { destruct Hlast as [Hle | ->]; [| apply prefix_nil].
    rewrite /pending_p
      -(pending_at_p_cs_ext ps cs cs' (snd <$> E) Hcc Hle). exact Hw. }
  split_and!; [exact Hok | exact Hpin' | exact HD | exact Hw' |].
  rewrite HD. exact (D_p_stage_prefix ps cs' E w HE Hw').
Qed.

(* AN EVENT THAT PUTS NOTHING ON THE CONSOLE'S WIRE cannot falsify a cycle
   that was good.  As at the file application it needs one move more than
   the echo one: the extended input may have one more COMPLETE LINE and
   [PipeDisc.alts_ok_p] demands an entry per line, so the resolution is
   padded.  The padding moves no prologue round ([alts_pad_p_pro_idx]) and
   changes no block the shorter input had ([alts_pad_p_take] through
   [PipeDisc.sessp_take]). *)
Lemma good_out_p_step (seg : list mobs) (e : mobs) :
  obs_wire Uart0 [e] = [] -> good_out_p seg -> good_out_p (seg ++ [e]).
Proof using.
  intros He (ps & cs & [Hpsb Hlt] & Hao & Hwire).
  set (I := ins seg). set (I' := ins (seg ++ [e])).
  assert (HII : I `prefix_of` I') by (rewrite /I /I' ins_app; by eexists).
  assert (Hlen : length cs = nlines I) by exact (alts_ok_p_length _ _ Hao).
  assert (Hnl : (nlines I <= nlines I')%nat) by (by apply nlines_prefix).
  set (cs' := alts_pad_p I' cs).
  exists ps, cs'. split.
  { split; [exact Hpsb |].
    rewrite /cs' (alts_pad_p_pro_idx I' cs (nlines I') ltac:(lia)).
    rewrite (pro_idx_p_ge cs (nlines I) (nlines I') ltac:(lia) Hnl).
    exact Hlt. }
  split.
  { rewrite /cs'. apply alts_pad_p_ok.
    apply (alts_pre_p_mono I I');
      [exact HII | exact (alts_pre_p_of_alts_ok _ _ Hao)]. }
  rewrite /I' obs_wire_app He app_nil_r.
  etrans; [exact Hwire |].
  assert (Hcut : sessp ps cs I = sessp ps cs' I).
  { rewrite -{1}(alts_pad_p_take I' cs) -/cs'. apply sessp_take. lia. }
  rewrite Hcut. by apply sessp_mono.
Qed.

(* ====================================================================== *)
(*  8.  DETERMINACY                                                        *)
(*                                                                        *)
(*  [FileOutPure.sessf_prefix_det2] exists because a file's transcript     *)
(*  reads the era's BOOT STATE and the two witnesses' states have no       *)
(*  reason to be equal.  A PIPELINE round reads no state, so               *)
(*  [PipeDisc.sessp_prefix_det] already compares two independent           *)
(*  resolutions and nothing has to be restated.  The brief's name is kept  *)
(*  so that the stage and the links can be read against it, and the        *)
(*  redundancy is REPORTED.                                                *)
(* ====================================================================== *)
Lemma sessp_prefix_det2 (ps ps' cs cs' : list nat) (I' I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps ->
  pro_ok_p ps' cs' (nlines I') ->
  alts_ok_p I cs -> alts_ok_p I' cs' ->
  pro_pin_p ps cs I -> disc_input_p I -> disc_input_p I' ->
  (forall i, (i < nlines I')%nat -> palt_isforkS (palt_at cs i) = true ->
     (S i = nlines I /\ rest_of I = [])) ->
  (forall i, (i < nlines I')%nat ->
     ~ pmergeable (pcont (pline_of (bodies_of I' !!! i)) (palt_at cs' i))) ->
  sessp ps' cs' I' `prefix_of` sessp ps cs I ->
  I' `prefix_of` I /\ pro_ok_p ps cs (nlines I')
  /\ sessp ps' cs' I' = sessp ps cs I'
  /\ (forall i, (i < nlines I')%nat ->
        alt_cont_p ps' cs' (bodies_of I') i = alt_cont_p ps cs (bodies_of I) i).
Proof using.
  exact (sessp_prefix_det ps ps' cs cs' I' I).
Qed.

(* THE DISCIPLINE'S LOWER BOUND AT THE OPEN CYCLE'S LAST INPUT: D1/D2 read
   off [disc_seg_p'] at the wire the last byte was typed on.
   [EchoOutPure.disc_seg'_pt_last]'s twin. *)
Lemma disc_seg_p'_pt_last (seg : list mobs) (c : bv 8) :
  disc_seg_p' seg -> obs_ends_in Uart0 seg c ->
  exists ps' cs' : list nat,
    pro_ok_p ps' cs' (nlines (removelast (ins seg)))
    /\ alts_ok_p (removelast (ins seg)) cs'
    /\ (forall i, (i < nlines (removelast (ins seg)))%nat ->
          ~ pmergeable
              (pcont (pline_of (bodies_of (removelast (ins seg)) !!! i))
                 (palt_at cs' i)))
    /\ sessp ps' cs' (removelast (ins seg)) `prefix_of` obs_wire Uart0 seg.
Proof using.
  intros [Hd (ps & cs & Hao & Hd4 & Hall)] [seg0 ->].
  assert (Hip : seg0 ∈ in_pres (seg0 ++ [ObsUartIn Uart0 c])).
  { rewrite in_pres_in. apply elem_of_app. right. apply elem_of_list_here. }
  destruct (Hall _ Hip) as [Hok Hpt]. rewrite /disc_pt_p in Hpt.
  rewrite ins_app ins_in epu_removelast_snoc.
  assert (Hpr : ins seg0 `prefix_of` ins (seg0 ++ [ObsUartIn Uart0 c])).
  { rewrite ins_app ins_in. by eexists. }
  assert (Hle : (nlines (ins seg0) <= nlines (ins seg0 ++ [c]))%nat)
    by (apply nlines_prefix; by eexists).
  exists ps, (take (nlines (ins seg0)) cs).
  assert (Heq : sessp ps (take (nlines (ins seg0)) cs) (ins seg0)
                = sessp ps cs (ins seg0))
    by (apply sessp_take; lia).
  split.
  { destruct Hok as [HF Hlt]. split; [exact HF |].
    rewrite (pro_idx_p_take cs (nlines (ins seg0)) (nlines (ins seg0))
               ltac:(lia)). exact Hlt. }
  split.
  { exact (alts_ok_p_take _ _ cs Hpr Hao). }
  split.
  { rewrite ins_app ins_in in Hao, Hd4.
    exact (d4_p_nomerge_snoc cs (ins seg0) c Hao Hd4). }
  rewrite Heq. etrans; [exact Hpt |]. rewrite obs_wire_app. by eexists.
Qed.

(* [sessp] is never empty once round 0 has settled *)
Lemma sessp_nonnil (ps cs : list nat) (I : list (bv 8)) :
  Forall (fun a => (a < length pro_alts)%nat) ps -> pro_done ps ->
  sessp ps cs I <> [].
Proof using.
  intros HF Hd H. rewrite /sessp in H.
  apply app_eq_nil in H as [H _].
  assert (Hne : ps <> []) by (intros ->; by apply Exists_nil in Hd).
  pose proof (pro_of_pos ps HF Hne) as Hpos. rewrite H in Hpos.
  cbn [length] in Hpos. lia.
Qed.
