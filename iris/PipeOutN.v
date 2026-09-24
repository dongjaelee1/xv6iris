(* ===================================================================== *)
(*  PipeOutN.v -- THE N-WRITER ROUND'S CLAIM (design:                    *)
(*  claude-notes/design/pipes-general.md SS2.2, cut C5).                 *)
(*                                                                       *)
(*  [PipeOut.pecl] -- the generic claim between rounds, [popen] while a  *)
(*  two-writer round is open -- at the per-stage outcome model           *)
(*  [PipesDisc.pipes_lm], with the open round read off the line MODEL    *)
(*  and not off [PipeDisc]'s alternatives:                               *)
(*                                                                       *)
(*    pecl' := gcl (pipes_lm fc adm) .. ∨ popenN                         *)
(*                                                                       *)
(*  1. The open reading, pure and over ANY line model ([lm_blk_open],    *)
(*     [gcl_pure_o]), with the three out-steps of the pure part.         *)
(*  2. The claim at [pipes_lm]: its parameters (the laws and the hooks   *)
(*     are the caller's), [popenN], [pecl'], and the three claim steps   *)
(*     [pecl'_blkN_open_gen] / [_byte_gen] / [_file], the twins of the   *)
(*     landed [PipeOut.pecl_blk2_*].                                     *)
(*  3. The family's credential [pwc_blkN] and the ONE obligation         *)
(*     [PipeBothN.eclN] it asks of the claim, PROVED here               *)
(*     ([pblkN_ecl_holds]), and the model's blocks as the claim's        *)
(*     non-terminal witness ([pipesN_HWIT]).                              *)
(*  4. THE N = 2 CHECK: the landed two-writer merge IS the N-form at     *)
(*     [W := bool], and the landed [PipeBoth.pblk2_wit_both] (the        *)
(*     witness the landed byte steps spend at a [PBoth] round) is        *)
(*     re-derived from [PipeBothNPure.pendN_complete] through the n = 1 *)
(*     bridge of C2 ([PipesDisc.palt_of_ok]).                             *)
(* ===================================================================== *)
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
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import PipeDisc.
Require Import PipeBothPure.
Require Import EchoOut.
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import GenOutHist.
Require Import GenOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import ProgTree.
Require Import PipesDisc.
Require Import PipeBothNPure.
Require Import PipeBothN.
Require Import PipeHooks.         (* [pline_at] *)
Require Import PipeBoth.          (* the N = 2 check: [pblk2_wit] *)
(* stdpp's list names over the ones the Stdlib import above re-exports *)
From stdpp Require Import list.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE OPEN READING, OVER ANY LINE MODEL                             *)
(* ===================================================================== *)

Lemma lmN_prefix_head {A} (l : list A) (b : A) : l !! 0%nat = Some b -> [b] `prefix_of` l.
Proof using. destruct l as [| x l]; [discriminate | cbn; intros [= ->]; by exists l]. Qed.

Lemma lmN_prefix_snoc {A} (w l : list A) (b : A) :
  (w ++ [b]) `prefix_of` l -> w `prefix_of` l.
Proof using. intros Hp. etrans; [| exact Hp]. by eexists. Qed.

Section open_pure.
  Context (M : lmodel) (sd : lm_st M).
  Local Notation st so := (gs_state M sd so).

  (* [GenOutPure.lm_out_pure] minus the conjunct that reads the block off
     the choice list: the landed [PipeOut.pout_pure_o], once *)
  Definition lm_out_pure_o (k : nat) (ho : list mobs) (so : gstage M)
      (acc : list (bv 8)) : Prop :=
    acc = lm_D M (gs_ps M so) (gs_cs M so) (st so) (gs_E M so) ++ gs_w M so
    /\ E_index (gs_E M so)
    /\ lm_E_disc M (gs_E M so)
    /\ Forall (fun a => (a < length pro_alts)%nat) (gs_ps M so)
    /\ lm_pro_pin M (gs_ps M so) (gs_cs M so) (snd <$> gs_E M so)
    /\ lm_alts_pre M (snd <$> gs_E M so) (gs_cs M so)
    /\ Forall (fun x => lm_disc_input M (ins x.1)) (gs_E M so)
    /\ Forall (fun x => x.1 `prefix_of` open_seg ho) (gs_E M so)
    /\ (length (gs_E M so) <= length (ins (open_seg ho)))%nat
    /\ (gs_E M so = [] \/ obs_boots ho = k)
    /\ Forall (fun c => lm_term M (lm_dec M c) = false) (gs_cs M so)
    /\ (gs_st M so = None <-> (gs_E M so = [] /\ gs_w M so = []))
    /\ lm_st_ok M (st so).

  (* THE ROUND'S LINE AND AN ADMITTED ALTERNATIVE the block so far is a
     prefix of: [PipeBothPure.pblk2_at], at the model *)
  Definition lm_blk_at (cs : list nat) (I : list (bv 8)) (s : lm_st M)
      (pre : list (bv 8)) (a : nat) : Prop :=
    I <> [] /\ rest_of I = [] /\ length cs = (nlines I - 1)%nat
    /\ lm_ok M (lm_of M (bodies_of I !!! (nlines I - 1))) (lm_dec M a)
    /\ lm_panic M (lm_dec M a) = false
    /\ pre `prefix_of` lm_cont M (lm_upto M cs s (bodies_of I) (nlines I - 1))
                         (lm_of M (bodies_of I !!! (nlines I - 1))) (lm_dec M a).

  (* THE BLOCK IN PROGRESS: [PipeOut.pblk_open], at the model *)
  Definition lm_blk_open (so : gstage M) (r : nat) (pre : list (bv 8)) : Prop :=
    r = (nlines (snd <$> gs_E M so) - 1)%nat
    /\ gs_w M so = pre
    /\ pre <> []
    /\ exists a : nat,
         lm_blk_at (gs_cs M so) (snd <$> gs_E M so) (st so) pre a
         /\ ((lm_term M (lm_dec M a) = false /\ Forall nodollar pre)
             \/ lm_term M (lm_dec M a) = true).

  (* the claim's pure part WHILE A ROUND IS OPEN: [PipeOut.pcl_pure_o] *)
  Definition gcl_pure_o (k : nat) (ho : list mobs) (so : gstage M)
      (r : nat) (pre : list (bv 8)) (H : LogEntryDefs.cons_hist) : Prop :=
    lm_out_pure_o k ho so (LogEntryDefs.ch_acc H)
    /\ lm_blk_open so r pre
    /\ lm_ps_len_ok M sd so
    /\ gin_pure M k (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) (gs_cs M so)
    /\ garm_era M k ho H
    /\ gs_E M so = ch_E H
    /\ lm_dl_ok M so (LogEntryDefs.ch_dl H).

  Lemma gcl_pure_o_dl_E k ho so r pre H :
    gcl_pure_o k ho so r pre H ->
    (snd <$> LogEntryDefs.ch_dl H) `prefix_of` (snd <$> gs_E M so).
  Proof using.
    intros (_ & _ & _ & Hin & _ & HE & _).
    destruct Hin as (_ & _ & _ & Hdlp & _).
    rewrite HE /ch_E.
    etrans; [exact (epu_fmap_prefix snd _ _ Hdlp) |].
    rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log H))).
    apply epu_fmap_prefix. by apply prefix_app_r.
  Qed.

  (* THE THREE OUT-STEPS of the pure part: opening, keeping, closing *)
  Lemma gcl_pure_o_out k ho (so so' : gstage M) r pre H (b : bv 8) :
    (length (gs_cs M so) <= length (gs_cs M so'))%nat -> gs_E M so' = gs_E M so ->
    lm_out_pure_o k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
    lm_blk_open so' r pre -> lm_ps_len_ok M sd so' ->
    lm_dl_ok M so' (LogEntryDefs.ch_dl H) ->
    gcl_pure M sd k ho so H ->
    gcl_pure_o k ho so' r pre (ConsLog.cons_step H (ConsLog.EvOut b)).
  Proof using.
    intros Hcs' HE' Hout Hop Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
    destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
    rewrite /gcl_pure_o /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hop | exact Hp | | exact Hera | | exact Hdlok'].
    - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                  | exact HEi | exact HEb | lia | exact Hall].
    - by rewrite HE' HE /ch_E.
  Qed.

  Lemma gcl_pure_o_out2 k ho (so so' : gstage M) r r' pre pre' H (b : bv 8) :
    (length (gs_cs M so) <= length (gs_cs M so'))%nat -> gs_E M so' = gs_E M so ->
    lm_out_pure_o k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
    lm_blk_open so' r' pre' -> lm_ps_len_ok M sd so' ->
    lm_dl_ok M so' (LogEntryDefs.ch_dl H) ->
    gcl_pure_o k ho so r pre H ->
    gcl_pure_o k ho so' r' pre' (ConsLog.cons_step H (ConsLog.EvOut b)).
  Proof using.
    intros Hcs' HE' Hout Hop Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
    destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
    rewrite /gcl_pure_o /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hop | exact Hp | | exact Hera | | exact Hdlok'].
    - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                  | exact HEi | exact HEb | lia | exact Hall].
    - by rewrite HE' HE /ch_E.
  Qed.

  Lemma gcl_pure_of_o_out k ho (so so' : gstage M) r pre H (b : bv 8) :
    (length (gs_cs M so) <= length (gs_cs M so'))%nat -> gs_E M so' = gs_E M so ->
    lm_out_pure M sd k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
    lm_cs_len_ok M so' -> lm_ps_len_ok M sd so' ->
    lm_dl_ok M so' (LogEntryDefs.ch_dl H) ->
    gcl_pure_o k ho so r pre H ->
    gcl_pure M sd k ho so' (ConsLog.cons_step H (ConsLog.EvOut b)).
  Proof using.
    intros Hcs' HE' Hout Hc Hp Hdlok' (_ & _ & _ & Hin & Hera & HE & _).
    destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt & Hall).
    rewrite /gcl_pure /ConsLog.cons_step.
    cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
         LogEntryDefs.ch_arm].
    split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera | | exact Hdlok'].
    - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                  | exact HEi | exact HEb | lia | exact Hall].
    - by rewrite HE' HE /ch_E.
  Qed.

  (* [GenOutPure.lm_ps_len_ok_blk] at ANY written block: the filing byte
     of a round whose block several writers put out ([PipeOut]'s
     [ps_len_ok_p_blk_w], once) *)
  Lemma lm_ps_len_ok_blk_w (B : lm_byte_laws M) (so : gstage M) (a : nat)
      (w' : list (bv 8)) :
    rest_of (snd <$> gs_E M so) = [] ->
    (snd <$> gs_E M so) <> [] ->
    length (gs_cs M so) = (nlines (snd <$> gs_E M so) - 1)%nat ->
    lm_ps_len_ok M sd so ->
    lm_ps_len_ok M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so) w'
                        (gs_st M so)).
  Proof using.
    intros Hr Hne Hq Hok.
    pose proof (nlines_pos_of_rest_nil (snd <$> gs_E M so) Hne Hr) as Hpos.
    pose proof Hok as [HA HB].
    rewrite /lm_ps_len_ok /lm_ps_round /lm_ps_opens in HA, HB |- *.
    cbn [gs_ps gs_cs gs_E gs_w gs_st] in HA, HB |- *.
    assert (Hold : lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))
                   = lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so) - 1)%nat).
    { replace (nlines (snd <$> gs_E M so))
        with (S (nlines (snd <$> gs_E M so) - 1))%nat at 1 by lia.
      apply lm_pro_idx_Sn. apply (lm_panic_ge M B). lia. }
    assert (Hnew : (lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))
                    <= lm_pro_idx M (gs_cs M so ++ [a])
                         (nlines (snd <$> gs_E M so)))%nat).
    { rewrite Hold.
      replace (nlines (snd <$> gs_E M so))
        with (S (nlines (snd <$> gs_E M so) - 1))%nat at 2 by lia.
      rewrite lm_pro_idx_S
        (lm_pro_idx_app_le M (gs_cs M so) [a] (nlines (snd <$> gs_E M so) - 1)%nat
           ltac:(lia)).
      destruct (lm_panic M _); lia. }
    split.
    - apply (lm_ps_len_ok_empty_above M sd so); [exact Hok |].
      rewrite /lm_ps_round. exact Hnew.
    - intros Ho ps' Hp Hne2. exfalso.
      destruct Ho as [Hz | [_ H3]]; [by destruct (Hne Hz) |].
      assert (Ha3 : lm_panic M (lm_dec M a) = true).
      { rewrite /lm_at list_lookup_total_alt lookup_app_r in H3; [| lia].
        rewrite Hq Nat.sub_diag in H3. by cbn in H3. }
      assert (Heq : lm_pro_idx M (gs_cs M so ++ [a]) (nlines (snd <$> gs_E M so))
                    = S (lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so)))).
      { rewrite Hold
          -(lm_pro_idx_app_le M (gs_cs M so) [a] (nlines (snd <$> gs_E M so) - 1)%nat
              ltac:(lia)).
        replace (nlines (snd <$> gs_E M so))
          with (S (nlines (snd <$> gs_E M so) - 1))%nat at 1 by lia.
        apply lm_pro_idx_Sp.
        rewrite /lm_at list_lookup_total_alt lookup_app_r; [| lia].
        rewrite Hq Nat.sub_diag. by cbn. }
      rewrite Heq in Hne2. apply Hne2.
      assert (Hnil : pro_from
                       (S (lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))))
                       (gs_ps M so) = []) by exact HA.
      assert (Hnil' : pro_from
                        (S (lm_pro_idx M (gs_cs M so) (nlines (snd <$> gs_E M so))))
                        ps' = []).
      { apply prefix_nil_inv. rewrite -Hnil. by apply pro_from_mono. }
      by rewrite Hnil Hnil'.
  Qed.
End open_pure.

(* the continuation of a round whose alternative does not panic is the
   alternative's own, with no prologue after it *)
Lemma lmN_cont_at_nopanic (M : lmodel) ps cs s bs i :
  lm_panic M (lm_at M cs i) = false ->
  lm_cont_at M ps cs s bs i = lm_cont M (lm_upto M cs s bs i) (lm_of M (bs !!! i)) (lm_at M cs i).
Proof using. intros H. rewrite /lm_cont_at H. apply app_nil_r. Qed.

(* ===================================================================== *)
(*  2.  THE CLAIM AT THE PER-STAGE OUTCOME MODEL                          *)
(* ===================================================================== *)

Section pipes_out_n.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Notation T := (echo_taint γ).
  (* THE MODEL: the content function, the admitted lines, and the laws
     and hooks of [pipes_lm fc adm], which are the caller's (the laws at
     [PipesDisc.pipes_lm_laws], the hooks a later cut's) *)
  Context (fc : bytes -> option bytes) (adm : pline' -> bool).
  Context (Lw : lm_laws (pipes_lm fc adm)) (K : lm_hooks (pipes_lm fc adm)).
  Local Notation PM := (pipes_lm fc adm).
  Local Notation PB := (pipes_lm_byte_laws fc adm).

  (* the model's state is [unit]: nothing survives a round *)
  Lemma pipesN_st (s : lm_st PM) : s = tt.
  Proof using. by destruct s. Qed.

  Definition pipesN_cparams : gen_cparams PM :=
    MkGCP PM Lw K T _ _ (era_pin γ) _ _ (era_pin_agree γ) (fun _ _ => emp%I) _ _.

  Lemma pipesN_wa_agree (k : nat) (st : option (lm_st PM)) (s0 : lm_st PM) :
    (emp : iProp Σ) -∗ emp -∗ ⌜default tt st = s0⌝.
  Proof using . iIntros "_ _". iPureIntro. by destruct (default tt st), s0. Qed.

  Lemma pipesN_wa_W (k : nat) (s0 : lm_st PM) :
    (emp : iProp Σ) -∗ emp ∗ emp ∗ emp.
  Proof using . iIntros "_". by iSplit; [| iSplit]. Qed.

  Lemma pipesN_wa_file (k : nat) (s0 : lm_st PM) :
    (emp : iProp Σ) -∗ emp ==∗ emp ∗ emp.
  Proof using . iIntros "_ _". by iModIntro; iSplit. Qed.

  Lemma pipesN_wa_free (k : nat) : (emp : iProp Σ) ==∗ emp.
  Proof using . by iIntros "_". Qed.

  (* the stream extension is the PIPE's: the era's byte ledger and the
     current-round ghost, held whole between rounds ([PipeOut.pext]) *)
  Definition pipesN_wa : gen_wa PM pipesN_cparams tt :=
    @MkGWA Σ _ PM pipesN_cparams tt (fun _ _ => emp%I) _ pipesN_wa_agree
      (fun _ => emp%I) _ pipesN_wa_W (fun _ _ => emp%I) pipesN_wa_file
      False (fun Hf => match Hf with end)
      True (fun _ => pipesN_wa_free)
      (pext g) _ (pext_grow g).

  (* THE OPEN ROUND: [PipeOut.popen] with the stage read at the model *)
  Definition popenN (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (∃ (v : era_pins) (w : pipe_era) (so : gstage PM)
       (r : nat) (gb : gname) (pre : list (bv 8)) (tm : bool),
       era_pin γ k v ∗ pera_pin g k w ∗ blk_auth w (lm_stream PM tt so)
       ∗ cur_half w (1/2) r gb tm ∗ rblk_auth gb pre
       ∗ turn_auth v (lm_pcount PM (gs_ps PM so) (gs_cs PM so)
                        (gs_state PM tt so) (gs_E PM so) (gs_w PM so))
       ∗ pcs v (gs_cs PM so) tm
       ∗ ps_auth v (gs_ps PM so)
       ∗ Elist_auth v (gs_E PM so)
       ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
       ∗ dl_list_auth v (LogEntryDefs.ch_dl H)
       ∗ ⌜gcl_pure_o PM tt k ho so r pre H⌝)%I.

  (* THE CLAIM: the generic one between rounds, [popenN] while a round of
     any number of writers is open -- design SS5's [pecl'] *)
  Definition pecl' (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    (gcl PM pipesN_cparams tt pipesN_wa k ho H ∨ popenN k ho H)%I.

  Global Instance pecl'_timeless k ho H : Timeless (pecl' k ho H).
  Proof using . rewrite /pecl' /popenN. apply _. Qed.

  Lemma pecl'_taint (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    T -∗ pecl' k ho H.
  Proof using . iIntros "#HT". rewrite /pecl' /gcl. iLeft. by iLeft. Qed.

  (* ---- (W-openN) THE ROUND'S FIRST BYTE: [PipeOut.pecl_blk2_open_gen]
          at the model.  The alternative is NOT filed; the claim mints the
          round's own ledger and splits the current-round ghost, and at a
          coverage-ending alternative freezes its resolution. ---- *)
  Lemma pecl'_blkN_open_gen (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    lm_pro_pin PM ps0 cs0 I0 ->
    P = length (lm_proc_before PM ps0 cs0 tt I0) ->
    lm_ok PM (lm_of PM (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec PM a) ->
    lm_panic PM (lm_dec PM a) = false ->
    lm_cont PM tt (lm_of PM (bodies_of I0 !!! (nlines I0 - 1)%nat)) (lm_dec PM a)
      !! 0%nat = Some b ->
    ((lm_term PM (lm_dec PM a) = false /\ nodollar b)
     \/ lm_term PM (lm_dec PM a) = true) ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl' k ho H ==∗
      pecl' k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (w : pipe_era) (gb : gname),
            turn v (S P) ∗ pera_pin g k w
            ∗ cur_half w (1/2) (nlines I0 - 1)%nat gb (lm_term PM (lm_dec PM a))
            ∗ rblk_lb gb [b]
            ∗ (⌜lm_term PM (lm_dec PM a) = false⌝
               ∨ cs_frozen_at v (nlines I0 - 1)%nat)
            ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T).
  Proof using K.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hpan Hhead Hfarm.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    pose proof (ll_nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hcl".
    iDestruct "Hcl" as "[Hcl | Hp]"; last first.
    { (* AN OPEN ROUND has already written a byte: the turn refutes it *)
      iDestruct "Hp" as (v2 w so r gb pre tm)
        "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
      iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
      iDestruct (turn_agree with "Ht Hta") as %HP.
      iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
      iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
      iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
      assert (HI0 : I0 `prefix_of` (snd <$> gs_E PM so)).
      { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E PM tt _ _ _ _ _ _ Hopen)]. }
      destruct Hopen as (_ & Hop & _).
      pose proof Hop as (_ & Hwpre' & Hne' & _).
      rewrite (pipesN_st (gs_state PM tt so)) in HP.
      assert (Hs2 : lm_proc_before PM ps0 cs0 tt I0
                    = lm_proc_before PM (gs_ps PM so) (gs_cs PM so) tt I0).
      { apply (lm_proc_before_cs_prefix PM ps0 (gs_ps PM so) cs0 (gs_cs PM so) tt I0
                 Hpsp Hcsp Hpin0). lia. }
      pose proof (prefix_length _ _
        (lm_proc_before_prefix PM (gs_ps PM so) (gs_cs PM so) tt I0
           (snd <$> gs_E PM so) HI0)) as Hle2.
      assert (Hwne : (1 <= length (gs_w PM so))%nat).
      { rewrite Hwpre'. destruct pre; [by destruct (Hne' eq_refl) | cbn; lia]. }
      rewrite /lm_pcount in HP. rewrite HPeq Hs2 in HP.
      exfalso. lia. }
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [by iApply pecl'_taint | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & _ & Hext & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct "Hext" as (w r gb pre tm) "(#Hpera & Hblk & Hcur & Hrb)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E PM so)).
    { etrans; [exact HI0dl | exact (gcl_pure_dl_E PM tt k ho so H Hall0)]. }
    rewrite (pipesN_st (gs_state PM tt so)) in HP.
    assert (Hstream : lm_proc_before PM ps0 cs0 tt I0
                      = lm_proc_before PM (gs_ps PM so) (gs_cs PM so) tt I0).
    { apply (lm_proc_before_cs_prefix PM ps0 (gs_ps PM so) cs0 (gs_cs PM so)
               tt I0 Hpsp Hcsp Hpin0). lia. }
    assert (HlenE : (snd <$> gs_E PM so) = I0).
    { destruct (decide ((snd <$> gs_E PM so) = I0)) as [? | Hne]; [done | exfalso].
      pose proof (lm_proc_stream_before PM (gs_ps PM so) (gs_cs PM so)
                    tt I0 (snd <$> gs_E PM so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
      apply prefix_length in Hpre.
      rewrite /lm_proc_stream length_app -Hstream in Hpre.
      pose proof (lm_pending_at_nonnil_at PM K (gs_ps PM so) (gs_cs PM so)
                    tt I0 (snd <$> gs_E PM so) HI0 Hcsb' Hne0 Hr0) as Hne1.
      assert (Hlen1 : (1 <= length (lm_pending_at PM (gs_ps PM so) (gs_cs PM so)
                                     tt I0))%nat).
      { destruct (lm_pending_at PM (gs_ps PM so) (gs_cs PM so) tt I0);
          [done | cbn; lia]. }
      rewrite /lm_pcount in HP. lia. }
    assert (Hwnil : gs_w PM so = []).
    { assert (Hz : length (gs_w PM so) = 0%nat).
      { rewrite /lm_pcount in HP. rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    destruct (lm_cs_len_ok_inv PM so Hcsl) as [[_ Hq] | [Hne _]]; last first.
    { exfalso. apply Hne. split; [exact Hwnil | by rewrite HlenE]. }
    rewrite HlenE in Hq.
    assert (Hpc2 : forall s : lm_st PM,
               lm_pcount PM (gs_ps PM so) (gs_cs PM so) s (gs_E PM so) [b] = S P).
    { intros s. rewrite (pipesN_st s) /lm_pcount HlenE -Hstream. cbn [length]. lia. }
    (* the round's OWN ledger, minted here and nowhere else *)
    iMod rblk_alloc as (gb2) "Hrb2".
    iMod (rblk_auth_grow gb2 [] b with "Hrb2") as "[Hrb2 #Hrlb]".
    iMod (cur_retarget w r gb tm (nlines I0 - 1)%nat gb2
            (lm_term PM (lm_dec PM a)) with "Hcur") as "Hcur".
    iDestruct (cur_split w (nlines I0 - 1)%nat gb2 (lm_term PM (lm_dec PM a))
                 with "Hcur") as "[Hcur1 Hcur2]".
    iDestruct (pcs_of_auth v (gs_cs PM so) false eq_refl with "Hcs") as "Hcs".
    iAssert (|==> pcs v (gs_cs PM so) (lm_term PM (lm_dec PM a))
                  ∗ (⌜lm_term PM (lm_dec PM a) = false⌝
                     ∨ cs_frozen_at v (nlines I0 - 1)%nat))%I
      with "[Hcs]" as ">[Hcs #Hfz]".
    { destruct (lm_term PM (lm_dec PM a)) eqn:Hfk2.
      - iMod (pcs_freeze v (gs_cs PM so) false with "Hcs") as "[Hcs #Hf]".
        iModIntro. iFrame "Hcs". iRight.
        iApply (cs_frozen_at_of v (gs_cs PM so) (nlines I0 - 1)%nat with "Hf").
        exact Hq.
      - iModIntro. iFrame "Hcs". iLeft. by iPureIntro. }
    iMod (turn_update v P _ (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (lm_stream PM tt so) b with "Hblk") as "[Hblk _]".
    iModIntro. iSplitR "Ht Hcur2".
    - rewrite /pecl'. iRight.
      iExists v, w, (MkGS PM (gs_ps PM so) (gs_cs PM so) (gs_E PM so) [b] (gs_st PM so)),
              (nlines I0 - 1)%nat, gb2, [b], (lm_term PM (lm_dec PM a)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st]. rewrite Hpc2.
      rewrite (_ : lm_stream PM tt (MkGS PM (gs_ps PM so) (gs_cs PM so) (gs_E PM so)
                                      [b] (gs_st PM so))
                   = lm_stream PM tt so ++ [b]); last first.
      { rewrite /lm_stream. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        rewrite Hwnil app_nil_r. reflexivity. }
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hpera Hblk Hcur1 Hrb2 Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (gcl_pure_o_out PM tt k ho so
               (MkGS PM (gs_ps PM so) (gs_cs PM so) (gs_E PM so) [b] (gs_st PM so))
               (nlines I0 - 1)%nat [b] H b);
        [cbn [gs_cs]; lia | reflexivity | | | | | exact Hall0].
      + rewrite /lm_out_pure_o. cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * rewrite Hacc Hwnil app_nil_r. reflexivity.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpin.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * exact Hnofk.
        * split; [| intros [_ Hq2]; discriminate Hq2].
          intros Hnone. exfalso. destruct (proj1 Hf0n Hnone) as [HE0 _].
          apply Hne0. by rewrite -HlenE HE0.
        * exact Hfok0.
      + rewrite /lm_blk_open. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        split_and!; [by rewrite HlenE | reflexivity | done |].
        exists a. split.
        { rewrite /lm_blk_at HlenE.
          split_and!; [exact Hne0 | exact Hr0 | exact Hq | exact Halt | exact Hpan |].
          apply lmN_prefix_head. exact Hhead. }
        destruct Hfarm as [[Hfk Hnd] | Hfk];
          [left; split; [exact Hfk | by apply Forall_singleton] | by right].
      + pose proof (lm_ps_len_ok_write PM tt so b Hpsl) as Hx.
        rewrite Hwnil in Hx. exact Hx.
      + apply (lm_dl_ok_out_full PM so
                 (MkGS PM (gs_ps PM so) (gs_cs PM so) (gs_E PM so) [b] (gs_st PM so)));
          [reflexivity | cbn [gs_w]; discriminate | by rewrite HlenE |].
        pose proof (prefix_length _ _ HI0dl) as Hlp.
        rewrite !length_fmap in Hlp. rewrite HlenE. lia.
    - iLeft. iExists w, gb2.
      iFrame "Ht Hpera Hcur2 Hrlb Hfz Hpslb Hcslb Hilb".
  Qed.

  (* ---- (W-byteN) A FURTHER BYTE OF AN OPEN ROUND, by ANY of its writers:
          [PipeOut.pecl_blk2_byte_gen] at the model.  The writer's half of
          the current-round ghost says its round and ledger ARE the claim's,
          and the ledger pins the bytes. ---- *)
  Lemma pecl'_blkN_byte_gen (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (tmi : bool) (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    lm_pro_pin PM ps0 cs0 I0 ->
    P = length (lm_proc_before PM ps0 cs0 tt I0) ->
    lm_ok PM (lm_of PM (bodies_of I0 !!! r)) (lm_dec PM a) ->
    lm_panic PM (lm_dec PM a) = false ->
    (pre0 ++ [b]) `prefix_of` lm_cont PM tt (lm_of PM (bodies_of I0 !!! r)) (lm_dec PM a) ->
    ((lm_term PM (lm_dec PM a) = false /\ Forall nodollar pre0 /\ nodollar b)
     \/ lm_term PM (lm_dec PM a) = true) ->
    era_pin γ k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb tmi -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl' k ho H ==∗
      pecl' k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S (P + length pre0))%nat
          ∗ cur_half w (1/2) r gb (tmi || lm_term PM (lm_dec PM a))
          ∗ rblk_lb gb (pre0 ++ [b])
          ∗ (⌜lm_term PM (lm_dec PM a) = false⌝ ∨ cs_frozen_at v r)) ∨ T).
  Proof using K.
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hpref Hfarm.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    iIntros "#Hpin #Hperaw Ht Hcw #Hrlb0 #Hpslb #Hcslb #Hilb Hcl".
    iDestruct "Hcl" as "[Hcl | Hp]".
    { (* BETWEEN ROUNDS the claim holds the whole ghost *)
      iDestruct "Hcl" as "[#HT | Hp]".
      { iModIntro. iSplitR; [by iApply pecl'_taint | by iRight]. }
      iDestruct "Hp" as (v2 so) "(_ & _ & Hext & _)".
      iDestruct "Hext" as (w2 r2 gb2 pre tm) "(#Hpera & _ & Hcur & _)".
      iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
      iDestruct (cur_half_excl with "Hcur Hcw") as %[]. }
    iDestruct "Hp" as (v2 w2 so r2 gb2 pre tm)
      "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E PM so)).
    { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E PM tt _ _ _ _ _ _ Hopen)]. }
    iDestruct (cur_half_agree with "Hcur Hcw") as %(-> & -> & Htmeq).
    subst tm.
    pose proof Hopen as (Hout & Hop & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hout as (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                        & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    pose proof Hop as (Hreq2 & Hwp' & Hne' & ao & Hb2 & Harm).
    pose proof Hb2 as (Hnn & Hrr & Hqq & Hokao & Hpanao & Hprefao).
    iDestruct (rblk_lb_prefix with "Hrb Hrlb0") as %Hprefl.
    pose proof (prefix_length _ _ Hprefl) as Hpl0.
    rewrite -Hwp' in Hpl0.
    rewrite (pipesN_st (gs_state PM tt so)) in HP.
    assert (Hs2 : lm_proc_before PM ps0 cs0 tt I0
                  = lm_proc_before PM (gs_ps PM so) (gs_cs PM so) tt I0).
    { apply (lm_proc_before_cs_prefix PM ps0 (gs_ps PM so) cs0 (gs_cs PM so) tt I0
               Hpsp Hcsp Hpin0).
      rewrite (ll_nlines_removelast _ Hr0) Hcseq Hreq. lia. }
    assert (HIeq : (snd <$> gs_E PM so) = I0).
    { destruct (decide ((snd <$> gs_E PM so) = I0)) as [? | Hne]; [done |].
      exfalso.
      pose proof (lm_proc_stream_before PM (gs_ps PM so) (gs_cs PM so) tt I0
                    (snd <$> gs_E PM so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hp2.
      apply prefix_length in Hp2.
      rewrite /lm_proc_stream length_app -Hs2 in Hp2.
      pose proof (lm_pending_at_nonnil_at PM K (gs_ps PM so) (gs_cs PM so)
                    tt I0 (snd <$> gs_E PM so) HI0 Hcsb' Hne0 Hr0) as Hne1.
      assert (Hlen1 : (1 <= length (lm_pending_at PM (gs_ps PM so) (gs_cs PM so)
                                     tt I0))%nat).
      { destruct (lm_pending_at PM (gs_ps PM so) (gs_cs PM so) tt I0);
          [done | cbn; lia]. }
      rewrite /lm_pcount in HP. lia. }
    assert (Hlen0 : length pre0 = length (gs_w PM so)).
    { rewrite /lm_pcount HIeq -Hs2 -HPeq in HP. lia. }
    assert (Hpre0 : pre0 = gs_w PM so).
    { rewrite Hwp' in Hlen0 |- *.
      exact (prefix_length_eq pre0 pre Hprefl ltac:(lia)). }
    (* THE TERMINAL FIRE: a coverage-ending byte sets the flag and freezes *)
    iAssert (|==> pcs v (gs_cs PM so) (tmi || lm_term PM (lm_dec PM a))
                  ∗ cur_half w (1/2) r gb (tmi || lm_term PM (lm_dec PM a))
                  ∗ cur_half w (1/2) r gb (tmi || lm_term PM (lm_dec PM a))
                  ∗ (⌜lm_term PM (lm_dec PM a) = false⌝ ∨ cs_frozen_at v r))%I
      with "[Hcs Hcur Hcw]" as ">(Hcs & Hcur & Hcw & #Hfz)".
    { destruct (lm_term PM (lm_dec PM a)) eqn:Hfk2.
      - rewrite (orb_true_r tmi).
        iMod (pcs_freeze v (gs_cs PM so) tmi with "Hcs") as "[Hcs #Hf]".
        iMod (cur_half_update w r gb tmi r gb tmi r gb true
                with "Hcur Hcw") as "[Hcur Hcw]".
        iModIntro. iFrame "Hcs Hcur Hcw". iRight.
        iApply (cs_frozen_at_of v (gs_cs PM so) r with "Hf").
        by rewrite Hqq Hreq2.
      - rewrite (orb_false_r tmi).
        iModIntro. iFrame "Hcs Hcur Hcw". iLeft. by iPureIntro. }
    iMod (rblk_auth_grow gb pre b with "Hrb") as "[Hrb #Hrlb1]".
    iMod (turn_update v (P + length pre0)%nat _ (S (P + length pre0)) ltac:(lia)
            with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (lm_stream PM tt so) b with "Hblk") as "[Hblk _]".
    assert (Hbod : bodies_of (snd <$> gs_E PM so) !!! r = bodies_of I0 !!! r)
      by (by rewrite HIeq).
    assert (Hpc2 : forall s : lm_st PM,
               lm_pcount PM (gs_ps PM so) (gs_cs PM so) s (gs_E PM so)
                 (gs_w PM so ++ [b]) = S (P + length pre0)).
    { intros s. rewrite lm_pcount_write (pipesN_st s) -HP. reflexivity. }
    iModIntro. iSplitR "Ht Hcw".
    - rewrite /pecl'. iRight.
      iExists v, w, (MkGS PM (gs_ps PM so) (gs_cs PM so) (gs_E PM so)
                       (gs_w PM so ++ [b]) (gs_st PM so)),
              r, gb, (pre ++ [b]), (tmi || lm_term PM (lm_dec PM a)).
      rewrite (lm_stream_write PM tt so b).
      cbn [gs_ps gs_cs gs_E gs_w gs_st]. rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hpera Hblk Hcur Hrb Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (gcl_pure_o_out2 PM tt k ho so
               (MkGS PM (gs_ps PM so) (gs_cs PM so) (gs_E PM so)
                  (gs_w PM so ++ [b]) (gs_st PM so))
               r r pre (pre ++ [b]) H b);
        [cbn [gs_cs]; lia | reflexivity | | | | | exact Hopen].
      + rewrite /lm_out_pure_o. cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * rewrite Hacc app_assoc. reflexivity.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpin.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * exact Hnofk.
        * split.
          -- intros Hn. exfalso. destruct (proj1 Hf0n Hn) as [_ Hw0].
             rewrite Hwp' in Hw0. exact (Hne' Hw0).
          -- intros [_ Hq2]. exfalso. destruct (app_eq_nil _ _ Hq2) as [_ Hq3].
             discriminate Hq3.
        * exact Hfok0.
      + rewrite /lm_blk_open. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        split_and!; [exact Hreq2 | by rewrite Hwp' |
                     intros Hz; destruct (app_eq_nil _ _ Hz) as [_ Hz2]; discriminate Hz2 |].
        exists a. split.
        { rewrite /lm_blk_at. rewrite -Hreq2 Hbod.
          split_and!; [exact Hnn | exact Hrr | by rewrite Hqq Hreq2 | exact Halt
                      | exact Hpan |].
          rewrite -Hwp' -Hpre0. exact Hpref. }
        destruct Hfarm as [(Hfk & Hnd0 & Hnd) | Hfk]; [| by right].
        left. split; [exact Hfk |].
        apply Forall_app. split; [| by apply Forall_singleton].
        rewrite -Hwp' -Hpre0. exact Hnd0.
      + exact (lm_ps_len_ok_write PM tt so b Hpsl).
      + apply (lm_dl_ok_out PM so
                 (MkGS PM (gs_ps PM so) (gs_cs PM so) (gs_E PM so)
                    (gs_w PM so ++ [b]) (gs_st PM so)));
          [reflexivity | cbn [gs_w] | left; rewrite Hwp'; exact Hne' | exact Hdlok].
        intro Hq. by destruct (app_eq_nil _ _ Hq) as [_ Hq2].
    - iLeft. rewrite Hpre0 -Hwp'. iFrame "Ht Hcw Hrlb1 Hfz".
  Qed.

  (* ---- (W-fileN) THE FILING, at the prompt's first byte:
          [PipeOut.pecl_blk2_file] at the model.  The filer presents its
          half at the flag [false], so the authority is the landed one and
          never the frozen one; the round's code enters [cs] and the ghost
          comes home whole. ---- *)
  Lemma pecl'_blkN_file (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    lm_pro_pin PM ps0 cs0 I0 ->
    P = length (lm_proc_before PM ps0 cs0 tt I0) ->
    lm_ok PM (lm_of PM (bodies_of I0 !!! r)) (lm_dec PM a) ->
    lm_panic PM (lm_dec PM a) = false ->
    lm_term PM (lm_dec PM a) = false ->
    lm_cont PM tt (lm_of PM (bodies_of I0 !!! r)) (lm_dec PM a) = pre0 ++ u_prompt ->
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb false -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    pecl' k ho H ==∗
      pecl' k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S (P + length pre0))%nat ∗ ps_lb v ps0
          ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0) ∨ T).
  Proof using K.
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hfk Hcont Hbv.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    iIntros "#Hpin #Hperaw Ht Hcw #Hrlb0 #Hpslb #Hcslb #Hilb Hcl".
    iDestruct "Hcl" as "[Hcl | Hp]".
    { iDestruct "Hcl" as "[#HT | Hp]".
      { iModIntro. iSplitR; [by iApply pecl'_taint | by iRight]. }
      iDestruct "Hp" as (v2 so) "(_ & _ & Hext & _)".
      iDestruct "Hext" as (w2 r2 gb2 pre tm) "(#Hpera & _ & Hcur & _)".
      iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
      iDestruct (cur_half_excl with "Hcur Hcw") as %[]. }
    iDestruct "Hp" as (v2 w2 so r2 gb2 pre tm)
      "(#Hpin2 & #Hpera & Hblk & Hcur & Hrb & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hopen)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (pera_pin_agree with "Hpera Hperaw") as %->.
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (pcs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E PM so)).
    { etrans; [exact HI0dl | exact (gcl_pure_o_dl_E PM tt _ _ _ _ _ _ Hopen)]. }
    iDestruct (cur_half_agree with "Hcur Hcw") as %(-> & -> & Htmeq).
    subst tm.
    pose proof Hopen as (Hout & Hop & Hpsl & Hin & Hera & HEtie & Hdlok).
    pose proof Hout as (Hacc & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                        & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    pose proof Hop as (Hreq2 & Hwp' & Hne' & ao & Hb2 & Harm).
    pose proof Hb2 as (Hnn & Hrr & Hqq & Hokao & Hpanao & Hprefao).
    iDestruct (rblk_lb_prefix with "Hrb Hrlb0") as %Hprefl.
    pose proof (prefix_length _ _ Hprefl) as Hpl0.
    rewrite -Hwp' in Hpl0.
    rewrite (pipesN_st (gs_state PM tt so)) in HP.
    assert (Hs2 : lm_proc_before PM ps0 cs0 tt I0
                  = lm_proc_before PM (gs_ps PM so) (gs_cs PM so) tt I0).
    { apply (lm_proc_before_cs_prefix PM ps0 (gs_ps PM so) cs0 (gs_cs PM so) tt I0
               Hpsp Hcsp Hpin0).
      rewrite (ll_nlines_removelast _ Hr0) Hcseq Hreq. lia. }
    assert (HIeq : (snd <$> gs_E PM so) = I0).
    { destruct (decide ((snd <$> gs_E PM so) = I0)) as [? | Hne]; [done |].
      exfalso.
      pose proof (lm_proc_stream_before PM (gs_ps PM so) (gs_cs PM so) tt I0
                    (snd <$> gs_E PM so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hp2.
      apply prefix_length in Hp2.
      rewrite /lm_proc_stream length_app -Hs2 in Hp2.
      pose proof (lm_pending_at_nonnil_at PM K (gs_ps PM so) (gs_cs PM so)
                    tt I0 (snd <$> gs_E PM so) HI0 Hcsb' Hne0 Hr0) as Hne1.
      assert (Hlen1 : (1 <= length (lm_pending_at PM (gs_ps PM so) (gs_cs PM so)
                                     tt I0))%nat).
      { destruct (lm_pending_at PM (gs_ps PM so) (gs_cs PM so) tt I0);
          [done | cbn; lia]. }
      rewrite /lm_pcount in HP. lia. }
    assert (Hlen0 : length pre0 = length (gs_w PM so)).
    { rewrite /lm_pcount HIeq -Hs2 -HPeq in HP. lia. }
    assert (Hpre0 : pre0 = gs_w PM so).
    { rewrite Hwp' in Hlen0 |- *.
      exact (prefix_length_eq pre0 pre Hprefl ltac:(lia)). }
    iMod (turn_update v (P + length pre0)%nat _ (S (P + length pre0)) ltac:(lia)
            with "Ht Hta") as "[Ht Hta]".
    iMod (blk_auth_grow w (lm_stream PM tt so) b with "Hblk") as "[Hblk _]".
    iDestruct (pcs_auth v (gs_cs PM so) false eq_refl with "Hcs") as "Hcs".
    iMod (cs_auth_grow v (gs_cs PM so) a with "Hcs") as "[Hcs #Hcslb2]".
    iDestruct (cur_join w r gb false with "Hcur Hcw") as "Hcur".
    assert (Hbod : bodies_of (snd <$> gs_E PM so) !!! r = bodies_of I0 !!! r)
      by (by rewrite HIeq).
    pose proof (nlines_pos_of_rest_nil _ Hnn Hrr) as Hposc.
    assert (Hcs0 : cs0 = gs_cs PM so).
    { apply (prefix_length_eq cs0 (gs_cs PM so) Hcsp). rewrite Hcseq Hqq Hreq2. lia. }
    assert (Hrlbnd : (nlines (removelast (snd <$> gs_E PM so))
                      <= length (gs_cs PM so))%nat).
    { rewrite (ll_nlines_removelast _ Hrr) Hqq. lia. }
    assert (Hpinq : lm_pro_pin PM (gs_ps PM so) (gs_cs PM so ++ [a]) (snd <$> gs_E PM so)).
    { intros qq Hqq2. rewrite lm_pro_idx_app_le; [by apply Hpin |].
      rewrite (nstarted_rest_nil _ Hrr) in Hqq2. rewrite Hqq. lia. }
    assert (HD : forall s : lm_st PM,
               lm_D PM (gs_ps PM so) (gs_cs PM so ++ [a]) s (gs_E PM so)
               = lm_D PM (gs_ps PM so) (gs_cs PM so) s (gs_E PM so)).
    { intros s. symmetry.
      apply (lm_D_cs_prefix PM (gs_ps PM so) (gs_ps PM so) (gs_cs PM so)
               (gs_cs PM so ++ [a]) s (gs_E PM so));
        [reflexivity | by eexists | exact Hpin | exact Hrlbnd]. }
    assert (Hproc : forall s : lm_st PM,
               lm_proc_before PM (gs_ps PM so) (gs_cs PM so ++ [a]) s (snd <$> gs_E PM so)
               = lm_proc_before PM (gs_ps PM so) (gs_cs PM so) s (snd <$> gs_E PM so)).
    { intros s. symmetry.
      apply (lm_proc_before_cs_prefix PM (gs_ps PM so) (gs_ps PM so) (gs_cs PM so)
               (gs_cs PM so ++ [a]) s (snd <$> gs_E PM so));
        [reflexivity | by eexists | exact Hpin | exact Hrlbnd]. }
    assert (Hpc2 : forall s : lm_st PM,
               lm_pcount PM (gs_ps PM so) (gs_cs PM so ++ [a]) s (gs_E PM so)
                 (gs_w PM so ++ [b]) = S (P + length pre0)).
    { intros s. rewrite /lm_pcount Hproc -/(lm_pcount PM (gs_ps PM so) (gs_cs PM so) s
                                              (gs_E PM so) (gs_w PM so ++ [b])).
      rewrite lm_pcount_write (pipesN_st s) -HP. reflexivity. }
    assert (Hat : lm_at PM (gs_cs PM so ++ [a]) (nlines (snd <$> gs_E PM so) - 1)
                  = lm_dec PM a).
    { rewrite /lm_at list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hqq Nat.sub_diag. reflexivity. }
    assert (HpendA : forall s : lm_st PM,
               lm_pending PM (gs_ps PM so) (gs_cs PM so ++ [a]) s (gs_E PM so)
               = pre0 ++ u_prompt).
    { intros s. rewrite /lm_pending /lm_pending_at decide_False; [| exact Hnn].
      rewrite decide_True; [| exact Hrr].
      rewrite lmN_cont_at_nopanic; [| by rewrite Hat].
      rewrite Hat -Hreq2 Hbod. exact Hcont. }
    iModIntro. iSplitR "Ht".
    - rewrite /pecl'. iLeft. rewrite /gcl. iRight.
      iExists v, (MkGS PM (gs_ps PM so) (gs_cs PM so ++ [a]) (gs_E PM so)
                    (gs_w PM so ++ [b]) (gs_st PM so)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st]. rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iSplitR; [iExact "Hpin" |]. iSplitR; [done |].
      iSplitL "Hblk Hcur Hrb".
      { unfold pipesN_wa. cbn [gext]. rewrite /pext.
        iExists w, r, gb, pre, false. iFrame "Hpera Hcur Hrb".
        rewrite (_ : lm_stream PM tt (MkGS PM (gs_ps PM so) (gs_cs PM so ++ [a])
                                        (gs_E PM so) (gs_w PM so ++ [b]) (gs_st PM so))
                     = lm_stream PM tt so ++ [b]); [iExact "Hblk" |].
        rewrite /lm_stream. cbn [gs_ps gs_cs gs_E gs_w gs_st].
        rewrite Hproc app_assoc. reflexivity. }
      iFrame "Hta Hcs Hps HE Hdl Hdll".
      iPureIntro.
      apply (gcl_pure_of_o_out PM tt k ho so
               (MkGS PM (gs_ps PM so) (gs_cs PM so ++ [a]) (gs_E PM so)
                  (gs_w PM so ++ [b]) (gs_st PM so))
               r pre H b);
        [cbn [gs_cs]; rewrite length_app; cbn [length]; lia
        | reflexivity | | | | | exact Hopen].
      + rewrite /lm_out_pure. cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * rewrite Hacc HD app_assoc. reflexivity.
        * rewrite HpendA -Hpre0 Hbv. apply prefix_app.
          exists (drop 1 u_prompt).
          rewrite -{1}(take_drop 1 u_prompt). f_equal.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpinq.
        * apply lm_alts_pre_snoc; [exact Hcsb' | rewrite Hqq; lia |].
          rewrite Hqq -Hreq2 Hbod. exact Halt.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * apply Forall_app. split; [exact Hnofk | by apply Forall_singleton].
        * split.
          -- intros Hn. exfalso. destruct (proj1 Hf0n Hn) as [_ Hw0].
             rewrite Hwp' in Hw0. exact (Hne' Hw0).
          -- intros [_ Hq2]. exfalso. destruct (app_eq_nil _ _ Hq2) as [_ Hq3].
             discriminate Hq3.
        * exact Hfok0.
      + apply lm_cs_len_ok_intro.
        * intros [Hz _]. exfalso. destruct (app_eq_nil _ _ Hz) as [_ Hz2].
          discriminate Hz2.
        * intros _. rewrite length_app Hqq. cbn [length]. lia.
      + exact (lm_ps_len_ok_blk_w PM tt PB so a (gs_w PM so ++ [b]) Hrr Hnn Hqq Hpsl).
      + apply (lm_dl_ok_out PM so
                 (MkGS PM (gs_ps PM so) (gs_cs PM so ++ [a]) (gs_E PM so)
                    (gs_w PM so ++ [b]) (gs_st PM so)));
          [reflexivity | cbn [gs_w] | left; rewrite Hwp'; exact Hne' | exact Hdlok].
        intro Hq. by destruct (app_eq_nil _ _ Hq) as [_ Hq2].
    - iLeft. rewrite Hcs0. iFrame "Ht Hpslb Hcslb2 Hilb".
  Qed.

  (* ================================================================= *)
  (*  3.  THE FAMILY'S CREDENTIAL, AND THE ONE OBLIGATION               *)
  (* ================================================================= *)

  (* the round's line *)
  Definition lineN (I : list (bv 8)) : pline' :=
    lm_of PM (bodies_of I !!! (nlines I - 1)%nat).

  (* the writer's stage at a block: [LineModel.lm_wr_blk] *)
  Definition wr_blkN (ps cs : list nat) (I : list (bv 8)) (P : nat) : Prop :=
    lm_wr_blk PM ps cs tt I P.

  (* THE ROUND'S LEDGER, as the family holds it: nothing before the first
     byte, the writer's half and the ledger's bound after *)
  Definition pledN (k : nat) (I pre : list (bv 8)) (tm : bool) : iProp Σ :=
    (⌜pre = []⌝ ∨ ∃ (w : pipe_era) (gb : gname),
        pera_pin g k w ∗ cur_half w (1/2) (nlines I - 1)%nat gb tm ∗ rblk_lb gb pre)%I.

  (* THE CREDENTIAL [PipeBothN]'s family is parameterised by: the landed
     [PipeBoth.pwc_blk2] read at the MERGED BYTES, whoever wrote them *)
  Definition pwc_blkN (v : era_pins) (I : list (bv 8)) (k : nat)
      (pre : list (bv 8)) (tm : bool) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_blkN ps cs I P⌝ ∗ era_pin γ k v ∗ turn v (P + length pre)%nat
        ∗ ps_lb v ps ∗ cs_lb v cs ∗ pledN k I pre tm ∗ inp_lb v I) ∨ T)%I.

  Global Instance pwc_blkN_timeless v I k pre tm : Timeless (pwc_blkN v I k pre tm).
  Proof using . rewrite /pwc_blkN /pledN. apply _. Qed.

  (* what a terminal byte hands its writer *)
  Definition ptkN (v : era_pins) (I : list (bv 8)) (k : nat) : iProp Σ :=
    (cs_frozen_at v (nlines I - 1)%nat ∨ T)%I.

  Global Instance ptkN_persistent v I k : Persistent (ptkN v I k).
  Proof using . rewrite /ptkN. apply _. Qed.

  (* WHAT THE CLAIM ASKS OF A BLOCK at the flag [tm]: an admitted,
     non-panicking alternative of the round's line, coverage-ending
     exactly at [tm], whose continuation the block is a prefix of, and
     '$'-free unless the round is terminal *)
  Definition pwitN (I : list (bv 8)) (tm : bool) (pre : list (bv 8)) : Prop :=
    exists a : nat,
      lm_ok PM (lineN I) (lm_dec PM a)
      /\ lm_panic PM (lm_dec PM a) = false
      /\ lm_term PM (lm_dec PM a) = tm
      /\ pre `prefix_of` lm_cont PM tt (lineN I) (lm_dec PM a)
      /\ (tm = false -> Forall nodollar pre).

  (* THE ENTRY: the lend a round's writer holds before the block's first
     byte is the credential at the empty block *)
  Lemma pwc_blkN_entry (v : era_pins) (I : list (bv 8)) (k : nat)
      (ps cs : list nat) (P : nat) :
    wr_blkN ps cs I P ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps -∗ cs_lb v cs -∗ inp_lb v I -∗
    pwc_blkN v I k [] false.
  Proof using .
    intros Hw. iIntros "#Hpin Ht #Hps #Hcs #HE". rewrite /pwc_blkN. iLeft.
    iExists ps, cs, P. iFrame "Hpin Hps Hcs HE".
    iSplitR; [by iPureIntro |]. cbn [length]. rewrite Nat.add_0_r. iFrame "Ht".
    rewrite /pledN. by iLeft.
  Qed.

  (* THE CLAIM PAYS THE FAMILY'S ONE OBLIGATION: the first byte opens the
     round, every further byte (any writer's) appends to its ledger *)
  Theorem pblkN_ecl_holds (v : era_pins) (I : list (bv 8)) :
    ⊢ eclN pecl' (pwc_blkN v I) (ptkN v I) (pwitN I).
  Proof using K.
    rewrite /eclN. iModIntro.
    iIntros (k ho H pre b tm tm' Htmt Hwit) "Hpw Hcl".
    destruct Hwit as (a & Hok & Hpan & Hterm & Hpref & Hnd).
    iDestruct "Hpw" as "[Hx | #HT]"; last first.
    { iModIntro. iSplitR; [by iApply pecl'_taint |].
      iSplitR; [rewrite /pwc_blkN; by iRight | iRight; rewrite /ptkN; by iRight]. }
    iDestruct "Hx" as (ps cs P) "(%Hw & #Hpin & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof Hw as (Hpp & Hr & Hn & HP).
    assert (Hne : I <> []) by (intros ->; rewrite nlines_nil in Hn; lia).
    iDestruct "Hled" as "[%Hnil | Hled]".
    - (* THE BLOCK'S FIRST BYTE: the round opens *)
      subst pre. cbn [app] in Hpref, Hnd |- *.
      assert (Hb0 : lm_cont PM tt (lineN I) (lm_dec PM a) !! 0%nat = Some b).
      { destruct Hpref as [z Hz]. rewrite Hz. reflexivity. }
      assert (Hfarm : (lm_term PM (lm_dec PM a) = false /\ nodollar b)
                      \/ lm_term PM (lm_dec PM a) = true).
      { destruct tm'; [by right |]. left. split; [exact Hterm |].
        exact (proj1 (Forall_singleton _ _) (Hnd eq_refl)). }
      iMod (pecl'_blkN_open_gen k v P a b ps cs I ho H Hne Hr ltac:(lia) Hpp HP
              Hok Hpan Hb0 Hfarm with "Hpin [Htn] Hps Hcs HE Hcl") as "(Hcl & Hret)".
      { cbn [length] in *. rewrite Nat.add_0_r. iExact "Htn". }
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[Hx | #HT]"; last first.
      { iSplitR; [rewrite /pwc_blkN; by iRight | iRight; rewrite /ptkN; by iRight]. }
      iDestruct "Hx" as (w gb) "(Htn & #Hpera & Hcur & #Hrlb & #Hfz & _ & _ & _)".
      rewrite Hterm.
      iSplitL "Htn Hcur".
      + rewrite /pwc_blkN. iLeft. iExists ps, cs, P. iFrame "Hpin Hps Hcs HE".
        iSplitR; [by iPureIntro |].
        rewrite (_ : (P + length [b])%nat = S P); [| cbn [length]; lia]. iFrame "Htn".
        rewrite /pledN. iRight. iExists w, gb. iFrame "Hpera Hcur Hrlb".
      + iDestruct "Hfz" as "[%Hf | #Hf]"; [by iLeft | iRight; rewrite /ptkN; by iLeft].
    - (* A FURTHER BYTE, by any writer *)
      iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
      assert (Hfarm : (lm_term PM (lm_dec PM a) = false /\ Forall nodollar pre
                       /\ nodollar b) \/ lm_term PM (lm_dec PM a) = true).
      { destruct tm'; [by right |]. left.
        pose proof (Hnd eq_refl) as Hall. apply Forall_app in Hall as [H1 H2].
        split; [exact Hterm | split; [exact H1 |]].
        exact (proj1 (Forall_singleton _ _) H2). }
      iMod (pecl'_blkN_byte_gen k v w gb tm P (nlines I - 1)%nat a b pre ps cs I ho H
              Hne Hr eq_refl ltac:(lia) Hpp HP Hok Hpan Hpref Hfarm
              with "Hpin Hpera Htn Hcur Hrlb Hps Hcs HE Hcl") as "(Hcl & Hret)".
      iModIntro. iFrame "Hcl".
      iDestruct "Hret" as "[(Htn & Hcur & #Hrlb' & #Hfz) | #HT]"; last first.
      { iSplitR; [rewrite /pwc_blkN; by iRight | iRight; rewrite /ptkN; by iRight]. }
      assert (Hor : (tm || lm_term PM (lm_dec PM a)) = tm').
      { rewrite Hterm. destruct tm, tm'; try reflexivity. discriminate (Htmt eq_refl). }
      rewrite Hor Hterm.
      iSplitL "Htn Hcur".
      + rewrite /pwc_blkN. iLeft. iExists ps, cs, P. iFrame "Hpin Hps Hcs HE".
        iSplitR; [by iPureIntro |].
        rewrite (_ : (P + length (pre ++ [b]))%nat = S (P + length pre));
          [| rewrite length_app; cbn [length]; lia].
        iFrame "Htn". rewrite /pledN. iRight. iExists w, gb. iFrame "Hpera Hcur Hrlb'".
      + iDestruct "Hfz" as "[%Hf | #Hf]"; [by iLeft | iRight; rewrite /ptkN; by iLeft].
  Qed.

  (* THE MODEL'S BLOCKS ARE THE CLAIM'S NON-TERMINAL WITNESS: the family's
     [HWIT] at the pipeline, for a well-formed admitted line *)
  Lemma pipesN_HWIT (I : list (bv 8)) :
    fc_ok fc -> adm_ok fc adm -> adm (lineN I) = true -> pl_ok (lineN I) ->
    forall pre bl, blkN (wids (lcats (lineN I))) (runN fc (lineN I)) bl ->
      pre `prefix_of` bl -> pwitN I false pre.
  Proof using .
    intros Hfc Hadm Ha Hl pre bl Hb Hp.
    exists (plalt_code (PLRun bl)).
    cbn [pipes_lm lm_ok lm_panic lm_term lm_cont lm_dec]. rewrite plalt_of_code.
    split_and!.
    - exact Ha.
    - exact (blkN_line_blocks fc _ bl Hb).
    - reflexivity.
    - reflexivity.
    - etrans; [exact Hp |]. by eexists.
    - intros _. exact (prefix_forall _ _ _ Hp (pipesN_blk_nodollar fc adm _ bl Hfc Hadm Ha Hl Hb)).
  Qed.

  (* THE FILING, at the credential: once the family has handed the block
     back ([PipeBothN.blkN_file]), the prompt's first byte files it as the
     alternative [PLRun pre] -- the landed [pblk2_ecl_file]'s twin *)
  Lemma pwc_blkN_file (v : era_pins) (I : list (bv 8)) (k : nat) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) (pre : list (bv 8)) (b : bv 8) :
    adm (lineN I) = true -> line_blocks fc (lineN I) pre -> pre <> [] ->
    b = u_prompt !!! 0%nat ->
    pwc_blkN v I k pre false -∗ pecl' k ho H ==∗
      pecl' k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((∃ (ps cs : list nat) (P : nat),
            ⌜wr_blkN ps cs I P⌝ ∗ turn v (S (P + length pre))%nat
            ∗ ps_lb v ps ∗ cs_lb v (cs ++ [plalt_code (PLRun pre)]) ∗ inp_lb v I) ∨ T).
  Proof using K.
    intros Ha Hbl Hne Hbv. iIntros "Hpw Hcl".
    iDestruct "Hpw" as "[Hx | #HT]"; last first.
    { iModIntro. iSplitR; [by iApply pecl'_taint | by iRight]. }
    iDestruct "Hx" as (ps cs P) "(%Hw & #Hpin & Htn & #Hps & #Hcs & Hled & #HE)".
    pose proof Hw as (Hpp & Hr & Hn & HP).
    assert (HneI : I <> []) by (intros ->; rewrite nlines_nil in Hn; lia).
    iDestruct "Hled" as "[%Hnil | Hled]"; [by destruct (Hne Hnil) |].
    iDestruct "Hled" as (w gb) "(#Hpera & Hcur & #Hrlb)".
    assert (Hok : lm_ok PM (lm_of PM (bodies_of I !!! (nlines I - 1)%nat))
                    (lm_dec PM (plalt_code (PLRun pre)))).
    { cbn [pipes_lm lm_ok lm_dec]. rewrite plalt_of_code. split; [exact Ha | exact Hbl]. }
    assert (Hpan : lm_panic PM (lm_dec PM (plalt_code (PLRun pre))) = false).
    { cbn [pipes_lm lm_panic lm_dec]. by rewrite plalt_of_code. }
    assert (Hterm : lm_term PM (lm_dec PM (plalt_code (PLRun pre))) = false).
    { cbn [pipes_lm lm_term lm_dec]. by rewrite plalt_of_code. }
    assert (Hcont : lm_cont PM tt (lm_of PM (bodies_of I !!! (nlines I - 1)%nat))
                      (lm_dec PM (plalt_code (PLRun pre))) = pre ++ u_prompt).
    { cbn [pipes_lm lm_cont lm_dec]. by rewrite plalt_of_code. }
    iMod (pecl'_blkN_file k v w gb P (nlines I - 1)%nat (plalt_code (PLRun pre)) b pre
            ps cs I ho H HneI Hr eq_refl ltac:(lia) Hpp HP Hok Hpan Hterm Hcont Hbv
            with "Hpin Hpera Htn Hcur Hrlb Hps Hcs HE Hcl") as "(Hcl & Hret)".
    iModIntro. iFrame "Hcl".
    iDestruct "Hret" as "[(Htn & _ & #Hcs' & _) | #HT]"; [| by iRight].
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs' HE". by iPureIntro.
  Qed.
End pipes_out_n.
