(* ===================================================================== *)
(*  GenOut.v -- THE PER-CYCLE CONSOLE CLAIM, ONCE OVER A LINE MODEL      *)
(*  (app-both M3b, second cut).                                          *)
(*                                                                       *)
(*  [EchoOut.ecl], [FileOut.fecl] and [PipeOut.pecl] are one shape:      *)
(*                                                                       *)
(*    T ∨ ∃ v so, PIN k v ∗ WA k (st so)                                 *)
(*          ∗ turn_auth v (pcount so) ∗ cs_auth v (cs so)                *)
(*          ∗ ps_auth v (ps so) ∗ Elist_auth v (E so)                    *)
(*          ∗ dl_cnt v ½ |ch_dl H| ∗ dl_list_auth v (ch_dl H)            *)
(*          ∗ ⌜gcl_pure k ho so H⌝                                       *)
(*                                                                       *)
(*  with the taint [T] and the pin [PIN] M2's [GenLinksLine.gen_params]  *)
(*  and the pure claim [GenOutHist.gcl_pure].  What the applications add *)
(*  is the STATE WITNESS'S AUTHORITY [WA k st] -- at the file, the era's *)
(*  second record, the filed-ledger authority, the claim's copy of the  *)
(*  boot witness and the deed's typed witness; [emp] where no line      *)
(*  touches the file system -- so it is the one hook here.  Its laws are *)
(*  what the steps read off it: the writer's witness [gW] agrees with    *)
(*  the stage's state ([gwa_agree]), a filed state hands [gW] out again  *)
(*  to the read and the drain ([gwa_W]), and the era's first process    *)
(*  byte files the state out of the boot evidence ([gwa_file]).          *)
(*                                                                       *)
(*  So far: the claim, the steps that take nothing (the taint's supply,  *)
(*  the close, the open, the arm), the era's head write, the ordinary    *)
(*  write and the write at a block's first byte.                         *)
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
Require Import LineModel.
Require Import LineModelLinks.
Require Import GenOutPure.
Require Import EchoOut.
Require Import GenOutHist.
Require Import GenLinksLine.     (* [gen_params]: the taint, the pin, [gW] *)
Local Open Scope nat_scope.

(* THE STATE WITNESS'S AUTHORITY, and what the steps read off it.  [sd] is
   the instance's default state ([GenOutPure.gs_state]'s): the stage reads
   it until the era's first process byte files the boot state. *)
Record gen_wa {Σ : gFunctors} `{!echoOutG Σ} (M : lmodel) (G : gen_params M)
    (sd : lm_st M) := MkGWA {
  gwa : nat -> option (lm_st M) -> iProp Σ;
  gwa_tl : forall k st, Timeless (gwa k st);
  (* the writer's witness pins the state the stage reads *)
  gwa_agree : forall k st s0,
    gwa k st -∗ gW G k s0 -∗ ⌜default sd st = s0⌝;
  (* a filed state hands the writer's witness out again *)
  gwa_W : forall k s0,
    gwa k (Some s0) -∗ gwa k (Some s0) ∗ gW G k s0;
  (* THE BOOT EVIDENCE the era's first writer holds (at the file: the era's
     second record, the boot ledger's entry, the deed's typed witness), and
     THE FILING LAW: the era's first process byte files the state out of it
     and yields the writer's witness *)
  gwa_boot : nat -> lm_st M -> iProp Σ;
  gwa_file : forall k s0,
    gwa k None -∗ gwa_boot k s0 ==∗ gwa k (Some s0) ∗ gW G k s0;
}.
Global Arguments MkGWA {Σ _ M G sd}.
Global Arguments gwa {Σ _ M G sd} _ _ _.
Global Arguments gwa_tl {Σ _ M G sd} _ _ _.
Global Arguments gwa_agree {Σ _ M G sd} _ _ _ _.
Global Arguments gwa_W {Σ _ M G sd} _ _ _.
Global Arguments gwa_boot {Σ _ M G sd} _ _ _.
Global Arguments gwa_file {Σ _ M G sd} _ _ _.
Global Existing Instance gwa_tl.

(* the reader's range condition grows by the alternative a block files
   ([FileOutPure.alts_pre_snoc] once) *)
Lemma lm_alts_pre_snoc (M : lmodel) I cs a :
  lm_alts_pre M I cs -> length cs < nlines I ->
  lm_ok M (lm_of M (bodies_of I !!! length cs)) (lm_dec M a) ->
  lm_alts_pre M I (cs ++ [a]).
Proof.
  intros H Hlt Hok i c Hc.
  destruct (decide (i < length cs)) as [Hi | Hi].
  - rewrite lookup_app_l in Hc; [| lia]. exact (H i c Hc).
  - rewrite lookup_app_r in Hc; [| lia].
    assert (Hie : i = length cs).
    { apply lookup_lt_Some in Hc. cbn [length] in Hc. lia. }
    subst i. rewrite Nat.sub_diag in Hc. cbn in Hc. injection Hc as <-.
    by split.
Qed.

Local Lemma gop_lta_prefix (cs0 cs : list nat) (i : nat) :
  cs0 `prefix_of` cs -> i < length cs0 -> cs !!! i = cs0 !!! i.
Proof.
  intros [z ->] Hi. rewrite !list_lookup_total_alt lookup_app_l; [done | lia].
Qed.

Local Lemma gop_prefix_snoc_lookup {A} (w l : list A) (b : A) :
  w `prefix_of` l -> l !! length w = Some b -> (w ++ [b]) `prefix_of` l.
Proof.
  intros [z ->] Hl. rewrite lookup_app_r in Hl; [| lia].
  rewrite Nat.sub_diag in Hl.
  destruct z as [| c z]; [discriminate |]. cbn in Hl. injection Hl as <-.
  exists z. by rewrite -app_assoc.
Qed.

Section gen_out.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (M : lmodel) (G : gen_params M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (A : gen_wa M G sd).

  Local Lemma gop_pending_at_nil ps cs s :
    lm_pending_at M ps cs s [] = pro_of ps.
  Proof using. exact (lm_pending_nil M ps cs s). Qed.

  (* AN EMPTY STAGE HAS AN EMPTY PROLOGUE RESOLUTION: nothing is written,
     so no shorter resolution may give a different prologue *)
  Local Lemma gop_empty_stage_ps (so : gstage M) :
    lm_ps_len_ok M sd so ->
    Forall (fun a => a < length pro_alts) (gs_ps M so) ->
    gs_E M so = [] -> gs_w M so = [] -> gs_ps M so = [].
  Proof using.
    intros [_ HpsB] Hpsb HEnil Hwnil.
    assert (Hopens : lm_ps_opens M so) by (left; by rewrite HEnil fmap_nil).
    assert (Hround : lm_ps_round M so = 0)
      by (rewrite /lm_ps_round HEnil fmap_nil nlines_nil; reflexivity).
    assert (Hproeq : pro_of (gs_ps M so) = []).
    { destruct (decide (pro_of (pro_from (lm_ps_round M so) [])
                        = pro_of (pro_from (lm_ps_round M so) (gs_ps M so))))
        as [Heq | Hne].
      - rewrite Hround in Heq. cbn [pro_from] in Heq.
        by rewrite -Heq pro_of_nil.
      - exfalso. pose proof (HpsB Hopens [] (prefix_nil _) Hne) as Hlt.
        rewrite Hwnil in Hlt. cbn [length] in Hlt. lia. }
    destruct (decide (gs_ps M so = [])) as [? | Hne]; [done | exfalso].
    pose proof (pro_of_pos (gs_ps M so) Hpsb Hne) as Hpp.
    rewrite Hproeq in Hpp. cbn [length] in Hpp. lia.
  Qed.

  Local Notation T := (gT G).
  Local Notation PIN := (gPIN G).
  Local Notation WA := (gwa A).

  (* ================================================================== *)
  (*  1.  THE CLAIM                                                      *)
  (* ================================================================== *)
  Definition gcl (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      : iProp Σ :=
    ( T
    ∨ ∃ (v : era_pins) (so : gstage M),
        PIN k v
        ∗ WA k (gs_st M so)
        ∗ turn_auth v (lm_pcount M (gs_ps M so) (gs_cs M so)
                         (gs_state M sd so) (gs_E M so) (gs_w M so))
        ∗ cs_auth v (gs_cs M so)
        ∗ ps_auth v (gs_ps M so)
        ∗ Elist_auth v (gs_E M so)
        ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
        ∗ dl_list_auth v (LogEntryDefs.ch_dl H)
        ∗ ⌜gcl_pure M sd k ho so H⌝)%I.

  Global Instance gcl_timeless k ho H : Timeless (gcl k ho H).
  Proof using . rewrite /gcl. apply _. Qed.

  (* ================================================================== *)
  (*  2.  THE STEPS THAT TAKE NOTHING                                    *)
  (* ================================================================== *)

  (* THE SUPPLY'S LAW: a tainted era answers any event out of its taint *)
  Lemma gcl_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    T -∗ gcl k ho H ==∗ gcl k ho (ConsLog.cons_step H ev).
  Proof using . iIntros "#HT _". iModIntro. rewrite /gcl. by iLeft. Qed.

  (* FILING THE LOG ENTRY *)
  Lemma gcl_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    gcl k ho H -∗ gcl k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev. rewrite /gcl.
    iIntros "[HT | Hc]"; [by iLeft |]. iRight.
    iDestruct "Hc" as (v so)
      "(Hpin & Hwa & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, so. iFrame "Hpin Hwa Htn Hcs Hps HE".
    rewrite ch_dl_close. iFrame "Hdl Hdll". iPureIntro.
    by apply (gcl_pure_close M sd k ho so H Hok Hev Hpure).
  Qed.

  (* OPENING ONE: the pure step records (K1) and the arm's echo, and
     refutes the drop and the receive flush *)
  Lemma gcl_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H (ConsLog.EvOpen h c cs) ->
    lm_disc_input M (ins (open_seg h)) -> obs_boots h = k ->
    lm_disc M h -> trace_shape h true ->
    gcl k ho H -∗ gcl k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using B.
    intros Hok Hev Hd Hb Hdh Hsh. rewrite /gcl.
    iIntros "[HT | Hc]"; [by iLeft |]. iRight.
    iDestruct "Hc" as (v so)
      "(Hpin & Hwa & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hpure)".
    iExists v, so. iFrame "Hpin Hwa Htn Hcs Hps HE".
    rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
    iFrame "Hdl Hdll". iPureIntro.
    by apply (gcl_pure_open M B sd k ho so H h c cs Hok Hev Hd Hb Hdh Hsh Hpure).
  Qed.

  (* what the claim says about an open arm, read back out *)
  Lemma gcl_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    gcl k ho CH -∗ gcl k ho CH ∗ (T ∨ ⌜garm_era M k ho CH⌝).
  Proof using .
    rewrite /gcl. iIntros "[#HT | Hp]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct "Hp" as (v so)
      "(#Hpin & Hwa & Htn & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iSplitL.
    - iRight. iExists v, so.
      iFrame "Hpin Hwa Htn Hcs Hps HE Hdl Hdll". by iPureIntro.
    - iRight. iPureIntro. exact (gcl_pure_arm M sd k ho so CH Hall).
  Qed.

  (* ================================================================== *)
  (*  3.  THE WRITES                                                     *)
  (* ================================================================== *)

  (* (H) THE ERA'S HEAD WRITE: nothing is written and nothing echoed, so
     the stage is empty; the first process byte files the boot state
     ([gwa_file]) and opens the prologue at the alternative [a] the
     writer chose.  [FileOut.fecl_step_write_first] once. *)
  Lemma gcl_step_write_first (k : nat) (v : era_pins) (a : nat) (b : bv 8)
      (s0 : lm_st M) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    lm_st_ok M s0 ->
    a < length pro_alts ->
    pro_alts !!! a !! 0 = Some b ->
    PIN k v -∗ turn v 0 -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (gwa_boot A k s0 ∨ T) -∗
    gcl k ho H ==∗
      gcl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v 1 ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v [] ∗ gW G k s0)
         ∨ T).
  Proof using .
    intros Hfok Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb Hbt Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hbt" as "[Hbt | #HT]"; last first.
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gPIN_agree G with "Hpin2 Hpin") as %->.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    assert (Hpb : length (lm_proc_before M (gs_ps M so) (gs_cs M so)
                            (gs_state M sd so) (snd <$> gs_E M so)) = 0
                  /\ length (gs_w M so) = 0)
      by (rewrite /lm_pcount in HP; lia).
    assert (Hwnil : gs_w M so = []) by (apply nil_length_inv; lia).
    assert (HEnil : gs_E M so = []).
    { destruct (decide (gs_E M so = [])) as [? | Hne]; [done | exfalso].
      assert (Hin : (snd <$> gs_E M so) <> []).
      { intro Hq. apply Hne. by apply fmap_nil_inv in Hq. }
      assert (Hst : 0 < nstarted (snd <$> gs_E M so)) by (by apply nstarted_pos).
      pose proof (Hpin 0 Hst) as Hlt.
      assert (Hps0 : gs_ps M so <> []).
      { intros Hq. rewrite Hq in Hlt. cbn [pro_rounds] in Hlt. lia. }
      pose proof (pro_of_pos (gs_ps M so) Hpsb Hps0) as Hpp.
      pose proof (prefix_length _ _
                    (lm_proc_before_head M (gs_ps M so) (gs_cs M so)
                       (gs_state M sd so) (snd <$> gs_E M so) Hin)) as Hle.
      rewrite gop_pending_at_nil in Hle.
      lia. }
    assert (Hf0nil : gs_st M so = None) by (apply Hf0n; by split).
    assert (Hpsnil : gs_ps M so = [])
      by exact (gop_empty_stage_ps so Hpsl Hpsb HEnil Hwnil).
    assert (Hcsnil : gs_cs M so = []).
    { apply nil_length_inv.
      destruct (lm_cs_len_ok_inv M so Hcsl) as [[_ Hq] | [Hne _]].
      - rewrite Hq HEnil fmap_nil nlines_nil. lia.
      - exfalso. apply Hne. split; [exact Hwnil |].
        by rewrite HEnil fmap_nil rest_of_nil. }
    iEval (rewrite Hf0nil) in "Hwa".
    iMod (gwa_file A k s0 with "Hwa Hbt") as "[Hwa #HW]".
    iMod (turn_update v 0
            (lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (gs_w M so))
            1 ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (ps_auth_grow v (gs_ps M so) a with "Hps") as "[Hps #Hpslb2]".
    rewrite Hpsnil. cbn [app].
    iModIntro. iSplitR "Ht".
    - rewrite /gcl. iRight.
      iExists v, (MkGS M [a] [] [] [b] (Some s0)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : lm_pcount M [a] [] (gs_state M sd (MkGS M [a] [] [] [b] (Some s0)))
                     [] [b] = 1); last first.
      { rewrite /lm_pcount fmap_nil lm_proc_before_nil. reflexivity. }
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite Hcsnil. iFrame "Hpin Hwa Hta Hcs Hps Hdl Hdll".
      rewrite HEnil. iFrame "HE".
      iPureIntro.
      apply (gcl_pure_out M sd k ho so (MkGS M [a] [] [] [b] (Some s0)) H b);
        [cbn [gs_cs]; rewrite Hcsnil; cbn [length]; lia
        | cbn [gs_E]; by rewrite HEnil | | |
        | (* (A2): an era with no input owes nothing *)
          rewrite /lm_dl_ok; cbn [gs_E gs_w]; rewrite fmap_nil lines_bytes_nil; lia
        | exact Hall0].
      + rewrite /lm_out_pure. unfold gs_state.
        cbn [gs_ps gs_cs gs_E gs_w gs_st default]. split_and!.
        * rewrite Hacc Hwnil HEnil Hpsnil !lm_D_nil. reflexivity.
        * rewrite (lm_pending_nil M [a] [] s0) pro_of_singleton.
          apply (gop_prefix_snoc_lookup [] _ b); [apply prefix_nil | exact Hhead].
        * intros j x Hx. by rewrite lookup_nil in Hx.
        * rewrite /lm_E_disc fmap_nil. split_and!; [constructor | constructor |].
          rewrite rest_of_nil. cbn [length]. rewrite /line_max. lia.
        * by apply Forall_singleton.
        * rewrite fmap_nil. intros q Hq. rewrite nstarted_nil in Hq. lia.
        * apply lm_alts_pre_nil.
        * constructor.
        * constructor.
        * cbn [length]. lia.
        * by left.
        * constructor.
        * split; [discriminate | intros [_ Hq]; discriminate].
        * exact Hfok.
      + apply lm_cs_len_ok_intro; intros Hq; [by destruct Hq |].
        rewrite fmap_nil nlines_nil. reflexivity.
      + rewrite /lm_ps_len_ok /lm_ps_round /lm_ps_opens.
        cbn [gs_ps gs_cs gs_E gs_w gs_st]. rewrite fmap_nil nlines_nil.
        cbn [lm_pro_idx]. split.
        * cbn [pro_from pro_tail]. by case_decide.
        * intros _ ps' Hp Hne. cbn [pro_from] in Hne |- *.
          assert (Hcases : ps' = [] \/ ps' = [a]).
          { destruct ps' as [| x [| y ps'']]; [by left | | ].
            - right. destruct Hp as [z Hz]. by injection Hz as -> _.
            - exfalso. pose proof (prefix_length _ _ Hp) as Hl.
              cbn [length] in Hl. lia. }
          destruct Hcases as [-> | ->]; [| by destruct (Hne eq_refl)].
          rewrite gop_pending_at_nil pro_of_nil. cbn [length]. lia.
    - iLeft. iFrame "Ht HW Hcslb Hilb". iExact "Hpslb2".
  Qed.

  (* (W) THE ORDINARY WRITE: the writer's witness pins the state the stage
     reads ([gwa_agree]), so the byte it computes from the stream is the
     byte the claim owes.  [FileOut.fecl_step_write] once. *)
  Lemma gcl_step_write (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8))
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    nlines I0 <= length cs0 ->
    lm_pro_pin M ps0 cs0 I0 ->
    lm_proc_stream M ps0 cs0 s0 I0 !! P = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    gW G k s0 -∗
    gcl k ho H ==∗
      gcl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0 ∗ gW G k s0)
         ∨ T).
  Proof using .
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (gwa_agree A with "Hwa HW") as %Hsteq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_dl_E M sd k ho so H Hall0)]. }
    assert (Hst : gs_state M sd so = s0) by exact Hsteq.
    rewrite -Hst in Hb.
    destruct (lm_write_stage_byte M ps0 (gs_ps M so) cs0 (gs_cs M so)
                (gs_state M sd so) (gs_E M so) (gs_w M so) I0 P b
                Hpsp Hpin0 Hcsp Hn HI0 HP Hb)
      as [HlenE Hnext].
    assert (Hcase : gs_w M so <> []
                    \/ rest_of (snd <$> gs_E M so) <> []
                    \/ (snd <$> gs_E M so) = []).
    { destruct (decide (gs_w M so = [])) as [Hw | Hw]; [| by left].
      destruct (decide (rest_of (snd <$> gs_E M so) = [])) as [Hm | Hm];
        [| by right; left].
      right; right.
      destruct (lm_cs_len_ok_inv M so Hcsl) as [[_ Hq] | [Hne _]]; last first.
      { exfalso. by apply Hne. }
      destruct (decide ((snd <$> gs_E M so) = [])) as [Hz | Hz]; [exact Hz |].
      exfalso.
      pose proof (prefix_length _ _ Hcsp) as Hlen0.
      pose proof (nlines_pos_of_rest_nil (snd <$> gs_E M so) Hz Hm) as Hpos.
      rewrite -HlenE in Hn. lia. }
    iMod (turn_update v P
            (lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (gs_w M so))
            (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iModIntro. iSplitR "Ht".
    - rewrite /gcl. iRight.
      iExists v,
        (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) (gs_w M so ++ [b])
           (gs_st M so)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                    (gs_w M so ++ [b]) (gs_st M so))
                   = gs_state M sd so); [| reflexivity].
      rewrite lm_pcount_write -HP.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hwa Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (gcl_pure_out M sd k ho so
               (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so) (gs_w M so ++ [b])
                  (gs_st M so)) H b);
        [cbn [gs_cs]; lia | reflexivity | | |
        | (* (A2): the writer is now inside a block *)
          apply (lm_dl_ok_out M so (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                      (gs_w M so ++ [b]) (gs_st M so)));
          [reflexivity
          | cbn [gs_w]; intro Hq; by destruct (app_eq_nil _ _ Hq) as [_ Hq2]
          | exact Hcase | exact Hdlok]
        | exact Hall0].
      + rewrite /lm_out_pure.
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so) (gs_E M so)
                                      (gs_w M so ++ [b]) (gs_st M so))
                     = gs_state M sd so); [| reflexivity].
        cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * by rewrite Hacc app_assoc.
        * by apply gop_prefix_snoc_lookup.
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
        * split; [| intros [_ Hq]; exfalso;
                    by destruct (app_eq_nil (gs_w M so) [b] Hq) as [_ Hb2]].
          (* an EMPTY stage owes nothing: its prologue resolution is empty
             ([gop_empty_stage_ps]), so there was no byte to write *)
          intros Hnone. exfalso.
          destruct (proj1 Hf0n Hnone) as [HE0 Hw0].
          pose proof (gop_empty_stage_ps so Hpsl Hpsb HE0 Hw0) as Hps0.
          rewrite /lm_pending HE0 fmap_nil gop_pending_at_nil Hps0 pro_of_nil
            lookup_nil in Hnext.
          discriminate Hnext.
        * exact Hfok0.
      + exact (lm_cs_len_ok_write M so b Hcsl Hcase).
      + exact (lm_ps_len_ok_write M sd so b Hpsl).
    - iLeft. iFrame "Ht Hpslb Hcslb Hilb HW".
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE: the alternative [a] is the
     program's knowledge and this step files it; the block is read at the
     state the writer's witness pins.  [FileOut.fecl_step_write_blk] once,
     with the model's no-coverage-ending clause as a premise (the pipe's
     terminal arm is its own step). *)
  Lemma gcl_step_write_blk (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8))
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    nlines I0 <= S (length cs0) ->
    lm_pro_pin M ps0 cs0 I0 ->
    P = length (lm_proc_before M ps0 cs0 s0 I0) ->
    lm_ok M (lm_of M (bodies_of I0 !!! (nlines I0 - 1))) (lm_dec M a) ->
    lm_term M (lm_dec M a) = false ->
    lm_cont M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1))
      (lm_of M (bodies_of I0 !!! (nlines I0 - 1))) (lm_dec M a) !! 0 = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    gW G k s0 -∗
    gcl k ho H ==∗
      gcl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
          ∗ gW G k s0) ∨ T).
  Proof using B.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hterm Hhead.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    pose proof (ll_nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (gwa_agree A with "Hwa HW") as %Hsteq.
    assert (Hst : gs_state M sd so = s0) by exact Hsteq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_dl_E M sd k ho so H Hall0)]. }
    rewrite -Hst in HPeq.
    assert (Hstream : lm_proc_before M ps0 cs0 (gs_state M sd so) I0
                      = lm_proc_before M (gs_ps M so) (gs_cs M so)
                          (gs_state M sd so) I0).
    { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so)
               (gs_state M sd so) I0 Hpsp Hcsp Hpin0). lia. }
    assert (HlenE : (snd <$> gs_E M so) = I0).
    { destruct (decide ((snd <$> gs_E M so) = I0)) as [? | Hne]; [done | exfalso].
      pose proof (lm_proc_stream_before M (gs_ps M so) (gs_cs M so)
                    (gs_state M sd so) I0 (snd <$> gs_E M so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
      apply prefix_length in Hpre.
      rewrite /lm_proc_stream length_app -Hstream in Hpre.
      pose proof (lm_pending_at_nonnil_at M (gK G) (gs_ps M so) (gs_cs M so)
                    (gs_state M sd so) I0 (snd <$> gs_E M so) HI0 Hcsb' Hne0 Hr0)
        as Hne1.
      assert (Hlen1 : 1 <= length (lm_pending_at M (gs_ps M so) (gs_cs M so)
                                     (gs_state M sd so) I0)).
      { destruct (lm_pending_at M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0);
          [done | cbn; lia]. }
      rewrite /lm_pcount in HP. lia. }
    assert (Hwnil : gs_w M so = []).
    { assert (Hz : length (gs_w M so) = 0).
      { rewrite /lm_pcount in HP. rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    destruct (lm_cs_len_ok_inv M so Hcsl) as [[_ Hq] | [Hne _]]; last first.
    { exfalso. apply Hne. split; [exact Hwnil | by rewrite HlenE]. }
    rewrite HlenE in Hq.
    assert (Hcs0 : cs0 = gs_cs M so).
    { pose proof (prefix_length _ _ Hcsp) as Hle.
      destruct Hcsp as [z Hz]. rewrite Hz.
      assert (Hzn : z = []).
      { apply nil_length_inv. rewrite Hz length_app in Hle |- *.
        rewrite Hz length_app in Hq. lia. }
      by rewrite Hzn app_nil_r. }
    assert (Hidx0 : lm_at M (gs_cs M so ++ [a]) (nlines I0 - 1) = lm_dec M a).
    { rewrite /lm_at list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hq Nat.sub_diag. reflexivity. }
    (* the block below the last line does not read the new entry, so the
       state the block starts in is the writer's own *)
    assert (Hfst : lm_upto M (gs_cs M so ++ [a]) s0 (bodies_of I0) (nlines I0 - 1)
                   = lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1)).
    { apply lm_upto_cs_ext. intros j Hj.
      rewrite Hcs0 !list_lookup_total_alt lookup_app_l; [done | lia]. }
    assert (Hpend : lm_pending M (gs_ps M so) (gs_cs M so ++ [a])
                      (gs_state M sd so) (gs_E M so) !! 0 = Some b).
    { rewrite /lm_pending HlenE /lm_pending_at.
      rewrite decide_False; [| exact Hne0]. rewrite decide_True; [| exact Hr0].
      rewrite /lm_cont_at Hidx0 Hst Hfst.
      rewrite lookup_app_l; [exact Hhead |].
      destruct (lm_cont M (lm_upto M cs0 s0 (bodies_of I0) (nlines I0 - 1))
                  (lm_of M (bodies_of I0 !!! (nlines I0 - 1))) (lm_dec M a))
        as [| z zs] eqn:Hz;
        [ exfalso; revert Hz; apply (lmh_cont_nonnil (gK G)); by left
        | cbn; lia ]. }
    assert (Hpinq : lm_pro_pin M (gs_ps M so) (gs_cs M so ++ [a])
                      (snd <$> gs_E M so)).
    { intros qq Hqq. rewrite lm_pro_idx_app_le; [by apply Hpin |].
      rewrite HlenE (nstarted_rest_nil I0 Hr0) in Hqq. rewrite Hq. lia. }
    assert (HD : lm_D M (gs_ps M so) (gs_cs M so ++ [a]) (gs_state M sd so)
                   (gs_E M so)
                 = lm_D M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                     (gs_E M so)).
    { symmetry. apply (lm_D_cs_prefix M (gs_ps M so) (gs_ps M so) (gs_cs M so)
                         (gs_cs M so ++ [a]) (gs_state M sd so) (gs_E M so));
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE Hrl0 Hq. lia. }
    assert (Hpceq : lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                      (gs_E M so) [b]
                    = lm_pcount M (gs_ps M so) (gs_cs M so ++ [a])
                        (gs_state M sd so) (gs_E M so) [b]).
    { apply (lm_pcount_cs_prefix M (gs_ps M so) (gs_ps M so) (gs_cs M so)
               (gs_cs M so ++ [a]) (gs_state M sd so) (gs_E M so) [b]);
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE Hrl0 Hq. lia. }
    assert (Hpc2 : lm_pcount M (gs_ps M so) (gs_cs M so ++ [a])
                     (gs_state M sd so) (gs_E M so) [b] = S P).
    { rewrite -Hpceq /lm_pcount HlenE -Hstream. cbn [length]. lia. }
    iMod (turn_update v P
            (lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (gs_w M so))
            (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (cs_auth_grow v (gs_cs M so) a with "Hcs") as "[Hcs #Hcslb2]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb2]".
    iModIntro. iSplitR "Ht".
    - rewrite /gcl. iRight.
      iExists v, (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so) [b]
                    (gs_st M so)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a])
                                    (gs_E M so) [b] (gs_st M so))
                   = gs_state M sd so); [| reflexivity].
      rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hwa Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (gcl_pure_out M sd k ho so
               (MkGS M (gs_ps M so) (gs_cs M so ++ [a]) (gs_E M so) [b]
                  (gs_st M so)) H b);
        [cbn [gs_cs]; rewrite length_app; cbn [length]; lia
        | reflexivity | | |
        | (* (A2) AT A BLOCK'S FIRST BYTE, paid by the writer's own bound
             on the DELIVERED input, which is the whole era's input *)
          apply (lm_dl_ok_out_full M so (MkGS M (gs_ps M so) (gs_cs M so ++ [a])
                                           (gs_E M so) [b] (gs_st M so)));
          [reflexivity | cbn [gs_w]; discriminate | by rewrite HlenE |];
          pose proof (prefix_length _ _ HI0dl) as Hlp;
          rewrite !length_fmap in Hlp; rewrite HlenE; lia
        | exact Hall0].
      + rewrite /lm_out_pure.
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so) (gs_cs M so ++ [a])
                                      (gs_E M so) [b] (gs_st M so))
                     = gs_state M sd so); [| reflexivity].
        cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * rewrite Hacc Hwnil app_nil_r HD. reflexivity.
        * apply (gop_prefix_snoc_lookup [] _ b); [apply prefix_nil |].
          by rewrite -Hpend.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpinq.
        * apply lm_alts_pre_snoc; [exact Hcsb' | rewrite HlenE Hq; lia |].
          rewrite HlenE Hq. exact Halt.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * apply Forall_app. split; [exact Hnofk | by apply Forall_singleton].
        * split; [| intros [_ Hq2]; discriminate].
          intros Hnone. exfalso. destruct (proj1 Hf0n Hnone) as [HE0 _].
          apply Hne0. by rewrite -HlenE HE0.
        * exact Hfok0.
      + apply (lm_cs_len_ok_blk M so a b);
          [by rewrite HlenE | by rewrite HlenE | exact Hwnil | exact Hcsl].
      + apply (lm_ps_len_ok_blk M B sd so a b);
          [by rewrite HlenE | by rewrite HlenE | by rewrite HlenE | exact Hpsl].
    - iLeft. rewrite Hcs0. iFrame "Ht Hilb Hcslb2 Hpslb HW".
  Qed.

  (* (W-pro) THE WRITE AT A PROLOGUE ROUND'S CHOICE BYTE: init's own
     knowledge of which alternative its restart loop is taking, filed into
     the claim.  [FileOut.fecl_step_write_pro] once.  ONE PREMISE MORE than
     the file's: [0 < P], the writer is past the era's head.  The file's
     witness forces the stage's state to be filed; the model's law only
     pins the state the stage READS, and at an empty stage the only first
     byte is the head's ([gcl_step_write_first]), which files it. *)
  Lemma gcl_step_write_pro (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
      (ps0 cs0 : list nat) (s0 : lm_st M) (I0 : list (bv 8))
      (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    0 < P ->
    rest_of I0 = [] ->
    (I0 = [] \/ lm_panic M (lm_at M cs0 (nlines I0 - 1)) = true) ->
    nlines I0 <= length cs0 ->
    lm_pro_pin M ps0 cs0 I0 ->
    ~ pro_done (pro_from (lm_pro_idx M cs0 (nlines I0)) ps0) ->
    P = length (lm_proc_stream M ps0 cs0 s0 I0) ->
    a < length pro_alts ->
    pro_alts !!! a !! 0 = Some b ->
    PIN k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    gW G k s0 -∗
    gcl k ho CH ==∗
      gcl k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
          ∗ gW G k s0) ∨ T).
  Proof using .
    intros HP0 Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb #HW Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /gcl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 so)
      "(#Hpin2 & Hwa & Hta & Hcs & Hps & HE & Hdl & Hdll & %Hall)".
    iDestruct (gPIN_agree G with "Hpin2 Hpin") as %->.
    iDestruct (gwa_agree A with "Hwa HW") as %Hsteq.
    assert (Hst : gs_state M sd so = s0) by exact Hsteq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _ & Hdlok).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpinf & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hnofk & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "Hdll Hilb") as %HI0dl.
    assert (HI0 : I0 `prefix_of` (snd <$> gs_E M so)).
    { etrans; [exact HI0dl | exact (gcl_pure_dl_E M sd k ho so CH Hall0)]. }
    rewrite -Hst in HPeq.
    pose proof (ll_nlines_removelast I0 Hr0) as Hrl0.
    (* the writer's own list is bounded, and its round index is the claim's *)
    assert (Hpsb0 : Forall (fun x => x < length pro_alts) ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2. by apply Forall_app in Hpsb2 as [? _]. }
    assert (Hlk : forall j, j < nlines I0 -> gs_cs M so !!! j = cs0 !!! j)
      by (intros j Hj; apply (gop_lta_prefix cs0 (gs_cs M so) j Hcsp); lia).
    assert (Hidxeq : lm_pro_idx M (gs_cs M so) (nlines I0)
                     = lm_pro_idx M cs0 (nlines I0))
      by exact (lm_pro_idx_ext M (gs_cs M so) cs0 (nlines I0) Hlk (nlines I0)
                  ltac:(lia)).
    rewrite -Hidxeq in Hnd.
    assert (HopenC : I0 = [] \/
              lm_panic M (lm_at M (gs_cs M so) (nlines I0 - 1)) = true).
    { destruct (decide (I0 = [])) as [Hz | Hne0]; [by left | right].
      pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
      destruct Hopen as [Hz | H3]; [by destruct (Hne0 Hz) |].
      rewrite /lm_at (Hlk (nlines I0 - 1) ltac:(lia)). exact H3. }
    assert (Hstream : lm_proc_before M ps0 cs0 (gs_state M sd so) I0
                      = lm_proc_before M (gs_ps M so) (gs_cs M so)
                          (gs_state M sd so) I0).
    { apply (lm_proc_before_cs_prefix M ps0 (gs_ps M so) cs0 (gs_cs M so)
               (gs_state M sd so) I0 Hpsp Hcsp Hpin0). lia. }
    assert (Hpend0 : lm_pending_at M ps0 cs0 (gs_state M sd so) I0
                     = lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0)
      by exact (lm_pending_at_cs_ext M ps0 cs0 (gs_cs M so) (gs_state M sd so)
                  I0 Hcsp Hdiv).
    assert (Hpmono : lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0
                     `prefix_of` lm_pending_at M (gs_ps M so) (gs_cs M so)
                                   (gs_state M sd so) I0)
      by (by apply lm_pending_at_ps_mono).
    assert (HPval : P = length (lm_proc_before M ps0 cs0 (gs_state M sd so) I0)
                        + length (lm_pending_at M ps0 cs0 (gs_state M sd so) I0)).
    { rewrite HPeq /lm_proc_stream.
      by rewrite (length_app (lm_proc_before M ps0 cs0 (gs_state M sd so) I0)
                    (lm_pending_at M ps0 cs0 (gs_state M sd so) I0)). }
    rewrite /lm_pcount in HP.
    (* the era's input IS [I0] *)
    assert (HlenE : (snd <$> gs_E M so) = I0).
    { destruct (decide ((snd <$> gs_E M so) = I0)) as [? | Hne]; [done | exfalso].
      assert (Hnei : I0 <> (snd <$> gs_E M so))
        by (intros Hq; apply Hne; symmetry; exact Hq).
      pose proof (lm_proc_stream_before M (gs_ps M so) (gs_cs M so)
                    (gs_state M sd so) I0 (snd <$> gs_E M so) HI0 Hnei) as Hpre.
      apply prefix_length in Hpre.
      rewrite /lm_proc_stream length_app -Hstream in Hpre.
      pose proof (prefix_length _ _ Hpmono) as Hlp. rewrite -Hpend0 in Hlp.
      assert (Hpe : lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0
                    = lm_pending_at M (gs_ps M so) (gs_cs M so)
                        (gs_state M sd so) I0).
      { apply prefix_length_eq; [exact Hpmono | rewrite -Hpend0; lia]. }
      pose proof (lm_pending_at_round_det M (gL G) ps0 (gs_ps M so) (gs_cs M so)
                    (gs_state M sd so) I0 Hr0 HopenC Hpe) as Hpro.
      assert (Hdone : pro_done (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                        (gs_ps M so))).
      { apply pro_from_done.
        apply Hpinf.
        exact (nstarted_strict I0 (snd <$> gs_E M so) HI0 Hnei). }
      apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) ps0)
                  (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hpro; reflexivity)) as [Hd _].
      exact Hd. }
    assert (Hlenw : length (gs_w M so)
                    = length (lm_pending_at M ps0 cs0 (gs_state M sd so) I0)).
    { rewrite HlenE -Hstream in HP. lia. }
    assert (Hweq : gs_w M so = lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0).
    { assert (Hw1 : gs_w M so
                    `prefix_of` lm_pending_at M (gs_ps M so) (gs_cs M so)
                                  (gs_state M sd so) I0)
        by (rewrite -HlenE; exact Hwpre).
      assert (Hlen2 : length (gs_w M so)
                      = length (lm_pending_at M ps0 (gs_cs M so)
                                  (gs_state M sd so) I0))
        by (rewrite -Hpend0; exact Hlenw).
      destruct (prefix_weak_total (gs_w M so)
                  (lm_pending_at M ps0 (gs_cs M so) (gs_state M sd so) I0)
                  (lm_pending_at M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0)
                  Hw1 Hpmono) as [Hq | Hq].
      - apply prefix_length_eq; [exact Hq | lia].
      - symmetry. apply prefix_length_eq; [exact Hq | lia]. }
    assert (Hopens : lm_ps_opens M so).
    { rewrite /lm_ps_opens HlenE.
      destruct HopenC as [Hz | H3]; [by left | right; by split]. }
    pose proof Hpsl as [HpsA HpsB].
    assert (Hproeq : pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) ps0)
                     = pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                         (gs_ps M so))).
    { destruct (decide (pro_of (pro_from
                          (lm_pro_idx M (gs_cs M so) (nlines I0)) ps0)
                        = pro_of (pro_from
                            (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))))
        as [Heq | Hne]; [exact Heq | exfalso].
      pose proof (HpsB Hopens ps0 Hpsp) as Hlt.
      rewrite /lm_ps_round HlenE in Hlt.
      pose proof (Hlt Hne) as Hlt2. rewrite Hweq in Hlt2. lia. }
    assert (Hndps : ~ pro_done (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                      (gs_ps M so))).
    { intros Hdone. apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) ps0)
                  (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hproeq; reflexivity)) as [Hd _].
      exact Hd. }
    assert (Hround0 : lm_pro_idx M (gs_cs M so) (nlines I0) <= pro_rounds ps0).
    { rewrite Hidxeq.
      by apply (lm_pro_pin_round_le M ps0 cs0 I0 Hr0 Hopen Hpin0). }
    assert (Hpseq : gs_ps M so = ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2.
      assert (Hzb : Forall (fun x => x < length pro_alts) z)
        by (by apply Forall_app in Hpsb2 as [_ ?]).
      pose proof Hproeq as Hpe2. rewrite Hz in Hpe2.
      rewrite (pro_from_app_le _ ps0 z Hround0) in Hpe2.
      assert (Hzn : z = []).
      { apply (pro_of_open_app_inj _ z Hnd Hzb). by rewrite -Hpe2. }
      rewrite Hz Hzn. by rewrite app_nil_r. }
    assert (HRle : lm_pro_idx M (gs_cs M so) (nlines I0) <= pro_rounds (gs_ps M so))
      by (rewrite Hpseq; exact Hround0).
    assert (Hshape2 : lm_pending_at M (gs_ps M so ++ [a]) (gs_cs M so)
                        (gs_state M sd so) I0
                      = lm_wr_pre I0
                        ++ pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                             (gs_ps M so ++ [a])))
      by (apply (lm_pending_at_round_pre M (gL G)); [exact Hr0 | exact HopenC]).
    assert (Hshape : lm_pending_at M (gs_ps M so) (gs_cs M so) (gs_state M sd so) I0
                     = lm_wr_pre I0
                       ++ pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                            (gs_ps M so)))
      by (apply (lm_pending_at_round_pre M (gL G)); [exact Hr0 | exact HopenC]).
    assert (Hpendb : lm_pending_at M (gs_ps M so ++ [a]) (gs_cs M so)
                       (gs_state M sd so) I0 !! length (gs_w M so) = Some b).
    { pose proof (pro_of_snoc_head
                    (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))
                    a b Hndps Hhead) as Hph.
      assert (Hpre3' :
        (lm_wr_pre I0
         ++ (pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))
             ++ [b]))
        `prefix_of` lm_pending_at M (gs_ps M so ++ [a]) (gs_cs M so)
                      (gs_state M sd so) I0).
      { rewrite Hshape2 (pro_from_snoc_le _ (gs_ps M so) a HRle).
        by apply prefix_app. }
      assert (Hwl : length (gs_w M so)
                    = length (lm_wr_pre I0)
                      + length (pro_of (pro_from
                          (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so)))).
      { rewrite Hweq -Hpseq Hshape.
        by rewrite (length_app (lm_wr_pre I0)
                      (pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                         (gs_ps M so)))). }
      rewrite Hwl. eapply prefix_lookup_Some; [| exact Hpre3'].
      rewrite (lookup_app_shift (lm_wr_pre I0)).
      replace (length (pro_of (pro_from
                 (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))))
        with (length (pro_of (pro_from
                 (lm_pro_idx M (gs_cs M so) (nlines I0)) (gs_ps M so))) + 0)
        by lia.
      by rewrite (lookup_app_shift
                    (pro_of (pro_from (lm_pro_idx M (gs_cs M so) (nlines I0))
                       (gs_ps M so)))). }
    assert (Hcase : gs_w M so <> []
                    \/ rest_of (snd <$> gs_E M so) <> []
                    \/ (snd <$> gs_E M so) = []).
    { destruct (decide (I0 = [])) as [Hz | Hnz].
      { right; right. by rewrite HlenE. }
      left. rewrite Hweq -Hpseq.
      exact (lm_pending_at_nonnil_at M (gK G) (gs_ps M so) (gs_cs M so)
               (gs_state M sd so) I0 (snd <$> gs_E M so) HI0 Hcsb' Hnz Hr0). }
    assert (HD : lm_D M (gs_ps M so ++ [a]) (gs_cs M so) (gs_state M sd so)
                   (gs_E M so)
                 = lm_D M (gs_ps M so) (gs_cs M so) (gs_state M sd so) (gs_E M so)).
    { symmetry. apply (lm_D_ps_ext M (gs_ps M so) (gs_ps M so ++ [a]) (gs_cs M so)
                         (gs_state M sd so) (gs_E M so)); [by eexists | exact Hpinf]. }
    assert (Hpceq : lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
                      (gs_E M so) (gs_w M so ++ [b])
                    = lm_pcount M (gs_ps M so ++ [a]) (gs_cs M so)
                        (gs_state M sd so) (gs_E M so) (gs_w M so ++ [b])).
    { apply (lm_pcount_cs_prefix M (gs_ps M so) (gs_ps M so ++ [a]) (gs_cs M so)
               (gs_cs M so) (gs_state M sd so) (gs_E M so) (gs_w M so ++ [b]));
        [by eexists | reflexivity | exact Hpinf |].
      pose proof (prefix_length _ _ Hcsp) as Hle2.
      rewrite HlenE Hrl0. lia. }
    assert (Hpc2 : lm_pcount M (gs_ps M so ++ [a]) (gs_cs M so) (gs_state M sd so)
                     (gs_E M so) (gs_w M so ++ [b]) = S P).
    { rewrite -Hpceq /lm_pcount (length_app (gs_w M so) [b]). cbn [length]. lia. }
    (* the stage is not empty: an empty one has an empty prologue, so the
       cursor would be at zero -- and the writer is past the head *)
    assert (Hst_some : gs_st M so <> None).
    { intros Hnone. destruct (proj1 Hf0n Hnone) as [HE0 Hw0].
      pose proof (gop_empty_stage_ps so Hpsl Hpsb HE0 Hw0) as Hps0.
      rewrite HE0 Hw0 Hps0 fmap_nil lm_proc_before_nil in HP.
      cbn [length] in HP. lia. }
    iMod (turn_update v P
            (lm_pcount M (gs_ps M so) (gs_cs M so) (gs_state M sd so)
               (gs_E M so) (gs_w M so))
            (S P) ltac:(rewrite /lm_pcount; lia) with "Ht Hta") as "[Ht Hta]".
    iMod (ps_auth_grow v (gs_ps M so) a with "Hps") as "[Hps #Hpslb2]".
    iModIntro. iSplitR "Ht".
    - rewrite /gcl. iRight.
      iExists v, (MkGS M (gs_ps M so ++ [a]) (gs_cs M so) (gs_E M so)
                    (gs_w M so ++ [b]) (gs_st M so)).
      cbn [gs_ps gs_cs gs_E gs_w gs_st].
      rewrite (_ : gs_state M sd (MkGS M (gs_ps M so ++ [a]) (gs_cs M so)
                                    (gs_E M so) (gs_w M so ++ [b]) (gs_st M so))
                   = gs_state M sd so); [| reflexivity].
      rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hwa Hta Hcs Hps HE Hdl Hdll". iPureIntro.
      apply (gcl_pure_out M sd k ho so
               (MkGS M (gs_ps M so ++ [a]) (gs_cs M so) (gs_E M so)
                  (gs_w M so ++ [b]) (gs_st M so)) CH b);
        [cbn [gs_cs]; lia | reflexivity | | |
        | (* (A2): the writer is now inside the block's prologue round *)
          apply (lm_dl_ok_out M so (MkGS M (gs_ps M so ++ [a]) (gs_cs M so)
                                      (gs_E M so) (gs_w M so ++ [b]) (gs_st M so)));
          [reflexivity
          | cbn [gs_w]; intro Hq; by destruct (app_eq_nil _ _ Hq) as [_ Hq2]
          | exact Hcase | exact Hdlok]
        | exact Hall0].
      + rewrite /lm_out_pure.
        rewrite (_ : gs_state M sd (MkGS M (gs_ps M so ++ [a]) (gs_cs M so)
                                      (gs_E M so) (gs_w M so ++ [b]) (gs_st M so))
                     = gs_state M sd so); [| reflexivity].
        cbn [gs_ps gs_cs gs_E gs_w gs_st]. split_and!.
        * rewrite Hacc HD. by rewrite app_assoc.
        * apply gop_prefix_snoc_lookup.
          { etrans; [exact Hwpre |]. rewrite /lm_pending.
            by apply lm_pending_at_ps_mono; eexists. }
          { rewrite /lm_pending HlenE. exact Hpendb. }
        * exact Hidx.
        * exact Hbyte.
        * rewrite Forall_app.
          split; [exact Hpsb | by rewrite Forall_singleton].
        * apply (lm_pro_pin_mono M (gs_ps M so) (gs_ps M so ++ [a]));
            [by eexists | exact Hpinf].
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * exact Hnofk.
        * split; [intro Hq; by destruct (Hst_some Hq) |].
          intros [_ Hq]. exfalso.
          by destruct (app_eq_nil (gs_w M so) [b] Hq) as [_ Hb2].
        * exact Hfok0.
      + apply (lm_cs_len_ok_write M
                 (MkGS M (gs_ps M so ++ [a]) (gs_cs M so) (gs_E M so) (gs_w M so)
                    (gs_st M so)) b); [exact Hcsl | exact Hcase].
      + apply (lm_ps_len_ok_pro M sd so a b);
          [ rewrite /lm_ps_round HlenE; exact HRle
          | rewrite /lm_ps_round HlenE; exact Hndps
          | rewrite /lm_pending HlenE Hweq; by rewrite -Hpseq
          | exact (conj HpsA HpsB) ].
    - iLeft. rewrite -Hpseq. iFrame "Ht Hpslb2 Hcslb Hilb HW".
  Qed.
End gen_out.
