(* FileOut.v -- THE FILE APPLICATION'S CONSOLE CLAIM, ITS TAG AND ITS LEDGER.

   Design of record: claude-notes/design/app-file.md section 4, deliverable
   2.  This is [EchoOut.v]'s twin at [FileDisc.sessf]: the same merged
   console claim over one [ConsLog.cons_hist], the same per-era authorities,
   the same ledger shape -- with the ERA'S BOOT FILE STATE added.  The echo
   files are NOT edited: every piece of ghost algebra this file needs
   ([EchoOut.era_pins], [turn], [cs_auth], [ps_auth], [Elist_auth],
   [dl_cnt], [ch_E] and its laws) is IMPORTED, and only what the file state
   adds is new.

   WHAT THE FILE ADDS, and where it lives.

   - ONE VALUE PER ERA.  [FileOutPure.fostage] is [EchoOut.ostage] with
     [fo_f0 : option fst]: [None] until the era's first process byte files
     it, [Some s0] from then on.  [feout_pure]'s two extra clauses are that
     [None] only ever occurs at the empty stage and that the state is a
     CONTENT ([FileDisc.fst_ok]) -- the second is what the determinacy
     argument spends.
   - A SECOND PER-ERA RECORD.  [EchoOut.era_pins] is not edited, so the
     boot state's [mono_list] gets its own gname in a record of its own
     ([file_era]) and its own per-era map, which the file ledger allocates
     beside [EchoOut]'s at power-on.  That map's authority needs a gname in
     the application's FIXED PART, and [AppFile.file_fixed] has none to
     spare -- so the RECORD's fixed part is [file_gn], AppFile's paired with
     that one gname.  Nothing in [AppFile.v] moves: every one of its lemmas
     is read at [fgn_cl g].
   - THE TYPED WITNESS.  The claim carries, beside the boot state, the deed's
     own evidence for it ([f0_typed]: a lower bound of the ledger's line list
     and the pure fact that the state is a chunk subset of one of its lines,
     or the taint).  The ledger's drain reads it against its own [fl_auth]
     and that is how [FileDisc.fadm_boot] is discharged.

   THE ONE THING THIS FILE TAKES AS A HYPOTHESIS AND CANNOT PROVE:
   [Decision (FileDisc.disc_f h)].  See the note above [Section file_led].
   Everything else is closed. *)
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
Require Import FileDisc.
Require Import FileOutPure.
Require Import EchoOut.          (* the ghost algebra, [ch_E] and its laws *)
Require Import AppEcho.          (* [echo_fixed] *)
Require Import AppFile.          (* [file_fixed], [fl_auth], [f_bytes_typed] *)
Local Open Scope list_scope.

(* [FileState.fst] shadows the pair projection, so nothing below writes
   [x.1]. *)
Local Notation ehist := (@Datatypes.fst (list mobs) (bv 8)).

(* ====================================================================== *)
(*  1.  THE PURE HISTORY LAYER                                             *)
(*                                                                        *)
(*  [EchoOut]'s [ein_pure], [rd_stage], [ch_arm_era] and [ecl_pure] at the *)
(*  FILE discipline.  [ch_E] itself is reused verbatim: it is about the    *)
(*  console log and knows nothing of any discipline.                       *)
(* ====================================================================== *)

Definition fein_pure (k : nat) (pops : list log_entry)
    (dl : list (list mobs * bv 8)) (cs0 : list nat) : Prop :=
  log_ok pops
  /\ (forall e, e ∈ pops -> disc_seg_f (open_seg (le_hist e)))
  /\ (forall e, e ∈ pops -> obs_boots (le_hist e) = k)
  /\ dl `prefix_of` echoed pops
  /\ E_index (seg_of (echoed pops))
  /\ E_disc_f (seg_of (echoed pops))
  /\ (nlines (snd <$> echoed pops) <= S (length cs0))%nat.

Lemma fein_pure_0 k : fein_pure k [] [] [].
Proof using.
  rewrite /fein_pure. split_and!.
  - exact log_ok_nil.
  - intros e He. by apply elem_of_nil in He.
  - intros e He. by apply elem_of_nil in He.
  - apply prefix_nil.
  - intros j x Hx. rewrite /seg_of echoed_nil fmap_nil in Hx.
    by rewrite lookup_nil in Hx.
  - rewrite /E_disc_f /seg_of echoed_nil !fmap_nil. exact disc_input_f_nil.
  - rewrite echoed_nil fmap_nil nlines_nil. cbn [length]. lia.
Qed.

(* WHAT THE CLAIM KNOWS OF THE WRITER'S STAGE at the input its log has
   echoed.  [EchoOut.rd_stage] with [alts_pre] where [Forall (< 4) cs0] was
   -- so, unlike the echo one, it NAMES the input: the range condition ties
   each entry to the line at its index. *)
Definition rd_stage_f (ps0 cs0 : list nat) (I : list (bv 8)) : Prop :=
  Forall (fun a => (a < length pro_alts)%nat) ps0
  /\ alts_pre I cs0
  /\ pro_pin_f ps0 cs0 I
  /\ (nlines (removelast I) <= length cs0)%nat.

Lemma rd_stage_f_0 : rd_stage_f [] [] [].
Proof using.
  rewrite /rd_stage_f. split_and!.
  - constructor.
  - apply alts_pre_nil.
  - intros q Hq. rewrite nstarted_nil in Hq. lia.
  - cbn [removelast]. rewrite nlines_nil. cbn [length]. lia.
Qed.

(* WHAT THE CLAIM REMEMBERS ABOUT AN OPEN ARM.  [EchoOut.ch_arm_era] with
   the FILE discipline in the third clause. *)
Definition ch_arm_era_f (k : nat) (ho : list mobs)
    (a : option LogEntryDefs.cons_arm) : Prop :=
  match a with
  | Some (h, c, cs, j) =>
      disc_seg_f (open_seg h) /\ obs_boots h = k
      /\ disc_f h /\ trace_shape h true
      /\ h = ho
  | None => True
  end.

Definition fecl_pure (k : nat) (ho : list mobs) (so : fostage)
    (H : LogEntryDefs.cons_hist) : Prop :=
  feout_pure k ho so (LogEntryDefs.ch_acc H)
  /\ cs_len_ok_f so
  /\ ps_len_ok_f so
  /\ fein_pure k (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H) (fo_cs so)
  /\ ch_arm_era_f k ho (LogEntryDefs.ch_arm H)
  /\ fo_E so = ch_E H.

Lemma fecl_pure_arm (k : nat) (ho : list mobs) (so : fostage)
    (H : LogEntryDefs.cons_hist) :
  fecl_pure k ho so H -> ch_arm_era_f k ho (LogEntryDefs.ch_arm H).
Proof using. by intros (_ & _ & _ & _ & Hera & _). Qed.

Lemma fecl_pure_E (k : nat) (ho : list mobs) (so : fostage)
    (H : LogEntryDefs.cons_hist) :
  fecl_pure k ho so H -> fo_E so = ch_E H.
Proof using. by intros (_ & _ & _ & _ & _ & HE). Qed.

Lemma fecl_pure_rd_stage (k : nat) (ho : list mobs) (so : fostage)
    (H : LogEntryDefs.cons_hist) :
  fecl_pure k ho so H ->
  rd_stage_f (fo_ps so) (fo_cs so) (snd <$> fo_E so).
Proof using.
  intros (Hout & Hcsl & _ & _ & _ & _).
  destruct Hout as (_ & _ & _ & _ & Hpsb & Hpin & Hcsb & _).
  rewrite /rd_stage_f. split_and!;
    [exact Hpsb | exact Hcsb | exact Hpin |].
  rewrite Hcsl. case_decide as Hd.
  - destruct Hd as [_ Hr]. rewrite (fop_nlines_removelast _ Hr). lia.
  - apply nlines_prefix, fop_removelast_prefix.
Qed.

(* ---- the five event steps of the pure part ---- *)

Lemma fecl_pure_close (k : nat) (ho : list mobs) (so : fostage)
    (H : LogEntryDefs.cons_hist) :
  ConsLog.cons_hist_ok H ->
  ConsLog.cons_ev_ok H ConsLog.EvClose ->
  fecl_pure k ho so H ->
  fecl_pure k ho so (ConsLog.cons_step H ConsLog.EvClose).
Proof using.
  intros Hok Hev Hecl.
  pose proof (ch_E_close H) as Hclose.
  pose proof (ch_E_close_len H) as Hlen.
  pose proof (ConsLog.cons_hist_ok_step H ConsLog.EvClose Hok Hev) as Hok'.
  unfold ConsLog.cons_hist_ok in Hok'. destruct Hok' as [Hlog' _].
  destruct (LogEntryDefs.ch_arm H) as [[[[h c] cs] j] |] eqn:Ha; cycle 1.
  { rewrite /ConsLog.cons_step Ha. exact Hecl. }
  destruct Hecl as (Hout & Hcs & Hps & Hin & Hera & HE).
  destruct Hin as (_ & Hdsc & Hbts & Hdl & _ & _ & _).
  rewrite Ha in Hera. cbn [ch_arm_era_f] in Hera.
  destruct Hera as (Hdseg & Hboots & _ & _ & _).
  destruct Hout as (Hacc & Hw & HEi & HEb & Hpsf & Hpin & Hcsf & Hdse & Hpre
                    & Hle & Hbo & Hf0 & Hfok).
  rewrite /ConsLog.cons_step Ha in Hlog', Hlen |- *.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm] in Hlog', Hlen |- *.
  assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H ++ [(h, c, take j cs)]))
                 = fo_E so).
  { rewrite HE -Hclose /ch_E /ConsLog.cons_step Ha.
    cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
    by rewrite app_nil_r. }
  split_and!.
  - by split_and!.
  - exact Hcs.
  - exact Hps.
  - split_and!.
    + exact Hlog'.
    + intros e He. apply elem_of_app in He as [He | He].
      * exact (Hdsc e He).
      * apply elem_of_list_singleton in He as ->.
        cbn [le_hist Datatypes.fst snd]. exact Hdseg.
    + intros e He. apply elem_of_app in He as [He | He].
      * exact (Hbts e He).
      * apply elem_of_list_singleton in He as ->.
        cbn [le_hist Datatypes.fst snd]. exact Hboots.
    + destruct (decide (log_echoed (h, c, take j cs))) as [Hy | Hn].
      * rewrite (echoed_snoc_yes _ _ Hy).
        by apply (prefix_app_r _ _ [(le_hist (h, c, take j cs),
                                     le_byte (h, c, take j cs))]).
      * by rewrite (echoed_snoc_no _ _ Hn).
    + by rewrite Hseg.
    + by rewrite Hseg.
    + rewrite -(seg_of_snd (echoed _)) Hseg.
      rewrite /cs_len_ok_f in Hcs.
      destruct (decide (fo_w so = [] /\ rest_of (snd <$> fo_E so) = [])); lia.
  - exact I.
  - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
    rewrite app_nil_r. by rewrite Hseg.
Qed.

Lemma fecl_pure_out (k : nat) (ho : list mobs) (so so' : fostage)
    (H : LogEntryDefs.cons_hist) (b : bv 8) :
  (length (fo_cs so) <= length (fo_cs so'))%nat -> fo_E so' = fo_E so ->
  feout_pure k ho so' (LogEntryDefs.ch_acc H ++ [b]) ->
  cs_len_ok_f so' -> ps_len_ok_f so' ->
  fecl_pure k ho so H ->
  fecl_pure k ho so' (ConsLog.cons_step H (ConsLog.EvOut b)).
Proof using.
  intros Hcs' HE' Hout Hc Hp (_ & _ & _ & Hin & Hera & HE).
  destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt).
  rewrite /fecl_pure /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera |].
  - split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                | exact HEi | exact HEb | lia].
  - by rewrite HE' HE /ch_E.
Qed.

Lemma fecl_pure_read (k : nat) (ho : list mobs) (so : fostage)
    (H : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
  (LogEntryDefs.ch_dl H ++ ws) `prefix_of` echoed (LogEntryDefs.ch_log H) ->
  fecl_pure k ho so H ->
  fecl_pure k ho so (ConsLog.cons_step H (ConsLog.EvRead ws)).
Proof using.
  intros Hpre (Hout & Hc & Hp & Hin & Hera & HE).
  destruct Hin as (Hlog & Hdsc & Hbts & _ & HEi & HEb & Hcnt).
  rewrite /fecl_pure /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hc | exact Hp | | exact Hera
              | by rewrite HE /ch_E].
  by split_and!.
Qed.

(* MOVING THE WITNESS, [EchoOut.eout_pure_move]'s twin. *)
Lemma feout_pure_move (k : nat) (ho h : list mobs) (so : fostage)
    (acc : list (bv 8)) (L : list log_entry)
    (dl : list (list mobs * bv 8)) :
  trace_shape h true ->
  obs_boots h = k ->
  (forall e, e ∈ L -> hist_ext (le_hist e) h) ->
  fein_pure k L dl (fo_cs so) ->
  seg_of (echoed L) = fo_E so ->
  (length (fo_E so) <= length (ins (open_seg h)))%nat ->
  feout_pure k ho so acc -> feout_pure k h so acc.
Proof using.
  intros Hsh Hk Hord Hin Hseg Hle
    (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb & Hdsc & _ & _ & _
     & Hf0 & Hfok).
  destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi).
  split_and!; [exact Hacc | exact Hwpre | exact Hidx | exact Hbyte
              | exact Hpsb | exact Hpin | exact Hcsb | exact Hdsc
              | | exact Hle | | exact Hf0 | exact Hfok].
  - rewrite -Hseg. apply Forall_lookup_2. intros j x Hx.
    rewrite /seg_of list_lookup_fmap in Hx.
    destruct (echoed L !! j) as [y |] eqn:Hy; [| discriminate].
    cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [Datatypes.fst].
    assert (Hyin : y ∈ echoed L) by (by eapply elem_of_list_lookup_2).
    destruct (echoed_elem_inv L y Hyin) as (e & He & _ & Hye).
    apply open_seg_prefix_boots.
    + rewrite -Hye. cbn [Datatypes.fst]. by destruct (Hord e He) as [Hpre _].
    + rewrite -Hye. cbn [Datatypes.fst]. rewrite (Hstamp e He). by rewrite Hk.
    + exact Hsh.
  - right. exact Hk.
Qed.

Lemma fecl_pure_open (k : nat) (ho : list mobs) (so : fostage)
    (H : LogEntryDefs.cons_hist) (h : list mobs) (c : bv 8)
    (cs : list (bv 8)) :
  LogEntryDefs.ch_arm H = None ->
  disc_seg_f (open_seg h) -> obs_boots h = k ->
  disc_f h -> trace_shape h true -> obs_ends_in Uart0 h c ->
  (forall e, e ∈ LogEntryDefs.ch_log H -> hist_ext (le_hist e) h) ->
  (length (echoed (LogEntryDefs.ch_log H)) < length (ins (open_seg h)))%nat ->
  fecl_pure k ho so H ->
  fecl_pure k h so (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
Proof using.
  intros Hn Hd Hb Hdh Hsh Hends Hord Hlt (Hout & Hc & Hp & Hin & _ & HE).
  pose proof (ch_E_open H h c cs Hn) as Hopen.
  assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log H)) = fo_E so).
  { rewrite HE /ch_E Hn. cbn [ch_arm_E]. by rewrite app_nil_r. }
  assert (Hle : (length (fo_E so) <= length (ins (open_seg h)))%nat).
  { rewrite -Hseg seg_of_length. lia. }
  rewrite /fecl_pure /ConsLog.cons_step.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!;
    [ exact (feout_pure_move k ho h so (LogEntryDefs.ch_acc H)
               (LogEntryDefs.ch_log H) (LogEntryDefs.ch_dl H)
               Hsh Hb Hord Hin Hseg Hle Hout)
    | exact Hc | exact Hp | exact Hin | | ].
  - cbn [ch_arm_era_f]. by split_and!.
  - rewrite HE -Hopen /ConsLog.cons_step /ch_E.
    by cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
Qed.

Lemma fecl_pure_byte (k : nat) (ho ho' : list mobs) (so so' : fostage)
    (H : LogEntryDefs.cons_hist) (b : bv 8) (h : list mobs) (c : bv 8) :
  LogEntryDefs.ch_arm H = Some (h, c, [echo_of c], 0%nat) ->
  ho' = h ->
  (length (fo_cs so) <= length (fo_cs so'))%nat ->
  fo_E so' = fo_E so ++ [(open_seg h, c)] ->
  feout_pure k ho' so' (LogEntryDefs.ch_acc H ++ [b]) ->
  cs_len_ok_f so' -> ps_len_ok_f so' ->
  fecl_pure k ho so H ->
  fecl_pure k ho' so' (ConsLog.cons_step H (ConsLog.EvByte b)).
Proof using.
  intros Ha Hw Hcs' HE' Hout Hc Hp (_ & _ & _ & Hin & Hera & HE).
  destruct Hin as (Hlog & Hdsc & Hbts & Hdl & HEi & HEb & Hcnt).
  pose proof (ch_E_byte_echo H b h c Ha) as Hgrow.
  rewrite /fecl_pure /ConsLog.cons_step Ha.
  cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
       LogEntryDefs.ch_arm].
  split_and!; [exact Hout | exact Hc | exact Hp
              | split_and!; [exact Hlog | exact Hdsc | exact Hbts | exact Hdl
                            | exact HEi | exact HEb | lia] | | ].
  - rewrite Ha in Hera. cbn [ch_arm_era_f] in Hera |- *.
    destruct Hera as (Hds & Hb & Hd & Hshh & _). by split_and!.
  - rewrite HE' HE -Hgrow /ConsLog.cons_step Ha.
    by cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm].
Qed.

(* AN OUTPUT CLAIM AT [acc = []] STANDS AT THE START OF ITS ERA. *)
Lemma feout_pure_nil_stage (k : nat) (ho : list mobs) (so : fostage) :
  feout_pure k ho so [] ->
  pcount_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so) (fo_w so) = 0%nat.
Proof using.
  intros (Hacc & _).
  assert (Hlen : (length (D_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so))
                  + length (fo_w so))%nat = 0%nat)
    by (rewrite -length_app -Hacc; reflexivity).
  destruct (fo_E so) as [| y E1] eqn:HE.
  - rewrite /pcount_f fmap_nil proc_before_f_nil. cbn [length]. lia.
  - exfalso.
    assert (Hup : (0 < length (D_f (fo_ps so) (fo_cs so) (fo_f0 so)
                                 (y :: E1)))%nat).
    { change (D_f (fo_ps so) (fo_cs so) (fo_f0 so) (y :: E1))
        with (pending_at_f (fo_ps so) (fo_cs so) (fo_f0 so) []
              ++ [echo_of y.2]
              ++ D_from_f (fo_ps so) (fo_cs so) (fo_f0 so) ([] ++ [y.2]) E1).
      rewrite !length_app. cbn [length]. lia. }
    lia.
Qed.

(* THE ECHO'S ONE CALLER-OWED PREMISE, [EchoOut.echoed_lt_ins]'s twin at the
   two facts it actually reads (the log's order and era stamps, and the
   echoed slice's index law) rather than at the whole of [ein_pure]. *)
Lemma echoed_lt_ins_f (k : nat) (h : list mobs) (c : bv 8)
    (pops : list log_entry) :
  trace_shape h true -> obs_boots h = k -> obs_ends_in Uart0 h c ->
  (forall e, e ∈ pops -> hist_ext (le_hist e) h) ->
  (forall e, e ∈ pops -> obs_boots (le_hist e) = k) ->
  E_index (seg_of (echoed pops)) ->
  (length (echoed pops) < length (ins (open_seg h)))%nat.
Proof using.
  intros Hsh Hk Hends Hord Hstamp Hidx.
  destruct (open_seg_ends_in h c Hends) as [h0 Hh0].
  assert (Hlen0 : length (ins (open_seg h)) = S (length (ins h0))).
  { rewrite Hh0 ins_app ins_in length_app. cbn [length]. lia. }
  destruct (decide (length (echoed pops) = 0%nat)) as [Hz | Hz]; [lia |].
  destruct (lookup_lt_is_Some_2 (echoed pops)
              ((length (echoed pops) - 1)%nat) ltac:(lia)) as [y Hy].
  assert (Hsy : seg_of (echoed pops) !! ((length (echoed pops) - 1)%nat)
                = Some (open_seg (ehist y), y.2))
    by (by rewrite /seg_of list_lookup_fmap Hy).
  destruct (Hidx _ _ Hsy) as [_ Hylen]. cbn [Datatypes.fst] in Hylen.
  assert (Hyin : y ∈ echoed pops) by (by eapply elem_of_list_lookup_2).
  destruct (echoed_elem_inv pops y Hyin) as (e & He & _ & Hye).
  assert (Hoe : open_seg (le_hist e) = open_seg (ehist y)) by (by rewrite -Hye).
  destruct (open_seg_hist_ext (le_hist e) h (Hord e He)
              (eq_trans (Hstamp e He) (eq_sym Hk)) Hsh) as [Hpre Hlt2].
  rewrite Hoe Hh0 in Hpre. rewrite Hoe Hh0 length_app in Hlt2.
  cbn [length] in Hlt2.
  pose proof (prefix_snoc_lt (open_seg (ehist y)) h0 (ObsUartIn Uart0 c) Hpre
                ltac:(lia)) as Hp0.
  pose proof (prefix_length _ _ (ins_prefix_of _ _ Hp0)) as Hle.
  rewrite Hylen in Hle. lia.
Qed.

(* ====================================================================== *)
(*  2.  THE FIXED PART, AND THE SECOND PER-ERA RECORD                      *)
(*                                                                        *)
(*  [EchoOut.era_pins] is an echo file and is not edited, so the era's     *)
(*  boot state gets a record and a map of its own.  That map's AUTHORITY   *)
(*  needs a gname that outlives every era, and [AppFile.file_fixed] has    *)
(*  none to spare -- so the RECORD's fixed part is [file_gn], AppFile's    *)
(*  paired with it.  Nothing in [AppFile.v] moves: every one of its        *)
(*  definitions is read at [fgn_cl g].                                     *)
(* ====================================================================== *)

Record file_gn := MkFileGn {
  fgn_cl  : file_fixed;   (* AppFile's: the taint counter, the era map, the
                             line list *)
  fgn_era : gname;        (* ghost_map nat file_era: the era's BOOT STATE *)
}.

Definition fgn_echo (g : file_gn) : echo_fixed := Datatypes.fst (fgn_cl g).

Record file_era := MkFEra {
  fe_f0 : gname;   (* mono_list fst: [] before the era's boot state is
                      filed, [s0] after; the persistent witness is the lower
                      bound at [[s0]] *)
}.

Class fileOutG (Σ : gFunctors) := FileOutG {
  fog_era : ghost_mapG Σ nat file_era;
  fog_f0  : inG Σ (mono_listR (leibnizO fst));
}.
#[global] Existing Instances fog_era fog_f0.

Definition fileOutΣ : gFunctors :=
  #[ ghost_mapΣ nat file_era; GFunctor (mono_listR (leibnizO fst)) ].

Global Instance subG_fileOutΣ {Σ} : subG fileOutΣ Σ -> fileOutG Σ.
Proof. solve_inG. Qed.

(* the stage's [option fst] as the monotone list sees it *)
Definition opt_list (f0 : option fst) : list fst :=
  match f0 with None => [] | Some s => [s] end.

Section file_out.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).

  (* ---- the era's BOOT-STATE ghost ---- *)

  Definition file_era_pin (k : nat) (v : file_era) : iProp Σ :=
    ghost_map_elem (fgn_era g) k DfracDiscarded v.

  Global Instance file_era_pin_persistent k v : Persistent (file_era_pin k v).
  Proof using . rewrite /file_era_pin. apply _. Qed.
  Global Instance file_era_pin_timeless k v : Timeless (file_era_pin k v).
  Proof using . rewrite /file_era_pin. apply _. Qed.

  Lemma file_era_pin_agree k v v' :
    file_era_pin k v -∗ file_era_pin k v' -∗ ⌜v = v'⌝.
  Proof using .
    rewrite /file_era_pin. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq. by iPureIntro.
  Qed.

  Definition f0_auth (v : file_era) (l : list fst) : iProp Σ :=
    own (fe_f0 v) (●ML (l : list (leibnizO fst))).
  Definition f0_lb (v : file_era) (s0 : fst) : iProp Σ :=
    own (fe_f0 v) (◯ML ([s0] : list (leibnizO fst))).

  Global Instance f0_lb_persistent v s : Persistent (f0_lb v s).
  Proof using . rewrite /f0_lb. apply _. Qed.
  Global Instance f0_lb_timeless v s : Timeless (f0_lb v s).
  Proof using . rewrite /f0_lb. apply _. Qed.
  Global Instance f0_auth_timeless v l : Timeless (f0_auth v l).
  Proof using . rewrite /f0_auth. apply _. Qed.

  (* the lower bound READS the era's boot state: a one-element lower bound
     of a list of length at most one pins the list *)
  Lemma f0_auth_lb_agree (v : file_era) (f0 : option fst) (s : fst) :
    f0_auth v (opt_list f0) -∗ f0_lb v s -∗ ⌜f0 = Some s⌝.
  Proof using .
    rewrite /f0_auth /f0_lb. iIntros "Ha Hb".
    iDestruct (own_valid_2 with "Ha Hb") as %Hv%mono_list_both_valid_L.
    iPureIntro. destruct f0 as [s' |]; cbn [opt_list] in Hv.
    - destruct Hv as [z Hz]. destruct z as [| y z].
      + rewrite app_nil_r in Hz. by injection Hz as <-.
      + exfalso. apply (f_equal length) in Hz.
        rewrite length_app in Hz. cbn [length] in Hz. lia.
    - exfalso. by apply prefix_nil_inv in Hv.
  Qed.

  (* TWO LOWER BOUNDS OF THE ERA'S BOOT STATE AGREE, with no authority in
     hand: the era's list never grows past ONE entry, so two one-element
     lower bounds are comparable and hence equal.  This is what lets the
     ledger check a later drain's state against the one it fixed at the
     era's first. *)
  Lemma f0_lb_agree (v : file_era) (s s' : fst) :
    f0_lb v s -∗ f0_lb v s' -∗ ⌜s = s'⌝.
  Proof using .
    rewrite /f0_lb. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro.
    destruct (mono_list_lb_op_valid_1_L _ _ Hv) as [[z Hz] | [z Hz]];
      (destruct z as [| y z];
       [ rewrite app_nil_r in Hz; by injection Hz as ->
       | exfalso; apply (f_equal length) in Hz;
         rewrite length_app in Hz; cbn [length] in Hz; lia ]).
  Qed.

  Lemma f0_lb_get (v : file_era) (s : fst) :
    f0_auth v [s] -∗ f0_auth v [s] ∗ f0_lb v s.
  Proof using .
    rewrite /f0_auth /f0_lb. iIntros "Ha".
    iDestruct (own_mono _ _ (◯ML ([s] : list (leibnizO fst))) with "Ha")
      as "#Hb"; [ apply mono_list_included |].
    iFrame "Ha Hb".
  Qed.

  (* THE ERA'S FIRST PROCESS BYTE FILES THE BOOT STATE, once and for all *)
  Lemma f0_file (v : file_era) (s : fst) :
    f0_auth v [] ==∗ f0_auth v [s] ∗ f0_lb v s.
  Proof using .
    rewrite /f0_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML ([s] : list (leibnizO fst))) with "Ha") as "Ha".
    { apply mono_list_update. by exists [s]. }
    iModIntro. iApply (f0_lb_get with "Ha").
  Qed.

  Lemma f0_alloc : ⊢ |==> ∃ v : file_era, f0_auth v [].
  Proof using .
    iMod (own_alloc (●ML ([] : list (leibnizO fst)))) as (gf) "Hf";
      [apply mono_list_auth_valid |].
    iModIntro. iExists (MkFEra gf). rewrite /f0_auth /=. iFrame "Hf".
  Qed.

  (* ---- THE TYPED WITNESS: what the deed's evidence for the era's boot
         state looks like once it is inside the claim ---- *)
  Definition f0_typed (s : fst) : iProp Σ :=
    match s with
    | None => emp
    | Some bs =>
        (∃ ls : list wordline, fl_lb (fgn_cl g) ls ∗ ⌜f_bytes_typed ls bs⌝)%I
    end.

  Global Instance f0_typed_persistent s : Persistent (f0_typed s).
  Proof using . destruct s as [bs |]; rewrite /f0_typed; apply _. Qed.
  Global Instance f0_typed_timeless s : Timeless (f0_typed s).
  Proof using . destruct s as [bs |]; rewrite /f0_typed; apply _. Qed.

  Lemma f0_typed_none : ⊢ f0_typed None.
  Proof using . by rewrite /f0_typed. Qed.

  (* ====================================================================== *)
  (*  3.  THE CLAIM, THE TAG AND THE TURN                                   *)
  (* ====================================================================== *)

  (* [EchoOut.ecl] with the era's second record beside its first, the boot
     state's authority beside the four, and the deed's typed witness for
     that state.  Under the taint there is nothing to say, as before. *)
  Definition fecl (k : nat) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) : iProp Σ :=
    ( file_taint (fgn_cl g)
    ∨ ∃ (v : era_pins) (vf : file_era) (so : fostage),
        era_pin (fgn_echo g) k v
        ∗ file_era_pin k vf
        ∗ turn_auth v (pcount_f (fo_ps so) (fo_cs so) (fo_f0 so)
                         (fo_E so) (fo_w so))
        ∗ cs_auth v (fo_cs so)
        ∗ ps_auth v (fo_ps so)
        ∗ Elist_auth v (fo_E so)
        ∗ dl_cnt v (1/2) (length (LogEntryDefs.ch_dl H))
        ∗ f0_auth vf (opt_list (fo_f0 so))
        ∗ f0_typed (f0_st (fo_f0 so))
        ∗ ⌜fecl_pure k ho so H⌝)%I.

  Global Instance fecl_timeless k ho H : Timeless (fecl k ho H).
  Proof using . rewrite /fecl. apply _. Qed.

  (* THE LINE LIST the console has received, as a pure function of the
     history: the words of every complete [echo … > f] line, in order. *)
  Definition efl_of (h : list mobs) : list wordline := echof_lines_of h.

  (* THE TAG: [EchoOut.etag] at the FILE discipline, with a lower bound of
     the ledger's line list beside it -- which is how a typed line reaches
     the child's create step. *)
  Definition ftag (h : list mobs) : iProp Σ :=
    (⌜trace_shape h true⌝ ∗ (⌜disc_f h⌝ ∨ file_taint (fgn_cl g))
     ∗ fl_lb (fgn_cl g) (efl_of h))%I.

  Global Instance ftag_persistent h : Persistent (ftag h).
  Proof using . rewrite /ftag. apply _. Qed.
  Global Instance ftag_timeless h : Timeless (ftag h).
  Proof using . rewrite /ftag. apply _. Qed.

  (* THE CREDENTIAL INIT IS HANDED AT ITS ERA'S FIRST INSTRUCTION:
     [EchoOut.eturn] with the era's SECOND record beside its first, so that
     the first write can file the boot state. *)
  Definition fturn (k : nat) : iProp Σ :=
    (∃ (v : era_pins) (vf : file_era),
       era_pin (fgn_echo g) k v ∗ file_era_pin k vf
       ∗ turn v 0%nat ∗ dl_cnt v (1/2) 0%nat
       ∗ cs_lb v [] ∗ ps_lb v [] ∗ inp_lb v [])%I.

  Global Instance fturn_timeless k : Timeless (fturn k).
  Proof using . rewrite /fturn. apply _. Qed.

  (* ---- FILING THE LOG ENTRY, AND OPENING ONE, TAKE NOTHING ---- *)

  Lemma fecl_close (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    ConsLog.cons_hist_ok H ->
    ConsLog.cons_ev_ok H ConsLog.EvClose ->
    fecl k ho H -∗ fecl k ho (ConsLog.cons_step H ConsLog.EvClose).
  Proof using .
    intros Hok Hev. rewrite /fecl.
    iIntros "[HT | Hc]"; [by iLeft |]. iRight.
    iDestruct "Hc" as (v vf so)
      "(Hpin & Hfp & Htn & Hcs & Hps & HE & Hdl & Hf0 & Hty & %Hpure)".
    iExists v, vf, so. iFrame "Hpin Hfp Htn Hcs Hps HE Hf0 Hty".
    rewrite ch_dl_close. iFrame "Hdl". iPureIntro.
    by apply (fecl_pure_close k ho so H Hok Hev Hpure).
  Qed.

  Lemma fecl_open (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (h : list mobs) (c : bv 8) (cs : list (bv 8)) :
    LogEntryDefs.ch_arm H = None ->
    disc_seg_f (open_seg h) -> obs_boots h = k ->
    disc_f h -> trace_shape h true -> obs_ends_in Uart0 h c ->
    (forall e, e ∈ LogEntryDefs.ch_log H -> hist_ext (le_hist e) h) ->
    (length (echoed (LogEntryDefs.ch_log H)) < length (ins (open_seg h)))%nat ->
    fecl k ho H -∗ fecl k h (ConsLog.cons_step H (ConsLog.EvOpen h c cs)).
  Proof using .
    intros Hn Hd Hb Hdh Hsh Hends Hord Hlt. rewrite /fecl.
    iIntros "[HT | Hc]"; [by iLeft |]. iRight.
    iDestruct "Hc" as (v vf so)
      "(Hpin & Hfp & Htn & Hcs & Hps & HE & Hdl & Hf0 & Hty & %Hpure)".
    iExists v, vf, so. iFrame "Hpin Hfp Htn Hcs Hps HE Hf0 Hty".
    rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl]. iFrame "Hdl".
    iPureIntro.
    by apply (fecl_pure_open k ho so H h c cs Hn Hd Hb Hdh Hsh Hends Hord Hlt
                Hpure).
  Qed.

  (* THE SUPPLY'S LAW: a tainted era answers any event out of its taint arm *)
  Lemma fecl_sup (k : nat) (ho : list mobs) (H : LogEntryDefs.cons_hist)
      (ev : ConsLog.cons_ev) :
    file_taint (fgn_cl g) -∗ fecl k ho H ==∗ fecl k ho (ConsLog.cons_step H ev).
  Proof using . iIntros "#HT _". iModIntro. rewrite /fecl. by iLeft. Qed.

  (* what the claim says about an open arm, read back out *)
  Lemma fecl_arm (k : nat) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    fecl k ho CH -∗
      fecl k ho CH
      ∗ (file_taint (fgn_cl g) ∨ ⌜ch_arm_era_f k ho (LogEntryDefs.ch_arm CH)⌝).
  Proof using .
    rewrite /fecl. iIntros "[#HT | Hp]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct "Hp" as (v vf so)
      "(#Hpin & #Hfp & Htn & Hcs & Hps & HE & Hdl & Hf0 & #Hty & %Hall)".
    iSplitL.
    - iRight. iExists v, vf, so.
      iFrame "Hpin Hfp Htn Hcs Hps HE Hdl Hf0 Hty". by iPureIntro.
    - iRight. iPureIntro. exact (fecl_pure_arm k ho so CH Hall).
  Qed.

  (* ...AND THE COUNTING FACT the echo's step spends *)
  Lemma fecl_lt (k : nat) (h : list mobs) (c : bv 8) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) :
    trace_shape h true -> obs_boots h = k -> obs_ends_in Uart0 h c ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    fecl k ho CH -∗
      fecl k ho CH
      ∗ (file_taint (fgn_cl g)
         ∨ ⌜(length (echoed (LogEntryDefs.ch_log CH))
              < length (ins (open_seg h)))%nat⌝).
  Proof using .
    intros Hsh Hk Hends Hord. rewrite /fecl. iIntros "[#HT | Hp]".
    { iSplitR; [by iLeft | by iLeft]. }
    iDestruct "Hp" as (v vf so)
      "(#Hpin & #Hfp & Htn & Hcs & Hps & HE & Hdl & Hf0 & #Hty & %Hall)".
    iSplitL.
    - iRight. iExists v, vf, so.
      iFrame "Hpin Hfp Htn Hcs Hps HE Hdl Hf0 Hty". by iPureIntro.
    - iRight. iPureIntro.
      destruct Hall as (_ & _ & _ & Hin & _ & _).
      destruct Hin as (_ & _ & Hstamp & _ & Hidx & _ & _).
      exact (echoed_lt_ins_f k h c (LogEntryDefs.ch_log CH)
               Hsh Hk Hends Hord Hstamp Hidx).
  Qed.


  (* ====================================================================== *)
  (*  4.  THE STEPS THE LINKS SPEND                                         *)
  (* ====================================================================== *)

  (* THE ERA'S FIRST PROCESS BYTE, WHICH FILES THE BOOT STATE.  It is the
     first byte of the prologue's first letter, so it is
     [EchoOut.ecl_step_write_pro] at the EMPTY stage -- and there the stage
     is fully determined: [turn v 0] pins the cursor, [pro_pin_f] then pins
     the era's input to [[]] (an echoed byte needs a prologue letter on the
     wire before it), [ps_len_ok_f]'s second clause pins the prologue
     resolution to [[]] (nothing is written, so no shorter resolution may
     differ), [cs_len_ok_f] pins the choice list, and [feout_pure]'s own
     [fo_f0]-clause then says the boot state has NOT been filed.  So this
     step files it, keeping the deed's typed witness for the ledger; under
     the taint there is nothing to file. *)
  Lemma fecl_step_write_first (k : nat) (v : era_pins) (vf : file_era)
      (a : nat) (b : bv 8) (s0 : fst) (ho : list mobs)
      (H : LogEntryDefs.cons_hist) :
    fst_ok s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin k vf -∗
    turn v 0%nat -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    (f0_typed s0 ∨ file_taint (fgn_cl g)) -∗
    fecl k ho H ==∗
      fecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v 1%nat ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v []
          ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)).
  Proof using .
    intros Hfok Halt Hhead.
    iIntros "#Hpin #Hfp Ht #Hpslb #Hcslb #Hilb Hty Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /fecl; by iLeft | by iRight]. }
    iDestruct "Hty" as "[#Hty | #HT]"; last first.
    { iModIntro. iSplitR; [rewrite /fecl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 vf2 so)
      "(#Hpin2 & #Hfp2 & Hta & Hcs & Hps & HE & Hdl & Hf0 & #Hty0 & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (file_era_pin_agree with "Hfp2 Hfp") as %->.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    assert (Hpb : length (proc_before_f (fo_ps so) (fo_cs so) (fo_f0 so)
                    (snd <$> fo_E so)) = 0%nat /\ length (fo_w so) = 0%nat)
      by (rewrite /pcount_f in HP; lia).
    assert (Hwnil : fo_w so = []) by (apply nil_length_inv; lia).
    assert (HEnil : fo_E so = []).
    { destruct (decide (fo_E so = [])) as [? | Hne]; [done | exfalso].
      assert (Hin : (snd <$> fo_E so) <> []).
      { intro Hq. apply Hne. by apply fmap_nil_inv in Hq. }
      assert (Hst : (0 < nstarted (snd <$> fo_E so))%nat)
        by (by apply nstarted_pos).
      pose proof (Hpin 0%nat Hst) as Hlt.
      assert (Hps0 : fo_ps so <> []).
      { intros Hq. rewrite Hq in Hlt. cbn [pro_rounds] in Hlt. lia. }
      pose proof (pro_of_pos (fo_ps so) Hpsb Hps0) as Hpp.
      pose proof (prefix_length _ _
                    (proc_before_f_head (fo_ps so) (fo_cs so) (fo_f0 so)
                       (snd <$> fo_E so) Hin)) as Hle.
      rewrite pending_at_f_nil in Hle. lia. }
    assert (Hf0nil : fo_f0 so = None) by (apply Hf0n; by split).
    (* the prologue resolution is empty: nothing is written, so no shorter
       resolution may give a different prologue *)
    assert (Hpsnil : fo_ps so = []).
    { destruct Hpsl as [_ HpsB].
      assert (Hopens : ps_opens_f so)
        by (left; by rewrite HEnil fmap_nil).
      assert (Hround : ps_round_f so = 0%nat)
        by (rewrite /ps_round_f HEnil fmap_nil nlines_nil; reflexivity).
      assert (Hproeq : pro_of (fo_ps so) = []).
      { destruct (decide (pro_of (pro_from (ps_round_f so) [])
                          = pro_of (pro_from (ps_round_f so) (fo_ps so))))
          as [Heq | Hne].
        - rewrite Hround in Heq. cbn [pro_from] in Heq.
          by rewrite -Heq pro_of_nil.
        - exfalso. pose proof (HpsB Hopens [] (prefix_nil _) Hne) as Hlt.
          rewrite Hwnil in Hlt. cbn [length] in Hlt. lia. }
      destruct (decide (fo_ps so = [])) as [? | Hne]; [done | exfalso].
      pose proof (pro_of_pos (fo_ps so) Hpsb Hne) as Hpp.
      rewrite Hproeq in Hpp. cbn [length] in Hpp. lia. }
    assert (Hcsnil : fo_cs so = []).
    { apply nil_length_inv.
      destruct (cs_len_ok_f_inv so Hcsl) as [[_ Hq] | [Hne _]].
      - rewrite Hq HEnil fmap_nil nlines_nil. lia.
      - exfalso. apply Hne. split; [exact Hwnil |].
        by rewrite HEnil fmap_nil rest_of_nil. }
    rewrite Hf0nil in HP. rewrite Hf0nil. cbn [opt_list].
    iMod (f0_file vf s0 with "Hf0") as "[Hf0 #Hf0lb]".
    iMod (turn_update v 0%nat
            (pcount_f (fo_ps so) (fo_cs so) None (fo_E so) (fo_w so))
            1%nat ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (ps_auth_grow v (fo_ps so) a with "Hps") as "[Hps #Hpslb2]".
    rewrite Hpsnil. cbn [app].
    iModIntro. iSplitR "Ht".
    - rewrite /fecl. iRight.
      iExists v, vf, (MkFO [a] [] [] [b] (Some s0)).
      cbn [fo_ps fo_cs fo_E fo_w fo_f0 opt_list].
      rewrite (_ : pcount_f [a] [] (Some s0) [] [b] = 1%nat); last first.
      { rewrite /pcount_f fmap_nil proc_before_f_nil. reflexivity. }
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite Hcsnil. iFrame "Hpin Hfp Hta Hcs Hps Hdl Hf0".
      rewrite HEnil. iFrame "HE".
      rewrite (_ : f0_st (Some s0) = s0); [| reflexivity]. iFrame "Hty".
      iPureIntro.
      apply (fecl_pure_out k ho so (MkFO [a] [] [] [b] (Some s0)) H b);
        [cbn [fo_cs]; rewrite Hcsnil; cbn [length]; lia
        | cbn [fo_E]; by rewrite HEnil | | | | exact Hall0].
      + rewrite /feout_pure. cbn [fo_ps fo_cs fo_E fo_w fo_f0]. split_and!.
        * rewrite Hacc Hwnil HEnil Hpsnil Hf0nil app_nil_r.
          rewrite /D_f. cbn [D_from_f]. by rewrite app_nil_l.
        * rewrite /pending_f fmap_nil pending_at_f_nil pro_of_singleton.
          apply (fop_prefix_snoc_lookup [] _ b); [apply prefix_nil | exact Hhead].
        * intros j x Hx. by rewrite lookup_nil in Hx.
        * rewrite /E_disc_f fmap_nil. exact disc_input_f_nil.
        * by apply Forall_singleton.
        * rewrite fmap_nil. intros q Hq. rewrite nstarted_nil in Hq. lia.
        * apply alts_pre_nil.
        * constructor.
        * constructor.
        * cbn [length]. lia.
        * by left.
        * split; [discriminate | intros [_ Hq]; discriminate].
        * exact Hfok.
      + apply cs_len_ok_f_intro; intros Hq; [by destruct Hq | ].
        rewrite fmap_nil nlines_nil. reflexivity.
      + rewrite /ps_len_ok_f /ps_round_f /ps_opens_f.
        cbn [fo_ps fo_cs fo_E fo_w fo_f0]. rewrite fmap_nil nlines_nil.
        cbn [pro_idx_f]. split.
        * cbn [pro_from pro_tail]. by case_decide.
        * intros _ ps' Hp Hne. cbn [pro_from] in Hne |- *.
          assert (Hcases : ps' = [] \/ ps' = [a]).
          { destruct ps' as [| x [| y ps'']]; [by left | | ].
            - right. destruct Hp as [z Hz]. by injection Hz as -> _.
            - exfalso. pose proof (prefix_length _ _ Hp) as Hl.
              cbn [length] in Hl. lia. }
          destruct Hcases as [-> | ->]; [| by destruct (Hne eq_refl)].
          rewrite pending_at_f_nil pro_of_nil. cbn [length]. lia.
    - iLeft. iFrame "Ht Hf0lb Hcslb Hilb". iExact "Hpslb2".
  Qed.


  (* (W) THE ORDINARY WRITE.  [EchoOut.ecl_step_write] with the era's boot
     state beside the three bounds: the writer's [f0_lb] pins the stage's
     own [fo_f0], so the byte it computes from the stream is the byte the
     claim owes. *)
  Lemma fecl_step_write (k : nat) (v : era_pins) (vf : file_era) (P : nat)
      (b : bv 8) (ps0 cs0 : list nat) (s0 : fst) (I0 : list (bv 8))
      (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    (nlines I0 <= length cs0)%nat ->
    pro_pin_f ps0 cs0 I0 ->
    proc_stream_f ps0 cs0 (Some s0) I0 !! P = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin k vf -∗
    turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
    fecl k ho H ==∗
      fecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0
          ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)).
  Proof using .
    intros Hn Hpin0 Hb.
    iIntros "#Hpin #Hfp Ht #Hpslb #Hcslb #Hilb #Hf0lb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /fecl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 vf2 so)
      "(#Hpin2 & #Hfp2 & Hta & Hcs & Hps & HE & Hdl & Hf0 & #Hty0 & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (file_era_pin_agree with "Hfp2 Hfp") as %->.
    iDestruct (f0_auth_lb_agree with "Hf0 Hf0lb") as %Hf0eq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "HE Hilb") as %HI0.
    rewrite -Hf0eq in Hb.
    destruct (write_stage_byte_f ps0 (fo_ps so) cs0 (fo_cs so) (fo_f0 so)
                (fo_E so) (fo_w so) I0 P b Hpsp Hpin0 Hcsp Hn HI0 HP Hb)
      as [HlenE Hnext].
    assert (Hcase : fo_w so <> []
                    \/ rest_of (snd <$> fo_E so) <> []
                    \/ (snd <$> fo_E so) = []).
    { destruct (decide (fo_w so = [])) as [Hw | Hw]; [| by left].
      destruct (decide (rest_of (snd <$> fo_E so) = [])) as [Hm | Hm];
        [| by right; left].
      right; right.
      destruct (cs_len_ok_f_inv so Hcsl) as [[_ Hq] | [Hne _]]; last first.
      { exfalso. by apply Hne. }
      destruct (decide ((snd <$> fo_E so) = [])) as [Hz | Hz]; [exact Hz |].
      exfalso.
      pose proof (prefix_length _ _ Hcsp) as Hlen0.
      pose proof (nlines_pos_of_rest_nil (snd <$> fo_E so) Hz Hm) as Hpos.
      rewrite -HlenE in Hn. lia. }
    iMod (turn_update v P
            (pcount_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so) (fo_w so))
            (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iModIntro. iSplitR "Ht".
    - rewrite /fecl. iRight.
      iExists v, vf,
        (MkFO (fo_ps so) (fo_cs so) (fo_E so) (fo_w so ++ [b]) (fo_f0 so)).
      cbn [fo_ps fo_cs fo_E fo_w fo_f0].
      rewrite pcount_f_write -HP.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hfp Hta Hcs Hps HE Hdl Hf0 Hty0". iPureIntro.
      apply (fecl_pure_out k ho so
               (MkFO (fo_ps so) (fo_cs so) (fo_E so) (fo_w so ++ [b])
                  (fo_f0 so)) H b);
        [cbn [fo_cs]; lia | reflexivity | | | | exact Hall0].
      + rewrite /feout_pure. cbn [fo_ps fo_cs fo_E fo_w fo_f0]. split_and!.
        * by rewrite Hacc app_assoc.
        * by apply fop_prefix_snoc_lookup.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpin.
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * split; [rewrite Hf0eq; discriminate |].
          intros [_ Hq]. exfalso.
          by destruct (app_eq_nil (fo_w so) [b] Hq) as [_ Hb2].
        * exact Hfok0.
      + exact (cs_len_ok_f_write so b Hcsl Hcase).
      + exact (ps_len_ok_f_write so b Hpsl).
    - iLeft. iFrame "Ht Hpslb Hcslb Hilb Hf0lb".
  Qed.

  (* (W') THE WRITE AT A BLOCK'S FIRST BYTE: the alternative's index is the
     program's knowledge and this step files it.  [EchoOut.ecl_step_write_blk]
     with [FileDisc.ralt_ok] where [a < 4] was, and the block read at the
     era's own boot state. *)
  Lemma fecl_step_write_blk (k : nat) (v : era_pins) (vf : file_era)
      (P a : nat) (b : bv 8) (ps0 cs0 : list nat) (s0 : fst)
      (I0 : list (bv 8)) (ho : list mobs) (H : LogEntryDefs.cons_hist) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin_f ps0 cs0 I0 ->
    P = length (proc_before_f ps0 cs0 (Some s0) I0) ->
    ralt_ok (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a) ->
    cont (fst_upto cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat)
         (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a)
      !! 0%nat = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin k vf -∗
    turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
    fecl k ho H ==∗
      fecl k ho (ConsLog.cons_step H (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
          ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)).
  Proof using .
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hhead.
    pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
    pose proof (fop_nlines_removelast I0 Hr0) as Hrl0.
    iIntros "#Hpin #Hfp Ht #Hpslb #Hcslb #Hilb #Hf0lb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /fecl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 vf2 so)
      "(#Hpin2 & #Hfp2 & Hta & Hcs & Hps & HE & Hdl & Hf0 & #Hty0 & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (file_era_pin_agree with "Hfp2 Hfp") as %->.
    iDestruct (f0_auth_lb_agree with "Hf0 Hf0lb") as %Hf0eq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpin & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "HE Hilb") as %HI0.
    rewrite -Hf0eq in HPeq.
    assert (Hstream : proc_before_f ps0 cs0 (fo_f0 so) I0
                      = proc_before_f (fo_ps so) (fo_cs so) (fo_f0 so) I0).
    { apply (proc_before_f_cs_prefix ps0 (fo_ps so) cs0 (fo_cs so)
               (fo_f0 so) I0 Hpsp Hcsp Hpin0). lia. }
    assert (HlenE : (snd <$> fo_E so) = I0).
    { destruct (decide ((snd <$> fo_E so) = I0)) as [? | Hne]; [done | exfalso].
      pose proof (proc_stream_f_before (fo_ps so) (fo_cs so) (fo_f0 so) I0
                    (snd <$> fo_E so) HI0
                    ltac:(intros Hq; apply Hne; symmetry; exact Hq)) as Hpre.
      apply prefix_length in Hpre.
      rewrite /proc_stream_f length_app -Hstream in Hpre.
      assert (Hne1 : pending_at_f (fo_ps so) (fo_cs so) (fo_f0 so) I0 <> []).
      { rewrite /pending_at_f decide_False; [| exact Hne0].
        rewrite decide_True; [| exact Hr0].
        rewrite /alt_cont_f. intros Hc. apply app_eq_nil in Hc as [Hc _].
        revert Hc. apply cont_nonnil.
        destruct (decide (nlines I0 - 1 < length (fo_cs so))%nat)
          as [Hlt | Hge]; [left | right; apply ralt_at_ge; lia].
        pose proof (alts_pre_at (snd <$> fo_E so) (fo_cs so) _ Hcsb' Hlt)
          as Hok.
        assert (Hb0 : (nlines I0 - 1 < length (bodies_of I0))%nat).
        { pose proof Hpos0 as Hp2. rewrite /nlines in Hp2 |- *. lia. }
        destruct (bodies_of_prefix I0 (snd <$> fo_E so) HI0) as [z Hz].
        rewrite Hz !list_lookup_total_alt lookup_app_l in Hok; [| exact Hb0].
        by rewrite -!list_lookup_total_alt in Hok. }
      assert (Hlen1 : (1 <= length (pending_at_f (fo_ps so) (fo_cs so)
                                      (fo_f0 so) I0))%nat).
      { destruct (pending_at_f (fo_ps so) (fo_cs so) (fo_f0 so) I0);
          [done | cbn; lia]. }
      rewrite /pcount_f in HP. lia. }
    assert (Hwnil : fo_w so = []).
    { assert (Hz : length (fo_w so) = 0%nat).
      { rewrite /pcount_f in HP. rewrite HlenE -Hstream in HP. lia. }
      by apply nil_length_inv. }
    destruct (cs_len_ok_f_inv so Hcsl) as [[_ Hq] | [Hne _]]; last first.
    { exfalso. apply Hne. split; [exact Hwnil | by rewrite HlenE]. }
    rewrite HlenE in Hq.
    assert (Hcs0 : cs0 = fo_cs so).
    { pose proof (prefix_length _ _ Hcsp) as Hle.
      destruct Hcsp as [z Hz]. rewrite Hz.
      assert (Hzn : z = []).
      { apply nil_length_inv. rewrite Hz length_app in Hle |- *.
        rewrite Hz length_app in Hq. lia. }
      by rewrite Hzn app_nil_r. }
    assert (Hidx0 : ralt_at (fo_cs so ++ [a]) (nlines I0 - 1)%nat = ralt_dec a).
    { rewrite /ralt_at list_lookup_total_alt lookup_app_r; [| lia].
      rewrite Hq Nat.sub_diag. reflexivity. }
    (* the block below the last line does not read the new entry, so the
       state the block starts in is the writer's own *)
    assert (Hfst : fst_upto (fo_cs so ++ [a]) s0 (bodies_of I0)
                     (nlines I0 - 1)%nat
                   = fst_upto cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat).
    { apply fst_upto_ext; [| intros j Hj; reflexivity].
      intros j Hj. rewrite Hcs0 !list_lookup_total_alt lookup_app_l; [done | lia]. }
    assert (Hpend : pending_f (fo_ps so) (fo_cs so ++ [a]) (fo_f0 so)
                      (fo_E so) !! 0%nat = Some b).
    { rewrite /pending_f HlenE /pending_at_f.
      rewrite decide_False; [| exact Hne0]. rewrite decide_True; [| exact Hr0].
      rewrite /alt_cont_f Hidx0 Hf0eq f0_st_some Hfst.
      rewrite lookup_app_l; [exact Hhead |].
      destruct (cont (fst_upto cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat)
                  (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat))
                  (ralt_dec a)) as [| z zs] eqn:Hz;
        [ exfalso; revert Hz; by apply cont_nonnil; left | cbn; lia ]. }
    assert (Hpinq : pro_pin_f (fo_ps so) (fo_cs so ++ [a]) (snd <$> fo_E so)).
    { intros qq Hqq. rewrite pro_idx_f_app_le; [by apply Hpin |].
      rewrite HlenE (fop_nstarted_rest_nil I0 Hr0) in Hqq. rewrite Hq. lia. }
    assert (HD : D_f (fo_ps so) (fo_cs so ++ [a]) (fo_f0 so) (fo_E so)
                 = D_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)).
    { symmetry. apply (D_f_cs_prefix (fo_ps so) (fo_ps so) (fo_cs so)
                         (fo_cs so ++ [a]) (fo_f0 so) (fo_E so));
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE Hrl0 Hq. lia. }
    assert (Hpceq : pcount_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so) [b]
                    = pcount_f (fo_ps so) (fo_cs so ++ [a]) (fo_f0 so)
                        (fo_E so) [b]).
    { apply (pcount_f_cs_prefix (fo_ps so) (fo_ps so) (fo_cs so)
               (fo_cs so ++ [a]) (fo_f0 so) (fo_E so) [b]);
        [reflexivity | by eexists | exact Hpin |].
      rewrite HlenE Hrl0 Hq. lia. }
    assert (Hpc2 : pcount_f (fo_ps so) (fo_cs so ++ [a]) (fo_f0 so)
                     (fo_E so) [b] = S P).
    { rewrite -Hpceq /pcount_f HlenE -Hstream. cbn [length]. lia. }
    iMod (turn_update v P
            (pcount_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so) (fo_w so))
            (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (cs_auth_grow v (fo_cs so) a with "Hcs") as "[Hcs #Hcslb2]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb2]".
    iModIntro. iSplitR "Ht".
    - rewrite /fecl. iRight.
      iExists v, vf, (MkFO (fo_ps so) (fo_cs so ++ [a]) (fo_E so) [b]
                        (fo_f0 so)).
      cbn [fo_ps fo_cs fo_E fo_w fo_f0]. rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hfp Hta Hcs Hps HE Hdl Hf0 Hty0". iPureIntro.
      apply (fecl_pure_out k ho so
               (MkFO (fo_ps so) (fo_cs so ++ [a]) (fo_E so) [b] (fo_f0 so))
               H b);
        [cbn [fo_cs]; rewrite length_app; cbn [length]; lia
        | reflexivity | | | | exact Hall0].
      + rewrite /feout_pure. cbn [fo_ps fo_cs fo_E fo_w fo_f0]. split_and!.
        * rewrite Hacc Hwnil app_nil_r HD. reflexivity.
        * apply (fop_prefix_snoc_lookup [] _ b); [apply prefix_nil |].
          by rewrite -Hpend.
        * exact Hidx.
        * exact Hbyte.
        * exact Hpsb.
        * exact Hpinq.
        * apply alts_pre_snoc; [exact Hcsb' | rewrite HlenE Hq; lia |].
          rewrite HlenE Hq. exact Halt.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * split; [rewrite Hf0eq; discriminate | intros [_ Hq2]; discriminate].
        * exact Hfok0.
      + apply (cs_len_ok_f_blk so a b);
          [by rewrite HlenE | by rewrite HlenE | exact Hwnil | exact Hcsl].
      + apply (ps_len_ok_f_blk so a b);
          [by rewrite HlenE | by rewrite HlenE | by rewrite HlenE | exact Hpsl].
    - iLeft. rewrite Hcs0. iFrame "Ht Hilb Hcslb2 Hpslb Hf0lb".
  Qed.


  (* (W-pro) THE WRITE AT A PROLOGUE ROUND'S CHOICE BYTE -- init's own
     knowledge of which of the four alternatives its restart loop is taking,
     filed into the claim.  [EchoOut.ecl_step_write_pro] at the file stage:
     the round-opening test is [FileDisc.ralt_panic] of the last line's
     alternative where echo asked for the literal index 3, so the two new
     line shapes' fork alternatives ([RFFork], [RCFork]) open a round too. *)
  Lemma fecl_step_write_pro (k : nat) (v : era_pins) (vf : file_era)
      (P a : nat) (b : bv 8) (ps0 cs0 : list nat) (s0 : fst)
      (I0 : list (bv 8)) (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    rest_of I0 = [] ->
    (I0 = [] \/ ralt_panic (ralt_at cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    pro_pin_f ps0 cs0 I0 ->
    ~ pro_done (pro_from (pro_idx_f cs0 (nlines I0)) ps0) ->
    P = length (proc_stream_f ps0 cs0 (Some s0) I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin k vf -∗ turn v P -∗
    ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
    fecl k ho CH ==∗
      fecl k ho (ConsLog.cons_step CH (ConsLog.EvOut b))
      ∗ ((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
          ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)).
  Proof using .
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "#Hpin #Hfp Ht #Hpslb #Hcslb #Hilb #Hf0lb Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /fecl; by iLeft | by iRight]. }
    iDestruct "Hp" as (v2 vf2 so)
      "(#Hpin2 & #Hfp2 & Hta & Hcs & Hps & HE & Hdl & Hf0 & #Hty0 & %Hall)".
    iDestruct (era_pin_agree with "Hpin2 Hpin") as %->.
    iDestruct (file_era_pin_agree with "Hfp2 Hfp") as %->.
    iDestruct (f0_auth_lb_agree with "Hf0 Hf0lb") as %Hf0eq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & _ & _ & _).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpinf & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hf0n & Hfok0).
    iDestruct (turn_agree with "Ht Hta") as %HP.
    iDestruct (cs_lb_prefix with "Hcs Hcslb") as %Hcsp.
    iDestruct (ps_lb_prefix with "Hps Hpslb") as %Hpsp.
    iDestruct (inp_lb_le with "HE Hilb") as %HI0.
    rewrite -Hf0eq in HPeq.
    pose proof (fop_nlines_removelast I0 Hr0) as Hrl0.
    (* the writer's own list is bounded, and its round index is the claim's *)
    assert (Hpsb0 : Forall (fun x => (x < length pro_alts)%nat) ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2. by apply Forall_app in Hpsb2 as [? _]. }
    assert (Hlk : forall j, (j < nlines I0)%nat ->
              fo_cs so !!! j = cs0 !!! j)
      by (intros j Hj; apply (fop_lta_prefix cs0 (fo_cs so) j Hcsp); lia).
    assert (Hidxeq : pro_idx_f (fo_cs so) (nlines I0)
                     = pro_idx_f cs0 (nlines I0))
      by (apply (pro_idx_f_ext (fo_cs so) cs0 (nlines I0)); [exact Hlk | lia]).
    rewrite -Hidxeq in Hnd.
    assert (HopenC : I0 = [] \/
              ralt_panic (ralt_at (fo_cs so) (nlines I0 - 1)%nat) = true).
    { destruct (decide (I0 = [])) as [Hz | Hne0]; [by left | right].
      pose proof (nlines_pos_of_rest_nil I0 Hne0 Hr0) as Hpos0.
      destruct Hopen as [Hz | H3]; [by destruct (Hne0 Hz) |].
      rewrite /ralt_at (Hlk (nlines I0 - 1)%nat ltac:(lia)). exact H3. }
    assert (Hstream : proc_before_f ps0 cs0 (fo_f0 so) I0
                      = proc_before_f (fo_ps so) (fo_cs so) (fo_f0 so) I0).
    { apply (proc_before_f_cs_prefix ps0 (fo_ps so) cs0 (fo_cs so)
               (fo_f0 so) I0 Hpsp Hcsp Hpin0). lia. }
    assert (Hpend0 : pending_at_f ps0 cs0 (fo_f0 so) I0
                     = pending_at_f ps0 (fo_cs so) (fo_f0 so) I0)
      by (apply (pending_at_f_cs_ext ps0 cs0 (fo_cs so) (fo_f0 so) I0
                   Hcsp Hdiv)).
    assert (Hpmono : pending_at_f ps0 (fo_cs so) (fo_f0 so) I0
                     `prefix_of` pending_at_f (fo_ps so) (fo_cs so)
                                   (fo_f0 so) I0)
      by (by apply pending_at_f_ps_mono).
    assert (HPval : P = (length (proc_before_f ps0 cs0 (fo_f0 so) I0)
                         + length (pending_at_f ps0 cs0 (fo_f0 so) I0))%nat).
    { rewrite HPeq /proc_stream_f.
      by rewrite (length_app (proc_before_f ps0 cs0 (fo_f0 so) I0)
                    (pending_at_f ps0 cs0 (fo_f0 so) I0)). }
    rewrite /pcount_f in HP.
    (* the era's input IS [I0] *)
    assert (HlenE : (snd <$> fo_E so) = I0).
    { destruct (decide ((snd <$> fo_E so) = I0)) as [? | Hne]; [done | exfalso].
      assert (Hnei : I0 <> (snd <$> fo_E so))
        by (intros Hq; apply Hne; symmetry; exact Hq).
      pose proof (proc_stream_f_before (fo_ps so) (fo_cs so) (fo_f0 so) I0
                    (snd <$> fo_E so) HI0 Hnei) as Hpre.
      apply prefix_length in Hpre.
      rewrite /proc_stream_f length_app -Hstream in Hpre.
      pose proof (prefix_length _ _ Hpmono) as Hlp. rewrite -Hpend0 in Hlp.
      assert (Hpe : pending_at_f ps0 (fo_cs so) (fo_f0 so) I0
                    = pending_at_f (fo_ps so) (fo_cs so) (fo_f0 so) I0).
      { apply prefix_length_eq; [exact Hpmono | rewrite -Hpend0; lia]. }
      pose proof (pending_at_f_round_det ps0 (fo_ps so) (fo_cs so) (fo_f0 so)
                    I0 Hr0 HopenC Hpe) as Hpro.
      assert (Hdone : pro_done (pro_from (pro_idx_f (fo_cs so) (nlines I0))
                        (fo_ps so))).
      { apply pro_from_done.
        apply Hpinf.
        exact (nstarted_strict I0 (snd <$> fo_E so) HI0 Hnei). }
      apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (pro_idx_f (fo_cs so) (nlines I0)) ps0)
                  (pro_from (pro_idx_f (fo_cs so) (nlines I0)) (fo_ps so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hpro; reflexivity)) as [Hd _].
      exact Hd. }
    assert (Hlenw : length (fo_w so)
                    = length (pending_at_f ps0 cs0 (fo_f0 so) I0)).
    { rewrite HlenE -Hstream in HP. lia. }
    assert (Hweq : fo_w so = pending_at_f ps0 (fo_cs so) (fo_f0 so) I0).
    { assert (Hw1 : fo_w so
                    `prefix_of` pending_at_f (fo_ps so) (fo_cs so)
                                  (fo_f0 so) I0)
        by (rewrite -HlenE; exact Hwpre).
      assert (Hlen2 : length (fo_w so)
                      = length (pending_at_f ps0 (fo_cs so) (fo_f0 so) I0))
        by (rewrite -Hpend0; exact Hlenw).
      destruct (prefix_weak_total (fo_w so)
                  (pending_at_f ps0 (fo_cs so) (fo_f0 so) I0)
                  (pending_at_f (fo_ps so) (fo_cs so) (fo_f0 so) I0)
                  Hw1 Hpmono) as [Hq | Hq].
      - apply prefix_length_eq; [exact Hq | lia].
      - symmetry. apply prefix_length_eq; [exact Hq | lia]. }
    assert (Hopens : ps_opens_f so).
    { rewrite /ps_opens_f HlenE.
      destruct HopenC as [Hz | H3]; [by left | right; by split]. }
    pose proof Hpsl as [HpsA HpsB].
    assert (Hproeq : pro_of (pro_from (pro_idx_f (fo_cs so) (nlines I0)) ps0)
                     = pro_of (pro_from (pro_idx_f (fo_cs so) (nlines I0))
                         (fo_ps so))).
    { destruct (decide (pro_of (pro_from
                          (pro_idx_f (fo_cs so) (nlines I0)) ps0)
                        = pro_of (pro_from
                            (pro_idx_f (fo_cs so) (nlines I0)) (fo_ps so))))
        as [Heq | Hne]; [exact Heq | exfalso].
      pose proof (HpsB Hopens ps0 Hpsp) as Hlt.
      rewrite /ps_round_f HlenE in Hlt.
      pose proof (Hlt Hne) as Hlt2. rewrite Hweq in Hlt2. lia. }
    assert (Hndps : ~ pro_done (pro_from (pro_idx_f (fo_cs so) (nlines I0))
                      (fo_ps so))).
    { intros Hdone. apply Hnd.
      destruct (pro_of_prefix_free
                  (pro_from (pro_idx_f (fo_cs so) (nlines I0)) ps0)
                  (pro_from (pro_idx_f (fo_cs so) (nlines I0)) (fo_ps so))
                  ltac:(by apply pro_from_Forall)
                  ltac:(by apply pro_from_Forall)
                  Hdone ltac:(rewrite -Hproeq; reflexivity)) as [Hd _].
      exact Hd. }
    assert (Hround0 : (pro_idx_f (fo_cs so) (nlines I0)
                       <= pro_rounds ps0)%nat).
    { rewrite Hidxeq.
      by apply (pro_pin_f_round_le ps0 cs0 I0 Hr0 Hopen Hpin0). }
    assert (Hpseq : fo_ps so = ps0).
    { pose proof Hpsp as Hq. destruct Hq as [z Hz]. pose proof Hpsb as Hpsb2.
      rewrite Hz in Hpsb2.
      assert (Hzb : Forall (fun x => (x < length pro_alts)%nat) z)
        by (by apply Forall_app in Hpsb2 as [_ ?]).
      pose proof Hproeq as Hpe2. rewrite Hz in Hpe2.
      rewrite (pro_from_app_le _ ps0 z Hround0) in Hpe2.
      assert (Hzn : z = []).
      { apply (pro_of_open_app_inj _ z Hnd Hzb). by rewrite -Hpe2. }
      rewrite Hz Hzn. by rewrite app_nil_r. }
    assert (HRle : (pro_idx_f (fo_cs so) (nlines I0)
                    <= pro_rounds (fo_ps so))%nat)
      by (rewrite Hpseq; exact Hround0).
    assert (Hshape2 : pending_at_f (fo_ps so ++ [a]) (fo_cs so) (fo_f0 so) I0
                      = (if decide (I0 = []) then [] else alt_panic)
                        ++ pro_of (pro_from
                             (pro_idx_f (fo_cs so) (nlines I0))
                             (fo_ps so ++ [a])))
      by (apply pending_at_f_round_pre; [exact Hr0 | exact HopenC]).
    assert (Hshape : pending_at_f (fo_ps so) (fo_cs so) (fo_f0 so) I0
                     = (if decide (I0 = []) then [] else alt_panic)
                       ++ pro_of (pro_from
                            (pro_idx_f (fo_cs so) (nlines I0)) (fo_ps so)))
      by (apply pending_at_f_round_pre; [exact Hr0 | exact HopenC]).
    assert (Hpendb : pending_at_f (fo_ps so ++ [a]) (fo_cs so) (fo_f0 so) I0
                       !! length (fo_w so) = Some b).
    { pose proof (pro_of_snoc_head
                    (pro_from (pro_idx_f (fo_cs so) (nlines I0)) (fo_ps so))
                    a b Hndps Hhead) as Hph.
      assert (Hpre3' :
        ((if decide (I0 = []) then [] else alt_panic)
         ++ (pro_of (pro_from (pro_idx_f (fo_cs so) (nlines I0)) (fo_ps so))
             ++ [b]))
        `prefix_of` pending_at_f (fo_ps so ++ [a]) (fo_cs so) (fo_f0 so) I0).
      { rewrite Hshape2 (pro_from_snoc_le _ (fo_ps so) a HRle).
        by apply prefix_app. }
      assert (Hwl : length (fo_w so)
                    = (length (if decide (I0 = []) then [] else alt_panic)
                       + length (pro_of (pro_from
                           (pro_idx_f (fo_cs so) (nlines I0))
                           (fo_ps so))))%nat).
      { rewrite Hweq -Hpseq Hshape.
        by rewrite (length_app
                      (if decide (I0 = []) then [] else alt_panic)
                      (pro_of (pro_from (pro_idx_f (fo_cs so) (nlines I0))
                         (fo_ps so)))). }
      rewrite Hwl. eapply prefix_lookup_Some; [| exact Hpre3'].
      rewrite (lookup_app_shift
                 (if decide (I0 = []) then [] else alt_panic)).
      replace (length (pro_of (pro_from
                 (pro_idx_f (fo_cs so) (nlines I0)) (fo_ps so))))
        with (length (pro_of (pro_from
                 (pro_idx_f (fo_cs so) (nlines I0)) (fo_ps so))) + 0)%nat
        by lia.
      by rewrite (lookup_app_shift
                    (pro_of (pro_from (pro_idx_f (fo_cs so) (nlines I0))
                       (fo_ps so)))). }
    assert (Hcase : fo_w so <> []
                    \/ rest_of (snd <$> fo_E so) <> []
                    \/ (snd <$> fo_E so) = []).
    { destruct (decide (I0 = [])) as [Hz | Hnz].
      { right; right. by rewrite HlenE. }
      left. rewrite Hweq -Hpseq.
      rewrite /pending_at_f decide_False; [| exact Hnz].
      rewrite decide_True; [| exact Hr0].
      rewrite /alt_cont_f. intros Hc. apply app_eq_nil in Hc as [Hc _].
      revert Hc. apply cont_nonnil.
      destruct (decide (nlines I0 - 1 < length (fo_cs so))%nat)
        as [Hlt | Hge]; [left | right; apply ralt_at_ge; lia].
      pose proof (alts_pre_at (snd <$> fo_E so) (fo_cs so) _ Hcsb' Hlt)
        as Hok. by rewrite HlenE in Hok. }
    assert (HD : D_f (fo_ps so ++ [a]) (fo_cs so) (fo_f0 so) (fo_E so)
                 = D_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)).
    { symmetry. apply (D_f_ps_ext (fo_ps so) (fo_ps so ++ [a]) (fo_cs so)
                         (fo_f0 so) (fo_E so)); [by eexists | exact Hpinf]. }
    assert (Hpceq : pcount_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)
                      (fo_w so ++ [b])
                    = pcount_f (fo_ps so ++ [a]) (fo_cs so) (fo_f0 so)
                        (fo_E so) (fo_w so ++ [b])).
    { apply (pcount_f_cs_prefix (fo_ps so) (fo_ps so ++ [a]) (fo_cs so)
               (fo_cs so) (fo_f0 so) (fo_E so) (fo_w so ++ [b]));
        [by eexists | reflexivity | exact Hpinf |].
      pose proof (prefix_length _ _ Hcsp) as Hle2.
      rewrite HlenE Hrl0. lia. }
    assert (Hpc2 : pcount_f (fo_ps so ++ [a]) (fo_cs so) (fo_f0 so) (fo_E so)
                     (fo_w so ++ [b]) = S P).
    { rewrite -Hpceq /pcount_f (length_app (fo_w so) [b]). cbn [length]. lia. }
    iMod (turn_update v P
            (pcount_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so) (fo_w so))
            (S P) ltac:(lia) with "Ht Hta") as "[Ht Hta]".
    iMod (ps_auth_grow v (fo_ps so) a with "Hps") as "[Hps #Hpslb2]".
    iModIntro. iSplitR "Ht".
    - rewrite /fecl. iRight.
      iExists v, vf, (MkFO (fo_ps so ++ [a]) (fo_cs so) (fo_E so)
                        (fo_w so ++ [b]) (fo_f0 so)).
      cbn [fo_ps fo_cs fo_E fo_w fo_f0]. rewrite Hpc2.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      iFrame "Hpin Hfp Hta Hcs Hps HE Hdl Hf0 Hty0". iPureIntro.
      apply (fecl_pure_out k ho so
               (MkFO (fo_ps so ++ [a]) (fo_cs so) (fo_E so)
                  (fo_w so ++ [b]) (fo_f0 so)) CH b);
        [cbn [fo_cs]; lia | reflexivity | | | | exact Hall0].
      + rewrite /feout_pure. cbn [fo_ps fo_cs fo_E fo_w fo_f0]. split_and!.
        * rewrite Hacc HD. by rewrite app_assoc.
        * apply fop_prefix_snoc_lookup.
          { etrans; [exact Hwpre |]. rewrite /pending_f.
            by apply pending_at_f_ps_mono; eexists. }
          { rewrite /pending_f HlenE. exact Hpendb. }
        * exact Hidx.
        * exact Hbyte.
        * rewrite Forall_app.
          split; [exact Hpsb | by rewrite Forall_singleton].
        * apply (pro_pin_f_mono (fo_ps so) (fo_ps so ++ [a]));
            [by eexists | exact Hpinf].
        * exact Hcsb'.
        * exact Hdsc.
        * exact Hpre1.
        * exact Hpre2.
        * exact Hpre3.
        * split; [rewrite Hf0eq; discriminate |].
          intros [_ Hq]. exfalso.
          by destruct (app_eq_nil (fo_w so) [b] Hq) as [_ Hb2].
        * exact Hfok0.
      + apply (cs_len_ok_f_write
                 (MkFO (fo_ps so ++ [a]) (fo_cs so) (fo_E so) (fo_w so)
                    (fo_f0 so)) b); [exact Hcsl | exact Hcase].
      + apply (ps_len_ok_f_pro so a b);
          [ rewrite /ps_round_f HlenE; exact HRle
          | rewrite /ps_round_f HlenE; exact Hndps
          | rewrite /pending_f HlenE Hweq; by rewrite -Hpseq
          | exact (conj HpsA HpsB) ].
    - iLeft. rewrite -Hpseq. iFrame "Ht Hpslb2 Hcslb Hilb Hf0lb".
  Qed.

  (* ---- THE READ.  [EchoOut.ein_read_pure]'s twin, then the step. ---- *)
  Lemma fein_read_pure (k : nat) (pops : list log_entry)
      (dl ws : list (list mobs * bv 8)) (cs0 : list nat) :
    read_ok pops dl ws -> fein_pure k pops dl cs0 ->
    (dl ++ ws) `prefix_of` echoed pops
    /\ fein_pure k pops (dl ++ ws) cs0
    /\ (nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat.
  Proof using .
    intros Hread (Hlog & Hdisc & Hstamp & Hdlp & Hidx & Hbyte & Hbnd).
    assert (Hnoer : forall e, e ∈ pops -> cons_erase (le_byte e) = false).
    { intros e He. eapply disc_seg_f_no_erase; [by apply Hdisc |].
      apply open_seg_ends_in. by apply (proj1 (proj1 Hlog e He)). }
    assert (Hpref : (dl ++ ws) `prefix_of` echoed pops)
      by (eapply read_window_prefix;
          [exact Hlog | exact Hread | exact Hnoer | exact Hdlp]).
    split; [exact Hpref |]. split.
    - rewrite /fein_pure. split_and!;
        [exact Hlog | exact Hdisc | exact Hstamp | exact Hpref | exact Hidx
         | exact Hbyte | exact Hbnd].
    - etrans; [| exact Hbnd]. apply nlines_prefix, epu_fmap_prefix, Hpref.
  Qed.

  Lemma cs_lb_weaken (v : era_pins) (l l' : list nat) :
    l' `prefix_of` l -> cs_lb v l -∗ cs_lb v l'.
  Proof using .
    intros Hp. rewrite /cs_lb. iIntros "H".
    iApply (own_mono with "H"). by apply mono_list_lb_mono.
  Qed.

  (* THE CHOICE LIST A READER EXPORTS IS THE ONE ITS OWN INPUT NAMES.  The
     claim's list may run past the window's far end, and [alts_pre] ties
     every entry to the line at its index -- so what the reader gets is the
     claim's list TRUNCATED to its own line count.  With [EchoOut]'s
     input-free [Forall (fun c => c < 4) cs] there was nothing to truncate. *)
  Lemma fecl_step_read (k : nat) (v : era_pins) (n : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (ws : list (list mobs * bv 8)) :
    read_ok (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH) ws ->
    era_pin (fgn_echo g) k v -∗ dl_cnt v (1/2) n -∗ fecl k ho CH ==∗
      fecl k ho (ConsLog.cons_step CH (ConsLog.EvRead ws))
      ∗ ((file_taint (fgn_cl g) ∗ dl_cnt v (1/2) n)
         ∨ dl_cnt v (1/2) (n + length ws)%nat
           ∗ ⌜length (LogEntryDefs.ch_dl CH) = n⌝
           ∗ ⌜(LogEntryDefs.ch_dl CH ++ ws)
              `prefix_of` echoed (LogEntryDefs.ch_log CH)⌝
           ∗ ⌜E_index (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ ⌜E_disc_f (seg_of (echoed (LogEntryDefs.ch_log CH)))⌝
           ∗ inp_lb v (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
           ∗ ⌜disc_input_f (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ (cs0 ps0 : list nat) (vf : file_era) (s0 : fst),
                  cs_lb v cs0 ∗ ps_lb v ps0
                  ∗ file_era_pin k vf ∗ f0_lb vf s0
                  ∗ ⌜(nlines (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                      <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (proc_before_f ps0 cs0 (Some s0)
                                 (snd <$> (LogEntryDefs.ch_dl CH ++ ws))))
                  ∗ ⌜rd_stage_f ps0 cs0
                       (snd <$> (LogEntryDefs.ch_dl CH ++ ws))⌝)).
  Proof using .
    intros Hread. iIntros "#Hpinr Hdlr Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. iSplitR; [rewrite /fecl; by iLeft |]. iLeft. by iFrame "Hdlr". }
    iDestruct "Hp" as (v2 vf so)
      "(#Hpin & #Hfp & Hta & Hcs & Hps & HE & Hdl & Hf0 & #Hty0 & %Hall)".
    iDestruct (era_pin_agree with "Hpin Hpinr") as %->.
    iDestruct (dl_cnt_agree with "Hdl Hdlr") as %Hdleq.
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie).
    pose proof Hin as Hin2.
    destruct Hin2 as (_ & _ & _ & _ & Hidx & Hbyte & Hbnd0).
    destruct (fein_read_pure k (LogEntryDefs.ch_log CH) (LogEntryDefs.ch_dl CH)
                ws (fo_cs so) Hread Hin) as (Hpref & Hp' & Hbnd').
    assert (HEpre : (snd <$> (LogEntryDefs.ch_dl CH ++ ws))
                    `prefix_of` (snd <$> fo_E so)).
    { rewrite (fecl_pure_E k ho so CH Hall0) /ch_E.
      etrans; [exact (epu_fmap_prefix snd _ _ Hpref) |].
      rewrite -(seg_of_snd (echoed (LogEntryDefs.ch_log CH))).
      apply epu_fmap_prefix. by apply prefix_app_r. }
    assert (Hdi : disc_input_f (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    { apply (disc_input_f_prefix _ (snd <$> fo_E so) HEpre).
      by destruct Hpure as (_ & _ & _ & Hd & _). }
    pose proof (fecl_pure_rd_stage k ho so CH Hall0) as Hrd.
    pose proof Hrd as (Hpsb & Hcsb' & Hpinf & Hbd).
    (* the reader's own list: the claim's, cut to its own line count *)
    set (Iw := (snd <$> (LogEntryDefs.ch_dl CH ++ ws))).
    set (q := nlines Iw).
    set (csq := take q (fo_cs so)).
    assert (Hqle : (nlines (removelast Iw) <= length csq)%nat).
    { rewrite /csq length_take.
      assert (H1 : (nlines (removelast Iw) <= q)%nat)
        by (apply nlines_prefix, fop_removelast_prefix).
      assert (H2 : (nlines (removelast Iw) <= length (fo_cs so))%nat).
      { etrans; [| exact Hbd].
        apply nlines_prefix, fop_prefix_removelast, HEpre. }
      lia. }
    assert (Hagree : forall j, (j < q)%nat -> csq !!! j = fo_cs so !!! j).
    { intros j Hj. rewrite /csq !list_lookup_total_alt.
      destruct (decide (j < length (fo_cs so))%nat) as [Hl | Hl].
      - rewrite lookup_take; [done | lia].
      - rewrite (lookup_ge_None_2 (fo_cs so) j ltac:(lia)).
        rewrite (lookup_ge_None_2 (take q (fo_cs so)) j);
          [done | rewrite length_take; lia]. }
    assert (Hqbnd : (q <= S (length csq))%nat).
    { rewrite /csq length_take.
      destruct (decide (q <= length (fo_cs so))%nat) as [Hl | Hl]; [lia |].
      rewrite /q /Iw. lia. }
    assert (Hpbq : proc_before_f (fo_ps so) csq (fo_f0 so) Iw
                   = proc_before_f (fo_ps so) (fo_cs so) (fo_f0 so) Iw).
    { apply proc_before_f_ext. intros J HJ Hne.
      apply (pending_at_f_cs_ext (fo_ps so) csq (fo_cs so) (fo_f0 so) J).
      - rewrite /csq. apply prefix_take.
      - etrans; [| exact Hqle].
        apply nlines_prefix, (fop_prefix_of_removelast J Iw HJ Hne). }
    assert (Hrdq : rd_stage_f (fo_ps so) csq Iw).
    { rewrite /rd_stage_f. split_and!; [exact Hpsb | | | exact Hqle].
      - intros i c Hc.
        assert (Hci : fo_cs so !! i = Some c)
          by (rewrite /csq in Hc; by apply lookup_take_Some in Hc as [? _]).
        assert (Hiq : (i < q)%nat).
        { apply lookup_lt_Some in Hc. rewrite /csq length_take in Hc. lia. }
        destruct (Hcsb' i c Hci) as [_ Hok].
        split; [exact Hiq |].
        destruct (bodies_of_prefix Iw (snd <$> fo_E so) HEpre) as [z Hz].
        rewrite Hz !list_lookup_total_alt lookup_app_l in Hok;
          [| rewrite /q /nlines in Hiq; lia].
        by rewrite -!list_lookup_total_alt in Hok.
      - intros q' Hq'.
        assert (Hq'q : (q' <= q)%nat).
        { pose proof (nstarted_le_S Iw). rewrite /q. lia. }
        rewrite (pro_idx_f_ext csq (fo_cs so) q
                   ltac:(intros j Hj; apply Hagree; lia) q' Hq'q).
        apply Hpinf. pose proof (nstarted_prefix Iw (snd <$> fo_E so) HEpre).
        lia. }
    iAssert (f0_auth vf (opt_list (fo_f0 so))
             ∗ (⌜fo_f0 so = None⌝
                ∨ ∃ s1 : fst, ⌜fo_f0 so = Some s1⌝ ∗ f0_lb vf s1))%I
      with "[Hf0]" as "[Hf0 #Hf0w]".
    { destruct (fo_f0 so) as [s1 |] eqn:Hf0; cbn [opt_list].
      - iDestruct (f0_lb_get with "Hf0") as "[Hf0 #Hlb]".
        iFrame "Hf0". iRight. iExists s1.
        iSplitR; [by iPureIntro | iExact "Hlb"].
      - iFrame "Hf0". iLeft. by iPureIntro. }
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (cs_lb_weaken v (fo_cs so) csq ltac:(rewrite /csq; apply prefix_take)
                 with "Hcslb") as "#Hcslbq".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (Elist_lb_get with "HE") as "[HE #HElb]".
    iDestruct (turn_lb_get with "Hta") as "#Htlb".
    iMod (dl_cnt_update v (length (LogEntryDefs.ch_dl CH)) n
            (n + length ws)%nat with "Hdl Hdlr") as "[Hdl Hdlr]".
    (* the reader sees the era's boot state only once it has been filed, and
       a NONEMPTY window means the era has echoed a byte, so it has *)
    iAssert (⌜ws = []⌝ ∨ ⌜exists s0 : fst, fo_f0 so = Some s0⌝)%I as %Hf0c.
    { destruct (decide (ws = [])) as [-> | Hne]; [by iLeft |].
      iRight. destruct (fo_f0 so) as [s0 |] eqn:Hf0; [iPureIntro; by exists s0 |].
      iExFalso. iPureIntro.
      destruct Hpure as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf0n & _).
      destruct (proj1 Hf0n Hf0) as [HEn _]. apply Hne.
      assert (Hz : Iw = []).
      { apply prefix_nil_inv. rewrite /Iw. rewrite HEn fmap_nil in HEpre.
        exact HEpre. }
      rewrite /Iw fmap_app in Hz. apply app_eq_nil in Hz as [_ Hz].
      by apply fmap_nil_inv in Hz. }
    iModIntro. iSplitL "Hta Hcs Hps HE Hdl Hf0".
    { rewrite /fecl. iRight. iExists v, vf, so.
      rewrite /ConsLog.cons_step. cbn [LogEntryDefs.ch_dl].
      rewrite length_app Hdleq. iFrame "Hpin Hfp Hta Hcs Hps HE Hdl Hf0 Hty0".
      iPureIntro. exact (fecl_pure_read k ho so CH ws Hpref Hall0). }
    iRight. iFrame "Hdlr".
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR.
    { iApply (inp_lb_of_lb v (fo_E so) _ HEpre). iExact "HElb". }
    iSplitR; [by iPureIntro |].
    destruct Hf0c as [-> | [s0 Hf0]]; [by iLeft |].
    iRight. iExists csq, (fo_ps so), vf, s0.
    iFrame "Hcslbq Hpslb Hfp".
    iSplitR.
    { iDestruct "Hf0w" as "[%Hn | (%s1 & %Hs1 & Hlb)]".
      - rewrite Hf0 in Hn. discriminate.
      - rewrite Hf0 in Hs1. injection Hs1 as <-. iExact "Hlb". }
    iSplitR; [by iPureIntro |].
    iSplitR.
    { assert (Hle2 : (length (proc_before_f (fo_ps so) csq (Some s0) Iw)
                      <= pcount_f (fo_ps so) (fo_cs so) (fo_f0 so)
                           (fo_E so) (fo_w so))%nat).
      { rewrite /pcount_f -Hf0 Hpbq.
        pose proof (prefix_length _ _
                      (proc_before_f_prefix (fo_ps so) (fo_cs so) (fo_f0 so)
                         Iw (snd <$> fo_E so) HEpre)) as Hlp. lia. }
      iApply (turn_lb_weaken with "Htlb"). exact Hle2. }
    iPureIntro. exact Hrdq.
  Qed.


  (* ---- THE ECHO'S STEP.  [EchoOut.ecl_step_echo] at the file session: the
     discipline's witness is compared with the claim's at ITS OWN boot state
     ([FileOutPure.sessf_prefix_det2]) and the claim's resolution is PADDED
     to a full one first ([FileOutPure.stage_sessf_pad]), because the
     determinacy theorem is stated at an [alts_ok] and the stage's list runs
     one short at a block boundary. ---- *)
  Lemma fecl_step_echo (k : nat) (h : list mobs) (c : bv 8)
      (ho : list mobs) (CH : LogEntryDefs.cons_hist) :
    disc_f h ->
    trace_shape h true ->
    obs_boots h = k ->
    obs_ends_in Uart0 h c ->
    obs_wire Uart0 (open_seg h) `prefix_of` LogEntryDefs.ch_acc CH ->
    (forall e, e ∈ LogEntryDefs.ch_log CH -> hist_ext (le_hist e) h) ->
    (length (echoed (LogEntryDefs.ch_log CH)) < length (ins (open_seg h)))%nat ->
    LogEntryDefs.ch_arm CH = Some (h, c, [echo_of c], 0%nat) ->
    fecl k ho CH ==∗
      fecl k h (ConsLog.cons_step CH (ConsLog.EvByte (echo_of c))).
  Proof using .
    intros Hdisc Hsh Hk Hends Hwire Hord Hlt Harm. subst k.
    iIntros "Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    { iModIntro. rewrite /fecl. by iLeft. }
    iDestruct "Hp" as (v vf so)
      "(#Hpin & #Hfp & Hta & Hcs & Hps & HE & Hdl & Hf0 & #Hty0 & %Hall)".
    pose proof Hall as Hall0.
    destruct Hall as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie).
    destruct Hpure as (Hacc & Hwpre & Hidx & Hbyte & Hpsb & Hpinf & Hcsb' & Hdsc
                       & Hpre1 & Hpre2 & Hpre3 & Hf0n & Hfok0).
    destruct Hin as (Hlog & Hdsc2 & Hstamp & Hdlp & Hidxi & Hbytei & Hbndi).
    assert (Hseg : seg_of (echoed (LogEntryDefs.ch_log CH)) = fo_E so).
    { rewrite HEtie /ch_E Harm ch_arm_E_open app_nil_r. reflexivity. }
    (* the byte's own facts *)
    destruct (disc_seg_f'_open_seg h Hsh Hdisc) as (sd & Hsdok & Hd').
    pose proof (proj1 Hd') as Hdseg.
    pose proof (open_seg_ends_in h c Hends) as Hends'.
    destruct (disc_seg_f'_pt_last sd (open_seg h) c Hd' Hends')
      as (ps' & cs' & Hok' & Hao' & Hlow').
    assert (Hup : obs_wire Uart0 (open_seg h)
                  `prefix_of` (D_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)
                               ++ fo_w so))
      by (rewrite -Hacc; exact Hwire).
    (* the era's boot state HAS been filed: otherwise nothing is on the wire
       and the discipline's own transcript, which begins with a settled
       prologue, would be empty *)
    assert (Hf0ne : fo_f0 so <> None).
    { intros Hn. destruct (proj1 Hf0n Hn) as [HEn Hwn].
      assert (Hacc0 : D_f (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)
                      ++ fo_w so = [])
        by (rewrite HEn Hwn D_f_nil; reflexivity).
      rewrite Hacc0 in Hup. apply prefix_nil_inv in Hup.
      rewrite Hup in Hlow'. apply prefix_nil_inv in Hlow'.
      destruct Hok' as [Hps'b Hlt'].
      exact (sessf_nonnil ps' cs' sd (removelast (ins (open_seg h)))
               Hps'b ltac:(apply pro_done_rounds; lia) Hlow'). }
    (* the stage's resolution, padded to a full one *)
    assert (Hrl : (nlines (removelast (snd <$> fo_E so))
                   <= length (fo_cs so))%nat).
    { pose proof (fecl_pure_rd_stage _ ho so CH Hall0) as (_ & _ & _ & Hb).
      exact Hb. }
    assert (Hlast : (nlines (snd <$> fo_E so) <= length (fo_cs so))%nat
                    \/ fo_w so = []).
    { destruct (cs_len_ok_f_inv so Hcsl) as [[[Hw _] _] | [_ Hq]];
        [by right | left; lia]. }
    set (csP := alts_pad (snd <$> fo_E so) (fo_cs so)).
    destruct (stage_sessf_pad (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)
                (fo_w so) Hcsb' Hrl Hlast Hbyte Hpinf Hwpre)
      as (HokP & HpinP & HDP & HwP & HstP).
    (* the discipline's bound, moved to the claim's own resolution *)
    assert (Hdi1 : disc_input_f (removelast (ins (open_seg h)))).
    { apply (disc_input_f_prefix _ (ins (open_seg h)));
        [apply fop_removelast_prefix | exact Hdseg]. }
    assert (Hbelow : sessf ps' cs' sd (removelast (ins (open_seg h)))
                     `prefix_of` sessf (fo_ps so) csP (f0_st (fo_f0 so))
                       (snd <$> fo_E so)).
    { etrans; [exact Hlow' |]. etrans; [exact Hup |]. exact HstP. }
    destruct (sessf_prefix_det2 (fo_ps so) ps' csP cs'
                (f0_st (fo_f0 so)) sd
                (removelast (ins (open_seg h))) (snd <$> fo_E so)
                Hpsb Hok' HokP Hao' HpinP Hbyte Hdi1 Hfok0 Hsdok Hbelow)
      as (_ & HokPres & Heq).
    assert (Hlow : sessf (fo_ps so) csP (f0_st (fo_f0 so))
                     (removelast (ins (open_seg h)))
                   `prefix_of` obs_wire Uart0 (open_seg h))
      by (rewrite -Heq; exact Hlow').
    (* the same-cycle prefixes of E, and the index facts *)
    assert (Hprefixes : Forall (fun x => ehist x `prefix_of` open_seg h)
                          (fo_E so)).
    { rewrite -Hseg. apply Forall_lookup_2. intros j x Hx.
      rewrite /seg_of list_lookup_fmap in Hx.
      destruct (echoed (LogEntryDefs.ch_log CH) !! j) as [y |] eqn:Hy;
        [| discriminate].
      cbn in Hx. injection Hx as Hx. rewrite -Hx. cbn [Datatypes.fst].
      assert (Hyin : y ∈ echoed (LogEntryDefs.ch_log CH))
        by (by eapply elem_of_list_lookup_2).
      destruct (echoed_elem_inv (LogEntryDefs.ch_log CH) y Hyin)
        as (e & He & _ & Hye).
      apply open_seg_prefix_boots.
      - rewrite -Hye. cbn [Datatypes.fst]. by destruct (Hord e He) as [Hpre _].
      - rewrite -Hye. cbn [Datatypes.fst]. exact (Hstamp e He).
      - exact Hsh. }
    assert (Hpl : forall j x, fo_E so !! j = Some x ->
                    ehist x `prefix_of` open_seg h)
      by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hprefixes Hx)).
    assert (Hoi : length (fo_E so)
                  = length (echoed (LogEntryDefs.ch_log CH)))
      by (by rewrite -Hseg seg_of_length).
    assert (Hbytes : (snd <$> fo_E so)
                     = take (length (fo_E so)) (ins (open_seg h)))
      by (apply (E_bytes_of_hist (fo_E so) (open_seg h) Hidx Hpl); lia).
    assert (Hnew' : forall x, x ∈ fo_E so -> hist_ext (ehist x) (open_seg h)).
    { intros x Hx. apply elem_of_list_lookup in Hx as [jj Hj].
      destruct (Hidx jj x Hj) as [Hxe Hxlen].
      pose proof (Forall_lookup_1 _ _ _ _ Hprefixes Hj) as Hpx.
      apply lookup_lt_Some in Hj.
      split; [exact Hpx |].
      destruct Hpx as [z Hz]. destruct z as [| aa z'].
      - exfalso. rewrite app_nil_r in Hz. rewrite -Hz in Hxlen. lia.
      - rewrite Hz length_app /=. lia. }
    (* F2 at the padded resolution *)
    assert (HupP : obs_wire Uart0 (open_seg h)
                   `prefix_of` (D_f (fo_ps so) csP (fo_f0 so) (fo_E so)
                                ++ fo_w so)) by (rewrite -HDP; exact Hup).
    destruct (D2_next_input_f (fo_ps so) csP (fo_f0 so) (fo_E so) (fo_w so)
                (obs_wire Uart0 (open_seg h)) (open_seg h) c
                (length (ins (open_seg h)))
                Hbyte Hidx Hnew' Hends' eq_refl HwP
                ltac:(rewrite -fop_removelast_take; exact Hlow) HupP)
      as [Hmeq HweqP].
    (* ...and back at the claim's own resolution *)
    assert (Hweq : fo_w so = pending_f (fo_ps so) (fo_cs so) (fo_f0 so)
                     (fo_E so)).
    { destruct (decide (nlines (snd <$> fo_E so) <= length (fo_cs so))%nat)
        as [Hle | Hgt].
      - rewrite HweqP /pending_f /csP.
        symmetry. apply (pending_at_f_cs_ext (fo_ps so) (fo_cs so) csP
                           (fo_f0 so) (snd <$> fo_E so));
          [apply alts_pad_prefix | exact Hle].
      - exfalso.
        destruct (cs_len_ok_f_inv so Hcsl) as [[[Hwn Hr] Hq] | [_ Hq]];
          [| lia].
        assert (HEn : (snd <$> fo_E so) = []).
        { apply (pending_f_nil_inv (fo_ps so) csP (fo_f0 so) (fo_E so));
            [exact (alts_pre_of_alts_ok _ _ HokP) | exact Hr
            | by rewrite -HweqP Hwn]. }
        apply Hf0ne. apply (proj2 Hf0n).
        split; [by apply fmap_nil_inv in HEn | exact Hwn]. }
    assert (HI : removelast (ins (open_seg h)) = (snd <$> fo_E so)).
    { rewrite Hbytes fop_removelast_take.
      replace (length (ins (open_seg h)) - 1)%nat with (length (fo_E so))
        by lia.
      reflexivity. }
    assert (Hrnd : (pro_idx_f (fo_cs so) (nlines (snd <$> fo_E so))
                    < pro_rounds (fo_ps so))%nat).
    { destruct HokPres as [_ Hres]. rewrite HI in Hres.
      rewrite (alts_pad_pro_idx (snd <$> fo_E so) (fo_cs so)
                 (nlines (snd <$> fo_E so)) ltac:(lia)) in Hres.
      exact Hres. }
    (* the two laws at the new entry *)
    assert (Hidx2 : E_index (fo_E so ++ [(open_seg h, c)])).
    { intros jj y Hy.
      destruct (decide (jj < length (fo_E so))%nat) as [Hj | Hj].
      { rewrite lookup_app_l in Hy; [| lia]. by apply Hidx. }
      rewrite lookup_app_r in Hy; [| lia].
      assert (Hjj : jj = length (fo_E so)).
      { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
      subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
      injection Hy as <-. cbn [Datatypes.fst snd].
      split; [exact Hends' | lia]. }
    assert (Hpl2 : forall j x, (fo_E so ++ [(open_seg h, c)]) !! j = Some x ->
                     ehist x `prefix_of` open_seg h).
    { intros jj y Hy.
      destruct (decide (jj < length (fo_E so))%nat) as [Hj | Hj].
      { rewrite lookup_app_l in Hy; [| lia]. exact (Hpl jj y Hy). }
      rewrite lookup_app_r in Hy; [| lia].
      assert (Hjj : jj = length (fo_E so)).
      { apply lookup_lt_Some in Hy. cbn [length] in Hy. lia. }
      subst jj. rewrite Nat.sub_diag in Hy. cbn in Hy.
      injection Hy as <-. cbn [Datatypes.fst]. reflexivity. }
    assert (Hdisc2 : E_disc_f (fo_E so ++ [(open_seg h, c)]))
      by exact (E_disc_f_of_hist _ (open_seg h) Hidx2 Hpl2 Hdseg).
    pose proof (cs_len_ok_f_echo so (open_seg h, c) Hcsb' Hweq Hcsl) as Hcsl2.
    assert (Hpin2 : pro_pin_f (fo_ps so) (fo_cs so) ((snd <$> fo_E so) ++ [c])).
    { intros q Hq. rewrite fop_nstarted_snoc in Hq.
      destruct (decide (q < nstarted (snd <$> fo_E so))%nat) as [Hq2 | Hq2];
        [by apply Hpinf |].
      assert (Hqe : q = nlines (snd <$> fo_E so)).
      { pose proof (nlines_le_nstarted (snd <$> fo_E so)). lia. }
      subst q. exact Hrnd. }
    iMod (Elist_auth_grow v (fo_E so) (open_seg h, c) with "HE")
      as "[HE #HElb2]".
    iModIntro. rewrite /fecl. iRight.
    iExists v, vf,
      (MkFO (fo_ps so) (fo_cs so) (fo_E so ++ [(open_seg h, c)]) []
         (fo_f0 so)).
    cbn [fo_ps fo_cs fo_E fo_w fo_f0].
    rewrite (pcount_f_echo (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)
               (open_seg h, c) (fo_w so) Hweq).
    rewrite ch_dl_byte.
    iFrame "Hpin Hfp Hta Hcs Hps HE Hdl Hf0 Hty0". iPureIntro.
    apply (fecl_pure_byte (obs_boots h) ho h so
             (MkFO (fo_ps so) (fo_cs so) (fo_E so ++ [(open_seg h, c)]) []
                (fo_f0 so))
             CH (echo_of c) h c Harm eq_refl);
      [cbn [fo_cs]; lia | reflexivity | | | | exact Hall0].
    - rewrite /feout_pure. cbn [fo_ps fo_cs fo_E fo_w fo_f0]. split_and!.
      + rewrite Hacc Hweq (D_f_app (fo_ps so) (fo_cs so) (fo_f0 so)
                             (fo_E so) (open_seg h, c)).
        cbn [snd]. by rewrite app_nil_r app_assoc.
      + apply prefix_nil.
      + exact Hidx2.
      + exact Hdisc2.
      + exact Hpsb.
      + rewrite fmap_app. cbn [snd fmap list_fmap]. exact Hpin2.
      + apply (alts_pre_mono (snd <$> fo_E so)); [| exact Hcsb'].
        rewrite fmap_app. by eexists.
      + rewrite Forall_app. split; [exact Hdsc |].
        rewrite Forall_singleton. cbn [Datatypes.fst]. exact Hdseg.
      + rewrite Forall_app. split; [exact Hprefixes |].
        rewrite Forall_singleton. cbn [Datatypes.fst]. reflexivity.
      + rewrite length_app. cbn [length]. lia.
      + by right.
      + split.
        * intros Hq. by destruct (Hf0ne Hq).
        * intros [Hq _]. exfalso.
          by destruct (app_eq_nil (fo_E so) [(open_seg h, c)] Hq) as [_ Hb].
      + exact Hfok0.
    - exact Hcsl2.
    - exact (ps_len_ok_f_echo so (open_seg h, c) Hpsl).
  Qed.


  (* ...AND THE BYTE, which takes NOTHING: the arm is the history's own
     field, and everything the step needs is inside the claim and the
     event's premises ([EchoOut.ecl_step_byte]'s twin). *)
  Lemma fecl_step_byte (k : nat) (ho : list mobs)
      (CH : LogEntryDefs.cons_hist) (b : bv 8) :
    ConsLog.cons_hist_ok CH ->
    ConsLog.cons_ev_ok CH (ConsLog.EvByte b) ->
    fecl k ho CH ==∗ fecl k ho (ConsLog.cons_step CH (ConsLog.EvByte b)).
  Proof using .
    intros Hok Hev. iIntros "Hcl".
    iDestruct (fecl_arm with "Hcl") as "[Hcl [#HT | %Hera]]".
    { iModIntro. rewrite /fecl. by iLeft. }
    pose proof Hev as Hev0.
    destruct Hev0 as (a & Ha & Hlk). destruct a as [[[ha ca] csa] ja].
    cbn [LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Hlk.
    rewrite Ha in Hera. cbn [ch_arm_era_f] in Hera.
    destruct Hera as (Hdseg & Hbts & Hdisc & Hsh & Hw).
    subst ha.
    destruct Hok as [_ Harm]. rewrite Ha in Harm.
    cbn [from_option LogEntryDefs.ca_hist LogEntryDefs.ca_byte
         LogEntryDefs.ca_echo LogEntryDefs.ca_sent] in Harm.
    destruct Harm as (Hends & Hecho & _ & Hord & Hwire).
    assert (Hshape : csa = [echo_of ca] /\ ja = 0%nat /\ b = echo_of ca).
    { destruct Hecho as [Hnil | [Hech | [Herase _]]].
      - exfalso. rewrite Hnil in Hlk. by rewrite lookup_nil in Hlk.
      - rewrite Hech in Hlk.
        destruct ja as [| j']; cbn in Hlk; [| by rewrite lookup_nil in Hlk].
        injection Hlk as <-. by split_and!.
      - exfalso.
        pose proof (disc_seg_f_no_erase (open_seg ho) ca Hdseg
                      (open_seg_ends_in ho ca Hends)) as Hno.
        rewrite Hno in Herase. discriminate. }
    destruct Hshape as (Hcsa & Hja & Hb).
    iDestruct (fecl_lt k ho ca ho CH Hsh Hbts Hends Hord with "Hcl")
      as "[Hcl [#HT | %Hlt]]".
    { iModIntro. rewrite /fecl. by iLeft. }
    subst b. rewrite Hcsa Hja in Ha.
    iApply (fecl_step_echo k ho ca ho CH Hdisc Hsh Hbts Hends Hwire Hord Hlt Ha
              with "Hcl").
  Qed.

  (* ---- THE DRAIN.  [App.Htx] reads the trace property off the claim at the
     end of the run; beside [FileDisc.good_out_f] at the ERA'S OWN boot state
     it hands over that state's DEED WITNESS, which is what the ledger turns
     into [FileDisc.fadm_boot]. ---- *)
  (* WHAT THE DRAIN HANDS THE LEDGER.  Beside the trace fact at the era's
     own boot state and that state's deed witness it hands the ERA PIN and
     a LOWER BOUND of the state, which is how the ledger recognises a later
     drain of the SAME era as the one whose state it already fixed.  The
     lower bound exists because the wire is not empty: a stage that has not
     filed its boot state has written nothing ([feout_pure]'s [o_f0] iff),
     so its accumulator -- and hence the wire -- is empty. *)
  Definition fdrain_ret (k : nat) (seg : list mobs) : iProp Σ :=
    (file_taint (fgn_cl g)
     ∨ ∃ (s0 : fst) (vf : file_era),
         ⌜good_out_f s0 seg⌝ ∗ ⌜fst_ok s0⌝ ∗ f0_typed s0
         ∗ file_era_pin k vf ∗ f0_lb vf s0)%I.

  Lemma fecl_drain (k : nat) (h ho : list mobs) (CH : LogEntryDefs.cons_hist)
      (seg : list mobs) :
    trace_shape h true ->
    obs_boots h = k ->
    ho `prefix_of` h ->
    ins seg = ins (open_seg h) ->
    obs_wire Uart0 seg `prefix_of` LogEntryDefs.ch_acc CH ->
    obs_wire Uart0 seg <> [] ->
    fecl k ho CH -∗ fecl k ho CH ∗ fdrain_ret k seg.
  Proof using .
    intros Hsh Hk Hpre Hins Hwire Hne. subst k. rewrite /fecl /fdrain_ret.
    iIntros "Hcl".
    iDestruct "Hcl" as "[#HT | Hp]".
    - iSplitR; [iLeft; iExact "HT" | iLeft; iExact "HT"].
    - iDestruct "Hp" as (v vf so)
        "(#Hpin & #Hfp & Hta & Hcs & Hps & HE & Hdl & Hf0 & #Hty0 & %Hall)".
      pose proof Hall as Hall2.
      destruct Hall2 as (Hpure & Hcsl & Hpsl & Hin & Hera & HEtie).
      destruct Hpure as (Hacc & Hwp & Hidx & Hbyte & Hpsb & Hpinf & Hcsb' & Hdsc
                         & Hpre1 & Hpre2 & Hpre3 & Hf0n & Hfok0).
      (* the era's boot state IS filed, because the wire is not empty: an
         unfiled stage has written nothing, so its accumulator is empty *)
      assert (Hsome : opt_list (fo_f0 so) = [f0_st (fo_f0 so)]).
      { destruct (fo_f0 so) as [sx |] eqn:Hfx; [reflexivity |].
        exfalso. destruct (proj1 Hf0n eq_refl) as [HE0 Hw0].
        assert (Hz : LogEntryDefs.ch_acc CH = [])
          by (rewrite Hacc HE0 Hw0 D_f_nil; reflexivity).
        apply Hne, prefix_nil_inv. rewrite -Hz. exact Hwire. }
      iEval (rewrite Hsome) in "Hf0".
      iDestruct (f0_lb_get with "Hf0") as "[Hf0 #Hlb]".
      iSplitL "Hta Hcs Hps HE Hdl Hf0".
      { iRight. iExists v, vf, so.
        iFrame "Hpin Hfp Hta Hcs Hps HE Hdl Hty0".
        iSplitL "Hf0"; [rewrite Hsome; iExact "Hf0" | by iPureIntro]. }
      iRight. iExists (f0_st (fo_f0 so)), vf.
      iFrame "Hty0 Hfp Hlb".
      iSplitR; [| by iPureIntro].
      iPureIntro.
      assert (Hbytes : (snd <$> fo_E so) `prefix_of` ins seg).
      { destruct Hpre3 as [HEnil | Hbo].
        - rewrite HEnil fmap_nil. apply prefix_nil.
        - assert (Hpl : forall j x, fo_E so !! j = Some x ->
                          ehist x `prefix_of` open_seg ho)
            by (intros j x Hx; exact (Forall_lookup_1 _ _ _ _ Hpre1 Hx)).
          rewrite (E_bytes_of_hist (fo_E so) (open_seg ho) Hidx Hpl Hpre2).
          etrans; [apply prefix_take |].
          rewrite Hins. apply ins_prefix_of, open_seg_prefix_boots;
            [exact Hpre | by rewrite Hbo | exact Hsh]. }
      apply (good_out_f_of_stage (fo_ps so) (fo_cs so) (fo_f0 so) (fo_E so)
               (fo_w so) seg Hpsb).
      + apply (alts_pre_mono (snd <$> fo_E so)); [exact Hbytes | exact Hcsb'].
      + pose proof (fecl_pure_rd_stage _ ho so CH Hall) as (_ & _ & _ & Hb).
        exact Hb.
      + destruct (cs_len_ok_f_inv so Hcsl) as [[[Hw _] _] | [_ Hq]];
          [by right | left; lia].
      + exact Hbyte.
      + exact Hpinf.
      + exact Hwp.
      + rewrite -Hacc. exact Hwire.
      + exact Hbytes.
  Qed.


  (* ====================================================================== *)
  (*  5.  THE LEDGER                                                        *)
  (*                                                                        *)
  (*  THE ONE HYPOTHESIS THIS FILE TAKES AND DOES NOT DISCHARGE.            *)
  (*  [EchoOut.echo_led]'s taint counter is at [decide (EchoDisc.disc h)],  *)
  (*  and the file ledger's must be at [decide (FileDisc.disc_f h)]: the    *)
  (*  conclusion's antecedent is the FILE discipline, and [disc_f h] does   *)
  (*  not imply [disc h] (a [cat f] line is not an echo line), so echo's    *)
  (*  counter proves nothing here.  [FileDisc.disc_f] is NOT decidable as   *)
  (*  landed -- lane MODEL says so ("[disc_seg_f'] is NOT decidable here")  *)
  (*  -- and the obstacle is not the finite search over resolutions but the *)
  (*  PER-CYCLE BOOT STATE: [disc_f] quantifies [exists s, fst_ok s /\ ...] *)
  (*  over ALL byte lists.  Only [al_rx] needs to DECIDE (every other step  *)
  (*  needs a [decide_ext] over one of [disc_f]'s closure laws), and there  *)
  (*  the ledger must hand out the byte's tag, whose left arm IS the        *)
  (*  discipline.  So the instance is a section hypothesis, named here and  *)
  (*  reported; every result below is a theorem WITH it, not an axiom.      *)
  (* ====================================================================== *)
  Context `{Hdf : forall hh : list mobs, Decision (disc_f hh)}.

  (* the SECOND per-era map, beside [EchoOut.pin_map] *)
  Definition f0_map (h : list mobs) : iProp Σ :=
    (∃ Mf : gmap nat file_era,
       ghost_map_auth (fgn_era g) 1 Mf ∗ ⌜pin_dom Mf (obs_boots h)⌝)%I.

  Global Instance f0_map_timeless h : Timeless (f0_map h).
  Proof using . rewrite /f0_map. apply _. Qed.

  Lemma f0_map_step (h : list mobs) (e : mobs) :
    obs_boots [e] = 0%nat -> f0_map h -∗ f0_map (h ++ [e]).
  Proof using .
    intros He. rewrite /f0_map obs_boots_app He Nat.add_0_r. by iIntros "$".
  Qed.

  Lemma f0_map_on (h : list mobs) (vf : file_era) :
    f0_map h ==∗
      f0_map (h ++ [ObsPowerOn]) ∗ file_era_pin (S (obs_boots h)) vf.
  Proof using .
    rewrite /f0_map /file_era_pin obs_boots_app. cbn [obs_boots].
    rewrite Nat.add_1_r.
    iIntros "H". iDestruct "H" as (Mf) "[Hm %Hd]".
    iMod (ghost_map_insert_persist (S (obs_boots h)) vf
            (pin_dom_absent _ _ Hd) with "Hm") as "[Hm #Hpin]".
    iModIntro. iFrame "Hpin". iExists _. iFrame "Hm".
    iPureIntro. by apply pin_dom_insert.
  Qed.

  (* ---- the history's own line list moves ---- *)

  Lemma efl_of_io (h : list mobs) (e : mobs) :
    trace_shape h true -> is_io e = true -> ins [e] = [] ->
    efl_of (h ++ [e]) = efl_of h.
  Proof using .
    intros Hsh Hio Hin.
    destruct (cycles_of_io h [e] Hsh (io_singleton e Hio)) as (cs & H1 & H2).
    rewrite /efl_of /echof_lines_of H1 H2 !fmap_app !concat_app.
    f_equal. cbn [fmap list_fmap concat].
    rewrite /echof_cyc ins_app Hin (app_nil_r (ins (open_seg h))).
    reflexivity.
  Qed.

  Lemma efl_of_out (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true -> efl_of (h ++ [ObsUartOut i b]) = efl_of h.
  Proof using .
    intros Hsh. apply efl_of_io; [exact Hsh | by destruct i | by destruct i].
  Qed.

  Lemma efl_of_power (h : list mobs) (on : bool) :
    efl_of (h ++ [if on then ObsPowerOff else ObsPowerOn]) = efl_of h.
  Proof using .
    rewrite /efl_of /echof_lines_of. destruct on.
    - by rewrite cycles_of_off.
    - rewrite cycles_of_on fmap_app concat_app.
      cbn [fmap list_fmap concat]. rewrite /echof_cyc.
      rewrite (_ : ins [] = []); [| reflexivity].
      rewrite /echof_lines_in /lines_of bodies_of_nil fmap_nil.
      by rewrite !app_nil_r.
  Qed.

  (* ---- THE ERA'S PIN IN THE LEDGER.
         The OPEN cycle's entry of [s0s] is PROVISIONAL until the era's
         first drain: [None] is admissible against any line set and an
         empty cycle is [good_out_f] at any state, so the power step parks
         [None] there and the first drain REPLACES it.  What makes the
         replacement sound is that from that drain on the ledger keeps the
         drain's own LOWER BOUND of the era's boot state, so every later
         drain of the same era hands back the same state ([f0_lb_agree]).
         The condition -- has this cycle put anything on the console's
         wire? -- is PURE and reads the history alone. ---- *)
  Definition f0_pinned (h : list mobs) (s0s : list fst) : iProp Σ :=
    (if decide (obs_wire Uart0 (open_seg h) = [])
     then emp
     else ∃ (vf : file_era) (s0 : fst),
            ⌜exists u1, s0s = u1 ++ [s0]⌝ ∗ file_era_pin (obs_boots h) vf
            ∗ f0_lb vf s0)%I.

  Global Instance f0_pinned_persistent h s0s : Persistent (f0_pinned h s0s).
  Proof using . rewrite /f0_pinned. case_decide; apply _. Qed.
  Global Instance f0_pinned_timeless h s0s : Timeless (f0_pinned h s0s).
  Proof using . rewrite /f0_pinned. case_decide; apply _. Qed.

  (* before the era's first drain there is nothing to keep *)
  Lemma f0_pinned_undrained (h : list mobs) (s0s : list fst) :
    obs_wire Uart0 (open_seg h) = [] -> ⊢ f0_pinned h s0s.
  Proof using .
    intro Hw. rewrite /f0_pinned decide_True; [| exact Hw]. by iIntros "".
  Qed.

  (* an event that puts nothing on the console's wire moves neither the
     condition nor the era *)
  Lemma f0_pinned_io (h : list mobs) (e : mobs) (s0s : list fst) :
    is_io e = true -> obs_wire Uart0 [e] = [] ->
    f0_pinned h s0s -∗ f0_pinned (h ++ [e]) s0s.
  Proof using .
    intros Hio Hw. rewrite /f0_pinned.
    rewrite (open_seg_io h [e] (proj2 (Forall_singleton _ _) Hio)).
    rewrite obs_wire_app Hw app_nil_r.
    rewrite obs_boots_app (obs_boots_io [e] (proj2 (Forall_singleton _ _) Hio)).
    rewrite Nat.add_0_r. by iIntros "$".
  Qed.

  (* ...and the drain's two halves: reading the state the ledger fixed, and
     fixing it *)
  Lemma f0_pinned_drained (h : list mobs) (s0s : list fst) (vf : file_era)
      (s0 : fst) :
    obs_wire Uart0 (open_seg h) <> [] ->
    file_era_pin (obs_boots h) vf -∗ f0_lb vf s0 -∗ f0_pinned h s0s -∗
      ⌜exists u1, s0s = u1 ++ [s0]⌝.
  Proof using .
    intro Hw. rewrite /f0_pinned decide_False; [| exact Hw].
    iIntros "#Hfp #Hlb Hp".
    iDestruct "Hp" as (vf' s0') "(%Hl & #Hfp' & #Hlb')".
    iDestruct (file_era_pin_agree with "Hfp Hfp'") as %<-.
    iDestruct (f0_lb_agree with "Hlb Hlb'") as %<-.
    by iPureIntro.
  Qed.

  Lemma f0_pinned_drain (h : list mobs) (b : bv 8) (u1 : list fst)
      (vf : file_era) (s0 : fst) :
    file_era_pin (obs_boots h) vf -∗ f0_lb vf s0 -∗
      f0_pinned (h ++ [ObsUartOut Uart0 b]) (u1 ++ [s0]).
  Proof using .
    iIntros "#Hfp #Hlb". rewrite /f0_pinned.
    rewrite obs_boots_app
      (obs_boots_io [ObsUartOut Uart0 b]
         (proj2 (Forall_singleton _ _)
            (eq_refl : is_io (ObsUartOut Uart0 b) = true))) Nat.add_0_r.
    rewrite (open_seg_io h [ObsUartOut Uart0 b]
               (proj2 (Forall_singleton _ _)
                  (eq_refl : is_io (ObsUartOut Uart0 b) = true))).
    rewrite decide_False; last first.
    { rewrite obs_wire_app (_ : obs_wire Uart0 [ObsUartOut Uart0 b] = [b]);
        [| reflexivity].
      intros Hz. apply (f_equal length) in Hz.
      rewrite length_app in Hz. cbn [length] in Hz. lia. }
    iExists vf, s0. iFrame "Hfp Hlb". iPureIntro. by exists u1.
  Qed.

  (* ---- THE CONCLUSION'S PURE CARRIER.
         [FileDisc.file_phi] VERBATIM, its antecedent included: that is what
         lets the era's boot state be fixed at the era's FIRST drain, where
         the cycle has typed nothing ([FileOutPure.efl_of_first_out]).
         [disc_f] is prefix-closed ([disc_f_prefix]), so every step below
         assumes the NEW history's discipline and reads the old one's
         witnesses off it. ---- *)
  Definition file_phi_res (h : list mobs) : iProp Σ :=
    (∃ s0s : list fst,
       ⌜disc_f h -> file_phi_body h s0s⌝ ∗ f0_pinned h s0s)%I.

  Global Instance file_phi_res_timeless h : Timeless (file_phi_res h).
  Proof using . rewrite /file_phi_res. apply _. Qed.

  (* ...AND THE WHOLE LEDGER, which is what the record's [app_R] becomes. *)
  Definition file_led (h : list mobs) : iProp Σ :=
    (mono_nat_auth_own (eg_taint (fgn_echo g)) 1
       (if decide (disc_f h) then 0%nat else 1%nat)
     ∗ pin_map (fgn_echo g) h
     ∗ f0_map h
     ∗ fl_auth (fgn_cl g) (efl_of h)
     ∗ (file_phi_res h ∨ file_taint (fgn_cl g)))%I.

  Global Instance file_led_timeless h : Timeless (file_led h).
  Proof using . rewrite /file_led. apply _. Qed.

  (* the birth's yield *)
  Definition file_cl_all : iProp Σ :=
    (file_cl (fgn_cl g)
     ∗ ghost_map_auth (fgn_era g) 1 (∅ : gmap nat file_era))%I.

  Lemma file_led_init : file_cl_all -∗ file_led [].
  Proof using .
    rewrite /file_cl_all /file_cl /echo_cl /file_led /pin_map /f0_map.
    iIntros "[[[Ht Hm] Hfl] Hmf]".
    rewrite decide_True; [| exact disc_f_nil].
    rewrite (_ : efl_of [] = []); last first.
    { rewrite /efl_of /echof_lines_of /cycles_of /cycles_rev /=. reflexivity. }
    iFrame "Ht Hfl".
    iSplitL "Hm"; [iExists ∅; iFrame "Hm"; iPureIntro; apply pin_dom_empty |].
    iSplitL "Hmf"; [iExists ∅; iFrame "Hmf"; iPureIntro; apply pin_dom_empty |].
    iLeft. iExists []. iSplitR.
    { iPureIntro. intros _. exact file_phi_body_nil. }
    iApply f0_pinned_undrained. reflexivity.
  Qed.


  (* ---- THE FOUNDING, as a resource split: the era's ghosts become the
         port's claim at the start of their era and init's credential ---- *)
  Lemma file_era_split (k : nat) (v : era_pins) (vf : file_era) :
    era_pin (fgn_echo g) k v -∗ file_era_pin k vf -∗
    era_full v -∗ f0_auth vf [] -∗
      fecl k [] (LogEntryDefs.MkCH [] [] [] None) ∗ fturn k.
  Proof using .
    iIntros "#Hpin #Hfp (Ht & Hcs & Hps & HE & Hdl) Hf0".
    iEval (rewrite -Qp.half_half) in "Ht".
    iDestruct "Ht" as "[Ht1 Ht2]".
    iEval (rewrite -Qp.half_half) in "Hdl".
    iDestruct (ghost_var_split with "Hdl") as "[Hdl1 Hdl2]".
    iDestruct (cs_lb_get with "Hcs") as "[Hcs #Hcslb]".
    iDestruct (ps_lb_get with "Hps") as "[Hps #Hpslb]".
    iDestruct (Elist_lb_get with "HE") as "[HE #HElb]".
    iSplitL "Ht1 Hcs Hps HE Hdl1 Hf0".
    { rewrite /fecl. iRight. iExists v, vf, fostage0.
      cbn [fo_ps fo_cs fo_E fo_w fo_f0 fostage0 opt_list
           LogEntryDefs.ch_dl length].
      rewrite (_ : pcount_f [] [] None [] [] = 0%nat); [| reflexivity].
      iFrame "Hpin Hfp Ht1 Hcs Hps HE Hdl1 Hf0".
      rewrite (_ : f0_st None = None); [| reflexivity].
      iSplitR; [by rewrite /f0_typed |]. iPureIntro.
      rewrite /fecl_pure.
      cbn [LogEntryDefs.ch_acc LogEntryDefs.ch_log LogEntryDefs.ch_dl
           LogEntryDefs.ch_arm].
      split_and!.
      - exact (feout_pure_0 k []).
      - exact cs_len_ok_f_0.
      - exact ps_len_ok_f_0.
      - exact (fein_pure_0 k).
      - by cbn [ch_arm_era_f].
      - rewrite /ch_E. cbn [LogEntryDefs.ch_log LogEntryDefs.ch_arm ch_arm_E].
        rewrite app_nil_r echoed_nil /seg_of fmap_nil. reflexivity. }
    rewrite /fturn. iExists v, vf. iFrame "Hpin Hfp Ht2 Hdl2 Hcslb Hpslb".
    iApply (inp_lb_of_lb v [] []); [apply prefix_nil | iExact "HElb"].
  Qed.

  (* THE POWER STEP: the on-arm allocates BOTH per-era records, mints both
     pins, and splits the ghosts into the era's claim and init's credential. *)
  Lemma file_led_pow (h : list mobs) (on : bool) :
    file_led h ==∗
      file_led (h ++ [if on then ObsPowerOff else ObsPowerOn])
      ∗ (if on then emp
         else fecl (S (obs_boots h)) [] (LogEntryDefs.MkCH [] [] [] None)
              ∗ fturn (S (obs_boots h))).
  Proof using .
    iIntros "(Ht & Hpm & Hfm & Hfl & Hphi)". rewrite /file_led.
    rewrite (decide_ext _ (disc_f h) 0%nat 1%nat (disc_f_power h on)).
    rewrite (efl_of_power h on).
    destruct on.
    - iDestruct (pin_map_step (fgn_echo g) h ObsPowerOff eq_refl with "Hpm")
        as "Hpm".
      iDestruct (f0_map_step h ObsPowerOff eq_refl with "Hfm") as "Hfm".
      iModIntro. iSplitR ""; [| done]. iFrame "Ht Hpm Hfm Hfl".
      iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
      iLeft. iDestruct "Hphi" as (s0s) "[%Hb _]". iExists s0s. iSplitR.
      { iPureIntro. intros Hd.
        exact (file_phi_body_off h s0s
                 (Hb (proj1 (disc_f_power h true) Hd))). }
      iApply f0_pinned_undrained.
      by rewrite (open_seg_power h ObsPowerOff eq_refl).
    - iMod era_full_alloc as (v) "Hfull".
      iMod f0_alloc as (vf) "Hf0".
      iMod (pin_map_on (fgn_echo g) h v with "Hpm") as "[Hpm #Hpin]".
      iMod (f0_map_on h vf with "Hfm") as "[Hfm #Hfp]".
      iDestruct (file_era_split (S (obs_boots h)) v vf
                   with "Hpin Hfp Hfull Hf0") as "(Hcl & Hturn)".
      iModIntro. iSplitR "Hcl Hturn".
      + iFrame "Ht Hpm Hfm Hfl".
        iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
        iLeft. iDestruct "Hphi" as (s0s) "[%Hb _]".
        iExists (s0s ++ [None]). iSplitR.
        { iPureIntro. intros Hd.
          exact (file_phi_body_on h s0s
                   (Hb (proj1 (disc_f_power h false) Hd))). }
        iApply f0_pinned_undrained.
        by rewrite (open_seg_power h ObsPowerOn eq_refl).
      + iFrame "Hcl Hturn".
  Qed.


  (* the deed's typed witness, read against the ledger's own line list *)
  Lemma f0_typed_adm (Ls : list wordline) (s0 : fst) :
    fl_auth (fgn_cl g) Ls -∗ f0_typed s0 -∗
      fl_auth (fgn_cl g) Ls ∗ ⌜fadm_boot Ls s0⌝.
  Proof using .
    iIntros "Ha Hty". destruct s0 as [bs |]; last first.
    { iFrame "Ha". iPureIntro. by left. }
    rewrite /f0_typed. iDestruct "Hty" as (ls) "[Hlb %Hbt]".
    iDestruct (fl_lb_prefix with "Ha Hlb") as %Hpre.
    iFrame "Ha". iPureIntro. right.
    destruct (f_bytes_typed_mono ls Ls bs Hpre Hbt)
      as (ws & sel & Hin & _ & Hsel & ->).
    by exists ws, sel.
  Qed.

  (* THE OUTPUT STEP, AND THE ERA'S FIRST DRAIN.
     The drain hands over the era's boot state [s0], its deed witness, and
     a LOWER BOUND of the state pinned to the era's record.  If the cycle
     has not yet put a byte on the console's wire then this is the era's
     FIRST drain: the entry the ledger parked at the power step was
     provisional, and it is replaced by [s0] -- whose admissibility comes
     out of the witness read against the ledger's own line list, which at
     that moment IS the list of lines typed in strictly earlier cycles
     ([FileOutPure.efl_of_first_out]; at cycle 0 that list is empty and the
     same reading refutes [f0_typed]'s [Some] arm, which is
     [FileDisc.file_phi]'s guarded first clause).  If the cycle HAS
     drained, the handed bound agrees with the one already kept
     ([f0_pinned_drained]), so the entry does not move and the body simply
     extends by the drain's own [good_out_f]. *)
  Lemma file_led_tx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    (file_taint (fgn_cl g)
     ∨ (match i with
        | Uart0 => ∃ (s0 : fst) (vf : file_era),
                     ⌜good_out_f s0 (open_seg h ++ [ObsUartOut Uart0 b])⌝
                     ∗ f0_typed s0 ∗ file_era_pin (obs_boots h) vf
                     ∗ f0_lb vf s0
        | _ => True
        end)) -∗
    file_led h ==∗ file_led (h ++ [ObsUartOut i b]).
  Proof using .
    intros Hsh. iIntros "Hgo (Ht & Hpm & Hfm & Hfl & Hphi)".
    iDestruct (pin_map_step (fgn_echo g) h (ObsUartOut i b) eq_refl
                 with "Hpm") as "Hpm".
    iDestruct (f0_map_step h (ObsUartOut i b) eq_refl with "Hfm") as "Hfm".
    rewrite /file_led.
    rewrite (decide_ext _ (disc_f h) 0%nat 1%nat (disc_f_out h i b Hsh)).
    rewrite (efl_of_out h i b Hsh).
    iFrame "Ht Hpm Hfm".
    iDestruct "Hphi" as "[Hphi | HT]"; last first.
    { iModIntro. iFrame "Hfl". by iRight. }
    iDestruct "Hphi" as (s0s) "[%Hb #Hpin0]".
    destruct i; last first.
    { iModIntro. iFrame "Hfl". iLeft. iExists s0s. iSplitR.
      { iPureIntro. intros Hd.
        apply (file_phi_body_step_io h (ObsUartOut Uart1 b) s0s Hsh eq_refl
                 eq_refl), Hb.
        exact (proj1 (disc_f_out h Uart1 b Hsh) Hd). }
      iApply (f0_pinned_io h (ObsUartOut Uart1 b) s0s eq_refl eq_refl
                with "Hpin0"). }
    iDestruct "Hgo" as "[#HT | Hgo]".
    { iModIntro. iFrame "Hfl". by iRight. }
    iDestruct "Hgo" as (s0 vf) "(%Hgo & #Hty & #Hfp & #Hlb)".
    iDestruct (f0_typed_adm (efl_of h) s0 with "Hfl Hty") as "[Hfl %Hadm]".
    iAssert (⌜obs_wire Uart0 (open_seg h) <> [] ->
               exists u1, s0s = u1 ++ [s0]⌝)%I as "%Hlast".
    { destruct (decide (obs_wire Uart0 (open_seg h) = [])) as [Hw | Hw].
      - iPureIntro. intro Hne. by destruct (Hne Hw).
      - iDestruct (f0_pinned_drained h s0s vf s0 Hw with "Hfp Hlb Hpin0")
          as %Hl. iPureIntro. by intros _. }
    iModIntro. iFrame "Hfl". iLeft.
    iExists (removelast s0s ++ [s0]). iSplitR; last first.
    { iApply (f0_pinned_drain h b (removelast s0s) vf s0 with "Hfp Hlb"). }
    iPureIntro. intros Hd.
    exact (file_phi_body_drain h b s0s s0 Hsh
             (proj1 (disc_f_out h Uart0 b Hsh) Hd) Hgo Hadm Hlast
             (Hb (proj1 (disc_f_out h Uart0 b Hsh) Hd))).
  Qed.

  (* the line list grows by whatever the new input completed *)
  Lemma fl_auth_grow_pre (ls ls' : list wordline) :
    ls `prefix_of` ls' ->
    fl_auth (fgn_cl g) ls ==∗
      fl_auth (fgn_cl g) ls' ∗ fl_lb (fgn_cl g) ls'.
  Proof using .
    intros Hp. rewrite /fl_auth. iIntros "Ha".
    iMod (own_update _ _ (●ML (ls' : list (leibnizO wordline))) with "Ha")
      as "Ha".
    { apply mono_list_update. by destruct Hp as [z ->]; exists z. }
    iModIntro. iApply (fl_auth_lb with "Ha").
  Qed.

  Lemma file_led_rx (h : list mobs) (i : uart_id) (b : bv 8) :
    trace_shape h true ->
    file_led h ==∗
      file_led (h ++ [ObsUartIn i b]) ∗ ftag (h ++ [ObsUartIn i b]).
  Proof using .
    intros Hsh. iIntros "(Hcnt & Hpm & Hfm & Hfl & Hphi)".
    iDestruct (pin_map_step (fgn_echo g) h (ObsUartIn i b) eq_refl
                 with "Hpm") as "Hpm".
    iDestruct (f0_map_step h (ObsUartIn i b) eq_refl with "Hfm") as "Hfm".
    iMod (fl_auth_grow_pre (efl_of h) (efl_of (h ++ [ObsUartIn i b]))
            (echof_lines_of_snoc h (ObsUartIn i b)) with "Hfl")
      as "[Hfl #Hfllb]".
    iAssert (file_phi_res (h ++ [ObsUartIn i b]) ∨ file_taint (fgn_cl g))%I
      with "[Hphi]" as "Hphi".
    { iDestruct "Hphi" as "[Hphi | HT]"; [| by iRight].
      iLeft. iDestruct "Hphi" as (s0s) "[%Hb #Hp]".
      iExists s0s. iSplitR.
      - iPureIntro. intros Hd.
        apply (file_phi_body_step_io h (ObsUartIn i b) s0s Hsh
                 ltac:(by destruct i) ltac:(by destruct i)), Hb.
        destruct i;
          [ exact (disc_f_in h b Hsh Hd)
          | exact (proj1 (disc_f_other h (ObsUartIn Uart1 b) eq_refl I Hsh)
                     Hd) ].
      - iApply (f0_pinned_io h (ObsUartIn i b) s0s ltac:(by destruct i)
                  ltac:(by destruct i) with "Hp"). }
    assert (Hsh' : trace_shape (h ++ [ObsUartIn i b]) true)
      by (eapply trace_shape_snoc; [exact Hsh | reflexivity]).
    rewrite /file_led /ftag.
    destruct (decide (disc_f (h ++ [ObsUartIn i b]))) as [Hd' | Hd'].
    - rewrite decide_True; last first.
      { destruct i;
          [ exact (disc_f_in h b Hsh Hd')
          | exact (proj1 (disc_f_other h (ObsUartIn Uart1 b) eq_refl I Hsh)
                     Hd') ]. }
      iModIntro. iFrame "Hcnt Hpm Hfm Hfl Hphi Hfllb".
      iSplitR; [by iPureIntro |]. iLeft. by iPureIntro.
    - iMod (mono_nat_own_update 1%nat with "Hcnt") as "[Hcnt #Hlb]";
        [destruct (decide (disc_f h)); lia |].
      iModIntro. iFrame "Hcnt Hpm Hfm Hfl Hphi Hfllb".
      iSplitR; [by iPureIntro |]. iRight. rewrite /file_taint /echo_taint.
      iExact "Hlb".
  Qed.

  (* PHI's read at the end of the run, in the owner's form: the guard is the
     WHOLE history's discipline. *)
  Lemma file_led_phi (h : list mobs) :
    file_led h -∗ ⌜file_phi h⌝.
  Proof using .
    iIntros "(Hcnt & _ & _ & _ & [Hphi | HT'])".
    { iDestruct "Hphi" as (s0s) "[%Hb _]". iPureIntro.
      exact (file_phi_of_body h s0s Hb). }
    rewrite /file_taint /echo_taint.
    iDestruct (mono_nat_lb_own_valid with "Hcnt HT'") as %[_ Hle].
    iPureIntro. rewrite /file_phi. intros Hd. exfalso.
    rewrite decide_True in Hle; [| exact Hd]. lia.
  Qed.

End file_out.

(* ====================================================================== *)
(*  6.  THE BIRTH STEP                                                     *)
(*                                                                        *)
(*  [AppFile.file_birth] beside one more [ghost_map_alloc]: the record's   *)
(*  fixed part is AppFile's paired with the file era map's gname.          *)
(* ====================================================================== *)
Section file_birth.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  Lemma file_birth_all : ⊢ |==> ∃ g : file_gn, file_cl_all g.
  Proof using .
    iMod file_birth as (c) "Hc".
    iMod (ghost_map_alloc (∅ : gmap nat file_era)) as (ge) "[Hm _]".
    iModIntro. iExists (MkFileGn c ge). rewrite /file_cl_all /=.
    iFrame "Hc Hm".
  Qed.
End file_birth.
