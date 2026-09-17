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
  Lemma f0_lb_agree (v : file_era) (f0 : option fst) (s : fst) :
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
    iDestruct (f0_lb_agree with "Hf0 Hf0lb") as %Hf0eq.
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
    iDestruct (f0_lb_agree with "Hf0 Hf0lb") as %Hf0eq.
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

End file_out.
