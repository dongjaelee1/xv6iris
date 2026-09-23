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
(*  the stage's state ([gwa_agree]) and a filed state hands [gW] out     *)
(*  again to the read and the drain ([gwa_W]).  The FILING law (the      *)
(*  era's first process byte files the state out of the boot evidence   *)
(*  and yields [gW]) joins the record with the head step.                *)
(*                                                                       *)
(*  This cut: the claim, and the steps that take nothing (the taint's   *)
(*  supply, the close, the open, the arm).                               *)
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
}.
Global Arguments MkGWA {Σ _ M G sd}.
Global Arguments gwa {Σ _ M G sd} _ _ _.
Global Arguments gwa_tl {Σ _ M G sd} _ _ _.
Global Arguments gwa_agree {Σ _ M G sd} _ _ _ _.
Global Arguments gwa_W {Σ _ M G sd} _ _ _.
Global Existing Instance gwa_tl.

Section gen_out.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (M : lmodel) (G : gen_params M) (B : lm_byte_laws M) (sd : lm_st M).
  Context (A : gen_wa M G sd).

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
End gen_out.
