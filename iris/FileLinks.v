(* FileLinks.v -- THE FILE APPLICATION'S CONSOLE LINKS.

   Design of record: claude-notes/design/app-file.md section 4, deliverable
   3.  [EchoOut.v]'s [Section echo_links] at the file claim: the same links
   wrapped onto the kernel's own console contracts, with the era's BOOT FILE
   STATE beside the three bounds a writer already carried, and the era's
   FIRST byte -- which files that state out of the deed's own typed witness
   -- as a link of its own.

   A link runs at [⊤ ∖ ↑uartN Uart0] and opens NOTHING but the port
   invariant: every authority an era has is in the claim the link is handed,
   so no link reaches the application's ledger and [App.al_echo] stays a
   CLOSED entailment, exactly as for the echo application. *)
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
Require Import EchoOut.
Require Import AppFile.
Require Import FileOut.
Require Import LineModel.
Require Import LineModelLinks.
Require Import LineModelInst.
Require Import FileHooks.
Require Import GenOutPure.
Require Import GenOutHist.
Require Import GenOut.
Require Import GenLinks.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import SpecConsoleintr.
Local Open Scope list_scope.

Section file_links.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.

  (* the record equations, as section parameters: [App.al_echo] hands them
     over at the [boot_fixedGS] literal *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = fecl g).
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = ftag g).

  Lemma fchist_at0 (kk : nat) (hh : list mobs) (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = fecl g kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ---- the taint route: once the era is off the discipline every link of
          every run is free ---- *)
  Lemma file_cons_link_of_taint (k : nat) (ev : ConsLog.cons_ev)
      (Φ : iProp Σ) :
    file_taint (fgn_cl g) -∗ Φ -∗ cons_link Uart0 k ev Φ.
  Proof using Hcons.
    exact (gcons_link_of_taint file_lm (file_cparams g) None (file_wa g) Hcons k ev Φ).
  Qed.

  Lemma file_write_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
    file_taint (fgn_cl g) -∗ (file_taint (fgn_cl g) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    exact (gwrite_link_taint file_lm (file_cparams g) None (file_wa g) Hcons k b Φ).
  Qed.

  (* (W-first) THE ERA'S FIRST PROCESS BYTE.  It is the first byte of the
     prologue's first letter, and it FILES the era's boot state out of the
     deed's own typed witness -- which is what [App.al_programs] hands
     <init> beside [fturn].  What comes back is that state's persistent
     witness [f0_lb], which every later write carries. *)
  Lemma file_write_link_first (k : nat) (v : era_pins) (vf : file_era)
      (a : nat) (b : bv 8) (s0 : fstate) (Φ : iProp Σ) :
    fstate_ok s0 ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗
    turn v 0%nat -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
    f0_bl vf s0 -∗
    (f0_typed g s0 ∨ file_taint (fgn_cl g)) -∗
    (((turn v 1%nat ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v []
       ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hfok Halt Hhead.
    iIntros "#Hpin #Hfp Ht #Hpslb #Hcslb #Hilb #Hbl Hty HΦ".
    iAssert (f0boot g k s0 ∨ file_taint (fgn_cl g))%I with "[Hty]" as "Hbt".
    { iDestruct "Hty" as "[#Hty | #HT]"; [iLeft | by iRight].
      iExists vf. by iFrame "Hfp Hbl Hty". }
    iApply (gwrite_link_first file_lm (file_cparams g) None (file_wa g) Hcons k v a b s0 Φ Hfok Halt Hhead
              with "Hpin Ht Hpslb Hcslb Hilb Hbt [HΦ]").
    iIntros "[(Ht & Hps & Hcs & Hil & Hw) | #HT]"; iApply "HΦ"; [iLeft | by iRight].
    iDestruct "Hw" as (vf') "[#Hfp' #Hlb]".
    iDestruct (file_era_pin_agree with "Hfp Hfp'") as %<-.
    iFrame "Ht Hps Hcs Hil Hlb".
  Qed.

  (* (W) THE WRITE LINK, INSIDE A BLOCK -- [EchoOut.echo_write_link] with
     the era's boot state beside the three bounds, and the byte read off
     [FileOutPure.proc_stream_f] at that state. *)
  Lemma file_write_link (k : nat) (v : era_pins) (vf : file_era) (P : nat)
      (b : bv 8) (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8))
      (Φ : iProp Σ) :
    (nlines I0 <= length cs0)%nat ->
    pro_pin_f ps0 cs0 I0 ->
    proc_stream_f ps0 cs0 (Some s0) I0 !! P = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
    ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0
       ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hn Hpin0 Hb.
    iIntros "#Hpin #Hfp Ht #Hpslb #Hcslb #Hilb #Hf0lb HΦ".
    rewrite proc_stream_f_lm in Hb.
    iApply (gwrite_link file_lm (file_cparams g) None (file_wa g) Hcons k v P b ps0 cs0 s0 I0 Φ
              Hn (proj1 (pro_pin_f_lm _ _ _) Hpin0) Hb
              with "Hpin Ht Hpslb Hcslb Hilb [] [HΦ]").
    { iExists vf. iFrame "Hfp Hf0lb". }
    iIntros "[(Ht & _) | #HT]"; iApply "HΦ"; [iLeft | by iRight].
    iFrame "Ht Hpslb Hcslb Hilb Hf0lb".
  Qed.

  (* (W') THE WRITE LINK AT A BLOCK'S FIRST BYTE.  The alternative's INDEX
     is the program's own knowledge and the step files it; where echo asked
     for [a < 4] the file asks for [FileDisc.ralt_ok] at the LINE the block
     answers, which is what "whatever you type is echoed back" becomes once
     three line shapes and twelve alternatives are in play. *)
  Lemma file_write_link_blk (k : nat) (v : era_pins) (vf : file_era)
      (P a : nat) (b : bv 8) (ps0 cs0 : list nat) (s0 : fstate)
      (I0 : list (bv 8)) (Φ : iProp Σ) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin_f ps0 cs0 I0 ->
    P = length (proc_before_f ps0 cs0 (Some s0) I0) ->
    ralt_ok (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a) ->
    cont (fstate_upto cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat)
         (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a)
      !! 0%nat = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
    ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
       ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hhead.
    iIntros "#Hpin #Hfp Ht #Hpslb #Hcslb #Hilb #Hf0lb HΦ".
    rewrite proc_before_f_lm in HPeq. rewrite fstate_upto_lm in Hhead.
    iApply (gwrite_link_blk file_lm (file_cparams g) file_lm_byte_laws None (file_wa g) Hcons k v P a b ps0 cs0 s0 I0 Φ
              Hne0 Hr0 Hdiv (proj1 (pro_pin_f_lm _ _ _) Hpin0) HPeq Halt eq_refl Hhead
              with "Hpin Ht Hpslb Hcslb Hilb [] [HΦ]").
    { iExists vf. iFrame "Hfp Hf0lb". }
    iIntros "[(Ht & _ & #Hcs & _ & _) | #HT]"; iApply "HΦ"; [iLeft | by iRight].
    iFrame "Ht Hpslb Hcs Hilb Hf0lb".
  Qed.

  (* (W-pro) THE WRITE LINK AT A PROLOGUE ROUND'S CHOICE BYTE.  Init's own
     knowledge of which of the four alternatives its restart loop is taking,
     filed into the claim; the round-opening test is
     [FileDisc.ralt_panic] of the last line's alternative, so the two new
     line shapes' fork alternatives open a round too. *)
  Lemma file_write_link_pro (k : nat) (v : era_pins) (vf : file_era)
      (P a : nat) (b : bv 8) (ps0 cs0 : list nat) (s0 : fstate)
      (I0 : list (bv 8)) (Φ : iProp Σ) :
    rest_of I0 = [] ->
    (I0 = [] \/ ralt_panic (ralt_at cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    pro_pin_f ps0 cs0 I0 ->
    ~ pro_done (pro_from (pro_idx_f cs0 (nlines I0)) ps0) ->
    P = length (proc_stream_f ps0 cs0 (Some s0) I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
    ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
    (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
       ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "#Hpin #Hfp Ht #Hpslb #Hcslb #Hilb #Hf0lb HΦ".
    rewrite proc_stream_f_lm in HPeq. rewrite pro_idx_f_lm in Hnd.
    iApply (gwrite_link_pro file_lm (file_cparams g) None (file_wa g) Hcons k v P a b ps0 cs0 s0 I0 Φ
              (or_intror (or_introl I)) Hr0 Hopen Hdiv
              (proj1 (pro_pin_f_lm _ _ _) Hpin0) Hnd HPeq Halt Hhead
              with "Hpin Ht Hpslb Hcslb Hilb [] [HΦ]").
    { iExists vf. iFrame "Hfp Hf0lb". }
    iIntros "[(Ht & #Hps & _ & _ & _) | #HT]"; iApply "HΦ"; [iLeft | by iRight].
    iFrame "Ht Hps Hcslb Hilb Hf0lb".
  Qed.

  (* (R) THE READ LINK.  Beside the window it exports THE ERA'S INPUT AT THE
     WINDOW'S FAR END, its discipline, the era's BOOT STATE and the stage
     the writer has reached -- with the choice list TRUNCATED to the
     window's own line count, because [FileOutPure.alts_pre] ties every
     entry to the line at its index. *)
  Definition fread_ret (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((file_taint (fgn_cl g) ∗ dl_cnt v (1/2) n)
     ∨ dl_cnt v (1/2) (n + length ws)%nat
       ∗ ∃ (pops : list log_entry) (dl : list (list mobs * bv 8)),
           ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
           ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
           ∗ ⌜E_index (seg_of (echoed pops))⌝
           ∗ ⌜E_disc_f (seg_of (echoed pops))⌝
           ∗ ⌜forall x : list mobs * bv 8, x ∈ dl ++ ws -> obs_boots x.1 = k⌝
           ∗ inp_lb v (snd <$> (dl ++ ws))
           ∗ ⌜disc_input_f (snd <$> (dl ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ (cs0 ps0 : list nat) (vf : file_era) (s0 : fstate),
                  cs_lb v cs0 ∗ ps_lb v ps0
                  ∗ file_era_pin g k vf ∗ f0_lb vf s0
                  ∗ ⌜(nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (proc_before_f ps0 cs0 (Some s0)
                                 (snd <$> (dl ++ ws))))
                  ∗ ⌜rd_stage_f ps0 cs0 (snd <$> (dl ++ ws))⌝))%I.

  Lemma file_read_link (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    era_pin (fgn_echo g) k v -∗ dl_cnt v (1/2) n -∗
    (fread_ret k v n ws -∗ Φ) -∗
    cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using Hcons.
    iIntros "#Hpin Hdlr HΦ".
    iApply (gread_link file_lm (file_cparams g) file_lm_byte_laws None (file_wa g) Hcons k v n ws Φ with "Hpin Hdlr [HΦ]").
    iIntros "Hret". iApply "HΦ". rewrite /gread_ret /fread_ret.
    iDestruct "Hret" as "[Hret | (Hdl & %pops & %dl & %Hrok & %Hn & %Hpref & %Hidx
                                  & %Hdisc & %Hbt & #Hilb & %Hdi & Hws)]"; [by iLeft |].
    iRight. iFrame "Hdl". iExists pops, dl.
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iSplitR; [done |]. iSplitR; [done |]. iSplitR; [done |].
    iSplitR; [iExact "Hilb" |]. iSplitR; [done |].
    iDestruct "Hws" as "[%Hw | (%cs0 & %ps0 & %s0 & #Hcs & #Hps & #Hw & %Hnl
                                 & #Htl & %Hrd)]"; [by iLeft |].
    iRight. iDestruct "Hw" as (vf) "[#Hfp #Hlb]".
    iExists cs0, ps0, vf, s0. rewrite proc_before_f_lm.
    iFrame "Hcs Hps Hfp Hlb Htl". iPureIntro.
    split; [exact Hnl | by apply rd_stage_f_lm].
  Qed.

  (* ---- the arm's close and its bytes, both free ---- *)
  Lemma file_close_link (k : nat) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k ConsLog.EvClose Φ.
  Proof using Hcons.
    exact (gclose_link file_lm (file_cparams g) None (file_wa g) Hcons k Φ).
  Qed.

  Lemma file_byte_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k (ConsLog.EvByte b) Φ.
  Proof using Hcons.
    exact (gbyte_link file_lm (file_cparams g) file_lm_byte_laws None (file_wa g) Hcons k b Φ).
  Qed.

  Lemma file_cons_run (k : nat) (cs : list (bv 8)) (Φ : iProp Σ) :
    Φ -∗ cons_run k cs Φ.
  Proof using Hcons.
    exact (gcons_run file_lm (file_cparams g) file_lm_byte_laws None (file_wa g) Hcons k cs Φ).
  Qed.

  (* ==================================================================== *)
  (*  THE BUNDLE (lane LINK-GEN, item 20).  CAT-ENTRY's ask, verbatim:     *)
  (*  FileLinks.v had no EchoLinks.echo_links-style BUNDLE, so every       *)
  (*  program-side file had to re-take Hcons as a section hypothesis and   *)
  (*  thread g and Hcons through every application.                        *)
  (*                                                                      *)
  (*  [EchoLinks.echo_links]'s shape at this claim: the seven links as     *)
  (*  CLOSED [box] wands with their Coq-level premises turned into         *)
  (*  [pure] wands, so the whole thing is ONE [iProp] a program holds and  *)
  (*  spends per byte, and the record equations stay where [App.al_echo]   *)
  (*  hands them over.  This is what fills [LinkRec.lk_links] at the file  *)
  (*  application.                                                         *)
  (* ==================================================================== *)
  Definition file_link_w : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (vf : file_era) (P : nat) (b : bv 8)
         (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜(nlines I0 <= length cs0)%nat⌝ -∗
        ⌜pro_pin_f ps0 cs0 I0⌝ -∗
        ⌜proc_stream_f ps0 cs0 (Some s0) I0 !! P = Some b⌝ -∗
        era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0
           ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition file_link_blk : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (vf : file_era) (P a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜I0 <> []⌝ -∗
        ⌜rest_of I0 = []⌝ -∗
        ⌜(nlines I0 <= S (length cs0))%nat⌝ -∗
        ⌜pro_pin_f ps0 cs0 I0⌝ -∗
        ⌜P = length (proc_before_f ps0 cs0 (Some s0) I0)⌝ -∗
        ⌜ralt_ok (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat))
                 (ralt_dec a)⌝ -∗
        ⌜cont (fstate_upto cs0 s0 (bodies_of I0) (nlines I0 - 1)%nat)
              (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a)
           !! 0%nat = Some b⌝ -∗
        era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
           ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition file_link_pro : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (vf : file_era) (P a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜rest_of I0 = []⌝ -∗
        ⌜I0 = [] \/ ralt_panic (ralt_at cs0 (nlines I0 - 1)%nat) = true⌝ -∗
        ⌜(nlines I0 <= length cs0)%nat⌝ -∗
        ⌜pro_pin_f ps0 cs0 I0⌝ -∗
        ⌜~ pro_done (pro_from (pro_idx_f cs0 (nlines I0)) ps0)⌝ -∗
        ⌜P = length (proc_stream_f ps0 cs0 (Some s0) I0)⌝ -∗
        ⌜(a < length pro_alts)%nat⌝ -∗
        ⌜pro_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
        (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0
           ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* (W-first) the era's FIRST process byte, which files the boot state *)
  Definition file_link_first : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (vf : file_era) (a : nat) (b : bv 8)
         (s0 : fstate) (Φ : iProp Σ),
        ⌜fstate_ok s0⌝ -∗
        ⌜(a < length pro_alts)%nat⌝ -∗
        ⌜pro_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗
        turn v 0%nat -∗ ps_lb v [] -∗ cs_lb v [] -∗ inp_lb v [] -∗
        f0_bl vf s0 -∗
        (f0_typed g s0 ∨ file_taint (fgn_cl g)) -∗
        (((turn v 1%nat ∗ ps_lb v [a] ∗ cs_lb v [] ∗ inp_lb v []
           ∗ f0_lb vf s0) ∨ file_taint (fgn_cl g)) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition file_link_taint : iProp Σ :=
    (□ ∀ (k : nat) (b : bv 8) (Φ : iProp Σ),
        file_taint (fgn_cl g) -∗ (file_taint (fgn_cl g) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition file_link_rd : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (n : nat)
         (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        era_pin (fgn_echo g) k v -∗ dl_cnt v (1/2) n -∗
        (fread_ret k v n ws -∗ Φ) -∗
        cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition file_link_rd_taint : iProp Σ :=
    (□ ∀ (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        file_taint (fgn_cl g) -∗ (file_taint (fgn_cl g) -∗ Φ) -∗
        cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition file_links : iProp Σ :=
    (file_link_w ∗ file_link_blk ∗ file_link_pro ∗ file_link_first
     ∗ file_link_taint ∗ file_link_rd ∗ file_link_rd_taint)%I.

  Global Instance file_link_w_persistent : Persistent file_link_w.
  Proof using . rewrite /file_link_w. apply _. Qed.
  Global Instance file_link_blk_persistent : Persistent file_link_blk.
  Proof using . rewrite /file_link_blk. apply _. Qed.
  Global Instance file_link_pro_persistent : Persistent file_link_pro.
  Proof using . rewrite /file_link_pro. apply _. Qed.
  Global Instance file_link_first_persistent : Persistent file_link_first.
  Proof using . rewrite /file_link_first. apply _. Qed.
  Global Instance file_link_taint_persistent : Persistent file_link_taint.
  Proof using . rewrite /file_link_taint. apply _. Qed.
  Global Instance file_link_rd_persistent : Persistent file_link_rd.
  Proof using . rewrite /file_link_rd. apply _. Qed.
  Global Instance file_link_rd_taint_persistent : Persistent file_link_rd_taint.
  Proof using . rewrite /file_link_rd_taint. apply _. Qed.
  Global Instance file_links_persistent : Persistent file_links.
  Proof using . rewrite /file_links. apply _. Qed.

  (* ---- the seven projections, which is all a consumer ever uses ---- *)
  Lemma file_links_w : file_links -∗ file_link_w.
  Proof using . by iIntros "($ & _ & _ & _ & _ & _ & _)". Qed.
  Lemma file_links_blk : file_links -∗ file_link_blk.
  Proof using . by iIntros "(_ & $ & _ & _ & _ & _ & _)". Qed.
  Lemma file_links_pro : file_links -∗ file_link_pro.
  Proof using . by iIntros "(_ & _ & $ & _ & _ & _ & _)". Qed.
  Lemma file_links_first : file_links -∗ file_link_first.
  Proof using . by iIntros "(_ & _ & _ & $ & _ & _ & _)". Qed.
  Lemma file_links_taint : file_links -∗ file_link_taint.
  Proof using . by iIntros "(_ & _ & _ & _ & $ & _ & _)". Qed.
  Lemma file_links_rd : file_links -∗ file_link_rd.
  Proof using . by iIntros "(_ & _ & _ & _ & _ & $ & _)". Qed.
  Lemma file_links_rd_taint : file_links -∗ file_link_rd_taint.
  Proof using . by iIntros "(_ & _ & _ & _ & _ & _ & $)". Qed.

  Lemma file_links_holds : ⊢ file_links.
  Proof using Hcons.
    rewrite /file_links /file_link_w /file_link_blk /file_link_pro
            /file_link_first /file_link_taint /file_link_rd
            /file_link_rd_taint.
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit]]]]].
    - iIntros "!>" (k v vf P b ps0 cs0 s0 I0 Φ) "%Hbnd %Hpin0 %Hb".
      iIntros "Hpin Hfp Ht Hps Hcs HE Hf0 HΦ".
      iApply (file_write_link with "Hpin Hfp Ht Hps Hcs HE Hf0 HΦ");
        try assumption.
    - iIntros "!>" (k v vf P a b ps0 cs0 s0 I0 Φ).
      iIntros "%Hne %Hrest %Hbnd %Hpin0 %HPeq %Halt %Hhead".
      iIntros "Hpin Hfp Ht Hps Hcs HE Hf0 HΦ".
      iApply (file_write_link_blk with "Hpin Hfp Ht Hps Hcs HE Hf0 HΦ");
        try assumption.
    - iIntros "!>" (k v vf P a b ps0 cs0 s0 I0 Φ).
      iIntros "%Hrest %Hopen %Hbnd %Hpin0 %Hnd %HPeq %Halt %Hhead".
      iIntros "Hpin Hfp Ht Hps Hcs HE Hf0 HΦ".
      iApply (file_write_link_pro with "Hpin Hfp Ht Hps Hcs HE Hf0 HΦ");
        try assumption.
    - iIntros "!>" (k v vf a b s0 Φ) "%Hfok %Halt %Hhead".
      iIntros "Hpin Hfp Ht Hps Hcs HE Hbl Hty HΦ".
      iApply (file_write_link_first with "Hpin Hfp Ht Hps Hcs HE Hbl Hty HΦ");
        try assumption.
    - iIntros "!>" (k b Φ) "HT HΦ".
      iApply (file_write_link_taint with "HT HΦ").
    - iIntros "!>" (k v n ws Φ) "Hpin Hdl HΦ".
      iApply (file_read_link with "Hpin Hdl HΦ").
    - iIntros "!>" (k ws Φ) "#HT HΦ".
      iApply (file_cons_link_of_taint with "HT [HΦ]").
      by iApply "HΦ".
  Qed.

  (* ==================================================================== *)
  (*  THE ECHO SHIFT ITSELF -- [App.al_echo], a CLOSED entailment.         *)
  (* ==================================================================== *)
  Lemma file_happ_echo :
    ⊢ ∀ (GEN : GenId) (XI : CurCtx),
        @SpecConsoleintr.cons_echo_shift Σ HRg GEN XI.
  Proof using Hcons Htag.
    iIntros (GEN XI).
    rewrite /SpecConsoleintr.cons_echo_shift Htag.
    iIntros "!>" (h c cs Φ) "%Hends %Hk %Hcs #Htg #Hlbh HΦ".
    iDestruct "Htg" as "(%Hsh & [%Hdisc | #HT] & #Hfllb)"; last first.
    { iApply (file_cons_link_of_taint with "HT [HΦ]").
      by iApply file_cons_run. }
    iIntros (o H) "#Hlb Hres %Hok %Hev".
    rewrite fchist_at0.
    (* the open takes NOTHING beyond the kernel's own event facts: (K1) and
       the drop's reason are inside [Hev] ([EchoLinks]'s shape) *)
    iDestruct (fecl_open g (S gen_id) (default [] o) H h c cs Hok Hev
                 (disc_seg_f_open_seg h Hsh Hdisc) Hk Hdisc Hsh
                 with "Hres") as "Hres".
    iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
    rewrite fchist_at0. iFrame "Hlbh Hres".
    by iApply file_cons_run.
  Qed.

End file_links.
