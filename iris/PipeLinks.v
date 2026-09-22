(* PipeLinks.v -- THE PIPELINE APPLICATION'S CONSOLE LINKS.

   Design of record: claude-notes/design/app-pipe.md section 4.1, lane
   PIPE-STAGE, deliverable 3.  [EchoOut.v]'s [Section echo_links] (and
   upstream's [FileLinks.v]) at the pipeline claim: the same links wrapped
   onto the kernel's own console contracts, the taint route, the bundle a
   program holds and spends per byte, and [App.al_echo] as a CLOSED
   entailment.

   WHAT IS SIMPLER THAN [FileLinks].  There is no per-era extra state, so
   there is no [file_write_link_first]: the era's FIRST process byte is the
   prologue's first letter and goes out through [pipe_write_link_pro] at the
   empty stage, exactly as at the echo application.  The bundle therefore
   has SIX components where the file's has seven, and a writer's argument
   list is echo's with the byte read off [PipeOutPure.proc_stream_p].
   (SH-PIPE-ROUND-4 added a SEVENTH: [pipe_link_file], the two-writer
   round's filing step at the prompt's first byte -- see [pipe_file_link].)

   A link runs at [⊤ ∖ ↑uartN Uart0] and opens NOTHING but the port
   invariant: every authority an era has is in the claim the link is handed,
   so no link reaches the application's ledger. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat own ghost_var ghost_map.
From iris.algebra.lib Require Import mono_list.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang.
Require Import LineWords.
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import PipeDisc.
Require Import PipeOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import SpecConsoleintr.
Local Open Scope list_scope.

Section pipe_links.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  (* THE FIXED PART IS [PipeOut.pipe_gn] (lane PIPE-2W-2): the echo half
     is [pgn_cl g], so every statement below names [γ] as it did. *)
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.

  Notation T := (echo_taint γ).

  (* the record equations, as section parameters: [App.al_echo] hands them
     over at the [boot_fixedGS] literal *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = ptag g).

  Lemma pchist_at0 (kk : nat) (hh : list mobs) (HH : LogEntryDefs.cons_hist) :
    chist_at Uart0 kk hh HH = pecl g kk hh HH.
  Proof using Hcons. rewrite /chist_at. by rewrite Hcons. Qed.

  (* ---- the taint route: once the era is off the discipline every link of
          every run is free ---- *)
  Lemma pipe_cons_link_of_taint (k : nat) (ev : ConsLog.cons_ev)
      (Φ : iProp Σ) :
    T -∗ Φ -∗ cons_link Uart0 k ev Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres _ _".
    iModIntro. iExists o.
    iSplitR; [iExact "Hlb" |].
    iSplitR "HΦ"; [| iExact "HΦ"].
    rewrite !pchist_at0 /pecl. by iLeft.
  Qed.

  Lemma pipe_write_link_taint (k : nat) (b : bv 8) (Φ : iProp Σ) :
    T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using Hcons.
    iIntros "#HT HΦ" (o H) "#Hlb Hres".
    iModIntro. iExists o.
    iSplitR; [iExact "Hlb" |].
    iSplitR "HΦ"; [| by iApply "HΦ"].
    rewrite !pchist_at0 /pecl. by iLeft.
  Qed.

  (* (W) THE WRITE LINK, INSIDE A BLOCK -- [EchoOut.echo_write_link] with
     the byte read off [PipeOutPure.proc_stream_p].  INIT'S FIRST BANNER
     BYTE IS THIS LINK at [P = 0], [I0 = []], [cs0 = []]: [pturn] is
     exactly its argument list. *)
  Lemma pipe_write_link (k : nat) (v : era_pins) (P : nat) (b : bv 8)
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
    (nlines I0 <= length cs0)%nat ->
    pro_pin_p ps0 cs0 I0 ->
    proc_stream_p ps0 cs0 I0 !! P = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hn Hpin0 Hb.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
    rewrite !pchist_at0.
    iMod (pecl_step_write g k v P b ps0 cs0 I0 (default [] o) H
            Hn Hpin0 Hb with "Hpin Ht Hpslb Hcslb Hilb Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (W') THE WRITE LINK AT A BLOCK'S FIRST BYTE.  Where echo asked for
     [a < 4] and [line_alts_of (last_ws I0) !!! a !! 0 = Some b], the
     pipeline asks for [PipeDisc.palt_ok] at the LINE the block answers and
     for the first byte of THAT alternative's continuation -- so the program
     NAMES the alternative its round is taking and proves the line admits
     it.  There is no state to compute: [pcont] reads the line and the
     alternative only. *)
  Lemma pipe_write_link_blk (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a) ->
    palt_isforkS (palt_of a) = false ->
    pcont (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a)
      !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0)
      ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hfk Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
    rewrite !pchist_at0.
    iMod (pecl_step_write_blk g k v P a b ps0 cs0 I0 (default [] o) H
            Hne0 Hr0 Hdiv Hpin0 HPeq Halt Hfk Hhead
            with "Hpin Ht Hpslb Hcslb Hilb Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (W-pro) THE WRITE LINK AT A PROLOGUE ROUND'S CHOICE BYTE.  The
     round-opening test is [PipeDisc.palt_panic] of the last line's
     alternative, so a PIPELINE line reaches it exactly as an echo line
     does -- PIPE-MODEL-2's ruling ([PEcho 3] at both shapes) is what makes
     this the SAME premise at either shape. *)
  Lemma pipe_write_link_pro (k : nat) (v : era_pins) (P a : nat)
      (b : bv 8) (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ) :
    rest_of I0 = [] ->
    (I0 = [] \/ palt_panic (palt_at cs0 (nlines I0 - 1)%nat) = true) ->
    (nlines I0 <= length cs0)%nat ->
    pro_pin_p ps0 cs0 I0 ->
    ~ pro_done (pro_from (pro_idx_p cs0 (nlines I0)) ps0) ->
    P = length (proc_stream_p ps0 cs0 I0) ->
    (a < length pro_alts)%nat ->
    pro_alts !!! a !! 0%nat = Some b ->
    era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0)
      ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
    intros Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead.
    iIntros "#Hpin Ht #Hpslb #Hcslb #Hilb HΦ" (o H) "#Hlb Hres".
    rewrite !pchist_at0.
    iMod (pecl_step_write_pro g k v P a b ps0 cs0 I0 (default [] o) H
            Hr0 Hopen Hdiv Hpin0 Hnd HPeq Halt Hhead
            with "Hpin Ht Hpslb Hcslb Hilb Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pchist_at0. iFrame "Hlb Hres".
    by iApply "HΦ".
  Qed.

  (* (F) THE ROUND'S FILING LINK -- THE SEVENTH LEAF (lane SH-PIPE-ROUND-4,
     design section 4.3f (R1), preferred route).  [PipeOut.pecl_blk2_file] wrapped
     as an [out_link], exactly as (W') wraps [pecl_step_write_blk]: the
     prompt's own first byte, which files a TWO-WRITER round's code.

     WHY IT HAS TO BE A LEAF AND CANNOT BE A FREE LEMMA WHERE IT IS SPENT.
     The step itself is free ([PipeBoth.pblk2_ecl_file_holds] is a closed
     entailment), but it is a [pecl] step and its consumer -- the record
     field [lk_prompt_dollar_line], which takes no [Hcons] -- needs it as
     an [out_link].  The conversion is [Hcons], and the bundle is where
     this application keeps [Hcons].

     ITS PREMISES ARE [pecl_blk2_file]'S OWN, not [PipeBoth]'s
     [wr_blk2_p]/[pblk2_code]: the latter name [PipeLinksLine.pline_at],
     [pab] and [wr_tail_p], which live ABOVE this file. *)
  Lemma pipe_file_link (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
      (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
      (ps0 cs0 : list nat) (I0 : list (bv 8)) (Phi : iProp Σ) :
    I0 <> [] ->
    rest_of I0 = [] ->
    r = (nlines I0 - 1)%nat ->
    length cs0 = r ->
    pro_pin_p ps0 cs0 I0 ->
    P = length (proc_before_p ps0 cs0 I0) ->
    palt_ok (pline_of (bodies_of I0 !!! r)) (palt_of a) ->
    palt_panic (palt_of a) = false ->
    palt_isforkS (palt_of a) = false ->
    pcont (pline_of (bodies_of I0 !!! r)) (palt_of a) = pre0 ++ u_prompt ->
    b = u_prompt !!! 0%nat ->
    era_pin γ k v -∗ pera_pin g k w -∗
    turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb false -∗
    rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
    (((turn v (S (P + length pre0))%nat ∗ ps_lb v ps0
       ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0) ∨ T) -∗ Phi) -∗
    out_link Uart0 k b Phi.
  Proof using Hcons.
    intros Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hfk Hcont Hbv.
    iIntros "#Hpin #Hpera Ht Hcw #Hrlb #Hpslb #Hcslb #Hilb HPhi" (o H) "#Hlb Hres".
    rewrite !pchist_at0.
    iMod (pecl_blk2_file g k v w gb P r a b pre0 ps0 cs0 I0 (default [] o) H
            Hne0 Hr0 Hreq Hcseq Hpin0 HPeq Halt Hpan Hfk Hcont Hbv
            with "Hpin Hpera Ht Hcw Hrlb Hpslb Hcslb Hilb Hres")
      as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pchist_at0. iFrame "Hlb Hres".
    by iApply "HPhi".
  Qed.

  (* (R) THE READ LINK.  Beside the window it exports THE ERA'S INPUT AT
     THE WINDOW'S FAR END, its discipline and the stage the writer has
     reached -- with the choice list read at [PipeOutPure.alts_pre_p],
     which ties every entry to the line at its index. *)
  Definition pread_ret (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) : iProp Σ :=
    ((T ∗ dl_cnt v (1/2) n)
     ∨ dl_cnt v (1/2) (n + length ws)%nat
       ∗ ∃ (pops : list log_entry) (dl : list (list mobs * bv 8)),
           ⌜read_ok pops dl ws⌝ ∗ ⌜length dl = n⌝
           ∗ ⌜(dl ++ ws) `prefix_of` echoed pops⌝
           ∗ ⌜E_index (seg_of (echoed pops))⌝
           ∗ ⌜E_disc_p (seg_of (echoed pops))⌝
           ∗ inp_lb v (snd <$> (dl ++ ws))
           ∗ ⌜disc_input_p (snd <$> (dl ++ ws))⌝
           ∗ (⌜ws = []⌝
              ∨ ∃ cs0 ps0 : list nat,
                  cs_lb v cs0 ∗ ps_lb v ps0
                  ∗ ⌜(nlines (snd <$> (dl ++ ws)) <= S (length cs0))%nat⌝
                  ∗ turn_lb v (length (proc_before_p ps0 cs0
                                 (snd <$> (dl ++ ws))))
                  ∗ ⌜rd_stage_p ps0 cs0 (snd <$> (dl ++ ws))⌝))%I.

  Lemma pipe_read_link (k : nat) (v : era_pins) (n : nat)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    era_pin γ k v -∗ dl_cnt v (1/2) n -∗ (pread_ret k v n ws -∗ Φ) -∗
    cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using Hcons.
    iIntros "#Hpin Hdlr HΦ" (o H) "#Hlb Hres _ %Hread".
    rewrite !pchist_at0.
    iMod (pecl_step_read g k v n (default [] o) H ws Hread
            with "Hpin Hdlr Hres") as "(Hres & Hret)".
    iModIntro. iExists o. rewrite pchist_at0. iFrame "Hlb Hres".
    iApply "HΦ". rewrite /pread_ret.
    iDestruct "Hret" as "[Ht | (Hdlr & %Hdl & %Hpref & %Hidx & %Hbyte
                               & Hilb & %Hdi & Hrest)]"; [by iLeft |].
    iRight. iFrame "Hdlr".
    iExists (LogEntryDefs.ch_log H), (LogEntryDefs.ch_dl H).
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |]. iSplitR; [by iPureIntro |].
    iSplitR; [by iPureIntro |].
    iSplitL "Hilb"; [iExact "Hilb" |].
    iSplitR; [by iPureIntro |]. iExact "Hrest".
  Qed.

  (* ---- the arm's close and its bytes, both free ---- *)
  Lemma pipe_close_link (k : nat) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k ConsLog.EvClose Φ.
  Proof using Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite pchist_at0.
    iDestruct (pecl_close g k (default [] o) H Hok Hev with "Hres") as "Hres".
    iModIntro. iExists o. rewrite pchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma pipe_byte_link (k : nat) (b : bv 8) (Φ : iProp Σ) :
    Φ -∗ cons_link Uart0 k (ConsLog.EvByte b) Φ.
  Proof using Hcons.
    iIntros "HΦ" (o H) "#Hlb Hres %Hok %Hev".
    rewrite pchist_at0.
    iMod (pecl_step_byte g k (default [] o) H b Hok Hev with "Hres") as "Hres".
    iModIntro. iExists o. rewrite pchist_at0. by iFrame "Hlb Hres HΦ".
  Qed.

  Lemma pipe_cons_run (k : nat) (cs : list (bv 8)) (Φ : iProp Σ) :
    Φ -∗ cons_run k cs Φ.
  Proof using Hcons.
    iIntros "HΦ". iInduction cs as [| b cs] "IH" forall (Φ); cbn [cons_run].
    - by iApply pipe_close_link.
    - iSplit.
      + by iApply pipe_close_link.
      + iApply pipe_byte_link. by iApply "IH".
  Qed.

  (* ==================================================================== *)
  (*  THE BUNDLE.  [EchoLinks.echo_links]'s shape at this claim: the six   *)
  (*  links as CLOSED [box] wands with their Coq-level premises turned     *)
  (*  into [pure] wands, so the whole thing is ONE [iProp] a program holds  *)
  (*  and spends per byte, and the record equations stay where             *)
  (*  [App.al_echo] hands them over.  SIX and not seven: there is no       *)
  (*  boot-state-filing first byte.                                       *)
  (* ==================================================================== *)
  Definition pipe_link_w : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P : nat) (b : bv 8)
         (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜(nlines I0 <= length cs0)%nat⌝ -∗
        ⌜pro_pin_p ps0 cs0 I0⌝ -∗
        ⌜proc_stream_p ps0 cs0 I0 !! P = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ inp_lb v I0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition pipe_link_blk : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜I0 <> []⌝ -∗
        ⌜rest_of I0 = []⌝ -∗
        ⌜(nlines I0 <= S (length cs0))%nat⌝ -∗
        ⌜pro_pin_p ps0 cs0 I0⌝ -∗
        ⌜P = length (proc_before_p ps0 cs0 I0)⌝ -∗
        ⌜palt_ok (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat))
                 (palt_of a)⌝ -∗
        ⌜palt_isforkS (palt_of a) = false⌝ -∗
        ⌜pcont (pline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (palt_of a)
           !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition pipe_link_pro : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (I0 : list (bv 8)) (Φ : iProp Σ),
        ⌜rest_of I0 = []⌝ -∗
        ⌜I0 = [] \/ palt_panic (palt_at cs0 (nlines I0 - 1)%nat) = true⌝ -∗
        ⌜(nlines I0 <= length cs0)%nat⌝ -∗
        ⌜pro_pin_p ps0 cs0 I0⌝ -∗
        ⌜~ pro_done (pro_from (pro_idx_p cs0 (nlines I0)) ps0)⌝ -∗
        ⌜P = length (proc_stream_p ps0 cs0 I0)⌝ -∗
        ⌜(a < length pro_alts)%nat⌝ -∗
        ⌜pro_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗
        ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
        (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ inp_lb v I0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition pipe_link_taint : iProp Σ :=
    (□ ∀ (k : nat) (b : bv 8) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ)%I.

  Definition pipe_link_rd : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (n : nat)
         (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        era_pin γ k v -∗ dl_cnt v (1/2) n -∗
        (pread_ret k v n ws -∗ Φ) -∗
        cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  Definition pipe_link_rd_taint : iProp Σ :=
    (□ ∀ (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ cons_link Uart0 k (ConsLog.EvRead ws) Φ)%I.

  (* THE SEVENTH LEAF (lane SH-PIPE-ROUND-4).  See [pipe_file_link]. *)
  Definition pipe_link_file : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (w : pipe_era) (gb : gname)
         (P r a : nat) (b : bv 8) (pre0 : list (bv 8))
         (ps0 cs0 : list nat) (I0 : list (bv 8)) (Phi : iProp Σ),
        ⌜I0 <> []⌝ -∗
        ⌜rest_of I0 = []⌝ -∗
        ⌜r = (nlines I0 - 1)%nat⌝ -∗
        ⌜length cs0 = r⌝ -∗
        ⌜pro_pin_p ps0 cs0 I0⌝ -∗
        ⌜P = length (proc_before_p ps0 cs0 I0)⌝ -∗
        ⌜palt_ok (pline_of (bodies_of I0 !!! r)) (palt_of a)⌝ -∗
        ⌜palt_panic (palt_of a) = false⌝ -∗
        ⌜palt_isforkS (palt_of a) = false⌝ -∗
        ⌜pcont (pline_of (bodies_of I0 !!! r)) (palt_of a) = pre0 ++ u_prompt⌝ -∗
        ⌜b = u_prompt !!! 0%nat⌝ -∗
        era_pin γ k v -∗ pera_pin g k w -∗
        turn v (P + length pre0)%nat -∗ cur_half w (1/2) r gb false -∗
        rblk_lb gb pre0 -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗
        (((turn v (S (P + length pre0))%nat ∗ ps_lb v ps0
           ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0) ∨ T) -∗ Phi) -∗
        out_link Uart0 k b Phi)%I.

  Definition pipe_links : iProp Σ :=
    (pipe_link_w ∗ pipe_link_blk ∗ pipe_link_pro ∗ pipe_link_taint
     ∗ pipe_link_rd ∗ pipe_link_rd_taint ∗ pipe_link_file)%I.

  Global Instance pipe_link_w_persistent : Persistent pipe_link_w | 0.
  Proof using . rewrite /pipe_link_w. apply _. Qed.
  Global Instance pipe_link_blk_persistent : Persistent pipe_link_blk | 0.
  Proof using . rewrite /pipe_link_blk. apply _. Qed.
  Global Instance pipe_link_pro_persistent : Persistent pipe_link_pro | 0.
  Proof using . rewrite /pipe_link_pro. apply _. Qed.
  Global Instance pipe_link_taint_persistent : Persistent pipe_link_taint | 0.
  Proof using . rewrite /pipe_link_taint. apply _. Qed.
  Global Instance pipe_link_rd_persistent : Persistent pipe_link_rd | 0.
  Proof using . rewrite /pipe_link_rd. apply _. Qed.
  Global Instance pipe_link_rd_taint_persistent :
    Persistent pipe_link_rd_taint | 0.
  Proof using . rewrite /pipe_link_rd_taint. apply _. Qed.
  Global Instance pipe_link_file_persistent : Persistent pipe_link_file | 0.
  Proof using . rewrite /pipe_link_file. apply _. Qed.
  Global Instance pipe_links_persistent : Persistent pipe_links | 0.
  Proof using . rewrite /pipe_links. apply _. Qed.

  (* ---- the seven projections, which is all a consumer ever uses ---- *)
  Lemma pipe_links_w : pipe_links -∗ pipe_link_w.
  Proof using . by iIntros "($ & _ & _ & _ & _ & _ & _)". Qed.
  Lemma pipe_links_blk : pipe_links -∗ pipe_link_blk.
  Proof using . by iIntros "(_ & $ & _ & _ & _ & _ & _)". Qed.
  Lemma pipe_links_pro : pipe_links -∗ pipe_link_pro.
  Proof using . by iIntros "(_ & _ & $ & _ & _ & _ & _)". Qed.
  Lemma pipe_links_taint : pipe_links -∗ pipe_link_taint.
  Proof using . by iIntros "(_ & _ & _ & $ & _ & _ & _)". Qed.
  Lemma pipe_links_rd : pipe_links -∗ pipe_link_rd.
  Proof using . by iIntros "(_ & _ & _ & _ & $ & _ & _)". Qed.
  Lemma pipe_links_rd_taint : pipe_links -∗ pipe_link_rd_taint.
  Proof using . by iIntros "(_ & _ & _ & _ & _ & $ & _)". Qed.
  Lemma pipe_links_file : pipe_links -∗ pipe_link_file.
  Proof using . by iIntros "(_ & _ & _ & _ & _ & _ & $)". Qed.

  Lemma pipe_links_holds : ⊢ pipe_links.
  Proof using Hcons.
    rewrite /pipe_links /pipe_link_w /pipe_link_blk /pipe_link_pro
            /pipe_link_taint /pipe_link_rd /pipe_link_rd_taint
            /pipe_link_file.
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit]]]]].
    - iIntros "!>" (k v P b ps0 cs0 I0 Φ) "%Hbnd %Hpin0 %Hb".
      iIntros "Hpin Ht Hps Hcs HE HΦ".
      iApply (pipe_write_link with "Hpin Ht Hps Hcs HE HΦ"); try assumption.
    - iIntros "!>" (k v P a b ps0 cs0 I0 Φ).
      iIntros "%Hne %Hrest %Hbnd %Hpin0 %HPeq %Halt %Hfk %Hhead".
      iIntros "Hpin Ht Hps Hcs HE HΦ".
      iApply (pipe_write_link_blk with "Hpin Ht Hps Hcs HE HΦ");
        try assumption.
    - iIntros "!>" (k v P a b ps0 cs0 I0 Φ).
      iIntros "%Hrest %Hopen %Hbnd %Hpin0 %Hnd %HPeq %Halt %Hhead".
      iIntros "Hpin Ht Hps Hcs HE HΦ".
      iApply (pipe_write_link_pro with "Hpin Ht Hps Hcs HE HΦ");
        try assumption.
    - iIntros "!>" (k b Φ) "HT HΦ".
      iApply (pipe_write_link_taint with "HT HΦ").
    - iIntros "!>" (k v n ws Φ) "Hpin Hdl HΦ".
      iApply (pipe_read_link with "Hpin Hdl HΦ").
    - iIntros "!>" (k ws Φ) "#HT HΦ".
      iApply (pipe_cons_link_of_taint with "HT [HΦ]").
      by iApply "HΦ".
    - iIntros "!>" (k v w gb P r a b pre0 ps0 cs0 I0 Phi).
      iIntros "%Hne %Hrest %Hreq %Hcseq %Hpin0 %HPeq %Halt %Hpan %Hfk %Hcont %Hbv".
      iIntros "Hpin Hpera Ht Hcw Hrlb Hps Hcs HE HPhi".
      iApply (pipe_file_link with "Hpin Hpera Ht Hcw Hrlb Hps Hcs HE HPhi");
        try assumption.
  Qed.

  (* ==================================================================== *)
  (*  THE ECHO SHIFT ITSELF -- [App.al_echo], a CLOSED entailment.         *)
  (* ==================================================================== *)
  Lemma pipe_happ_echo :
    ⊢ ∀ (GEN : GenId) (XI : CurCtx),
        @SpecConsoleintr.cons_echo_shift Σ HRg GEN XI.
  Proof using Hcons Htag.
    iIntros (GEN XI).
    rewrite /SpecConsoleintr.cons_echo_shift Htag.
    iIntros "!>" (h c cs Φ) "%Hends %Hk %Hcs #Htg #Hlbh HΦ".
    iDestruct "Htg" as "[%Hsh [%Hdisc | #HT]]"; last first.
    { iApply (pipe_cons_link_of_taint with "HT [HΦ]").
      by iApply pipe_cons_run. }
    iIntros (o H) "#Hlb Hres %Hok %Hev".
    rewrite pchist_at0.
    iDestruct (pecl_open g (S gen_id) (default [] o) H h c cs Hok Hev
                 (disc_seg_p_open_seg h Hsh Hdisc) Hk Hdisc Hsh
                 with "Hres") as "Hres".
    iModIntro. iExists (Some h). cbn [obs_hist_lb_o from_option id].
    rewrite pchist_at0. iFrame "Hlbh Hres".
    by iApply pipe_cons_run.
  Qed.

End pipe_links.

(* PIPE-2W-3: THE BUNDLE IS OPAQUE TO THE INSTANCE SEARCH.  [pipe_links] is
   a six-fold [∗] of wand bundles; left transparent, the [Persistent] search
   UNFOLDS it instead of taking [pipe_links_persistent], and then descends
   into the wands -- the tree's documented "a bundle of wands hangs the
   [Persistent] search".  It was already minutes per site; when the fixed
   part grew ([pipeOutG]'s two cameras beside [echoOutG]'s five) every
   [own]-leaf of that descent gained branches and one [iIntros "#Hlk"] went
   past 300 s (PipeLinksLine.v:1401 -- the whole file went from ~40 min to
   6+ CPU hours).  The seven leaves above are named at priority 0 and the
   constants are opaque to the search, so a [Persistent (pipe_links _)] goal
   is settled by its own instance and nothing else is tried. *)
#[global] Typeclasses Opaque pipe_links.
(* ONLY THE BUNDLE.  The six links themselves stay transparent: each is
   [□ ∀ ...], so its own [Persistent] is one step, and [iSpecialize] /
   [iApply ("Ht" $! k b Φ)] must be able to see the [∀] through the name
   (made them opaque once -- PipeLinksLine.v:1406 answered with
   "iSpecialize: cannot instantiate (pipe_link_taint g) with k"). *)
