(* ===================================================================== *)
(*  PipeReadInst.v -- [ReadRec.ReadRec] AT THE PIPELINE APPLICATION.      *)
(*                                                                       *)
(*  Lane PIPE-CC.  [PipeLinkInst.v] carries the pipeline era's            *)
(*  [LinkRec.LinkRec]; this is the other half of what sh's console READ   *)
(*  takes of an era, which [LinkRec] deliberately does not expose         *)
(*  ([ReadRec.v]'s header): the input's DISCIPLINE, the era's read link   *)
(*  and its taint route, and the WINDOW ARM.                              *)
(*                                                                       *)
(*  [FileReadInst.v] is the mould.  THIS ONE IS SHORTER, and the reason   *)
(*  is worth stating: the file era's window arm has to read the TYPED     *)
(*  LINE LIST's lower bound off the consumed bytes' tags (a line reaches  *)
(*  the child that writes it to `f' that way), so it needs the tag rows   *)
(*  and a last-consumed-entry argument.  The pipeline era carries no      *)
(*  per-era state at all, so its arm ignores all three rows and is        *)
(*  [ReadRec.eri_arms] verbatim at [PipeLinks.pread_ret] -- whose         *)
(*  trailing disjunct is [EchoOut.read_ret]'s with [disc_input_p] /       *)
(*  [rd_stage_p] / [proc_before_p] for echo's three.                      *)
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
Require Import LogEntryDefs.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import PipeDisc.
Require Import PipeOutPure.
Require Import RiscvPtsto.
Require Import ConsoleInv.
Require Import WpUart.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOut.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import CtxIdDefs.
Require Import LinkRec.
Require Import ReadRec.
Require Import UserConsole.
Require Import PipeLinkInst.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S1  THE PIPELINE DISCIPLINE'S ONE READING [rr_byte_of_rows] TAKES     *)
(*                                                                       *)
(*  The ring's translation is the identity on a disciplined input.        *)
(*  [ReadRec.disc_input_no_cr] / [FileReadInst.disc_input_f_no_cr] are    *)
(*  the two landed twins.  Spelled HERE and not lifted out of             *)
(*  [UShPipeRound.ushq_disc_snoc_ncr], which is the same fact: that file  *)
(*  sits at the top of the program tier and this record belongs beside    *)
(*  [PipeLinkInst.v], so importing it for one pure lemma would drag the   *)
(*  whole shell walk into this cone.                                      *)
(* ===================================================================== *)

(* the last byte of a disciplined input is a body byte -- BAR INCLUDED --
   or the newline ([UShPipeRound.ushq_disc_snoc_byte]) *)
Lemma pdisc_snoc_byte (I : list (bv 8)) (b : bv 8) :
  disc_input_p (I ++ [b]) -> pbody_byte b \/ b = wl_nl.
Proof using.
  intro Hd. destruct (decide (b = wl_nl)) as [-> | Hne]; [ by right | ].
  left. destruct Hd as (_ & Hr & _).
  rewrite (rest_of_snoc_other I b Hne) in Hr.
  apply Forall_app in Hr as [_ Hb].
  apply (Forall_lookup_1 _ _ 0%nat b Hb). reflexivity.
Qed.

Lemma pdisc_snoc_ncr (I : list (bv 8)) (b : bv 8) :
  disc_input_p (I ++ [b]) -> bv_unsigned b <> 13%Z.
Proof using.
  intro Hd. pose proof (pdisc_snoc_byte I b Hd) as Hp.
  destruct Hp as [Hp | Hnl]; [ | rewrite Hnl wl_nl_val; lia ].
  destruct Hp as [Hp | Hbar]; [ | rewrite Hbar; by vm_compute ].
  destruct Hp as [Ha | Hsp]; [ | rewrite Hsp wl_sp_val; lia ].
  destruct Ha as [HA | Ha]; [ lia | ].
  destruct Ha as [HB | HC]; lia.
Qed.

Lemma disc_input_p_byte_ncr (I : list (bv 8)) (j : nat) :
  disc_input_p I -> (j < length I)%nat -> bv_unsigned (I !!! j) <> 13%Z.
Proof using.
  intros Hd Hj.
  destruct (lookup_lt_is_Some_2 I j Hj) as [b Hb].
  assert (Heq : I !!! j = b)
    by (rewrite list_lookup_total_alt Hb; reflexivity).
  rewrite Heq.
  assert (Hpre : take (S j) I `prefix_of` I)
    by (exists (drop (S j) I); symmetry; apply take_drop).
  pose proof (disc_input_p_prefix _ _ Hpre Hd) as Hdt.
  rewrite (take_S_r I j b Hb) in Hdt.
  exact (pdisc_snoc_ncr (take j I) b Hdt).
Qed.

Lemma disc_input_p_no_cr (I : list (bv 8)) (j : nat) :
  disc_input_p I -> (j < length I)%nat -> cons_xlate (I !!! j) = I !!! j.
Proof using.
  intros Hd Hj. pose proof (disc_input_p_byte_ncr I j Hd Hj) as Hv.
  rewrite /cons_xlate. rewrite decide_False; [reflexivity |].
  intro Hq. apply (f_equal bv_unsigned) in Hq.
  rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
    [lia | by vm_compute].
Qed.

(* ===================================================================== *)
(*  S2  THE RECORD                                                        *)
(* ===================================================================== *)
Section pipe_read_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ}.
  Context `{!pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context `{HRg : !riscvGS Σ}.
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId}.

  Local Notation PI := (pipe_link_inst_at g).

  Local Lemma pri_rd (k n : nat) (v : era_pins)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    ⊢ PipeLinks.pipe_links g -∗ era_pin γ k v -∗ dl_cnt v (1/2) n -∗
      (PipeLinks.pread_ret g k v n ws -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk #Hpin Hdl HΦ".
    iDestruct (PipeLinks.pipe_links_rd with "Hlk") as "#Hrdl".
    iApply ("Hrdl" $! k v n ws with "Hpin Hdl HΦ").
  Qed.

  Local Lemma pri_rd_taint (k : nat) (ws : list (list mobs * bv 8))
      (Φ : iProp Σ) :
    ⊢ PipeLinks.pipe_links g -∗ echo_taint γ -∗ (echo_taint γ -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk HT HΦ".
    iDestruct (PipeLinks.pipe_links_rd_taint with "Hlk") as "#Hrdt".
    iApply ("Hrdt" $! k ws with "HT HΦ").
  Qed.

  (* THE WINDOW ARM: [ReadRec.eri_arms]'s proof, at the pipeline era's own
     receipt.  The input at the window's far end EXTENDS the lease's,
     because both are lower bounds of one echoed list
     ([EchoOut.inp_lb_cmp] -- the ledger is echo's) and the lease's is the
     shorter; the residue comes off the receipt where a byte was delivered
     and off the lease where the count did not move.  The three tag rows
     are ignored: the pipeline era reads nothing off an input byte's tag. *)
  Local Lemma pri_arms (cn : cons_names) (v : era_pins) (I : list (bv 8))
      (ws sl sl' : list (list mobs * bv 8))
      (hs : list (list mobs)) (dd dc : nat) (g0 : nat -> bv 8) :
    (dd <= dc)%nat -> length ws = dc ->
    cons_window sl (length I) dd g0 hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
    ⊢ era_pin γ (S gen_id) v -∗ inp_lb v I -∗ pwc_rres v I -∗
      PipeLinks.pread_ret g (S gen_id) v (length I) ws -∗
      ([∗ list] hh ∈ hs, riscv_rx_tag hh) -∗
      ucons_swallow cn False sl dd dc -∗
      ucons_stored_lb cn sl' -∗
      (dl_cnt v (1/2) (length I + dc)%nat
       ∗ ∃ J : list (bv 8),
           ⌜length J = dc⌝ ∗ ⌜disc_input_p (I ++ J)⌝
           ∗ ⌜(0 < dd)%nat -> g0 0%nat = J !!! 0%nat⌝
           ∗ inp_lb v (I ++ J) ∗ pwc_rres v (I ++ J))
      ∨ echo_taint γ.
  Proof using .
    intros Hddc Hlws Hwinf Hpre2 Hwsj.
    iIntros "#Hpin #HE0 #Hres0 Hret _ _ _".
    rewrite /PipeLinks.pread_ret.
    iDestruct "Hret" as "[[#HT _] | [Hdlr Hfacts]]"; [ by iRight | ].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdscp & #HEin & %Hdinp & Hrest)".
    iEval (rewrite Hlws) in "Hdlr".
    iDestruct (inp_lb_cmp v I (snd <$> (dl ++ ws)) with "HE0 HEin") as %Hcmp.
    assert (Hlen' : length (snd <$> (dl ++ ws)) = (length I + dc)%nat).
    { rewrite length_fmap length_app Hdl Hlws. reflexivity. }
    assert (Hpre' : I `prefix_of` (snd <$> (dl ++ ws))).
    { destruct Hcmp as [Hc | Hc]; [ exact Hc | ].
      pose proof (prefix_length _ _ Hc) as Hle.
      assert (Hdc0 : dc = 0%nat) by lia.
      assert (Heq : (snd <$> (dl ++ ws)) = I).
      { apply (list_eq_same_length _ _ (length I)); [ lia | lia | ].
        intros i x y Hi Hx Hy.
        pose proof (prefix_lookup_Some _ _ i x Hx Hc) as Hxy.
        rewrite Hxy in Hy. by injection Hy as <-. }
      rewrite Heq. done. }
    destruct Hpre' as [J HJ].
    assert (HJlen : length J = dc)
      by (rewrite HJ length_app in Hlen'; lia).
    assert (HJdisc : disc_input_p (I ++ J)) by (rewrite <- HJ; exact Hdinp).
    iDestruct "Hrest" as "#Hrest".
    iAssert (pwc_rres v (I ++ J)) as "#Hresn".
    { iDestruct "Hrest" as "[%Hws0 | Hbb]".
      - assert (Hdc0 : dc = 0%nat)
          by (rewrite <- Hlws, Hws0; reflexivity).
        assert (HJnil : J = []) by (apply nil_length_inv; lia).
        rewrite HJnil app_nil_r. iExact "Hres0".
      - iDestruct "Hbb" as (cs0 ps0) "(#Hcs & #Hps & _ & #Htlb & %Hrds)".
        rewrite /pwc_rres. iExists ps0, cs0.
        rewrite <- HJ. iFrame "Htlb Hps Hcs". by iPureIntro. }
    iAssert (inp_lb v (I ++ J)) as "#HEn";
      [ rewrite <- HJ; iExact "HEin" | ].
    iLeft. iFrame "Hdlr". iExists J.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitR; [ | iFrame "HEn Hresn" ].
    iPureIntro. intro Hdd0.
    exact (rr_byte_of_rows disc_input_p sl sl' ws dl hs pops I J dd dc g0
             disc_input_p_no_cr
             Hdd0 Hddc Hwinf Hpre2 Hwsj Hpref Hdl HJ HJdisc ltac:(lia)).
  Qed.

  Definition pipe_read_inst : ReadRec PI :=
    MkReadRec PI disc_input_p pri_rd pri_rd_taint pri_arms.

  (* ---- the definitional check ([FileReadInst]'s) ---- *)
  Lemma pipe_read_inst_disc : rk_disc PI pipe_read_inst = disc_input_p.
  Proof using . reflexivity. Qed.

End pipe_read_inst.
