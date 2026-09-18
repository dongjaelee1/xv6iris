(* ===================================================================== *)
(*  FileReadInst.v -- THE FILE ERA'S READ RECORD, AND SH'S READ LEAF AT   *)
(*  IT (lane LINK-GEN-5, residue 3 of LINK-GEN-4's findings).             *)
(*                                                                       *)
(*  [ReadRec.v] names what sh's read takes of an era; [FileLinkInst.v]    *)
(*  names the file era's LINK record.  This file is the read half of the  *)
(*  second instance, and the ONE thing it delivers upwards is             *)
(*  [file_read_leaf_holds]: sh's console read leaf at the FILE            *)
(*  discipline, by one application of                                     *)
(*  [UShLine.ush_read_recv_leaf_holds_at].                                *)
(*                                                                       *)
(*  IT SITS ABOVE [UShLine.v] and not beside [FileLinkInst.v] because the *)
(*  leaf is [UShLine]'s: the instance and its one consumer are in the     *)
(*  same file, which is what keeps [FileLinkInst.v] -- lane LINK-GEN-2's  *)
(*  -- untouched.                                                        *)
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
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import EchoLinks.
Require Import EchoLinksLine.
Require Import LinkRec.
Require Import ReadRec.
Require Import FileLinkInst.
Require Import RiscvPtsto.
Require Import ConsoleInv.
Require Import WpUart.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.
Require Import AppInv.
Require Import FsCfg.
Require Import UserConsole.
Require Import UkSh.
Require Import UkShRedirBody.
Require Import UShLine.
Require Import CtxIdDefs.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  1.  THE FILE DISCIPLINE'S THREE PURE READINGS                         *)
(*                                                                       *)
(*  [FileDisc] has [disc_input_f] and its closure laws ([disc_input_f_nil]*)
(*  [_snoc], [_prefix], [_body], [_at]); what it does NOT have is the     *)
(*  BYTE-level reading -- the echo model's [EchoDisc.disc_input_byte] and *)
(*  the three consequences under it -- so those are here.  The extra byte *)
(*  the file discipline admits is [FileDisc.wl_gt] ('>' = 62), which is   *)
(*  why the echo statement's alphanumeric range is NOT the shape that     *)
(*  travels and the NEGATIONS are.                                       *)
(* ===================================================================== *)
Lemma disc_input_f_byte (I : list (bv 8)) (b : bv 8) :
  disc_input_f I -> b ∈ I -> fbody_byte b \/ b = wl_nl.
Proof using.
  intros Hd Hin. pose proof Hd as (Hb & Hr & _).
  rewrite (wl_cut_join I) in Hin.
  apply elem_of_app in Hin as [Hin | Hin].
  - destruct (join_elem_of (bodies_of I) b Hin) as [-> | (l & Hl & Hbl)];
      [by right | left].
    apply elem_of_list_lookup in Hl as [k Hk].
    pose proof (disc_input_f_body I k l Hd Hk) as Hbok.
    pose proof (fbody_ok_bytes l Hbok) as Hfb.
    apply elem_of_list_lookup in Hbl as [q Hq].
    exact (proj1 (Forall_lookup _ _) Hfb q b Hq).
  - left. apply elem_of_list_lookup in Hin as [q Hq].
    exact (proj1 (Forall_lookup _ _) Hr q b Hq).
Qed.

Lemma fbody_byte_val (b : bv 8) :
  fbody_byte b ->
  bv_unsigned b = 32%Z \/ bv_unsigned b = 62%Z
  \/ (48 <= bv_unsigned b <= 57)%Z
  \/ (65 <= bv_unsigned b <= 90)%Z
  \/ (97 <= bv_unsigned b <= 122)%Z.
Proof using.
  intros [[Ha | ->] | ->].
  - destruct Ha as [H | [H | H]];
      [ right; right; by left
      | right; right; right; by left
      | right; right; right; by right ].
  - by left.
  - right. left. by vm_compute.
Qed.

Lemma disc_input_f_byte_ncr (I : list (bv 8)) (j : nat) :
  disc_input_f I -> (j < length I)%nat -> bv_unsigned (I !!! j) <> 13%Z.
Proof using.
  intros Hd Hj.
  destruct (lookup_lt_is_Some_2 I j Hj) as [b Hb].
  assert (Heq : I !!! j = b)
    by (rewrite list_lookup_total_alt Hb; reflexivity).
  rewrite Heq.
  destruct (disc_input_f_byte I b Hd (elem_of_list_lookup_2 I j b Hb))
    as [Hfb | Hnl].
  - destruct (fbody_byte_val b Hfb) as [H | [H | [H | [H | H]]]]; lia.
  - rewrite Hnl wl_nl_val. lia.
Qed.

(* THE RING'S TRANSLATION IS THE IDENTITY, at the file discipline
   ([ReadRec.disc_input_no_cr]'s twin, and the one reading
   [ReadRec.rr_byte_of_rows] takes). *)
Lemma disc_input_f_no_cr (I : list (bv 8)) (j : nat) :
  disc_input_f I -> (j < length I)%nat -> cons_xlate (I !!! j) = I !!! j.
Proof using.
  intros Hd Hj. pose proof (disc_input_f_byte_ncr I j Hd Hj) as Hv.
  rewrite /cons_xlate. rewrite decide_False; [reflexivity |].
  intro Hq. apply (f_equal bv_unsigned) in Hq.
  rewrite (_ : bv_unsigned (mword_of_int 13 : mword 8) = 13%Z) in Hq;
    [lia | by vm_compute].
Qed.

(* ...and the two the WALK spends beyond the leaf ([UkSh]'s [Hdsc_ncr] and
   [Hdsc_short]).  The third, [Hdsc_nl], is NOT here and cannot be: see
   this lane's findings. *)
Lemma disc_input_f_snoc_ncr (I : list (bv 8)) (b : bv 8) :
  disc_input_f (I ++ [b]) -> bv_unsigned b <> 13%Z.
Proof using.
  intro Hd.
  assert (Hat : (I ++ [b]) !!! length I = b).
  { rewrite list_lookup_total_alt (lookup_app_r I [b] (length I) ltac:(lia))
            Nat.sub_diag. reflexivity. }
  rewrite <- Hat.
  apply (disc_input_f_byte_ncr (I ++ [b]) (length I) Hd
           ltac:(rewrite length_app; cbn [length]; lia)).
Qed.

Lemma disc_input_f_rest_short (I : list (bv 8)) :
  disc_input_f I -> (S (length (rest_of I)) < line_max)%nat.
Proof using. by intros (_ & _ & H). Qed.

(* ...AND THE LINE THE NEWLINE CLOSED ([EchoDisc.disc_input_snoc_nl]'s
   twin): the body it completed parses, at any of the three
   constructors. *)
Lemma disc_input_f_snoc_nl (I : list (bv 8)) :
  disc_input_f (I ++ [wl_nl]) -> fbody_ok (rest_of I).
Proof using.
  intros (Hb & _ & _). rewrite bodies_of_snoc_nl in Hb.
  apply Forall_app in Hb as [_ Hb2]. by rewrite Forall_singleton in Hb2.
Qed.

(* ===================================================================== *)
(*  1b. THE FILE ERA'S [Hdsc_line] -- sh's loop leaf at the FILE          *)
(*      discipline, ending in a typed line the era admits.                *)
(*                                                                       *)
(*  [Hws] IS THE ONE MODEL FACT IT TAKES, and it is the lane's open item: *)
(*  [UkSh.ush_posw]'s index is [LineWords.last_ws] of the input, so the   *)
(*  loop's line has to answer [FileDisc.uline_ws lu = wl_words J].  That  *)
(*  holds at [LEcho] and [LEchoF] (whose [uline_ws] IS the parse) and NOT *)
(*  at [LCat], whose [uline_ws] is [[]] while a [cat f] line's words are  *)
(*  [wl_words cmd_cat_f].  See this lane's findings.                      *)
(* ===================================================================== *)
Lemma file_disc_line
    (Hws : forall J : list (bv 8),
       fbody_ok J -> uline_ws (uline_of J) = wl_words J)
    (I : list (bv 8)) (f : nat -> bv 8) :
  disc_input_f (I ++ [wl_nl]) ->
  (forall j : nat, (j < length (rest_of I))%nat -> f j = rest_of I !!! j) ->
  f (length (rest_of I)) = wl_nl ->
  exists lu : uline,
    UkShRedirBody.ush_line_file lu
    /\ uline_ws lu = wl_words (rest_of I)
    /\ length (line_bytes lu) = S (length (rest_of I))
    /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))).
Proof using.
  intros Hd Hby Hfnl.
  set (J := rest_of I) in *.
  pose proof (disc_input_f_snoc_nl I Hd) as Hok.
  destruct (fbody_ok_line J Hok) as [Huok Hbody].
  assert (Hlb : line_bytes (uline_of J) = J ++ [wl_nl])
    by (rewrite line_bytes_body -Hbody; reflexivity).
  exists (uline_of J).
  split; [ exact Logic.I | ].
  split; [ exact (Hws J Hok) | ].
  split; [ rewrite Hlb length_app; cbn [length]; lia | ].
  rewrite /UkSh.ush_line_at Hlb. split_and!.
  - exact Huok.
  - rewrite length_app. cbn [length]. lia.
  - intros j Hj. rewrite Nat.add_0_l.
    assert (Hnlat : (J ++ [wl_nl]) !!! length J = wl_nl).
    { pose proof (wl_lta_app_r J [wl_nl] 0%nat) as Hr.
      rewrite Nat.add_0_r in Hr. exact Hr. }
    destruct (Nat.eq_dec j (length J)) as [-> | Hne].
    + rewrite Hfnl Hnlat. reflexivity.
    + rewrite (Hby j ltac:(lia)).
      symmetry. exact (wl_lta_app_l J [wl_nl] j ltac:(lia)).
Qed.

(* ...AND THE THREE, BUNDLED: exactly what [UShKernel.sh_image_entry_at]
   takes of an era's line read, in its own order. *)
Lemma file_gets_holds
    (Hws : forall J : list (bv 8),
       fbody_ok J -> uline_ws (uline_of J) = wl_words J) :
  (forall (I : list (bv 8)) (b : bv 8),
     disc_input_f (I ++ [b]) -> bv_unsigned b <> 13%Z)
  /\ (forall I : list (bv 8),
        disc_input_f I -> (S (length (rest_of I)) < line_max)%nat)
  /\ (forall (I : list (bv 8)) (f : nat -> bv 8),
        disc_input_f (I ++ [wl_nl]) ->
        (forall j : nat, (j < length (rest_of I))%nat ->
           f j = rest_of I !!! j) ->
        f (length (rest_of I)) = wl_nl ->
        exists lu : uline,
          UkShRedirBody.ush_line_file lu
          /\ uline_ws lu = wl_words (rest_of I)
          /\ length (line_bytes lu) = S (length (rest_of I))
          /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I)))).
Proof using.
  split; [ exact disc_input_f_snoc_ncr | ].
  split; [ exact disc_input_f_rest_short | exact (file_disc_line Hws) ].
Qed.

(* ===================================================================== *)
(*  2.  THE RECORD                                                        *)
(* ===================================================================== *)
Section file_read_inst.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{!uartGhostG Σ}.
  Context `{GEN : GenId}.

  Local Notation FI := (FileLinkInst.file_link_inst g).

  Local Lemma fri_rd (k n : nat) (v : era_pins)
      (ws : list (list mobs * bv 8)) (Φ : iProp Σ) :
    ⊢ FileLinks.file_links g -∗ era_pin (fgn_echo g) k v -∗
      dl_cnt v (1/2) n -∗
      (FileLinks.fread_ret g k v n ws -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk #Hpin Hdl HΦ".
    iDestruct (FileLinks.file_links_rd with "Hlk") as "#Hrdl".
    iApply ("Hrdl" $! k v n ws with "Hpin Hdl HΦ").
  Qed.

  Local Lemma fri_rd_taint (k : nat) (ws : list (list mobs * bv 8))
      (Φ : iProp Σ) :
    ⊢ FileLinks.file_links g -∗ file_taint (fgn_cl g) -∗
      (file_taint (fgn_cl g) -∗ Φ) -∗
      cons_link Uart0 k (ConsLog.EvRead ws) Φ.
  Proof using .
    iIntros "#Hlk HT HΦ".
    iDestruct (FileLinks.file_links_rd_taint with "Hlk") as "#Hrdt".
    iApply ("Hrdt" $! k ws with "HT HΦ").
  Qed.

  (* THE WINDOW ARM at the file model: [ReadRec.eri_arms]'s proof with
     [FileLinks.fread_ret]'s own trailing disjunct, whose untainted side
     carries the era's FILE pin and the boot state's lower bound beside
     the writer's cursor -- which is exactly the extra conjunct
     [FileLinksLine.fwc_rres] has over [LinkRec.echo_rres]. *)
  Local Lemma fri_arms (v : era_pins) (I : list (bv 8))
      (ws sl sl' : list (list mobs * bv 8))
      (hs : list (list mobs)) (dd dc : nat) (g0 : nat -> bv 8) :
    (dd <= dc)%nat -> length ws = dc ->
    cons_window sl (length I) dd g0 hs ->
    sl `prefix_of` sl' ->
    (forall j : nat, (j < dc)%nat -> ws !! j = sl' !! (length I + j)%nat) ->
    ⊢ era_pin (fgn_echo g) (S gen_id) v -∗ inp_lb v I -∗
      FileLinksLine.fwc_rres g v I -∗
      FileLinks.fread_ret g (S gen_id) v (length I) ws -∗
      (dl_cnt v (1/2) (length I + dc)%nat
       ∗ ∃ J : list (bv 8),
           ⌜length J = dc⌝ ∗ ⌜disc_input_f (I ++ J)⌝
           ∗ ⌜(0 < dd)%nat -> g0 0%nat = J !!! 0%nat⌝
           ∗ inp_lb v (I ++ J) ∗ FileLinksLine.fwc_rres g v (I ++ J))
      ∨ file_taint (fgn_cl g).
  Proof using .
    intros Hddc Hlws Hwinf Hpre2 Hwsj.
    iIntros "#Hpin #HE0 #Hres0 Hret".
    rewrite /FileLinks.fread_ret.
    iDestruct "Hret" as "[[#HT _] | [Hdlr Hfacts]]"; [ by iRight | ].
    iDestruct "Hfacts" as (pops dl)
      "(%Hrok & %Hdl & %Hpref & %Hidx & %Hdsce & #HEin & %Hdinp & Hrest)".
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
    assert (HJdisc : disc_input_f (I ++ J)) by (rewrite <- HJ; exact Hdinp).
    iDestruct "Hrest" as "#Hrest".
    iAssert (FileLinksLine.fwc_rres g v (I ++ J)) as "#Hresn".
    { iDestruct "Hrest" as "[%Hws0 | Hbb]".
      - assert (Hdc0 : dc = 0%nat)
          by (rewrite <- Hlws, Hws0; reflexivity).
        assert (HJnil : J = []) by (apply nil_length_inv; lia).
        rewrite HJnil app_nil_r. iExact "Hres0".
      - iDestruct "Hbb" as (cs0 ps0 vf s0)
          "(#Hcs & #Hps & #Hvf & #Hf0 & _ & #Htlb & %Hrds)".
        rewrite /FileLinksLine.fwc_rres. iExists ps0, cs0, s0.
        rewrite <- HJ. iFrame "Htlb Hps Hcs".
        iSplitR; [ by iPureIntro | ].
        rewrite /FileLinksLine.f0w. iSplitR; [ by iPureIntro | ].
        iExists vf. iFrame "Hvf Hf0". }
    iAssert (inp_lb v (I ++ J)) as "#HEn";
      [ rewrite <- HJ; iExact "HEin" | ].
    iLeft. iFrame "Hdlr". iExists J.
    iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ].
    iSplitR; [ | iFrame "HEn Hresn" ].
    iPureIntro. intro Hdd0.
    exact (rr_byte_of_rows disc_input_f sl sl' ws dl hs pops I J dd dc g0
             disc_input_f_no_cr
             Hdd0 Hddc Hwinf Hpre2 Hwsj Hpref Hdl HJ HJdisc ltac:(lia)).
  Qed.

  Definition file_read_inst : ReadRec FI :=
    MkReadRec FI disc_input_f fri_rd fri_rd_taint fri_arms.

  Lemma file_read_inst_disc : rk_disc FI file_read_inst = disc_input_f.
  Proof using . reflexivity. Qed.

End file_read_inst.

(* ===================================================================== *)
(*  3.  SH'S READ LEAF AT THE FILE ERA -- ONE APPLICATION                 *)
(* ===================================================================== *)
Section file_read_leaf.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).

  Local Notation FI := (FileLinkInst.file_link_inst g).

  (* the pieces' own pin IS the record's -- [FileLinkInst] sets
     [lk_pin := era_pin (fgn_echo g)] -- so the bridge is the identity *)
  Lemma file_ep_refl (v : era_pins) :
    ⊢ era_pin (fgn_echo g) (S gen_id) v -∗ lk_pin FI (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  Lemma file_read_leaf_holds (Wb : list (bv 8) -> iProp Σ)
      (N : uk_names Σ) (γp : gname) (l : list fdstate) :
    ukn_pay N
      = ucons_pay fsc_cons γp (lk_T FI)
          (UShLine.ush_rd_x_at (lk_rres FI) (fgn_echo g) Wb) ->
    (⊢ app_sup -∗ lk_T FI) ->
    (⊢ lk_T FI -∗ app_sup) ->
    (⊢ lk_links FI) ->
    ⊢ UkSh.ush_read_recv_leaf_at (PS := uprogSG_free) N γp (lk_T FI)
        (UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp)
        (rk_disc FI (file_read_inst g)) fsc_cons l.
  Proof using .
    intros Hpay Hst Hts Hlk.
    iApply (UShLine.ush_read_recv_leaf_holds_at (file_read_inst g)
              (fgn_echo g) Wb N γp l Hpay Hst Hts file_ep_refl Hlk).
  Qed.

End file_read_leaf.
