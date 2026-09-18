(* ===================================================================== *)
(*  FileLinksAtPro.v -- /INIT'S TWO PAYABLE DIAGNOSTICS AT THE FILE       *)
(*  CLAIM, AT A NAMED BOOT STATE (lane INIT-FILE, ruling H').             *)
(*                                                                       *)
(*  [EchoLinksPro.v] is this family at the ECHO claim: the round-open     *)
(*  credential [ewc_pro] that /init's banner leaves, the family           *)
(*  [ewc_pdiag] of a prologue alternative's bytes on their way out (byte  *)
(*  0 through the prologue-choice link, the rest through the ordinary     *)
(*  write link), and the end shape of alternative 1 -- the NEXT failed    *)
(*  sub-round's banner, owed at the same input.  The two alternatives are *)
(*  /init's own diagnostics, init: exec sh failed and init: fork failed.  *)
(*  This file is that family at the FILE claim, with the era's boot state *)
(*  [s0] HOISTED out of the existential, exactly as [FileLinksAt.v]       *)
(*  hoists it out of the twelve families of [FileLinksLine.v].            *)
(*                                                                       *)
(*  THE PURE HALF IS SHARED AND NOT TWINNED WHERE IT CAN BE.  The         *)
(*  prologue ([pro_of], [pro_from], [pro_done], [pro_fail], [pro_rounds], *)
(*  [pro_alts], /init's banner, the shell's prompt) is [EchoDisc]'s and   *)
(*  the file application runs the same /init, so [EchoLinksPro]'s         *)
(*  [pro_alts_1_length], [pro_alts_lt_of_lookup], [pro_of_fail_snoc] and  *)
(*  [pro_round_alts] are IMPORTED.  What IS restated is the CURSOR        *)
(*  condition, and only because the file's cursor is a different function *)
(*  of a different stage: where echo reads [EchoOutPure.proc_stream] and  *)
(*  tests [cs !!! (nlines I - 1) = 3], the file reads                     *)
(*  [FileOutPure.proc_stream_f ps cs (Some s0) I] -- the era's boot state *)
(*  threaded -- and tests [ralt_panic (ralt_at cs (nlines I - 1))], so    *)
(*  the two new line shapes' fork alternatives open a round too.  That is *)
(*  the same recipe [FileLinksLine] used to relate [wr_banp_f] to echo's  *)
(*  [wr_ban]: the shapes are restated at the file model, the prologue     *)
(*  arithmetic under them is not.                                        *)
(*                                                                       *)
(*  WHY THE FAMILY'S BASE IS [fwc_pban_at] AND NOT [FileLinksAt.          *)
(*  fwc_pro_at].  A diagnostic's LAST byte has to land on the next        *)
(*  sub-round's banner credential ([fwc_ban_at] at 0), whose pure shape   *)
(*  [FileLinksLine.wr_ban_f] says the round's open prologue is            *)
(*  [pro_fail j] -- j whole failed sub-rounds and nothing else.           *)
(*  [FileLinksLine.wr_pro_f] says only that the open prologue is not      *)
(*  DONE, i.e. some list over the continuing letters [1] and [3]          *)
(*  ([EchoDisc.pro_cont]), which does not pin [pro_fail j ++ [3]]; and    *)
(*  filing [1] against an unpinned open prologue gives no [pro_fail]      *)
(*  either.  So [fwc_pro_at] is strictly too weak to be the base, and the *)
(*  base is the file twin of [EchoLinksPro.ewc_pro]: [wr_pro_f] PLUS the  *)
(*  open prologue's shape, which is exactly what the banner's own         *)
(*  credential already holds ([fwc_pban_of_ban_done_at], the entry        *)
(*  point).  The projection [fwc_pro_of_pban_at] connects the base back   *)
(*  to [fwc_pro_at] in the direction that IS sound.                       *)
(*                                                                       *)
(*  A LEAF FILE: nothing is below it, so the program stream does not move *)
(*  when it does.                                                        *)
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
Require Import FileState.
Require Import FileDisc.
Require Import FileOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileLinksLine.
Require Import FileLinksAt.
Require Import EchoLinks.
Require Import EchoLinksPro.    (* the SHARED prologue arithmetic *)
Require Import LinkRec.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Local Open Scope list_scope.


(* ===================================================================== *)
(*  S1  THE PURE SHAPES, AT THE FILE MODEL                                *)
(* ===================================================================== *)

(* the round-opening block, spelt with [FileLinksLine.wr_pre_f] --
   [FileOutPure.pending_at_f_round_pre] with its constant named *)
Lemma pending_at_f_round_wr_pre (ps cs : list nat) (s0 : fst)
    (I : list (bv 8)) :
  rest_of I = [] ->
  (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true) ->
  pending_at_f ps cs (Some s0) I
  = wr_pre_f I ++ pro_of (pro_from (pro_idx_f cs (nlines I)) ps).
Proof using.
  intros Hm Hr. rewrite (pending_at_f_round_pre ps cs (Some s0) I Hm Hr).
  by rewrite /wr_pre_f.
Qed.

(* ===================================================================== *)
(*  THE ROUND-OPEN SHAPE AFTER A BANNER, at the file model:               *)
(*  [EchoLinksPro.wr_pban]'s twin.  A bare [wr_pro_f] says only that the  *)
(*  round is open (any word over the continuing letters), which is not    *)
(*  enough to place the diagnostic's bytes nor to read the next banner    *)
(*  off the end of alternative 1.                                        *)
(* ===================================================================== *)
Definition wr_pban_f (ps cs : list nat) (s0 : fst) (I : list (bv 8))
    (P : nat) : Prop :=
  wr_pro_f ps cs s0 I P
  /\ (exists j : nat,
        pro_from (pro_idx_f cs (nlines I)) ps = pro_fail j ++ [3%nat]).

Lemma wr_pban_of_ban_f (ps cs : list nat) (s0 : fst) (I : list (bv 8))
    (P : nat) :
  wr_ban_f ps cs s0 I P ->
  wr_pban_f (ps ++ [3%nat]) cs s0 I (P + length u_banner)%nat.
Proof using.
  intros Hw. split; [exact (wr_ban_done_f ps cs s0 I P Hw) |].
  destruct (wr_ban_filed_f ps cs s0 I P Hw) as (j & Hj & _). by exists j.
Qed.

Lemma wr_pban_pro_f (ps cs : list nat) (s0 : fst) (I : list (bv 8))
    (P : nat) : wr_pban_f ps cs s0 I P -> wr_pro_f ps cs s0 I P.
Proof using. by intros [H _]. Qed.

(* ===================================================================== *)
(*  THE SHAPE: alternative [a] filed at the round's open prologue, [i] of *)
(*  its bytes out.  [EchoLinksPro.wr_pdiag] at the file's stage.          *)
(* ===================================================================== *)
Definition wr_pdiag_f (ps cs : list nat) (s0 : fst) (I : list (bv 8))
    (P a i : nat) : Prop :=
  pro_pin_f ps cs I
  /\ rest_of I = []
  /\ nlines I = length cs
  /\ (I = [] \/ ralt_panic (ralt_at cs (nlines I - 1)%nat) = true)
  /\ (exists j : nat,
        pro_from (pro_idx_f cs (nlines I)) ps = pro_fail j ++ [3%nat; a]
        /\ P = (length (proc_before_f ps cs (Some s0) I) + length (wr_pre_f I)
                + pro_round * j + length u_banner + i)%nat).

(* THE BYTE AT THE CURSOR is the alternative's [i]-th. *)
Lemma wr_pdiag_byte_f (ps cs : list nat) (s0 : fst) (I : list (bv 8))
    (P a i : nat) (b : bv 8) :
  wr_pdiag_f ps cs s0 I P a i -> pro_alts !!! a !! i = Some b ->
  proc_stream_f ps cs (Some s0) I !! P = Some b.
Proof using.
  intros (Hpin & Hm & Hdv & Hr & (j & Hj & HP)) Hb.
  rewrite /proc_stream_f (pending_at_f_round_wr_pre ps cs s0 I Hm Hr) Hj
          pro_of_fail_snoc HP.
  replace (length (proc_before_f ps cs (Some s0) I) + length (wr_pre_f I)
           + pro_round * j + length u_banner + i)%nat
    with (length (proc_before_f ps cs (Some s0) I)
          + (length (wr_pre_f I)
             + (length (pro_of (pro_fail j)) + (length u_banner + i))))%nat
    by (rewrite pro_of_fail_length; lia).
  rewrite (lookup_app_shift (proc_before_f ps cs (Some s0) I))
          (lookup_app_shift (wr_pre_f I))
          (lookup_app_shift (pro_of (pro_fail j))) (lookup_app_shift u_banner).
  exact Hb.
Qed.

(* THE CHOICE BYTE: filing [a] at the round-open shape after a banner is
   this shape one byte in. *)
Lemma wr_pdiag_1_of_pban_f (ps cs : list nat) (s0 : fst) (I : list (bv 8))
    (P a : nat) :
  wr_pban_f ps cs s0 I P -> wr_pdiag_f (ps ++ [a]) cs s0 I (S P) a 1%nat.
Proof using.
  intros ((Hpin & Hm & Hdv & Hr & Hnd & HP) & (j & Hj)).
  assert (Hle : (pro_idx_f cs (nlines I) <= pro_rounds ps)%nat)
    by exact (pro_pin_f_round_le ps cs I Hm Hr Hpin).
  assert (Hpre : ps `prefix_of` (ps ++ [a])) by by eexists.
  (* the stream strictly below [I] does not read the new choice *)
  assert (Hlow : proc_before_f (ps ++ [a]) cs (Some s0) I
                 = proc_before_f ps cs (Some s0) I).
  { symmetry. apply proc_before_f_ext. intros J HJ Hne.
    apply (pending_at_f_ps_ext ps (ps ++ [a]) cs (Some s0) J Hpre).
    exact (pro_pin_f_at ps cs I (nlines J) Hpin (nstarted_strict J I HJ Hne)). }
  assert (H3 : length (pro_of (pro_fail j ++ [3%nat]))
               = (pro_round * j + length u_banner)%nat).
  { rewrite (pro_of_open_app _ _ (pro_done_fail j)) pro_of_singleton pro_alts_3.
    rewrite length_app pro_of_fail_length. reflexivity. }
  rewrite /wr_pdiag_f. split_and!.
  - exact (pro_pin_f_mono ps (ps ++ [a]) cs I Hpre Hpin).
  - exact Hm.
  - exact Hdv.
  - exact Hr.
  - exists j. split.
    + rewrite (pro_from_snoc_le _ ps a Hle) Hj. by rewrite -app_assoc.
    + rewrite Hlow HP /proc_stream_f
              (length_app (proc_before_f ps cs (Some s0) I))
              (pending_at_f_round_wr_pre ps cs s0 I Hm Hr)
              (length_app (wr_pre_f I)) Hj H3. lia.
Qed.

(* EVERY LATER BYTE moves the cursor by one and nothing else. *)
Lemma wr_pdiag_S_f (ps cs : list nat) (s0 : fst) (I : list (bv 8))
    (P a i : nat) :
  wr_pdiag_f ps cs s0 I P a i -> wr_pdiag_f ps cs s0 I (S P) a (S i).
Proof using.
  intros (Hpin & Hm & Hdv & Hr & (j & Hj & HP)).
  split_and!; try assumption. exists j. split; [exact Hj | lia].
Qed.

(* THE END OF ALTERNATIVE 1: the writer stands at the banner of the NEXT
   failed sub-round -- [wr_ban_f] with [S j] sub-rounds, at the same
   count.  [pro_round] is exactly the banner and this diagnostic, which is
   the whole arithmetic. *)
Lemma wr_pdiag_done_1_f (ps cs : list nat) (s0 : fst) (I : list (bv 8))
    (P i : nat) :
  i = length (pro_alts !!! 1%nat) ->
  wr_pdiag_f ps cs s0 I P 1%nat i -> wr_ban_f ps cs s0 I P.
Proof using.
  intros Hi (Hpin & Hm & Hdv & Hr & (j & Hj & HP)).
  assert (Hb : length u_banner = 18%nat) by (vm_compute; reflexivity).
  assert (Ha : length (pro_alts !!! 1%nat) = 21%nat)
    by (vm_compute; reflexivity).
  assert (Hrd : pro_round = 39%nat) by (vm_compute; reflexivity).
  rewrite /wr_ban_f. split_and!; try assumption.
  exists (S j). split.
  - rewrite Hj. by rewrite pro_fail_S.
  - rewrite HP Hi Hb Ha Hrd. lia.
Qed.


Section file_links_at_pro.
  Context {Σ : gFunctors}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).
  Context `{HRg : !riscvGS Σ}.
  Context `{GEN : GenId}.

  Local Notation FT := (file_taint (fgn_cl g)).
  Local Notation FPIN := (era_pin (fgn_echo g)).

  (* =================================================================== *)
  (*  S2  THE ROUND-OPEN CREDENTIAL AFTER A BANNER, AT THE NAMED STATE    *)
  (* =================================================================== *)
  Definition fwc_pban_at (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_pban_f ps cs s0 I P⌝ ∗ fcur g v ps cs s0 I P k) ∨ FT)%I.

  Global Instance fwc_pban_at_timeless s0 k v I :
    Timeless (fwc_pban_at s0 k v I).
  Proof using . rewrite /fwc_pban_at. apply _. Qed.

  Lemma fwc_pban_at_taint s0 k v I : FT -∗ fwc_pban_at s0 k v I.
  Proof using . iIntros "H". rewrite /fwc_pban_at. by iRight. Qed.

  (* ...it is one arm of what the round already owed... *)
  Lemma fwc_pro_of_pban_at (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) :
    fwc_pban_at s0 k v I -∗ fwc_pro_at g s0 k v I.
  Proof using .
    rewrite /fwc_pban_at /fwc_pro_at.
    iIntros "[H | #HT]"; last by (iRight; iRight).
    iDestruct "H" as (ps cs P) "[%Hw Hc]".
    iLeft. iExists ps, cs, P. iFrame "Hc". iPureIntro.
    exact (wr_pban_pro_f ps cs s0 I P Hw).
  Qed.

  (* ...and it is EXACTLY what the last banner byte leaves. *)
  Lemma fwc_pban_of_ban_done_at (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) :
    fwc_ban_at g s0 k v I (length u_banner) -∗ fwc_pban_at s0 k v I.
  Proof using .
    rewrite /fwc_ban_at /fwc_pban_at.
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18.
    iIntros "[H | [[%Hq _] | #HT]]"; [| discriminate Hq | by iRight].
    iDestruct "H" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    cbn [wr_banp_f] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3%nat]), cs, (P + 18)%nat. rewrite /fcur.
    iFrame "Htn Hps Hcs HE Hf". iPureIntro.
    pose proof (wr_pban_of_ban_f ps' cs s0 I P Hw) as H. by rewrite H18 in H.
  Qed.

  (* =================================================================== *)
  (*  S3  THE DIAGNOSTIC'S BYTES, AT THE NAMED STATE                      *)
  (*                                                                     *)
  (*  The round's choice [a] filed with [i] of its bytes out.  [0] is the *)
  (*  round-open credential itself (nothing filed yet); byte 0 goes       *)
  (*  through [FileLinks.file_link_pro], which files [ps ++ [a]]; every   *)
  (*  later byte through [FileLinks.file_link_w].                         *)
  (* =================================================================== *)
  Definition fwc_pdg_at (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) (a i : nat) : iProp Σ :=
    ((∃ (ps cs : list nat) (P : nat),
        ⌜wr_pdiag_f ps cs s0 I P a i⌝ ∗ fcur g v ps cs s0 I P k) ∨ FT)%I.

  Definition fwc_pdiag_at (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) (a i : nat) : iProp Σ :=
    match i with
    | O => fwc_pban_at s0 k v I
    | S _ => fwc_pdg_at s0 k v I a i
    end.

  Global Instance fwc_pdg_at_timeless s0 k v I a i :
    Timeless (fwc_pdg_at s0 k v I a i).
  Proof using . rewrite /fwc_pdg_at. apply _. Qed.
  Global Instance fwc_pdiag_at_timeless s0 k v I a i :
    Timeless (fwc_pdiag_at s0 k v I a i).
  Proof using . rewrite /fwc_pdiag_at. destruct i; apply _. Qed.

  (* the taint is at EVERY state, and at every byte count *)
  Lemma fwc_pdg_at_taint s0 k v I a i : FT -∗ fwc_pdg_at s0 k v I a i.
  Proof using . iIntros "H". rewrite /fwc_pdg_at. by iRight. Qed.

  Lemma fwc_pdiag_at_taint s0 k v I a i : FT -∗ fwc_pdiag_at s0 k v I a i.
  Proof using .
    iIntros "H". rewrite /fwc_pdiag_at. destruct i.
    - by iApply fwc_pban_at_taint.
    - by iApply fwc_pdg_at_taint.
  Qed.

  (* the family's start IS the round-open credential (definitionally) *)
  Lemma fwc_pdiag_at_0 (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) (a : nat) :
    fwc_pban_at s0 k v I -∗ fwc_pdiag_at s0 k v I a 0%nat.
  Proof using . by iIntros "$". Qed.

  (* ...and it is at least the round's own owed credential *)
  Lemma fwc_pdiag_at_pro (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) (a : nat) :
    fwc_pdiag_at s0 k v I a 0%nat -∗ fwc_pro_at g s0 k v I.
  Proof using . iIntros "H". by iApply fwc_pro_of_pban_at. Qed.

  (* ONE BYTE, at either link. *)
  Lemma fpdiag_step_at (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) (a i : nat) (b : bv 8) (Φ : iProp Σ) :
    pro_alts !!! a !! i = Some b ->
    FPIN k v -∗ FileLinks.file_links g -∗
    fwc_pdiag_at s0 k v I a i -∗
    (fwc_pdiag_at s0 k v I a (S i) -∗ Φ) -∗ out_link Uart0 k b Φ.
  Proof using .
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (file_links_w with "Hlk") as "#Hw".
    iDestruct (file_links_pro with "Hlk") as "#Hpro".
    iDestruct (file_links_taint with "Hlk") as "#Ht".
    pose proof (pro_alts_lt_of_lookup a i b Hb) as Ha.
    destruct i as [| i'].
    - (* byte 0: the round's choice byte, through the prologue link *)
      rewrite /fwc_pdiag_at /fwc_pban_at /fwc_pdg_at /fcur /f0w.
      iDestruct "Hc" as "[Hl | #HT]"; last first.
      { iApply ("Ht" $! k b Φ with "HT [HΦ]").
        iIntros "#HT'". iApply "HΦ". by iRight. }
      iDestruct "Hl" as (ps cs P)
        "(%Hw & Htn & #Hps & #Hcs & #HE & %Hk & Hvf)".
      iDestruct "Hvf" as (vf) "[#Hfe #Hf0]".
      pose proof (wr_pdiag_1_of_pban_f ps cs s0 I P a Hw) as Hw'.
      destruct Hw as ((Hpin0 & Hm & Hdv & Hr & Hnd & HP) & _).
      iApply ("Hpro" $! k v vf P a b ps cs s0 I Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Hfe Htn Hps Hcs HE Hf0 [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin0. }
      { exact Hnd. }
      { exact HP. }
      { exact Ha. }
      { exact Hb. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists (ps ++ [a]), cs, (S P).
      iSplitR; [by iPureIntro |]. iFrame "Htn' Hps' Hcs' HE'".
      iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hfe Hf0'".
    - (* bytes 1..: ordinary bytes of the alternative just filed *)
      rewrite /fwc_pdiag_at /fwc_pdg_at /fcur /f0w.
      iDestruct "Hc" as "[Hl | #HT]"; last first.
      { iApply ("Ht" $! k b Φ with "HT [HΦ]").
        iIntros "#HT'". iApply "HΦ". by iRight. }
      iDestruct "Hl" as (ps cs P)
        "(%Hw & Htn & #Hps & #Hcs & #HE & %Hk & Hvf)".
      iDestruct "Hvf" as (vf) "[#Hfe #Hf0]".
      pose proof (wr_pdiag_byte_f ps cs s0 I P a (S i') b Hw Hb) as Hby.
      pose proof (wr_pdiag_S_f ps cs s0 I P a (S i') Hw) as Hw'.
      destruct Hw as (Hpin0 & Hm & Hdv & Hr & _).
      iApply ("Hw" $! k v vf P b ps cs s0 I Φ
                with "[%] [%] [%] Hpin Hfe Htn Hps Hcs HE Hf0 [HΦ]").
      { lia. }
      { exact Hpin0. }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE' & Hf0') | #HT]";
        last by iRight.
      iLeft. iExists ps, cs, (S P).
      iSplitR; [by iPureIntro |]. iFrame "Htn' Hps' Hcs' HE'".
      iSplitR; [by iPureIntro |]. iExists vf. by iFrame "Hfe Hf0'".
  Qed.

  (* THE END SHAPE OF ALTERNATIVE 1: the next sub-round's banner is owed
     at the SAME input, which is the credential /init's restart head pays
     its banner from.  Alternative 2 has no end shape: the round is
     terminal and the credential is dropped (affine). *)
  Lemma fwc_pdiag_at_done_1 (s0 : fst) (k : nat) (v : era_pins)
      (I : list (bv 8)) (i : nat) :
    i = length (pro_alts !!! 1%nat) ->
    fwc_pdiag_at s0 k v I 1%nat i -∗ fwc_ban_at g s0 k v I 0%nat.
  Proof using .
    intros Hi. rewrite Hi pro_alts_1_length.
    rewrite /fwc_pdiag_at /fwc_pdg_at /fcur /fwc_ban_at.
    iIntros "[Hl | #HT]"; last by (iRight; iRight).
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE & #Hf)".
    iLeft. iExists ps, cs, P. rewrite Nat.add_0_r.
    iSplitR.
    { iPureIntro. cbn [wr_banp_f].
      exact (wr_pdiag_done_1_f ps cs s0 I P 21%nat
               (eq_sym pro_alts_1_length) Hw). }
    by iFrame "Htn Hps Hcs HE Hf".
  Qed.

End file_links_at_pro.
