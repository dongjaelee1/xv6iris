(* ===================================================================== *)
(*  EchoLinksPro.v -- /INIT'S TWO PAYABLE DIAGNOSTICS THROUGH THE LINKS   *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane INIT-DIAG, the      *)
(*   preparation for IO-LEAF M6b.)                                        *)
(*                                                                       *)
(*  Two of /init's three failure messages are PROLOGUE ALTERNATIVES of    *)
(*  the transcript ([EchoDisc.pro_alts]):                                 *)
(*                                                                       *)
(*    1  "init: exec sh failed\n"   the child /init forked could not exec  *)
(*                                  the shell; it prints this and exits,   *)
(*                                  /init reaps it and prints its banner   *)
(*                                  AGAIN -- the round gets one more       *)
(*                                  failed sub-round;                      *)
(*    2  "init: fork failed\n"      /init could not fork; it exits and     *)
(*                                  nothing follows on this wire.          *)
(*                                                                       *)
(*  Both start where /init's banner leaves the era's write credential:    *)
(*  the round's prologue OPEN after the banner LETTER with the next byte  *)
(*  its choice byte, the pure shape [wr_pban] ([EchoLinks.wr_pro] plus    *)
(*  the open prologue's shape [pro_fail j ++ [3]]).  This file states     *)
(*  that credential EXACTLY ([ewc_pro]: [EchoLinks.ewc_owed] is the       *)
(*  disjunction with                                                      *)
(*  [wr_blk], which is what /init lends the shell but MORE than the       *)
(*  banner leaves and, as [wr_owed_ambiguous] shows, not recoverable      *)
(*  from it), the family of the diagnostic's bytes on their way out       *)
(*  ([ewc_pdiag], byte 0 through the prologue-choice link, the rest       *)
(*  through the ordinary write link), and where the family ENDS: for      *)
(*  alternative 1 at the NEXT sub-round's banner credential at the SAME   *)
(*  count ([EchoLinks.ewc_ban] at [0]) -- the shape /init's restart head  *)
(*  already pays its banner from -- and for alternative 2 nowhere (the    *)
(*  round is terminal; the credential is dropped, affine).                *)
(*                                                                       *)
(*  ON THE SAME MOULD AS [EchoLinks]: the pure shapes first, then the      *)
(*  section at [Context (T) (γ)], every pure fact about a literal by      *)
(*  [vm_compute] in a small closed lemma.                                 *)
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
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import EchoOut.
Require Import EchoLinks.
(* as in EchoLinks: the Sail imports leave string_scope on top and [++]
   would elaborate as String.append. *)
Local Open Scope list_scope.


(* ===================================================================== *)
(*  THE LITERALS, BY COMPUTATION.  [pro_round] is one failed sub-round in *)
(*  wire bytes -- the banner and the exec diagnostic -- and that is the   *)
(*  arithmetic fact the end shape of alternative 1 turns on.              *)
(* ===================================================================== *)
Lemma pro_alts_1_length : length (pro_alts !!! 1%nat) = 21%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma pro_alts_2_length : length (pro_alts !!! 2%nat) = 18%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma pro_round_alts :
  pro_round = (length u_banner + length (pro_alts !!! 1%nat))%nat.
Proof. vm_compute. reflexivity. Qed.

(* a byte read out of an alternative says the alternative exists *)
Lemma pro_alts_lt_of_lookup (a i : nat) (b : bv 8) :
  pro_alts !!! a !! i = Some b -> (a < length pro_alts)%nat.
Proof.
  intros Hb.
  destruct (decide (a < length pro_alts)%nat) as [Hlt | Hge];
    [exact Hlt | exfalso].
  rewrite list_lookup_total_alt in Hb.
  rewrite (lookup_ge_None_2 pro_alts a ltac:(lia)) in Hb.
  cbn in Hb. discriminate.
Qed.

(* ===================================================================== *)
(*  THE OPEN ROUND WITH ITS BANNER AND ITS ALTERNATIVE FILED.  An open     *)
(*  prologue at init's restart head is [j] failed sub-rounds              *)
(*  ([EchoDisc.pro_fail j] = banner, exec failure, ...) and then the      *)
(*  banner LETTER init has just written ([pro_alts !!! 3]); filing [a]    *)
(*  after it appends the alternative's bytes ([pro_of_open_app]).         *)
(* ===================================================================== *)
Lemma pro_of_fail_snoc (j a : nat) :
  pro_of (pro_fail j ++ [3%nat; a])
  = pro_of (pro_fail j) ++ u_banner ++ pro_alts !!! a.
Proof.
  rewrite (pro_of_open_app _ _ (pro_done_fail j)).
  cbn [pro_of]. rewrite pro_alts_3 (pro_more_cont 3%nat _ ltac:(by right)).
  rewrite /pro_more. case_decide; by rewrite app_nil_r.
Qed.

(* the round-opening block, spelt with [EchoLinks.wr_pre] *)
Lemma pending_n_round_wr_pre (ps cs : list nat) (n : nat) :
  (n `mod` length echo_line)%nat = 0%nat ->
  (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
  pending_n ps cs n
  = wr_pre cs n ++ pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps).
Proof. intros Hm Hr. rewrite /wr_pre. exact (pending_n_round_pre ps cs n Hm Hr). Qed.

(* ===================================================================== *)
(*  THE ROUND-OPEN SHAPE AFTER A BANNER: [wr_pro] whose open prologue is  *)
(*  [pro_fail j ++ [3]] -- what the eighteenth banner byte leaves         *)
(*  ([EchoLinks.wr_ban_done] + [wr_ban_filed]) and what the diagnostics   *)
(*  start from.  A bare [wr_pro] says only that the round is open (any    *)
(*  word over the continuing letters), which is not enough to place the   *)
(*  diagnostic's bytes.                                                   *)
(* ===================================================================== *)
Definition wr_pban (ps cs : list nat) (n P : nat) : Prop :=
  wr_pro ps cs n P
  /\ (exists j : nat,
        pro_from (pro_idx cs (n `div` length echo_line)) ps = pro_fail j ++ [3%nat]).

Lemma wr_pban_of_ban (ps cs : list nat) (n P : nat) :
  wr_ban ps cs n P -> wr_pban (ps ++ [3%nat]) cs n (P + length u_banner)%nat.
Proof.
  intros Hw. split; [exact (wr_ban_done ps cs n P Hw) |].
  destruct (wr_ban_filed ps cs n P Hw) as (j & Hj & _). by exists j.
Qed.

(* ===================================================================== *)
(*  THE SHAPE: alternative [a] filed at the round's open prologue, [i] of *)
(*  its bytes out.  [wr_ban]'s conjuncts with the open prologue now       *)
(*  [pro_fail j ++ [3; a]] and the cursor past the [j]-th sub-round, the  *)
(*  banner and [i] bytes of the alternative.                              *)
(* ===================================================================== *)
Definition wr_pdiag (ps cs : list nat) (n P a i : nat) : Prop :=
  pro_pin ps cs n
  /\ (n `mod` length echo_line)%nat = 0%nat
  /\ (n `div` length echo_line)%nat = length cs
  /\ (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat)
  /\ (exists j : nat,
        pro_from (pro_idx cs (n `div` length echo_line)) ps
        = pro_fail j ++ [3%nat; a]
        /\ P = (length (proc_upto ps cs n) + length (wr_pre cs n)
                + pro_round * j + length u_banner + i)%nat).

(* THE BYTE AT THE CURSOR is the alternative's [i]-th. *)
Lemma wr_pdiag_byte (ps cs : list nat) (n P a i : nat) (b : bv 8) :
  wr_pdiag ps cs n P a i -> pro_alts !!! a !! i = Some b ->
  proc_upto ps cs (S n) !! P = Some b.
Proof.
  intros (Hpin & Hm & Hdv & Hr & (j & Hj & HP)) Hb.
  rewrite proc_upto_snoc (pending_n_round_wr_pre ps cs n Hm Hr) Hj
          pro_of_fail_snoc HP.
  replace (length (proc_upto ps cs n) + length (wr_pre cs n)
           + pro_round * j + length u_banner + i)%nat
    with (length (proc_upto ps cs n)
          + (length (wr_pre cs n)
             + (length (pro_of (pro_fail j)) + (length u_banner + i))))%nat
    by (rewrite pro_of_fail_length; lia).
  rewrite (lookup_app_shift (proc_upto ps cs n)) (lookup_app_shift (wr_pre cs n))
          (lookup_app_shift (pro_of (pro_fail j))) (lookup_app_shift u_banner).
  exact Hb.
Qed.

(* THE CHOICE BYTE: filing [a] at the round-open shape after a banner is
   this shape one byte in.  The same step as [EchoLinks.wr_pro_dollar] at
   [a = 0], for any [a]. *)
Lemma wr_pdiag_1_of_pro (ps cs : list nat) (n P a : nat) :
  wr_pban ps cs n P -> wr_pdiag (ps ++ [a]) cs n (S P) a 1%nat.
Proof.
  intros ((Hpin & Hm & Hdv & Hr & Hnd & HP) & (j & Hj)).
  assert (Hle : (pro_idx cs (n `div` length echo_line) <= pro_rounds ps)%nat)
    by exact (pro_pin_idx_le ps cs n Hpin).
  assert (Hpre : ps `prefix_of` (ps ++ [a])) by by eexists.
  (* the stream below [n] does not read the new choice *)
  assert (Hlow : proc_upto (ps ++ [a]) cs n = proc_upto ps cs n).
  { symmetry. rewrite /proc_upto. apply proc_upto_from_ext.
    intros k _ Hk. apply (pending_n_ps_ext ps (ps ++ [a]) cs k Hpre).
    apply (pro_pin_at ps cs n k Hpin). lia. }
  assert (H3 : length (pro_of (pro_fail j ++ [3%nat])) = (pro_round * j + length u_banner)%nat).
  { rewrite (pro_of_open_app _ _ (pro_done_fail j)) pro_of_singleton pro_alts_3.
    rewrite length_app pro_of_fail_length. reflexivity. }
  rewrite /wr_pdiag. split_and!.
  - exact (pro_pin_mono ps (ps ++ [a]) cs n Hpre Hpin).
  - exact Hm.
  - exact Hdv.
  - exact Hr.
  - exists j. split.
    + rewrite (pro_from_snoc_le _ ps a Hle) Hj. by rewrite -app_assoc.
    + rewrite Hlow HP proc_upto_snoc (length_app (proc_upto ps cs n))
              (pending_n_round_wr_pre ps cs n Hm Hr) (length_app (wr_pre cs n))
              Hj H3. lia.
Qed.

(* EVERY LATER BYTE moves the cursor by one and nothing else. *)
Lemma wr_pdiag_S (ps cs : list nat) (n P a i : nat) :
  wr_pdiag ps cs n P a i -> wr_pdiag ps cs n (S P) a (S i).
Proof.
  intros (Hpin & Hm & Hdv & Hr & (j & Hj & HP)).
  split_and!; try assumption. exists j. split; [exact Hj | lia].
Qed.

(* THE END OF ALTERNATIVE 1: the writer stands at the banner of the NEXT
   failed sub-round -- [wr_ban] with [S j] sub-rounds, at the same count.
   [pro_round] is exactly the banner and this diagnostic, which is the
   whole arithmetic. *)
Lemma wr_pdiag_done_1 (ps cs : list nat) (n P i : nat) :
  i = length (pro_alts !!! 1%nat) ->
  wr_pdiag ps cs n P 1%nat i -> wr_ban ps cs n P.
Proof.
  intros Hi (Hpin & Hm & Hdv & Hr & (j & Hj & HP)).
  assert (Hb : length u_banner = 18%nat) by (vm_compute; reflexivity).
  assert (Ha : length (pro_alts !!! 1%nat) = 21%nat)
    by (vm_compute; reflexivity).
  assert (Hrd : pro_round = 39%nat) by (vm_compute; reflexivity).
  rewrite /wr_ban. split_and!; try assumption.
  exists (S j). split.
  - rewrite Hj. by rewrite pro_fail_S.
  - rewrite HP Hi Hb Ha Hrd. lia.
Qed.

(* ===================================================================== *)
(*  WHY [wr_pro] HAS TO BE KEPT AND NOT RECOVERED.  At a round-opening    *)
(*  boundary the two arms of [wr_owed] are BOTH inhabited, at the same    *)
(*  count and at prefix-comparable line choices: after one line whose     *)
(*  block was the shell's fork panic, the round is open ([wr_pro] at      *)
(*  [cs = [3]], nothing of the new round predicted); after one line whose *)
(*  block is still owed, it is not ([wr_blk] at [cs = []]).  Nothing      *)
(*  /init holds -- it names no line choice, and the era's two bounds are  *)
(*  persistent lower bounds, so [cs_lb v [3]] and [cs_lb v []] sit side   *)
(*  by side -- separates them.  So a holder of [ewc_owed] cannot get      *)
(*  [ewc_pro] back; the credential that /init keeps for its fork's refund *)
(*  must be [ewc_pro] itself.                                             *)
(* ===================================================================== *)
Lemma wr_owed_ambiguous :
  wr_pro [3%nat; 0%nat] [3%nat] 17%nat 25%nat
  /\ wr_blk [3%nat; 0%nat] [] 17%nat 20%nat.
Proof.
  split.
  - rewrite /wr_pro. split_and!.
    + intros q Hq. pose proof echo_line_length as HL. rewrite HL in Hq.
      assert (Hq0 : q = 0%nat) by lia. subst q. vm_compute. lia.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + right. vm_compute. reflexivity.
    + vm_compute. intro H. inversion H.
    + vm_compute. reflexivity.
  - rewrite /wr_blk. split_and!.
    + intros q Hq. pose proof echo_line_length as HL. rewrite HL in Hq.
      assert (Hq0 : q = 0%nat) by lia. subst q. vm_compute. lia.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
    + vm_compute. reflexivity.
Qed.

Section echo_links_pro.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  (* =================================================================== *)
  (*  THE ROUND-OPEN CREDENTIAL, EXACTLY: what /init's banner leaves,     *)
  (*  and what its two diagnostics start from.                            *)
  (* =================================================================== *)
  Definition ewc_pro (v : era_pins) (n : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_pban ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  Global Instance ewc_pro_timeless v n : Timeless (ewc_pro v n).
  Proof. rewrite /ewc_pro. apply _. Qed.

  Lemma ewc_pro_taint v n : T -∗ ewc_pro v n.
  Proof. iIntros "HT". rewrite /ewc_pro. by iRight. Qed.

  (* ...is one arm of what the shell is lent... *)
  Lemma ewc_owed_of_pro (v : era_pins) (n : nat) :
    ewc_pro v n -∗ ewc_owed T v n.
  Proof.
    rewrite /ewc_pro /ewc_owed.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE".
    iPureIntro. left. exact (proj1 Hw).
  Qed.

  (* ...and is EXACTLY what the eighteenth banner byte leaves
     ([EchoLinks.ewc_ban_done] is this followed by [ewc_owed_of_pro]). *)
  Lemma ewc_ban_done_pro (v : era_pins) (n : nat) :
    ewc_ban T v n (length u_banner) -∗ ewc_pro v n.
  Proof.
    rewrite /EchoLinks.ewc_ban /ewc_pro.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    assert (H18 : length u_banner = 18%nat) by (vm_compute; reflexivity).
    rewrite H18 in Hw. cbn [EchoLinks.wr_banp] in Hw. destruct Hw as (ps' & -> & Hw).
    iLeft. iExists (ps' ++ [3%nat]), cs, (P + length u_banner)%nat.
    iFrame "Htn Hps Hcs HE". iPureIntro.
    exact (wr_pban_of_ban ps' cs n P Hw).
  Qed.

  (* =================================================================== *)
  (*  THE DIAGNOSTIC'S BYTES THROUGH THE LINKS: the round's choice [a]    *)
  (*  filed with [i] of its bytes out.  [0] is the round-open credential  *)
  (*  itself (nothing filed yet); byte 0 goes through [echo_link_pro],    *)
  (*  which files [ps ++ [a]]; every later byte through [echo_link_w].     *)
  (* =================================================================== *)
  Definition ewc_pdg (v : era_pins) (n a i : nat) : iProp Σ :=
    ((∃ ps cs P : _, ⌜wr_pdiag ps cs n P a i⌝ ∗ turn v P ∗ ps_lb v ps
        ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.

  Definition ewc_pdiag (v : era_pins) (n a i : nat) : iProp Σ :=
    match i with
    | O => ewc_pro v n
    | S _ => ewc_pdg v n a i
    end.

  Global Instance ewc_pdg_timeless v n a i : Timeless (ewc_pdg v n a i).
  Proof. rewrite /ewc_pdg. apply _. Qed.
  Global Instance ewc_pdiag_timeless v n a i : Timeless (ewc_pdiag v n a i).
  Proof. rewrite /ewc_pdiag. destruct i; apply _. Qed.

  Lemma ewc_pdiag_taint v n a i : T -∗ ewc_pdiag v n a i.
  Proof.
    iIntros "HT". rewrite /ewc_pdiag. destruct i.
    - by iApply ewc_pro_taint.
    - rewrite /ewc_pdg. by iRight.
  Qed.

  (* the family's start IS the round-open credential (definitionally) *)
  Lemma ewc_pdiag_0 (v : era_pins) (n a : nat) :
    ewc_pro v n -∗ ewc_pdiag v n a 0%nat.
  Proof. by iIntros "$". Qed.

  (* ONE BYTE, at either link. *)
  Lemma echo_pdiag_step (k : nat) (v : era_pins) (n a i : nat) (b : bv 8)
      (Φ : iProp Σ) :
    pro_alts !!! a !! i = Some b ->
    era_pin γ k v -∗ echo_links T γ -∗ ewc_pdiag v n a i -∗
    (ewc_pdiag v n a (S i) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof.
    intros Hb. iIntros "#Hpin #Hlk Hc HΦ".
    iDestruct (echo_links_w with "Hlk") as "#Hw".
    iDestruct (echo_links_pro with "Hlk") as "#Hpro".
    iDestruct (echo_links_taint with "Hlk") as "#Ht".
    pose proof (pro_alts_lt_of_lookup a i b Hb) as Ha.
    destruct i as [| i].
    - (* byte 0: the round's choice byte, through the prologue link *)
      rewrite /ewc_pdiag /ewc_pro /ewc_pdg.
      iDestruct "Hc" as "[Hl | #HT]"; last first.
      { iApply ("Ht" $! k b Φ with "HT [HΦ]").
        iIntros "#HT'". iApply "HΦ". by iRight. }
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
      pose proof (wr_pdiag_1_of_pro ps cs n P a Hw) as Hw'.
      destruct Hw as ((Hpin & Hm & Hdv & Hr & Hnd & HP) & _).
      iApply ("Hpro" $! k v P n a b ps cs Φ
                with "[%] [%] [%] [%] [%] [%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { exact Hm. }
      { exact Hr. }
      { lia. }
      { exact Hpin. }
      { exact Hnd. }
      { exact HP. }
      { exact Ha. }
      { exact Hb. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists (ps ++ [a]), cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
    - (* bytes 1..: ordinary bytes of the alternative just filed *)
      rewrite /ewc_pdiag /ewc_pdg.
      iDestruct "Hc" as "[Hl | #HT]"; last first.
      { iApply ("Ht" $! k b Φ with "HT [HΦ]").
        iIntros "#HT'". iApply "HΦ". by iRight. }
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
      pose proof (wr_pdiag_byte ps cs n P a (S i) b Hw Hb) as Hby.
      pose proof (wr_pdiag_S ps cs n P a (S i) Hw) as Hw'.
      destruct Hw as (Hpin & Hm & Hdv & Hr & _).
      iApply ("Hw" $! k v P n b ps cs Φ
                with "[%] [%] [%] Hpin Htn Hps Hcs HE [HΦ]").
      { lia. }
      { exact Hpin. }
      { exact Hby. }
      iIntros "Hres". iApply "HΦ".
      iDestruct "Hres" as "[(Htn' & Hps' & Hcs' & HE') | #HT]"; last by iRight.
      iLeft. iExists ps, cs, (S P). iFrame "Htn' Hps' Hcs' HE'".
      by iPureIntro.
  Qed.

  (* THE END SHAPE OF ALTERNATIVE 1: the next sub-round's banner is owed
     at the SAME count, which is the credential /init's restart head pays
     its banner from ([UInitBanner.kinit_ban]).  Alternative 2 has no end
     shape: the round is terminal and the credential is dropped (affine). *)
  Lemma ewc_pdiag_done_1 (v : era_pins) (n : nat) :
    ewc_pdiag v n 1%nat (length (pro_alts !!! 1%nat)) -∗ ewc_ban T v n 0%nat.
  Proof.
    rewrite pro_alts_1_length /ewc_pdiag /ewc_pdg /EchoLinks.ewc_ban.
    iIntros "[Hl | #HT]"; last by iRight.
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    iLeft. iExists ps, cs, P. rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE".
    iPureIntro.
    exact (wr_pdiag_done_1 ps cs n P 21%nat (eq_sym pro_alts_1_length) Hw).
  Qed.

End echo_links_pro.
