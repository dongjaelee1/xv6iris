(* ===================================================================== *)
(*  EchoLinks.v -- THE CONSOLE LINKS AS ONE PERSISTENT LAW                *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM: DESIGN OF RECORD";        *)
(*   lane IO-LEAF, decision D1.)                                          *)
(*                                                                       *)
(*  [EchoOut]'s five links are stated under the boot record's four        *)
(*  equations ([riscv_out_res = eout] and its three siblings), which the  *)
(*  top theorem fixes and no PROGRAM file may name: the U tier sits below *)
(*  the record and knows nothing about which application it is running.   *)
(*  So the links travel to the programs the way the write DEPOSIT does    *)
(*  today ([UkSh.sh_deps], [UkInit.init_deps]) -- as ONE PERSISTENT       *)
(*  RESOURCE a program takes as a premise and spends per byte:            *)
(*                                                                       *)
(*    [echo_links T γ] -- the five links as closed [□] wands, mentioning  *)
(*      the era's ghosts ([era_pin], [turn], [ps_lb], [cs_lb], [E_lb],    *)
(*      [dl_cnt], [read_ret]) and the kernel's own console contracts      *)
(*      ([WpUart.out_link] / [read_link]) and NOTHING of the record;      *)
(*    [echo_links_holds] -- the entailment, proved where the equations    *)
(*      are in scope, i.e. exactly where [UInitBoot.echo_Hinit_boot]      *)
(*      already has them.                                                *)
(*                                                                       *)
(*  WHY A FILE OF ITS OWN and not a section of [EchoOut.v]: the law is a  *)
(*  PROGRAM-side interface and it changes with the programs, while        *)
(*  [EchoOut.v] is the claim.  A sibling file also keeps the two lanes    *)
(*  that touch them apart.                                               *)
(*                                                                       *)
(*  THE BUNDLE IS NOT CLOSED, and the five PROJECTIONS below are what     *)
(*  every consumer goes through, so a sixth link costs the consumers      *)
(*  nothing -- the fifth, [echo_link_pro] (PROLOGUE-ALTS-2's choice       *)
(*  byte), arrived exactly that way.                                     *)
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
Require Import EchoDisc.
Require Import ConsLog.
Require Import EchoOutPure.
Require Import RiscvPtsto.
Require Import WpUart.
Require Import TsoCtx.
Require Import EchoOut.
(* as in EchoDisc / EchoOutPure / EchoOut: the Sail imports leave
   string_scope on top and [++] would elaborate as String.append. *)
Local Open Scope list_scope.

Section echo_links.
  Context {Σ : gFunctors} `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{HRg : !riscvGS Σ}.

  (* ------------------------------------------------------------------ *)
  (*  THE LAW.  Each conjunct is [EchoOut]'s link with its Coq-level      *)
  (*  premises turned into [⌜⌝] wands, so that the whole thing is one     *)
  (*  [iProp] a program can hold; each is a CLOSED entailment under the   *)
  (*  equations, hence intuitionistic, hence persistent.                  *)
  (* ------------------------------------------------------------------ *)
  Definition echo_link_w : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P n0 : nat) (b : bv 8)
         (ps0 cs0 : list nat) (Φ : iProp Σ),
        ⌜((n0 `div` length echo_line) <= length cs0)%nat⌝ -∗
        ⌜pro_pin ps0 cs0 n0⌝ -∗
        ⌜proc_upto ps0 cs0 (S n0) !! P = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        E_lb v n0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v cs0 ∗ E_lb v n0) ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  Definition echo_link_blk : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P n0 a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (Φ : iProp Σ),
        ⌜(0 < n0)%nat⌝ -∗
        ⌜(n0 `mod` length echo_line)%nat = 0%nat⌝ -∗
        ⌜((n0 `div` length echo_line) <= S (length cs0))%nat⌝ -∗
        ⌜pro_pin ps0 cs0 n0⌝ -∗
        ⌜P = length (proc_upto ps0 cs0 n0)⌝ -∗
        ⌜(a < length line_alts)%nat⌝ -∗
        ⌜line_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        E_lb v n0 -∗
        (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ E_lb v n0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* (W'') THE WRITE LINK AT A PROLOGUE ROUND'S CHOICE BYTE, the
     block-first link's twin one level up: the writer that resolves the
     round's alternative (init after an exec failure or a fork failure,
     sh after its [fork1] panic) files the INDEX and the bound that comes
     back has grown by one -- in [ps], not in [cs]. *)
  Definition echo_link_pro : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P n0 a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (Φ : iProp Σ),
        ⌜(n0 `mod` length echo_line)%nat = 0%nat⌝ -∗
        ⌜n0 = 0%nat \/ cs0 !!! (n0 `div` length echo_line - 1)%nat = 3%nat⌝ -∗
        ⌜((n0 `div` length echo_line) <= length cs0)%nat⌝ -∗
        ⌜pro_pin ps0 cs0 n0⌝ -∗
        ⌜~ pro_done (pro_from (pro_idx cs0 (n0 `div` length echo_line)) ps0)⌝ -∗
        ⌜P = length (proc_upto ps0 cs0 (S n0))⌝ -∗
        ⌜(a < length pro_alts)%nat⌝ -∗
        ⌜pro_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        E_lb v n0 -∗
        (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ E_lb v n0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

  (* THE TAINT ROUTE, and it is not a convenience: every per-byte loop
     invariant of a program tower is [<the era's cursor> ∨ T], so the
     TAINT arm of byte [i] has to produce byte [i+1]'s link on its own. *)
  Definition echo_link_taint : iProp Σ :=
    (□ ∀ (k : nat) (b : bv 8) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ out_link Uart0 k b Φ)%I.

  Definition echo_link_rd : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (n : nat)
         (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        era_pin γ k v -∗ dl_cnt v (1/2) n -∗
        (read_ret T k v n ws -∗ Φ) -∗
        read_link k ws Φ)%I.

  Definition echo_links : iProp Σ :=
    (echo_link_w ∗ echo_link_blk ∗ echo_link_pro ∗ echo_link_taint
     ∗ echo_link_rd)%I.

  Global Instance echo_link_w_persistent : Persistent echo_link_w.
  Proof. rewrite /echo_link_w. apply _. Qed.
  Global Instance echo_link_blk_persistent : Persistent echo_link_blk.
  Proof. rewrite /echo_link_blk. apply _. Qed.
  Global Instance echo_link_pro_persistent : Persistent echo_link_pro.
  Proof. rewrite /echo_link_pro. apply _. Qed.
  Global Instance echo_link_taint_persistent : Persistent echo_link_taint.
  Proof. rewrite /echo_link_taint. apply _. Qed.
  Global Instance echo_link_rd_persistent : Persistent echo_link_rd.
  Proof. rewrite /echo_link_rd. apply _. Qed.
  Global Instance echo_links_persistent : Persistent echo_links.
  Proof. rewrite /echo_links. apply _. Qed.

  (* ---- the five projections, which is all a consumer ever uses ---- *)
  Lemma echo_links_w : echo_links -∗ echo_link_w.
  Proof. by iIntros "($ & _ & _ & _ & _)". Qed.
  Lemma echo_links_blk : echo_links -∗ echo_link_blk.
  Proof. by iIntros "(_ & $ & _ & _ & _)". Qed.
  Lemma echo_links_pro : echo_links -∗ echo_link_pro.
  Proof. by iIntros "(_ & _ & $ & _ & _)". Qed.
  Lemma echo_links_taint : echo_links -∗ echo_link_taint.
  Proof. by iIntros "(_ & _ & _ & $ & _)". Qed.
  Lemma echo_links_rd : echo_links -∗ echo_link_rd.
  Proof. by iIntros "(_ & _ & _ & _ & $)". Qed.

  (* ================================================================== *)
  (*  ...AND THE LAW HOLDS, under the record's four equations.  This is  *)
  (*  the one place in the arc where the application's claims and the    *)
  (*  kernel's console contracts are the same object, and it is exactly  *)
  (*  where [UInitBoot.echo_Hinit_boot] already stands.                  *)
  (* ================================================================== *)
  Section echo_links_holds.
    Context (Hout : @riscv_out_res Σ (@riscv_fixedGS Σ HRg) = eout T γ).
    Context (Hin : @riscv_in_res Σ (@riscv_fixedGS Σ HRg) = ein T γ).
    Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HRg) = etag T).
    Context (Hwin : @riscv_win_res Σ (@riscv_fixedGS Σ HRg) = ewin T γ).

    Lemma echo_links_holds : ⊢ echo_links.
    Proof.
      rewrite /echo_links /echo_link_w /echo_link_blk /echo_link_pro
              /echo_link_taint /echo_link_rd.
      iSplit; [| iSplit; [| iSplit; [| iSplit]]].
      - iIntros "!>" (k v P n0 b ps0 cs0 Φ) "%Hdiv %Hpin0 %Hb".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k v P n0 a b ps0 cs0 Φ).
        iIntros "%Hpos %Hmod %Hdiv %Hpin0 %HPeq %Halt %Hhead".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link_blk with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k v P n0 a b ps0 cs0 Φ).
        iIntros "%Hmod %Hpr %Hdiv %Hpin0 %Hnd %HPeq %Halt %Hhead".
        iIntros "Hpin Ht Hps Hcs HE HΦ".
        iApply (echo_write_link_pro with "Hpin Ht Hps Hcs HE HΦ");
          try assumption.
      - iIntros "!>" (k b Φ) "HT HΦ".
        iApply (echo_write_link_taint T γ with "HT HΦ"); try assumption.
      - iIntros "!>" (k v n ws Φ) "Hpin Hdl HΦ".
        iApply (echo_read_link with "Hpin Hdl HΦ"); try assumption.
    Qed.
  End echo_links_holds.

End echo_links.
