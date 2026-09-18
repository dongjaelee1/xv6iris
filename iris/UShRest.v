(* ===================================================================== *)
(*  UShRest.v -- THE SHELL'S TAIL OBLIGATION, AT THE ECHO ERA'S OWN       *)
(*  FAMILIES (lane R3).                                                   *)
(*                                                                       *)
(*  [UkSh.ush_rest_l N γp T Wc Wb Pm R] is the obligation the command     *)
(*  loop hands the rest of main's body: “from 0x97a, with the line fact   *)
(*  and the loop's carried state, the body runs and re-enters the loop    *)
(*  head”.  [UkShFork.ushf_rest_of_body] is its ONE proof, and its        *)
(*  remaining premises are facts about THE ERA -- the paid child's walk,  *)
(*  a killed child's credential, sh's own fork panic, the timelessness    *)
(*  of the write credential.  Those are FALSE for an arbitrary family     *)
(*  (take [Wc := emp] and the child law asks /echo to write the line's    *)
(*  words out of nothing), so no [forall T Wc Wb Pm] statement can carry  *)
(*  them: the obligation has to be discharged where the era is known.     *)
(*  This file is that place, and [sh_rest_holds] is the one glue lemma.   *)
(*  It is what deletes [UInitSh.sh_pay_rest] and, with it, the last       *)
(*  shell-side hypothesis of the top theorem.                            *)
(*                                                                       *)
(*  It cannot live in [UkShFork.v] (no era there) nor in [UInitBoot.v]    *)
(*  without dragging [UShEchoPay]'s cone into the boot assembly's own     *)
(*  file, so it is a leaf of its own, just above [UShEchoPay.v].          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import UserPerm.
Require Import UkRun.
Require Import UserFd.
Require Import ElfUser.
Require Import SpecKexec.   (* [kexec_sz] *)
Require Import UShKernel.         (* [sh_kexec_sz] *)
Require Import UserPtTree.        (* [pgroundup] *)
Require Import UexecExecInst.
Require Import LineWords.  (* [last_ws] *)
Require Import EchoDisc.  (* [line_ok] -- the era's line guard *)
Require Import UkSh.
Require Import UkShLoop.          (* [ush_line_lexable] / [ushl_R] *)
Require Import UkShFork. (* [ushf_rest_of_body] *)
Require Import UkShEcho.          (* [ush_line_toks_holds] / [echo_toks] *)
Require Import EchoOut.           (* [era_pin] / [era_pins] *)
Require Import EchoLinks.         (* [echo_links] / [ewc_ban] *)
Require Import EchoLinksLine.     (* [ewc_lcred] and its two laws *)
Require Import UShEcho.           (* [sh_echo_slot] *)
Require Import LinkRec.           (* the era's link record *)
Require Import StageRec.          (* the cursor / stage record *)
Require Import UShLine.           (* [ush_mid] / [ush_mid_at] *)
Require Import UShPanic.          (* [ush_panic_law_holds] *)
Require Import UShEchoPay.        (* the paid child's two laws *)
Require Import UInitSh.           (* [sh_Rsh] *)

(* ===================================================================== *)
(*  0.  THE LINE THE DISCIPLINE ADMITS LEXES -- E4's closed computation    *)
(*      in the shape [UkShFork.ushf_rest_of_body] takes it.                *)
(*                                                                       *)
(*  [UkShEcho.ush_line_toks_holds] names the token list;                  *)
(*  [UkShLoop.ush_line_lexable] only asks that one exists and is short.   *)
(* ===================================================================== *)
Lemma ush_line_lexable_holds : UkShLoop.ush_line_lexable.
Proof.
  intros ws f k len Hl.
  destruct (UkShEcho.ush_line_toks_holds ws f k len Hl) as (_ & Hns & Htk).
  split; [ exact Hns | ].
  exists (UkShEcho.echo_toks ws).
  split; [ exact Htk | exact (UkShEcho.echo_toks_lt10 ws (proj1 Hl)) ].
Qed.

(* ===================================================================== *)
(*  0b. SH'S BREAK, AS [exec] LEAVES IT -- three closed side conditions.   *)
(*      [UShKernel.sh_kexec_sz] is the one computation; everything below   *)
(*      is arithmetic on the literal 0x5000.                              *)
(* ===================================================================== *)
Lemma sh_sz_lo : 8344 <= kexec_sz ElfUser.sh_elf.
Proof. rewrite UShKernel.sh_kexec_sz. lia. Qed.

Lemma sh_sz_al :
  UserPtTree.pgroundup (kexec_sz ElfUser.sh_elf) = kexec_sz ElfUser.sh_elf.
Proof. rewrite UShKernel.sh_kexec_sz. vm_compute. reflexivity. Qed.

Lemma sh_sz_ok : usz_ok (kexec_sz ElfUser.sh_elf + 65536).
Proof.
  rewrite UShKernel.sh_kexec_sz. unfold usz_ok.
  assert (E : UserPtTree.pgroundup (0x5000 + 65536) = 86016)
    by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.

Section UShRest.
  (* [UInitSh.v]'s binder list VERBATIM (durable-notes: a shorter list
     makes Coq synthesise an instance and the elaboration explodes), so
     that what this file proves is stated at the very instances
     [UInitBoot.echo_Hinit_boot] holds.  In particular NO
     [ghost_varG Σ (gset gname)] binder: the children set's camera is
     [Xv6G]'s own field ([Xv6Cameras.uchG]), and a second provider in the
     same scope is two instances whose propositions print identically. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ}.
  (* the era: its taint and its ghost names *)
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.

  (* THE FAMILIES, spelled as the era's own.  [Wc] is the TIGHT write
     credential at a line boundary, [Wb] the banner-owed one (this is
     [UInitBanner.kinit_ban T γ] unfolded -- kept at the literal so that
     [UShPanic.ush_panic_law_holds]'s statement matches without a rewrite,
     and the ONE rewrite is at the call site), [Pm] the console lease's
     pieces the loop carries in the payload's place. *)
  Local Notation Wc := (EchoLinksLine.ewc_lcred T γ (S gen_id)).
  Local Notation Wbn :=
    (fun I : list (bv 8) => ∃ v : era_pins,
       era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v I 0%nat)%I.

  (* =================================================================== *)
  (*  1.  THE GLUE                                                        *)
  (*                                                                      *)
  (*  What the top hands in: the era's links, the generic exec deposit,   *)
  (*  the ingredients of /echo's pinned entry, and ONE era pin.  What      *)
  (*  comes back is the whole obligation, at the record the kernel minted  *)
  (*  and the position ghost /init lent -- i.e. exactly the second         *)
  (*  conjunct of [UInitSh.sh_pay].                                        *)
  (*                                                                      *)
  (*  The three era laws are introduced as NAMED hypotheses by             *)
  (*  [iPoseProof] and never by [iIntros "#..."] on the bundle             *)
  (*  (durable-notes: the [Persistent] search walks the child law's wand   *)
  (*  chain and does not return).  Every deposit-bearing term is pinned    *)
  (*  at [uprogSG_free] on both sides.                                     *)
  (* =================================================================== *)
  Lemma sh_rest_holds (γp : gname) (N : uk_names Σ) :
    (⊢ app_taint -∗ T) ->
    ⊢ EchoLinks.echo_links T γ -∗
      (* PINNED at the FREE instance on both sides (durable-notes): the
         deposit's [uprogSG] is what [UShEchoPay]'s laws are stated at, and
         a bare [udep] here resolves to the ambient generic one. *)
      udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ v : era_pins, era_pin γ (S gen_id) v) -∗
      UkSh.ush_rest_l (PS := uprogSG_free) N γp T Wc Wbn
        (UShLine.ush_mid γ γp)
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
  Proof using HPT HTT.
    intros Hkt.
    (* the credential's conversion at a fork that failed: the block the
       line owed, read as a boundary credential *)
    assert (Hwbl : forall I : list (bv 8),
              ⊢ EchoLinksLine.ewc_lcred T γ (S gen_id) I 3%nat -∗
                EchoLinksLine.ewc_lcred T γ (S gen_id) I 0%nat)
      by (intro I; exact (EchoLinksLine.ewc_lcred_blk_line T γ (S gen_id) I)).
    iIntros "#Hlk #Hdep #Hslot #Hpin".
    iDestruct "Hpin" as (v) "#Hp".
    (* ---- the three era laws, as named hypotheses ---- *)
    iPoseProof (UShEchoPay.ushf_child_law_holds_at T γ Hkt
                  with "Hlk Hdep Hslot") as "#Hchl".
    iPoseProof (UShEchoPay.ushf_kill_law_holds T γ v Hkt with "Hp") as "#Hkl".
    iPoseProof (UShPanic.ush_panic_law_holds (PS := uprogSG_free) T γ
                  with "Hlk") as "#Hplaw".
    (* ---- the obligation's box: the record's own facts come OUT of it,
           so the discharger can be applied at [ukn_const N] ---- *)
    iIntros "!>" (l) "%Hc".
    iPoseProof (UkShFork.ushf_rest_of_body
                  (PS := uprogSG_free) (Hpay := Hc)
                  N γp T Wc Wbn (UShLine.ush_mid γ γp)
                  (fun k H => H) (kexec_sz ElfUser.sh_elf)
                  sh_sz_lo sh_sz_al sh_sz_ok Hwbl
                  with "Hkl Hchl Hplaw") as "Hb".
    rewrite /UkSh.ush_rest_l /UkSh.ush_rest_l_at.
    iDestruct ("Hb" $! l with "[%]") as "Hb'"; [ exact Hc | iExact "Hb'" ].
  Qed.

End UShRest.

(* ===================================================================== *)
(*  THE SAME GLUE OVER THE RECORD (lane LINK-GEN-3).                      *)
(*                                                                       *)
(*  [sh_rest_holds] above is echo's; this is the ONE statement a second   *)
(*  era instantiates.  The family is [UShRound]'s exactly --              *)
(*  [Wcf I p := Wcl I p ∗ Hold I] and [Wbf I := (∃ v, pin ∗ ban) ∗        *)
(*  Hold I] -- so the file application's [ush_rest_l] is ONE application  *)
(*  of it once [file_link_inst] / the file's [StageRec] exist.  It is NOT *)
(*  the whole of [UShRound.sh_round_holds_file]: the redirect child is a  *)
(*  law [UkShFork.ushf_rest_of_body] does not take.                       *)
(* ===================================================================== *)
Section UShRestGen.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ}.
  Context {L : LinkRec Σ} (St : StageRec L).

  Lemma sh_rest_holds_at (Hold : list (bv 8) -> iProp Σ)
      (γ : echo_gn) (γp : gname) (N : uk_names Σ) :
    (forall I0 : list (bv 8), Timeless (Hold I0)) ->
    (forall I0 : list (bv 8), ⊢ lk_T L -∗ Hold I0) ->
    (⊢ app_taint -∗ lk_T L) ->
    (* the era's own reading of its admissible lines ([StageRec.ck_lineok]:
       which inputs the cursor's block is the LINE's alternative at) *)
    (forall I0 : list (bv 8),
       line_ok (last_ws I0) -> ck_lineok (sk_cur St) I0) ->
    ⊢ lk_links L -∗
      udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot (lk_T L) -∗
      (* THE EXEC-FAILED DIAGNOSTIC'S LAW comes in (lane LINK-GEN-2):
         [UkShEcho.ush_execfail_law_wq] names [alt_execfail] at EVERY
         input and the file's [fexfb LCat] is not that, so this is a
         premise until that carrier takes the diagnostic as a parameter.
         [UShEchoPay.ush_execfail_law_wq_hold_at] discharges it at any era
         whose exec-failed bytes are constant. *)
      UkShEcho.ush_execfail_law_wq (PS := uprogSG_free)
        (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I -∗
      (∃ v : era_pins, lk_pin L (S gen_id) v) -∗
      UkSh.ush_rest_l (PS := uprogSG_free) N γp (lk_T L)
        (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I
        (fun I => (∃ v : era_pins, lk_pin L (S gen_id) v
                     ∗ lk_ban L (S gen_id) v I 0%nat) ∗ Hold I)%I
        (UShLine.ush_mid_at (lk_rres L) γ γp)
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
  Proof using St.
    intros HTl Hht Hkt Hlok.
    assert (Hwbl : forall I : list (bv 8),
              ⊢ (lk_lcred L (S gen_id) I 3%nat ∗ Hold I) -∗
                (lk_lcred L (S gen_id) I 0%nat ∗ Hold I)).
    { intro I. iIntros "[Hc $]".
      iApply (lk_lcred_blk_line L (S gen_id) I with "Hc"). }
    iIntros "#Hlk #Hdep #Hslot #Hxlw #Hpin".
    iDestruct "Hpin" as (v) "#Hp".
    iPoseProof (UShEchoPay.ushf_child_law_hold_at St Hold HTl Hht Hkt Hlok
                  with "Hlk Hdep Hslot Hxlw") as "#Hchl".
    iAssert (UkShFork.ushf_kill_law
               (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I) as "#Hkl".
    { rewrite /UkShFork.ushf_kill_law. iIntros "!>" (n) "#Hk".
      iAssert (lk_T L) as "#HT"; [ iApply Hkt; iExact "Hk" | ].
      iSplitL.
      - iApply (lk_lcred_taint L (S gen_id) n 0%nat v with "Hp HT").
      - iApply Hht. iExact "HT". }
    iPoseProof (UShPanic.ush_panic_law_hold_at (PS := uprogSG_free) L Hold
                  with "Hlk") as "#Hplaw".
    iIntros "!>" (l) "%Hc".
    iPoseProof (UkShFork.ushf_rest_of_body
                  (PS := uprogSG_free) (Hpay := Hc)
                  N γp (lk_T L)
                  (fun I p => lk_lcred L (S gen_id) I p ∗ Hold I)%I
                  (fun I => (∃ v0 : era_pins, lk_pin L (S gen_id) v0
                               ∗ lk_ban L (S gen_id) v0 I 0%nat) ∗ Hold I)%I
                  (UShLine.ush_mid_at (lk_rres L) γ γp)
                  (fun k H => H) (kexec_sz ElfUser.sh_elf)
                  sh_sz_lo sh_sz_al sh_sz_ok Hwbl
                  with "Hkl Hchl Hplaw") as "Hb".
    rewrite /UkSh.ush_rest_l /UkSh.ush_rest_l_at.
    iDestruct ("Hb" $! l with "[%]") as "Hb'"; [ exact Hc | iExact "Hb'" ].
  Qed.

End UShRestGen.
