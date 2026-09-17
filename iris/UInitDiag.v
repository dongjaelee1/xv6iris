(* ===================================================================== *)
(*  UInitDiag.v -- WHAT PAYS FOR /init's TWO DIAGNOSTICS                  *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane INIT-DIAG, the      *)
(*   preparation for IO-LEAF M6b.  [UInitBanner] is the mould.)           *)
(*                                                                       *)
(*  <init> prints "init: exec sh failed\n" in the child whose exec of the *)
(*  shell failed (user/init.c:35) and "init: fork failed\n" when it       *)
(*  cannot fork (user/init.c:30), both with [printf] to fd 1 -- the       *)
(*  console, on the ledger the head's console arm is at                   *)
(*  ([UInitFd.ufd_l3], [ufd_l3_row1]).  Both are PROLOGUE ALTERNATIVES of *)
(*  the transcript ([EchoDisc.pro_alts !!! 1] and [!!! 2]) and both start *)
(*  from the credential the banner leaves behind: the round's prologue   *)
(*  open with the next byte its choice byte ([EchoLinksPro.ewc_pro]).     *)
(*                                                                       *)
(*  WHAT THIS FILE IS: the two per-byte obligations                       *)
(*  ([UkInit.kinit_w1] at fd 1, one byte of the alternative, on           *)
(*  [UInitBanner.kinit_w1_of_link]'s exact mould) and the two PAYMENTS in *)
(*  the shape /init's printf tower consumes ([UkInit.kinit_banner_pay]    *)
(*  is generic in the literal: “give me the descriptor table and I give  *)
(*  you a per-byte family for the [len] bytes [f]”, which is what          *)
(*  [UkInitPrintf.wp_kinit_printf_chain] takes), as PERSISTENT            *)
(*  conversions of the credential on [kinit_banner_law_holds]'s mould.    *)
(*  The exec diagnostic's payment ENDS at the next sub-round's banner     *)
(*  credential at the same count ([UInitBanner.kinit_ban n]), so the      *)
(*  restart head pays its banner from it with the law it already has;    *)
(*  the fork diagnostic's ends nowhere (the round is terminal).           *)
(*                                                                       *)
(*  WHAT IT IS NOT: nothing here is wired into /init's walk.  The two die *)
(*  arms ([UkInitMain.wp_kinit_main_die_de] / [_die_df]) print through    *)
(*  [UkInitPrintf.wp_kinit_printf], the free-law form at                  *)
(*  [Ch := fun _ => emp]; threading a credential to them is M6b proper.   *)
(*                                                                       *)
(*  ...AND THE CREDENTIAL THE BANNER LEAVES, EXACTLY ([kinit_pro]):       *)
(*  [UInitBanner.kinit_own] is stated at [EchoLinks.ewc_owed], the        *)
(*  disjunction [wr_pro ∨ wr_blk] the SHELL is lent, and the other arm is *)
(*  not refutable from anything /init holds ([EchoLinksPro.               *)
(*  wr_owed_ambiguous]).  What the fork's refund (FORK-REFUND's [Rc])     *)
(*  must hand back for the fork diagnostic to be payable is therefore     *)
(*  [kinit_pro], and the banner's law is restated to leave it            *)
(*  ([kinit_banner_law_pro_holds]); [kinit_own_of_pro] is the lend.       *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
(* the ghost binder list, each module IMPORTED and not merely required --
   see [UkWriteLeaf.v]'s header *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UexecSlot UexecSG.
Require Import UkRun UkRunSys.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.
Require Import UkWriteLeaf.        (* the supply and the post, at row 16 *)
Require Import UInitFd.            (* [ufd_l3] / [ufd_l3_row1] *)
Require Import UkInit UkInitLit UkInitMain.
Require Import EchoDisc.
Require Import EchoOut.
Require Import EchoLinks.
Require Import EchoLinksPro.       (* [ewc_pro] / [ewc_pdiag] / the steps *)
Require Import UInitBanner.        (* the mould: the halves, [kbn_fam],
                                      [kinit_ban] / [kinit_own] *)
Require Import CtxIdDefs.
Require User.InitSyms.
Local Open Scope Z_scope.
Import Defs.

Section UInitDiag.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  (* init's literals, by base ([UkInitMain]'s table) *)
  Local Notation LIT_START := 0x978.   (* "init: starting sh\n"     *)
  Local Notation LIT_FORK  := 0x990.   (* "init: fork failed\n"     *)
  Local Notation LIT_EXEC  := 0x9b0.   (* "init: exec sh failed\n"  *)

  (* =================================================================== *)
  (*  S1  THE PURE HALF: init's two rodata diagnostics ARE the era's      *)
  (*      alternatives 1 and 2                                            *)
  (* =================================================================== *)
  Lemma init_execfail_bytes_bool :
    forallb (fun j : nat =>
               match pro_alts !!! 1%nat !! j with
               | Some x => Z.eqb (bv_unsigned x)
                                 (bv_unsigned (init_lit LIT_EXEC j))
               | None => false
               end) (seq 0 21) = true.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma init_execfail_bytes (j : nat) :
    (j < 21)%nat -> pro_alts !!! 1%nat !! j = Some (init_lit LIT_EXEC j).
  Proof using .
    intros Hj. pose proof init_execfail_bytes_bool as H.
    rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    destruct (pro_alts !!! 1%nat !! j) as [x |] eqn:Hx; [| discriminate ].
    apply Z.eqb_eq in H. f_equal. by apply bv_eq.
  Qed.

  Lemma init_forkfail_bytes_bool :
    forallb (fun j : nat =>
               match pro_alts !!! 2%nat !! j with
               | Some x => Z.eqb (bv_unsigned x)
                                 (bv_unsigned (init_lit LIT_FORK j))
               | None => false
               end) (seq 0 18) = true.
  Proof using . vm_compute. reflexivity. Qed.

  Lemma init_forkfail_bytes (j : nat) :
    (j < 18)%nat -> pro_alts !!! 2%nat !! j = Some (init_lit LIT_FORK j).
  Proof using .
    intros Hj. pose proof init_forkfail_bytes_bool as H.
    rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    destruct (pro_alts !!! 2%nat !! j) as [x |] eqn:Hx; [| discriminate ].
    apply Z.eqb_eq in H. f_equal. by apply bv_eq.
  Qed.

  (* =================================================================== *)
  (*  S2  ONE BYTE OF A DIAGNOSTIC, THROUGH THE ERA'S LINKS               *)
  (* =================================================================== *)
  (* WHAT THE WALK WOULD CARRY: the round's choice [a] filed with [i] of
     its bytes out, or the taint -- [EchoLinksPro]'s family, as
     [UInitBanner.bnr] is [EchoLinks]'s. *)
  Definition pdg (v : era_pins) (I : list (bv 8)) (a i : nat) : iProp Σ :=
    EchoLinksPro.ewc_pdiag T v I a i.

  (* [UInitBanner.kinit_w1_of_link]'s exact mould, with the diagnostic's
     step in the banner's place. *)
  Lemma kinit_w1_of_link_pdiag (N : uk_names Σ) (v : era_pins)
      (I : list (bv 8))
      (l : list fdstate) (rb : bool) (a i : nat) (b : bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    pro_alts !!! a !! i = Some b ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    UkInit.kinit_w1 N (mword_of_int 1 : mword 64) b
      (UserFd.ustd (ukn_fd N) l ∗ pdg v I a i)
      (UserFd.ustd (ukn_fd N) l ∗ pdg v I a (S i)).
  Proof.
    intros Hli Hb.
    iIntros "#Hpin #Hlk" (h m avail) "%Ha0 %Ha2 #Hcode Hbuf [Hl Hbnd] Hrun Hcont".
    (* the two halves *)
    iDestruct (ubyte_split with "Hbuf") as "[Hb1 Hb2]".
    set (ua := m !!! Regidx a1_idx).
    (* the cursor family the deposit is stated at: the closure's half of
       the byte, and the era's cursor before and after this byte *)
    set (Q := (fun k : nat =>
                 ubyteq (ukn_d N) (DfracOwn (1/2)) (uint ua) b
                 ∗ match k with O => pdg v I a i | _ => pdg v I a (S i) end)%I).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = ua)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 1%nat)
      by (rewrite Ham2; vm_compute; reflexivity).
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 1)
      by (rewrite Ham0; vm_compute; reflexivity).
    iApply (UkInit.wp_kinit_write_chain N h m avail
              (kbn_fam N Q) l (DfracOwn (1/2)) 1%nat (fun _ => b)
              with "Hcode Hrun [Hb1 Hbnd] Hl [Hb2]").
    { (* THE DEPOSIT: the caller's own chain at its own cursor *)
      iApply (uwrite_chain_sup N Q
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int InitSyms.write : mword 64) 2)
                l 1%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hli).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   (DfracOwn (1/2)) ua 1%nat (fun _ => b)
                   with "Hheap [Hb1]") as %HM;
        [ iApply (ubytesq_of_one with "Hb1") | ].
      iFrame "Hheap".
      rewrite Ham1 Hcnt. cbn [cons_out_chain].
      iSplit.
      - (* the cursor, unmoved: what the SHORT arm would hand back *)
        rewrite /Q. iFrame "Hb1 Hbnd".
      - iIntros (b') "%Hb'".
        assert (Hbb : b' = b).
        { pose proof (HM 0%nat ltac:(lia)) as HM0.
          cbn in HM0. rewrite HM0 in Hb'. by injection Hb'. }
        subst b'.
        iApply (EchoLinksPro.echo_pdiag_step T γ (S gen_id) v I a i b (Q 1%nat)
                  Hb with "Hpin Hlk Hbnd [Hb1]").
        iIntros "Hres". rewrite /Q. iFrame "Hb1". rewrite /pdg. iExact "Hres". }
    { iApply (ubytesq_of_one with "Hb2"). }
    iIntros (h' ret W cw' cs') "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hl Hb2 Hpost Hrun".
    (* THE POST: the short arm is refuted from the run the caller owns *)
    iDestruct (uwrite_no_short Q (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 1%nat rb 1%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hli
                 ltac:(rewrite Hka2 Ha2; vm_compute; reflexivity)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    rewrite /Q. iDestruct "HQ" as "[Hb1 Hbnd]".
    iDestruct (ubytesq_to_one with "Hb2") as "Hb2".
    iDestruct (ubyte_join with "Hb1 Hb2") as "Hbuf".
    iApply ("Hcont" $! h' ret with "Hbuf [$Hl $Hbnd] Hrun").
  Qed.

  (* =================================================================== *)
  (*  S3  THE CREDENTIAL THE BANNER LEAVES, EXACTLY                       *)
  (* =================================================================== *)
  Local Notation stc_cons := (FdOpen true true (FdDevice CONSOLE)).

  (* the round's prologue open, the choice byte next, with the era's pin
     beside it: [UInitBanner.kinit_own] without the [wr_blk] arm *)
  Definition kinit_pro (n : nat) : iProp Σ :=
    (∃ (v : era_pins) (I : list (bv 8)),
       ⌜length I = n⌝ ∗ era_pin γ (S gen_id) v
       ∗ EchoLinksPro.ewc_pro T v I)%I.

  (* A bare [apply _] here cost 7.4 s of this file's 11 s: the search is on
     the (exists, sep) STRUCTURE, not on the leaves.  Naming the two
     structural instances first leaves the leaf search cheap (0.6 s). *)
  Global Instance kinit_pro_timeless n : Timeless (kinit_pro n).
  Proof.
    rewrite /kinit_pro.
    apply bi.exist_timeless => v.
    apply bi.exist_timeless => I.
    apply bi.sep_timeless; [ apply _ | ].
    apply bi.sep_timeless; apply _.
  Qed.

  (* ...is what /init lends the shell ([kinit_own] is the shape the
     shell's prompt law takes) ... *)
  Lemma kinit_own_of_pro (n : nat) :
    kinit_pro n -∗ UInitBanner.kinit_own T γ n.
  Proof.
    rewrite /kinit_pro /UInitBanner.kinit_own /UInitBanner.kinit_own_at.
    iIntros "H". iDestruct "H" as (v I) "(%Hl & #Hpin & Hc)".
    iExists v, I. iSplitR; [ by iPureIntro | ]. iFrame "Hpin".
    iApply (EchoLinksPro.ewc_owed_of_pro T v I with "Hc").
  Qed.

  (* ...and is what the banner's eighteenth byte leaves: the banner law
     restated to keep it ([UInitBanner.kinit_banner_law_holds] with the
     end shape not weakened).  Same proof, one lemma different. *)
  Lemma kinit_banner_law_pro_holds :
    echo_links T γ -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         UInitBanner.kinit_ban T γ n -∗
         UkInitMain.kinit_banner0 N stc_cons (kinit_pro n)).
  Proof.
    iIntros "#Hlk !>" (n N) "Hban".
    rewrite /UkInitMain.kinit_banner0 /UkInit.kinit_banner_pay.
    iIntros "Hl".
    rewrite /UInitBanner.kinit_ban /UInitBanner.kinit_ban_at.
    iDestruct "Hban" as (v I) "(%Hlen & #Hpin & Hbnr)".
    iExists (fun i => UserFd.ustd (ukn_fd N) (ufd_l3 stc_cons)
                      ∗ UInitBanner.bnr T γ v I i)%I.
    iSplitR "Hbnr Hl".
    { iIntros "!>" (j) "%Hj".
      iApply (UInitBanner.kinit_w1_of_link T γ N v I (ufd_l3 stc_cons) true j
                (init_lit LIT_START j)
                (ufd_l3_row1 stc_cons) (UInitBanner.init_banner_bytes j Hj)
                with "Hpin Hlk"). }
    iSplitL; [ rewrite /UInitBanner.bnr /UInitBanner.bnr_at; iFrame "Hl Hbnr" | ].
    iIntros "[$ Hbnd]". rewrite /kinit_pro. iExists v, I.
    iSplitR; [ by iPureIntro | ]. iFrame "Hpin".
    iApply (EchoLinksPro.ewc_ban_done_pro T v I with "[Hbnd]").
    rewrite /UInitBanner.bnr /UInitBanner.bnr_at.
    by replace (length u_banner) with 18%nat by (vm_compute; reflexivity).
  Qed.

  (* =================================================================== *)
  (*  S4  THE TWO PAYMENTS, AS PERSISTENT CONVERSIONS OF THE CREDENTIAL   *)
  (*                                                                     *)
  (*  [UkInit.kinit_banner_pay N stc len f Rt] is what the printf tower   *)
  (*  spends for ANY literal ([UkInitPrintf.wp_kinit_printf_chain] takes  *)
  (*  its [∃ Ch] apart), and [UkInitMain.kinit_banner0] is it at the      *)
  (*  banner.  These are it at the two diagnostics, paid from             *)
  (*  [kinit_pro n] on the console ledger, closed under the era's links   *)
  (*  and so [□]: whatever /init's walk will carry the credential as, the *)
  (*  conversion travels beside it the way [UkInitMain.kinit_ban_law]     *)
  (*  does for the banner.                                               *)
  (* =================================================================== *)

  (* "init: exec sh failed\n": 21 bytes at fd 1, alternative 1, and what
     is left is the NEXT sub-round's banner credential at the same count
     -- /init reaps this child and its restart head spends it on the
     banner law it already holds. *)
  Lemma kinit_execfail_law_holds :
    echo_links T γ -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         kinit_pro n -∗
         UkInit.kinit_banner_pay N stc_cons 21%nat (init_lit LIT_EXEC)
           (UInitBanner.kinit_ban T γ n)).
  Proof.
    iIntros "#Hlk !>" (n N) "Hpro".
    rewrite /UkInit.kinit_banner_pay. iIntros "Hl".
    rewrite /kinit_pro. iDestruct "Hpro" as (v I) "(%Hlen & #Hpin & Hc)".
    iExists (fun i => UserFd.ustd (ukn_fd N) (ufd_l3 stc_cons)
                      ∗ pdg v I 1%nat i)%I.
    iSplitR "Hc Hl".
    { iIntros "!>" (j) "%Hj".
      iApply (kinit_w1_of_link_pdiag N v I (ufd_l3 stc_cons) true 1%nat j
                (init_lit LIT_EXEC j)
                (ufd_l3_row1 stc_cons) (init_execfail_bytes j Hj)
                with "Hpin Hlk"). }
    iSplitL.
    { iFrame "Hl". rewrite /pdg.
      iApply (EchoLinksPro.ewc_pdiag_0 T v I 1%nat with "Hc"). }
    iIntros "[$ Hc]". rewrite /UInitBanner.kinit_ban /UInitBanner.kinit_ban_at. iExists v, I.
    iSplitR; [ by iPureIntro | ]. iFrame "Hpin".
    iApply (EchoLinksPro.ewc_pdiag_done_1 T v I with "[Hc]").
    rewrite /pdg.
    by replace (length (pro_alts !!! 1%nat)) with 21%nat
      by (vm_compute; reflexivity).
  Qed.

  (* "init: fork failed\n": 18 bytes at fd 1, alternative 2, the round
     terminal -- nothing follows on this wire, so nothing is left: the
     credential the last byte hands back is dropped (affine). *)
  Lemma kinit_forkfail_law_holds :
    echo_links T γ -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         kinit_pro n -∗
         UkInit.kinit_banner_pay N stc_cons 18%nat (init_lit LIT_FORK) emp).
  Proof.
    iIntros "#Hlk !>" (n N) "Hpro".
    rewrite /UkInit.kinit_banner_pay. iIntros "Hl".
    rewrite /kinit_pro. iDestruct "Hpro" as (v I) "(%Hlen & #Hpin & Hc)".
    iExists (fun i => UserFd.ustd (ukn_fd N) (ufd_l3 stc_cons)
                      ∗ pdg v I 2%nat i)%I.
    iSplitR "Hc Hl".
    { iIntros "!>" (j) "%Hj".
      iApply (kinit_w1_of_link_pdiag N v I (ufd_l3 stc_cons) true 2%nat j
                (init_lit LIT_FORK j)
                (ufd_l3_row1 stc_cons) (init_forkfail_bytes j Hj)
                with "Hpin Hlk"). }
    iSplitL.
    { iFrame "Hl". rewrite /pdg.
      iApply (EchoLinksPro.ewc_pdiag_0 T v I 2%nat with "Hc"). }
    by iIntros "[$ _]".
  Qed.

End UInitDiag.
