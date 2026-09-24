(* ===================================================================== *)
(*  UInitPipe.v -- THE PIPELINE APPLICATION'S [al_programs]               *)
(*  (lane PIPE-CC): [UInitBoot.echo_Hinit_boot]'s twin at [AppPipe.       *)
(*  app_pipe], and the line that takes [UPipeBootAdequacy.               *)
(*  pipe_adequacy_pipeSigma] down to ONE premise about the machine.       *)
(*                                                                       *)
(*  WHAT IS HERE, in the order the assembly needs it:                     *)
(*                                                                       *)
(*   S1  the pipeline era's readings of its own credential families --    *)
(*       [ush_wc_inp] / [ush_wb_inp] at [PipeLinkInst]'s pair, and the    *)
(*       lend's conversion at the shell's entry.  [UShLine.               *)
(*       ush_wc_inp_lcred] / [ush_wb_inp_ban] are echo's twins; the       *)
(*       first is a fact about [PipeLinksLine]'s families and the other   *)
(*       two are [LinkRec] fields.                                        *)
(*   S2  [pipe_cons_in_of_Cns] and [pipe_cons_sup_of_sh_slot] --          *)
(*       [UInitBoot]'s two era-specific seam lemmas at the pipe claim and *)
(*       at [UInitSh]'s [_at] forms (an arbitrary input discipline and an *)
(*       arbitrary line constructor), because the pipeline era's are      *)
(*       [PipeDisc.disc_input_p] and [PipeUline.ush_line_pipe].           *)
(*   S3  [pipe_cc] -- the era's [UserConsole.cons_cred] -- and            *)
(*       [pipe_cc_holds], its ten laws.                                   *)
(*   S4  [pipe_Hinit_boot]: /init's exec bundle at the pipeline record,   *)
(*       modulo the ONE premise lane SH-PIPE-ROUND-4 owes                 *)
(*       ([UShPipeRound.sh_pipe_child_law]).                              *)
(*   S5  [pipe_prog_law_of_child] and the CLOSED COROLLARY.               *)
(*                                                                       *)
(*  THE ONE PREMISE, AND ITS SHAPE.  [UShPipeRound.sh_pipe_child_law] is  *)
(*  [UkShFork.ushf_child_law_at] at the pipe line's shape; after its       *)
(*  section closes it depends on the fixed part [g] and on the classes    *)
(*  alone -- no [γp], no [r], no record equation -- so what this file      *)
(*  takes is                                                              *)
(*                                                                       *)
(*     forall HR GEN HBs HFd HIr HPav HWc HF (c : pipe_gn),               *)
(*       ⊢ sh_pipe_child_law c                                            *)
(*                                                                       *)
(*  i.e. [pipe_prog_law]'s own binder list with [c] and nothing else.      *)
(*                                                                       *)
(*  WHY THE COROLLARY IS HERE AND NOT IN [UPipeBootAdequacy.v].           *)
(*  That file carries the ADEQUACY cone and deliberately not the program  *)
(*  tier (its header says why, and [UInitBoot.v]'s says what happens when  *)
(*  the two are mixed); it also DEFINES [pipe_prog_law], which this file   *)
(*  discharges, so the dependency cannot be turned round.  The restated    *)
(*  corollary therefore lives here, one [Require] below it, and            *)
(*  [iris/PipeAssumptions.v] audits THIS one -- a strictly larger cone     *)
(*  than the old target's, since it now walks the whole program tier as    *)
(*  well.                                                                 *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpUart.
Require Import CtxIdDefs.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import ChildTok.
Require Import UexecSlot.
Require Import UexecRet.
Require Import UexecSG.
Require Import PathElems.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import ConsoleInv.
Require Import SpecKexec.
Require Import FsAbsDefs.
Require Import FsAbsEra.
Require Import PinnedExec.
Require Import UexecExecInst.
Require Import UkRun.
Require Import UkInit.
Require Import UexecExecMint.
Require Import UkWriteClosed.
Require Import UInitKernel.
Require Import LineWords.
Require Import EchoLinks.
Require Import UInitDiag.
Require Import UInitBanner.
Require Import UInitCons.
Require Import UInitConsK.
Require Import UInitSh.
Require Import UShPanic.
Require Import UShEcho.
Require Import EchoLinksPro.
Require Import EchoLinksLine.
Require Import EchoLinksBan.
Require Import UShLine.
Require Import AppEcho.
Require Import EchoOut.
Require Import UserConsole.
Require Import UserFd.
Require Import LinkUserinit.
Require Import UkSh.
Require Import UShConsK.
Require Import KexecDefs.
Require Import PageGeom.
Require Import InitBoot.
Require Import ElfUser.
Require Import ElfLoadable.
Require Import FsInitPin.
Require Import FsInitPinBoot.
Require Import UInitBoot.          (* [init_deps_of_laws] / [init_boot_bundle_of_pinned] *)
(* ---- the pipeline era's own layers ---- *)
Require Import LinkRec.
Require Import ReadRec.
Require Import PipeDisc.
Require Import PipeOutPure.
Require Import PipeOut.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import PipeHooks.         (* S0 of [PipeLinksLine], moved *)
Require Import PipeLinkInst.
Require Import GenLinksLine.
Require Import PipeBoth.        (* [pwc_lpr2], the record's lk_lpr since SH-PIPE-ROUND-4 *)
Require Import PipeReadInst.
Require Import PipeUline.
Require Import AppPipeClaim.
Require Import AppPipeCons.
Require Import UInitConsPipe.
Require Import UShPipeRound.
Require Import PipeProto.          (* [pipeProtoG]: the protocol's ghosts *)
Require Import UShPipeLaw.         (* the child law's DISCHARGE (SH-PIPE-ROUND-14) *)
Require UkPipeIface.               (* [pifRegG]: the binder below needs it in scope *)
Require Import UkShPipeFork.   (* [pterm_wc] -- design SS4.3p's WIDENED era credential *)
Require Import UShPipeCatSlot.  (* [pipe_sh_cat_slot] -- the /cat pin, off
                                   the era equation (lane SH-PIPE-ROUND-6) *)
Require Import AppPipe.
Require FsImg.
Require InodeInv.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  S1/S2  THE ERA'S SEAM, at [UInitBoot]'s Section-1 binder list          *)
(*         VERBATIM (a shorter one makes Coq synthesise an instance and    *)
(*         the elaboration explodes -- that file's own note) plus the      *)
(*         pipeline class.                                                 *)
(* ===================================================================== *)

Section UInitPipeSeam.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  (* the pipeline application's own class (lane PIPE-2W-2) *)
  Context `{!pipeOutG Σ}.

  (* =================================================================== *)
  (*  S1  THE TWO READINGS OF THE FAMILIES' INPUT, at the pipe record     *)
  (*                                                                     *)
  (*  [UShLine]'s seam between /init's position-indexed payload and sh's  *)
  (*  input-indexed credential has to identify the two inputs, and a      *)
  (*  LENGTH alone does not ([EchoOut.inp_lb_agree]): what identifies     *)
  (*  them is that both are lower bounds of the same era's echoed list.   *)
  (*  So each family owes its input on its untainted arm.                 *)
  (*                                                                     *)
  (*  The banner-owed one is a [LinkRec] FIELD ([lk_ban_inp]).  The       *)
  (*  boundary one is not, and cannot be: [lk_lcred] is an existential    *)
  (*  over [lk_lpr], whose four indices are four different families, so   *)
  (*  the reading is a fact about the ERA's spelling of them.  At the     *)
  (*  pipeline era all six arms are ONE shape -- a witness triple, the    *)
  (*  turn, the two lower bounds and the input, or the taint -- so the    *)
  (*  six proofs are one tactic.                                         *)
  (* =================================================================== *)
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Local Notation T := (echo_taint γ).
  Local Notation PI := (pipe_link_inst_at g).

  (* THE SAME EIGHT LINES FOUR TIMES, and NOT an [Ltac]: the reconstruction
     names the witnesses the destructuring bound, and an [Ltac] body cannot
     mention an identifier a tactic inside it introduces at run time ("The
     reference ps was not found"). *)
  Local Lemma pwc_pro_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    pwc_pro g k v I -∗ pwc_pro g k v I ∗ (inp_lb v I ∨ T).
  Proof using .
    rewrite pwc_pro_view. iIntros "[Hl | #HT]"; last first.
    { iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Ht & #Hps & #Hcs & #HE)".
    iSplitL "Ht".
    - iLeft. iExists ps, cs, P. iFrame "Ht Hps Hcs HE". by iPureIntro.
    - iLeft. iExact "HE".
  Qed.

  Local Lemma pwc_blk_inp (k : nat) (v : era_pins) (I : list (bv 8))
      (a i : nat) :
    pwc_blk g k v I a i -∗ pwc_blk g k v I a i ∗ (inp_lb v I ∨ T).
  Proof using .
    rewrite pwc_blk_view. iIntros "[Hl | #HT]"; last first.
    { iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Ht & #Hps & #Hcs & #HE)".
    iSplitL "Ht".
    - iLeft. iExists ps, cs, P. iFrame "Ht Hps Hcs HE". by iPureIntro.
    - iLeft. iExact "HE".
  Qed.

  Local Lemma pwc_sp_t_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    pwc_sp_t g k v I -∗ pwc_sp_t g k v I ∗ (inp_lb v I ∨ T).
  Proof using .
    rewrite pwc_sp_t_view. iIntros "[Hl | #HT]"; last first.
    { iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Ht & #Hps & #Hcs & #HE)".
    iSplitL "Ht".
    - iLeft. iExists ps, cs, P. iFrame "Ht Hps Hcs HE". by iPureIntro.
    - iLeft. iExact "HE".
  Qed.

  Local Lemma pwc_open_t_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    pwc_open_t g k v I -∗ pwc_open_t g k v I ∗ (inp_lb v I ∨ T).
  Proof using .
    rewrite pwc_open_t_view. iIntros "[Hl | #HT]"; last first.
    { iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & Ht & #Hps & #Hcs & #HE)".
    iSplitL "Ht".
    - iLeft. iExists ps, cs, P. iFrame "Ht Hps Hcs HE". by iPureIntro.
    - iLeft. iExact "HE".
  Qed.

  Local Lemma pwc_line_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    pwc_line g k v I -∗ pwc_line g k v I ∗ (inp_lb v I ∨ T).
  Proof using .
    rewrite /pwc_line. iIntros "[Hp | Hq]".
    - iDestruct (pwc_pro_inp k v I with "Hp") as "[Hp Hi]".
      iSplitL "Hp"; [ by iLeft | iExact "Hi" ].
    - iDestruct "Hq" as (a) "[%Ha Hp]".
      rewrite /pwc_post.
      iDestruct (pwc_blk_inp k v I a (length (pab I a) - 2)%nat with "Hp")
        as "[Hp Hi]".
      iSplitL "Hp"; [ | iExact "Hi" ].
      iRight. iExists a. iSplitR; [ by iPureIntro | ]. iExact "Hp".
  Qed.

  (* ...AND THE TWO-WRITER BLOCK (lane SH-PIPE-ROUND-4's R1): the record's
     [lk_lpr] is [PipeBoth.pwc_lpr2], whose index 0 is the WIDENED boundary
     credential [pwc_line2] with the unfiled two-writer block as its third
     arm; that arm carries the input prefix too. *)
  Local Lemma pwc_blk2_inp (k : nat) (v : era_pins) (I R : list (bv 8))
      (sel : list bool) (c1 c2 : nat) (tm : bool) :
    PipeBoth.pwc_blk2 g k v I R sel c1 c2 tm -∗
    PipeBoth.pwc_blk2 g k v I R sel c1 c2 tm ∗ (inp_lb v I ∨ T).
  Proof using .
    rewrite /PipeBoth.pwc_blk2. iIntros "[Hl | #HT]"; last first.
    { iSplit; [ iRight; iExact "HT" | iRight; iExact "HT" ]. }
    iDestruct "Hl" as (ps cs P) "(%Hw & %Htl & Ht & #Hps & #Hcs & Hled & #HE)".
    iSplitL "Ht Hled".
    - iLeft. iExists ps, cs, P. iFrame "Ht Hps Hcs Hled HE". by iPureIntro.
    - iLeft. iExact "HE".
  Qed.

  Local Lemma pwc_line2_inp (k : nat) (v : era_pins) (I : list (bv 8)) :
    PipeBoth.pwc_line2 g k v I -∗
    PipeBoth.pwc_line2 g k v I ∗ (inp_lb v I ∨ T).
  Proof using .
    rewrite pwc_line2_view /pipe_X. iIntros "[Hp | [Hq | Hb]]".
    - iDestruct (pwc_pro_inp k v I with "Hp") as "[Hp Hi]".
      iSplitL "Hp"; [ by iLeft | iExact "Hi" ].
    - iDestruct "Hq" as (a) "[%Ha Hp]".
      rewrite /pwc_post.
      iDestruct (pwc_blk_inp k v I a (length (pab I a) - 2)%nat with "Hp")
        as "[Hp Hi]".
      iSplitL "Hp"; [ | iExact "Hi" ].
      iRight; iLeft. iExists a. iSplitR; [ by iPureIntro | ]. iExact "Hp".
    - iDestruct "Hb" as (R sel c1 c2 a) "(%Hc & %Hn & Hp)".
      iDestruct (pwc_blk2_inp k v I R sel c1 c2 false with "Hp") as "[Hp Hi]".
      iSplitL "Hp"; [ | iExact "Hi" ].
      iRight; iRight. iExists R, sel, c1, c2, a.
      iSplitR; [ by iPureIntro | ]. iSplitR; [ by iPureIntro | ]. iExact "Hp".
  Qed.

  Local Lemma pwc_lpr_inp (k : nat) (v : era_pins) (I : list (bv 8))
      (p : nat) :
    PipeBoth.pwc_lpr2 g k v I p -∗
    PipeBoth.pwc_lpr2 g k v I p ∗ (inp_lb v I ∨ T).
  Proof using .
    destruct p as [| [| [| p']]]; cbn [gwc_lpr].
    - exact (pwc_line2_inp k v I).
    - exact (pwc_sp_t_inp k v I).
    - exact (pwc_open_t_inp k v I).
    - exact (pwc_blk_inp k v I 0%nat 0%nat).
  Qed.

  (* [UShLine.ush_wc_inp_lcred]'s pipe twin *)
  Lemma pipe_wc_inp : UShLine.ush_wc_inp γ T (pipe_Wcl_at g).
  Proof using .
    intros I p. rewrite /pipe_Wcl_at (pipe_inst_lcred g (S gen_id) I p).
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hc]".
    iDestruct (pwc_lpr_inp (S gen_id) v I p with "Hc") as "[Hc Hi]".
    iSplitL "Hc"; [ iExists v; iFrame "Hpin Hc" | ].
    iDestruct "Hi" as "[HE | HT]";
      [ iLeft; iExists v; iFrame "Hpin HE" | iRight; iExact "HT" ].
  Qed.

  (* [UShLine.ush_wb_inp_ban]'s pipe twin, off the record's own field *)
  Lemma pipe_wb_inp : UShLine.ush_wb_inp γ T (pipe_Wbl_at g).
  Proof using .
    intros I. rewrite /pipe_Wbl_at.
    iIntros "H". iDestruct "H" as (v) "[#Hpin Hb]".
    iDestruct (lk_ban_inp PI (S gen_id) v I with "Hb") as "[Hb Hi]".
    iSplitL "Hb"; [ iExists v; iFrame "Hpin Hb" | ].
    iDestruct "Hi" as "[[#HE %Hr] | #HT]"; last first.
    { iRight. iExact "HT". }
    iLeft. iSplitR; [ | by iPureIntro ]. iExists v. iFrame "Hpin HE".
  Qed.

  (* THE LEND'S CONVERSION AT THE SHELL'S ENTRY (the tenth law): /init's
     round-open credential IS a boundary credential.  Generic in the
     record, unlike echo's [Hpw], because the pipeline era's prologue
     family is the record's [lk_pban] and not a spelled-out shape. *)
  Lemma pipe_wp_line (n : nat) :
    ⊢ UInitDiag.kinit_pro_at PI n -∗
      ∃ I : list (bv 8), ⌜length I = n⌝ ∗ pipe_Wcl_at g I 0%nat.
  Proof using .
    iIntros "H". rewrite /UInitDiag.kinit_pro_at.
    iDestruct "H" as (v I) "(%Hlen & #Hpin & Hc)".
    iExists I. iSplitR; [ by iPureIntro | ].
    rewrite /pipe_Wcl_at /lk_lcred. iExists v. iFrame "Hpin".
    rewrite (lk_lpr_0 PI (S gen_id) v I).
    iApply (lk_line_of_pro PI (S gen_id) v I).
    iApply (lk_pro_of_pban PI (S gen_id) v I with "Hc").
  Qed.

  (* the pieces' pin IS the record's, at this instance *)
  Lemma pipe_ep_refl (v : era_pins) :
    ⊢ era_pin γ (S gen_id) v -∗ lk_epin PI (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  Lemma pipe_pin_refl (v : era_pins) :
    ⊢ era_pin γ (S gen_id) v -∗ lk_pin PI (S gen_id) v.
  Proof using . by iIntros "$". Qed.

  (* ...AND THE READ LAW AT THE WIDENED CREDENTIAL (design SS4.3p): the
     era runs at [UkShPipeFork.pterm_wc g], whose terminal arm a delivered
     line REFUTES -- [pterm_wc_read_of] on the landed law and the pipeline
     era's own [pterm_read_law] ([UShPipeRound.pipe_pterm_read_law], off
     the mid-line pieces' reader residue). *)
  Lemma pipe_wc_read_t (γp : gname) :
    forall I l : list (bv 8), wl_nl ∉ l ->
      ⊢ UShLine.ush_mid_at (lk_rres PI) γ γp (I ++ l ++ [wl_nl])%list -∗
        UkShPipeFork.pterm_wc g I 2%nat ={⊤}=∗
        UShLine.ush_mid_at (lk_rres PI) γ γp (I ++ l ++ [wl_nl])%list
        ∗ UkShPipeFork.pterm_wc g (I ++ l ++ [wl_nl])%list 3%nat.
  Proof using .
    apply (UkShPipeFork.pterm_wc_read_of g
             (UShLine.ush_mid_at (lk_rres PI) γ γp)
             (UShPipeRound.pipe_pterm_read_law g γp)).
    intros I l Hnl. iIntros "Hm Hc". iModIntro.
    iApply (UShLine.ush_mid_wc_read_t_at PI γ γp (S gen_id) I l Hnl
              pipe_ep_refl with "Hm Hc").
  Qed.

  (* =================================================================== *)
  (*  S2  THE SEAM SH-OPEN CONSUMES, and the supply as a wand              *)
  (*      ([UInitBoot.ush_cons_in_of_Cns] / [init_cons_sup_of_sh_slot] at  *)
  (*      the pipe claim; the second at [UInitSh]'s [_at] forms).          *)
  (* =================================================================== *)
  Context (r : echo_names).

  Lemma pipe_cons_in_of_Cns :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    app_inv fsc_fs -∗ init_cons_cred T r -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N T)
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N T
               (cons_never r))
        ∗ cons_never r)
     ∨ T).
  Proof using .
    intros Heq. iIntros "#Hinv #Hc".
    rewrite /init_cons_cred.
    iDestruct "Hc" as "[#Hn | [[%i #Hm] | #HT]]".
    - iRight. iLeft. iSplitR; [ | iExact "Hn" ].
      iApply (sh_cons_absent_pipe γ r (cons_never r)
                ltac:(apply _) ltac:(apply _) Heq with "[] Hinv").
      rewrite /UShConsK.sh_cons_never_law. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (pipe_cons_never_law γ r).
    - iLeft. iApply (sh_cons_console_pipe γ r i Heq with "Hm Hinv").
    - iRight. iRight. iExact "HT".
  Qed.

  (* NAME EVERY [Persistent] THE INTRO BELOW RAISES, AT PRIORITY 0.
     [pipe_cons_sup_of_sh_slot]'s [iIntros "#Hdep #Hdp #Hplaw #Hcore"] is
     [UInitSh.init_exec_sup_of_sh_slot_at]'s own, character for
     character, and it WEDGES here (measured: [Set Default Timeout 300]
     fires on that one sentence) where it is structural there.  What
     differs is this file's Require set: the hint net now carries the
     whole pipeline tier, and [sh_prompt_law] / [sh_pay_at] /
     [init_sh_slot] are transparent definitions over VARIABLE predicates
     ([Dl], [Cr]) -- durable-notes' "fourth silent hang".  The four
     instances exist; the search does not reach them. *)
  #[local] Instance pipe_udep_pers0 :
    Persistent (udep (PS := uprogSG_free)) | 0 := udep_persistent.
  #[local] Instance pipe_prompt_law_pers0
      (Wc : list (bv 8) -> nat -> iProp Σ) :
    Persistent (UShKernel.sh_prompt_law (PS := uprogSG_free) Wc) | 0
    := UShKernel.sh_prompt_law_persistent Wc.
  #[local] Instance pipe_sh_pay_at_pers0 (Dl : FileDisc.uline -> Prop)
      (T0 : iProp Σ) (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    Persistent (UInitSh.sh_pay_at Dl T0 Cr Rsh n0) | 0
    := UInitSh.sh_pay_at_persistent Dl T0 Cr Rsh n0.
  #[local] Instance pipe_init_sh_slot_pers0 (T0 Pay : iProp Σ)
      `{!Persistent Pay} :
    Persistent (UInitSh.init_sh_slot T0 Pay) | 0
    := UInitSh.init_sh_slot_persistent T0 Pay.

  (* ...AND THE TWO THE ASSEMBLY BELOW RAISES, NAMED HERE AND NOT THERE.
     [UShEcho.sh_echo_slot] and [UkInit.init_cons_sup] need [riscvGS],
     [GenId] and the five slot classes to even ELABORATE, and the
     assembly's section binds none of them ([UInitBoot]'s [EchoInitBoot]
     takes [HR]/[GEN] as LEMMA binders) -- an [Instance] declared there
     wedges in its own STATEMENT, before any proof.  Declared here, the
     section discharge generalises them and the assembly instantiates
     them at its own [HR]/[GEN]. *)
  #[local] Instance pipe_sh_echo_slot_pers0 (T0 : iProp Σ) :
    Persistent (UShEcho.sh_echo_slot T0) | 0
    := UShEcho.sh_echo_slot_persistent T0.
  #[local] Instance pipe_init_cons_sup_pers0 (cn : cons_names)
      (T0 Cns : iProp Σ) (st : fdstate) (Cr : cons_cred Σ) :
    Persistent (UkInit.init_cons_sup cn T0 Cns st Cr) | 0
    := UkInit.init_cons_sup_persistent cn T0 Cns st Cr.
  (* ...AND THE SEAL, because a NAMED instance does not protect a
     TRANSPARENT obligation (durable-notes, LINK-GEN-6): without it the
     [Persistent] search unfolds [sh_pay_at] into [UkSh.ush_rest_l_at]'s
     wand tower before it ever reaches the instance above.  ONLY
     [sh_pay_at]: sealing [init_sh_slot] as well breaks the [iDestruct
     "Hcore" as "(#Hinv & _)"] below ("No matching clauses for match" --
     [IntoSep] cannot see through a seal either), and it is not needed,
     because the search unfolds [init_sh_slot]'s three [box]-conjuncts
     cheaply and lands on [Persistent Pay] with [Pay] sealed. *)
  #[local] Typeclasses Opaque UInitSh.sh_pay_at.

  Lemma pipe_cons_sup_of_sh_slot
      (Dsc : list (bv 8) -> Prop)
      (* [%list] IS NOT DECORATION: with this file's Require set the bare
         [++] parses in [string_scope] ("The term I has type bio_x while it
         is expected to have type string"), where [UInitSh.v]'s identical
         text parses in [list_scope]. *)
      (Hdncr : forall (I : list (bv 8)) (b : bv 8),
         Dsc (I ++ [b])%list -> bv_unsigned b <> 13%Z)
      (Hdshort : forall I : list (bv 8),
         Dsc I -> (S (length (rest_of I)) < EchoDisc.line_max)%nat)
      (Dl : FileDisc.uline -> Prop)
      (Hdline : forall (I : list (bv 8)) (f : nat -> bv 8),
         Dsc (I ++ [wl_nl])%list ->
         (forall j : nat, (j < length (rest_of I))%nat ->
            f j = rest_of I !!! j) ->
         f (length (rest_of I)) = wl_nl ->
         exists lu : FileDisc.uline,
           Dl lu
           /\ FileDisc.uline_ws lu = wl_words (rest_of I)
           /\ length (FileDisc.line_bytes lu) = S (length (rest_of I))
           /\ UkSh.ush_line_at lu f 0%nat (S (length (rest_of I))))
      (cn : cons_names) (st : fdstate)
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (UkSh.ush_Dbody + n0)))) <= 0xFE0 ->
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    UInitSh.cons_cred_holds_at cn T Dsc Hdncr Hdshort Dl Hdline Cr ->
    udep (PS := uprogSG_free) -∗
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) (cc_wc Cr) -∗
    UInitSh.init_sh_slot T (UInitSh.sh_pay_at Dl T Cr Rsh n0) -∗
    UkInit.init_cons_sup cn T (init_cons_cred T r) st Cr.
  Proof using .
    intros Heq Hpsok_free Hn0 Hst HCr.
    iIntros "#Hdep #Hdp #Hplaw #Hcore". rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> #Hcns".
      iDestruct "Hcore" as "#Hcore'".
      iApply (UInitSh.init_exec_sup_of_sh_slot_at Dsc Hdncr Hdshort Dl Hdline
                T cn st (cons_never r) Cr Rsh n0 Hpsok_free Hn0 Hst HCr
                with "Hdep Hdp Hplaw [] Hcore'").
      iApply (pipe_cons_in_of_Cns Heq with "[] Hcns").
      iDestruct "Hcore'" as "(#Hinv & _)". iExact "Hinv".
    - iIntros "!> #HT".
      iApply (init_cons_cred_of_taint T r with "HT").
  Qed.

End UInitPipeSeam.

(* ===================================================================== *)
(*  S3/S4/S5  THE CREDENTIAL, THE BUNDLE AND THE THEOREM                  *)
(*  ([UInitBoot]'s [Section EchoInitBoot] binder list, verbatim, plus the  *)
(*  pipeline class.)                                                      *)
(* ===================================================================== *)
Section PipeInitBoot.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{!pipeOutG Σ}.
  (* THE PROTOCOL'S GHOSTS (lane SH-PIPE-ROUND-14).  Nothing ABOVE this
     line uses them -- [sh_pipe_child_law_all]'s Prop does not mention
     [pipeProtoG], so its type does NOT move and neither
     [pipe_prog_law_of_child] nor [pipe_adequacy_pipeSigma_of_child] does
     -- but the DISCHARGE below allocates a [pnames] record
     ([UShPipeLaw.pl_round_alloc] through [PipeProto.pipe_names_alloc])
     and so needs the class.  See the lane's Findings: the functor list
     [UPipeBootAdequacy.pipeSigma] does NOT contain [pipeProtoSigma], so
     [pipeProtoG pipeSigma] has no instance and the discharge is stated at
     the extended list in [UInitPipeAdequacy.v]. *)
  Context `{!pipeProtoG Σ}.
  (* ...AND THE TREE-ROUTE ENTRIES' DEVICE REGISTRY (lane REPOINT-PIPE):
     the discharge's two children allocate one inside the exec slot
     ([UkPipeEntries.pe_cat_image_entry_qc_alloc] /
     [pe_echo_image_entry_alloc]).  Like [pipeProtoG], [sh_pipe_child_law_all]'s
     Prop does not mention it. *)
  Context `{HpifR : !UkPipeIface.pifRegG Σ}.

  (* NAME THE LEAF, DO NOT SEARCH ([UShPipeRound.v]'s measured note, and
     it is the one that bites here): [iIntros "#H"] / [iAssert ... as "#H"]
     on [PipeLinks.pipe_links g] -- six [box]-wands behind ONE transparent
     definition -- sends the [Persistent] search into the wand chain and
     in a file with this cone it does not come back.  The bundle HAS a
     [Global Instance]; the hint net does not reach it. *)
  #[local] Instance pipe_links_pers0 `{!riscvGS Σ} (g : pipe_gn) :
    Persistent (PipeLinks.pipe_links g) | 0
    := PipeLinks.pipe_links_persistent g.
  #[local] Instance pipe_T_pers0 (g : pipe_gn) :
    Persistent (echo_taint (pgn_cl g)) | 0
    := echo_taint_persistent (pgn_cl g).
  #[local] Instance pipe_T_tl0 (g : pipe_gn) :
    Timeless (echo_taint (pgn_cl g)) | 0
    := echo_taint_timeless (pgn_cl g).


  (* =================================================================== *)
  (*  S3  THE APPLICATION'S CONSOLE CREDENTIAL                            *)
  (*                                                                     *)
  (*  [UInitBoot.echo_cc]'s twin.  Every one of the five families is a    *)
  (*  READING OF THE RECORD and none is spelled out: the lend is the      *)
  (*  lease's read side at the record's residue, the mid-line pieces are  *)
  (*  the same at that residue, the loop's write credential and the       *)
  (*  banner-owed one are [PipeLinkInst]'s [UShRound]-facing pair, and    *)
  (*  the round-open one is [UInitDiag]'s generic prologue family.  That  *)
  (*  is what makes [pipe_cc_holds] below ten applications rather than    *)
  (*  ten proofs.                                                        *)
  (* =================================================================== *)
  Lemma pipe_cc_rd_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) :
    forall i : nat,
      Timeless (UShLine.ush_rd_pin_at (lk_rres (pipe_link_inst_at g))
                  (pgn_cl g) i).
  (* NAME THE LEAVES: a bare [apply _] at this altitude searches the
     tree's 455 [Timeless] instances ([UInitBoot.echo_cc_wb_timeless]'s
     measured note). *)
  Proof using .
    intro i. rewrite /UShLine.ush_rd_pin_at.
    apply bi.exist_timeless; intro v.
    apply bi.exist_timeless; intro I.
    apply bi.sep_timeless; [ apply bi.pure_timeless | ].
    apply bi.sep_timeless; [ apply era_pin_timeless | ].
    apply bi.sep_timeless; [ apply _ | ].
    apply bi.sep_timeless; [ apply inp_lb_timeless | ].
    apply (lk_rres_tl (pipe_link_inst_at g)).
  Qed.

  Lemma pipe_cc_wb_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) :
    forall I : list (bv 8), Timeless (pipe_Wbl_at g I).
  Proof using . intro I. apply pipe_Wbl_at_timeless. Qed.

  Definition pipe_cc (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) : cons_cred Σ :=
    MkConsCred
      (UShLine.ush_rd_pin_at (lk_rres (pipe_link_inst_at g)) (pgn_cl g))
      (pipe_cc_rd_timeless HR GEN g)
      (UShLine.ush_mid_at (lk_rres (pipe_link_inst_at g)) (pgn_cl g))
      (* THE ERA'S WRITE CREDENTIAL IS THE WIDENED ONE (design SS4.3p;
         lane SH-PIPE-ROUND-7).  The terminal round of a pipeline line --
         a [fork1] that failed inside runcmd -- comes back to sh in the
         child's exit payload and can only reach the prompt inside the
         LOOP'S OWN credential, because the fork arm's re-entry at 0x938
         has no continuation but [UkShLoop.ushl_head].  No arm of
         [lk_lcred] can carry it (PIPE-STAGE-3, PIPE-STAGE-5 SS3), so the
         credential the era runs at is [pterm_wc] and not [pipe_Wcl_at]:
         they agree at index 3 -- the only index the loop's BODY sees
         ([UkShPipeFork.pterm_wc_3]) -- and differ at 0, 1, 2, where the
         prompt is written. *)
      (UkShPipeFork.pterm_wc g)
      (pipe_Wbl_at g) (pipe_cc_wb_timeless HR GEN g)
      (UInitDiag.kinit_pro_at (pipe_link_inst_at g)).

  (* ...AND THE TEN LAWS.  [UInitBoot.echo_cc_holds]'s structure exactly,
     with the era's five discipline readings named: [PipeDisc.
     disc_input_p] and [PipeUline.ush_line_pipe] are the pipeline era's
     discipline and line constructor, and [UShPipeRound] carries the three
     proofs that bridge them. *)
  Lemma pipe_cc_holds (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) (r : echo_names) :
    @file_app Σ HF = MkAppcfg echo_names (pipe_pred (pgn_cl g)) r ->
    (⊢ PipeLinks.pipe_links g) ->
    UInitSh.cons_cred_holds_at fsc_cons (echo_taint (pgn_cl g))
      PipeDisc.disc_input_p UShPipeRound.ushq_disc_snoc_ncr
      PipeDisc.disc_input_p_rest_short
      PipeUline.ush_line_pipe UShPipeRound.ushq_disc_line_pipe
      (pipe_cc HR GEN g).
  Proof using .
    intros Heq Hlkp.
    (* THE TWO READINGS OF THE SUPPLY, at Coq level *)
    assert (Htsw : ⊢ echo_taint (pgn_cl g) -∗ app_sup).
    { rewrite /app_sup. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "#Ht". iApply (pipe_sup_of_taint (pgn_cl g) r with "Ht"). }
    assert (Hstw : ⊢ app_sup -∗ echo_taint (pgn_cl g)).
    { rewrite /app_sup. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "#Hs". iApply (pipe_taint_of_sup (pgn_cl g) r with "Hs"). }
    pose proof (pipe_wc_inp g) as Hwci.
    pose proof (pipe_wb_inp g) as Hwbi.
    rewrite /UInitSh.cons_cred_holds_at /pipe_cc /=.
    split_and!.
    (* (1) sh's read leaf, at the pipeline discipline *)
    - intros γp N l Hpeq.
      exact (UShLine.ush_read_recv_leaf_holds_at (pipe_read_inst g)
               (pgn_cl g) (pipe_Wbl_at g) N γp l Hpeq Hstw Htsw
               (pipe_pin_refl g) Hlkp).
    (* (2) the lease, off the position *)
    - intros γp N i Hpeq.
      exact (UShLine.ush_lease_of_at (lk_rres (pipe_link_inst_at g))
               (pgn_cl g) (echo_taint (pgn_cl g)) (pipe_Wbl_at g) N γp i
               Hpeq).
    (* (3) ...and back together under the taint *)
    - intros γp N I Hpeq.
      exact (UShLine.ush_at_of_mid_taint_at (lk_rres (pipe_link_inst_at g))
               (pgn_cl g) (echo_taint (pgn_cl g)) (pipe_Wbl_at g) N γp I
               Hpeq).
    (* (4) ...and with the banner-owed credential *)
    - intros γp N I Hpeq.
      exact (UShLine.ush_at_of_mid_wb_at (lk_rres (pipe_link_inst_at g))
               (pgn_cl g) (echo_taint (pgn_cl g)) (pipe_Wbl_at g) N γp I
               Hpeq Hwbi).
    (* (5) the write credential's step at the read, AT THE WIDENED
       CREDENTIAL (design SS4.3p): the terminal arm is refuted by the
       round's frozen resolution against the reader's own residue. *)
    - intros γp I l Hnl. exact (pipe_wc_read_t g γp I l Hnl).
    (* (6) the banner-owed credential is a boundary credential *)
    - intros I. exact (UkShPipeFork.pterm_wb_wc g I).
    (* (7) a block owed is one too *)
    - intros I. exact (UkShPipeFork.pterm_wc_blk_line g I).
    (* (8) a line read at an unwritten prompt is the taint *)
    - intros γp I l Hnl.
      exact (UShLine.ush_wb_read_holds_at (pipe_link_inst_at g) (pgn_cl g)
               γp (S gen_id) I l Hnl (pipe_ep_refl g)).
    (* (9) the cursor's boundary, at the widened credential: the reading
       [UShLine.ush_wc_inp] is the ONE of the ten that does not transfer
       for free, and [UkShPipeFork.pterm_wc_inp_of] pays it out of the
       [inp_lb] conjunct [pterm_shape] carries (design SS4.3p (a)). *)
    - intros γp N l i Hpeq.
      exact (UShLine.ush_posb_of_lend_at (lk_rres (pipe_link_inst_at g))
               (pgn_cl g) (echo_taint (pgn_cl g)) N γp
               (UkShPipeFork.pterm_wc g) (pipe_Wbl_at g) l i Hpeq
               (UkShPipeFork.pterm_wc_inp_of g Hwci) Hwbi).
    (* (10) the lend's conversion at the shell's entry *)
    - intros n. iIntros "H".
      iDestruct (pipe_wp_line g n with "H") as (I) "[%Hlen Hc]".
      iExists I. iSplitR; [ by iPureIntro | ].
      iApply (UkShPipeFork.pterm_wc_of g I 0%nat with "Hc").
  Qed.

  (* =================================================================== *)
  (*  S4  /init's EXEC BUNDLE AT THE PIPELINE RECORD                      *)
  (*                                                                     *)
  (*  [UInitBoot.echo_Hinit_boot], line for line, with four               *)
  (*  substitutions and NOTHING else: the claim's accessors are           *)
  (*  [AppPipeCons]'s, the console dance is [UInitConsPipe]'s, the        *)
  (*  credential is [pipe_cc] and the shell's TAIL is                     *)
  (*  [UShPipeRound.sh_round_holds_pipe] where echo's was                 *)
  (*  [UShRest.sh_rest_holds].  That last one is the ONE premise: it      *)
  (*  spends [sh_pipe_child_law].                                        *)
  (* =================================================================== *)
  Lemma pipe_Hinit_boot
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : pipe_gn) (r : echo_names) :
    (⊢ UShPipeRound.sh_pipe_child_law g) ->
    @file_app Σ HF = MkAppcfg echo_names (pipe_pred (pgn_cl g)) r ->
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = pipe_ifc g ->
    ⊢ app_inv fsc_fs -∗ pipe_boot (pgn_cl g) (S gen_id) r -∗
      pturn g (S gen_id) -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof using HU.
    intros Hchild Heq Hiface.
    (* the three projections, off the one equation *)
    assert (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = ptag g)
      by (rewrite /riscv_rx_tag Hiface; by cbn [pipe_ifc ai_tag pipe_tag]).
    assert (Hkill : @app_taint Σ (@riscv_fixedGS Σ HR)
                    = echo_taint (pgn_cl g))
      by (rewrite /app_taint Hiface; by cbn [pipe_ifc ai_kill pipe_kill]).
    assert (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = pecl g)
      by (rewrite /riscv_cons_res Hiface; by cbn [pipe_ifc ai_cons pipe_cons]).
    assert (Hktaint : ⊢ app_taint -∗ echo_taint (pgn_cl g)).
    { rewrite Hkill. iIntros "#H". iExact "H". }
    iIntros "#Hinv Hb Hturn". iModIntro.
    (* ---- THE ERA'S PIN, out of the turn and back ---- *)
    iAssert ((∃ v : era_pins, era_pin (pgn_cl g) (S gen_id) v)
             ∗ pturn g (S gen_id))%I
      with "[Hturn]" as "[#Hpine Hturn]".
    { rewrite /pturn /EchoOut.eturn.
      iDestruct "Hturn" as (v0) "(#Hp0 & Ht1 & Ht2 & Ht3 & Ht4 & Ht5)".
      iSplitR; [ iExists v0; iExact "Hp0" | ].
      iExists v0. iFrame "Hp0 Ht1 Ht2 Ht3 Ht4 Ht5". }
    (* ---- the taint's supply, and the generic slot it buys ---- *)
    iAssert (□ (echo_taint (pgn_cl g) -∗ app_sup))%I as "#Hsup".
    { rewrite /app_sup. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "!> #Ht". iApply (pipe_sup_of_taint (pgn_cl g) r with "Ht"). }
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iAssert (□ (∀ (R : iProp Σ) (W : uvis),
                  echo_taint (pgn_cl g) -∗
                  my_pay (uvis_gen W) (fun _ => R)%I -∗
                  □ (app_taint -∗ R) -∗ uslot W))%I as "#Hmint".
    { iIntros "!>" (R W) "#Ht Hp #HR".
      iDestruct ("Hsup" with "Ht") as "#Hs".
      iAssert (app_taint)%I as "#Hkc";
        [ rewrite Hkill; iExact "Ht" | ].
      iApply (uslot_mint_all with "Hs Hkc Hwp Hp HR"). }
    (* ---- the pins law, and /init's own row out of it ---- *)
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v
                  ∗ (⌜echo_fs_pure v⌝ ∨ echo_taint (pgn_cl g))))%I
      as "#Hfs".
    { rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "!>" (v) "Hp".
      iApply (pipe_echo_fs_pure_acc (pgn_cl g) r v with "Hp"). }
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v
                  ∗ (⌜era0_pins v⌝ ∨ echo_taint (pgn_cl g))))%I
      as "#Hcl".
    { iIntros "!>" (v) "Hp".
      iDestruct ("Hfs" $! v with "Hp") as "[Hp [%Hf | HT]]";
        [ iFrame "Hp"; iLeft; iPureIntro; exact (proj1 Hf)
        | iFrame "Hp"; iRight; iExact "HT" ]. }
    (* ---- /init's three deposits ---- *)
    iAssert (□ UkInit.init_deps (PS := uprogSG_free) (echo_taint (pgn_cl g)))%I
      as "#Hdp".
    { iApply (init_deps_of_laws (PSx := uprogSG_free) (echo_taint (pgn_cl g))
                with "[] [] [] []").
      - iModIntro. iIntros "#HT".
        iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
        + iApply ("Hsup" with "HT").
        + rewrite Hkill. iExact "HT".
      - rewrite /UkInit.kinit_wcl. iIntros "!>" (N0 b).
        iApply (UkWriteClosed.kinit_w1_of_closed_l0 (PS := uprogSG_free) N0 b).
      - iModIntro. iIntros "HT".
        iApply (udepw_law_of_sup (PSx := uprogSG_free) 15
                  (or_introl eq_refl)).
        iApply ("Hsup" with "HT").
      - iModIntro. iIntros "HT".
        iApply (udepw_law_of_sup (PSx := uprogSG_free) 17
                  (or_intror eq_refl)).
        iApply ("Hsup" with "HT"). }
    (* ...AND sh's OWN FREE WRITE LAW UNDER THE TAINT (design SS4.3z item
       3): [UkSh.sh_deps] IS [udepw_law 16], and the pipeline round's
       [panic("fork")] chain goes out on it when the lend carries no input
       bound.  It is the first bullet of [Hdp] above, read at sh's name --
       and it can only be built HERE, where the era equation and [r] are. *)
    iAssert (□ (echo_taint (pgn_cl g) -∗ UkSh.sh_deps (PS := uprogSG_free)))%I
      as "#Hshdp".
    { iModIntro. iIntros "#HT". rewrite /UkSh.sh_deps.
      iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
      - iApply ("Hsup" with "HT").
      - rewrite Hkill. iExact "HT". }
    (* ---- the tag's reading, at the PIPELINE discipline ---- *)
    iAssert (UkSh.ush_tag_law (echo_taint (pgn_cl g))) as "#Htg".
    { iApply (UkSh.ush_tag_law_of_at (echo_taint (pgn_cl g))
                PipeDisc.disc_p UShPipeRound.ushq_disc_no_ctrl_d).
      rewrite /UkSh.ush_tag_law_at. iIntros "!>" (h) "Hr".
      rewrite Htag /ptag.
      iDestruct "Hr" as "[_ Hr]". iExact "Hr". }
    (* THE LINKS, ONCE *)
    iAssert (PipeLinks.pipe_links g) as "#Hlks";
      [ iApply (PipeLinks.pipe_links_holds g Hcons) | ].
    assert (Hlkp : ⊢ PipeLinks.pipe_links g)
      by (iApply (PipeLinks.pipe_links_holds g Hcons)).
    (* ---- /echo's PINNED ENTRY ---- *)
    iAssert (UShEcho.sh_echo_slot (echo_taint (pgn_cl g))) as "#Hslot".
    { iApply UShEcho.sh_echo_slot_of_fs_pure_holds.
      rewrite /UShEcho.sh_echo_slot_of_fs_pure.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hfs" | iExact "Hmint" ]. }
    (* ---- /cat's PINNED ENTRY (lane PIPE-STAGE-5, design SS4.3n's fourth
           bullet).  The round's right child execs /cat, and the pin its
           (W) half needs has exactly one producer in the tree, at
           [FileFsPure.file_fs_pure] -- which is reachable only through
           the ERA EQUATION [Heq], and that lives here and nowhere below.
           Beside [Hslot], off the same [Hinv] and the same [Hmint]. ---- *)
    iAssert (UShCatPay.sh_cat_slot (echo_taint (pgn_cl g))) as "#Hcat".
    { iApply (UShPipeCatSlot.pipe_sh_cat_slot (pgn_cl g) r Heq
                with "Hinv Hmint"). }
    (* ---- the shell's slot: the state payload, the TAIL at the pipeline
           era's round, and the tag ---- *)
    (* LINEAR, NOT [#Hsh], and it is the lane's third wedge: an
       [iAssert ... as "#H"] raises [Persistent P] on its STATEMENT, and
       here that is [Persistent (sh_pay_at ush_line_pipe T (pipe_cc …)
       sh_Rsh 0)], whose search descends into [UkSh.ush_rest_l_at]'s wand
       tower and does not come back (measured, twice, with the named
       instance and the [Typeclasses Opaque] seal both in place).  The
       slot is SPENT ONCE -- by [pipe_cons_sup_of_sh_slot] below, which
       intros it persistently in ITS own file's context -- so nothing
       needs it duplicated here.  [with "[]"]: it is built from the
       intuitionistic context alone, so the round's [Hb]/[Hturn] stay. *)
    iAssert (UInitSh.init_sh_slot (echo_taint (pgn_cl g))
               (UInitSh.sh_pay_at PipeUline.ush_line_pipe
                  (echo_taint (pgn_cl g)) (pipe_cc HR GEN g)
                  UInitSh.sh_Rsh 0%nat))%I with "[]" as "Hsh".
    { rewrite /UInitSh.init_sh_slot /UInitSh.init_sh_slot_core.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hfs" | ].
      iSplitR; [ iExact "Hmint" | ].
      iApply (UInitSh.sh_pay_of_parts_at PipeUline.ush_line_pipe
                (echo_taint (pgn_cl g)) (pipe_cc HR GEN g)
                UInitSh.sh_Rsh 0%nat
                with "[] [] Htg");
        [ iApply UInitSh.sh_pay_state_holds | ].
      iIntros (γp N).
      iApply (UShPipeRound.sh_round_holds_pipe g r Hcons Hkill Heq γp N
                with "Hlks [] Hslot Hcat Hpine Hshdp []").
      - iApply (udep_free).
      - iApply Hchild. }
    (* ...AND THE PROMPT'S LAW AT EVERY LINE BOUNDARY, off the links *)
    (* ...AT THE WIDENED CREDENTIAL (design SS4.3p): the landed law on the
       left arm and the terminal round's two prompt bytes on the right
       ([UkShPipeFork.pterm_prompt_law], off PIPE-STAGE-3's steps). *)
    (* ...AT THE WIDENED CREDENTIAL (design SS4.3p).  The law is built one
       file down ([UShPipeRound.pipe_sh_prompt_law_t]), where the section
       carries ONE instance set beside the record equation; at THIS lemma,
       which takes [HR] and [GEN] explicitly, the wand's two sides are
       elaborated at different [uprogSG] instances and the proofmode's
       [IntoWand] does not come back (measured: 1h28m). *)
    iAssert (UShKernel.sh_prompt_law (PS := uprogSG_free)
               (UkShPipeFork.pterm_wc g))%I as "#Hplaw".
    { iApply (UShPipeRound.pipe_sh_prompt_law_t g Hcons with "Hlks"). }
    (* ---- the supply as a wand from the console credential ---- *)
    iAssert (UkInit.init_cons_sup fsc_cons (echo_taint (pgn_cl g))
               (init_cons_cred (echo_taint (pgn_cl g)) r) init_cons_fd
               (pipe_cc HR GEN g))%I as "#Hxs".
    { iApply (pipe_cons_sup_of_sh_slot g r
                PipeDisc.disc_input_p UShPipeRound.ushq_disc_snoc_ncr
                PipeDisc.disc_input_p_rest_short
                PipeUline.ush_line_pipe UShPipeRound.ushq_disc_line_pipe
                fsc_cons init_cons_fd (pipe_cc HR GEN g)
                UInitSh.sh_Rsh 0%nat Heq (fun k H => H)
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity)
                (pipe_cc_holds HR GEN g r Heq Hlkp)
                with "[] [] Hplaw Hsh").
      - iApply (udep_free).
      - iModIntro. iIntros "#HT".
        iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
        + iApply ("Hsup" with "HT").
        + rewrite Hkill. iExact "HT". }
    (* ---- THE CONSOLE DANCE, at whichever arm the VIEW decided ---- *)
    iAssert (UInitKernel.init_cons_dance_all (PS := uprogSG_free)
               (echo_taint (pgn_cl g))
               (init_cons_cred (echo_taint (pgn_cl g)) r)
               init_cons_fd)%I with "[Hb]" as "Hdn".
    { rewrite /pipe_boot /echo_boot. iDestruct "Hb" as "[HK | [%i #Hm]]".
      - iApply (UInitKernel.init_cons_dance_all_miss (PS := uprogSG_free)
                  (echo_taint (pgn_cl g))
                  (init_cons_cred (echo_taint (pgn_cl g)) r)
                  (cons_key r) init_cons_fd with "[] HK").
        iApply (init_cons_leaves_pipe (pgn_cl g) r Heq with "Hinv").
      - iApply (UInitKernel.init_cons_dance_all_hit (PS := uprogSG_free)
                  (echo_taint (pgn_cl g))
                  (init_cons_cred (echo_taint (pgn_cl g)) r)
                  init_cons_fd with "[] []").
        + iApply (init_cons_hit_pipe (pgn_cl g) r i Heq with "Hm Hinv").
        + iApply (init_cons_cred_made_pipe (pgn_cl g) r i with "Hm"). }
    (* ---- /init's own entry, as the bundle's constructor wand ---- *)
    iAssert (□ (∀ W' : uvis,
                  ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
                     (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  UInitKernel.init_boot_pay (PS := uprogSG_free)
                    (echo_taint (pgn_cl g))
                    (init_cons_cred (echo_taint (pgn_cl g)) r)
                    fsc_cons init_cons_fd
                    (pipe_cc HR GEN g)
                    -∗ uslot W'))%I as "#Hcon".
    { iApply (UInitKernel.init_boot_con (PS := uprogSG_free)
                (echo_taint (pgn_cl g))
                (init_cons_cred (echo_taint (pgn_cl g)) r) init_cons_fd
                (pipe_cc HR GEN g)
                fsc_cons
                1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0 0%nat
                init_cons_fd_ne
                (UkInit.init_kill_law_of_taint _ _ _ _ Hktaint)
                (init_boot_room 0%nat
                                   ltac:(vm_compute; discriminate))
                fdt0_length eq_refl (fdv_nopipe_closed _)
                (fun k H => H)
                with "[] [] Hxs").
      - iModIntro. iExact "Hdp".
      - iApply (udep_free). }
    iApply (init_boot_bundle_of_pinned (echo_taint (pgn_cl g))
              (UInitKernel.init_boot_pay (PS := uprogSG_free)
                 (echo_taint (pgn_cl g))
                 (init_cons_cred (echo_taint (pgn_cl g)) r) fsc_cons
                 init_cons_fd (pipe_cc HR GEN g))
              with "Hcl Hinv Hcon [] [Hdn Hturn]").
    - iIntros "!>" (W') "#Ht Hp".
      iApply ("Hmint" $! True%I W' with "Ht Hp []").
      iModIntro. iIntros "_". done.
    - iIntros "Hrd". rewrite /UInitKernel.init_boot_pay.
      (* THE READER'S RECEIPT RESIDUE AT COUNT ZERO, at the record's own
         residue ([PipeLinksLine.pwc_rres]) *)
      iAssert (∃ v0 : era_pins, era_pin (pgn_cl g) (S gen_id) v0
                 ∗ pwc_rres v0 [])%I
        with "[Hturn]" as "(%v0 & #Hpin0 & #Hres0)".
      { rewrite /pturn /EchoOut.eturn.
        iDestruct "Hturn" as (v0) "(#Hpin0 & Htn & _ & #Hcs0 & #Hps0 & _)".
        iExists v0. iFrame "Hpin0". rewrite /pwc_rres.
        iExists [], []. iEval (rewrite /EchoOut.turn) in "Htn".
        iDestruct (mono_nat_lb_own_get with "Htn") as "#Hlb0".
        assert (E0 : length (proc_before_p [] [] ([] : list (bv 8))) = 0%nat)
          by (rewrite proc_before_p_nil; reflexivity).
        rewrite E0. iFrame "Hlb0 Hps0 Hcs0". iPureIntro.
        exact PipeOut.rd_stage_p_0. }
      iDestruct (UInitBanner.kinit_ban0_of_eturn_at (pipe_link_inst_at g)
                   with "[Hturn]")
        as "[Hdl Hbn]";
        [ rewrite (pipe_inst_turn g) /pturn_pre; iExact "Hturn" | ].
      (* THE THREE LAWS, at the record *)
      iDestruct (UInitDiag.kinit_banner_law_pro_holds_at
                   (pipe_link_inst_at g) (PS := uprogSG_free)
                   with "Hlks") as "#Hblaw".
      iDestruct (UInitDiag.kinit_execfail_law_holds_at
                   (pipe_link_inst_at g) (PS := uprogSG_free)
                   with "Hlks") as "#Hxlaw".
      iDestruct (UInitDiag.kinit_forkfail_law_holds_at
                   (pipe_link_inst_at g) (PS := uprogSG_free)
                   with "Hlks") as "#Hflaw".
      iSplitL "Hdn"; [ iExact "Hdn" | ].
      iSplitL "Hrd"; [ rewrite ucons_reader_eq; iExact "Hrd" | ].
      iSplitL "Hdl".
      { rewrite /UInitBanner.kinit_dl0_at.
        iDestruct "Hdl" as (v) "(#Hpin & Hdl & #HE)".
        iDestruct (era_pin_agree with "Hpin0 Hpin") as %<-.
        rewrite /pipe_cc /=. rewrite /UShLine.ush_rd_pin_at.
        iExists v0, []. iSplitR;
          [ iPureIntro; split; [ reflexivity | exact rest_of_nil ] | ].
        iFrame "Hpin0 Hdl HE Hres0". }
      (* the banner-owed family and the record's [cc_wbn] are ONE family *)
      iAssert (□ (∀ n : nat,
                    UInitBanner.kinit_ban_at (pipe_link_inst_at g) n -∗
                    UserConsole.cc_wbn (pipe_cc HR GEN g) n))%I as "#Hbto".
      { iIntros "!>" (n) "Hb".
        rewrite /UInitBanner.kinit_ban_at /UserConsole.cc_wbn
                /pipe_cc /pipe_Wbl_at /=.
        iDestruct "Hb" as (v I) "(%Hlen & #Hpin & Hb)".
        iExists I. iSplitR; [ by iPureIntro | ]. iExists v. iFrame "Hpin Hb". }
      iAssert (□ (∀ n : nat, UserConsole.cc_wbn (pipe_cc HR GEN g) n -∗
                    UInitBanner.kinit_ban_at (pipe_link_inst_at g) n))%I
        as "#Hbfr".
      { iIntros "!>" (n) "Hb".
        rewrite /UInitBanner.kinit_ban_at /UserConsole.cc_wbn
                /pipe_cc /pipe_Wbl_at /=.
        iDestruct "Hb" as (I) "[%Hlen Hb]".
        iDestruct "Hb" as (v) "[#Hpin Hb]".
        iExists v, I. iSplitR; [ by iPureIntro | ]. iFrame "Hpin Hb". }
      iSplitL "Hbn"; [ iApply ("Hbto" with "Hbn") | ].
      iSplitR.
      { iIntros "!>" (n N') "Hb".
        iApply ("Hblaw" $! n N' with "[Hb]"). iApply ("Hbfr" with "Hb"). }
      rewrite /UkInitMain.kinit_diag_law.
      iSplitR; [ | iExact "Hflaw" ].
      iIntros "!>" (n N') "Hp".
      iPoseProof ("Hxlaw" $! n N' with "Hp") as "H".
      rewrite /UkInit.kinit_banner_pay.
      iIntros "Hl". iDestruct ("H" with "Hl") as (Ch) "(#Hst & H0 & Hfin)".
      iExists Ch. iFrame "Hst H0".
      iIntros "HC". iDestruct ("Hfin" with "HC") as "[$ Hrt]".
      iApply ("Hbto" with "Hrt").
  Qed.

  (* =================================================================== *)
  (*  S5  THE ONE PREMISE, NAMED ONCE                                     *)
  (*                                                                     *)
  (*  [UShPipeRound.sh_pipe_child_law]'s own binder list after its        *)
  (*  section closes -- the classes, the generation and the fixed part,   *)
  (*  and NOTHING else: no [γp], no [r], no record equation, no           *)
  (*  [CurCtx].  [UInitPipeAdequacy.pipe_prog_law_of_child] is what       *)
  (*  spends it.                                                          *)
  (* =================================================================== *)
  (* ...AND IT TAKES THE RECORD EQUATION (design SS4.3z item 1, lane
     SH-PIPE-ROUND-11 finding (8)).  Stated at an ARBITRARY [riscvGS Σ]
     the Prop is UNPROVABLE: every console step of the round is
     [PipeBoth.pblk2_cstep_L]/[_R], each of which takes
     [Hcons : riscv_cons_res (riscv_fixedGS HR) = pecl c], and that
     equation is [pipe_ifc]'s own field -- false at an arbitrary [HR].
     So the ONE hypothesis is the interface equation, which costs the
     consumer NOTHING: [pipe_prog_law_of_child] already receives
     [Hiface] from [pipe_prog_law]'s own binder list, and
     [pipe_Hinit_boot] already derives [Hcons]/[Htag]/[Hkill] from it.
     AND THE ERA'S RECORD EQUATION on [file_app] (lane REPOINT-PIPE): the
     two children now run the TREE-ROUTE entries, whose instance
     ([UkPipeIface.pipe_iface]) is stated at it; it costs the consumer
     nothing either -- [pipe_prog_law] binds [r] and the equation beside
     [Hiface], and [pipe_Hinit_boot] already takes both. *)
  Definition sh_pipe_child_law_all : Prop :=
    forall (HR : riscvGS Σ) (GEN : GenId)
           (HBs : bioslotG Σ) (HFd : fdslotG Σ) (HIr : irefslotG Σ)
           (HPav : pavG Σ) (HWc : wchG Σ) (HF : fileG Σ)
           (c : pipe_gn) (r : echo_names),
      @file_app Σ HF = MkAppcfg echo_names (pipe_pred (pgn_cl c)) r ->
      @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = pipe_ifc c ->
      ⊢ UShPipeRound.sh_pipe_child_law c.

  (* =================================================================== *)
  (*  S6  ...AND IT IS DISCHARGED (lane SH-PIPE-ROUND-14)                 *)
  (*                                                                     *)
  (*  [UShPipeLaw.pl_child_law] is the whole round: the protocol's names  *)
  (*  and the two-writer family's three cursors minted at the child law's *)
  (*  own [mWP] entry, the registrar, the four-way split, the two         *)
  (*  diagnostics and the three continuations.  All this lemma does is    *)
  (*  project the record equation into the two the round is stated at.    *)
  (* =================================================================== *)
  Theorem sh_pipe_child_law_all_holds : sh_pipe_child_law_all.
  Proof using HU HX pipeProtoG0 HpifR.
    intros HR GEN HBs HFd HIr HPav HWc HF c r Heq Hiface.
    assert (Hkill : @app_taint Σ (@riscv_fixedGS Σ HR)
                    = echo_taint (pgn_cl c))
      by (rewrite /app_taint Hiface; by cbn [pipe_ifc ai_kill pipe_kill]).
    assert (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = pecl c)
      by (rewrite /riscv_cons_res Hiface; by cbn [pipe_ifc ai_cons pipe_cons]).
    exact (UShPipeLaw.pl_child_law c Hcons Hkill r Heq).
  Qed.

End PipeInitBoot.

