(* ===================================================================== *)
(*  UShRound.v -- SH'S ROUND AT THE FILE APPLICATION (lane SKELETON, K2). *)
(*                                                                       *)
(*  [UShRest.sh_rest_holds] is the shell's round at the ECHO era: the     *)
(*  command loop's body obligation ([UkSh.ush_rest_l]) discharged at that *)
(*  era's credential families.  This is its twin at the FILE era, where   *)
(*  the loop has THREE child shapes instead of one and carries the DEED   *)
(*  between rounds (design/app-file.md SS3, SS4.2, SS5.4).                  *)
(*                                                                       *)
(*  THIS FILE IS A SKELETON: every proof is [Admitted] and every fact the *)
(*  console tier, the kernel or a sibling lane still owes is a NAMED      *)
(*  SECTION HYPOTHESIS with its exact statement.                         *)
(*                                                                       *)
(*  ===== THE ONE RULING THIS FILE MAKES =============================== *)
(*                                                                       *)
(*  THE DEED RIDES INSIDE THE CREDENTIAL FAMILY, and therefore            *)
(*  [UkShFork.ushf_wq]'s TWIN needs no new definition in [UkShFork.v].    *)
(*  [UkSh]'s [Wc : list (bv 8) -> nat -> iProp] is ABSTRACT, so the file  *)
(*  era instantiates it at [Wcf I p := Wcl I p ∗ sh_hold I] -- the        *)
(*  console credential of lane LINK-GEN paired with the deed at the       *)
(*  model's state for the round whose input is [I].  Then                 *)
(*  [UkShFork.ushf_wq Wcf I] IS the block owed or the block written       *)
(*  together with the deed back, which is what the design asks for, and   *)
(*  [ushf_child_law], [ush_panic_law], [ush_rest_l] and                   *)
(*  [UkShEcho.sh_exec_sup_echo_wq] all typecheck at it unchanged.         *)
(*                                                                       *)
(*  WHY THE DEED MUST BE IN [Wc] AND NOT BESIDE IT: sh READS ITS DEED     *)
(*  BEFORE IT PRINTS (design SS5.3 ruling (b), CAT-ENTRY).  The prompt     *)
(*  byte is the round's BLOCK-FIRST byte whenever the child printed        *)
(*  nothing -- an [echo ... > f] round, or a [cat f] at an empty `f` --    *)
(*  so the alternative that byte files ([FileLinks.file_write_link_blk]'s  *)
(*  [a]) is decided by the deed's value.  A credential that could be spent *)
(*  without the deed in hand would therefore be spendable at the wrong     *)
(*  alternative.                                                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import ObsTrace.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserPerm.
Require Import UserCwd.
Require Import UserChildren.
Require Import UserConsole.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import ExecEntry.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.            (* THE INSTANCES *)
Require Import WpUart.
Require Import ConsLog.
Require Import LogEntryDefs.
Require Import FsCfg.
Require Import FsImg.
Require Import FsImgCheck.
Require Import AppCfg.
Require Import AppInv.
Require Import LineWords.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import FileDisc.
Require Import FileOutPure.
Require Import FileState.
Require Import AppEcho.
Require Import AppFile.
Require Import FileOut.
Require Import FileLinks.
Require Import FileOpen.                 (* [fdq], [file_open_pay] *)
Require Import UserOff.
Require Import ElfUser.
Require Import UserHeap.
Require Import UkSh.
Require Import UkShDiag.
Require Import UkShLoop.
Require Import UShLexRedir.  (* [ush_line_lexable_redir_holds] -- the
                                redirect line's lexability, PROVED *)
Require Import UkShMalloc.
Require Import UkShParse.
Require Import UCodeShP.
Require Import UCodeShK.
Require Import UkShRedir.
Require Import UkShRedirLine.
Require Import UkShRedirAns.
Require Import UkShRedirSeam.
Require Import UkShEcho.
Require Import UkShFork.
Require Import UkFileOpen.
Require Import LinkRec.                  (* the era's link record *)
Require Import FileLinkInst.             (* [file_link_inst] -- lane LINK-GEN-2 *)
Require Import UShLine.
Require Import UShEcho.
Require Import UShPanic.          (* the panic and exec-failed laws at a record *)
Require Import UShEchoPay.        (* the paid child's laws at a record *)
Require Import UShKernel.
Require Import UInitSh.
Require Import UCatOut.                  (* [cat_tie] -- the pure round tie *)
Require Import UCatKernel.
Require Import UEchoFile.                (* K1: echo's entry at `f` *)
Require Import CtxIdDefs.
Require Import FsAbs.
Local Open Scope Z_scope.
Import Defs.

Section UShRound.
  (* [UShRest.v]'s binder list VERBATIM (durable-notes: a shorter list
     makes Coq synthesise an instance and the elaboration explodes), plus
     the file claim's and the file stage's classes.  NO [uexecSG] and NO
     [uprogSG] SECTION VARIABLE. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.

  (* the era's record: [FileOut]'s gname pair, and the deed's names *)
  Context (g : file_gn) (r : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred (fgn_cl g)) r).

  (* ...AND THE ERA'S BOOT STATE (RULING H', 2026-09-18).  The round's
     hold is tied to the era's first state BY A SHARED INDEX and not by
     [FileOut.f0_lb]: that lower bound only exists after the era's first
     console byte ([FileLinks.file_write_link_first] is its only producer),
     so a hold that asked for it was uninhabitable at /init's first
     instruction, where [UInitKernel.init_boot_pay] asks for [cc_wbn Cr 0]
     -- i.e. for [Wbf []] -- and the taint is not available and must not be
     (ADEQUACY's ruling).  THE STATE IS AN ERA CONSTANT, so it is a section
     variable beside [gen_id]; /init instantiates it at the deed's own
     content ([AppFile.dst_content s_deed]), which is what makes
     [UCatOut.cat_tie [] s0 [] s] hold by [eq_refl] at the head. *)
  Context (s0 : fst).

  (* the record equations the top theorem hands over
     ([UInitBoot.echo_Hinit_boot]'s [Hcons] / [Htag] one application on) *)
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = fecl g).
  Context (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ _) = ftag g).
  (* ...AND THE THIRD PROJECTION, beside the two (the program stream).
     [UInitBoot] derives all three from ONE interface equation
     ([Hiface]); the round took two of them as equations and the third as
     a hypothesis, which is the same fact twice. *)
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ _) = file_taint (fgn_cl g)).

  Local Notation T := (file_taint (fgn_cl g)).
  (* the era's LINK RECORD (lane LINK-GEN-2): every family this file's
     hypotheses are stated at is one of its fields. *)
  Local Notation FI := (FileLinkInst.file_link_inst g).

  (* =================================================================== *)
  (*  S1  THE FAMILIES                                                    *)
  (*                                                                     *)
  (*  [Wcl] / [Wbl] are lane LINK-GEN's: [EchoLinksLine.ewc_lcred] and    *)
  (*  [EchoLinks.ewc_ban] INSTANTIATED at [FileLinks] rather than twinned *)
  (*  (review SSD3).  They are PARAMETERS here, with exactly the five      *)
  (*  conversions the loop spends stated as hypotheses below -- which is  *)
  (*  where LINK-GEN's instance plugs in.  [Pm] is NOT a parameter:       *)
  (*  [UShLine.ush_mid_at] mentions only [EchoOut]'s era pins and the        *)
  (*  console lease, so the file era takes it verbatim at [fgn_echo g].   *)
  (* =================================================================== *)
  (* sh's own half of the console position pair ([UkSh]'s [γp]) *)
  Context (γp : gname).
  (* ...AND THEY ARE THE FILE INSTANCE NOW (the program stream), not
     parameters: [FileLinkInst.file_Wcl] / [file_Wbl] are lane LINK-GEN-2's
     record at this era, so the five conversions below are its five lemmas
     and not hypotheses. *)
  Local Notation Wcl := (FileLinkInst.file_Wcl g).
  Local Notation Wbl := (FileLinkInst.file_Wbl g).

  (* THE DEED, AT SH'S ROUND -- design SS4.2, "the deed meets the stage in
     sh's proof, PURELY".  The pure tie is [UCatOut.cat_tie]'s: the deed's
     content IS the model's state before the round whose input is [I]
     ([fst_upto cs0 s0 (bodies_of I) (nlines I - 1)]), with [cs0] and [s0]
     pinned by the era's own lower bounds so that the tie is about THIS
     era and not some other. *)
  (*  AT RULING H' THE INDEX IS THE SECTION'S and the era's filed boot
      state is NOT named here.  What used to stand in this arm --
      [file_era_pin g (S gen_id) vf ∗ f0_lb vf s0] -- said "the state the
      tie is about is the one the era filed", and it said it with a
      resource that does not exist before the era's first console byte.
      The index does the same work for free: the CREDENTIAL's own families
      ([FileLinksLine.fcur]'s [f0w]) carry the filed state under an
      existential, [FileLinksLine.f0w_agree] identifies any two of them,
      and the round's [s0] is what both are read at.  The named layer that
      makes the identification structural rather than an agreement step is
      [file_link_inst_at s0] at [FileLinksLine]'s [fwc_*_at s0] families
      ([file_link_inst] its [∃ s0] packing), and it is LINK-GEN's: until it
      lands, [FI] below is the packed record and the tie is by
      [f0w_agree]. *)
  Definition sh_hold_at (sb : fst) (I : list (bv 8)) : iProp Σ :=
    ((∃ (cs0 : list nat) (s : dst) (v : era_pins),
        fown r s
        ∗ ⌜UCatOut.cat_tie cs0 sb I s⌝
        ∗ f_typed (fgn_cl g) s
        ∗ era_pin (fgn_echo g) (S gen_id) v ∗ cs_lb v cs0)
     ∨ T)%I.

  Local Notation sh_hold := (sh_hold_at s0).

  Definition Wcf (I : list (bv 8)) (p : nat) : iProp Σ :=
    (Wcl I p ∗ sh_hold I)%I.
  Definition Wbf (I : list (bv 8)) : iProp Σ :=
    (Wbl I ∗ sh_hold I)%I.

  Global Instance Wcf_timeless I p : Timeless (Wcf I p).
  Proof using . rewrite /Wcf /sh_hold_at /T /file_taint /echo_taint. apply _. Qed.

  (* ...AND IT IS INHABITED AT THE ERA'S HEAD, which is the whole of
     RULING H': at [I = []] the tie is [dst_content s = s0] (because
     [UCatOut.cat_st cs0 s0 [] = s0]), so /init hands over its own deed at
     its own boot value and owes no lower bound.  [UInitFileCons.
     file_hold_head] is this arm's content minus the era pin, which /init
     holds at that instant ([UInitFileCons.file_turn_pre_of_boot]). *)

  (* =================================================================== *)
  (*  S2  LANE LINK-GEN'S OBLIGATIONS, at the ECHO shapes                 *)
  (*                                                                     *)
  (*  Each is an [EchoLinksLine]/[EchoLinks] lemma with [echo_links]      *)
  (*  replaced by [FileLinks]' bundle; they are exactly the conversions   *)
  (*  [UShRest.sh_rest_holds] and [UShKernel.sh_image_entry_at] spend.    *)
  (* =================================================================== *)

  (* [EchoLinksLine.ewc_lcred_blk_line], at the record *)
  Definition Hwbl : forall I : list (bv 8), ⊢ Wcl I 3%nat -∗ Wcl I 0%nat :=
    FileLinkInst.file_Hwbl g.
  (* [UInitBoot]'s [Hsh_wbwc]: the banner-owed credential is a boundary one *)
  Definition Hwbwc : forall I : list (bv 8), ⊢ Wbl I -∗ Wcl I 0%nat :=
    FileLinkInst.file_Hwbwc g.
  (* [LinkRec.lk_lcred_taint]: the taint inhabits every credential -- AT A
     PIN (lane LINK-GEN's section 6, sharpened by LINK-GEN-2).  [Wcl I p]
     carries the era's pin under an existential and the pin is a linear
     [ghost_map] element persisted, which the taint does not produce; the
     ECHO-SIDE pin is the one the record's [lk_pin FI] IS
     ([FileLinkInst]: [lk_pin := era_pin (fgn_echo g)]), so ONE pin is
     enough and every spender ([sh_kill_law_file]) holds it. *)
  Definition Hcltaint : forall (I : list (bv 8)) (p : nat) (v : era_pins),
      ⊢ era_pin (fgn_echo g) (S gen_id) v -∗ T -∗ Wcl I p :=
    FileLinkInst.file_Hcltaint g.
  (* [UkSh]'s [Hwc]: the read that completed a line moves the credential
     from "2" at the old input to "3" at the new one.  The record's own
     lemma is stated at the PIN and the input's lower bound, and the loop's
     [ush_mid_at] carries both -- persistently -- so the bridge is one
     destructuring and no resource moves. *)
  Lemma Hwc : forall I l : list (bv 8), wl_nl ∉ l ->
    ⊢ UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl]) -∗ Wcl I 2%nat -∗
      UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl])
      ∗ Wcl (I ++ l ++ [wl_nl]) 3%nat.
  Proof using .
    intros I l Hl. iIntros "Hmid Hc".
    rewrite /UShLine.ush_mid_at.
    iDestruct "Hmid" as "(Hp & Hpa & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #Hinp & Hres)".
    iSplitR "Hc".
    - iFrame "Hp Hpa Hrd". iExists v. iFrame "Hpin Hdl Hinp Hres".
    - iApply (FileLinkInst.file_Hwc g I l v Hl with "Hpin Hinp Hc").
  Qed.

  (* [UShLine.ush_wb_read_holds]: a read at a banner-owed credential taints *)
  Lemma Hwbr : forall I l : list (bv 8), wl_nl ∉ l ->
    ⊢ UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl]) -∗ Wbl I -∗
      UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp
        (I ++ l ++ [wl_nl]) ∗ T.
  Proof using .
    intros I l Hl. iIntros "Hmid Hb".
    rewrite /UShLine.ush_mid_at.
    iDestruct "Hmid" as "(Hp & Hpa & Hrd & Hv)".
    iDestruct "Hv" as (v) "(#Hpin & Hdl & #Hinp & #Hres)".
    iSplitR "Hb".
    - iFrame "Hp Hpa Hrd". iExists v. iFrame "Hpin Hdl Hinp Hres".
    - iApply (FileLinkInst.file_Hwbr g I l v Hl with "Hpin Hres Hb").
  Qed.
  (* the era's kill credential IS the file taint -- the equation above,
     read as an entailment *)
  Lemma Hktaint : ⊢ app_taint -∗ T.
  Proof using Hkill. rewrite Hkill. iIntros "$". Qed.

  (* =================================================================== *)
  (*  S3  THE PROMPT LINK, AT THE DEED (design SS4.2; CAT-ENTRY ruling (b)) *)
  (*                                                                     *)
  (*  sh's prompt byte is the round's BLOCK-FIRST byte exactly when the    *)
  (*  child printed nothing, and then it FILES the round's alternative:    *)
  (*  [RFRan sel] after an [echo ... > f] child (with [sel] read off the   *)
  (*  child's exit payload, i.e. off the deed's own content), [RCRan]      *)
  (*  after a [cat f] whose deed is empty.  Otherwise the child opened     *)
  (*  the block and the prompt is an ordinary byte.                       *)
  (*                                                                     *)
  (*  WHAT THIS LEMMA IS: the instantiation of                            *)
  (*  [FileLinks.file_write_link_blk] whose [a] is computed from the deed. *)
  (*  It is stated here because it is the ONE place where the claim and    *)
  (*  the stage meet, and they meet PURELY.                                *)
  (* =================================================================== *)
  Lemma sh_prompt_alt_of_deed (k : nat) (v : era_pins) (vf : file_era)
      (P a : nat) (b : bv 8) (ps0 cs0 : list nat)
      (I0 : list (bv 8)) (s : dst) (Φ : iProp Σ) :
    I0 <> [] ->
    rest_of I0 = [] ->
    (nlines I0 <= S (length cs0))%nat ->
    pro_pin_f ps0 cs0 I0 ->
    P = length (proc_before_f ps0 cs0 (Some s0) I0) ->
    (* THE DEED DECIDES THE ALTERNATIVE: the round's state is the deed's
       own content, so [ralt_ok] and the block's first byte are facts
       about [s] and the line, and about nothing else. *)
    UCatOut.cat_tie cs0 s0 I0 s ->
    ralt_ok (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a) ->
    cont (dst_content s)
         (uline_of (bodies_of I0 !!! (nlines I0 - 1)%nat)) (ralt_dec a)
      !! 0%nat = Some b ->
    era_pin (fgn_echo g) k v -∗ file_era_pin g k vf -∗ turn v P -∗
    ps_lb v ps0 -∗ cs_lb v cs0 -∗ inp_lb v I0 -∗ f0_lb vf s0 -∗
    (((turn v (S P) ∗ ps_lb v ps0 ∗ cs_lb v (cs0 ++ [a]) ∗ inp_lb v I0
       ∗ f0_lb vf s0) ∨ T) -∗ Φ) -∗
    out_link Uart0 k b Φ.
  Proof using Hcons.
  Admitted.

  (* =================================================================== *)
  (*  S4  THE LINE READ, AT [FileOut.ftag]                                *)
  (*                                                                     *)
  (*  [UkSh.ush_tag_law] reads the era's line list off the machine's rx    *)
  (*  tag; at this application the tag is [ftag], whose third conjunct is  *)
  (*  [AppFile.fl_lb] -- the lower bound the child's create step needs     *)
  (*  ([AppFile.f_typed_some] wants [ws ∈ ls]).  This is the file twin of  *)
  (*  [UInitBoot]'s [Htg], and it is where sh's fork lend gets the line.   *)
  (* =================================================================== *)
  (*  ===== A SHAPE THAT DOES NOT COMPILE AS STATED ==================== *)
  (*                                                                     *)
  (*  [UkSh.ush_tag_law T] is [box (forall h, riscv_rx_tag h -* pure      *)
  (*  (EchoDisc.disc h) or T)] -- the ECHO discipline -- and the file     *)
  (*  era CANNOT supply it: [FileOut.ftag]'s second conjunct is           *)
  (*  [pure (FileDisc.disc_f h) or file_taint], and [disc_f h] does NOT   *)
  (*  imply [disc h] (lane STAGE's own ruling: a [cat] line is not an     *)
  (*  echo line).  So what this file proves is the FILE tag law, and      *)
  (*  [UkSh.ush_tag_law]'s [disc] must become a PARAMETER                 *)
  (*  [D : list mobs -> Prop] before [UInitSh.sh_pay_of_parts] can be     *)
  (*  applied at this era.  That is a NEW obligation; it surfaces in K3,  *)
  (*  not here, because [UkSh.ush_rest_l] does not mention the tag.       *)
  (*  PROVED (the program stream): the era's tag IS [FileOut.ftag] and its *)
  (*  second conjunct is this disjunction, so the law is the projection.    *)
  Lemma sh_tag_law_file :
    ⊢ □ (∀ h : list mobs,
           riscv_rx_tag h -∗ ⌜FileDisc.disc_f h⌝ ∨ T).
  Proof using Htag.
    rewrite Htag. iIntros "!>" (h) "Ht".
    rewrite /FileOut.ftag. iDestruct "Ht" as "(_ & Hd & _)". iExact "Hd".
  Qed.

  (* =================================================================== *)
  (*  S5  THE THREE-WAY CHILD DISPATCH                                    *)
  (*                                                                     *)
  (*  sh's child branches on the parsed line's shape -- a PURE case on     *)
  (*  [FileDisc]'s [uline_of] of the buffer, which sh's own tag law ties   *)
  (*  to the typed line (design SS5.4).  Three shapes, three entries:       *)
  (*                                                                     *)
  (*    LEcho      [UkShEcho.wp_kshm_child_echo_holds] at the FILE links  *)
  (*               -- echo at the console, [UEchoOut]'s entry.            *)
  (*    LEchoF     [UkShRedirSeam.wp_kshm_child_alloc_redir], whose open   *)
  (*               is a CALL PREMISE instantiated by [UkFileOpen]'s deed   *)
  (*               create corollary, then [exec /echo] at K1's entry.      *)
  (*    LCat       [UCatKernel]'s entry at a deed FRACTION.                *)
  (* =================================================================== *)

  (* ---- the redirect child's open receipt, on both arms ---- *)
  (* [UkShRedirAns.ush_open_ans2]'s two payload slots, at this claim.  [K]
     is the fd arm's -- the descriptor's TYPE, `f` present and EMPTY at it,
     AND the program's own half of the offset shadow at ZERO, which is what
     lane OFF-LINK's publish hands out and what K1's entry asks for.  [Kf]
     is the [-1] arm's and is NOT [emp]: the create may have fired before
     [filealloc] failed. *)
  Definition redir_K (ty : fdtype) : iProp Σ :=
    (∃ (i : Z) (γo : gname) (om : offmode),
       ⌜ty = FdInode i γo om⌝ ∗ fown r (Some (i, [])) ∗ uoff γo 0%nat)%I.

  Definition redir_Kf (s : dst) : iProp Σ :=
    (fown r s ∨ ∃ i : Z, fown r (Some (i, [])))%I.

  (* ---- HYPOTHESIS (lane OFF-LINK + F-OPEN-6): the deed's create
          corollary WITH THE FRAGMENT.  [UkFileOpen.
          wp_uk_ecall_open_create_deed_d] is this statement today with
          [uoff γo 0] missing from the fd arm and the DEVICE arm still
          present; OFF-LINK's publish adds the first
          ([UserOff.off_pub_hand_0] in [ProofSysOpenPub]) and F-OPEN-6
          removes the second. ---- *)
  Hypothesis Hopen_hand :
    forall (N : uk_names Σ) (cwdv file : Z) (l : list fdstate)
           (ls : list wordline) (ws : wordline) (jc : Z) (s : dst),
      ws ∈ ls -> EchoDisc.line_ok ws ->
      app_inv fsc_fs -∗ cons_made (fn_cons r) jc -∗ fl_lb (fgn_cl g) ls -∗
      fown r s -∗
      UkShRedirAns.ush_open_call2 N cwdv file 1537 l redir_K (redir_Kf s).

  (* ---- NOT A HYPOTHESIS ANY MORE (the program stream): the redirect
          line's lexability is a THEOREM,
          [UShLexRedir.ush_line_lexable_redir_holds], and the threading is
          [UkShRedirBody]'s three-way case.  Kept as a [Definition] so the
          round's [Proof using] lines read as they did. ---- *)
  Definition Hlexr : UkShLoop.ush_line_lexable_redir :=
    UShLexRedir.ush_line_lexable_redir_holds.

  (* ---- HYPOTHESIS: the echo-at-console child, at the FILE links.
          [UShEchoPay.sh_exec_sup_echo_wq_holds]'s twin -- with LINK-GEN
          it is an instantiation, without it a ~1,250-line twin. ---- *)
  (*  (This one names no deposit instance -- [sh_exec_sup_echo_wq] takes
      only [uexecSG].  The two laws above DO, and they are annotated:
      left implicit, [uprogSG] resolves to the ambient instance and the
      discharge, which is at [uprogSG_free], is not well-typed against it
      -- and the conversion between two deposit instances does not come
      back.  That is a fifth silent-hang shape.) *)
  Hypothesis Hchild_echo : ⊢ UkShEcho.sh_exec_sup_echo_wq Wcf.

  (* ---- HYPOTHESIS: the exec-failed diagnostic's law at the file
          families, AT THE PARAMETERIZED CARRIER (lane LINK-GEN-4).  The
          landed [ush_execfail_law_wq] names [alt_execfail] at EVERY input
          and the file's diagnostic is [FileLinksLine.fexfb], which is
          [alt_execcat] at an [LCat] line -- so the constant form is FALSE
          here.  At [ush_execfail_law_wq_at (lk_exfb FI) ...]
          the hypothesis is DISCHARGEABLE TODAY:
          [UShEchoPay.ush_execfail_law_wq_at_hold file_stage_inst]. ---- *)
  (*  ...AND IT IS DISCHARGED (the program stream), exactly as the comment
      above said it would be: the carrier is the record's own, the era's
      links are the only input, and [file_stage_inst] is not even needed.
      The links are a PREMISE and not a hypothesis because they are a
      resource the round is handed ([sh_round_holds_file]'s first). *)
  Lemma Hexecfail :
    ⊢ FileLinks.file_links g -∗
      UkShEcho.ush_execfail_law_wq_at (PS := uprogSG_free) (lk_exfb FI)
        (fun I : list (bv 8) => (length (lk_exfb FI I) - 2)%nat)
        Wcf.
  (* NOT [iApply] (durable-notes, the silent hang): the proofmode would
     unify the [Wc] SLOT -- a function -- against [Wcf]'s body, and that
     search does not come back.  Both sides are the same term after delta,
     so [exact] closes it by conversion. *)
  Proof using .
    exact (UShEchoPay.ush_execfail_law_wq_at_hold (L := FI) sh_hold).
  Qed.

  (* ---- NOT A HYPOTHESIS ANY MORE (the program stream): sh's own fork
          panic at the file families is [UShPanic.ush_panic_law_hold_at] at
          this record and [sh_hold], and the two families are the record's
          own ([FileLinkInst.file_Wcl] / [file_Wbl]) with that one linear
          conjunct -- which is the shape that lemma takes.  The era's links
          are its only input. ---- *)
  Lemma Hpanic :
    ⊢ FileLinks.file_links g -∗
      UkShDiag.ush_panic_law (PS := uprogSG_free) Wcf Wbf.
  Proof using .
    exact (UShPanic.ush_panic_law_hold_at (PS := uprogSG_free) FI sh_hold).
  Qed.

  (* ---- HYPOTHESIS (lane CAT-ENTRY-2): cat's entry at the exec channel,
          at a deed FRACTION and the offset-pinned read.  [UCatKernel.
          cat_round_at]'s [Hold] is instantiated at
          [ufd ... ∗ uoff γo p ∗ fdq r q (Some (i, bs))] -- the row, the
          program's half at the cursor, and the fraction that agrees the
          content -- which is the one line CAT-ENTRY-2's brief changes. ---- *)
  Definition cat_hold (N : uk_names Σ) (fd : nat) (wb : bool) (i : Z)
      (γo : gname) (om : offmode) (q : Qp) (bs : list (bv 8))
      : nat -> iProp Σ :=
    fun p => (UserFd.ufd (ukn_fd N) fd (FdOpen true wb (FdInode i γo om))
              ∗ uoff γo p ∗ fdq r q (Some (i, bs)))%I.

  (* WHAT SH LENDS THE cat CHILD (lane CAT-GEOM-4).  It used to be the
     credential and a deed FRACTION; it is now
     [UCatKernel.cat_lend] beside the credential -- the fraction, the
     era's cursor at the round's own start, AND THE TWO ROWS LANE
     OFF-LINK-4 OWES.  They travel HERE and not as premises of the entry
     for the reason echo's credential does: [ExecEntry.image_entry] is
     [□]-quantified over the key, so its payment premise cannot HOLD a
     linear resource, and [Pay] is what the entry hands over per
     invocation.  [om] is a PARAMETER throughout -- never [OffParked],
     never [OffHeld] literally. *)
  Definition cat_pay (I : list (bv 8)) (q1 q2 : Qp) (om : offmode)
      (sts : list fdstate) (v : era_pins) (vf : file_era)
      (ps0 : list nat) (P : nat) : iProp Σ :=
    (Wcl I 3%nat
     ∗ (∃ (cs0 : list nat) (i : Z) (bs : list (bv 8)),
          ⌜UCatOut.cat_tie cs0 s0 I (Some (i, bs))⌝
          ∗ UCatKernel.cat_lend g (fgn_cl g) r q1 q2 i bs om sts
              FsImg.ROOTINO v vf ps0 cs0 s0 I P))%I.

  (* THE ENTRY, AT THE NODE SH BUILT (lane CAT-GEOM-2).  This used to
     quantify [M] and [av] FREE, and that was WRONG: cat's diagnostic
     names `f` ([FileDisc.alt_catopen]), so an entry owed at EVERY
     argument vector is a claim cat cannot make.  The five premises below
     are the ones [UCatKernel.cat_image_entry] takes, and every one of
     them is a fact SH HAS -- it built the node ([UkShEcho.echo_cmd] at
     [t]) and it parsed the line -- so [Hchild_cat] is ONE application of
     that lemma. *)
  Hypothesis Hchild_cat :
    forall (I : list (bv 8)) (q1 q2 : Qp) (om : offmode)
           (ws : list (list (bv 8)))
           (M : gmap Z (bv 8)) (sv t : Z) (gn : nat -> bv 8)
           (sts : list fdstate) (cw : Z) (cs : gset gname)
           (pidv : mword 32)
           (v : era_pins) (vf : file_era) (ps0 : list nat) (P : nat)
           (rb : bool),
      length sts = NOFILE ->
      cw = FsImg.ROOTINO ->
      (* ...and the line is `cat f`, read off sh's own node *)
      EchoDisc.line_ok ws ->
      UShEcho.echo_node_img ws M sv t gn ->
      UkShEcho.echo_argv_bytes ws gn ->
      length ws = 2%nat ->
      UkShEcho.echo_alen ws 1%nat = 1%nat ->
      (forall j : nat, (j < 1)%nat ->
         LineWords.wl_line ws !!! (UkShEcho.echo_off ws 1%nat + j)%nat
         = FsImgCheck.fname_f !!! j) ->
      (* ...and the child's standard streams, which are sh's own *)
      take NSTD sts !! 1%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE)) ->
      take NSTD sts !! 2%nat = Some (FdOpen rb true (FdDevice ConsoleInv.CONSOLE)) ->
      fd_lowest_closed (take NSTD sts) = None ->
      (* THE PAYLOAD CONVERSION, and it is SH's: what cat's exit files is
         one of its OWN two alternatives ([UCatKernel.catq_cat], at cat's
         own end cursor); what the fork chose is [ushf_wq Wcf I].  The
         wand between them is a fact about the era's links, so it belongs
         to the round and not to cat's entry -- which is why
         [UCatKernel.cat_child_of_entry] takes [Q] as a parameter. *)
      ⊢ □ (∀ cs0 : list nat,
             UCatKernel.catq_cat g v vf ps0 cs0 s0 I P (-1)
             -∗ UkShFork.ushf_wq Wcf I) -∗
        app_taint -∗
        image_entry ElfUser.cat_elf M (mword_of_int (t + 8) : mword 64) sts
          cw cs pidv
          (fun _ : Z => UkShFork.ushf_wq Wcf I)
          (cat_pay I q1 q2 om sts v vf ps0 P) uslot.

  (* ---- HYPOTHESIS: the redirect child's own walk, from 0x9c0 to its
          exit, at the payload sh's fork chose.  [UkShFork.ushf_child_law]
          is the ECHO shape (its line premise is [UkSh.ush_line_is]); this
          is the same statement at [UkShRedirLine.ushs_line_is], assembled
          from [UkShRedirSeam.wp_kshm_child_alloc_redir] (the open as a
          call premise, [Hopen_hand]), K1's entry after [exec /echo], and
          [Hexecfail] on the failing arm. ---- *)
  Definition sh_redir_child_law : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (h : CpuId) (m : regfile) (dw dv : dfrac)
          (sa : Z) (len : nat) (ws : wordline) (file : list (bv 8))
          (fb : nat -> bv 8) (sz : Z) (ld : list fdstate) (n : nat)
          (I : list (bv 8)),
          ⌜ ukn_pay N' = (fun _ : Z => UkShFork.ushf_wq Wcf I) ⌝ -∗
          ⌜ m !!! Regidx (mword_of_int 9 : mword 5)
              = (mword_of_int sa : mword 64) ⌝ -∗
          (* THE LINE IS THE REDIRECT SHAPE, which is where this law and
             [UkShFork.ushf_child_law] part company: that one's premise is
             [UkSh.ush_line_is], and [UkShRedirLine.ushs_line_is_nosym]
             proves no such line can carry the [>] byte. *)
          ⌜ UkShRedirLine.ushs_line_is ws file fb 0%nat len ⌝ -∗
          ⌜ ws = last_ws I ⌝ -∗
          ⌜ 0 < sa ⌝ -∗ ⌜ sa + Z.of_nat len + 1 < Z64 ⌝ -∗
          ⌜ sa + Z.of_nat len < 2 ^ 38 ⌝ -∗
          ⌜ 8344 <= sz ⌝ -∗ ⌜ UserPtTree.pgroundup sz = sz ⌝ -∗
          ⌜ usz_ok (sz + 65536) ⌝ -∗
          ⌜ UkSh.ush_fd0c ld /\ UkSh.ush_fd1p ld /\ UkSh.ush_fd2p ld ⌝ -∗
          UCodeShK.shk_code (ukn_t N') -∗
          UCodeShP.shp_code (ukn_t N') -∗
          UCodeShP.shp_rodata (ukn_t N') -∗
          UkSh.ush_jtab (ukn_t N') -∗
          ustr (ukn_d N') (DfracOwn 1) sa len fb -∗
          ustr (ukn_d N') dw ushp_whitespace 5 ushp_ws_f -∗
          ustr (ukn_d N') dv ushp_symbols 7 ushp_sym_f -∗
          UserFd.ustd (ukn_fd N') ld -∗
          UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
          UserChildren.uch_any (ukn_ch N') -∗
          UkShMalloc.ushm_fresh N' sz -∗
          Wcf I 3%nat -∗
          urun N' h m (mword_of_int 0x9c0)
            (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
          WP (Loop : expr riscv_lang)))%I.

  Hypothesis Hchild_redir : ⊢ sh_redir_child_law.

  (* ...AND THE DISPATCH ITSELF: the three shapes assembled into the one
     law [UkShFork.ushf_rest_of_body] takes.  The case is PURE -- on
     [FileDisc.uline_of (wl_body (last_ws I))] -- and sh's tag law ties it
     to the line the discipline admitted. *)
  Lemma sh_child_law_file : ⊢ UkShFork.ushf_child_law Wcf.
  Proof using Hchild_cat Hchild_echo Hchild_redir Hopen_hand.
  Admitted.

  (* ...and a KILLED child pays the payload with the taint (the taint
     inhabits the credential AND the deed's arm).  PROVED (the program
     stream): the taint is the era's ([Hktaint]), it inhabits the link
     record's credential at the era's pin ([Hcltaint], which is
     [FileLinkInst.file_Hcltaint] now) and it is [sh_hold]'s own right
     arm.  The PIN is a premise because the credential's is linear under
     an existential and the killed child holds none -- the round has it
     ([sh_round_holds_file]'s third argument). *)
  Lemma sh_kill_law_file (v : era_pins) :
    era_pin (fgn_echo g) (S gen_id) v -∗ UkShFork.ushf_kill_law Wcf.
  Proof using Hkill.
    iIntros "#Hpin". rewrite /UkShFork.ushf_kill_law.
    iIntros "!>" (I) "#Hk".
    iAssert T as "#HT"; [ iApply Hktaint; iExact "Hk" | ].
    rewrite /Wcf. iSplitR.
    - iApply (Hcltaint I 0%nat v with "Hpin HT").
    - rewrite /sh_hold_at. iRight. iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  S6  THE ROUND -- [UShRest.sh_rest_holds]'s TWIN                     *)
  (*                                                                     *)
  (*  WHAT SH-ROUND MUST DELIVER: the command loop's body obligation at   *)
  (*  the file era's families, which is what [UInitSh.sh_pay_of_parts]    *)
  (*  takes and therefore what K3's [file_prog_law] spends.              *)
  (* =================================================================== *)
  Lemma sh_round_holds_file (N : uk_names Σ) :
    ⊢ udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ v : era_pins, era_pin (fgn_echo g) (S gen_id) v) -∗
      (∃ vf : file_era, file_era_pin g (S gen_id) vf) -∗
      UkSh.ush_rest_l (PS := uprogSG_free) N γp T Wcf Wbf
        (UShLine.ush_mid_at (lk_rres FI) (fgn_echo g) γp)
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
  Proof using Hchild_cat Hchild_echo Hchild_redir Hcons
              Hkill Hopen_hand Htag.
  Admitted.

End UShRound.
