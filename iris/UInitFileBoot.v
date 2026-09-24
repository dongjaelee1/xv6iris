(* ===================================================================== *)
(*  UInitFileBoot.v -- /init's EXEC BUNDLE AT THE FILE RECORD              *)
(*  (lane INIT-FILE, item 4 of the app-file worklist).                    *)
(*                                                                       *)
(*  [UInitPipe.pipe_Hinit_boot], line for line, at the file era: the      *)
(*  claim's accessors are [UInitFileCons]'s, the console dance is         *)
(*  [UInitConsFile]'s, the credential is [UInitFileCC.file_cc] and the    *)
(*  shell's TAIL is [UShRound.sh_round_holds_file].  Three things are    *)
(*  the file's own:                                                      *)
(*                                                                       *)
(*   - THE BOOT STATE IS FILED HERE (RULING F0-BOOT).  [AppFile.file_boot]  *)
(*     hands /init the deed and its typed witness, [FileOut.fturn] the     *)
(*     boot ledger's authority; the witness names the era's boot state    *)
(*     [s0] (the deed's content, or [None] under the taint), /init files   *)
(*     it ([UInitFileCons.file_f0pre_at_of_boot]), and EVERYTHING below   *)
(*     is at the record indexed by that [s0] ([FileLinkInst.               *)
(*     file_link_inst_at g s0], RULING H').                               *)
(*   - THE SHELL'S SLOT IS BUILT UNDER THE CONSOLE'S FLAG (RULING          *)
(*     CONS-CRED): the round needs [AppFileCons.file_cons_cred], which     *)
(*     /init's own mknod decides mid-walk, so what the exec supply takes  *)
(*     is a wand from the flag to the slot.                               *)
(*   - THE PROLOGUE CREDENTIAL CARRIES THE DEED'S HOLD ([UInitFileCC.      *)
(*     file_H]): the banner and diagnostic laws are the record's, framed  *)
(*     through the writer ([UInitFileCC.kinit_banner_pay_frame]).         *)
(*                                                                       *)
(*  A FILE OF ITS OWN, as [UInitPipe.v] is beside [UInitPipeAdequacy.v]:  *)
(*  [UInitFile.v] carries the adequacy cone and takes exactly ONE thing   *)
(*  from here, [file_Hinit_boot_at].                                      *)
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
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import ChildTok.
Require Import UexecSlot.
Require Import UexecRet.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import SpecKexec.
Require Import FsAbsDefs.
Require Import UexecExecInst.
Require Import UkRun.
Require Import UkInit.
Require Import UexecExecMint.
Require Import UInitKernel.
Require Import LineWords.
Require Import UInitDiag.
Require Import UInitCons.
Require Import UInitSh.
Require Import UShEcho.
Require Import UShCatPay.
Require Import UShLine.
Require Import AppEcho.
Require Import EchoOut.
Require Import UserConsole.
Require Import UserFd.
Require Import UkSh.
Require Import InitBoot.
Require Import ElfUser.
Require Import UInitBoot.          (* [init_boot_bundle_of_pinned] *)
Require Import FileState.
Require Import EchoFsPure.
Require Import FileFsPure.
Require Import FileOut.
Require Import AppFile.
Require Import AppFileCons.        (* [file_cons_cred] *)
Require Import AppFileRec.         (* [file_ifc] and its projections *)
Require Import FileLinks.
Require Import FileLinksAt.
Require Import FileLinkInst.
Require Import UkShRedirBody.      (* [ush_line_file] *)
Require Import UInitFileCons.      (* the claim's readings, the boot filing *)
Require Import UInitConsFile.      (* the console dance's file leaves *)
Require Import UShRound.           (* the round *)
Require Import UInitFileCC.        (* [file_cc], its laws, the supply *)
Require FsImg.
Require InodeInv.

Local Open Scope Z_scope.

Section FileInitBoot.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  Context `{!echoOutG Σ}.
  Context `{!fileAppG Σ, !fileOutG Σ}.

  (* SEALED, as [UInitFileCC.v] / [UInitPipe.v]: a [Persistent]/[IntoWand]
     search on [sh_pay_at] descends into [ush_rest_l_at]'s wand tower. *)
  #[local] Typeclasses Opaque UInitSh.sh_pay_at.
  #[local] Typeclasses Opaque UkSh.ush_rest_l_at.

  (* A SLOT ABSORBS A [◇], because it ends in a [WP] ([UexecRet.uslot_bupd]'s
     twin).  It is what lets /init hand the first process the two payload
     pieces the deed's witness pays for ONE STEP LATER: the witness comes
     under the [▷] of [AppFile.file_boot]'s transport, the pieces are
     timeless, and the bundle's own [|==>] absorbs no [◇]. *)
  Lemma uslot_except_0 (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (W : uvis) :
    ◇ (uslot (SG := uexecSG_xv6) W : iProp Σ) -∗ uslot (SG := uexecSG_xv6) W.
  Proof using .
    rewrite !(uslot_unfold (SG := uexecSG_xv6) W).
    iIntros "H" (h xi C pt Rfd Rut HRut) "%Hl %Hp %Hlz Hb".
    rewrite /wp_triv. iMod "H".
    iApply ("H" $! h xi C pt Rfd Rut HRut with "[//] [//] [//] Hb").
  Qed.

  Lemma file_Hinit_boot_at
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (g : file_gn) (r : file_names) :
    @file_app Σ HF = MkAppcfg file_names (file_pred (fgn_cl g)) r ->
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = file_ifc g ->
    ⊢ app_inv fsc_fs -∗ file_boot (fgn_cl g) (S gen_id) r -∗
      fturn g (S gen_id) -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof using HU.
    intros Heq Hiface.
    (* the three projections, off the one equation *)
    assert (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = ftag g)
      by (rewrite /riscv_rx_tag Hiface; by cbn [file_ifc ai_tag file_tag]).
    assert (Hkill : @app_taint Σ (@riscv_fixedGS Σ HR)
                    = file_taint (fgn_cl g))
      by (rewrite /app_taint Hiface; by cbn [file_ifc ai_kill file_kill]).
    assert (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = fecl g)
      by (rewrite /riscv_cons_res Hiface; by cbn [file_ifc ai_cons file_cons]).
    assert (Hktaint : ⊢ app_taint -∗ file_taint (fgn_cl g)).
    { rewrite Hkill. iIntros "#H". iExact "H". }
    iIntros "#Hinv Hb Hturn".
    (* ---- THE DEED, AND THE BOOT STATE IT NAMES (RULING F0-BOOT) ----
       [file_boot]'s typed witness is under one [▷] -- the transport is a
       [|==>], and this theorem's conclusion is one too, which absorbs no
       [◇] -- so the witness is CASE-SPLIT UNDER THE LATER (which state it
       names decides the index), the ledger is filed now (it needs no
       witness), and the head precondition is taken one step later. *)
    rewrite /file_boot. iDestruct "Hb" as "[Hcb Hd]".
    iDestruct "Hd" as (s) "[Hd Hty]". rewrite bi.later_or.
    iAssert (∃ s0 : fstate, ▷ boot_at g s0 s)%I with "[Hty]" as (s0) "#Hbt".
    { iDestruct "Hty" as "[#Hty | #HT]".
      - iExists (dst_content s). iNext. rewrite /boot_at. iLeft. by iFrame "Hty".
      - iExists None. iNext. rewrite /boot_at. iRight. by iFrame "HT". }
    iMod (file_f0bw_of_boot g s0 with "Hturn") as "[Hturn #Hbw]".
    iAssert (▷ f0pre_at g s0)%I as "#Hpre".
    { iNext. iApply (file_f0pre_at_of_bw g s0 s with "Hbw Hbt"). }
    (* ---- THE ERA'S PIN, out of the (filed) turn ---- *)
    iAssert (∃ v : era_pins, era_pin (fgn_echo g) (S gen_id) v)%I as "#Hpine".
    { rewrite /fturn_core. iDestruct "Hturn" as (v vf) "(#Hp0 & _)".
      iExists v. iExact "Hp0". }
    (* ---- the taint's supply, and the generic slot it buys ---- *)
    iDestruct (file_sup_of_taint_at g r Heq) as "#Hsup".
    iDestruct (file_gen_mint g r Heq Hkill) as "#Hmint".
    (* ---- the pins law, and /init's own row out of it ---- *)
    iDestruct (file_fs_pure_law g r Heq) as "#Hfs".
    iDestruct (file_era0_pins_law g r Heq) as "#Hcl".
    (* ---- /init's three deposits ---- *)
    iDestruct (file_init_deps g r Heq Hkill) as "#Hdp".
    (* ...AND sh's OWN FREE WRITE LAW UNDER THE TAINT: [UkSh.sh_deps] IS
       [udepw_law 16], the first bullet of [Hdp] read at sh's name *)
    iAssert (□ (file_taint (fgn_cl g) -∗ UkSh.sh_deps (PS := uprogSG_free)))%I
      as "#Hshdp".
    { iModIntro. iIntros "#HT". rewrite /UkSh.sh_deps.
      iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] []").
      - iApply ("Hsup" with "HT").
      - rewrite Hkill. iExact "HT". }
    (* ---- the tag's reading, at the FILE discipline ---- *)
    iDestruct (file_tag_law_holds g Htag) as "#Htg".
    (* THE LINKS, ONCE *)
    iAssert (FileLinks.file_links g) as "#Hlks";
      [ iApply (FileLinks.file_links_holds g Hcons) | ].
    assert (Hlkp : ⊢ FileLinks.file_links g)
      by (iApply (FileLinks.file_links_holds g Hcons)).
    (* ---- /echo's and /cat's PINNED ENTRIES, off the same claim law:
           echo's slot reads the claim at the ECHO purity, which the file
           purity carries ([FileFsPure.file_fs_pure_echo]) ---- *)
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v
                  ∗ (⌜EchoFsPure.echo_fs_pure v⌝ ∨ file_taint (fgn_cl g))))%I
      as "#Hefs".
    { iIntros "!>" (v) "Hp".
      iDestruct ("Hfs" $! v with "Hp") as "[Hp [%Hf | HT]]";
        [ iFrame "Hp"; iLeft; iPureIntro; exact (FileFsPure.file_fs_pure_echo v Hf)
        | iFrame "Hp"; iRight; iExact "HT" ]. }
    iAssert (UShEcho.sh_echo_slot (file_taint (fgn_cl g))) as "#Hslot".
    { iApply UShEcho.sh_echo_slot_of_fs_pure_holds.
      rewrite /UShEcho.sh_echo_slot_of_fs_pure.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hefs" | iExact "Hmint" ]. }
    iAssert (UShCatPay.sh_cat_slot (file_taint (fgn_cl g))) as "#Hcat".
    { iApply UShCatPay.sh_cat_slot_of_fs_pure_holds.
      rewrite /UShCatPay.sh_cat_slot_of_fs_pure.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hfs" | iExact "Hmint" ]. }
    (* ---- the shell's slot, UNDER THE CONSOLE'S FLAG (RULING CONS-CRED):
           the state payload, the TAIL at the file era's round, the tag ---- *)
    iAssert (□ (∀ jo : option Z,
                  file_cons_cred (fgn_cl g) r jo -∗
                  UInitSh.init_sh_slot (file_taint (fgn_cl g))
                    (UInitSh.sh_pay_at UkShRedirBody.ush_line_file
                       (file_taint (fgn_cl g)) (file_cc HR GEN g r s0)
                       UInitSh.sh_Rsh 0%nat)))%I with "[]" as "#Hsh".
    { iIntros "!>" (jo) "#Hcred".
      rewrite /UInitSh.init_sh_slot /UInitSh.init_sh_slot_core.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hefs" | ].
      iSplitR; [ iExact "Hmint" | ].
      iApply (UInitSh.sh_pay_of_parts_at UkShRedirBody.ush_line_file
                (file_taint (fgn_cl g)) (file_cc HR GEN g r s0)
                UInitSh.sh_Rsh 0%nat
                with "[] [] Htg");
        [ iApply UInitSh.sh_pay_state_holds | ].
      iIntros (γp N).
      iApply (UShRound.sh_round_holds_file g r Heq s0 Hcons Htag Hkill γp N
                with "Hlks [] Hslot Hcat Hpine []").
      - iApply (udep_free).
      - iExists jo. iExact "Hcred". }
    (* ---- THE PROMPT'S LAW at every line boundary, off the links ---- *)
    iAssert (UShKernel.sh_prompt_law (PS := uprogSG_free) (UShRound.Wcf g r s0))%I
      as "#Hplaw".
    { iApply (UShRound.sh_prompt_law_file g r s0 Hcons with "Hlks"). }
    (* ---- the supply as a wand from the console credential ---- *)
    iAssert (UkInit.init_cons_sup fsc_cons (file_taint (fgn_cl g))
               (init_cons_cred (file_taint (fgn_cl g)) (fn_cons r)) init_cons_fd
               (file_cc HR GEN g r s0))%I as "#Hxs".
    { iApply (file_cons_sup_of_sh_slot HR GEN g r s0 Heq Hcons Htag
                init_cons_fd 0%nat (fun k H => H)
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity) Hlkp
                with "[] Hshdp Hplaw Hsh").
      iApply (udep_free). }
    (* ---- THE CONSOLE DANCE, at whichever arm the VIEW decided ---- *)
    iAssert (UInitKernel.init_cons_dance_all (PS := uprogSG_free)
               (file_taint (fgn_cl g))
               (init_cons_cred (file_taint (fgn_cl g)) (fn_cons r))
               init_cons_fd)%I with "[Hcb]" as "Hdn".
    { rewrite /echo_boot. iDestruct "Hcb" as "[HK | [%i #Hm]]".
      - iApply (UInitKernel.init_cons_dance_all_miss (PS := uprogSG_free)
                  (file_taint (fgn_cl g))
                  (init_cons_cred (file_taint (fgn_cl g)) (fn_cons r))
                  (cons_key (fn_cons r)) init_cons_fd with "[] HK").
        iApply (init_cons_leaves_file_of_leg g r Heq with "[] Hinv").
        iApply (file_cons_create_leg_holds g r).
      - iApply (UInitKernel.init_cons_dance_all_hit (PS := uprogSG_free)
                  (file_taint (fgn_cl g))
                  (init_cons_cred (file_taint (fgn_cl g)) (fn_cons r))
                  init_cons_fd with "[] []").
        + iApply (init_cons_hit_file_of_leg g r i Heq with "[] Hm Hinv").
          iApply (file_cons_create_leg_holds g r).
        + iApply (init_cons_cred_made_file g r i with "Hm"). }
    (* ---- /init's own entry, as the bundle's constructor wand ---- *)
    iAssert (□ (∀ W' : uvis,
                  ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
                     (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  UInitKernel.init_boot_pay (PS := uprogSG_free)
                    (file_taint (fgn_cl g))
                    (init_cons_cred (file_taint (fgn_cl g)) (fn_cons r))
                    fsc_cons init_cons_fd
                    (file_cc HR GEN g r s0)
                    -∗ uslot W'))%I as "#Hcon".
    { iApply (UInitKernel.init_boot_con (PS := uprogSG_free)
                (file_taint (fgn_cl g))
                (init_cons_cred (file_taint (fgn_cl g)) (fn_cons r)) init_cons_fd
                (file_cc HR GEN g r s0)
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
    (* ---- THE LINEAR PAYLOAD'S TWO WITNESS-PAID PIECES, ONE STEP LATER:
           the reader's pin at count 0 (the residue at the head) and the
           banner-owed credential AT THE DEED'S OWN CONTENT
           ([file_rres_at_of_boot] / [file_Wbf_at_of_boot]).  Both are
           timeless, which is what the slot's [◇] below spends. ---- *)
    iAssert (▷ (UserConsole.cc_rd (file_cc HR GEN g r s0) 0%nat
                ∗ UserConsole.cc_wbn (file_cc HR GEN g r s0) 0%nat))%I
      with "[Hturn Hd]" as "Hp1".
    { iNext.
      iDestruct (file_rres_at_of_boot g s0 with "Hturn Hpre")
        as "[Hturn Hres0]".
      iDestruct "Hres0" as (v0) "[#Hpin0 #Hres0]".
      iDestruct (file_Wbf_at_of_boot g r s0 s with "Hturn Hpre Hd Hbt")
        as "[Hdl Hbn]".
      iSplitL "Hdl".
      { rewrite /file_cc /=. rewrite /UShLine.ush_rd_pin_at.
        iDestruct "Hdl" as (v) "(#Hpin & Hdl & #HE)".
        iDestruct (era_pin_agree with "Hpin0 Hpin") as %<-.
        iExists v0, []. iSplitR;
          [ iPureIntro; split; [ reflexivity | exact rest_of_nil ] | ].
        iFrame "Hpin0 Hdl HE Hres0". }
      rewrite /UserConsole.cc_wbn /file_cc /=. iExists []. by iFrame "Hbn". }
    (* ---- THE THREE LAWS, at the record, and the bundle's payload as the
           constructor takes it: the witness-free half now, the other
           under the later ---- *)
    iDestruct (UInitDiag.kinit_banner_law_pro_holds_at
                 (file_link_inst_at g s0) (PS := uprogSG_free)
                 with "Hlks") as "#Hblaw".
    iDestruct (UInitDiag.kinit_execfail_law_holds_at
                 (file_link_inst_at g s0) (PS := uprogSG_free)
                 with "Hlks") as "#Hxlaw".
    iDestruct (UInitDiag.kinit_forkfail_law_holds_at
                 (file_link_inst_at g s0) (PS := uprogSG_free)
                 with "Hlks") as "#Hflaw".
    set (Pay0 := (UInitKernel.init_cons_dance_all (PS := uprogSG_free)
                    (file_taint (fgn_cl g))
                    (init_cons_cred (file_taint (fgn_cl g)) (fn_cons r))
                    init_cons_fd
                  ∗ ucons_reader fsc_cons 0%nat
                  ∗ □ (∀ (n : nat) (N' : uk_names Σ),
                        UserConsole.cc_wbn (file_cc HR GEN g r s0) n -∗
                        UkInitMain.kinit_banner0 (PS := uprogSG_free) N' init_cons_fd
                          (UserConsole.cc_wp (file_cc HR GEN g r s0) n))
                  ∗ UkInitMain.kinit_diag_law (PS := uprogSG_free) init_cons_fd
                      (UserConsole.cc_wp (file_cc HR GEN g r s0))
                      (UserConsole.cc_wbn (file_cc HR GEN g r s0)))%I).
    set (Pay1 := (UserConsole.cc_rd (file_cc HR GEN g r s0) 0%nat
                  ∗ UserConsole.cc_wbn (file_cc HR GEN g r s0) 0%nat)%I).
    (* the constructor wand at THIS payload: the later's pieces are timeless,
       and the slot absorbs the [◇] *)
    iAssert (□ (∀ W' : uvis,
                  ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
                     (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  (Pay0 ∗ ▷ Pay1) -∗ uslot W'))%I as "#Hcon'".
    { iIntros "!>" (W') "%Hok %Hcw %Hlz Hp [HP0 HP1]".
      iApply uslot_except_0. rewrite /Pay1. iMod "HP1" as "[Hrd0 Hwb0]".
      iModIntro.
      iApply ("Hcon" $! W' with "[%] [%] [%] Hp [HP0 Hrd0 Hwb0]");
        [ exact Hok | exact Hcw | exact Hlz | ].
      rewrite /UInitKernel.init_boot_pay /Pay0.
      iDestruct "HP0" as "(Hdn & Hrd & #Hbl & #Hdg)".
      (* by hand, in the payload's order: a [Frame] search through the
         dance and the diagnostic law does not come back *)
      iSplitL "Hdn"; [ iExact "Hdn" | ].
      iSplitL "Hrd"; [ iExact "Hrd" | ].
      iSplitL "Hrd0"; [ iExact "Hrd0" | ].
      iSplitL "Hwb0"; [ iExact "Hwb0" | ].
      iSplitR; [ iExact "Hbl" | iExact "Hdg" ]. }
    iApply (init_boot_bundle_of_pinned (file_taint (fgn_cl g)) (Pay0 ∗ ▷ Pay1)
              with "Hcl Hinv Hcon' [] [Hdn Hp1]").
    - iIntros "!>" (W') "#Ht Hp".
      iApply ("Hmint" $! True%I W' with "Ht Hp []").
      iModIntro. iIntros "_". done.
    - iIntros "Hrd". iSplitR "Hp1"; [ | iExact "Hp1" ]. rewrite /Pay0.
      iSplitL "Hdn"; [ iExact "Hdn" | ].
      iSplitL "Hrd"; [ rewrite ucons_reader_eq; iExact "Hrd" | ].
      (* the banner-owed family WITH THE HOLD and the record's [cc_wbn] are
         ONE family ([file_wbn_to] / [file_wbn_of]) *)
      iSplitR.
      { iIntros "!>" (n N') "Hb".
        iDestruct (file_wbn_to HR GEN g r s0 n with "Hb") as "[Hb Hh]".
        iApply (kinit_banner_pay_frame HR GEN N' _ _ _ _ _
                  with "[Hb] Hh").
        iApply ("Hblaw" $! n N' with "Hb"). }
      rewrite /UkInitMain.kinit_diag_law.
      iSplitR; last first.
      { iIntros "!>" (n N') "[Hp _]". iApply ("Hflaw" $! n N' with "Hp"). }
      iIntros "!>" (n N') "[Hp Hh]".
      iPoseProof ("Hxlaw" $! n N' with "Hp") as "H".
      iDestruct (kinit_banner_pay_frame HR GEN N' _ _ _ _ _ with "H Hh") as "H".
      rewrite /UkInit.kinit_banner_pay.
      iIntros "Hl". iDestruct ("H" with "Hl") as (Ch) "(#Hst & H0 & Hfin)".
      iExists Ch. iFrame "Hst H0".
      iIntros "HC". iDestruct ("Hfin" with "HC") as "[$ Hrt]".
      iDestruct "Hrt" as "[Hb Hh]".
      iApply (file_wbn_of HR GEN g r s0 n with "Hb Hh").
  Qed.

End FileInitBoot.
