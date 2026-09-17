(* ===================================================================== *)
(* UInitTreeExec.v -- /INIT'S EXEC SUPPLY FOR /sh, PAID FROM THE TAINT    *)
(* (lane TL-8, deliverable D3; design/user-tree.md section 9.6(4)).       *)
(*                                                                       *)
(* [UInitSh.init_exec_sup_of_sh_slot] is ECHO's producer of              *)
(* [UkInit.init_exec_sup_lend]: it builds the exec'd shell's OWN entry    *)
(* theorem out of sh's slot, and its Coq-level premise is the ten console *)
(* laws ([UInitSh.cons_cred_holds]).  Under a TREE application sh is not  *)
(* verified against the claim at all -- section 9.2, section 9.3(5): a    *)
(* live owner's exec goes through the taint arm -- so none of that        *)
(* machinery arises here.  This file pays the supply TREE-NATIVELY:       *)
(*                                                                       *)
(*   (W)  the walk is [ExecRun.exec_walk_of_taint]: every cursor is       *)
(*        [True], the observation opens nothing and the node the walk     *)
(*        reports is identified only by the taint;                       *)
(*   (E)  the entry is [ExecRun.image_entry_of_taint] at the GENERIC      *)
(*        slot, which the taint buys through [AppTree.tree_sup_of_taint]  *)
(*        ([AppInv.app_sup]) and [UexecExecMint.uslot_mint_all] -- the    *)
(*        output licence and the kill credential being free at this       *)
(*        record's interface, exactly as [UInitTree.tree_init_deps]       *)
(*        already reads them;                                            *)
(*   (L)  loadability is [ElfLoadable.sh_elf_loadable], by computation;   *)
(*   the refund is the lend as it went in ([UkInit.init_lend_ref]), by    *)
(*   framing -- a failed exec hands /init's child back what pays its      *)
(*   diagnostic and its exit.                                            *)
(*                                                                       *)
(* WHAT THE CREDENTIAL [Cns] IS, AND WHY IT IS THE TAINT.                 *)
(* [UkInit.init_cons_sup cn T Cns st Cr] is the supply as a WAND from the *)
(* credential /init's own console dance leaves, beside [box (T -* Cns)].  *)
(* At this claim the supply is payable at [Cns := T]: the shell's entry   *)
(* is the generic slot, the generic slot is bought with the taint, and    *)
(* nothing weaker buys it.  Both halves are then one line each.           *)
(*                                                                       *)
(* WHY IT IS NOT PAYABLE AT [Cns := True] -- the wall lane TL-7 left, and *)
(* it is REFUTED rather than open.  At [Cns := True] the node             *)
(* ([UkInit.init_exec_sup_pos], UkInit.v:1769) must produce the deposit   *)
(* holding only what it is handed, and on the lend's SECOND arm           *)
(* ([UkInit.init_lend_cred], UkInit.v:1687) that is the era's UNSPENT     *)
(* LICENCE ([UInitTree.tree_cc]'s [cc_wb], UInitTree.v:121).  One licence *)
(* cannot pay, for a reason that is a token count and not a missing       *)
(* lemma:                                                                *)
(*                                                                       *)
(*   - the conclusion [UkRunExecRef.udepw_at_refR_ids]                    *)
(*     (UkRunExecRef.v:240) is UPDATE-FREE, and                          *)
(*     [UkInit.init_exec_sup_lend] (UkInit.v:1806) is a [box], so a       *)
(*     linear licence can be spent only INSIDE the node's own            *)
(*     construction, never before it;                                    *)
(*   - inside, the taint is owed in three [*]-separated places: the two   *)
(*     slot wands of [SpecKexec.exec_slot_pre] (SpecKexec.v:861 -- the   *)
(*     bundle carries both arms though one fires), and the deposit's REFUND,    *)
(*     which must be the lend again.  [PieceFam.pf_at]'s [/\]            *)
(*     (PieceFam.v:99) covers fire-versus-refund and not the two arms;   *)
(*     the walk's cursor and the observation's receipt each reach both    *)
(*     arms but live in conjuncts [*]-separated from the refund           *)
(*     ([SpecSysExec.sys_exec_au_pre], SpecSysExec.v:265).               *)
(*                                                                       *)
(* So [Cns := True] would need TWO licences per era and [App.al_pow]      *)
(* files one.  The consequence for D4 is recorded in                      *)
(* design/user-tree.md section 9.7: /init's console dance                 *)
(* ([UInitTreeBoot.tree_init_cons_dance_all]) is landed at [Cns := True]  *)
(* and this supply at [Cns := tree_taint c], and                          *)
(* [UInitKernel.init_boot_con] takes ONE [Cns] for both.                  *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpUart.             (* [cons_licence] / [cons_licence_triv] *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.           (* [uheap_text] *)
Require Import UmodeAbi.           (* [uimg_sub] *)
Require Import UserConsole.        (* [ucons_pay] / [upos] and the record *)
Require Import UexecSlot UexecRet UexecSG.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UexecExecMint.      (* [uslot_mint_all] *)
Require Import ExecEntry.          (* [image_entry_taint] *)
Require Import ExecRun.            (* the deposit out of the supply *)
Require Import ElfLoadable.        (* [sh_elf_loadable] *)
Require Import UkRun.
Require Import UkRunExecRef.       (* [udepw_at_refR_ids] *)
Require Import UCodeInit.          (* [init_rodata] / [init_ro] *)
Require Import UkInit.
Require Import UInitSh.            (* [init_sh_pl] / [init_sh_path_of] *)
Require Import LinkUserinit.       (* [UG.uexec_wp_gen]: the generic user WP *)
Require Import SpecKexec.          (* [kexec_image_ok] / [exec_slot_pre] *)
Require Import InitBoot.           (* [init_boot_bytes] *)
Require Import UInitCons.          (* [init_cons_fd] *)
Require Import UInitKernel.        (* [init_boot_con] / [init_boot_pay] *)
Require Import UInitBoot.          (* [init_boot_room]: echo's arithmetic *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsTree.
Require Import AppTree.            (* the licence, the taint and the claim *)
Require Import UInitTree.          (* [tree_cc] *)
Require FsImg.
Require ElfUser.

Local Open Scope Z_scope.

Section UInitTreeExec.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UInitSh.v]'s rule): no local
     [Context {SG}] / [Context {PS}].  Everything stated below names no
     [psok], so there is no [uprogSG] instance to pin either. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* the console ring's cameras: the POSITION /init lends the shell across
     the exec is stated over them ([UserConsole.upos]) *)
  Context `{!uartGhostG Σ}.
  Context `{!treeG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  1.  THE GENERIC SLOT, OFF THE TAINT                                 *)
  (*                                                                     *)
  (*  [UInitBoot]'s own assembly of [UexecExecMint.uslot_mint_all], one   *)
  (*  application over.  The supply is the taint's                        *)
  (*  ([AppTree.tree_sup_of_taint]); the two other credentials the mint   *)
  (*  takes are FREE at this record's interface -- the output licence     *)
  (*  because the claim claims no console ([WpUart.cons_licence_triv])    *)
  (*  and the kill credential because a kill costs this application       *)
  (*  nothing ([RiscvPtsto.kill_cred_triv]).  Those are the same two      *)
  (*  readings [UInitTree.tree_init_deps] already makes.                  *)
  (* =================================================================== *)
  Lemma tree_gen_slot (c : tree_fixed) (r : tree_names) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    riscv_kill_cred = kill_cred_triv ->
    tree_taint c -∗
    □ (∀ (R : iProp Σ) (W : uvis),
         my_pay (uvis_gen W) (fun _ => R)%I -∗
         □ (riscv_kill_cred -∗ R) -∗ uslot W).
  Proof using .
    intros Heq Hcons Hkill. iIntros "#Ht".
    iAssert (AppInv.app_sup) as "#Hsup".
    { rewrite /AppInv.app_sup Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (tree_sup_of_taint c r with "Ht"). }
    iAssert (□ riscv_kill_cred)%I as "#Hkc";
      [ rewrite Hkill /kill_cred_triv; by iModIntro | ].
    iPoseProof (WpUart.cons_licence_triv Hcons) as "#Hlic".
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iApply (uslot_mint_all with "Hsup Hkc Hlic Hwp").
  Qed.

  (* ...AND THE TAINT ARM OF AN ENTRY, which is that mint at the payload
     the lease names.  [UserConsole.ucons_pay_eta] is why the constant
     family the generic mint is stated at IS this payload, and
     [ucons_pay_taint] is what the arm's own kill row costs: nothing, once
     the taint is in hand.  NOTE THE TAINT IS AN ARGUMENT HERE -- the
     statement is closed, and that is what makes it usable at a round
     whose lend has not been read yet. *)
  Lemma tree_image_entry_taint (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (γ : gname) (Rd : nat -> iProp Σ) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    riscv_kill_cred = kill_cred_triv ->
    ⊢ image_entry_taint (tree_taint c)
        (ucons_pay cn γ (tree_taint c) Rd) uslot.
  Proof using .
    intros Heq Hcons Hkill.
    (* the key's all-parked row (lane OFF-HAND-4, S2) is not read here:
       the generic slot is quantified over every key *)
    rewrite /image_entry_taint. iIntros "!>" (W') "%Hpk #HT Hmp".
    iDestruct (tree_gen_slot c r Heq Hcons Hkill with "HT") as "#Hgen".
    iApply ("Hgen" $! (ucons_pay cn γ (tree_taint c) Rd (-1)) W'
              with "[Hmp] []").
    - rewrite ucons_pay_eta. iExact "Hmp".
    - iModIntro. iIntros "_". iApply (ucons_pay_taint with "HT").
  Qed.

  (* =================================================================== *)
  (*  2.  THE EXEC SUPPLY ITSELF                                          *)
  (*                                                                     *)
  (*  [UInitSh.init_exec_sup_of_sh_slot]'s tree twin, and it is short     *)
  (*  because NOTHING of the exec'd image is claimed: the walk is the     *)
  (*  taint's, the entry is the generic slot, and the only reading left   *)
  (*  is /init's own -- the path `sh` out of its read-only image, which   *)
  (*  is where a0 points ([UInitSh.init_sh_path_of], a fact about /init   *)
  (*  and not about the shell).  The identity fragments and the           *)
  (*  descriptor row the node is handed are not read at all here: they    *)
  (*  are what a VERIFIED entry constructor reads, and there is none.     *)
  (* =================================================================== *)
  Lemma tree_init_exec_sup_lend (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (stc : fdstate) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    riscv_kill_cred = kill_cred_triv ->
    tree_taint c -∗
    UkInit.init_exec_sup_lend cn (tree_taint c) stc (tree_cc c).
  Proof using .
    intros Heq Hcons Hkill. iIntros "#HT".
    rewrite /UkInit.init_exec_sup_lend.
    iIntros "!>" (γ np N m pc l)
      "%Hpeq %Hhd %Ha0 %Ha1 #Hro #Hargv Hstd Hrow Hcred Hpos Hlease Hchf Hpidf".
    iAssert (image_entry_taint (tree_taint c) (ukn_pay N) uslot) as "#Hgen".
    { rewrite Hpeq.
      iApply (tree_image_entry_taint c r cn γ
                (UkInit.init_rd (cc_rd (tree_cc c)) (cc_wbn (tree_cc c)))
                Heq Hcons Hkill). }
    iApply (udepw_at_refR_ids_of_sup_ids N m pc
              (mword_of_int 0x9a8) (mword_of_int 0x1000)
              FsImg.ROOTINO (tree_taint c) UInitSh.init_sh_pl
              ElfUser.sh_elf 1%nat
              (UserFd.ustd (ukn_fd N) l ∗ upos γ np
                 ∗ ucons_pay cn γ (tree_taint c) (cc_rd (tree_cc c)) (-1)
                 ∗ UkInit.init_lend_cred (tree_taint c) stc
                     (cc_wp (tree_cc c)) (cc_wbn (tree_cc c)) l np)%I
              _ sh_elf_loadable Ha0 Ha1 Hhd
              with "[] Hgen [Hstd Hpos Hlease Hcred]").
    (* ---- THE REFUND IS THE LEND ITSELF ([UkInit.init_lend_ref]): what
           went into the deposit comes back at the shapes it went in at,
           which is what pays the child's diagnostic and its exit. ---- *)
    { iIntros "!> (Hstd & Hps & Hls & Hcred)".
      rewrite /UkInit.init_lend_ref. iFrame "Hstd Hps Hls Hcred". }
    rewrite /uexec_sup_run_ids.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd Hids".
    (* /init's own image reading, off the lent heap *)
    iAssert (⌜uimg_sub UCodeInit.init_ro M⌝)%I as %Hsro.
    { iIntros (a b Hb). rewrite /UCodeInit.init_rodata /utext_img.
      iDestruct (big_sepM_lookup _ _ a b Hb with "Hro") as "Hb".
      iDestruct (uheap_text with "Hheap Hb") as %(HM & _ & _).
      iPureIntro. exact HM. }
    iFrame "Hheap Hufd Hids".
    iSplitR; [ iPureIntro; exact (UInitSh.init_sh_path_of M Hsro) | ].
    iSplitR; [ iApply (exec_walk_of_taint with "HT") | ].
    (* the taint arm asks for the exec'ing table's all-parked row (lane
       OFF-HAND-4, S2); /init's run answers it at the empty held set *)
    iDestruct (urun_rows_parked (ukn_parked0 := Hhd) N fdv with "Hnpw")
      as %Hpk0.
    iSplitR "Hstd Hpos Hlease Hcred";
      [ iApply (image_entry_of_taint _ _ _ _ _ _ _ _ _ _ _ Hpk0 with "HT Hgen") | ].
    iFrame "Hstd Hpos Hlease Hcred".
  Qed.

  (* ...AND THE SUPPLY AS /INIT'S WALK TAKES IT.  Both halves of
     [UkInit.init_cons_sup] at [Cns := tree_taint c]: the wand from the
     credential IS the lemma above, and the law that pays it under the
     taint is the identity. *)
  Lemma tree_init_cons_sup (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (stc : fdstate) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    riscv_kill_cred = kill_cred_triv ->
    ⊢ UkInit.init_cons_sup cn (tree_taint c) (tree_taint c) stc (tree_cc c).
  Proof using .
    intros Heq Hcons Hkill. rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> #HT".
      iApply (tree_init_exec_sup_lend c r cn stc Heq Hcons Hkill with "HT").
    - iIntros "!> #HT". iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  3.  WHAT THE SUPPLY BUYS: /INIT'S WHOLE ENTRY SLOT AT THE TREE      *)
  (*                                                                     *)
  (*  [UInitKernel.init_boot_con] at this claim, with every premise of    *)
  (*  its list discharged.  Three are the tree's own -- the deposits      *)
  (*  ([UInitTree.tree_init_deps]), the kill row                          *)
  (*  ([UInitTree.tree_init_kill_law], section 9.5(2)) and the exec       *)
  (*  supply above -- and the rest is echo's assembly reused VERBATIM,    *)
  (*  which is what section 9.5(5) predicted: the room arithmetic         *)
  (*  ([UInitBoot.init_boot_room]), the ledger's length and its head, the *)
  (*  nopipe fact and [psok] at the free instance.                        *)
  (*                                                                     *)
  (*  So nothing between /init's entry and its boot bundle is echo's any  *)
  (*  more.  What D4 still owes is recorded at the two lemmas below.      *)
  (* =================================================================== *)
  Lemma tree_init_boot_con (c : tree_fixed) (r : tree_names) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    riscv_kill_cred = kill_cred_triv ->
    ⊢ □ (∀ W' : uvis,
           ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
              (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
           ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
           ⌜uvis_lazy W' = false⌝ -∗
           my_pay (uvis_gen W') (fun _ => True)%I -∗
           UInitKernel.init_boot_pay (PS := uprogSG_free) (tree_taint c)
             (tree_taint c) fsc_cons init_cons_fd (tree_cc c) -∗
           uslot W').
  Proof using .
    intros Heq Hcons Hkill.
    iApply (UInitKernel.init_boot_con (PS := uprogSG_free)
              (tree_taint c) (tree_taint c) init_cons_fd (tree_cc c) fsc_cons
              1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0 0%nat
              init_cons_fd_ne
              (tree_init_kill_law c init_cons_fd)
              (init_boot_room 0%nat ltac:(vm_compute; discriminate))
              fdt0_length eq_refl (fdv_nopipe_closed _) fdv_all_parked_fdt0
              (fun k H => H)
              with "[] [] []").
    - iApply (tree_init_deps c r Heq Hcons Hkill).
    - iApply (udep_free).
    - iApply (tree_init_cons_sup c r fsc_cons init_cons_fd Heq Hcons Hkill).
  Qed.

  (* the read family is trivial at this record, so the boot bundle's third
     conjunct costs nothing *)
  Lemma tree_cc_rd_triv (c : tree_fixed) (n : nat) : ⊢ cc_rd (tree_cc c) n.
  Proof using . exact (bi.True_intro _). Qed.

  (* ...AND THE PAYLOAD THE SLOT IS SPENT AT.  Six conjuncts, and only TWO
     of them cost the era anything: the console dance and the banner-owed
     credential [cc_wbn 0].  The banner law and the two diagnostics are
     [UInitTree]'s, off the deposits, and the read credential is [True].

     BOTH OF THE TWO COST A LICENCE, AND THAT IS D4'S WALL.  With the exec
     supply at [Cns := tree_taint c] the dance's own leaves must PRODUCE
     the taint, i.e. spend a licence ([AppTree.tree_taint_mint]); [cc_wbn 0]
     is the era's licence as well ([UInitTree.tree_cc]'s [cc_wb],
     UInitTree.v:121, which is what makes the banner the mint, section
     9.5(3)).  The two are [*]-separated here, and [App.al_pow] files ONE
     row per power-on ([AppTree.tree_licence_mint], AppTree.v:1401).  So
     this lemma takes both as premises and D4 is blocked on a ruling about
     the licence, not on a proof. *)
  Lemma tree_init_boot_pay (c : tree_fixed) (r : tree_names)
      (cn : cons_names) (stc : fdstate) :
    file_app = MkAppcfg tree_names (tree_pred c) r ->
    riscv_cons_res = cons_res_triv ->
    riscv_kill_cred = kill_cred_triv ->
    UInitKernel.init_cons_dance_all (PS := uprogSG_free) (tree_taint c)
      (tree_taint c) stc -∗
    ucons_reader cn 0%nat -∗
    cc_wbn (tree_cc c) 0%nat -∗
    UInitKernel.init_boot_pay (PS := uprogSG_free) (tree_taint c)
      (tree_taint c) cn stc (tree_cc c).
  Proof using .
    intros Heq Hcons Hkill. iIntros "Hdn Hrd Hbn".
    iDestruct (tree_init_deps c r Heq Hcons Hkill) as "#Hdp".
    rewrite /UInitKernel.init_boot_pay.
    iSplitL "Hdn"; [ iExact "Hdn" | ].
    iSplitL "Hrd"; [ iExact "Hrd" | ].
    iSplitR; [ iApply tree_cc_rd_triv | ].
    iSplitL "Hbn"; [ iExact "Hbn" | ].
    iSplitR.
    - iIntros "!>" (n N') "Hwb".
      iDestruct (tree_kinit_ban_law c stc N' with "Hdp") as "#Hbl".
      iApply ("Hbl" with "Hwb").
    - iApply (tree_kinit_diag_law c stc with "Hdp").
  Qed.

End UInitTreeExec.
