(* ===================================================================== *)
(*  UInitConsPipe.v -- /init's CONSOLE DANCE AT THE PIPE CLAIM            *)
(*  (lane PIPE-CLAIM).                                                   *)
(*                                                                       *)
(*  [UInitCons.init_cons_laws_at] -- the nine-conjunct bundle /init's     *)
(*  mknod/open rounds run on -- ASSEMBLED at                              *)
(*  [AppPipeClaim.pipe_pred], at both credentials (the KEY arm and the    *)
(*  FLAG arm) and at both readings of the pure parameter (the pipeline    *)
(*  claim's own [FileFsPure.file_fs_pure] and the [EchoFsPure.            *)
(*  echo_fs_pure] the landed leaves are stated at).                       *)
(*                                                                       *)
(*  Upstream's [UInitConsFile.v] is the mould.  THE PIPE BUNDLE IS        *)
(*  CHEAPER IN TWO PLACES, and both are consequences of the claim having  *)
(*  no deed:                                                              *)
(*                                                                       *)
(*   - conjunct (g) needs NO create leg of its own.  The file bundle      *)
(*     carries [file_cons_create_leg] as a PREMISE because a device       *)
(*     called `f` in the root refutes its deed conjunct at every deed     *)
(*     value, so (g) had to be supplied from outside at the one name the  *)
(*     syscall can reach; [AppPipeCons.pipe_cons_create_other] discharges *)
(*     (g) outright at [init_cons_laws_at]'s own first side condition and *)
(*     ignores the second.                                                *)
(*                                                                       *)
(*   - the record equation is the ONLY parameter.  There is no era ghost, *)
(*     no ledger and no second name record: [r] is an [AppEcho.           *)
(*     echo_names] and the fixed part is [AppEcho.echo_fixed].            *)
(*                                                                       *)
(*  Sections 1-3 are [UInitConsFile]'s 4a-4c (the four bundles), section  *)
(*  4 is its section 2 (the seal and the credential the shell is handed)  *)
(*  and section 5 its 4d/4e/4f (the two LEAF pairs and sh's console arm). *)
(*  All of it goes through: nothing here needs the pipeline record's      *)
(*  interface equation, only the CLAIM equation, which is a parameter.    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface
        SailStdpp.ConcurrencyInterfaceBuiltins
        SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values
        SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import FsAbsDefs.
Require Import FsConsPin.
Require Import EchoFsPure.
Require Import FileFsPure.
Require Import ConsoleInv.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.
Require Import EchoOut.
Require Import AppEcho.
Require Import AppPipeClaim.
Require Import AppPipeCons.
Require Import UkRun.
Require Import UkInit.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import UkSh.
Require Import CtxIdDefs.
Require Import UInitCons.
Require Import UInitConsK.
Require Import UShConsK.
Local Open Scope Z_scope.

Section UInitConsPipe.
  (* the kernel's instance is AMBIENT ([UInitSh.v]'s note): no local
     [Context {SG}] / [Context {PS}]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* the console KEY's camera ([Xv6Cameras]'s note: NOT a second
     [mono_natG] beside the flag's) *)
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  (* the echo claims' class -- the pipeline application's fixed part is
     the echo application's *)
  Context `{!echoOutG Σ}.

  Context (γ : echo_fixed) (r : echo_names).

  Local Notation cdev := (ADev CONSOLE 0).

  (* ---- 1.  THE KEY ARM, at the PIPE reading of the pure half ---- *)
  Lemma init_cons_laws_pipe :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    ⊢ init_cons_laws_at FileFsPure.file_fs_pure (cons_made r)
        cons_absent (echo_taint γ) (cons_key r).
  Proof using .
    intros Heq.
    rewrite /init_cons_laws_at /init_cons_pin_law.
    rewrite Heq. rewrite /app_sup. cbn [app_pred app_run app_names].
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit;
      [| iSplit; [| iSplit ]]]]]]].
    - iIntros "!> #Ht". iApply (pipe_sup_of_taint γ r with "Ht").
    - iIntros "!>" (v) "Hp". iApply (pipe_fs_pure_acc γ r v with "Hp").
    - iApply (pipe_cons_abs_law γ r).
    - iIntros "!>" (av i) "%Hfree Hp".
      iApply (pipe_cons_arm γ r av i Hfree with "Hp").
    - iIntros "!>" (av0 av i cn) "%Hfree %Hp0 %Hab0 %Hab %Hrow %Hcn Hp".
      iApply (pipe_cons_unarm_efp_absent γ r av0 av i cn Hfree
                (FileFsPure.file_fs_pure_echo av0 Hp0) Hrow Hcn Hab
                with "Hp").
    - iIntros "!>" (av ents nl i) "%Hpre Hk Hp".
      iApply (pipe_cons_mknod γ r av ents nl i Hpre with "Hk Hp").
    - iIntros "!>" (av d nmn ents nl i) "%Hpre %Hoth _ Hp".
      iApply (pipe_cons_create_other γ r av d nmn ents nl i Hpre Hoth
                with "Hp").
    - iIntros "!>" (av i) "%Hpr Hp".
      iApply (pipe_cons_shoot γ r av i Hpr with "Hp").
    - iIntros "!>" (i) "#Hm". iApply (pipe_cons_law γ r i with "Hm").
  Qed.

  (* ---- 2.  ...and at the ECHO reading, which is what the leaves take ---- *)
  Lemma init_cons_laws_efp_pipe :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    ⊢ init_cons_laws (echo_taint γ) (cons_key r) r.
  Proof using .
    intros Heq.
    rewrite /init_cons_laws /init_cons_laws_at /init_cons_pin_law.
    rewrite Heq. rewrite /app_sup. cbn [app_pred app_run app_names].
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit;
      [| iSplit; [| iSplit ]]]]]]].
    - iIntros "!> #Ht". iApply (pipe_sup_of_taint γ r with "Ht").
    - iIntros "!>" (v) "Hp". iApply (pipe_echo_fs_pure_acc γ r v with "Hp").
    - iApply (pipe_cons_abs_law γ r).
    - iIntros "!>" (av i) "%Hfree Hp".
      iApply (pipe_cons_arm γ r av i Hfree with "Hp").
    - iIntros "!>" (av0 av i cn) "%Hfree %Hp0 %Hab0 %Hab %Hrow %Hcn Hp".
      iApply (pipe_cons_unarm_efp_absent γ r av0 av i cn Hfree Hp0 Hrow Hcn
                Hab with "Hp").
    - iIntros "!>" (av ents nl i) "%Hpre Hk Hp".
      iApply (pipe_cons_mknod γ r av ents nl i Hpre with "Hk Hp").
    - iIntros "!>" (av d nmn ents nl i) "%Hpre %Hoth _ Hp".
      iApply (pipe_cons_create_other γ r av d nmn ents nl i Hpre Hoth
                with "Hp").
    - iIntros "!>" (av i) "%Hpr Hp".
      iApply (pipe_cons_shoot γ r av i Hpr with "Hp").
    - iIntros "!>" (i) "#Hm". iApply (pipe_cons_law γ r i with "Hm").
  Qed.

  (* ---- 3.  THE FLAG ARM, both readings ---- *)
  Lemma init_cons_laws_made_pipe (i0 : Z) :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    cons_made r i0 -∗
    init_cons_laws_at FileFsPure.file_fs_pure (cons_made r)
      (cons_present_at i0) (echo_taint γ) (cons_made r i0).
  Proof using .
    intros Heq.
    rewrite /init_cons_laws_at /init_cons_pin_law.
    rewrite Heq. rewrite /app_sup. cbn [app_pred app_run app_names].
    iIntros "#Hm".
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit;
      [| iSplit; [| iSplit ]]]]]]].
    - iIntros "!> #Ht". iApply (pipe_sup_of_taint γ r with "Ht").
    - iIntros "!>" (v) "Hp". iApply (pipe_fs_pure_acc γ r v with "Hp").
    - iIntros "!>" (v) "#Hm' Hp".
      iDestruct (pipe_cons_law γ r i0 with "Hm") as "#Hl".
      iDestruct ("Hl" $! v with "Hp") as "[Hp Hc]". iFrame "Hp Hm' Hc".
    - iIntros "!>" (av i) "%Hfree Hp".
      iApply (pipe_cons_arm γ r av i Hfree with "Hp").
    - iIntros "!>" (av0 av i cn) "%Hfree %Hp0 %Hpv0 %Hpv %Hrow %Hcn Hp".
      iApply (pipe_cons_unarm_efp_present γ r av0 av i i0 cn Hfree
                (FileFsPure.file_fs_pure_echo av0 Hp0) Hrow Hcn Hpv0
                with "Hm Hp").
    - iIntros "!>" (av ents nl i) "%Hpre Hk Hp".
      iApply (pipe_cons_mknod_present γ r av ents nl i i0 Hpre with "Hk Hp").
    - iIntros "!>" (av d nmn ents nl i) "%Hpre %Hoth _ Hp".
      iApply (pipe_cons_create_other γ r av d nmn ents nl i Hpre Hoth
                with "Hp").
    - iIntros "!>" (av i) "%Hpr Hp".
      iApply (pipe_cons_shoot γ r av i Hpr with "Hp").
    - iIntros "!>" (i) "#Hm2". iApply (pipe_cons_law γ r i with "Hm2").
  Qed.

  Lemma init_cons_laws_made_efp_pipe (i0 : Z) :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    cons_made r i0 -∗
    init_cons_laws_at EchoFsPure.echo_fs_pure (cons_made r)
      (cons_present_at i0) (echo_taint γ) (cons_made r i0).
  Proof using .
    intros Heq.
    rewrite /init_cons_laws_at /init_cons_pin_law.
    rewrite Heq. rewrite /app_sup. cbn [app_pred app_run app_names].
    iIntros "#Hm".
    iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit; [| iSplit;
      [| iSplit; [| iSplit ]]]]]]].
    - iIntros "!> #Ht". iApply (pipe_sup_of_taint γ r with "Ht").
    - iIntros "!>" (v) "Hp". iApply (pipe_echo_fs_pure_acc γ r v with "Hp").
    - iIntros "!>" (v) "#Hm' Hp".
      iDestruct (pipe_cons_law γ r i0 with "Hm") as "#Hl".
      iDestruct ("Hl" $! v with "Hp") as "[Hp Hc]". iFrame "Hp Hm' Hc".
    - iIntros "!>" (av i) "%Hfree Hp".
      iApply (pipe_cons_arm γ r av i Hfree with "Hp").
    - iIntros "!>" (av0 av i cn) "%Hfree %Hp0 %Hpv0 %Hpv %Hrow %Hcn Hp".
      iApply (pipe_cons_unarm_efp_present γ r av0 av i i0 cn Hfree Hp0
                Hrow Hcn Hpv0 with "Hm Hp").
    - iIntros "!>" (av ents nl i) "%Hpre Hk Hp".
      iApply (pipe_cons_mknod_present γ r av ents nl i i0 Hpre with "Hk Hp").
    - iIntros "!>" (av d nmn ents nl i) "%Hpre %Hoth _ Hp".
      iApply (pipe_cons_create_other γ r av d nmn ents nl i Hpre Hoth
                with "Hp").
    - iIntros "!>" (av i) "%Hpr Hp".
      iApply (pipe_cons_shoot γ r av i Hpr with "Hp").
    - iIntros "!>" (i) "#Hm2". iApply (pipe_cons_law γ r i with "Hm2").
  Qed.

  (* =================================================================== *)
  (*  4.  THE SEAL, AND THE CREDENTIAL THE SHELL IS HANDED                *)
  (*                                                                     *)
  (*  [UInitConsFile]'s section 2 at the pipe claim.  None of the three   *)
  (*  reads the nine laws: the first two are [AppPipeCons]'s own seal     *)
  (*  lemmas at the era's record and the third is built from them through *)
  (*  [AppInv.app_claim_update] and                                       *)
  (*  [UInitConsK.init_open_absent_leaf_holds].                           *)
  (* =================================================================== *)

  Lemma init_cons_never_abs_law_pipe :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    ⊢ init_cons_abs_law (echo_taint γ) (cons_never r).
  Proof using .
    intros Heq. rewrite /init_cons_abs_law /init_cons_pin_law.
    rewrite Heq. cbn [app_pred app_run app_names].
    iIntros "!>" (v) "#Hn Hp".
    iDestruct (pipe_cons_never_law γ r) as "#Hl".
    iDestruct ("Hl" with "Hn") as "#Hl'".
    iDestruct ("Hl'" $! v with "Hp") as "[Hp Hc]". iFrame "Hp Hn Hc".
  Qed.

  Lemma init_cons_seal_law_pipe :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    ⊢ □ (∀ av : aview, cons_key r -∗ ▷ app_pred app_run av
           ={⊤ ∖ ↑appN}=∗
           ▷ app_pred app_run av ∗ (cons_never r ∨ echo_taint γ)).
  Proof using .
    intros Heq. rewrite Heq. cbn [app_pred app_run app_names].
    iIntros "!>" (av) "HK >Hp".
    iMod (pipe_cons_seal_step γ r av with "HK Hp") as "[Hp Hn]".
    iModIntro. iFrame "Hp Hn".
  Qed.

  (* WHAT A FAILED MKNOD LEAVES AT THE KEY ARM. *)
  Lemma init_cons_seal_out_pipe (N : uk_names Σ) :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    app_inv fsc_fs -∗
    □ (cons_key r ={⊤}=∗
         UkInit.uki_mknod_out (PS := uprogSG_free) N (echo_taint γ)
           (init_cons_cred (echo_taint γ) r) init_cons_fd).
  Proof using .
    intros Heq. iIntros "#Hinv !> HK".
    iDestruct (init_cons_never_abs_law_pipe Heq) as "#Habs".
    iMod (app_claim_update ⊤ fsc_fs (cons_key r)
            (cons_never r ∨ echo_taint γ)%I
            ltac:(set_solver) with "Hinv [] HK") as "Hn".
    { iApply (init_cons_seal_law_pipe Heq). }
    iModIntro. rewrite /UkInit.uki_mknod_out.
    iDestruct "Hn" as "[#Hn | #HT]"; last first.
    { iRight. iRight. iExact "HT". }
    iRight. iLeft. iExists (cons_never r).
    iDestruct (init_open_absent_leaf_holds N (echo_taint γ) (cons_never r)
                 ltac:(apply _) ltac:(apply _) ltac:(apply _)
                 with "Habs Hinv") as "#Hlf".
    iSplitR; [iExact "Hlf" |]. iSplitR; [iExact "Hn" |].
    iApply (init_cons_cred_of_never (echo_taint γ) r with "Hn").
  Qed.

  Lemma init_cons_cred_made_pipe (i0 : Z) :
    cons_made r i0 -∗ init_cons_cred (echo_taint γ) r.
  Proof using .
    iApply (init_cons_cred_of_made (echo_taint γ) r i0).
  Qed.

  (* =================================================================== *)
  (*  5.  THE TWO LEAF PAIRS, AND WHAT SH IS HANDED                       *)
  (*  ([UInitConsFile]'s 4d / 4e / 4f at the pipe claim.)                 *)
  (* =================================================================== *)

  Lemma init_cons_leaves_pipe :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         UkInit.init_cons_leaves (PS := uprogSG_free) N
           (echo_taint γ) (cons_key r)
           (init_cons_cred (echo_taint γ) r) init_cons_fd).
  Proof using .
    intros Heq.
    assert (HTL : forall v : aview, Timeless (app_pred app_run v)).
    { rewrite Heq. cbn [app_pred app_run]. intro v. apply _. }
    iIntros "#Hinv".
    iDestruct (init_cons_laws_efp_pipe Heq) as "#Hlaws".
    iModIntro. iIntros (N). rewrite /UkInit.init_cons_leaves. iSplit.
    - iApply (init_open_absent_leaf_holds N (echo_taint γ) (cons_key r)
                ltac:(apply _) ltac:(apply _) ltac:(apply _) with "[] Hinv").
      rewrite /init_cons_laws /init_cons_laws_at.
      iDestruct "Hlaws" as "(_ & _ & #Hc & _)". iExact "Hc".
    - iApply (init_mknod_leaf_holds N cons_absent (echo_taint γ)
                (cons_key r) r
                ltac:(apply _) ltac:(apply _) ltac:(apply _) HTL
                with "Hlaws [] Hinv").
      iApply (init_cons_seal_out_pipe N Heq with "Hinv").
  Qed.

  Lemma init_cons_hit_pipe (i0 : Z) :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    cons_made r i0 -∗ app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         □ UkInit.uki_open_console_leaf (PS := uprogSG_free) N
             (echo_taint γ) init_cons_fd
         ∗ □ UkInit.uki_mknod_hit_leaf (PS := uprogSG_free) N
               (echo_taint γ) (init_cons_cred (echo_taint γ) r)
               init_cons_fd).
  Proof using .
    intros Heq.
    assert (HTL : forall v : aview, Timeless (app_pred app_run v)).
    { rewrite Heq. cbn [app_pred app_run]. intro v. apply _. }
    iIntros "#Hm #Hinv".
    iDestruct (init_cons_laws_made_efp_pipe i0 Heq with "Hm") as "#Hlaws".
    iAssert (init_cons_cred (echo_taint γ) r) as "#Hcred".
    { iApply (init_cons_cred_made_pipe i0 with "Hm"). }
    iModIntro. iIntros (N). iSplit.
    - iApply (init_open_console_leaf_holds N (cons_present_at i0)
                (echo_taint γ) (cons_made r i0) r i0
                ltac:(apply _) ltac:(apply _) with "Hlaws Hm Hinv").
    - iModIntro.
      iApply (UkInit.uki_mknod_hit_of_leaf (PS := uprogSG_free) N
                (echo_taint γ) (cons_made r i0)
                (init_cons_cred (echo_taint γ) r) init_cons_fd with "[] Hm").
      iApply (init_mknod_leaf_holds N (cons_present_at i0) (echo_taint γ)
                (cons_made r i0) r
                ltac:(apply _) ltac:(apply _) ltac:(apply _) HTL
                with "Hlaws [] Hinv").
      iIntros "!> #Hm'". iModIntro. rewrite /UkInit.uki_mknod_out. iLeft.
      iSplitR; [| iExact "Hcred"].
      iApply (init_open_console_leaf_holds N (cons_present_at i0)
                (echo_taint γ) (cons_made r i0) r i0
                ltac:(apply _) ltac:(apply _) with "Hlaws Hm Hinv").
  Qed.

  (* ---- SH'S ABSENT ARM: generic in the credential ---- *)
  Lemma sh_cons_absent_pipe (K : iProp Σ) :
    Persistent K -> Timeless K ->
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    UShConsK.sh_cons_never_law (echo_taint γ) K -∗
    app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         UkSh.ush_open_absent_leaf (PS := uprogSG_free) N (echo_taint γ) K).
  Proof using .
    intros HPK HTK Heq. iIntros "#Hlaw #Hinv". iIntros "!>" (N).
    iDestruct (UShConsK.sh_open_absent_leaf_holds N (echo_taint γ) K _ _
                 HPK HTK with "Hlaw Hinv") as "#H".
    iApply "H".
  Qed.

  (* ---- WHAT SH'S CONSOLE ARM IS HANDED ---- *)
  Lemma sh_cons_console_pipe (i : Z) :
    file_app = MkAppcfg echo_names (pipe_pred γ) r ->
    cons_made r i -∗ app_inv fsc_fs -∗
    □ (∀ N : uk_names Σ,
         UkSh.ush_open_console_leaf (PS := uprogSG_free) N (echo_taint γ)).
  Proof using .
    intros Heq. iIntros "#Hmade #Hinv".
    iDestruct (init_cons_laws_efp_pipe Heq) as "#Hlaws".
    iIntros "!>" (N).
    iDestruct (UShConsK.sh_open_console_leaf_holds N (echo_taint γ)
                 (cons_key r) r i _ _ with "Hlaws Hmade Hinv") as "#H".
    iApply "H".
  Qed.

End UInitConsPipe.
