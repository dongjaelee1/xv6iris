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
(*  The four bundles below are exactly [UInitConsFile]'s 4a-4c.  What is  *)
(*  NOT here is [UInitConsFile]'s 4d/4e -- the LEAVES ([UkInit.           *)
(*  init_cons_leaves]) -- and the reason is reported in the lane's        *)
(*  findings: they need [init_cons_seal_out], whose pipe instance wants a *)
(*  console-seal step at the pipeline record's own interface equation,    *)
(*  which is PIPE-ADEQUACY's literal and not this lane's.                 *)
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
Require Import FsAbsDelta.
Require Import FsTree.
Require Import FsImg.
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
Require Import UInitCons.
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

End UInitConsPipe.
