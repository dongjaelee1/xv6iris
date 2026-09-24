(* ===================================================================== *)
(* UkPipeEntries.v -- THE PIPELINE APPLICATION'S TWO ENTRIES FROM THE    *)
(* TREE ROUTE (program-specs SS3.4e, cut 5 lane F): cat at the pipe and  *)
(* echo at the pipe, each an [ExecEntry.image_entry] proved from          *)
(* [UkTreeEntry.cat_image_entry_env_c] / [echo_image_entry_env_c] at the *)
(* pipeline's instance [UkPipeIface.pipe_iface], BESIDE the landed        *)
(* entries ([UShCatPay.cat_image_entry_1w], [UEchoPipe.ep_image_entry]); *)
(* no assembly is repointed and no landed lemma moves.                    *)
(*                                                                        *)
(* THE INSTANCE AT EVERY MINTED RECORD.  The entry mints the process's    *)
(* record [N'] inside, so the interface is a function of [N'] and of the  *)
(* payload equation [ukn_pay N' = Q] (the [_c] entries): the equation at *)
(* a constant [Q] is the [ukn_const N'] the instance's free handler needs *)
(* ([UkRun.ukn_const_of_eq]).  The five stubs are [UkStub]'s at cat's and *)
(* echo's code; the four fields the kernel refuses                        *)
(* ([UkPipeIface.pif_refused]) are this section's two hypotheses, one per *)
(* program, quantified over the minted record.                            *)
(*                                                                        *)
(* WHAT THE STATEMENTS ADD TO THE LANDED ONES:                            *)
(*   - the REGISTRY: [ei_fds] holds the registry's pool                   *)
(*     [own greg (pif_pool empty w)], which only a caller can allocate    *)
(*     (the entry's environment wand has no update), so it rides in the  *)
(*     entry's [Pay] beside the landed lend;                              *)
(*   - the round's context (the family's ghosts, the pins, the two        *)
(*     witnesses) as section variables: the instance is ONE record over  *)
(*     the pipeline's devices, so echo's entry names the round too;       *)
(*   - cat: the landed entry's argv reading ([UkShCat.cat_argv_bytes] at  *)
(*     the token [(a, b)]) is bridged to the tree entry's word-list       *)
(*     reading at [[cmd_cat]] ([pe_cat_1w_args]), which needs the node's  *)
(*     two addresses under [2 ^ 38] (the landed reading bounds them by    *)
(*     the machine word only); the descriptor rows the copy device is     *)
(*     built at (fd 0 the read end, fds 1, 2 the console), the pool's two *)
(*     kinds, the line nonempty and under [2 ^ 31]; the payment is the    *)
(*     round's [UShPipeLaw.pl_RcR] with the continuation                  *)
(*     [pl_Cend * side_R -* Q (-1)] ([UShPipeLaw.pl_qc_of_cend]'s shape)  *)
(*     and the era pin and the link taint, both persistent;               *)
(*   - echo: the line [L] is the round's, equal to the words' line, and   *)
(*     the pool's device 0 is the write end.                              *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra Require Import functions.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UkRun UkRunSys.
Require Import UCodeEcho UCodeCat.
Require User.EchoSyms User.CatSyms.
Require Import FdSlots ProcGeom UserFd UserCwd UserHeap.
Require Import UexecSG UexecSlot UexecRet.
Require Import UexecExecInst.
Require Import ConsoleInv.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import LineWords LineBytes EchoDisc ExecWords.
Require Import EchoOut AppEcho.
Require Import PipeDisc.
Require Import PipeOutPure PipeOut.
Require Import PipeBothPure PipeBoth.
Require Import PipeNames PipeProto.
Require Import PipeLinks.
Require Import UShPipeRound2.
Require Import AppCfg AppInv AppPipeClaim.
Require Import CtxIdDefs.
Require Import ExecArgs ExecEntry.
Require Import ElfUser.
Require Import ProgTree UkTree UkStub.
Require Import UkEchoTree UkCatTree.
Require Import UkHandler.
Require Import UkShMain UkShEcho UShEcho UkShCat.
Require Import UkTreeEntry.
Require Import UEchoPipe.
Require Import UkPipeIface.
Require Import UShPipeLaw.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  1.  THE PURE BRIDGES                                                  *)
(* ===================================================================== *)

(* the protected-device list of an [ep_iface] is empty *)
Lemma pe_dp_nil (ds : gset nat) : dp_in [] ds.
Proof using . intros d Hd. by apply elem_of_nil in Hd. Qed.

(* the words' line after the command fits a C int *)
Lemma pe_line_len (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> Z.of_nat (length (wl_line (drop 1 ws))) < 2 ^ 31.
Proof using .
  intros Hok. pose proof (EchoDisc.line_ok_len ws Hok) as Hl.
  unfold EchoDisc.line_max in Hl.
  assert (Hcons : forall (w : list (bv 8)) (r : list (list (bv 8))),
             (length (wl_line r) <= length (wl_line (w :: r)))%nat).
  { intros w r. rewrite !wl_line_length wl_body_cons length_app.
    destruct r as [| w' r'].
    - cbn. lia.
    - rewrite wl_tail_cons. cbn [length]. lia. }
  assert (Hle : (length (wl_line (drop 1 ws)) <= length (wl_line ws))%nat).
  { destruct ws as [| w r]; [reflexivity |].
    replace (drop 1 (w :: r)) with r by reflexivity. apply Hcons. }
  lia.
Qed.

Lemma pe_drop1_ne (ws : list (list (bv 8))) :
  EchoDisc.line_ok ws -> drop 1 ws <> [].
Proof using .
  intros Hok Hd. pose proof (EchoDisc.line_ok_ge2 ws Hok) as H2.
  apply (f_equal length) in Hd. rewrite length_drop in Hd. cbn in Hd. lia.
Qed.

(* THE LANDED CAT ENTRY'S ARGV, READ AS THE TREE ENTRY'S: the token
   [(a, b)] of sh's node is the one-word line [[cmd_cat]] at the string's
   own address.  The word-list reading bounds the node's two addresses by
   [2 ^ 38]; the landed one by the machine word, so the bound is a premise. *)
Lemma pe_cat_1w_args (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z)
    (gn : nat -> bv 8) :
  0 < t < 2 ^ 38 ->
  0 < sv + Z.of_nat a < 2 ^ 38 ->
  UkShCat.cat_argv_bytes a b gn ->
  uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
  exec_ok [UkShCat.cmd_cat]
  /\ UShEcho.echo_node_img [UkShCat.cmd_cat] Mn (sv + Z.of_nat a) t
       (fun j : nat => gn (a + j)%nat)
  /\ UkShEcho.echo_argv_bytes [UkShCat.cmd_cat] (fun j : nat => gn (a + j)%nat).
Proof using .
  intros Ht Hs Hbytes Himg.
  pose proof (UkShCat.cat_argv_bytes_end a b gn Hbytes) as Hb3.
  destruct Hbytes as (_ & Hin & Hnul).
  rewrite UkShCat.cmd_cat_len in Hin.
  pose proof (UkShCat.cat_cmd_args_lookup a b sv gn Hb3) as Hlk.
  destruct Himg as (_ & _ & _ & Hptr & Hterm & Hrow).
  assert (Hoff : UkShEcho.echo_off [UkShCat.cmd_cat] 0 = 0%nat) by reflexivity.
  assert (Halen : UkShEcho.echo_alen [UkShCat.cmd_cat] 0 = 3%nat)
    by exact UkShCat.cmd_cat_len.
  split_and!.
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - rewrite /UShEcho.echo_node_img. cbn [length]. split_and!.
    + lia.
    + lia.
    + intros i Hi. assert (i = 0%nat) as -> by lia. rewrite Hoff. lia.
    + intros i Hi k Hk. assert (i = 0%nat) as -> by lia. rewrite Hoff.
      pose proof (Hptr 0%nat _ Hlk k Hk) as Hp.
      cbn [UserHeap.ua_ptr] in Hp. revert Hp.
      match goal with |- ?l1 = ?r1 -> ?l2 = ?r2 =>
        assert (El : l1 = l2) by (f_equal; lia);
        assert (Er : r1 = r2) by (f_equal; f_equal; lia) end.
      intros Hp. congruence.
    + intros k Hk. pose proof (Hterm k Hk) as Hp.
      rewrite UkShMain.ush_args_length in Hp. exact Hp.
    + intros i Hi j Hj. assert (i = 0%nat) as -> by lia.
      rewrite Halen in Hj. rewrite ?Hoff.
      pose proof (Hrow 0%nat _ Hlk j ltac:(cbn [UserHeap.ua_len]; lia)) as Hp.
      cbn [UserHeap.ua_ptr UserHeap.ua_bytes] in Hp. revert Hp.
      match goal with |- ?l1 = ?r1 -> ?l2 = ?r2 =>
        assert (El : l1 = l2) by (f_equal; lia);
        assert (Er : r1 = r2) by (f_equal; f_equal; lia) end.
      intros Hp. congruence.
    + intros i Hi. assert (i = 0%nat) as -> by lia. rewrite ?Hoff ?Halen.
      pose proof (Hrow 0%nat _ Hlk 3%nat ltac:(cbn [UserHeap.ua_len]; lia)) as Hp.
      cbn [UserHeap.ua_ptr UserHeap.ua_bytes] in Hp.
      rewrite <- Hnul, Hb3. revert Hp.
      match goal with |- ?l1 = ?r1 -> ?l2 = ?r2 =>
        assert (El : l1 = l2) by (f_equal; lia);
        assert (Er : r1 = r2) by (f_equal; f_equal; lia) end.
      intros Hp. congruence.
  - split.
    + intros i j Hi Hj. cbn [length] in Hi. assert (i = 0%nat) as -> by lia.
      rewrite Halen in Hj. rewrite ?Hoff. cbn [Nat.add].
      rewrite (Hin j Hj).
      do 3 (destruct j as [| j]; [reflexivity |]). lia.
    + intros i Hi. cbn [length] in Hi. assert (i = 0%nat) as -> by lia.
      rewrite ?Hoff ?Halen. cbn [Nat.add]. rewrite <- Hb3. exact Hnul.
Qed.

(* ===================================================================== *)
(*  2.  THE INSTANCE AT THE MINTED RECORD, AND THE TWO ENTRIES            *)
(* ===================================================================== *)

Section UkPipeEntries.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z))}.
  Context `{!pipeOutG Σ, !pipeProtoG Σ, !pifRegG Σ}.
  Context `{PS : UexecSG.uprogSG Σ}.

  (* the pipeline application *)
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HRg) = pecl g).
  Context (Hkill : @app_taint Σ (@riscv_fixedGS Σ HRg) = echo_taint γ).
  Context (r : echo_names).
  Context (Heq : file_app = MkAppcfg echo_names (pipe_pred γ) r).

  (* THE ROUND, at the family's facts the round itself uses
     ([UShPipeLaw.pl_XL] / [pl_YR]) *)
  Context (v : era_pins) (I L : list (bv 8)) (gL gR gM : gname).
  Context (Hnd : Forall nodollar L).
  Context (Hwit2 : forall sel : list bool,
             sel_wf2 dg_execR sel -> pblk2_wit I dg_execR sel).
  Context (Hwit1 : forall sel : list bool,
             count_true sel = 0%nat -> (length sel <= length L)%nat ->
             pblk2_wit I L sel).
  Context (pn : pnames) (γp : pipe_names).
  Context (γreg : gname).

  Local Notation XL := (pl_XL pn).
  Local Notation YR := (pl_YR pn L).

  Lemma pe_yr : pws_lb pn (take 1%nat L) ⊢ YR.
  Proof using . rewrite /pl_YR. reflexivity. Qed.

  (* THE REFUSED FIELDS at every minted record, one per program *)
  Hypothesis Href_cat : forall N' : uk_names Σ,
    pif_refused g v I L gL gR gM XL YR pn γp N' (cat_prog N') γreg.
  Hypothesis Href_echo : forall N' : uk_names Σ,
    pif_refused g v I L gL gR gM XL YR pn γp N' (echo_prog N') γreg.

  Local Instance pe_cat_code_persistent (N' : uk_names Σ) :
    Persistent (up_code (cat_prog N')).
  Proof using . simpl. apply _. Qed.
  Local Instance pe_echo_code_persistent (N' : uk_names Σ) :
    Persistent (up_code (echo_prog N')).
  Proof using . simpl. apply _. Qed.

  Definition pe_iface_cat (N' : uk_names Σ) (HNc : ukn_const N') :
      ep_iface N' (cat_prog N') :=
    pipe_iface g Hcons Hkill v I L gL gR gM XL YR Hnd Hwit2 Hwit1 pn γp pe_yr
      N' (cat_prog N') (HNc := HNc)
      (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
      (cat_stub_close N') (cat_stub_exit N') γreg
      (proj1 (Href_cat N')) (proj1 (proj2 (Href_cat N')))
      (proj1 (proj2 (proj2 (Href_cat N')))) (proj2 (proj2 (proj2 (Href_cat N')))).

  Definition pe_iface_echo (N' : uk_names Σ) (HNc : ukn_const N') :
      ep_iface N' (echo_prog N') :=
    pipe_iface g Hcons Hkill v I L gL gR gM XL YR Hnd Hwit2 Hwit1 pn γp pe_yr
      N' (echo_prog N') (HNc := HNc)
      (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
      (echo_stub_close N') (echo_stub_exit N') γreg
      (proj1 (Href_echo N')) (proj1 (proj2 (Href_echo N')))
      (proj1 (proj2 (proj2 (Href_echo N')))) (proj2 (proj2 (proj2 (Href_echo N')))).

  (* ------------------------------------------------------------------- *)
  (*  2a. CAT AT THE PIPE: [UShCatPay.cat_image_entry_1w]'s statement,    *)
  (*      the payment the round's [pl_RcR] with the pool                  *)
  (* ------------------------------------------------------------------- *)
  Lemma pe_cat_image_entry (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) (sts : list fdstate) (cw : Z) (cs : gset gname)
      (pidv : mword 32) (Q : Z -> iProp Σ)
      (w : nat -> pdev) (wb rb1 rb2 : bool) :
    (forall x y : Z, Q x = Q y) ->
    0 < t < 2 ^ 38 ->
    0 < sv + Z.of_nat a < 2 ^ 38 ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    length sts = NOFILE ->
    take NSTD sts !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    take NSTD sts !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    w 0%nat = PDMute -> w 1%nat = PDCopy ->
    L <> [] -> Z.of_nat (length L) < 2 ^ 31 ->
    era_pin γ (S gen_id) v -∗ pipe_link_taint g -∗
    □ (pl_Cend g pn L gR gM ∗ side_R pn -∗ Q (-1)) -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q (pl_RcR g v I L pn gL gR gM γp ∗ own γreg (pif_pool ∅ w)) uslot.
  Proof using Hcons Hkill Heq Hnd Hwit1 Hwit2 Href_cat.
    intros HQc Ht Hs Hbytes Himg Hfdl Hl0 Hl1 Hl2 Hw0 Hw1 HLne HL.
    destruct (pe_cat_1w_args a b Mn sv t gn Ht Hs Hbytes Himg)
      as (Hok & Hnode & Hab).
    iIntros "#Hpin #Hlt #Hq #Hnpw #Hdep".
    iApply (cat_image_entry_env_c [UkShCat.cmd_cat] Mn (sv + Z.of_nat a) t
              (fun j : nat => gn (a + j)%nat) sts cw cs pidv Q
              (pl_RcR g v I L pn gL gR gM γp ∗ own γreg (pif_pool ∅ w))%I
              (fun N' Hpq => pe_iface_cat N' (ukn_const_of_eq N' Q Hpq HQc))
              (copy_env (DCopy false L []) [[]] (fun _ => None) []) {[0%nat; 1%nat]}
              Hok Hnode Hab Hfdl
              (cat_copy_conforms false L [[]] (fun _ => None) []
                 ltac:(apply elem_of_list_singleton; reflexivity)
                 ltac:(intros Hf; discriminate Hf))
              (cat_tree_safe _ _) (pe_dp_nil _)
              with "[] Hnpw Hdep").
    iIntros "!>" (N' Hpq) "Hstd _ [Hrc Hpool]".
    rewrite /pl_RcR. iDestruct "Hrc" as "(#Hblk & #Hpi & Hrt & HsR & HgR & HgM)".
    iDestruct (pipe_excl_wtok_lb_pipeN pn γp L HLne with "Hpi") as "#Hex".
    rewrite /pe_iface_cat.
    iApply (copy_env_res g Hcons Hkill r Heq v I L gL gR gM XL YR Hnd Hwit2 Hwit1
              pn γp pe_yr N' (cat_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
              (cat_stub_read N') (cat_stub_write N') (cat_stub_open N')
              (cat_stub_close N') (cat_stub_exit N') γreg
              (proj1 (Href_cat N')) (proj1 (proj2 (Href_cat N')))
              (proj1 (proj2 (proj2 (Href_cat N')))) (proj2 (proj2 (proj2 (Href_cat N'))))
              (take NSTD sts) wb rb1 rb2 w (fun _ => None)
              Hw0 Hw1 Hl0 Hl1 Hl2 HL
              with "Hstd Hpool [HsR] Hpi Hrt Hpin Hlt Hblk Hex HgR HgM").
    iIntros "Hce". rewrite Hpq. iApply "Hq". iFrame "HsR". iExact "Hce".
  Qed.

  (* ...AND AT THE ROUND'S OWN PAYLOAD: the continuation is
     [UShPipeLaw.pl_qc_of_cend] *)
  Lemma pe_cat_image_entry_qc (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) (sts : list fdstate) (cw : Z) (cs : gset gname)
      (pidv : mword 32) (w : nat -> pdev) (wb rb1 rb2 : bool) :
    0 < t < 2 ^ 38 ->
    0 < sv + Z.of_nat a < 2 ^ 38 ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    length sts = NOFILE ->
    take NSTD sts !! 0%nat = Some (FdOpen true wb (FdPipe γp)) ->
    take NSTD sts !! 1%nat = Some (FdOpen rb1 true (FdDevice CONSOLE)) ->
    take NSTD sts !! 2%nat = Some (FdOpen rb2 true (FdDevice CONSOLE)) ->
    w 0%nat = PDMute -> w 1%nat = PDCopy ->
    L <> [] -> Z.of_nat (length L) < 2 ^ 31 ->
    era_pin γ (S gen_id) v -∗ pipe_link_taint g -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM)
      (pl_RcR g v I L pn gL gR gM γp ∗ own γreg (pif_pool ∅ w)) uslot.
  Proof using Hcons Hkill Heq Hnd Hwit1 Hwit2 Href_cat.
    intros Ht Hs Hbytes Himg Hfdl Hl0 Hl1 Hl2 Hw0 Hw1 HLne HL.
    iIntros "#Hpin #Hlt #Hnpw #Hdep".
    iApply (pe_cat_image_entry a b Mn sv t gn sts cw cs pidv
              (fun _ : Z => UShPipeAssembly.pipe_Qc_at g pn L gL gR gM) w wb rb1 rb2
              (fun x y => eq_refl) Ht Hs Hbytes Himg Hfdl Hl0 Hl1 Hl2 Hw0 Hw1 HLne HL
              with "Hpin Hlt [] Hnpw Hdep").
    iIntros "!> H". iApply (pl_qc_of_cend g pn L gL gR gM with "H").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  2b. ECHO AT THE PIPE: [UEchoPipe.ep_image_entry]'s statement, the   *)
  (*      exit through the LEFT wand ([UkPipeIface.pif_exit_k_left]) fed  *)
  (*      by the landed box with the frame [side_L * Wq] captured         *)
  (* ------------------------------------------------------------------- *)
  Lemma pe_echo_image_entry (Wq : iProp Σ) (ws : list (list (bv 8)))
      (M : gmap Z (bv 8)) (s0 t : Z) (gb : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32) (rb : bool)
      (Q : Z -> iProp Σ) (w : nat -> pdev) :
    (forall x y : Z, Q x = Q y) ->
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t gb ->
    UkShEcho.echo_argv_bytes ws gb ->
    length sts = NOFILE ->
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdPipe γp)) ->
    L = wl_line (drop 1 ws) ->
    w 0%nat = PDWr ->
    □ (ep_exit Wq pn (wl_line (drop 1 ws)) -∗ Q (-1)) -∗
    UkRun.urun_nopipe sts -∗
    udep -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q
      (ep_pay Wq pn γp (wl_line (drop 1 ws)) ∗ own γreg (pif_pool ∅ w)) uslot.
  Proof using Hcons Hkill Heq Hnd Hwit1 Hwit2 Href_echo.
    intros HQc Hok Hnode Hab Hfdl Hl1 HLw Hw0.
    assert (HL : Z.of_nat (length L) < 2 ^ 31)
      by (rewrite HLw; exact (pe_line_len ws Hok)).
    assert (Hc : conforms (pipe_env (DOutH [L]) (fun _ => None)) (echo_tree ws)).
    { rewrite HLw. exact (echo_pipe_conforms ws _ (pe_drop1_ne ws Hok)). }
    rewrite -HLw.
    iIntros "#Hq #Hnpw #Hdep".
    iApply (echo_image_entry_env_c ws M s0 t gb sts cw cs pidv Q
              (ep_pay Wq pn γp L ∗ own γreg (pif_pool ∅ w))%I
              (fun N' Hpq => pe_iface_echo N' (ukn_const_of_eq N' Q Hpq HQc))
              (pipe_env (DOutH [L]) (fun _ => None)) {[0%nat]}
              Hok Hnode Hab Hfdl Hc (echo_tree_safe _ _) (pe_dp_nil _)
              with "[] Hnpw Hdep").
    iIntros "!>" (N' Hpq) "Hstd _ [Hpay Hpool]".
    rewrite /ep_pay. iDestruct "Hpay" as "(#Hpi & Hfr & Hw & Hlb)".
    rewrite /pe_iface_echo.
    iApply (echo_env_res_k g Hcons Hkill r Heq v I L gL gR gM XL YR Hnd Hwit2 Hwit1
              pn γp pe_yr N' (echo_prog N') (HNc := ukn_const_of_eq N' Q Hpq HQc)
              (echo_stub_read N') (echo_stub_write N') (echo_stub_open N')
              (echo_stub_close N') (echo_stub_exit N') γreg
              (proj1 (Href_echo N')) (proj1 (proj2 (Href_echo N')))
              (proj1 (proj2 (proj2 (Href_echo N')))) (proj2 (proj2 (proj2 (Href_echo N'))))
              (take NSTD sts) rb w (fun _ => None) Hw0 Hl1 HL
              with "Hstd [Hfr] Hpool Hpi Hw Hlb").
    iApply (pif_kpay_left g L gR gM pn N' _ 0%nat (lookup_singleton _ _)).
    iApply (pif_exit_k_left_of g Hkill L pn N').
    iIntros "Hle". rewrite Hpq. iApply "Hq".
    rewrite /ep_exit /ep_car /ep_frame. iFrame "Hfr".
    rewrite /ep_ok /ep_halt /ep_stuck /ep_cur /pif_lexit. iExact "Hle".
  Qed.

End UkPipeEntries.
