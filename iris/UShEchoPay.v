(* ===================================================================== *)
(*  UShEchoPay.v -- THE SHELL'S FORKED CHILD RUNS /echo ON THE PAID ENTRY  *)
(*  (lane IO-LEAF, step 4, M3b core).                                     *)
(*                                                                       *)
(*  [UShEcho.v] built sh's exec supply at the TRIVIAL payload and the      *)
(*  FREE write law: the child's exit owed nothing and echo's four writes  *)
(*  were paid by the flagged deposit.  Here the same assembly is done at  *)
(*  the payload sh's fork CHOSE ([UkShFork.ushf_wq np]: the era's         *)
(*  credential after echo's block, or the block still owed) and the      *)
(*  credential sh LENT ([Wc np 3], the line's block owed at boundary      *)
(*  [np]), so that echo's bytes go through the era's write link          *)
(*  ([UEchoOut.echo_uexec_slot_at]) and what the child hands back through *)
(*  its exit is the shell's next prompt credential.                      *)
(*                                                                       *)
(*  Terms.  The LEND is what sh's fork hands the child; the REFUND is     *)
(*  what a failed exec hands back ([UkRunExecRef.udepw_at_refR], at the   *)
(*  supplier's own shape: the ledger fragment and the lend, whole).  The  *)
(*  loop's credential family is the TIGHT one ([EchoLinksLine.ewc_lcred]) *)
(*  -- the loose [EchoLinks.ewc_cred] admits a wire the credential cannot *)
(*  re-derive after a child has written (SH-LINE-CRED's finding).         *)
(*                                                                       *)
(*  WHERE THE fd 1 ROW COMES FROM.  echo's paid entry needs the child's   *)
(*  fd 1 to be the console, a fact about the TABLE the exec channel       *)
(*  carries verbatim; the shell's slot carries the row for its own table  *)
(*  ([UkSh.ush_fd1p]) and the child's table is its parent's, so the       *)
(*  supply takes the ledger fragment INTO the deposit, reads the row off  *)
(*  the table's authority there ([UserFd.ustd_agree]), and refunds the    *)
(*  fragment on the failing arm.                                          *)
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
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UexecSlot UexecRet.
Require Import UkRun.
Require Import UserFd.
Require Import ChildTok.
Require Import ElfFile ElfUser.
Require Import FsCfg.             (* [fsc_fs] *)
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeAbi.
Require Import FsImg.
Require Import PinnedExec.
Require Import FsEchoPin.
Require Import SpecKexec SpecSysExec.
Require Import UInitSh.           (* [sbundle_pay_exec_intro_refR] *)
Require Import UShKernel.
Require Import KexecDefs.
Require Import UexecExecInst.
Require Import UCodeEcho.         (* [echo_img_sub] / [echo_data_sub] *)
Require Import UkSh UkShFork UkShEcho.
Require Import UkRunExecRef.      (* [udepw_at_refR] *)
Require Import EchoDisc.
Require Import EchoOut.           (* [era_pin] / [turn] / [ps_lb] *)
Require Import EchoLinks.         (* [echo_links] / [wr_blk] *)
Require Import EchoLinksLine.     (* [ewc_lcred] and the lend's two ends *)
Require Import UEchoOut.          (* [echo_uexec_slot_at] / [ech] / [echo_stage] *)
Require Import UShEcho.           (* the pinned bundle's inputs *)
Require Import UShEchoOut.        (* [echo_out_argv_of_image] *)
Require Import UShPanic.          (* [ush_execfail_law_holds]: the exec-failed diagnostic's law (M4b(2)) *)
Require User.EchoSyms.

(* ECHO'S .rodata IS IN THE EXEC IMAGE, as its text is: the image is the
   text map, the data map and the zero pages, and the two dumped maps
   agree where they meet (a closed computation, the shape of
   [UShKernel.sh_union_comm_bool]), so the data half is the left component
   of the commuted union. *)
Lemma echo_union_comm_bool :
  bool_decide (EchoInstrs.echo_bytes ∪ EchoData.echo_data
               = EchoData.echo_data ∪ EchoInstrs.echo_bytes) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma echo_data_of_elf_image (M : gmap Z (bv 8)) :
  uimg_sub (elf_image ElfUser.echo_elf) M -> echo_data_sub M.
Proof.
  intros H. rewrite ElfUser.echo_elf_image in H.
  apply UShKernel.uimg_sub_union_l in H.
  rewrite (bool_decide_eq_true_1 _ echo_union_comm_bool) in H.
  exact (UShKernel.uimg_sub_union_l _ _ _ H).
Qed.

Section UShEchoPay.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  (* the loop's credential family, at the era's pin *)
  Local Notation Wc := (EchoLinksLine.ewc_lcred T γ (S gen_id)).
  Local Notation Wq := (UkShFork.ushf_wq Wc).

  (* =================================================================== *)
  (*  1.  ECHO'S PAID ENTRY AT THE EXEC CHANNEL                            *)
  (*                                                                      *)
  (*  [UShEcho.echo_slot_of_kexec] at the paid constructor: the exec       *)
  (*  channel's image fact gives every row [UEchoOut.echo_uexec_slot_at]   *)
  (*  asks about the key, the argument vector is the line's two tokens    *)
  (*  ([UShEchoOut.echo_out_argv_of_image]), fd 1 is the console (the     *)
  (*  caller's row, off the table the channel carries verbatim), and the  *)
  (*  lend -- the block owed at [np], pinned -- is exactly the turn bundle *)
  (*  echo's first byte needs.  A TAINTED lend (the era's discipline       *)
  (*  already broken) buys the generic slot instead.                      *)
  (* =================================================================== *)
  Lemma echo_slot_of_kexec_at (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis)
      (v : era_pins) (np : nat) :
    kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
    kexec_sz ElfUser.echo_elf - PGSIZE + 96
      <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
    length sts = NOFILE ->
    uvis_lazy W' = false ->
    na = 3%nat ->
    (forall i : nat, (i < 3)%nat -> alen i = UkShEcho.echo_alen i) ->
    (forall i j : nat, (i < 3)%nat -> (j < UkShEcho.echo_alen i)%nat ->
       afun i j = echo_line !!! (UkShEcho.echo_off i + j)%nat) ->
    UkSh.ush_fd1p (take NSTD sts) ->
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ era_pin γ (S gen_id) v -∗
      echo_links T γ -∗
      udep (PS := uprogSG_free) -∗
      (* the taint's generic slot, at any constant payload *)
      □ (∀ (R : iProp Σ) (W : uvis),
           T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
           □ (riscv_kill_cred -∗ R) -∗ uslot W) -∗
      my_pay (uvis_gen W') (fun _ : Z => Wq np) -∗
      EchoLinksLine.ewc_lpr T v np 3%nat -∗
      uslot W'.
  Proof.
    intros Hok Hroom Hfdl Hlzf Hna Halen Hafun Hfd1 Hkt.
    iIntros "#Hpin #Hlk #Hdep #Hgen Hmp Hc".
    destruct (echo_kexec_pages na alen afun sts W' Hok)
      as (Hpc & Hsub & Hx & Hwr & Hrp).
    destruct (echo_kexec_entry_rows na alen afun sts W' Hok Hroom Hfdl Hwr Hrp)
      as (Hroom96 & Hal8 & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (echo_out_argv_of_image na alen afun sts W' Hok Hna Halen Hafun)
      as Hargv.
    (* the child's fd 1, off the channel's table *)
    assert (Hfd : uvis_fd W' = sts)
      by (destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
    destruct Hfd1 as [rb Hl1]. rewrite <- Hfd in Hl1.
    (* echo's .rodata, off the same image as its text *)
    assert (Hsub2 : echo_data_sub (uvis_M W')).
    { destruct Hok as (_ & _ & _ & _ & _ & Himg & _).
      exact (echo_data_of_elf_image _ Himg). }
    (* THE LEND: the turn bundle at the block's first byte, or the taint *)
    cbn [EchoLinksLine.ewc_lpr].
    iDestruct (EchoLinksLine.ewc_blk_0_lend T v np 0%nat with "Hc")
      as "[Hl | #HT]"; last first.
    { (* a tainted lend: the generic slot, and the kill wand from the taint *)
      iApply ("Hgen" $! (Wq np) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (EchoLinksLine.ewc_lcred_taint T γ (S gen_id) np 0%nat v
                with "Hpin [Hk]").
      iApply Hkt. iModIntro. iExact "Hk". }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct (wr_blk_t_stage ps cs np P Hw) as (Hn0 & HP & Hpin & Htail).
    assert (Hst : echo_stage ps cs np P) by (split_and!; assumption).
    iApply (echo_uexec_slot_at (PS := uprogSG_free) T γ W' v ps cs np P rb
              (fun _ : Z => Wq np)
              ltac:(intros x y; reflexivity)
              Hst Hargv Hl1 Hpc Hsub Hsub2 Hx Hroom96 Hal8 Hstkrow Hargsrow
              Havd Havs Hfdlen Hstop Hlzf
              with "[] Hpin Hlk Hdep Hmp [Htn]").
    - (* THE BLOCK'S END PAYS THE EXIT: twelve bytes on, the choice filed,
         the credential is the shell's next prompt's *)
      iIntros "!> Hc". rewrite /UkShFork.ushf_wq. iRight.
      iApply (EchoLinksLine.ewc_lcred_of_post T γ (S gen_id) np v with "Hpin").
      iApply (EchoLinksLine.ewc_post_of_ech T v ps cs np P Hn0 HP Hpin Htail).
      iEval (rewrite /ech; cbn [echcs]) in "Hc". iExact "Hc".
    - (* ...and its first byte is where the lend stands *)
      rewrite /ech. cbn [echcs]. rewrite Nat.add_0_r.
      iLeft. iFrame "Htn Hps Hcs HE".
  Qed.

  (* =================================================================== *)
  (*  2.  THE ASSEMBLY: sh's pinned bundle pays its exec supply, PAID      *)
  (*                                                                      *)
  (*  [UShEcho]'s section 7 at the paid entry: the resolving arm is       *)
  (*  [echo_slot_of_kexec_at], the taint arm the generic slot at the       *)
  (*  chosen payload, the deposit's refund the ledger fragment and the     *)
  (*  lend ([UInitSh.sbundle_pay_exec_intro_refR]).                        *)
  (* =================================================================== *)
  Lemma sh_exec_sup_echo_wq_holds :
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ echo_links T γ -∗ udep (PS := uprogSG_free) -∗ sh_echo_slot T -∗
      UkShEcho.sh_exec_sup_echo_wq Wc.
  Proof.
    intros Hkt.
    iIntros "#Hlk #Hdep (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_wq. iIntros "!>" (np).
    rewrite /UkShEcho.sh_exec_sup_echo.
    iIntros "!>" (N' m pc s0 t g ld) "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    rewrite /udepw_at_refR. iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd".
    (* the node, read ONCE off the lent heap *)
    iAssert (⌜ echo_node_img M s0 t g ⌝)%I as %Himg.
    { iApply (echo_node_img_of_cmd with "Hheap Hcmd"). }
    (* ...the table's length, and sh's fd 1 row AT THE TABLE, off the lent
       authority against the fragment *)
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    assert (Hfd1' : UkSh.ush_fd1p (take NSTD fdv)) by (rewrite Hl; exact Hfd1).
    iFrame "Hheap Hufd".
    (* the lend, pinned *)
    rewrite /EchoLinksLine.ewc_lcred. iDestruct "Hcr" as (v) "[#Hpin Hcr]".
    (* ---- THE RESOLVING ARM: echo's paid entry, at the pinned image ---- *)
    iAssert (□ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
                  (W' : uvis),
                  ⌜kexec_image_ok ElfUser.echo_elf na alen afun fdv W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  (* the two identity rows (lane EXEC-SEAM): echo reads
                     neither *)
                  ⌜uvis_ch W' = cs⌝ -∗
                  ⌜uvis_pid W' = pidv⌝ -∗
                  ⌜exec_args_of M (mword_of_int (t + 8) : mword 64)
                     na alen afun⌝ -∗
                  my_pay (uvis_gen W') (fun _ : Z => Wq np) -∗
                  (UserFd.ustd (ukn_fd N') ld
                   ∗ EchoLinksLine.ewc_lpr T v np 3%nat) -∗
                  uslot W'))%I as "#Hcon".
    { iModIntro.
      iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf _ _ %Hargs Hmp [_ Hc]".
      destruct (echo_args_det_holds M s0 t g na alen afun Himg Hbytes Hargs)
        as (Hna & Halen & Hafun).
      iApply (echo_slot_of_kexec_at na alen afun fdv W' v np Hok
                ltac:(subst na;
                      exact (echo_room alen (Halen 0%nat ltac:(lia))
                               (Halen 1%nat ltac:(lia)) (Halen 2%nat ltac:(lia))))
                Hlen Hlzf Hna Halen Hafun Hfd1' Hkt
                with "Hpin Hlk Hdep Hgen Hmp Hc"). }
    (* ---- THE TAINT ARM: the generic slot at the chosen payload ---- *)
    iAssert (□ (∀ W' : uvis, T -∗
                  my_pay (uvis_gen W') (fun _ : Z => Wq np) -∗
                  uslot W'))%I as "#Hgen'".
    { iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (Wq np) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (EchoLinksLine.ewc_lcred_taint T γ (S gen_id) np 0%nat v
                with "Hpin [Hk]").
      iApply Hkt. iModIntro. iExact "Hk". }
    (* ---- THE BUNDLE ---- *)
    iDestruct (pinned_exec_bundle fsc_fs uslot FsEchoPin.era0_echo_pins T
                 FsImg.ROOTINO echo_pl
                 [FsImg.ROOTINO; FsEchoPin.ECHO_INO] FsEchoPin.ECHO_INO
                 ElfUser.echo_elf 1%nat
                 (UserFd.ustd (ukn_fd N') ld
                  ∗ EchoLinksLine.ewc_lpr T v np 3%nat)%I
                 (fun _ : Z => Wq np)
                 M (mword_of_int s0) (mword_of_int (t + 8)) fdv cs pidv
                 sh_echo_pin_resolves echo_elf_loadable
                 (sh_echo_path_of_holds M s0 t g Himg Hbytes)
                 with "Hcl Hinv Hcon Hgen' [Hstd Hcr]") as (P Pmiss Fo) "Hb";
      [ iFrame "Hstd Hcr" | ].
    assert (Ea0 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv
                                  FsImg.ROOTINO gn cs pidv false))
                    (tf_arg_idx 0) = (mword_of_int s0 : mword 64))
      by (etransitivity; [ exact (tf_of_arg0 m pc) | exact Ha0 ]).
    assert (Ea1 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv
                                  FsImg.ROOTINO gn cs pidv false))
                    (tf_arg_idx 1) = (mword_of_int (t + 8) : mword 64))
      by (etransitivity; [ exact (tf_of_arg1 m pc) | exact Ha1 ]).
    (* THE REFUND IS THE LEND, WHOLE: the fragment and the block credential
       come back to the child whose exec failed *)
    iApply (sbundle_pay_exec_intro_refR uslot
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false)
              (ukn_pay N') (UserFd.ustd (ukn_fd N') ld ∗ Wc np 3%nat)
              P Pmiss Fo
              (UserFd.ustd (ukn_fd N') ld
               ∗ EchoLinksLine.ewc_lpr T v np 3%nat)%I).
    { iIntros "!> [$ Hc]". rewrite /EchoLinksLine.ewc_lcred.
      iExists v. iFrame "Hpin Hc". }
    { cbn [uvis_gen uvis_of_run]. iExact "Hmpay". }
    rewrite Hpeq Ea0 Ea1. iExact "Hb".
  Qed.

  (* =================================================================== *)
  (*  3.  THE BODY'S TWO LAWS AT THE TIGHT FAMILY -- the witnesses         *)
  (* =================================================================== *)
  (* a killed child pays the credential with the taint, at any pin *)
  Lemma ushf_kill_law_holds (v : era_pins) :
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ era_pin γ (S gen_id) v -∗ UkShFork.ushf_kill_law Wc.
  Proof.
    intros Hkt. iIntros "#Hpin". rewrite /UkShFork.ushf_kill_law.
    iIntros "!>" (n) "#Hk".
    iApply (EchoLinksLine.ewc_lcred_taint T γ (S gen_id) n 0%nat v
              with "Hpin [Hk]").
    iApply Hkt. iModIntro. iExact "Hk".
  Qed.

  (* ...and the paid child's walk, out of the supply above: the closed form
     that says the composition exists *)
  Lemma ushf_child_law_holds_at :
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ echo_links T γ -∗ udep (PS := uprogSG_free) -∗ sh_echo_slot T -∗
      UkShFork.ushf_child_law (PS := uprogSG_free) Wc.
  Proof.
    intros Hkt. iIntros "#Hlk #Hdep #Hslot".
    (* at [uprogSG_free] the numbers sh admits are the free ones: the
       hypothesis is the identity *)
    (* the two laws first, as named hypotheses: an [iApply ... with "[] []"]
       here sends the [Persistent] search down the child law's wand chain
       (durable-notes, "iIntros #H on a bundle of wands") *)
    iPoseProof (sh_exec_sup_echo_wq_holds Hkt with "Hlk Hdep Hslot") as "Hsup".
    (* ...PINNED at [uprogSG_free] on both sides (durable-notes, "instance
       pinning"): left to instance search the assertion lands at another
       [uprogSG] and the [iApply] below unfolds the child law trying to
       make the two agree, and never returns *)
    iAssert (UkShEcho.ush_execfail_law_wq (PS := uprogSG_free) Wc) as "Hxlw".
    { (* the exec-failed diagnostic's law, at every boundary (M4b(2)) *)
      rewrite /UkShEcho.ush_execfail_law_wq. iIntros "!>" (np).
      iApply (UShPanic.ush_execfail_law_holds (PS := uprogSG_free) T γ np
                with "Hlk"). }
    iApply (UkShEcho.ushf_child_law_holds (PS := uprogSG_free) (fun k H => H) Wc
              with "Hxlw Hsup").
  Qed.

End UShEchoPay.
