(* ===================================================================== *)
(*  UShEchoPay.v -- THE SHELL'S FORKED CHILD RUNS /echo ON THE PAID ENTRY  *)
(*  (lane IO-LEAF, step 4, M3b core).                                     *)
(*                                                                       *)
(*  [UShEcho.v] built sh's exec supply at the TRIVIAL payload and the      *)
(*  FREE write law: the child's exit owed nothing and echo's four writes  *)
(*  were paid by the flagged deposit.  Here the same assembly is done at  *)
(*  the payload sh's fork CHOSE ([UkShFork.ushf_wq I]: the era's          *)
(*  credential after echo's block, or the block still owed) and the      *)
(*  credential sh LENT ([Wc I 3], the line's block owed at the era's      *)
(*  input [I]), so that echo's bytes go through the era's write link      *)
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
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeAbi.
Require Import FsImg.
Require Import FsEchoPin.
Require Import SpecKexec.
Require Import ExecEntry.         (* [image_entry] / [image_entry_taint] *)
Require Import FsAbsDefs.         (* [anode] / [MkAnode] / [AFile] *)
Require Import ExecRun.           (* THE U-TIER EXEC RULE this supply is an
                                     instance of *)
Require Import UShKernel.
Require Import KexecDefs.
Require Import UexecExecInst.
Require Import UCodeEcho.         (* [echo_img_sub] / [echo_data_sub] *)
Require Import UkSh UkShFork UkShEcho.
Require Import LineWords.         (* [last_ws] / [wl_line_pos] *)
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
  (*  lend -- the block owed at [I], pinned -- is exactly the turn bundle  *)
  (*  echo's first byte needs.  A TAINTED lend (the era's discipline       *)
  (*  already broken) buys the generic slot instead.                      *)
  (* =================================================================== *)
  Lemma echo_slot_of_kexec_at (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) (sts : list fdstate) (W' : uvis)
      (v : era_pins) (I : list (bv 8)) :
    line_ok (last_ws I) ->
    kexec_image_ok ElfUser.echo_elf na alen afun sts W' ->
    kexec_sz ElfUser.echo_elf - PGSIZE + 96
      <= kxc_sp_final (kexec_sz ElfUser.echo_elf) alen na ->
    length sts = NOFILE ->
    (* ...and the exec'ing process's table is all parked (lane OFF-HAND-3,
       R1) -- [UShEcho.echo_slot_of_kexec]'s note *)
    fdv_all_parked sts ->
    uvis_lazy W' = false ->
    na = length (last_ws I) ->
    (forall i : nat, (i < length (last_ws I))%nat ->
       alen i = UkShEcho.echo_alen (last_ws I) i) ->
    (forall i j : nat, (i < length (last_ws I))%nat ->
       (j < UkShEcho.echo_alen (last_ws I) i)%nat ->
       afun i j
       = wl_line (last_ws I)
           !!! (UkShEcho.echo_off (last_ws I) i + j)%nat) ->
    UkSh.ush_fd1p (take NSTD sts) ->
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ era_pin γ (S gen_id) v -∗
      echo_links T γ -∗
      (* ...and whether the exec'ing process's table held a pipe row
         (design/pipe.md, "The exit path"): echo's table IS sh's
         ([SpecKexec.kexec_image_ok_fd]), echo's run carries the fact, and
         echo's exit leaf mints the tear-down's bundle row off it. *)
      UkRun.urun_nopipe sts -∗
      udep (PS := uprogSG_free) -∗
      (* the taint's generic slot, at any constant payload *)
      □ (∀ (R : iProp Σ) (W : uvis),
           T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
           □ (riscv_kill_cred -∗ R) -∗ uslot W) -∗
      my_pay (uvis_gen W') (fun _ : Z => Wq I) -∗
      EchoLinksLine.ewc_lpr T v I 3%nat -∗
      uslot W'.
  Proof using HPT ghost_varG0 ghost_varG1 ufdG0.
    intros Hokws Hok Hroom Hfdl Hpark Hlzf Hna Halen Hafun Hfd1 Hkt.
    iIntros "#Hpin #Hlk #Hnpw #Hdep #Hgen Hmp Hc".
    destruct (echo_kexec_pages na alen afun sts W' Hok)
      as (Hpc & Hsub & Hx & Hwr & Hrp).
    destruct (echo_kexec_entry_rows na alen afun sts W' Hok Hroom Hfdl Hwr Hrp)
      as (Hroom96 & Hal8 & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (echo_out_argv_of_image (last_ws I) na alen afun sts W'
                  Hokws Hok Hna Halen Hafun) as Hargv.
    (* the child's fd 1, off the channel's table *)
    assert (Hfd : uvis_fd W' = sts)
      by (destruct Hok as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
    destruct Hfd1 as [rb Hl1]. rewrite <- Hfd in Hl1.
    (* ...and the table fact at the RESUMED key, by the same equation *)
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    (* echo's .rodata, off the same image as its text *)
    assert (Hsub2 : echo_data_sub (uvis_M W')).
    { destruct Hok as (_ & _ & _ & _ & _ & Himg & _).
      exact (echo_data_of_elf_image _ Himg). }
    (* THE LEND: the turn bundle at the block's first byte, or the taint *)
    cbn [EchoLinksLine.ewc_lpr].
    iDestruct (EchoLinksLine.ewc_blk_0_lend T v I 0%nat with "Hc")
      as "[Hl | #HT]"; last first.
    { (* a tainted lend: the generic slot, and the kill wand from the taint *)
      iApply ("Hgen" $! (Wq I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (EchoLinksLine.ewc_lcred_taint T γ (S gen_id) I 0%nat v
                with "Hpin [Hk]").
      iApply Hkt. iModIntro. iExact "Hk". }
    iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
    destruct (wr_blk_t_stage ps cs I P Hw)
      as (Hrest & Hn0 & HP & Hpin & Htail).
    assert (Hst : echo_stage ps cs I (last_ws I) P)
      by (rewrite /echo_stage; split_and!;
          [ exact Hrest | exact Hn0 | reflexivity | exact HP | exact Hpin ]).
    iApply (echo_uexec_slot_at (PS := uprogSG_free) T γ W' v ps cs I
              (last_ws I) P rb (fun _ : Z => Wq I)
              ltac:(intros x y; reflexivity)
              (line_ok_ge2 (last_ws I) Hokws)
              Hst Hargv Hl1 Hpc Hsub Hsub2 Hx Hroom96 Hal8 Hstkrow Hargsrow
              Havd Havs Hfdlen Hstop Hlzf
              ltac:(rewrite Hfd; exact Hpark)
              with "[] Hpin Hlk Hnpw' Hdep Hmp [Htn]").
    - (* THE BLOCK'S END PAYS THE EXIT: the output's own length on, the
         choice filed, the credential is the shell's next prompt's *)
      iIntros "!> Hc". rewrite /UkShFork.ushf_wq. iRight.
      iApply (EchoLinksLine.ewc_lcred_of_post T γ (S gen_id) I v with "Hpin").
      iApply (EchoLinksLine.ewc_post_of_ech T v ps cs I (last_ws I) P
                Hrest Hn0 eq_refl HP Hpin Htail).
      iEval (rewrite /ech
               (echcs_pos cs (length (wl_line (drop 1 (last_ws I))))
                  (wl_line_pos (drop 1 (last_ws I))))) in "Hc".
      iExact "Hc".
    - (* ...and its first byte is where the lend stands *)
      rewrite /ech. cbn [echcs]. rewrite Nat.add_0_r.
      iLeft. iFrame "Htn Hps Hcs HE".
  Qed.

  (* =================================================================== *)
  (*  2.  THE ASSEMBLY: sh's pinned bundle pays its exec supply, PAID      *)
  (*                                                                      *)
  (*  [UShEcho]'s section 7 at the paid entry.  IT IS AN INSTANCE OF THE   *)
  (*  U-TIER RULE ([ExecRun.udepw_at_refR_of_sup], lane EX-4) and what is  *)
  (*  left here is sh's own supply: the node it malloc'd read off the lent *)
  (*  heap, the PIN as (W)'s supplier ([ExecRun.exec_walk_of_pin]), the    *)
  (*  resolving arm [echo_slot_of_kexec_at] as (E), the taint arm at the   *)
  (*  chosen payload, and the refund -- the ledger fragment and the lend.  *)
  (* =================================================================== *)
  Lemma sh_exec_sup_echo_wq_holds :
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ echo_links T γ -∗ udep (PS := uprogSG_free) -∗ sh_echo_slot T -∗
      UkShEcho.sh_exec_sup_echo_wq Wc.
  Proof using HPT HTT ghost_varG1.
    intros Hkt.
    iIntros "#Hlk #Hdep (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_wq. iIntros "!>" (I) "%Hokws".
    rewrite /UkShEcho.sh_exec_sup_echo.
    iIntros "!>" (N' m pc s0 t g ld) "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    (* the lend, pinned *)
    rewrite /EchoLinksLine.ewc_lcred. iDestruct "Hcr" as (v) "[#Hpin Hcr]".
    (* ---- THE TAINT ARM: the generic slot at the chosen payload.  It names
       no key, so it is built before the deposit's own ∀. ---- *)
    iAssert (image_entry_taint T (fun _ : Z => Wq I) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (Wq I) W' with "HT Hmp []").
      iIntros "!> #Hk". rewrite /UkShFork.ushf_wq. iRight.
      iApply (EchoLinksLine.ewc_lcred_taint T γ (S gen_id) I 0%nat v
                with "Hpin [Hk]").
      iApply Hkt. iModIntro. iExact "Hk". }
    (* ---- ...AND THE REST IS THE U-TIER RULE (lane EX-4).
       [ExecRun.udepw_at_refR_of_sup] is the general step from an exec
       bundle to the deposit the exec leaf consumes; what is left here is
       sh's own SUPPLY -- the node it malloc'd, read off the lent heap, the
       PIN as (W)'s supplier, and echo's PAID entry. ---- *)
    iApply (udepw_at_refR_of_sup N' m pc
              (mword_of_int s0) (mword_of_int (t + 8))
              FsImg.ROOTINO T echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld
               ∗ EchoLinksLine.ewc_lpr T v I 3%nat)%I
              _ echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    (* THE REFUND IS THE LEND, WHOLE: the fragment and the block credential
       come back to the child whose exec failed *)
    { iIntros "!> [$ Hc]". rewrite /EchoLinksLine.ewc_lcred.
      iExists v. iFrame "Hpin Hc". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
    (* the run's two table rows come in bundled (lane OFF-HAND-3, R1);
       the entry below is stated at the pipe half. *)
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    (* the node, read ONCE off the lent heap *)
    iAssert (⌜ echo_node_img (last_ws I) M s0 t g ⌝)%I as %Himg.
    { iApply (echo_node_img_of_cmd (last_ws I) _ _ _ M pm sz s0 t g Hokws
                with "Hheap Hcmd"). }
    (* ...the table's length, and sh's fd 1 row AT THE TABLE, off the lent
       authority against the fragment *)
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    assert (Hfd1' : UkSh.ush_fd1p (take NSTD fdv)) by (rewrite Hl; exact Hfd1).
    iFrame "Hheap Hufd".
    (* ---- (W)'s PURE INPUT: argv[0]'s string IS the path exec resolves --- *)
    iSplitR "Hstd Hcr".
    { iPureIntro.
      exact (sh_echo_path_of_holds (last_ws I) Hokws M s0 t g Himg Hbytes). }
    (* ---- (W) ITSELF, AT THE PIN SUPPLIER ---- *)
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsEchoPin.era0_echo_pins T FsImg.ROOTINO
                echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (MkAnode (AFile ElfUser.echo_elf) 1%nat) sh_echo_pin_resolves
                with "Hcl Hinv"). }
    (* ---- (E): echo's PAID entry, at the pinned image ---- *)
    iSplitR "Hstd Hcr".
    { rewrite Hpeq. rewrite /image_entry. iModIntro.
      iIntros (na alen afun W') "%Hok %Hcwd0 %Hlzf _ _ %Hpkq %Hargs Hmp [_ Hc]".
      destruct (echo_args_det_holds (last_ws I) Hokws M s0 t g na alen afun
                  Himg Hbytes Hargs) as (Hna & Halen & Hafun).
      (* ECHO'S FRAME FITS: the arguments this line pushed leave the
         twelve words the entry needs.  An INEQUALITY off the push
         geometry, discharged at the lengths the parser pinned -- not the
         vector's address as a number ([UShEcho.echo_room_of_det]). *)
      iApply (echo_slot_of_kexec_at na alen afun fdv W' v I Hokws Hok
                (echo_room_of_det (last_ws I) na alen Hokws Hna Halen)
                Hlen
                ltac:(rewrite <- (kexec_image_ok_fd _ na alen afun fdv W' Hok);
                      exact Hpkq)
                Hlzf Hna Halen Hafun Hfd1' Hkt
                with "Hpin Hlk Hnp0 Hdep Hgen Hmp Hc"). }
    iFrame "Hstd Hcr".
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
      rewrite /UkShEcho.ush_execfail_law_wq. iIntros "!>" (I).
      iApply (UShPanic.ush_execfail_law_holds (PS := uprogSG_free) T γ I
                with "Hlk"). }
    iApply (UkShEcho.ushf_child_law_holds (PS := uprogSG_free) (fun k H => H) Wc
              with "Hxlw Hsup").
  Qed.

End UShEchoPay.
