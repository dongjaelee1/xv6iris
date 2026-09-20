(* ===================================================================== *)
(*  UShRedirPay.v -- THE REDIRECT CHILD'S EXEC SUPPLY AT fd 1 = `f`       *)
(*  (the PROGRAM STREAM's era step for [UShRound.Hchild_redir]).          *)
(*                                                                       *)
(*  [UShEchoPay.sh_exec_sup_echo_wq_holds_at] is sh's exec supply when    *)
(*  the child's fd 1 is the CONSOLE: the U-tier rule                      *)
(*  ([ExecRun.udepw_at_refR_of_sup]) at three components -- the path (P), *)
(*  the walk (W) and the image's entry (E) -- with the ledger fragment    *)
(*  and the era's lend as the payload, refunded whole on the failing arm. *)
(*                                                                       *)
(*  The REDIRECT child's fd 1 is a HELD DESCRIPTOR ON `f`, so (P) and (W) *)
(*  are unchanged -- the child still execs /echo, so the path is          *)
(*  [UShEcho.echo_pl] and the walk is the same pin resolution -- and the  *)
(*  ONE thing that changes is (E): the entry is echo's at a file, i.e.    *)
(*  [UEchoFile.efile_image_entry], not [UShEcho]'s console twin.  That    *)
(*  entry is this file's PREMISE ([sh_file_entry]) and not an import: it  *)
(*  is stated at exactly K1's premises, so the round -- which holds the   *)
(*  file claim [(c, r, Heq)] and the era's opaque console credential      *)
(*  [Wq] -- applies K1's lemma to it in one step, and this file stays out *)
(*  of [UEchoFile]'s cone.                                               *)
(*                                                                       *)
(*  THE PAYLOAD IS A CONSTANT ([fun _ : Z => Qc]).  The fork chose        *)
(*  [UkShFork.ushf_wq Wc I], which is of that shape, and keeping it       *)
(*  literal is what lets the taint arm hand the generic slot its          *)
(*  [fun _ => R] without a functional-extensionality step.                *)
(*                                                                       *)
(*  WHAT THE ENTRY'S [Pay] IS.  The U-tier rule hands the entry the       *)
(*  supply's own payload on the exec path and gives it back as the refund *)
(*  on the failing one, so the payload here is the ledger fragment and    *)
(*  the lend ([ustd ∗ Cr]) and the refund is the identity.  K1's entry    *)
(*  asks for [UEchoFile.ef_pay] instead -- the deed at `f` empty and the  *)
(*  program's own half of the offset shadow at zero -- so the conversion  *)
(*  between the two is a PREMISE, and it is the round's: at the file era  *)
(*  the deed rides inside the lend.                                      *)
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
Require Import ProcGeom.          (* [NOFILE] / [NSTD] *)
Require Import UexecSlot UexecRet.
Require Import UkRun.
Require Import UserFd.
Require Import ElfFile ElfUser.
Require Import FsImg.
Require Import FsEchoPin.
Require Import ExecEntry.         (* [image_entry] / [image_entry_taint] *)
Require Import FsAbsDefs.         (* [anode] / [MkAnode] / [AFile] *)
Require Import ExecRun.           (* THE U-TIER EXEC RULE this supply is an
                                     instance of *)
Require Import UkShEcho.
Require Import UkShRedirBody.     (* [ushs_fd1f]: the abstract fd-1 row *)
Require Import EchoDisc.
Require Import UShEcho.           (* the pinned bundle's inputs *)
Local Open Scope Z_scope.
Import Defs.

Section UShRedirPay.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  1.  THE ENTRY THIS SUPPLY IS MISSING, AS A PREMISE                  *)
  (*                                                                     *)
  (*  [UEchoFile.efile_image_entry] at the payload the fork chose, with   *)
  (*  every input the supply meets inside its own ∀ quantified here:      *)
  (*  the image the exec'ing process runs with, the node sh built, and    *)
  (*  the table the exec channel carries verbatim.  The premises are      *)
  (*  K1's, in K1's order.                                                *)
  (* =================================================================== *)
  Definition sh_file_entry (ty : fdtype) (ws : list (list (bv 8)))
      (Q : Z -> iProp Σ) (Pay : iProp Σ) : iProp Σ :=
    (□ (∀ (M : gmap Z (bv 8)) (s0 t : Z) (g : nat -> bv 8)
          (sts : list fdstate) (cs : gset gname) (pidv : mword 32),
          ⌜ UShEcho.echo_node_img ws M s0 t g ⌝ -∗
          ⌜ UkShEcho.echo_argv_bytes ws g ⌝ -∗
          ⌜ length sts = NOFILE ⌝ -∗
          ⌜ UkShRedirBody.ushs_fd1f ty (take NSTD sts) ⌝ -∗
          UkRun.urun_nopipe sts -∗
          image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64)
            sts FsImg.ROOTINO cs pidv Q Pay uslot))%I.

  Global Instance sh_file_entry_persistent ty ws Q Pay :
    Persistent (sh_file_entry ty ws Q Pay).
  Proof using . rewrite /sh_file_entry. apply bi.intuitionistically_persistent. Qed.

  (* the entry's payload slot is a WAND away, which is all the difference
     between what the U-tier rule lends and what K1's entry asks for *)
  Local Lemma image_entry_pay_of (f : elf_bytes) (M : gmap Z (bv 8))
      (av : mword 64) (sts : list fdstate) (cw : Z) (cs : gset gname)
      (pidv : mword 32) (Q : Z -> iProp Σ) (Pay Pay' : iProp Σ)
      (X : uvis -d> iPropO Σ) :
    □ (Pay' -∗ Pay) -∗
    image_entry f M av sts cw cs pidv Q Pay X -∗
    image_entry f M av sts cw cs pidv Q Pay' X.
  Proof using .
    iIntros "#Hw #He". rewrite /image_entry. iIntros "!>" (na alen afun W')
      "%H1 %H2 %H3 %H4 %H5 %H6 Hmp HP".
    iApply ("He" $! na alen afun W' with "[%] [%] [%] [%] [%] [%] Hmp [HP]");
      [ exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | ].
    iApply "Hw". iExact "HP".
  Qed.

  (* =================================================================== *)
  (*  2.  THE SUPPLY ITSELF                                              *)
  (*                                                                     *)
  (*  [UkShRedirBody.wp_kshm_child_file_redir] takes exactly this, at the *)
  (*  [ty] the child's own [open] returned.                              *)
  (* =================================================================== *)
  Lemma sh_exec_sup_file_at_holds (T : iProp Σ)
      `{!Persistent T} `{!Timeless T}
      (ty : fdtype) (ws : list (list (bv 8))) (Qc Cr Pay : iProp Σ) :
    line_ok ws ->
    (* THE PAY CONVERSION, and it is the round's: at the file era the deed
       rides inside the lend *)
    □ (∀ (N' : uk_names Σ) (ld : list fdstate),
         UserFd.ustd (ukn_fd N') ld ∗ Cr -∗ Pay) -∗
    (* ...and the taint's arm at the payload the fork chose *)
    □ (app_taint -∗ Qc) -∗
    sh_file_entry ty ws (fun _ : Z => Qc) Pay -∗
    UShEcho.sh_echo_slot T -∗
    UkShEcho.sh_exec_sup_echo_at (UkShRedirBody.ushs_fd1f ty) ws
      (fun _ : Z => Qc) Cr.
  Proof using ufdG0.
    intros Hokws.
    iIntros "#Hpay #Hkill #Hent (#Hinv & #Hcl & #Hgen)".
    rewrite /UkShEcho.sh_exec_sup_echo_at.
    iIntros "!>" (N' m pc s0 t g ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd1 Hstd #Hcmd Hcr".
    (* ---- THE TAINT ARM: the generic slot at the chosen payload ---- *)
    iAssert (image_entry_taint T (fun _ : Z => Qc) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT Hmp".
      iApply ("Hgen" $! Qc W' with "HT Hmp Hkill"). }
    (* ---- ...AND THE REST IS THE U-TIER RULE ---- *)
    iApply (udepw_at_refR_of_sup N' m pc
              (mword_of_int s0) (mword_of_int (t + 8))
              FsImg.ROOTINO T UShEcho.echo_pl ElfUser.echo_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I
              _ UShEcho.echo_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    (* THE REFUND IS THE PAYLOAD, WHOLE *)
    { iIntros "!> $". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iAssert (⌜ UShEcho.echo_node_img ws M s0 t g ⌝)%I as %Himg.
    { iApply (UShEcho.echo_node_img_of_cmd ws _ _ _ M pm sz s0 t g Hokws
                with "Hheap Hcmd"). }
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    assert (Hfd1' : UkShRedirBody.ushs_fd1f ty (take NSTD fdv))
      by (rewrite Hl; exact Hfd1).
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro.
      exact (UShEcho.sh_echo_path_of_holds ws Hokws M s0 t g Himg Hbytes). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsEchoPin.era0_echo_pins T FsImg.ROOTINO
                UShEcho.echo_pl [FsImg.ROOTINO; FsEchoPin.ECHO_INO]
                FsEchoPin.ECHO_INO
                (MkAnode (AFile ElfUser.echo_elf) 1%nat)
                UShEcho.sh_echo_pin_resolves with "Hcl Hinv"). }
    iSplitR "Hstd Hcr".
    { rewrite Hpeq.
      iApply (image_entry_pay_of ElfUser.echo_elf M
                (mword_of_int (t + 8) : mword 64) fdv FsImg.ROOTINO cs pidv
                (fun _ : Z => Qc) Pay
                (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I uslot with "[] []").
      - iIntros "!> H". iApply ("Hpay" $! N' ld with "H").
      - iApply ("Hent" $! M s0 t g fdv cs pidv with "[%] [%] [%] [%] Hnp0");
          [ exact Himg | exact Hbytes | exact Hlen | exact Hfd1' ]. }
    iFrame "Hstd Hcr".
  Qed.

End UShRedirPay.
