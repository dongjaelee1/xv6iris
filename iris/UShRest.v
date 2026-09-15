(* ===================================================================== *)
(*  UShRest.v -- THE SHELL'S TAIL OBLIGATION, AT THE ECHO ERA'S OWN       *)
(*  FAMILIES (lane R3).                                                   *)
(*                                                                       *)
(*  [UkSh.ush_rest_l N γp T Wc Wb Pm R] is the obligation the command     *)
(*  loop hands the rest of main's body: "from 0x97a, with the line fact   *)
(*  and the loop's carried state, the body runs and re-enters the loop    *)
(*  head".  [UkShFork.ushf_rest_of_body] is its ONE proof, and its        *)
(*  remaining premises are facts about THE ERA -- the paid child's walk,  *)
(*  a killed child's credential, sh's own fork panic, the timelessness    *)
(*  of the write credential.  Those are FALSE for an arbitrary family     *)
(*  (take [Wc := emp] and the child law asks /echo to write "hello        *)
(*  world" out of nothing), so no [forall T Wc Wb Pm] statement can carry *)
(*  them: the obligation has to be discharged where the era is known.     *)
(*  This file is that place, and [sh_rest_holds] is the one glue lemma.   *)
(*  It is what deletes [UInitSh.sh_pay_rest] and, with it, the last       *)
(*  shell-side hypothesis of the top theorem.                            *)
(*                                                                       *)
(*  It cannot live in [UkShFork.v] (no era there) nor in [UInitBoot.v]    *)
(*  without dragging [UShEchoPay]'s cone into the boot assembly's own     *)
(*  file, so it is a leaf of its own, just above [UShEchoPay.v].          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import Xv6Cameras Xv6G FdSlots IrefSlots ProcAvail FileInvDefs.
Require Import RegFile.
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UserPerm UexecSlot UexecRet.
Require Import UserHeap UkRun UkRunLeaf.
Require Import UserFd UserCwd UserChildren.
Require Import ChildTok.
Require Import ElfFile ElfUser ElfLoadable.
Require Import PathElems FsTree FsBlocks FsBytesGamma.
Require Import FsCfg.             (* [fsc_fs] *)
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeArith UmodeAbi.
Require Import FsImg FsImgCheck.
Require Import FsAbsDefs FsAbsEra.
Require Import AppCfg AppInv.
Require Import PinnedObs PinnedExec.
Require Import FsEchoPin.
Require Import PieceFam.
Require Import SpecKexec SpecSysExec.   (* [kexec_sz] *)
Require Import UShKernel.         (* [sh_kexec_sz] *)
Require Import KexecBuilt.
Require Import UserPtTree.        (* [pgroundup] *)
Require Import KexecDefs.
Require Import UkAbi.
Require Import UexecSG UexecExecInst UexecExecMint.
Require Import UkSh UkShRun UkShDiag.
Require Import UkShParse.         (* [ushp_no_symbols] / [ushp_tokens] *)
Require Import UkShLoop.          (* [ush_line_lexable] / [ushl_R] *)
Require Import UkShMain UkShFork. (* [ushf_rest_of_body] *)
Require Import UConsLine EchoDisc.
Require Import UkShEcho.          (* [ush_line_toks_holds] / [echo_toks] *)
Require Import EchoOut.           (* [era_pin] / [era_pins] *)
Require Import EchoLinks.         (* [echo_links] / [ewc_ban] *)
Require Import EchoLinksLine.     (* [ewc_lcred] and its two laws *)
Require Import UShEcho.           (* [sh_echo_slot] *)
Require Import UShLine.           (* [ush_mid] *)
Require Import UShPanic.          (* [ush_panic_law_holds] *)
Require Import UShEchoPay.        (* the paid child's two laws *)
Require Import UInitSh.           (* [sh_Rsh] *)

(* ===================================================================== *)
(*  0.  THE LINE THE DISCIPLINE ADMITS LEXES -- E4's closed computation    *)
(*      in the shape [UkShFork.ushf_rest_of_body] takes it.                *)
(*                                                                       *)
(*  [UkShEcho.ush_line_toks_holds] names the token list;                  *)
(*  [UkShLoop.ush_line_lexable] only asks that one exists and is short.   *)
(* ===================================================================== *)
Lemma ush_line_lexable_holds : UkShLoop.ush_line_lexable.
Proof.
  intros f k len Hl.
  destruct (UkShEcho.ush_line_toks_holds f k len Hl) as (_ & Hns & Htk).
  split; [ exact Hns | ].
  exists UkShEcho.echo_toks.
  split; [ exact Htk | exact UkShEcho.echo_toks_lt10 ].
Qed.

(* ===================================================================== *)
(*  0b. SH'S BREAK, AS [exec] LEAVES IT -- three closed side conditions.   *)
(*      [UShKernel.sh_kexec_sz] is the one computation; everything below   *)
(*      is arithmetic on the literal 0x5000.                              *)
(* ===================================================================== *)
Lemma sh_sz_lo : 8344 <= kexec_sz ElfUser.sh_elf.
Proof. rewrite UShKernel.sh_kexec_sz. lia. Qed.

Lemma sh_sz_al :
  UserPtTree.pgroundup (kexec_sz ElfUser.sh_elf) = kexec_sz ElfUser.sh_elf.
Proof. rewrite UShKernel.sh_kexec_sz. vm_compute. reflexivity. Qed.

Lemma sh_sz_ok : usz_ok (kexec_sz ElfUser.sh_elf + 65536).
Proof.
  rewrite UShKernel.sh_kexec_sz. unfold usz_ok.
  assert (E : UserPtTree.pgroundup (0x5000 + 65536) = 86016)
    by (vm_compute; reflexivity).
  rewrite E. lia.
Qed.

Section UShRest.
  (* [UInitSh.v]'s binder list VERBATIM (durable-notes: a shorter list
     makes Coq synthesise an instance and the elaboration explodes), so
     that what this file proves is stated at the very instances
     [UInitBoot.echo_Hinit_boot] holds.  In particular NO
     [ghost_varG Σ (gset gname)] binder: the children set's camera is
     [Xv6G]'s own field ([Xv6Cameras.uchG]), and a second provider in the
     same scope is two instances whose propositions print identically. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ}.
  (* the era: its taint and its ghost names *)
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{HPT : !Persistent T} `{HTT : !Timeless T}.

  (* THE FAMILIES, spelled as the era's own.  [Wc] is the TIGHT write
     credential at a line boundary, [Wb] the banner-owed one (this is
     [UInitBanner.kinit_ban T γ] unfolded -- kept at the literal so that
     [UShPanic.ush_panic_law_holds]'s statement matches without a rewrite,
     and the ONE rewrite is at the call site), [Pm] the console lease's
     pieces the loop carries in the payload's place. *)
  Local Notation Wc := (EchoLinksLine.ewc_lcred T γ (S gen_id)).
  Local Notation Wbn :=
    (fun n : nat => ∃ v : era_pins,
       era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v n 0%nat)%I.

  (* =================================================================== *)
  (*  1.  THE GLUE                                                        *)
  (*                                                                      *)
  (*  What the top hands in: the era's links, the generic exec deposit,   *)
  (*  the ingredients of /echo's pinned entry, and ONE era pin.  What      *)
  (*  comes back is the whole obligation, at the record the kernel minted  *)
  (*  and the position ghost /init lent -- i.e. exactly the second         *)
  (*  conjunct of [UInitSh.sh_pay].                                        *)
  (*                                                                      *)
  (*  The three era laws are introduced as NAMED hypotheses by             *)
  (*  [iPoseProof] and never by [iIntros "#..."] on the bundle             *)
  (*  (durable-notes: the [Persistent] search walks the child law's wand   *)
  (*  chain and does not return).  Every deposit-bearing term is pinned    *)
  (*  at [uprogSG_free] on both sides.                                     *)
  (* =================================================================== *)
  Lemma sh_rest_holds (γp : gname) (N : uk_names Σ) :
    (⊢ □ riscv_kill_cred -∗ T) ->
    ⊢ EchoLinks.echo_links T γ -∗
      (* PINNED at the FREE instance on both sides (durable-notes): the
         deposit's [uprogSG] is what [UShEchoPay]'s laws are stated at, and
         a bare [udep] here resolves to the ambient generic one. *)
      udep (PS := uprogSG_free) -∗
      UShEcho.sh_echo_slot T -∗
      (∃ v : era_pins, era_pin γ (S gen_id) v) -∗
      UkSh.ush_rest_l (PS := uprogSG_free) N γp T Wc Wbn
        (UShLine.ush_mid γ γp)
        (UInitSh.sh_Rsh (ukn_t N) (ukn_d N) (ukn_s N)).
  Proof.
    intros Hkt.
    (* the credential's conversion at a fork that failed: the block the
       line owed, read as a boundary credential *)
    assert (Hwbl : forall i : nat,
              ⊢ EchoLinksLine.ewc_lcred T γ (S gen_id) i 3%nat -∗
                EchoLinksLine.ewc_lcred T γ (S gen_id) i 0%nat)
      by (intro i; exact (EchoLinksLine.ewc_lcred_blk_line T γ (S gen_id) i)).
    iIntros "#Hlk #Hdep #Hslot #Hpin".
    iDestruct "Hpin" as (v) "#Hp".
    (* ---- the three era laws, as named hypotheses ---- *)
    iPoseProof (UShEchoPay.ushf_child_law_holds_at T γ Hkt
                  with "Hlk Hdep Hslot") as "#Hchl".
    iPoseProof (UShEchoPay.ushf_kill_law_holds T γ v Hkt with "Hp") as "#Hkl".
    iPoseProof (UShPanic.ush_panic_law_holds (PS := uprogSG_free) T γ
                  with "Hlk") as "#Hplaw".
    (* ---- the obligation's box: the record's own facts come OUT of it,
           so the discharger can be applied at [ukn_const N] ---- *)
    iIntros "!>" (l) "%Hc".
    iPoseProof (UkShFork.ushf_rest_of_body
                  (PS := uprogSG_free) (Hpay := Hc)
                  N γp T Wc Wbn (UShLine.ush_mid γ γp)
                  (fun k H => H) (kexec_sz ElfUser.sh_elf)
                  ush_line_lexable_holds sh_sz_lo sh_sz_al sh_sz_ok Hwbl
                  with "Hkl Hchl Hplaw") as "Hb".
    rewrite /UkSh.ush_rest_l.
    iDestruct ("Hb" $! l with "[%]") as "Hb'"; [ exact Hc | iExact "Hb'" ].
  Qed.

End UShRest.
