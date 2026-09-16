(* ===================================================================== *)
(* UInitBoot.v -- THE FIRST PROCESS'S EXEC BUNDLE, FOR A CONSTRAINING    *)
(* APPLICATION (lane E2, ARM-c (1b)).                                    *)
(*                                                                       *)
(* [InitBoot.init_boot_bundle] is what the whole-system theorem asks its  *)
(* application for ([App.xv6_app_adequacy]'s [Hinit_boot]): the kernel's  *)
(* own caller-side bundle for [kexec("/init")] at forkret's boot arm.     *)
(* The GENERIC application discharges it from the trivial mint            *)
(* ([InitBoot.init_boot_bundle_triv]); this file is the other             *)
(* discharge -- a PINNED exec at "/init", whose slot piece answers with   *)
(* /init's OWN verified entry ([UInitKernel.init_slot_of_kexec]) rather   *)
(* than with a generic family.                                           *)
(*                                                                       *)
(* WHY IT IS A SEPARATE FILE FROM [UInitSh.v], which is the same assembly *)
(* one level up (init execing sh): the two differ in exactly ONE place    *)
(* and it is not the pin -- it is WHERE THE ARGUMENTS COME FROM.  sh's    *)
(* exec is a SYSCALL, so its path and argument vector are readings of the *)
(* calling image ([SpecSysExec.exec_path_of] / [exec_args_of]) and the    *)
(* bundle is [sys_exec_au_pre]; /init's is the KERNEL's own call, with a  *)
(* literal path and a literal vector, and the bundle is                   *)
(* [SpecKexec.exec_au_pre].  [PinnedExec.pinned_exec_bundle_boot] is that *)
(* second shape, and [PinnedExec.pex_slot_at] is the identifying step the *)
(* two share.                                                            *)
(*                                                                       *)
(* WHAT IS STILL A PREMISE HERE, and what discharges it:                  *)
(*   the CLAIM LAW at [FsInitPinBoot.era0_pins] -- [AppEcho]'s, through   *)
(*     the era's record equation (the pin is one of the three conjuncts   *)
(*     of [EchoFsPure.echo_fs_pure], so [echo_fs_pure_acc] gives it);        *)
(*   the CONSTRUCTOR WAND -- [UInitKernel.init_slot_of_kexec] at /init's  *)
(*     own entry premises;                                               *)
(*   the TAINT ARM -- [UexecExecMint.uslot_mint_all] on                   *)
(*     [AppEcho.echo_sup_of_taint];                                       *)
(*   [Pay] -- the LINEAR half: the console reader token the bundle's own  *)
(*     wand hands in ([InitBoot.init_boot_bundle] is a wand from          *)
(*     [ConsoleInv.cons_reader]) beside the era's console credential      *)
(*     (the KEY or the FLAG, [AppEcho.echo_boot]'s two arms).             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.base_logic Require Import iprop.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.base_logic.lib Require Import mono_nat.   (* [mono_nat_lb_own_get]: the era's turn at 0 is the reader's receipt residue (step 4) *)
(* [mono_list] AND [ghost_var] ARE REQUIRED HERE FOR A REASON, and so is
   [TsoCtx] below: a [Context] binder naming a class whose defining module
   is not in scope does not fail -- the backtick generalisation invents a
   FRESH VARIABLE for the name ([mono_listR : ofe -> cmra], [ghost_varG :
   gFunctors -> Set -> Type], [CurCtx : Type]) and the binder is then about
   something no real instance can ever match.  The symptom is not a missing
   instance where you wrote it; it is an elaboration that never comes back
   somewhere else (measured here at 47 GB RSS in 94 seconds, in the
   STATEMENT of [ush_cons_in_of_Cns], because [AppEcho.cons_never]'s [own]
   is at the real [mono_listR] and the section's was not).  See
   [UShConsK.v]'s header note. *)
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import proofmode.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import WpUart.            (* [cons_licence]: the generic slot's output licence *)
(* THE GHOST BINDER LIST'S DEFINING MODULES, each IMPORTED and not merely
   required ([PinnedExec.v]'s note: a field instance is inert wherever its
   module is not imported). *)
Require Import CtxIdDefs.            (* [CurCtx] -- see the note above *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import ChildTok.
Require Import UexecSlot.
Require Import UexecRet.          (* [uslot] -- REQUIRED DIRECTLY (the seal) *)
Require Import UexecSG.
Require Import PathElems.
Require Import AppCfg.
Require Import AppInv.
Require Import FsCfg.             (* [fsc_fs] / [fsc_cons] *)
Require Import ConsoleInv.        (* [cons_reader] *)
Require Import SpecKexec.         (* [exec_au_pre] / [kexec_image_ok] *)
Require Import FsAbsDefs.
Require Import FsAbsEra.
Require Import PinnedExec.
Require Import UexecExecInst.     (* the class INSTANCE: [uexecSG_xv6].  This
                                     file is E2's assembly for THE xv6
                                     application, so its [uexecSG] is the
                                     kernel's own -- which is also what
                                     [App.xv6_app_adequacy] instantiates
                                     [InitBoot.init_boot_bundle]'s at, and
                                     what [UexecExecMint]'s supply laws are
                                     stated over. *)
Require Import UkRun.             (* [udepw_law] -- the named deposits *)
Require Import UkInit.            (* [init_deps] / [init_cons_sup] *)
Require Import UexecExecMint.     (* [udepw_law_of_sup] / [udep_free] *)
Require Import UkWriteClosed.     (* [kinit_w1_of_closed_l0]: init's write on a closed fd 1 (lane EXEC-SEAM, (D)) *)
Require Import UInitKernel.       (* [init_slot_of_kexec] / the dance *)
Require Import EchoLinks.         (* [echo_links] -- E5's four links as one
                                     persistent law *)
Require Import UInitDiag.         (* [kinit_pro] and the three laws /init's
                                     walk is handed (lane M6b): the banner's
                                     leaving the round-open credential, and
                                     the two diagnostics paid from it *)
Require Import UInitBanner.       (* [kinit_banner0_holds] -- the era's
                                     credential as init's banner payment *)
Require Import UInitCons.         (* [init_cons_fd] / [init_cons_cred] *)
Require Import UInitConsK.        (* the two arms' discharges at echo's era *)
Require Import UInitSh.           (* [init_cons_sup_of_sh_slot] *)
Require Import UShPanic.          (* [sh_prompt_law_holds_line]: the prompt's law at the tight family (step 4) *)
Require Import UShRest.           (* [sh_rest_holds]: the shell's tail
                                     obligation, discharged at the era's
                                     own families (lane R3) *)
Require Import EchoLinksPro.      (* [ewc_pro]: the round-open shape /init lends *)
Require Import EchoLinksLine.     (* [ewc_lcred]: the loop's tight credential family (step 4) *)
Require Import EchoLinksBan.      (* [ewc_ban_line]: the banner-owed credential is a boundary credential *)
Require Import UShLine.           (* sh's console read-leaf file.  Its
                                     discharge [ush_read_recv_leaf_holds]
                                     is GONE (lane ECHO-OUT part 5): the
                                     leaf is a premise here now.  The
                                     [Require] stays because the cone it
                                     brings is what this file's own
                                     statements elaborate against. *)
Require Import AppEcho.           (* [echo_boot] / [echo_taint] *)
Require Import EchoOut.            (* [echoOutG]: the class [AppEcho]'s claims
                                      and its ledger are stated at (lane
                                      ECHO-OUT part 5).  It CARRIES
                                      [mono_natG], so it is the taint's one
                                      instance here too. *)
Require Import UserConsole.       (* [ucons_reader_eq] *)
Require Import UserFd.            (* [NSTD] *)
Require Import LinkUserinit.      (* [UG.uexec_wp_gen]: the generic user WP,
                                     the module route SystemAdequacy uses --
                                     the application tier does not Require a
                                     Proof*.v *)
Require Import UkSh.              (* [sh_deps] / [ush_tag_law] / the two
                                     console leaves sh's entry is told *)
Require Import UShConsK.          (* sh's two console leaf discharges at
                                     echo's era (lane SH-OPEN) *)
(* THE ADEQUACY LAYER IS DELIBERATELY NOT REQUIRED HERE.  This file is a
   proofmode-heavy u-tier assembly; pulling [RiscvAdequacy] /
   [SystemAdequacy] / [FsCfgBoot] into it -- which is what the B3 theorem
   [echo_adequacy_modulo_phi] needs, since [Require Import App] is not a
   [Require Export] and brings none of them -- makes the elaboration blow
   up (measured at 54 GB RSS in 64 seconds, and 489 GB in nine minutes
   before the cap was tightened).  The B3 theorem therefore lives in its
   own file, [UInitBootAdequacy.v], which carries the adequacy cone and
   takes only [echo_Hinit_boot] from this one. *)
Require Import KexecDefs.         (* [kxc_sp_final] *)
Require Import PageGeom.          (* [PGSIZE] *)
Require Import InitBoot.          (* [init_boot_bundle] and its path *)
Require Import ElfUser.           (* [init_elf] *)
Require Import ElfLoadable.       (* [init_elf_loadable] *)
Require Import FsInitPin.         (* [INIT_INO] / [init_path] / [init_bytes] *)
Require Import FsInitPinBoot.     (* [era0_pins] *)
Require FsImg.                    (* [FsImg.ROOTINO] *)
Require InodeInv.                 (* [InodeInv.ROOTINO] -- the theorem's cwd *)
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PATH, AS THE WALK READS IT                                    *)
(*                                                                        *)
(*  [InitBoot.init_boot_path] is the six bytes of "/init" the kernel      *)
(*  calls kexec with; [FsInitPin.init_path] is the one name the pin is    *)
(*  stated at.  The first is ABSOLUTE, so the walk ignores the cwd -- and *)
(*  /init's cwd IS the root anyway, which is what makes the [um_start_of] *)
(*  case split below a [reflexivity] on both arms.                        *)
(* ===================================================================== *)
Lemma init_boot_path_elems : path_elems init_boot_path = init_path.
Proof. vm_compute. reflexivity. Qed.

(* the theorem's own working directory, as the pin's number: [Hinit_boot]
   is stated at [bv_unsigned InodeInv.ROOTINO] and every file-system pin
   at [FsImg.ROOTINO], and they are the same 1. *)
Lemma init_boot_cw : bv_unsigned InodeInv.ROOTINO = FsImg.ROOTINO.
Proof. vm_compute. reflexivity. Qed.

(* THE TIE TO THE ELF LAYER, [FsShPin.sh_bytes_elf]'s twin, and it is not
   optional: [ElfUser.init_elf] is [pstring_hex_bytes] APPLIED to the raw
   hex string, so leaving [FsInitPin.init_bytes = init_elf] to unification
   sends the conversion into that computation and the kernel's stack goes
   at [Qed].  Named, the delta happens once, here. *)
Lemma init_bytes_elf : init_bytes = ElfUser.init_elf.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2.  THE PIN RESOLVES                                                  *)
(* ===================================================================== *)
Lemma init_boot_pin_resolves :
  pin_resolves era0_pins FsImg.ROOTINO init_boot_path
    [FsImg.ROOTINO; INIT_INO] INIT_INO ElfUser.init_elf 1%nat.
Proof.
  split_and!.
  - (* "/init" is ABSOLUTE, so the walk starts at the root; /init's cwd is
       the root too, so both arms of [um_start_of] agree *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (init_boot_path !! 0%nat = Some PathElems.SLASH));
      reflexivity.
  - rewrite init_boot_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite init_boot_path_elems. split.
    + exact Hrun.
    + rewrite Hnode init_bytes_elf. reflexivity.
Qed.

(* =================================================================== *)
(*  THE CONSOLE CREDENTIAL                                              *)
(* =================================================================== *)
(*  The six predicates the console's supply is parametric in.  They used *)
(*  to travel as six separate arguments through every lemma of the seam, *)
(*  which is why [init_cons_sup_of_sh_slot] below once read as five      *)
(*  predicates and ten law hypotheses: the application had to hand each  *)
(*  one over at the call.  Bundled here, the application builds the      *)
(*  record ONCE ([AppEcho]'s side: [echo_cc]) and discharges the laws    *)
(*  ONCE ([echo_cc_holds]), and the seam takes a pair.                   *)
(*                                                                      *)
(*  The taint is NOT a field: it comes from the application's interface  *)
(*  ([RiscvPtsto.app_iface]'s [ai_kill]) and is already threaded         *)
(*  separately everywhere the credential goes.  A second copy here would *)
(*  be a second name for the same resource, and the seam's lemmas would  *)
(*  then need an equation between them.                                 *)
(*                                                                      *)
(*  This record's home is really [UShKernel.v], next to [sh_prompt_law], *)
(*  so that [sh_slot_of_kexec] and the rest of the U tier can take the   *)
(*  pair too.  It sits here because that move touches 190 sites across   *)
(*  17 files of a tier another lane is live in; the collapse at the      *)
(*  APPLICATION's boundary -- which is what the redesign is about -- is  *)
(*  contained to this file.                                             *)
Record cons_cred (Σ : gFunctors) := MkConsCred {
  (* the per-position credential on the lease (lane IO-LEAF, M5) *)
  cc_rd : nat -> iProp Σ;
  cc_rd_timeless : forall i : nat, Timeless (cc_rd i);
  (* ...and the mid-line pieces of the same lease (M5(3)) *)
  cc_mid : gname -> nat -> iProp Σ;
  (* ...the era's write credential as the command loop carries it (M6a(3)) *)
  cc_wc : nat -> nat -> iProp Σ;
  (* ...the banner-owed one (step 3) *)
  cc_wb : nat -> iProp Σ;
  cc_wb_timeless : forall i : nat, Timeless (cc_wb i);
  (* ...and the round-open one /init lends on the console row (M6b) *)
  cc_wp : nat -> iProp Σ;
}.
Arguments MkConsCred {Σ} _ _ _ _ _ _ _.
Arguments cc_rd {Σ} _ _.
Arguments cc_mid {Σ} _ _ _.
Arguments cc_wc {Σ} _ _ _.
Arguments cc_wb {Σ} _ _.
Arguments cc_wp {Σ} _ _.
Global Existing Instance cc_rd_timeless.
Global Existing Instance cc_wb_timeless.

Section UInitBoot.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId}.
  (* the console FLAG and KEY's camera ([AppEcho.cons_made] / [cons_key] /
     [cons_never], which the dance's assembly names).  NOT [mono_natG]:
     the taint's camera is [riscvFixedGS]'s own and a second binder here
     would be a second instance that prints alike, which is what makes the
     era's record equation unusable ([UInitConsK.v]'s note).  It is not
     optional -- a lemma naming a resource over a class its section does
     not bind makes Coq SYNTHESISE the instance, and through [solve_inG]
     the elaboration explodes (durable-notes, "A lemma's binder list must
     match the definition it is about"). *)
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  (* the echo claims' class (lane ECHO-OUT part 5): [AppEcho.echo_taint] and
     everything built over it is stated at [EchoOut.echoOutG] now, not at a
     bare [mono_natG] -- and that class CARRIES [mono_natG], which is why
     the note above still holds: there is exactly one binder for it here. *)
  Context `{!echoOutG Σ}.
  (* ...and the rest of [UInitSh.v]'s list, because this file now carries
     its era-specific seam.  COPIED VERBATIM from that file: a shorter
     list is what makes Coq synthesise an instance and blow the
     elaboration up (durable-notes; measured here at 8.6 GB RSS). *)
  Context `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!uartGhostG Σ}.
  (* NO [Context {SG}] / [Context {PS}] -- [UInitSh.v]'s rule, and this
     file learned it the expensive way.  [UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] GLOBALLY, and a section variable of
     the same class standing beside a global instance is two [sbundle]s
     that print identically: the statements below name [UkSh]'s leaves,
     which are elaborated at the ambient pair, and asking Coq to reconcile
     them with a local one blows the elaboration up in the STATEMENT --
     measured here at 47 GB RSS in 94 seconds, before the proof runs.
     Where a lemma has to speak about a DIFFERENT [uprogSG] (the free
     instance /init runs at, [UexecExecInst.uprogSG_free]) it binds one
     itself, as [init_deps_of_laws] does, and the caller passes it. *)

  (* =================================================================== *)
  (*  3.  THE ASSEMBLY                                                    *)
  (*                                                                      *)
  (*  [InitBoot.init_boot_bundle]'s four existential families ARE          *)
  (*  [PinnedExec]'s: [P := PinnedObs.pobs_P T [ROOTINO; INIT_INO]] (the   *)
  (*  cursor that says which inums THIS walk stands on), [Pmiss :=         *)
  (*  pobs_Pmiss T] (a walk that misses is the taint -- a pinned file is   *)
  (*  there), [Fo := pobs_Fo era0_pins T] (the terminal observation, which *)
  (*  hands the lent row back and yields the pin at the observed view) and *)
  (*  [R := Pay] (the refund: exec can fail, and what the construction     *)
  (*  spent has to come back).                                            *)
  (*                                                                      *)
  (*  THE PAYLOAD IS THE TRIVIAL ONE, and that is not a simplification:    *)
  (*  <init> has no parent, so its exit owes nobody anything -- userinit's *)
  (*  own choice, which [InitBoot.init_boot_bundle] writes into its        *)
  (*  statement as [fun _ => True] and which [UInitKernel.init_uexec_slot] *)
  (*  reads back.  So the [Q (-1)] both slot wands carry is [True] and the *)
  (*  constructor below drops it.                                         *)
  (*                                                                      *)
  (*  THE READER TOKEN IS THE BUNDLE'S OWN ARGUMENT (app-echo.md,          *)
  (*  "SH-LINE RULING", R3): it is the KERNEL's to hand, born with the     *)
  (*  ring at boot, and it reaches this wand from forkret's boot arm.  So  *)
  (*  what the application supplies is a WAND from it into the linear      *)
  (*  [Pay] -- which is where /init's console credential travels beside    *)
  (*  it.                                                                 *)
  (* =================================================================== *)
  (* =================================================================== *)
  (*  3a.  THE CWD ROW IS THE KERNEL'S NOW (lane LAZY-FLAG-2, landed)      *)
  (*                                                                      *)
  (*  /init's entry is stated at [uvis_cwd W' = FsImg.ROOTINO] -- its exec *)
  (*  of the RELATIVE name "sh" is only about a file because its cwd is    *)
  (*  the root -- and [SpecKexec.kexec_image_ok] does not carry the        *)
  (*  working directory: exec does not chdir, so the key's [uvis_cwd] is   *)
  (*  the block's, and only the kernel can see it                         *)
  (*  ([SpecKexec.v]'s [exec_key_cwd]).  Lane LAZY-FLAG-2 put that row,    *)
  (*  and the lazy bit beside it, on BOTH wands of                        *)
  (*  [SpecKexec.exec_slot_pre]; [PinnedExec.pinned_exec_bundle_boot]      *)
  (*  relays the two, so the constructor below receives them and there is  *)
  (*  no bridge left to state.                                            *)
  (* =================================================================== *)

  (* ------------------------------------------------------------------- *)
  (*  3b.  THE ROOM: /init's frames fit under its argument block           *)
  (* ------------------------------------------------------------------- *)
  (* [UInitSh.init_sh_room]'s twin at /init's own image: [kexec_sz
     init_elf] is 0x4000 (one page of text, one of data, one guard, one
     stack) and the argument block is the six bytes of "/init" rounded to
     sixteen plus a two-word pointer vector, so [kxc_sp_final] lands at
     0x3FE0 -- 0xFE0 above the stack page's base, which is what /init's
     frames have to fit in. *)
  Lemma init_boot_sp_final :
    kxc_sp_final 0x4000 (fun _ => 5%nat) 1%nat = 0x3FE0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma init_boot_room (n0 : nat) :
    8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0))))) <= 0xFE0 ->
    kexec_sz ElfUser.init_elf - PGSIZE
      + 8 * Z.of_nat (2 + (4 + (12 + (12 + (4 + n0)))))
      <= kxc_sp_final (kexec_sz ElfUser.init_elf) (fun _ => 5%nat) 1%nat.
  Proof.
    intros Hn0. rewrite init_kexec_sz init_boot_sp_final.
    unfold PGSIZE. lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3c.  /INIT'S THREE DEPOSITS, BOXED ONCE                              *)
  (*                                                                       *)
  (*  [UkInit.init_deps T] is [udepw_law 16] beside two [T]-guarded laws,   *)
  (*  and 15 (open) and 17 (mknod) are FREE off the era's supply            *)
  (*  ([UexecExecMint.udepw_law_of_sup]): only the banner write is owed     *)
  (*  (E5's [udepw_law 16], the caller's hypothesis).                       *)
  (*                                                                       *)
  (*  THE CONCLUSION CARRIES ITS OWN [□], and every consumer's premise does *)
  (*  too ([UInitKernel.init_boot_con]).  Handing the bundle round unboxed  *)
  (*  and asking the proofmode to notice it is persistent is what wedges    *)
  (*  the elaboration: the [Persistent] search unfolds [UkRun.udepw]'s wand *)
  (*  chain and does not return (durable-notes; measured as a 40-minute     *)
  (*  UInitKernel.vo at a flat 1.1 GB).  Paying the box HERE, once, at the  *)
  (*  one place that builds the bundle, keeps every later intro structural. *)
  (* ------------------------------------------------------------------- *)
  (*  IT IS PURE PLUMBING, and the supply is NOT read here: this section
      binds [uexecSG] as a VARIABLE, while [UexecExecMint.udepw_law_of_sup]
      is stated at the kernel's own instance ([UexecExecInst.uexecSG_xv6]),
      so a proof mixing the two cannot unify ("cannot apply (app_sup -∗
      udepw_law 15)").  The two free laws are therefore premises, and the
      ASSEMBLY -- whose section has no [uexecSG] variable, so both sides
      resolve to the kernel's instance -- reads them off the supply. *)
  Lemma init_deps_of_laws `{PSx : uprogSG Σ} (T : iProp Σ) :
    (* the write deposit at its two arms (lane EXEC-SEAM, (D)): the law
       under the taint, and the closed-fd leaf at every record *)
    □ (T -∗ UkRun.udepw_law (PS := PSx) 16) -∗
    UkInit.kinit_wcl (PS := PSx) -∗
    □ (T -∗ UkRun.udepw_law (PS := PSx) 15) -∗
    □ (T -∗ UkRun.udepw_law (PS := PSx) 17) -∗
    □ UkInit.init_deps (PS := PSx) T.
  Proof.
    iIntros "#Hwr #Hwcl #H15 #H17 !>". rewrite /UkInit.init_deps /UkInit.kinit_wlaw.
    iSplit; [ iSplit; [ iModIntro; iExact "Hwr" | iExact "Hwcl" ] | ]. iSplit.
    - iModIntro. iExact "H15".
    - iModIntro. iExact "H17".
  Qed.


  (* ...AND THE SEAM SH-OPEN CONSUMES.  [UShConsK] states sh's two console
     leaves against an abstract credential; these are its two discharges,
     chosen by the credential /init's own mknod left.  At the SEAL the
     credential is [AppEcho.cons_never] and sh's first open MISSES (its
     repair arm runs); at the FLAG it is [cons_made r i] and sh's first
     open is the pinned one; under the taint sh proves nothing. *)
  Lemma ush_cons_in_of_Cns (γ : echo_fixed) (r : echo_names) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    app_inv fsc_fs -∗ init_cons_cred (echo_taint γ) r -∗
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N (echo_taint γ))
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N
               (echo_taint γ) (cons_never r))
        ∗ cons_never r)
     ∨ echo_taint γ).
  Proof.
    intros Heq. iIntros "#Hinv #Hc".
    rewrite /init_cons_cred.
    iDestruct "Hc" as "[#Hn | [[%i #Hm] | #HT]]".
    - iRight. iLeft. iSplitR; [ | iExact "Hn" ].
      iApply (sh_cons_absent_echo γ r (cons_never r)
                ltac:(apply _) ltac:(apply _) Heq with "[] Hinv").
      rewrite /sh_cons_never_law. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iApply (echo_cons_never_law γ r).
    - iLeft. iApply (sh_cons_console_echo γ r i Heq with "Hm Hinv").
    - iRight. iRight. iExact "HT".
  Qed.

  (* AT THE FREE INSTANCE, NAMED, all the way through: /init and the shell
     it execs both run at [UexecExecInst.uprogSG_free], which is what keeps
     their [UkRun.udep] clear of the application's supply.  See the note at
     [UInitSh.init_exec_sup_of_sh_slot]. *)
  (* The ten laws the console's supply asks of the application's
     credential.  Gathered VERBATIM from what used to be
     [init_cons_sup_of_sh_slot]'s hypothesis list; each one is used at
     [UInitSh.init_exec_sup_of_sh_slot], which still takes them apart. *)
  Definition cons_cred_holds (cn : cons_names) (T : iProp Σ)
      (Cr : cons_cred Σ) : Prop :=
    (* the read leaf sh runs on *)
    (forall (γp : gname) (N : uk_names Σ) (l : list fdstate),
       ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wb Cr)) ->
       ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp T
           (cc_mid Cr γp) cn l)
    (* the lease's three laws *)
    /\ (forall (γp : gname) (N : uk_names Σ) (i : nat),
          ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wb Cr)) ->
          ⊢ UkSh.ush_at N γp i -∗ UkSh.ush_lease N γp T (cc_mid Cr γp) i)
    /\ (forall (γp : gname) (N : uk_names Σ) (i : nat),
          ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wb Cr)) ->
          ⊢ T -∗ cc_mid Cr γp i -∗ UkSh.ush_at N γp i)
    /\ (forall (γp : gname) (N : uk_names Σ) (i : nat),
          ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wb Cr)) ->
          UkSh.ush_bnd i ->
          ⊢ cc_mid Cr γp i -∗ cc_wb Cr i -∗ UkSh.ush_at N γp i)
    (* the loop's step on the era's write credential *)
    /\ (forall (γp : gname) (n : nat),
          ⊢ cc_mid Cr γp (n + length EchoDisc.echo_line)%nat -∗
            cc_wc Cr n 2%nat -∗
            cc_mid Cr γp (n + length EchoDisc.echo_line)%nat
            ∗ cc_wc Cr (n + length EchoDisc.echo_line)%nat 3%nat)
    (* the three conversions of step 4 *)
    /\ (forall n : nat, ⊢ cc_wb Cr n -∗ cc_wc Cr n 0%nat)
    /\ (forall n : nat, ⊢ cc_wc Cr n 3%nat -∗ cc_wc Cr n 0%nat)
    /\ (forall (γp : gname) (n : nat),
          ⊢ cc_mid Cr γp (n + length EchoDisc.echo_line)%nat -∗
            cc_wb Cr n -∗
            cc_mid Cr γp (n + length EchoDisc.echo_line)%nat ∗ T)
    (* the cursor's boundary *)
    /\ (forall (γp : gname) (N : uk_names Σ) (l : list fdstate) (i : nat),
          ukn_pay N = ucons_pay cn γp T (UkInit.init_rd (cc_rd Cr) (cc_wb Cr)) ->
          ⊢ upos γp i -∗ ucons_pay cn γp T (cc_rd Cr) (-1) -∗
            (UkSh.ush_wcp (cc_wc Cr) (cc_wb Cr) l i 0%nat ∨ T) -∗
            UkSh.ush_posb N γp T (cc_wc Cr) (cc_wb Cr) (cc_mid Cr γp) l 0%nat)
    (* the lend's conversion at the shell's entry (lane M6b) *)
    /\ (forall n : nat, ⊢ cc_wp Cr n -∗ cc_wc Cr n 0%nat).

  (* AT THE FREE INSTANCE, NAMED, all the way through: /init and the shell
     it execs both run at [UexecExecInst.uprogSG_free], which is what keeps
     their [UkRun.udep] clear of the application's supply.  See the note at
     [UInitSh.init_exec_sup_of_sh_slot]. *)
  Lemma init_cons_sup_of_sh_slot (γ : echo_fixed) (r : echo_names)
      (cn : cons_names) (st : fdstate)
      (* the application's console credential, passed straight through to
         [UInitSh.init_exec_sup_of_sh_slot], which still takes its six
         predicates and ten laws apart *)
      (Cr : cons_cred Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    file_app = MkAppcfg echo_names (echo_pred γ) r ->
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (UkSh.ush_Dbody + n0)))) <= 0xFE0 ->
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    cons_cred_holds cn (echo_taint γ) Cr ->
    udep (PS := uprogSG_free) -∗
    □ (echo_taint γ -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    UShKernel.sh_prompt_law (PS := uprogSG_free) (cc_wc Cr) -∗
    UInitSh.init_sh_slot (echo_taint γ)
      (UInitSh.sh_pay (echo_taint γ) (cc_wc Cr) (cc_wb Cr) (cc_mid Cr) Rsh n0) -∗
    UkInit.init_cons_sup cn (echo_taint γ)
      (init_cons_cred (echo_taint γ) r) st
      (cc_wp Cr) (cc_wb Cr) (cc_rd Cr).
  Proof.
    intros Heq Hpsok_free Hn0 Hst
      (Hrl & Hpm1 & Hpm3 & Hpmwb & Hwc & Hwbwc & Hwbl & Hwbr & Hbd & Hpw).
    iIntros "#Hdep #Hdp #Hplaw #Hcore". rewrite /UkInit.init_cons_sup. iSplit.
    - iIntros "!> #Hcns".
      iDestruct "Hcore" as "#Hcore'".
      (* [Persistent K] is an INSTANCE binder there, so it is not passed
         positionally; [cons_never_persistent] answers it. *)
      iApply (UInitSh.init_exec_sup_of_sh_slot (echo_taint γ) cn st
                (cons_never r) (cc_rd Cr) (cc_mid Cr) (cc_wc Cr) (cc_wb Cr)
                (cc_wp Cr) Rsh n0 Hpsok_free Hn0 Hst
                Hrl Hpm1 Hpm3 Hpmwb Hwc Hwbwc Hwbl Hwbr Hbd Hpw
                with "Hdep Hdp Hplaw [] Hcore'").
      iApply (ush_cons_in_of_Cns γ r Heq with "[] Hcns").
      iDestruct "Hcore'" as "(#Hinv & _)". iExact "Hinv".
    - iIntros "!> #HT".
      iApply (init_cons_cred_of_taint (echo_taint γ) r with "HT").
  Qed.

  (* =================================================================== *)
  (*  3e.  THE BOOT BUNDLE                                                *)
  (* =================================================================== *)
  (*  [InitBoot.init_boot_bundle]'s four existential families ARE          *)
  (*  [PinnedExec]'s: [P := PinnedObs.pobs_P T [ROOTINO; INIT_INO]] (the   *)
  (*  cursor that says which inums THIS walk stands on), [Pmiss :=         *)
  (*  pobs_Pmiss T] (a walk that misses is the taint -- a pinned file is   *)
  (*  there), [Fo := pobs_Fo era0_pins T] (the terminal observation) and   *)
  (*  [R := Pay] (the refund: exec can fail and what the construction      *)
  (*  spent comes back).                                                   *)
  (*                                                                      *)
  (*  THE PAYLOAD IS THE TRIVIAL ONE, and that is not a simplification:    *)
  (*  <init> has no parent, so its exit owes nobody anything -- userinit's *)
  (*  own choice, which [InitBoot.init_boot_bundle] writes into its        *)
  (*  statement as [fun _ => True].                                        *)
  (*                                                                      *)
  (*  THE READER TOKEN IS THE BUNDLE'S OWN ARGUMENT (app-echo.md,          *)
  (*  "SH-LINE RULING", R3): it is the KERNEL's to hand, born with the     *)
  (*  ring at boot, and it reaches this wand from forkret's boot arm.      *)
  (* =================================================================== *)
  Lemma init_boot_bundle_of_pinned (T : iProp Σ)
      `{!Persistent T} `{!Timeless T} (Pay : iProp Σ) :
    (* the pin, as a law over the application's claim *)
    □ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                      AppCfg.app_pred AppCfg.app_run v ∗ (⌜era0_pins v⌝ ∨ T)) -∗
    app_inv fsc_fs -∗
    (* /init's OWN entry, at every key the kernel's image fact admits and
       at the two rows it relays beside it.  ABSTRACT HERE: the wand is
       [UInitKernel.init_boot_con]'s, stated where its vocabulary lives,
       and the caller applies that lemma with the [ctokG] instance given
       explicitly -- see the note at [init_boot_con]. *)
    □ (∀ W' : uvis,
         ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
            (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
         ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
         ⌜uvis_lazy W' = false⌝ -∗
         my_pay (uvis_gen W') (fun _ => True)%I -∗ Pay -∗ uslot W') -∗
    (* the taint's generic slot at the (trivial) payload *)
    □ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') (fun _ => True)%I -∗ uslot W') -∗
    (* the linear half, as a wand from the token the kernel hands in *)
    (cons_reader fsc_cons 0%nat -∗ Pay) -∗
    init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof.
    iIntros "#Hcl #Hinv #Hcon #Hgen HPay".
    rewrite /init_boot_bundle. iIntros "Hrd".
    iDestruct ("HPay" with "Hrd") as "HPay".
    rewrite init_boot_cw.
    iDestruct (pinned_exec_bundle_boot fsc_fs uslot era0_pins T
                 FsImg.ROOTINO init_boot_path [FsImg.ROOTINO; INIT_INO]
                 INIT_INO ElfUser.init_elf 1%nat Pay (fun _ => True)%I
                 1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0
                 init_boot_pin_resolves init_elf_loadable
                 with "Hcl Hinv [] [] HPay") as (P Pmiss Fo R) "Hb".
    - iModIntro. iIntros (W') "%Hok %Hcw %Hlz #Hp HP".
      iApply ("Hcon" $! W' with "[%] [%] [%] Hp HP");
        [ exact Hok | exact Hcw | exact Hlz ].
    - iModIntro. iIntros (W') "#HT #Hp". iApply ("Hgen" $! W' with "HT Hp").
    - iExists P, Pmiss, Fo, R. iExact "Hb".
  Qed.

End UInitBoot.

(* ===================================================================== *)
(*  5.  THE THEOREM SIDE (B3): echo's [Hinit_boot].                       *)
(*                                                                       *)
(*  Stated at [App.xv6_app_adequacy]'s own binders -- the era's classes   *)
(*  are quantified there because they are born by the boot mint -- and    *)
(*  carrying, BESIDES the two equations the theorem hands over, ONLY the  *)
(*  arc's remaining obligations, one per owning lane:                     *)
(*                                                                       *)
(*    [Hsh_deps]  write(16)'s deposit, which is ALL [UkSh.sh_deps] is now  *)
(*                (lane SH-LINE 2b, R1': read(5)'s law left the bundle    *)
(*                when the console read moved onto the lease, and         *)
(*                open(15) left it when SH-OPEN pinned the open) -- E5.   *)
(*                /init's own write deposit is the SAME proposition, so   *)
(*                the two hypotheses collapsed into this one.             *)
(*    [Hsh_state] sh's static state out of the data below the frame -- E4 *)
(*    [Hsh_rest]  sh's tail ([UkSh.ush_rest])         -- SH-LINE 2b       *)
(*                                                                       *)
(*  [UkSh.ush_tag_law] -- the third conjunct of [UInitSh.sh_pay] -- is    *)
(*  NOT among them: it is E2's, and it is immediate from the theorem's    *)
(*  own [riscv_rx_tag = app_tag] equation, because echo's tag IS the      *)
(*  discipline-or-taint disjunction.                                      *)
(* ===================================================================== *)
Section EchoInitBoot.
  Context {Σ : gFunctors}.
  Context `{HX : !xv6G Σ, HU : !ufdG Σ}.
  Context `{!inG Σ (mono_listR (leibnizO Z))}.
  (* the echo claims' class (lane ECHO-OUT part 5), as in the section above *)
  Context `{!echoOutG Σ}.

  (* ===================================================================== *)
  (*  THE APPLICATION'S CONSOLE CREDENTIAL (redesign R4)                   *)
  (* ===================================================================== *)
  (*  The six families echo runs the console seam at, and the ten laws the  *)
  (*  seam asks of them.  They used to be written out at the ONE call of    *)
  (*  [init_cons_sup_of_sh_slot] below -- five predicates and ten [assert]s *)
  (*  inline in [echo_Hinit_boot]'s proof.  The record and this lemma are   *)
  (*  the same content named once, which is what lets the seam take a pair  *)
  (*  where it took fifteen arguments.                                     *)
  (*                                                                       *)
  (*  The families, in the record's order: the per-position credential on   *)
  (*  the lease is the cursor's own pin; its mid-line pieces are the        *)
  (*  lease's; the loop's write credential is the era's TIGHT family        *)
  (*  ([EchoLinksLine.ewc_lcred] at the era's stamp, step 4); the           *)
  (*  banner-owed one is [UInitBanner.kinit_ban]; the round-open one is the *)
  (*  prompt credential /init keeps across its fork.                       *)

  Lemma echo_cc_rd_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (γ : echo_fixed) :
    forall i : nat, Timeless (UShLine.ush_rd_pin γ i).
  Proof. apply _. Qed.

  Lemma echo_cc_wb_timeless (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (γ : echo_fixed) :
    forall i : nat, Timeless (UInitBanner.kinit_ban (echo_taint γ) γ i).
  Proof. apply _. Qed.

  Definition echo_cc (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (γ : echo_fixed) : cons_cred Σ :=
    MkConsCred
      (UShLine.ush_rd_pin γ) (echo_cc_rd_timeless HR GEN γ)
      (UShLine.ush_mid γ)
      (EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id))
      (UInitBanner.kinit_ban (echo_taint γ) γ) (echo_cc_wb_timeless HR GEN γ)
      (UInitDiag.kinit_pro (echo_taint γ) γ).

  (*  ...AND THE TEN LAWS, ONCE.  Everything here is Coq level: the links
      ([EchoLinks.echo_links], which the caller proves off the interface
      equation) and the two readings of the supply, which are [Heq]'s.  The
      PROMPT's law is NOT here -- it is an [iProp] the caller holds, so it
      stays a separate argument of the seam. *)
  Lemma echo_cc_holds (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (γ : echo_fixed) (r : echo_names) :
    @file_app Σ HF = MkAppcfg echo_names (echo_pred γ) r ->
    (⊢ EchoLinks.echo_links (echo_taint γ) γ) ->
    cons_cred_holds fsc_cons (echo_taint γ) (echo_cc HR GEN γ).
  Proof.
    intros Heq Hlkc.
    (* THE TWO READINGS OF THE SUPPLY, at Coq level: the console ring's
       dirty credential read AS THE TAINT and back
       ([AppEcho.echo_taint_of_sup] / [echo_sup_of_taint]).  They were
       sh's read leaf's premises until lane ECHO-OUT part 5 made that leaf
       an owed one; [UInitSh.init_cons_sup_of_sh_slot] still reads them
       through [UkInit.init_cons_sup]'s own body. *)
    assert (Htsw : ⊢ echo_taint γ -∗ app_sup).
    { rewrite /app_sup. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "#Ht". iApply (echo_sup_of_taint γ r with "Ht"). }
    assert (Hstw : ⊢ app_sup -∗ echo_taint γ).
    { rewrite /app_sup. rewrite Heq.
      cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "#Hs". iApply (echo_taint_of_sup γ r with "Hs"). }
    (* ...AND SH'S READ LEAF, DISCHARGED (lane IO-LEAF, M5). *)
    assert (Hsh_rdleaf :
      forall (γp : gname) (N : uk_names Σ) (l : list fdstate),
        ukn_pay N = ucons_pay fsc_cons γp (echo_taint γ)
                      (UShLine.ush_rd_x γ (UInitBanner.kinit_ban (echo_taint γ) γ)) ->
        ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp (echo_taint γ)
            (UShLine.ush_mid γ γp) fsc_cons l).
    { intros γp N l Hpeq.
      exact (UShLine.ush_read_recv_leaf_holds γ (echo_taint γ)
               (UInitBanner.kinit_ban (echo_taint γ) γ) N γp l Hpeq Hstw Htsw Hlkc). }
    (* ...AND THE LEASE'S LAWS AND THE ENTRY LAW (lane IO-LEAF, M5(3),
       step 3), at the same one instance. *)
    assert (Hsh_pm1 :
      forall (γp : gname) (N : uk_names Σ) (i : nat),
        ukn_pay N = ucons_pay fsc_cons γp (echo_taint γ)
                      (UShLine.ush_rd_x γ (UInitBanner.kinit_ban (echo_taint γ) γ)) ->
        ⊢ UkSh.ush_at N γp i -∗
          UkSh.ush_lease N γp (echo_taint γ) (UShLine.ush_mid γ γp) i)
      by (intros γp N i Hpeq;
          exact (UShLine.ush_mid_of_at γ (echo_taint γ) (UInitBanner.kinit_ban (echo_taint γ) γ)
                   N γp i Hpeq)).
    assert (Hsh_pm3 :
      forall (γp : gname) (N : uk_names Σ) (i : nat),
        ukn_pay N = ucons_pay fsc_cons γp (echo_taint γ)
                      (UShLine.ush_rd_x γ (UInitBanner.kinit_ban (echo_taint γ) γ)) ->
        ⊢ echo_taint γ -∗ UShLine.ush_mid γ γp i -∗
          UkSh.ush_at N γp i)
      by (intros γp N i Hpeq;
          exact (UShLine.ush_at_of_mid_taint γ (echo_taint γ) (UInitBanner.kinit_ban (echo_taint γ) γ)
                   N γp i Hpeq)).
    assert (Hsh_pmwb :
      forall (γp : gname) (N : uk_names Σ) (i : nat),
        ukn_pay N = ucons_pay fsc_cons γp (echo_taint γ)
                      (UShLine.ush_rd_x γ (UInitBanner.kinit_ban (echo_taint γ) γ)) -> UkSh.ush_bnd i ->
        ⊢ UShLine.ush_mid γ γp i -∗ UInitBanner.kinit_ban (echo_taint γ) γ i -∗
          UkSh.ush_at N γp i)
      by (intros γp N i Hpeq Hb;
          exact (UShLine.ush_at_of_mid_wb γ (echo_taint γ) (UInitBanner.kinit_ban (echo_taint γ) γ)
                   N γp i Hpeq Hb)).
    (* ...AND THE WRITE CREDENTIAL'S STEP AT THE READ, and the boundary law
       with the loop's credential slot beside it (lane IO-LEAF, M6a(3)); the
       credential family is [EchoLinksLine.ewc_lcred] at this era (step 4);
       the read leaves the BLOCK-OWED credential (index 3). *)
    assert (Hsh_wc :
      forall (γp : gname) (n : nat),
        ⊢ UShLine.ush_mid γ γp (n + length EchoDisc.echo_line)%nat -∗
          EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id) n 2%nat -∗
          UShLine.ush_mid γ γp (n + length EchoDisc.echo_line)%nat
          ∗ EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id) (n + length EchoDisc.echo_line)%nat 3%nat)
      by (intros γp n; exact (UShLine.ush_mid_wc_read_t γ (echo_taint γ) γp n)).
    assert (Hsh_bd :
      forall (γp : gname) (N : uk_names Σ) (l : list fdstate) (i : nat),
        ukn_pay N = ucons_pay fsc_cons γp (echo_taint γ)
                      (UShLine.ush_rd_x γ (UInitBanner.kinit_ban (echo_taint γ) γ)) ->
        ⊢ upos γp i -∗
          ucons_pay fsc_cons γp (echo_taint γ) (UShLine.ush_rd_pin γ) (-1) -∗
          (UkSh.ush_wcp (EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id))
             (UInitBanner.kinit_ban (echo_taint γ) γ) l i 0%nat ∨ echo_taint γ) -∗
          UkSh.ush_posb N γp (echo_taint γ)
            (EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id))
            (UInitBanner.kinit_ban (echo_taint γ) γ) (UShLine.ush_mid γ γp) l 0%nat)
      by (intros γp N l i Hpeq;
          exact (UShLine.ush_posb_of_lend γ (echo_taint γ) N γp
                   (EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id))
                   (UInitBanner.kinit_ban (echo_taint γ) γ) l i Hpeq)).
    (* THE ROUND-OPEN CREDENTIAL IS THE PROMPT CREDENTIAL AT THE SHELL'S
       ENTRY (lane M6b): [UInitDiag.kinit_pro n] is one arm of
       [UInitBanner.kinit_own n]; at the tight family (step 4) the
       round-open shape is [EchoLinksLine.ewc_line]'s own first arm. *)
    assert (Hpw : forall n : nat,
              ⊢ UInitDiag.kinit_pro (echo_taint γ) γ n -∗
                EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id) n 0%nat).
    { intros n. iIntros "H".
      rewrite /UInitDiag.kinit_pro /EchoLinksLine.ewc_lcred.
      iDestruct "H" as (v) "[#Hpin Hc]". iExists v. iFrame "Hpin".
      cbn [EchoLinksLine.ewc_lpr]. iApply (EchoLinksLine.ewc_line_of_pro (echo_taint γ) v n).
      rewrite /EchoLinksPro.ewc_pro /EchoLinksLine.ewc_pro.
      iDestruct "Hc" as "[Hl | #HT]"; [ | iRight; iExact "HT" ].
      iDestruct "Hl" as (ps cs P) "(%Hw & Htn & #Hps & #Hcs & #HE)".
      iLeft. iExists ps, cs, P. iFrame "Htn Hps Hcs HE".
      iPureIntro. exact (proj1 Hw). }
    (* ...AND THE THREE CONVERSIONS OF STEP 4, at the tight family: the
       banner-owed credential is a boundary credential ([EchoLinksBan.
       ewc_ban_line]); a block owed is one too ([EchoLinksLine.
       ewc_lcred_blk_line]); a line read at an unwritten prompt is the
       taint ([UShLine.ush_wb_read_holds]). *)
    assert (Hsh_wbwc : forall n : nat,
              ⊢ UInitBanner.kinit_ban (echo_taint γ) γ n -∗
                EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id) n 0%nat).
    { intros n. iIntros "H". rewrite /UInitBanner.kinit_ban /EchoLinksLine.ewc_lcred.
      iDestruct "H" as (v) "[#Hpin Hc]". iExists v. iFrame "Hpin".
      cbn [EchoLinksLine.ewc_lpr].
      iApply (EchoLinksBan.ewc_ban_line (echo_taint γ) v n with "Hc"). }
    assert (Hsh_wbl : forall n : nat,
              ⊢ EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id) n 3%nat -∗
                EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id) n 0%nat)
      by (intros n; exact (EchoLinksLine.ewc_lcred_blk_line (echo_taint γ) γ (S gen_id) n)).
    assert (Hsh_wbr : forall (γp : gname) (n : nat),
              ⊢ UShLine.ush_mid γ γp (n + length EchoDisc.echo_line)%nat -∗
                UInitBanner.kinit_ban (echo_taint γ) γ n -∗
                UShLine.ush_mid γ γp (n + length EchoDisc.echo_line)%nat ∗ echo_taint γ).
    { intros γp n. rewrite /UInitBanner.kinit_ban.
      exact (UShLine.ush_wb_read_holds γ (echo_taint γ) γp n). }
    rewrite /cons_cred_holds /echo_cc /=.
    split_and!; assumption.
  Qed.


  (* ===================================================================== *)
  (*  WHICH DEPOSIT INSTANCE THIS ASSEMBLY RUNS AT, and why it is written   *)
  (*  down rather than resolved.                                           *)
  (*                                                                       *)
  (*  /init runs at [UexecExecInst.uprogSG_free] and it MUST: its           *)
  (*  [UkRun.udep] is a premise of [UInitKernel.init_slot_of_kexec], and at *)
  (*  the ambient [uprogSG_gen] that deposit is [box Dsup] with [Dsup :=    *)
  (*  xv6_ssupply := AppInv.app_sup] -- the application's supply, which for *)
  (*  the echo era is interderivable with the taint                        *)
  (*  ([AppEcho.echo_sup_of_taint] / [echo_taint_of_sup]).  A slot built at *)
  (*  [gen] outside the taint arm would therefore be a VACUOUS ARM, which   *)
  (*  the lane's ruling forbids.  The same holds one level up for the       *)
  (*  shell: [UInitSh.init_exec_sup_of_sh_slot] and                         *)
  (*  [UShKernel.sh_slot_of_kexec] are at the free instance too.            *)
  (*                                                                       *)
  (*  SO EVERY DEPOSIT POSITION NAMES IT: [UexecExecMint.udep_free],        *)
  (*  [UkInit.init_deps (PS := uprogSG_free)], [UkSh.sh_deps (PS :=         *)
  (*  uprogSG_free)], [UkInit.init_cons_sup (PS := uprogSG_free)],          *)
  (*  [UInitKernel.init_boot_con (PS := uprogSG_free)].  Per-lemma, never a *)
  (*  section binder and never a [Local Existing Instance]: [uprogSG_gen]   *)
  (*  stays the one instance resolution finds, because the GENERIC slot --  *)
  (*  the safety net the taint arm falls back on -- is that instance by     *)
  (*  design.                                                               *)
  (*                                                                       *)
  (*  At [uprogSG_free], [psok] IS [UexecSG.free_num], which is why the     *)
  (*  [(fun k H => H)] below is the identity rather than a proof.           *)
  (* ===================================================================== *)
  Lemma echo_Hinit_boot
      (HR : riscvGS Σ) (GEN : GenId)
      `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
        HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ}
      (γ : echo_fixed) (r : echo_names) :
    (* ---- the arc's remaining obligations, by lane ---- *)
    (* [Rsh] IS NO LONGER A PARAMETER (lane SH-STATE): sh's state payload is
       proved here ([UInitSh.sh_pay_state_holds]) and it fixes the family --
       [UInitSh.sh_Rsh], the loop's own data at the break the exec'd key
       pins.  What is still owed is the TAIL at that same family. *)
    (* THE FREE WRITE LAW IS NO LONGER OWED (lane EXEC-SEAM, (D)): the
       paid walks spend write's deposit under the taint, where it is the
       supply's ([UexecExecMint.udepw_law_of_sup_write]), or through the
       closed-fd leaf where the console never opened. *)
    (* THE REST-OF-LINE OBLIGATION IS NO LONGER OWED EITHER (lane R3):
       it is discharged below at the echo era's own credential families
       ([UShRest.sh_rest_holds]), so NOTHING about the shell's program is
       assumed by the top theorem any more. *)
    (* SH'S READ LEAF IS NO LONGER OWED (lane IO-LEAF, M5).  It was a
       Coq-level premise here from lane ECHO-OUT part 5, because the
       boundary's flat input licence is FALSE at [AppEcho.echo_in]'s real
       claim -- moving [dl] needs the READER's half of [EchoOut.dl_cnt],
       and sh's lease did not carry it.  It does now: the half is
       [UserConsole.ucons_pay]'s [Rd], instantiated below at
       [UShLine.ush_rd_pin γ], under the same existential as the cursor,
       so it round-trips through /init's wait like the token itself.  The
       discharge is [UShLine.ush_read_recv_leaf_holds], applied in the
       proof, and [UInitBootAdequacy]'s [Hsh_owed] is GONE (lane R3). *)
    (* ---- and the two equations [Hinit_boot] hands over ---- *)
    @file_app Σ HF = MkAppcfg echo_names (echo_pred γ) r ->
    (* ...AND THE INTERFACE EQUATION (redesign R4), ONE where there were
       three.  This file sits ABOVE the instantiation, so it cannot know
       that the machine's tag family is echo's, that its kill credential is
       the taint, or that its console claim is echo's; the top theorem's
       [Hinit_boot] hands the interface over and each of the three is a
       projection of it.  What they buy here: the tag for
       [UConsLine.ush_tag_law], the credential for the taint arm's generic
       mint, and the claim for the port's ONE LICENCE beside the supply --
       an unverified program may [write(2)] on the console and [read(2)] fd
       0, and consoleintr files every accepted byte in the log, and all
       three are events on one resource. *)
    @riscvF_app_iface Σ (@riscv_fixedGS Σ HR) = echo_ifc γ ->
    ⊢ app_inv fsc_fs -∗ echo_boot γ (S gen_id) r -∗
      (* ...AND THE ERA'S TURN (lane CONS-IO milestone F), the application's
         own per-era credential, handed over beside the boot resource.
         Echo does not read it here: it rides the bundle's one linear slot
         ([UInitKernel.init_boot_pay]) into <init>'s entry, where lane
         ECHO-OUT's ledger will spend it. *)
      echo_turn γ (S gen_id) -∗
      |==> init_boot_bundle (bv_unsigned InodeInv.ROOTINO) fdt0.
  Proof.
    intros Heq Hiface.
    (* the three projections, off the one equation *)
    assert (Htag : @riscv_rx_tag Σ (@riscv_fixedGS Σ HR) = echo_tag γ)
      by (rewrite /riscv_rx_tag Hiface; by cbn [echo_ifc ai_tag]).
    assert (Hkill : @riscv_kill_cred Σ (@riscv_fixedGS Σ HR) = echo_taint γ)
      by (rewrite /riscv_kill_cred Hiface; by cbn [echo_ifc ai_kill]).
    assert (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ HR) = echo_cons γ)
      by (rewrite /riscv_cons_res Hiface; by cbn [echo_ifc ai_cons]).
    (* THE CREDENTIAL IS THE TAINT (lane KILL-PAY, K1), which is what pays
       a KILLED shell's exit payload (K4(a)): [UserConsole.ucons_pay]'s
       right arm is the taint, and the equation is known exactly here. *)
    assert (Hktaint : ⊢ □ riscv_kill_cred -∗ echo_taint γ).
    { rewrite Hkill. iIntros "#H". iExact "H". }
    (* ...AND THE LICENCE IS THE TAINT'S (redesign R2).  The generic slot's
       console write, its read and consoleintr's shift are paid out of the
       TAINT ARM -- exactly what [App.al_sup] says and what
       [EchoOut.ecl_sup] proves.  A wand from the credential, because the
       only holder of a generic slot is one the taint has already accounted
       for.  ONE licence where there were two: lane OUT-FUPD's and lane
       CONS-IO's are both [WpUart.cons_licence] now. *)
    iAssert (□ (echo_taint γ -∗ cons_licence))%I as "#Hlic".
    { iIntros "!> #Ht". rewrite /cons_licence Hcons /echo_cons.
      iIntros "!>" (k h H ev) "Ho".
      iApply (EchoOut.ecl_sup (echo_taint γ) γ k h H ev with "Ht Ho"). }
    iIntros "#Hinv Hb Hturn". iModIntro.
    (* ---- THE ERA'S PIN, out of the turn and back (lane R3).  The pin is
           persistent and the turn is not, so the pin is read off here and
           the turn re-sealed unchanged; [UShRest.sh_rest_holds] needs the
           pin to say what a KILLED child's write credential is, and the
           shell's slot is assembled (persistently) before the turn is
           spent at the end of this proof. ---- *)
    iAssert ((∃ v : era_pins, era_pin γ (S gen_id) v)
             ∗ echo_turn γ (S gen_id))%I
      with "[Hturn]" as "[#Hpine Hturn]".
    { rewrite /echo_turn /EchoOut.eturn.
      iDestruct "Hturn" as (v0) "(#Hp0 & Ht1 & Ht2 & Ht3 & Ht4 & Ht5)".
      iSplitR; [ iExists v0; iExact "Hp0" | ].
      iExists v0. iFrame "Hp0 Ht1 Ht2 Ht3 Ht4 Ht5". }
    (* ---- the taint's supply, and the generic slot it buys ---- *)
    iAssert (□ (echo_taint γ -∗ app_sup))%I as "#Hsup".
    { rewrite /app_sup. rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "!> #Ht". iApply (echo_sup_of_taint γ r with "Ht"). }
    iPoseProof LinkUserinit.UG.uexec_wp_gen as "#Hwp".
    iAssert (□ (∀ (R : iProp Σ) (W : uvis),
                  echo_taint γ -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
                  □ (riscv_kill_cred -∗ R) -∗ uslot W))%I as "#Hmint".
    { iIntros "!>" (R W) "#Ht Hp #HR".
      iDestruct ("Hsup" with "Ht") as "#Hs".
      (* the kill credential IS the taint at this application (K1), and the
         generic slot's supply is the pair (§1c) *)
      iAssert (□ riscv_kill_cred)%I as "#Hkc";
        [ rewrite Hkill; iModIntro; iExact "Ht" | ].
      iDestruct ("Hlic" with "Ht") as "#Hlc".
      (* (* RA-2: held case here *) THE TAINT ARM'S MINT IS AT AN ARBITRARY
         KEY, which is what RA-2's narrowing bites: [uslot_mint_all] will
         ask for [FdSlots.fdv_all_parked (uvis_fd W)] and this [W] is
         universally quantified here.  Where the fact comes from is the
         SITE THAT SPENDS this arm -- [PinnedExec.pex_slot]'s taint arm,
         applied at the key exec resumed, whose table is the exec'ing
         process's own ([SpecKexec.kexec_image_ok_parked] /
         [exec_key_ok_parked]) -- so the premise travels IN to this
         assertion from there, not out of it. *)
      iApply (uslot_mint_all with "Hs Hkc Hlc Hwp Hp HR"). }
    (* ---- the pins law, and /init's own row out of it ---- *)
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v ∗ (⌜echo_fs_pure v⌝ ∨ echo_taint γ)))%I
      as "#Hfs".
    { rewrite Heq. cbn [AppCfg.app_pred AppCfg.app_run AppCfg.app_names].
      iIntros "!>" (v) "Hp". iApply (echo_fs_pure_acc γ r v with "Hp"). }
    iAssert (□ (∀ v : aview, AppCfg.app_pred AppCfg.app_run v -∗
                  AppCfg.app_pred AppCfg.app_run v ∗ (⌜era0_pins v⌝ ∨ echo_taint γ)))%I
      as "#Hcl".
    { iIntros "!>" (v) "Hp".
      iDestruct ("Hfs" $! v with "Hp") as "[Hp [%Hf | HT]]";
        [ iFrame "Hp"; iLeft; iPureIntro; exact (proj1 Hf)
        | iFrame "Hp"; iRight; iExact "HT" ]. }
    (* ---- /init's three deposits ---- *)
    iAssert (□ UkInit.init_deps (PS := uprogSG_free) (echo_taint γ))%I
      as "#Hdp".
    { iApply (init_deps_of_laws (PSx := uprogSG_free) (echo_taint γ)
                with "[] [] [] []").
      - (* write, under the taint: the supply and the output licence *)
        iModIntro. iIntros "#HT".
        iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] [] []").
        + iApply ("Hsup" with "HT").
        + iApply ("Hlic" with "HT").
        + (* ...AND THE TAINT (design/pipe.md, "The byte queue"): write's
             PIPE arm is the byte queue's write chain, and the generic
             supply pays it out of the kill credential -- which at this
             application IS the taint the arm is already under. *)
          rewrite Hkill. iModIntro. iExact "HT".
      - (* ...and the closed-fd leaf, at every record *)
        rewrite /UkInit.kinit_wcl. iIntros "!>" (N0 b).
        iApply (UkWriteClosed.kinit_w1_of_closed_l0 (PS := uprogSG_free) N0 b).
      - iModIntro. iIntros "HT".
        iApply (udepw_law_of_sup (PSx := uprogSG_free) 15
                  (or_introl eq_refl)).
        iApply ("Hsup" with "HT").
      - iModIntro. iIntros "HT".
        iApply (udepw_law_of_sup (PSx := uprogSG_free) 17
                  (or_intror eq_refl)).
        iApply ("Hsup" with "HT"). }
    (* ---- the tag's reading: E2's own, off the theorem's equation ---- *)
    iAssert (UkSh.ush_tag_law (echo_taint γ)) as "#Htg".
    { rewrite /UkSh.ush_tag_law. iIntros "!>" (h) "Hr".
      rewrite Htag /echo_tag /EchoOut.etag.
      iDestruct "Hr" as "[_ Hr]". iExact "Hr". }
    (* THE LINKS, ONCE: the law the read leaf and the banner both spend,
       proved exactly where the record's four equations are. *)
    iAssert (EchoLinks.echo_links (echo_taint γ) γ) as "#Hlks";
      [ iApply (EchoLinks.echo_links_holds (echo_taint γ) γ Hcons) | ].
    assert (Hlkc : ⊢ EchoLinks.echo_links (echo_taint γ) γ)
      by (iApply (EchoLinks.echo_links_holds (echo_taint γ) γ Hcons)).
    (* ---- /echo's PINNED ENTRY, as the paid child's law needs it (lane
           R3): the file-system invariant, the claim law projected at
           echo's pins, and the taint's generic mint -- the three pieces
           already in hand. ---- *)
    iAssert (UShEcho.sh_echo_slot (echo_taint γ)) as "#Hslot".
    { iApply UShEcho.sh_echo_slot_of_fs_pure_holds.
      rewrite /UShEcho.sh_echo_slot_of_fs_pure.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hfs" | iExact "Hmint" ]. }
    (* ---- the shell's slot, and the exec supply as a wand from the
           console credential ---- *)
    (* THE FAMILIES, ONCE (step 3): the write credential is the era's at
       a line boundary ([EchoLinksLine.ewc_lcred], the TIGHT family --
       step 4), the banner-owed one is
       /init's round head ([UInitBanner.kinit_ban]), the lend is the
       lease's read side ([UShLine.ush_rd_pin]) and the exit family the
       pair of the last two ([UShLine.ush_rd_x] = [UkInit.init_rd]). *)
    iAssert (UInitSh.init_sh_slot (echo_taint γ)
               (UInitSh.sh_pay (echo_taint γ)
                  (EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id))
                  (UInitBanner.kinit_ban (echo_taint γ) γ) (UShLine.ush_mid γ)
                  UInitSh.sh_Rsh 0%nat))%I as "#Hsh".
    { rewrite /UInitSh.init_sh_slot /UInitSh.init_sh_slot_core.
      iSplitR; [ iExact "Hinv" | ]. iSplitR; [ iExact "Hfs" | ].
      iSplitR; [ iExact "Hmint" | ].
      iApply (UInitSh.sh_pay_of_parts (echo_taint γ)
                (EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id))
                (UInitBanner.kinit_ban (echo_taint γ) γ) (UShLine.ush_mid γ)
                UInitSh.sh_Rsh 0%nat
                with "[] [] Htg");
        [ iApply UInitSh.sh_pay_state_holds | ].
      (* THE TAIL, AT THE ERA'S FAMILIES (lane R3).  [UInitBanner.kinit_ban]
         IS the banner-owed family spelled at the era's pin, and
         [UShRest.sh_rest_holds] is stated at that spelling, so the one
         unfolding here is the same one [echo_cc_holds] does above. *)
      iIntros (γp N). rewrite /UInitBanner.kinit_ban.
      iApply (UShRest.sh_rest_holds (echo_taint γ) γ γp N Hktaint
                with "Hlks [] Hslot Hpine").
      iApply (udep_free). }
    (* ...AND THE PROMPT'S LAW AT EVERY LINE BOUNDARY, off the links *)
    iAssert (UShKernel.sh_prompt_law (PS := uprogSG_free) (EchoLinksLine.ewc_lcred (echo_taint γ) γ (S gen_id)))%I
      as "#Hplaw".
    { iApply (UShPanic.sh_prompt_law_holds_line (echo_taint γ) γ (PS := uprogSG_free)
                with "Hlks"). }
    (* THE FAMILIES, ONCE MORE (M6b): the round-open credential /init keeps
       across its fork is [UInitDiag.kinit_pro], and the banner leaves it
       ([kinit_banner_law_pro_holds]). *)
    iAssert (UkInit.init_cons_sup fsc_cons (echo_taint γ)
               (init_cons_cred (echo_taint γ) r) init_cons_fd
               (UInitDiag.kinit_pro (echo_taint γ) γ)
               (UInitBanner.kinit_ban (echo_taint γ) γ)
               (UShLine.ush_rd_pin γ))%I as "#Hxs".
    { iApply (init_cons_sup_of_sh_slot γ r fsc_cons init_cons_fd
                (echo_cc HR GEN γ)
                UInitSh.sh_Rsh 0%nat Heq (fun k H => H)
                ltac:(vm_compute; discriminate)
                ltac:(reflexivity)
                (echo_cc_holds HR GEN γ r Heq Hlkc)
                with "[] [] Hplaw Hsh").
      - iApply (udep_free).
      - (* sh's write deposit, under the taint (lane EXEC-SEAM, (D)) *)
        iModIntro. iIntros "#HT".
        iApply (udepw_law_of_sup_write (PSx := uprogSG_free) with "[] [] []").
        + iApply ("Hsup" with "HT").
        + iApply ("Hlic" with "HT").
        + rewrite Hkill. iModIntro. iExact "HT". }
    (* ---- THE CONSOLE DANCE, at whichever arm the VIEW decided
           ([AppEcho.echo_boot]).  Built through [UInitKernel]'s two intro
           lemmas, which is the one place this file names its vocabulary:
           the [ctokG] instance is [Xv6G.xv6_ctok] here and a section
           VARIABLE there, and that unification happens at THESE
           applications rather than inside [UkInit]'s wand tower. ---- *)
    iAssert (UInitKernel.init_cons_dance_all (PS := uprogSG_free)
               (echo_taint γ) (init_cons_cred (echo_taint γ) r)
               init_cons_fd)%I with "[Hb]" as "Hdn".
    { rewrite /echo_boot. iDestruct "Hb" as "[HK | [%i #Hm]]".
      - iApply (UInitKernel.init_cons_dance_all_miss (PS := uprogSG_free)
                  (echo_taint γ) (init_cons_cred (echo_taint γ) r)
                  (cons_key r) init_cons_fd with "[] HK").
        iApply (init_cons_leaves_echo γ r Heq with "Hinv").
      - iApply (UInitKernel.init_cons_dance_all_hit (PS := uprogSG_free)
                  (echo_taint γ) (init_cons_cred (echo_taint γ) r)
                  init_cons_fd with "[] []").
        + iApply (init_cons_hit_echo γ r i Heq with "Hm Hinv").
        + iApply (init_cons_cred_made_echo γ r i with "Hm"). }
    (* ---- /init's own entry, as the bundle's constructor wand ---- *)
    iAssert (□ (∀ W' : uvis,
                  ⌜kexec_image_ok ElfUser.init_elf 1%nat (fun _ => 5%nat)
                     (fun _ => init_boot_bytes) fdt0 W'⌝ -∗
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  my_pay (uvis_gen W') (fun _ => True)%I -∗
                  UInitKernel.init_boot_pay (PS := uprogSG_free)
                    (echo_taint γ)
                    (init_cons_cred (echo_taint γ) r)
                    fsc_cons init_cons_fd
                    (UInitDiag.kinit_pro (echo_taint γ) γ)
                    (UInitBanner.kinit_ban (echo_taint γ) γ)
                    (UShLine.ush_rd_pin γ)
                    -∗ uslot W'))%I as "#Hcon".
    { iApply (UInitKernel.init_boot_con (PS := uprogSG_free)
                (echo_taint γ)
                (init_cons_cred (echo_taint γ) r) init_cons_fd
                (UInitDiag.kinit_pro (echo_taint γ) γ)
                (UInitBanner.kinit_ban (echo_taint γ) γ)
                (UShLine.ush_rd_pin γ)
                fsc_cons
                1%nat (fun _ => 5%nat) (fun _ => init_boot_bytes) fdt0 0%nat
                init_cons_fd_ne Hktaint
                (init_boot_room 0%nat
                                   ltac:(vm_compute; discriminate))
                fdt0_length eq_refl (fdv_nopipe_closed _) (fun k H => H)
                with "[] [] Hxs").
      - iModIntro. iExact "Hdp".
      - iApply (udep_free). }
    iApply (init_boot_bundle_of_pinned (echo_taint γ)
              (UInitKernel.init_boot_pay (PS := uprogSG_free)
                 (echo_taint γ)
                 (init_cons_cred (echo_taint γ) r) fsc_cons init_cons_fd
                 (UInitDiag.kinit_pro (echo_taint γ) γ)
                 (UInitBanner.kinit_ban (echo_taint γ) γ)
                 (UShLine.ush_rd_pin γ))
              with "Hcl Hinv Hcon [] [Hdn Hturn]").
    - iIntros "!>" (W') "#Ht Hp".
      iApply ("Hmint" $! True%I W' with "Ht Hp []").
      iModIntro. iIntros "_". done.
    - iIntros "Hrd". rewrite /UInitKernel.init_boot_pay.
      (* THE READER'S RECEIPT RESIDUE AT COUNT ZERO (step 4): the era's
         own turn -- the writer's cursor at 0 and the two empty bounds --
         is the receipt of the nothing read so far, at the era's pin *)
      iAssert (∃ v0 : era_pins, era_pin γ (S gen_id) v0 ∗ UShLine.rd_res v0 0%nat)%I
        with "[Hturn]" as "(%v0 & #Hpin0 & #Hres0)".
      { rewrite /echo_turn /EchoOut.eturn.
        iDestruct "Hturn" as (v0) "(#Hpin0 & Htn & _ & #Hcs0 & #Hps0 & _)".
        iExists v0. iFrame "Hpin0". rewrite /UShLine.rd_res.
        iExists [], []. iEval (rewrite /EchoOut.turn) in "Htn".
        iDestruct (mono_nat_lb_own_get with "Htn") as "#Hlb0".
        assert (E0 : length (proc_upto [] [] 0%nat) = 0%nat)
          by (vm_compute; reflexivity).
        rewrite E0. iFrame "Hlb0 Hps0 Hcs0". iPureIntro.
        exact EchoOut.rd_stage_0. }
      iDestruct (UInitBanner.kinit_ban0_of_eturn (echo_taint γ) γ
                   with "[Hturn]")
        as "[Hdl Hbn]"; [ rewrite /echo_turn; iExact "Hturn" | ].
      (* THE THREE LAWS (lane M6b): the banner leaves the round-open
         credential, and the two diagnostics are paid from it -- all
         closed under the era's links ([UInitDiag]). *)
      iDestruct (UInitDiag.kinit_banner_law_pro_holds (echo_taint γ) γ
                   (PS := uprogSG_free) with "Hlks") as "#Hblaw".
      iDestruct (UInitDiag.kinit_execfail_law_holds (echo_taint γ) γ
                   (PS := uprogSG_free) with "Hlks") as "#Hxlaw".
      iDestruct (UInitDiag.kinit_forkfail_law_holds (echo_taint γ) γ
                   (PS := uprogSG_free) with "Hlks") as "#Hflaw".
      iSplitL "Hdn"; [ iExact "Hdn" | ].
      iSplitL "Hrd"; [ rewrite ucons_reader_eq; iExact "Hrd" | ].
      iSplitL "Hdl".
      { (* ...and the count it is at IS a line boundary: it is ZERO (lane
           IO-LEAF, M5(3)). *)
        rewrite /UShLine.ush_rd_pin /UInitBanner.kinit_dl0.
        iSplitR; [ iPureIntro; exact UkSh.ush_bnd_0 | ].
        iDestruct "Hdl" as (v) "(#Hpin & Hdl & #HE)".
        iDestruct (era_pin_agree with "Hpin0 Hpin") as %<-.
        iExists v0. iFrame "Hpin0 Hdl HE Hres0". }
      (* THE ERA'S CREDENTIAL BECOMES /init's BANNER PAYMENT (lane IO-LEAF,
         M1(e)).  This is the one place where the application's claim and
         the kernel's console contracts are the same object AND row 16's
         concrete reading is in scope, which is why the conversion lives
         above [UkWriteLeaf] and reaches <init>'s walk as a premise. *)
      (* ...AND IT NO LONGER SPENDS THE FREE WRITE LAW (lane IO-LEAF,
         M1(f)): /init's two dups pin fds 1 and 2 to the console, so the
         payment has ONE row to answer for and [Hsh_deps] is not a premise
         of it any more.  [Hsh_deps] still stands above -- init's three die
         arms and [UkInit.init_deps] spend it (M4/M6). *)
      iSplitL "Hbn"; [ iExact "Hbn" | ].
      iSplitR; [ iExact "Hblaw" | ].
      rewrite /UkInitMain.kinit_diag_law.
      iSplitR; [ iExact "Hxlaw" | iExact "Hflaw" ].
  Qed.

End EchoInitBoot.

