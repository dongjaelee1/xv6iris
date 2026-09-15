(* ===================================================================== *)
(* UInitSh.v -- init's OWN exec deposit: the PINNED bundle for /sh, and    *)
(* the reading of init's image that prices sh's frames.                   *)
(*                                                                        *)
(* [UkInit.init_exec_sup] is what init's proof carries in place of         *)
(* [UkRun.uxsup] -- the exec deposit at init's OWN two argument registers  *)
(* (a0 = 0x9a8, the string "sh" in its rodata; a1 = 0x1000, the argument   *)
(* vector in its .data) and at the ONE working directory it ever has       *)
(* ([FsImg.ROOTINO]).  This file is where that supply is PAID, out of the  *)
(* application's claim that /sh is the file [ElfUser.sh_elf]:              *)
(*                                                                        *)
(*   [init_sh_slot T Pay]  the four persistent ingredients -- the          *)
(*                         file-system invariant, the duplicating claim    *)
(*                         law at [FsShPin.era0_sh_pins], the taint's      *)
(*                         generic slot, and sh's entry payload [Pay].     *)
(*   [init_args_det]       INIT'S ARGUMENTS ARE DETERMINED BY ITS IMAGE.   *)
(*   [init_exec_sup_of_sh_slot]  the assembly.                             *)
(*                                                                        *)
(* WHY THE READING IS NEEDED.  [UShKernel.sh_slot_of_kexec] prices sh's    *)
(* frames against [kxc_sp_final], which is a function of the argument      *)
(* COUNT and LENGTHS -- and the exec channel offers those only as bound    *)
(* variables.  [SpecSysExec.exec_args_of] ties them to the caller's own    *)
(* image, and init's image is a constant: the word at 0x1000 is the        *)
(* pointer 0x9a8, the word at 0x1008 is NULL, and the string at 0x9a8 is   *)
(* "sh".  So [na = 1] and [alen 0 = 2], and the room premise is closed     *)
(* arithmetic ([kxc_sp_final 0x5000 alen 1 = 0x4FE0], and sh's frames need *)
(* 0x4000 + 8 * (106 + n0) below the top of its image).                    *)
(*                                                                        *)
(* WHY IT IS NOT IN THE u-TIER.  The last step is                          *)
(* [UexecExecInst.sbundle_exec_intro], which is proved at the KERNEL's     *)
(* instance of [UexecSG.uexecSG]; [UkInitMain.v] and [UInitKernel.v] are   *)
(* stated over the CLASS, with the instance a section variable.  Importing *)
(* the instance into either of them would put two [sbundle]s that print    *)
(* identically in scope, and would make [UexecSG.psok] resolve to          *)
(* [uprogSG_gen]'s trivial one -- every [psok] premise vacuously true.     *)
(* So the u-tier speaks [UkInit.init_exec_sup] and this file, above the    *)
(* instance, is what pays it.                                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvModelBytes.
Require Import WpMmodeLeafBase.  (* [csp_rs1] *)
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
(* THE GHOST BINDER LIST, each module IMPORTED and not merely required:
   naming [xv6G] / [fileG] / [irefslotG] / [pavG] without their defining
   module in scope introduces a FRESH Type variable instead of the class,
   and the kernel's [uexecSG] instance is then invisible to resolution.
   [PinnedExec.v]'s header is the note. *)
Require Import Xv6G.            (* [xv6G] *)
Require Import FdSlots.         (* [fdslotG], [fdstate] *)
Require Import IrefSlots.       (* [irefslotG] *)
Require Import ProcAvail.       (* [pavG] *)
Require Import FileInvDefs.     (* [fileG], and its [appcfg] / [icfg] fields *)
Require Import UserFd.
Require Import UserHeap.
Require Import ChildTok.  (* [my_pay]: the exec wands' pay fact *)
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UInitFd.  (* [ufd_head] / [ufd_head_row] -- init's own
                            descriptor head, and the row sh's entry reads
                            off it against the lent authority *)
Require Import UkRun.
Require Import UkRunExecRef.    (* [udepw_at_refR] / [sbundle_pay_refR]: the
                                   exec deposit at the LEND's own refund
                                   (lane M6b) *)
Require Import UCodeInit UkInit.
Require Import UkSh UShKernel.
Require Import UkShParse.       (* the two lexer tables' addresses and
                                   content functions, which sh's static
                                   state is made of *)
Require Import UkShLoop.        (* [ushl_dat] -- sh's opaque static state *)
Require Import ElfFile.         (* [elf_image] / [elf_zero_byte] *)
Require Import BlockWords.      (* [nth_byte_zero] *)
Require User.ShData User.ShInstrs.
Require Import PathElems.          (* [path_elems] *)
Require Import ElfUser.
Require Import ElfLoadable.        (* [sh_elf_loadable] *)
Require Import EchoFsPure.         (* [echo_fs_pure] -- the WHOLE pins law
                                      sh is handed (lane E4: its own exec of
                                      /echo needs [FsEchoPin.era0_echo_pins],
                                      which is one of its conjuncts).  A PURE
                                      [Prop], so naming it costs nothing; the
                                      era's console GHOSTS are deliberately
                                      NOT named here -- see the note at
                                      [init_sh_slot]. *)
Require Import EchoOut.            (* [echoOutG]: the class [AppEcho]'s claims
                                      and its ledger are stated at (lane
                                      ECHO-OUT part 5).  It CARRIES
                                      [mono_natG], so it is the taint's one
                                      instance here too. *)
Require Import PageGeom.           (* [PGSIZE] *)
Require Import KexecDefs.
Require Import SpecKexec.
Require Import SpecCopyin.         (* [uimg_word_at] *)
Require Export UImgWordDefs.  (* [img_word_of_bytes], [uimg_word_det]
                                 -- split out of this file for [UShEcho].
                                 EXPORT: existing importers unchanged. *)
Require Import SpecSysExec.        (* [exec_args_of] / [exec_path_of] *)
Require Import AppCfg AppInv.
Require Import FsCfg.
Require Import FsImgCheck.         (* [fname_sh] *)
Require Import FsShPin.            (* [era0_sh_pins] / [sh_path] / [SH_INO] *)
Require Import FsAbsDefs.          (* [aview] / [arun] / [AFile] *)
Require Import PinnedExec.
Require Import PieceFam.           (* [pfam] / [MkPfam] -- the exec deposit's
                                      one-shot piece, named by the refund
                                      twin below (lane M6b) *)
Require Import FsBytesGamma.       (* [fs_gamma_L] -- likewise *)
Require Import UexecExecInst.      (* [sbundle_exec_intro] -- THE INSTANCE *)
Require Import Xv6Cameras.         (* [uartGhostG] *)
Require Import UartNames.          (* [cons_names] *)
Require Import UserConsole.        (* [ucons_pay] / [upos] *)
Require Import TsoCtx.
Require User.InitData.
Import Defs.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE PATH init PASSES, as a byte list                              *)
(*                                                                        *)
(*  [SpecSysExec.exec_path_of] reads the caller's string off its image as  *)
(*  a [list (bv 8)]; [FsShPin]'s pin speaks of [FsShPin.sh_path], a list   *)
(*  of NAMES.  The two are joined by [PathElems.path_elems], and at "sh"   *)
(*  the join is the identity on the bytes -- so the byte list is spelled   *)
(*  AS the name, and nothing is retyped.                                   *)
(* ===================================================================== *)
Definition init_sh_pl : list (bv 8) := FsImgCheck.fname_sh.

Lemma init_sh_path_elems : path_elems init_sh_pl = FsShPin.sh_path.
Proof. vm_compute. reflexivity. Qed.

Lemma init_sh_pl_len : length init_sh_pl = 2%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  2.  THE PIN RESOLVES, at init's cwd                                    *)
(* ===================================================================== *)
Lemma init_sh_pin_resolves :
  pin_resolves FsShPin.era0_sh_pins FsImg.ROOTINO init_sh_pl
    [FsImg.ROOTINO; FsShPin.SH_INO] FsShPin.SH_INO ElfUser.sh_elf 1%nat.
Proof.
  split_and!.
  - (* the start: "sh" is RELATIVE, so the walk starts at the cwd -- which
       is the root anyway, so both arms of [um_start_of] agree *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (init_sh_pl !! 0%nat = Some PathElems.SLASH));
      reflexivity.
  - rewrite init_sh_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite init_sh_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsShPin.sh_bytes_elf. reflexivity.
Qed.

(* ===================================================================== *)
(*  3.  INIT'S IMAGE, READ                                                 *)
(*                                                                        *)
(*  Three closed facts about the dump, each one [vm_compute] and nothing   *)
(*  else: the two words of the argument vector, and the three bytes of     *)
(*  the path.  Everything downstream is arithmetic over them.              *)
(* ===================================================================== *)
Lemma init_argv_words_bool :
  forallb (fun k : nat =>
      bool_decide (
        UCodeInit.init_argv_map !! (0x1000 + Z.of_nat k)
          = Some (nth_byte (mword_of_int 0x9a8 : mword 64) k)
        /\ UCodeInit.init_argv_map !! (0x1008 + Z.of_nat k)
          = Some (nth_byte (mword_of_int 0 : mword 64) k)))
    (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma init_argv_words (k : nat) :
  (k < 8)%nat ->
  UCodeInit.init_argv_map !! (0x1000 + Z.of_nat k)
    = Some (nth_byte (mword_of_int 0x9a8 : mword 64) k)
  /\ UCodeInit.init_argv_map !! (0x1008 + Z.of_nat k)
    = Some (nth_byte (mword_of_int 0 : mword 64) k).
Proof.
  intro Hk.
  pose proof (proj1 (forallb_forall _ (seq 0 8)) init_argv_words_bool k
                ltac:(apply in_seq; lia)) as H.
  exact (bool_decide_eq_true_1 _ H).
Qed.

Lemma init_ro_sh_bool :
  bool_decide (
      UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x9a8 : mword 64) (Z.of_nat 0%nat))
      = init_sh_pl !! 0%nat
   /\ UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x9a8 : mword 64) (Z.of_nat 1%nat))
      = init_sh_pl !! 1%nat
   /\ UCodeInit.init_ro
        !! uint (add_vec_int (mword_of_int 0x9a8 : mword 64) (Z.of_nat 2%nat))
      = Some (bv_0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bv0_moi0 : (bv_0 8 : bv 8) = (mword_of_int 0 : mword 8).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [img_word_of_bytes] and [uimg_word_det] MOVED DOWN to
   [UImgWordDefs.v] (re-exported above): they are pure facts about a
   byte map, and [UShEcho] wants exactly those two out of this file. *)

(* ===================================================================== *)
(*  4.  INIT'S ARGUMENTS ARE DETERMINED BY ITS IMAGE                       *)
(*                                                                        *)
(*  Every reading of the argument vector at 0x1000 that [sys_exec] can     *)
(*  perform against an image containing init's .data and .rodata is the    *)
(*  same one: ONE argument, of length two.  That is what prices sh's       *)
(*  frames, and it is why the pinned route needs [exec_args_of] and not    *)
(*  merely [exec_args_shape].                                              *)
(* ===================================================================== *)
Lemma init_args_det (M : gmap Z (bv 8)) (na : nat) (alen : nat -> nat)
    (afun : nat -> nat -> bv 8) :
  uimg_sub UCodeInit.init_argv_map M ->
  uimg_sub UCodeInit.init_ro M ->
  exec_args_of M (mword_of_int 0x1000 : mword 64) na alen afun ->
  na = 1%nat /\ alen 0%nat = 2%nat.
Proof.
  intros Hav Hro (Hshape & avf & Hptr & Hnz & Hnul & Hstr).
  destruct Hshape as (_ & Hcstr & _).
  (* the two windows, in the contract's spelling *)
  assert (Hb0 : forall k : nat, (k < 8)%nat ->
            M !! (0x1000 + Z.of_nat k)
            = bv_to_little_endian 8 8 0x9a8 !! k).
  { apply img_word_of_bytes. intros k Hk.
    exact (Hav _ _ (proj1 (init_argv_words k Hk))). }
  assert (Hb1 : forall k : nat, (k < 8)%nat ->
            M !! (0x1008 + Z.of_nat k)
            = bv_to_little_endian 8 8 0 !! k).
  { apply img_word_of_bytes. intros k Hk.
    exact (Hav _ _ (proj2 (init_argv_words k Hk))). }
  (* ---- the two pointer words ---- *)
  assert (E0 : uint (add_vec_int (mword_of_int 0x1000 : mword 64)
                       (8 * Z.of_nat 0%nat)) = 0x1000)
    by (vm_compute; reflexivity).
  assert (E1 : uint (add_vec_int (mword_of_int 0x1000 : mword 64)
                       (8 * Z.of_nat 1%nat)) = 0x1008)
    by (vm_compute; reflexivity).
  assert (Hne : (mword_of_int 0x9a8 : mword 64) <> mword_of_int 0).
  { intro Hc. apply (f_equal bv_unsigned) in Hc.
    vm_compute in Hc. discriminate Hc. }
  assert (Hna1 : na = 1%nat).
  { destruct (decide (na = 0%nat)) as [-> | Hn0].
    - exfalso. pose proof (Hptr 0%nat (Nat.le_refl 0%nat)) as Hw.
      rewrite E0 in Hw.
      assert (Hz0 : 0 <= 0x9a8 < 2 ^ 64) by (clear; lia).
      rewrite (uimg_word_det M 0x1000 (avf 0%nat) 0x9a8 Hz0 Hw Hb0) in Hnul.
      exact (Hne Hnul).
    - destruct (decide (na = 1%nat)) as [-> | Hn1]; [ reflexivity | exfalso ].
      pose proof (Hptr 1%nat ltac:(lia)) as Hw. rewrite E1 in Hw.
      pose proof (Hnz 1%nat ltac:(lia)) as Hz.
      assert (Hz1 : 0 <= 0 < 2 ^ 64) by (clear; lia).
      exact (Hz (uimg_word_det M 0x1008 (avf 1%nat) 0 Hz1 Hw Hb1)). }
  subst na.
  (* ---- the string at 0x9a8 ---- *)
  split; [ reflexivity | ].
  pose proof (Hptr 0%nat ltac:(lia)) as Hw. rewrite E0 in Hw.
  assert (Hz0 : 0 <= 0x9a8 < 2 ^ 64) by (clear; lia).
  assert (Hp0 : avf 0%nat = (mword_of_int 0x9a8 : mword 64))
    by exact (uimg_word_det M 0x1000 (avf 0%nat) 0x9a8 Hz0 Hw Hb0).
  pose proof (Hstr 0%nat ltac:(lia)) as Hs. rewrite Hp0 in Hs.
  destruct (Hcstr 0%nat ltac:(lia)) as [Hno Hnl].
  pose proof (bool_decide_eq_true_1 _ init_ro_sh_bool) as (Hr0 & Hr1 & Hr2).
  destruct (decide (alen 0%nat = 2%nat)) as [Hok | Hbad]; [ exact Hok | ].
  exfalso.
  destruct (decide (alen 0%nat < 2)%nat) as [Hlt | Hge].
  - (* the string would end at 0x9a8 or 0x9a9, and neither byte is NUL *)
    pose proof (Hs (alen 0%nat) (Nat.le_refl _)) as Hj.
    destruct (decide (alen 0%nat = 0%nat)) as [Hz | Hz].
    + rewrite Hz in Hj. rewrite Hz in Hnl. rewrite (Hro _ _ Hr0) in Hj.
      injection Hj as Hj. rewrite <- Hj in Hnl.
      vm_compute in Hnl. discriminate Hnl.
    + assert (Ha : alen 0%nat = 1%nat) by lia.
      rewrite Ha in Hj. rewrite Ha in Hnl. rewrite (Hro _ _ Hr1) in Hj.
      injection Hj as Hj. rewrite <- Hj in Hnl.
      vm_compute in Hnl. discriminate Hnl.
  - (* ...and past 0x9aa the string would have to continue through a NUL *)
    pose proof (Hs 2%nat ltac:(lia)) as Hj.
    rewrite (Hro _ _ Hr2) in Hj. injection Hj as Hj.
    exact (Hno 2%nat ltac:(lia) (eq_trans (eq_sym Hj) bv0_moi0)).
Qed.

(* ===================================================================== *)
(*  5.  THE INGREDIENTS                                                    *)
(* ===================================================================== *)
(* ===================================================================== *)
(*  4b.  THE BYTES SH'S STATIC STATE IS MADE OF (lane SH-STATE)           *)
(*                                                                        *)
(*  sh's writable PT_LOAD is (vaddr 0x2000, filesz 0x10, memsz 0x98).      *)
(*  The file half is the two lexer tables ([UkShParse.ushp_symbols] at     *)
(*  0x2000, [ushp_whitespace] at 0x2008) and comes off the DUMP; the rest  *)
(*  -- [freep] at 0x2010, sh's line buffer [UkSh.sh_buf] at 0x2020, the    *)
(*  allocator's [base] cell at 0x2088 -- is .bss and comes off             *)
(*  [ElfUser.sh_elf_zero_image].  Both halves are read through             *)
(*  [ElfUser.sh_elf_image_concrete], the NAMED image equation, so nothing  *)
(*  here reduces [sh_elf] (durable-notes, "Name the ELF-bytes equation").  *)
(* ===================================================================== *)

(* the two tables, in the [forallb]-over-[seq] shape [UkSh.ush_jrow_bytes_ok]
   uses: ONE [vm_compute] over the 2532-entry dump, not fourteen *)
Definition sh_tbl_ok : bool :=
  forallb (fun j : nat =>
      bool_decide (ShData.sh_data !! (ushp_symbols + Z.of_nat j)
                   = Some (ushp_sym_f j))) (seq 0 7)
  && forallb (fun j : nat =>
      bool_decide (ShData.sh_data !! (ushp_whitespace + Z.of_nat j)
                   = Some (ushp_ws_f j))) (seq 0 5)
  && bool_decide (ShData.sh_data !! (ushp_symbols + 7) = Some ubyte0)
  && bool_decide (ShData.sh_data !! (ushp_whitespace + 5) = Some ubyte0).

Lemma sh_tbl_ok_true : sh_tbl_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sh_tbl_parts :
  forallb (fun j : nat =>
      bool_decide (ShData.sh_data !! (ushp_symbols + Z.of_nat j)
                   = Some (ushp_sym_f j))) (seq 0 7) = true
  /\ forallb (fun j : nat =>
      bool_decide (ShData.sh_data !! (ushp_whitespace + Z.of_nat j)
                   = Some (ushp_ws_f j))) (seq 0 5) = true
  /\ bool_decide (ShData.sh_data !! (ushp_symbols + 7) = Some ubyte0) = true
  /\ bool_decide (ShData.sh_data !! (ushp_whitespace + 5) = Some ubyte0) = true.
Proof.
  pose proof sh_tbl_ok_true as H. unfold sh_tbl_ok in H.
  apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

(* the dumped .data window IS part of the image *)
Lemma sh_dat_img (a : Z) (b : bv 8) :
  ShData.sh_data !! a = Some b -> elf_image ElfUser.sh_elf !! a = Some b.
Proof.
  intro Hb. rewrite ElfUser.sh_elf_image_concrete.
  assert (Hn : ShInstrs.sh_bytes !! a = None).
  { destruct (ShInstrs.sh_bytes !! a) as [c |] eqn:E; [ exfalso | reflexivity ].
    pose proof (ShInstrs.sh_bytes_range a c E) as Hr.
    pose proof (ShData.sh_data_range a b Hb) as Hr2.
    unfold ShInstrs.sh_bytes_hi, ShInstrs.sh_bytes_lo,
           ShData.sh_data_lo, ShData.sh_data_hi in *. lia. }
  apply lookup_union_Some_l. rewrite lookup_union_r; [ exact Hb | exact Hn ].
Qed.

(* ...and the .bss window is zero *)
Lemma sh_bss_img (a : Z) :
  0x2010 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some ubyte0.
Proof.
  intro Ha. rewrite ElfUser.sh_elf_image_concrete.
  assert (Hn : (ShInstrs.sh_bytes ∪ ShData.sh_data) !! a = None).
  { destruct ((ShInstrs.sh_bytes ∪ ShData.sh_data) !! a) as [c |] eqn:E;
      [ exfalso | reflexivity ].
    apply lookup_union_Some_raw in E as [E | [_ E]].
    - pose proof (ShInstrs.sh_bytes_range a c E) as Hr.
      unfold ShInstrs.sh_bytes_hi, ShInstrs.sh_bytes_lo in Hr. lia.
    - pose proof (ShData.sh_data_range a c E) as Hr.
      unfold ShData.sh_data_lo, ShData.sh_data_hi in Hr. lia. }
  rewrite lookup_union_r; [ | exact Hn ].
  apply lookup_map_seqZ_Some. split.
  - unfold ElfUser.sh_bss_lo. lia.
  - apply lookup_replicate_2. unfold ElfUser.sh_bss_lo, ElfUser.sh_bss_size. lia.
Qed.

Lemma moi0_bv0_64 : (mword_of_int 0 : mword 64) = bv_0 64.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma nth_byte_zero64 (j : nat) :
  nth_byte (mword_of_int 0 : mword 64) j = ubyte0.
Proof.
  rewrite moi0_bv0_64 nth_byte_zero.
  unfold ubyte0. apply bv_eq. vm_compute. reflexivity.
Qed.

(* a WINDOW of a map, in and out.  [UserHeap.umap_split_at]'s twin at a
   half-open interval; RELOCATION ASK: it belongs beside that lemma, and
   is local here only because moving it rebuilds the tier
   ([UkShMain.v]'s SS1 note is the same case. *)
Lemma umap_win_lookup (D : gmap Z (bv 8)) (lo hi a : Z) (b : bv 8) :
  lo <= a < hi -> D !! a = Some b ->
  base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D !! a = Some b.
Proof.
  intros Ha Hb. apply map_lookup_filter_Some.
  split; [ exact Hb | cbn [fst]; exact Ha ].
Qed.

Lemma umap_win_lookup_out (D : gmap Z (bv 8)) (lo hi a : Z) (b : bv 8) :
  ~ (lo <= a < hi) -> D !! a = Some b ->
  base.filter (fun kv : Z * bv 8 => ~ (lo <= kv.1 < hi)) D !! a = Some b.
Proof.
  intros Ha Hb. apply map_lookup_filter_Some.
  split; [ exact Hb | cbn [fst]; exact Ha ].
Qed.

Section UInitSh.
  (* THE KERNEL'S INSTANCE IS AMBIENT: [UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] globally, and this file is where the
     u-tier's class-level statements meet them.  NO [Context {SG}] /
     [Context {PS}] here -- a local instance beside the global one is two
     [sbundle]s that print identically. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* the console ring's cameras: the POSITION init lends sh across the exec
     is stated over them ([UserConsole.upos]) *)
  Context `{!uartGhostG Σ}.
  (* the echo claims' class (lane ECHO-OUT part 5): [AppEcho.echo_taint] and
     everything built over it is stated at [EchoOut.echoOutG] now, not at a
     bare [mono_natG]. *)
  Context `{!echoOutG Σ}.

  (* ------------------------------------------------------------------- *)
  (* sh's ENTRY PAYLOAD, as init holds it.                                 *)
  (*                                                                       *)
  (* The two ∀-quantified persistent pieces [UShKernel.sh_slot_of_kexec]   *)
  (* takes beside the image fact: the wand that produces sh's opaque       *)
  (* static state [R] and its line buffer out of the writable data below   *)
  (* the frame, and the discharge of sh's own tail obligation              *)
  (* ([UkSh.ush_rest]).  Both are PARAMETERS of init's constructor -- the  *)
  (* application (AppEcho) instantiates them -- and both are persistent,   *)
  (* which they must be: init execs inside the fork child, inside an       *)
  (* [iLob] the parent re-enters, so nothing linear can be spent there.    *)
  (*                                                                       *)
  (* [n0] is the slack sh's entry is priced at.  Any [n0] under 402 fits   *)
  (* ([init_sh_room] below); the caller picks one.                         *)
  (* ------------------------------------------------------------------- *)
  (* ITS THREE CONJUNCTS, NAMED (lane E2).  Each is owed by a different
     lane, and the top theorem carries the two it does not own as named
     hypotheses -- so [sh_pay] itself is assembled from the parts rather
     than quoted twice ([sh_pay_of_parts]).  The tag's reading is E2's own
     and is proved from the theorem's [riscv_rx_tag = app_tag] equation. *)
  (* LANE SH-STATE RESTATED THIS.  Two things were wrong with the [∀]-over-
     every-key form: at an arbitrary key nothing pins [uvis_sz W'] to the
     break a turn of the loop carries, and nothing puts sh's writable
     window in the map -- so NO [Rsh] could satisfy it.  Both are the
     entry's own reading of its key, and they enter as
     [UShKernel.sh_pay_key] ([UShKernel.sh_pay_key_of_kexec] is the
     discharge, off [kexec_image_ok] and the room bound).
     ...AND THE CONCLUSION IS AN UPDATE: [UkShLoop.ushl_dat] holds the two
     lexer tables at [DfracDiscarded], and persisting a [DfracOwn 1] byte
     is a frame-preserving update.  The wand is spent inside a [WP]
     ([UShKernel.sh_uexec_slot]), which absorbs it. *)
  Definition sh_pay_state (Rsh : gname -> gname -> gname -> iProp Σ)
      (n0 : nat) : iProp Σ :=
    (□ (∀ (W' : uvis) (γt γd γs : gname),
          ⌜ UShKernel.sh_pay_key W' n0 ⌝ -∗
          usz γs (uvis_sz W') -∗
          ([∗ map] k ↦ b ∈ base.filter
                (fun kv : Z * bv 8 =>
                   kv.1 < uint (tf_resume_gpr0 (uvis_tf W')
                                !!! Regidx csp_rs1)
                          - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
                (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
             ubyte γd k b) -∗
          |==> ∃ f : nat -> bv 8, Rsh γt γd γs ∗ ubytes γd sh_buf sh_nbuf f))%I.

  (* [sh_pay_rest] IS GONE (lane R3).  It was the era-FREE form of the
     tail obligation -- a [forall T Wc Wb Pm] the top theorem assumed --
     and it is not provable in that shape: its one discharger
     ([UkShFork.ushf_rest_of_body]) needs the PAID CHILD's law, a killed
     child's credential and sh's own panic law, all of which are facts
     about the era's families and FALSE for some of them.  The obligation
     is discharged at the echo era's own families instead
     ([UShRest.sh_rest_holds]), which is what [sh_pay]'s second conjunct
     below asks for and what [UInitBoot.echo_Hinit_boot] now proves rather
     than assumes. *)

  Definition sh_pay (T : iProp Σ) (Wc : nat -> nat -> iProp Σ)
      (Wb : nat -> iProp Σ) (Pm : gname -> nat -> iProp Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ)
      (n0 : nat) : iProp Σ :=
    (□ (∀ (W' : uvis) (γt γd γs : gname),
          ⌜ UShKernel.sh_pay_key W' n0 ⌝ -∗
          usz γs (uvis_sz W') -∗
          ([∗ map] k ↦ b ∈ base.filter
                (fun kv : Z * bv 8 =>
                   kv.1 < uint (tf_resume_gpr0 (uvis_tf W')
                                !!! Regidx csp_rs1)
                          - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))))
                (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W')),
             ubyte γd k b) -∗
          |==> ∃ f : nat -> bv 8, Rsh γt γd γs ∗ ubytes γd sh_buf sh_nbuf f)
     (* ...AND THE TAIL AT EVERY POSITION GHOST: init mints a FRESH pair
        per child ([UserConsole.upos_alloc]), so what the application owes
        is sh's body at whichever name this round's pair got. *)
     ∗ (∀ (γp : gname) (N : uk_names Σ),
          ush_rest_l (PS := uprogSG_free) N γp T Wc Wb (Pm γp)
            (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))
     (* ...AND THE TAG'S READING (lane SH-LINE 2b, L4).  How a tagged input
        history is READ -- as the discipline or as the taint -- is a fact
        about the TOP theorem's [boot_fixedGS] equation [riscv_rx_tag =
        app_tag] and nothing below it, so it reaches sh as a premise, and
        this is the slot it rides in ([UConsLine.ush_exec_pay] is the
        shape).  E2 discharges it from that equation, beside init's claim
        law.  LAST, so every existing destructuring of this payload keeps
        working (durable-notes, "Shaping a change so the sweep is small"). *)
     ∗ UkSh.ush_tag_law T)%I.

  (* THE MIDDLE PREMISE IS [sh_pay]'s SECOND CONJUNCT ITSELF (lane R3):
     the tail obligation at THIS era's taint and families, one per
     position ghost.  [UShRest.sh_rest_holds] is what supplies it. *)
  Lemma sh_pay_of_parts (T : iProp Σ) `{!Persistent T}
      (Wc : nat -> nat -> iProp Σ) (Wb : nat -> iProp Σ)
      (Pm : gname -> nat -> iProp Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    sh_pay_state Rsh n0 -∗
    (∀ (γp : gname) (N : uk_names Σ),
       ush_rest_l (PS := uprogSG_free) N γp T Wc Wb (Pm γp)
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N))) -∗
    UkSh.ush_tag_law T -∗
    sh_pay T Wc Wb Pm Rsh n0.
  Proof.
    iIntros "#Hst #Hre #Htg". rewrite /sh_pay /sh_pay_state.
    iSplitR; [ iExact "Hst" | ]. iSplitR; [ iExact "Hre" | iExact "Htg" ].
  Qed.

  Global Instance sh_pay_persistent T Wc Wb Pm Rsh n0 :
    Persistent (sh_pay T Wc Wb Pm Rsh n0).
  Proof. rewrite /sh_pay. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (* THE CARVE (lane SH-STATE): sh's static state and its line buffer,    *)
  (* out of the writable data the entry hands over.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma umap_window (g : gname) (D : gmap Z (bv 8)) (lo hi : Z) :
    ([∗ map] k ↦ b ∈ D, ubyte g k b) -∗
      ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D,
         ubyte g k b)
      ∗ ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => ~ (lo <= kv.1 < hi)) D,
           ubyte g k b).
  Proof.
    iIntros "H".
    rewrite -(big_sepM_union (fun k b => ubyte g k b)
                (base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D)
                (base.filter (fun kv : Z * bv 8 => ~ (lo <= kv.1 < hi)) D)
                (map_disjoint_filter_complement _ D)).
    rewrite (map_filter_union_complement (fun kv : Z * bv 8 => lo <= kv.1 < hi) D).
    iExact "H".
  Qed.

  Lemma ubytes_of_window (g : gname) (D : gmap Z (bv 8)) (lo hi a : Z) (n : nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < n)%nat -> lo <= a + Z.of_nat j < hi) ->
    (forall j : nat, (j < n)%nat -> D !! (a + Z.of_nat j) = Some (f j)) ->
    ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D,
       ubyte g k b) -∗ ubytes g a n f.
  Proof.
    intros Hr HD. iIntros "H".
    assert (Hlk : forall j : nat, (j < n)%nat ->
              base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D
                !! (a + Z.of_nat j) = Some (f j)).
    { intros j Hj. apply umap_win_lookup; [ exact (Hr j Hj) | exact (HD j Hj) ]. }
    iApply (ubytes_of_map g
              (base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D) a n f Hlk
              with "H").
  Qed.

  Lemma ustr_of_window (g : gname) (D : gmap Z (bv 8)) (lo hi a : Z) (len : nat)
      (f : nat -> bv 8) :
    (forall j : nat, (j < len)%nat -> f j <> ubyte0) ->
    Z.of_nat len < 2 ^ 31 ->
    (forall j : nat, (j <= len)%nat -> lo <= a + Z.of_nat j < hi) ->
    (forall j : nat, (j < len)%nat -> D !! (a + Z.of_nat j) = Some (f j)) ->
    D !! (a + Z.of_nat len) = Some ubyte0 ->
    ([∗ map] k ↦ b ∈ base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D,
       ubyteq g DfracDiscarded k b) -∗ ustr g DfracDiscarded a len f.
  Proof.
    intros Hne Hlen Hr HD Hnul. iIntros "#H".
    assert (Hlk : forall j : nat, (j < len)%nat ->
              base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D
                !! (a + Z.of_nat j) = Some (f j)).
    { intros j Hj. apply umap_win_lookup; [ apply Hr; lia | exact (HD j Hj) ]. }
    assert (Hlk0 : base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D
                     !! (a + Z.of_nat len) = Some ubyte0).
    { apply umap_win_lookup; [ apply Hr; lia | exact Hnul ]. }
    iApply (ustr_of_pmap g
              (base.filter (fun kv : Z * bv 8 => lo <= kv.1 < hi) D)
              a len f Hne Hlen Hlk Hlk0 with "H").
  Qed.

  (* THE [Rsh] SH'S STATE FIXES, at the CONSTANT break (lane SH-STATE).
     [UkShLoop.ushl_R] uncurried, at the size [UShKernel.sh_pay_key] pins;
     the three bounds [UkShFork.ushf_rest_of_body] asks of the break
     ([8344 <= sz], [pgroundup sz = sz], [usz_ok (sz + 65536)]) are CLOSED
     computations at [0x5000], which is why the existential form the
     design of record carried is not needed. *)
  Definition sh_Rsh : gname -> gname -> gname -> iProp Σ :=
    fun _ γd γs => (UkShLoop.ushl_dat γd ∗ usz γs (kexec_sz ElfUser.sh_elf))%I.

  Lemma sh_pay_state_holds : ⊢ sh_pay_state sh_Rsh 0%nat.
  Proof.
    rewrite /sh_pay_state /sh_Rsh.
    destruct sh_tbl_parts as (Hsy & Hws & Hsy0 & Hws0).
    iModIntro. iIntros (W' γt γd γs) "%Hkey Hszf HD".
    destruct Hkey as [Hsz Hin]. rewrite <- Hsz.
    set (D0 := base.filter
          (fun kv : Z * bv 8 =>
             kv.1 < uint (tf_resume_gpr0 (uvis_tf W') !!! Regidx csp_rs1)
                    - 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + 0%nat)))))
          (udata_lo (uvis_M W') (uvis_perm W') (uvis_sz W'))) in *.
    assert (HD0 : forall (a : Z) (b : bv 8),
              0x2000 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some b ->
              D0 !! a = Some b).
    { intros a b Ha Hb. apply Hin;
        [ unfold ShData.shRodataEnd, ShData.shMemEnd; lia | exact Hb ]. }
    (* ---- window 1: the .data half, [0x2000, 0x2010) ---- *)
    iDestruct (umap_window γd D0 0x2000 0x2010 with "HD") as "[Wdat HD]".
    set (D1 := base.filter (fun kv : Z * bv 8 => ~ (0x2000 <= kv.1 < 0x2010)) D0)
      in *.
    assert (HD1 : forall (a : Z) (b : bv 8),
              0x2010 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some b ->
              D1 !! a = Some b).
    { intros a b Ha Hb. unfold D1. apply umap_win_lookup_out;
        [ lia | apply HD0; [ lia | exact Hb ] ]. }
    (* ---- window 2: [freep], [0x2010, 0x2018) ---- *)
    iDestruct (umap_window γd D1 0x2010 0x2018 with "HD") as "[Wfp HD]".
    set (D2 := base.filter (fun kv : Z * bv 8 => ~ (0x2010 <= kv.1 < 0x2018)) D1)
      in *.
    assert (HD2 : forall (a : Z) (b : bv 8),
              0x2018 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some b ->
              D2 !! a = Some b).
    { intros a b Ha Hb. unfold D2. apply umap_win_lookup_out;
        [ lia | apply HD1; [ lia | exact Hb ] ]. }
    (* ---- window 3: the line buffer, [0x2020, 0x2084) ---- *)
    iDestruct (umap_window γd D2 sh_buf (sh_buf + 100) with "HD") as "[Wbuf HD]".
    set (D3 := base.filter
                 (fun kv : Z * bv 8 => ~ (sh_buf <= kv.1 < sh_buf + 100)) D2) in *.
    assert (HD3 : forall (a : Z) (b : bv 8),
              0x2084 <= a < 0x2098 -> elf_image ElfUser.sh_elf !! a = Some b ->
              D3 !! a = Some b).
    { intros a b Ha Hb. unfold D3. apply umap_win_lookup_out;
        [ unfold sh_buf; lia | apply HD2; [ lia | exact Hb ] ]. }
    (* ---- window 4: the allocator's [base] cell, [0x2088, 0x2098) ---- *)
    iDestruct (umap_window γd D3 8328 (8328 + 16) with "HD") as "[Wbs _]".
    (* ---- the lookups, run by run ---- *)
    assert (Hsymb : forall j : nat, (j < 7)%nat ->
              D0 !! (ushp_symbols + Z.of_nat j) = Some (ushp_sym_f j)).
    { intros j Hj.
      assert (Hin7 : In j (seq 0 7)) by (apply in_seq; lia).
      pose proof (proj1 (forallb_forall _ _) Hsy j Hin7) as Hb.
      apply HD0; [ unfold ushp_symbols; lia | ].
      apply sh_dat_img. exact (bool_decide_eq_true_1 _ Hb). }
    assert (Hsymn : D0 !! (ushp_symbols + Z.of_nat 7) = Some ubyte0).
    { change (Z.of_nat 7) with 7. apply HD0; [ unfold ushp_symbols; lia | ].
      apply sh_dat_img. exact (bool_decide_eq_true_1 _ Hsy0). }
    assert (Hwsb : forall j : nat, (j < 5)%nat ->
              D0 !! (ushp_whitespace + Z.of_nat j) = Some (ushp_ws_f j)).
    { intros j Hj.
      assert (Hin5 : In j (seq 0 5)) by (apply in_seq; lia).
      pose proof (proj1 (forallb_forall _ _) Hws j Hin5) as Hb.
      apply HD0; [ unfold ushp_whitespace; lia | ].
      apply sh_dat_img. exact (bool_decide_eq_true_1 _ Hb). }
    assert (Hwsn : D0 !! (ushp_whitespace + Z.of_nat 5) = Some ubyte0).
    { change (Z.of_nat 5) with 5. apply HD0; [ unfold ushp_whitespace; lia | ].
      apply sh_dat_img. exact (bool_decide_eq_true_1 _ Hws0). }
    assert (Hfpb : forall j : nat, (j < 8)%nat ->
              D1 !! (8208 + Z.of_nat j)
              = Some (nth_byte (mword_of_int 0 : mword 64) j)).
    { intros j Hj. rewrite nth_byte_zero64.
      apply HD1; [ lia | apply sh_bss_img; lia ]. }
    assert (Hbufb : forall j : nat, (j < sh_nbuf)%nat ->
              D2 !! (sh_buf + Z.of_nat j) = Some ubyte0).
    { intros j Hj. unfold sh_nbuf in Hj. apply HD2;
        [ unfold sh_buf; lia | apply sh_bss_img; unfold sh_buf; lia ]. }
    assert (Hbsb : forall j : nat, (j < 16)%nat ->
              D3 !! (8328 + Z.of_nat j) = Some ubyte0).
    { intros j Hj. apply HD3; [ lia | apply sh_bss_img; lia ]. }
    (* ---- the window-range side conditions, HOISTED (durable-notes:
           an inline [ltac:] runs against an evar) ---- *)
    assert (Rws : forall j : nat, (j <= 5)%nat ->
              0x2000 <= ushp_whitespace + Z.of_nat j < 0x2010)
      by (intros j Hj; unfold ushp_whitespace; lia).
    assert (Rsym : forall j : nat, (j <= 7)%nat ->
              0x2000 <= ushp_symbols + Z.of_nat j < 0x2010)
      by (intros j Hj; unfold ushp_symbols; lia).
    assert (Rfp : forall j : nat, (j < 8)%nat ->
              0x2010 <= 8208 + Z.of_nat j < 0x2018) by (intros j Hj; lia).
    assert (Rbs : forall j : nat, (j < 16)%nat ->
              8328 <= 8328 + Z.of_nat j < 8328 + 16) by (intros j Hj; lia).
    assert (Rbuf : forall j : nat, (j < sh_nbuf)%nat ->
              sh_buf <= sh_buf + Z.of_nat j < sh_buf + 100)
      by (intros j Hj; unfold sh_nbuf in Hj; lia).
    assert (L5 : Z.of_nat 5 < 2 ^ 31) by (vm_compute; reflexivity).
    assert (L7 : Z.of_nat 7 < 2 ^ 31) by (vm_compute; reflexivity).
    (* ---- persist the .data half and assemble ---- *)
    iMod (uarea_persist γd
            (base.filter (fun kv : Z * bv 8 => 0x2000 <= kv.1 < 0x2010) D0)
            with "Wdat") as "#Wdatq".
    iModIntro. iExists (fun _ : nat => ubyte0).
    iSplitR "Wbuf".
    - iSplitR "Hszf"; [ | iExact "Hszf" ].
      rewrite /UkShLoop.ushl_dat.
      iSplitR.
      { iApply (ustr_of_window γd D0 0x2000 0x2010 ushp_whitespace 5 ushp_ws_f
                  ushp_ws_f_nonul L5 Rws Hwsb Hwsn with "Wdatq"). }
      iSplitR.
      { iApply (ustr_of_window γd D0 0x2000 0x2010 ushp_symbols 7 ushp_sym_f
                  ushp_sym_f_nonul L7 Rsym Hsymb Hsymn with "Wdatq"). }
      iSplitL "Wfp".
      { iPoseProof (ubytes_of_window γd D1 0x2010 0x2018 8208 8
                      (nth_byte (mword_of_int 0 : mword 64))
                      Rfp Hfpb with "Wfp") as "H".
        rewrite /uword /uwordq /ubytes. iExact "H". }
      iExists (fun _ : nat => ubyte0).
      iApply (ubytes_of_window γd D3 8328 (8328 + 16) 8328 16
                (fun _ : nat => ubyte0) Rbs Hbsb with "Wbs").
    - iApply (ubytes_of_window γd D2 sh_buf (sh_buf + 100) sh_buf sh_nbuf
                (fun _ : nat => ubyte0) Rbuf Hbufb with "Wbuf").
  Qed.


  (* ------------------------------------------------------------------- *)
  (* INIT'S PINNED EXEC SLOT, as one persistent premise.                   *)
  (*                                                                       *)
  (* [T] is the application's TAINT -- the disjunct its claim law admits    *)
  (* when the pins may have been broken -- and it is Persistent AND        *)
  (* Timeless because the claim sits under [AppInv.app_body]'s later and   *)
  (* each fire strips it ([PinnedExec]'s header).                          *)
  (* ------------------------------------------------------------------- *)
  (* THE TAINT ARM IS INDEXED BY THE PAY FACT, AT EVERY CONSTANT PAYLOAD:
     a tainted process runs arbitrary code on the generic family, which is
     indexed by the pay fact ([UexecExecMint.uslot_mint_pay]) -- and the
     payload of the process init execs sh into is the one init chose at the
     fork that made it, which is the console reader token
     ([UserConsole.ucons_pay]) and not the trivial one.  So the arm is
     ∀-bound over the resource [R] the payload names: the tainted slot
     HOLDS it, pays it at exit and at every kill check, and hands it on
     across an exec (GENERIC-PAY).  Under the [□] and not outside it,
     because the arm is persistent and is spent at whatever payload the
     ROUND chose -- the console token of that round's own position pair.
     [UexecExecMint.uslot_mint_all] is exactly this proposition. *)
  (* THE PINS LAW IS THE WHOLE ONE (lane E4).  sh does not only get its own
     row: its [exec] of the parsed command is a PINNED exec at
     [FsEchoPin.era0_echo_pins], and both that and [FsShPin.era0_sh_pins]
     are conjuncts of [EchoFsPure.echo_fs_pure], so what crosses is the one
     law and each consumer projects ([sh_pins_of_fs_pure] below is /sh's
     projection; E4's is /echo's). *)
  Definition init_sh_slot_core (T : iProp Σ) (Pay : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (riscv_kill_cred -∗ R) -∗ uslot W)
     ∗ Pay)%I.

  (* THE CONSOLE CREDENTIAL IS NOT HERE but a premise of the constructor
     ([init_exec_sup_of_sh_slot]'s third, lane SH-OPEN): which of sh's two
     pinned leaves it can make is decided by /INIT'S OWN mknod, mid-walk,
     and this record is fixed at /init's entry.

     AND THE ERA'S SIDE OF THAT PREMISE IS NOT HERE EITHER.  Stating the
     bridge from [UInitCons.init_cons_cred] to those two leaves IN THIS
     FILE makes its elaboration explode -- measured at 8.6 GB RSS in 20
     seconds, killed as [UInitSh.vo Error 143].  The leaves are [UkSh]'s,
     over ITS section's binder list, and this file's is a different one;
     the bridge therefore lives in [UInitBoot.v], whose context is the
     assembly's ([UInitBoot.ush_cons_in_of_Cns]). *)
  Definition init_sh_slot (T : iProp Σ) (Pay : iProp Σ) : iProp Σ :=
    init_sh_slot_core T Pay.

  Global Instance init_sh_slot_core_persistent T Pay `{!Persistent Pay} :
    Persistent (init_sh_slot_core T Pay).
  Proof. rewrite /init_sh_slot_core. apply _. Qed.

  Global Instance init_sh_slot_persistent T Pay `{!Persistent Pay} :
    Persistent (init_sh_slot T Pay).
  Proof. rewrite /init_sh_slot /init_sh_slot_core. apply _. Qed.

  (* the projection /sh's own pinned exec wants *)
  Lemma sh_pins_of_fs_pure (T : iProp Σ) :
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T)) -∗
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜FsShPin.era0_sh_pins v⌝ ∨ T)).
  Proof.
    iIntros "#Hl !>" (v) "Hp".
    iDestruct ("Hl" $! v with "Hp") as "[Hp [%Hf | HT]]";
      [ iFrame "Hp"; iLeft; iPureIntro; exact (proj1 (proj2 Hf))
      | iFrame "Hp"; iRight; iExact "HT" ].
  Qed.

  (* ...and /echo's, which is lane E4's seam: one [iApply] of this. *)
  Lemma echo_pins_of_fs_pure (T : iProp Σ) :
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜echo_fs_pure v⌝ ∨ T)) -∗
    □ (∀ v : aview, app_pred app_run v -∗
         app_pred app_run v ∗ (⌜FsEchoPin.era0_echo_pins v⌝ ∨ T)).
  Proof.
    iIntros "#Hl !>" (v) "Hp".
    iDestruct ("Hl" $! v with "Hp") as "[Hp [%Hf | HT]]";
      [ iFrame "Hp"; iLeft; iPureIntro; exact (proj2 (proj2 Hf))
      | iFrame "Hp"; iRight; iExact "HT" ].
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE ROOM, as closed arithmetic.                                       *)
  (*                                                                       *)
  (* [kexec_sz sh_elf] is 0x5000 and the argument block is one two-byte    *)
  (* string plus a two-word pointer vector, so [kxc_sp_final] lands at     *)
  (* 0x4FE0 -- 0xFE0 above the stack page's base, which is what sh's       *)
  (* frames have to fit in.                                                *)
  (* ------------------------------------------------------------------- *)
  Lemma init_sh_sp_final (alen : nat -> nat) :
    alen 0%nat = 2%nat -> kxc_sp_final 0x5000 alen 1%nat = 0x4FE0.
  Proof.
    intro Ha. unfold kxc_sp_final. cbn [kxc_sp]. rewrite Ha.
    vm_compute. reflexivity.
  Qed.

  Lemma init_sh_room (alen : nat -> nat) (n0 : nat) :
    alen 0%nat = 2%nat ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    kexec_sz ElfUser.sh_elf - PGSIZE
      + 8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0))))
      <= kxc_sp_final (kexec_sz ElfUser.sh_elf) alen 1%nat.
  Proof.
    intros Ha Hn0. rewrite sh_kexec_sz. rewrite (init_sh_sp_final alen Ha).
    unfold PGSIZE. lia.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE PATH, read out of init's read-only image.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma init_sh_path_of (M : gmap Z (bv 8)) :
    uimg_sub UCodeInit.init_ro M ->
    exec_path_of M (mword_of_int 0x9a8 : mword 64) init_sh_pl.
  Proof.
    intro Hro.
    pose proof (bool_decide_eq_true_1 _ init_ro_sh_bool) as (Hb0 & Hb1 & Hb2).
    split_and!.
    - split.
      + rewrite init_sh_pl_len. clear; lia.
      + intros j b Hj.
        destruct j as [| [| j]]; cbn in Hj; try discriminate Hj;
          injection Hj as <-; (intro Hc; apply (f_equal bv_unsigned) in Hc;
                               vm_compute in Hc; discriminate Hc).
    - intros j b Hj.
      destruct j as [| [| j]]; cbn in Hj; try discriminate Hj.
      + apply Hro. rewrite Hb0. exact Hj.
      + apply Hro. rewrite Hb1. exact Hj.
    - rewrite init_sh_pl_len. apply Hro. exact Hb2.
  Qed.

  (* THE HEAD'S ROWS 0 AND 2 AT ONCE (lane IO-LEAF, M4a(3)).
     [UInitFd.ufd_head_row] and [UInitFd.ufd_head_row12] each SPEND the
     head, and this constructor needs BOTH readings: row 0 is what sh's
     entry is told ([UkSh.ush_fd0]) and row 2 is what its prompt's payment
     asks for ([UShOut.ksh_w_of_link_prompt]).  So they are read off the
     one head together, at the same three arms.  (The two lemmas above
     stay: they are what every other consumer takes.) *)
  Lemma ufd_head_rows (T : iProp Σ) (st : fdstate) (γfd : gname)
      (fdv : list fdstate) :
    ufd_auth γfd fdv -∗ ufd_head T st γfd -∗
    ufd_auth γfd fdv ∗
    ((⌜take NSTD fdv !! 0%nat = Some st⌝ ∗ ⌜take NSTD fdv !! 2%nat = Some st⌝)
     ∨ ⌜take NSTD fdv !! 0%nat = Some FdClosed⌝ ∨ T).
  Proof.
    rewrite /ufd_head /ufd_headL.
    iIntros "Ha [H | [H | [_ HT]]]".
    - iDestruct (ustd_agree with "Ha H") as %->.
      iFrame "Ha". iLeft. iSplit; iPureIntro;
        [ exact (ufd_l3_row0 st) | exact (ufd_l3_row2 st) ].
    - iDestruct (ustd_agree with "Ha H") as %->.
      iFrame "Ha". iRight. iLeft. iPureIntro. exact ufd_l0_row0.
    - iFrame "Ha". iRight. iRight. iExact "HT".
  Qed.

  (* ------------------------------------------------------------------- *)
  (* THE ASSEMBLY: init's pinned bundle pays its exec supply.              *)
  (* ------------------------------------------------------------------- *)
  (* [UexecExecInst.sbundle_pay_exec_intro_ref] with the refund's
     consequence a parameter (lane M6b): the same deposit, its refund wand
     stated at whatever the supplier wants back instead of the record's
     exit payload.  Same proof. *)
  Lemma sbundle_pay_exec_intro_refR (X : uvis -d> iPropO Σ) (W : uvis)
      (Q : Z -> iProp Σ) (R : iProp Σ)
      (P Pmiss : nat -> Z -> iProp Σ)
      (Fo : pfam Σ (aview -> Z -> anode -> iProp Σ)) (Rs : iProp Σ) :
    □ (Rs -∗ R) -∗
    my_pay (uvis_gen W) Q -∗
    sys_exec_au_pre (MkPfam X Rs) (fs_gamma_L fsc_fs) fsc_fs (uvis_cwd W)
      Q P Pmiss Fo
      (uvis_M W) (tf_w (uvis_tf W) (tf_arg_idx 0))
      (tf_w (uvis_tf W) (tf_arg_idx 1)) (uvis_fd W) (uvis_ch W) (uvis_pid W) -∗
    sbundle_pay_refR X Q R W.
  Proof.
    iIntros "#Hrf Hmp H". rewrite /sbundle_pay_refR.
    iExists (xfam_at Q (xfam_exec P Pmiss Fo Rs)).
    iSplitR; [ done | ].
    iSplitR; [ iExact "Hrf" | ].
    rewrite /sbundle_at /= /xv6_sbundle.
    destruct (decide (USYS_exec = USYS_exec)) as [_ | Hc];
      [ | exfalso; exact (Hc eq_refl) ].
    rewrite /exec_sbundle /=. iFrame "Hmp". iExact "H".
  Qed.

  (* /init's all-closed ledger is the closed-arm shape at zero opens
     (step 4) *)
  Lemma ufd_l0_lcl : UkSh.ush_lcl UInitFd.ufd_l0 0%nat.
  Proof.
    split; [ intros i Hi; lia | ].
    intros i [_ Hi]. unfold NSTD in Hi.
    destruct i as [| [| [| i]]];
      [ exact UInitFd.ufd_l0_row0 | vm_compute; reflexivity
      | exact UInitFd.ufd_l0_row2 | lia ].
  Qed.

  Lemma init_exec_sup_of_sh_slot (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (cn : cons_names) (st : fdstate) (K : iProp Σ) `{!Persistent K}
      (* ...AND THE APPLICATION'S PER-POSITION CREDENTIAL (lane IO-LEAF,
         M5): [UserConsole.ucons_pay]'s [Rd], which rides sh's exit payload
         under the same existential as the cursor and so round-trips
         through /init's wait.  A parameter for [T]'s reason -- this file
         names no era. *)
      (* ...AS THE PAIR (step 3): the exit family is [UkInit.init_rd Rdl Wb]
         -- the READ side of the lease, which is what the child is handed
         ([Rdl], the lend family), beside the banner-owed credential the
         child's shell assembles where it leaves. *)
      (Rdl : nat -> iProp Σ) `{HRdl : !forall i : nat, Timeless (Rdl i)}
      (* ...AND THE SAME CREDENTIAL WITH THE TOKEN AND THE CURSOR BESIDE
         IT (lane IO-LEAF, M5(3)): what a shell holds in the MIDDLE of a
         line, where the payload's own boundary row is false.  Indexed by
         the position ghost for [Rd]'s reason -- init mints a fresh pair
         per child. *)
      (Pm : gname -> nat -> iProp Σ)
      (* ...AND THE ERA'S WRITE CREDENTIAL AS THE COMMAND LOOP CARRIES IT
         (lane IO-LEAF, M6a(3)): at a line boundary, with [p] prompt bytes
         out.  Not indexed by the position ghost: the credential is the
         era's and the pair is the round's. *)
      (Wc : nat -> nat -> iProp Σ)
      (* ...AND THE BANNER-OWED CREDENTIAL (step 3): the loop's closed
         arm, and the exit family's own arm. *)
      (Wb : nat -> iProp Σ) `{HWb : !forall i : nat, Timeless (Wb i)}
      (* ...AND THE ROUND-OPEN CREDENTIAL /init lends on the console row
         (lane M6b): what the banner leaves and what pays init's two
         diagnostics; the shell's entry converts it to the prompt
         credential ([Hpw] below). *)
      (Wp : nat -> iProp Σ)
      (Rsh : gname -> gname -> gname -> iProp Σ) (n0 : nat) :
    (* the numbers sh admits -- THE FREE ONES (lane SUPPLY-SPLIT) *)
    (* AT THE FREE INSTANCE, NAMED AND NOT RESOLVED (lane SUPPLY-SPLIT's
       own intent, ruled for E2).  A VERIFIED program's slot never takes
       the taint: [UkRun.udep] at the ambient [UexecExecInst.uprogSG_gen]
       is [box Dsup] with [Dsup := xv6_ssupply := AppInv.app_sup], and for
       the echo era the supply and the taint are interderivable
       ([AppEcho.echo_sup_of_taint] / [echo_taint_of_sup]) -- so a shell
       slot built at [gen] would be a vacuous arm.  This file may not bind
       [uprogSG] as a section variable (see the header: [uprogSG_gen] is
       the one instance resolution may find, and a second makes every
       [udep] in the tree ambiguous), and the GENERIC slot's lemmas below
       stay at [gen] by design.  So the free instance is written on EVERY
       position that carries a deposit -- the premises, the conclusion,
       and the [sh_slot_of_kexec] application in the proof -- and nowhere
       else.  At that instance [psok] IS [free_num], so this premise is
       the identity. *)
    (forall k : Z, free_num k -> @psok Σ uprogSG_free k) ->
    8 * Z.of_nat (2 + (8 + (16 + (ush_Dbody + n0)))) <= 0xFE0 ->
    (* WHAT INIT'S OWN OPEN INSTALLED ON SLOT 0.  sh's entry is told one
       row about its table -- fd 0 is the console, slot 0 is closed, or the
       taint ([UkSh.ush_fd0]) -- and those are exactly the three arms of
       init's head ([UInitFd.ufd_head]), which the exec supply now carries
       ([UkInit.init_exec_sup_pos]) and reads against the lent authority
       ([UInitFd.ufd_head_row]).  The only thing left for the caller to say
       is that the head's OWN state is the console one, which is what the
       pinned open's receipt gives it.
       AT BOTH BITS (lane IO-LEAF, M4a(3)): /init's open is [O_RDWR], and
       the WRITABLE one is what sh's prompt asks of fd 2
       ([UShOut.ksh_w_of_link_prompt]).  It was [exists wr, ...] while only
       fd 0's READABLE bit was read off it. *)
    st = FdOpen true true (FdDevice ConsoleInv.CONSOLE) ->
    (* ...AND THE READ LEAF SH RUNS ON (lane SH-LINE 2b, R1').  sh's
       [gets] runs on the RECEIPT-KEEPING console read now, and its supply
       is the reader lease inside sh's own exit payload -- which is the
       payload this constructor chooses ([UserConsole.ucons_pay] at the
       pair minted for the round).  The discharge is
       [UShLine.ush_read_recv_leaf_holds]; it names [FsCfg.fsc_cons] and
       the application's two readings of the supply, neither of which this
       file may name, so it arrives as a Coq-level premise -- quantified
       over the POSITION GHOST because init mints a fresh pair per child,
       exactly as [sh_pay]'s tail is. *)
    (forall (γp : gname) (N : uk_names Σ) (l : list fdstate),
       ukn_pay N = ucons_pay cn γp T (UkInit.init_rd Rdl Wb) ->
       ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp T (Pm γp) cn l) ->
    (* ...AND THE LEASE IN THE PIECES A LINE'S MIDDLE LEAVES IT IN, with
       its three laws and the boundary the payload carries (lane IO-LEAF,
       M5(3)).  All four are Coq-level for the leaf's own reason: this file
       names no era, and the one discharge ([UShLine]'s [ush_mid]) is where
       the record's equations are. *)
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp T (UkInit.init_rd Rdl Wb) ->
       ⊢ UkSh.ush_at N γp i -∗
         UkSh.ush_lease N γp T (Pm γp) i) ->
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp T (UkInit.init_rd Rdl Wb) ->
       ⊢ T -∗ Pm γp i -∗ UkSh.ush_at N γp i) ->
    (* ...AND THE PAYLOAD'S OWN ARM (step 3): the pieces and the
       banner-owed credential, at a boundary. *)
    (forall (γp : gname) (N : uk_names Σ) (i : nat),
       ukn_pay N = ucons_pay cn γp T (UkInit.init_rd Rdl Wb) -> UkSh.ush_bnd i ->
       ⊢ Pm γp i -∗ Wb i -∗ UkSh.ush_at N γp i) ->
    (* ...AND THE CREDENTIAL'S STEP AT THE READ (lane IO-LEAF, M6a(3)):
       what the prompt left at boundary [n] is the boundary credential at
       [n + 17] once the line is read, on the pieces the read leaves.
       Unguarded -- it names no payload. *)
    (forall (γp : gname) (n : nat),
       ⊢ Pm γp (n + length EchoDisc.echo_line)%nat -∗ Wc n 2%nat -∗
         Pm γp (n + length EchoDisc.echo_line)%nat
         ∗ Wc (n + length EchoDisc.echo_line)%nat 3%nat) ->
    (* ...AND THE THREE CONVERSIONS OF STEP 4 ([UShKernel.sh_uexec_slot]'s
       [Hwbwc] / [Hwbl] / [Hwbr]), passed straight through *)
    (forall n : nat, ⊢ Wb n -∗ Wc n 0%nat) ->
    (forall n : nat, ⊢ Wc n 3%nat -∗ Wc n 0%nat) ->
    (forall (γp : gname) (n : nat),
       ⊢ Pm γp (n + length EchoDisc.echo_line)%nat -∗ Wb n -∗
         Pm γp (n + length EchoDisc.echo_line)%nat ∗ T) ->
    (* ...AND THE ENTRY LAW (step 3): the raw lend and the loop's
       credential slot make the loop's cursor ([UShLine.ush_posb_of_lend]
       is the one discharge). *)
    (forall (γp : gname) (N : uk_names Σ) (l : list fdstate) (i : nat),
       ukn_pay N = ucons_pay cn γp T (UkInit.init_rd Rdl Wb) ->
       ⊢ upos γp i -∗ ucons_pay cn γp T Rdl (-1) -∗
         (UkSh.ush_wcp Wc Wb l i 0%nat ∨ T) -∗
         UkSh.ush_posb N γp T Wc Wb (Pm γp) l 0%nat) ->
    (* ...AND THE LEND'S CONVERSION AT THE SHELL'S ENTRY (lane M6b): the
       round-open credential is the prompt credential at the same count
       with no prompt byte out (top: [UInitDiag.kinit_own_of_pro] +
       [UInitBanner.kinit_own_is_cred]).  Coq-level like the entry law. *)
    (forall n : nat, ⊢ Wp n -∗ Wc n 0%nat) ->
    udep (PS := uprogSG_free) -∗
    (* ...AND THE THREE DEPOSITS SH OWES: read(5), open(15), write(16), the
       CLAIM numbers sh calls ([UkSh.sh_deps]).  They cross the exec with
       the slot, because the slot they build IS sh's. *)
    □ (T -∗ UkSh.sh_deps (PS := uprogSG_free)) -∗
    (* ...AND THE PROMPT'S LAW AT EVERY LINE BOUNDARY (lane IO-LEAF,
       M6a(3)): persistent, so it crosses into every shell this [□] builds. *)
    UShKernel.sh_prompt_law (PS := uprogSG_free) Wc -∗
    (* ...AND WHAT SH'S CONSOLE PREAMBLE IS TOLD (lane SH-OPEN, H3).  sh's
       open of "console" is PINNED, so which of the two pinned leaves it
       makes is decided here.  PERSISTENT, AND THAT IS FORCED: this
       constructor's body is under a [□] -- /init execs sh inside the
       restart loop's [iLob] -- so the only LINEAR resource that can cross
       into sh is the one /init hands per round ([UserConsole.upos], through
       [PinnedExec]'s single [Pay]).  An EXCLUSIVE absence credential
       ([AppEcho.cons_key]) therefore cannot reach sh at all; the
       credential is [AppEcho.cons_never] (the owner's ruling (A), E2's to
       mint) and [UShConsK] states the two leaves against it. *)
    (* AT THE FREE INSTANCE TOO, and this is where the seam actually bit:
       the leaves CARRY the deposit instance ([UkSh]'s leaf section binds
       [{SG}] and [{PS}] as section variables), so an unannotated premise
       here is at [uprogSG_gen] while the [sh_slot_of_kexec] application
       below wants [uprogSG_free] -- and the two records are NOT
       convertible ([Dsup := xv6_ssupply] vs [True], [psok := fun _ =>
       True] vs [xv6_free]), so [iApply] unfolds both into
       [UexecSG.sbundle]'s tower looking for a match that cannot exist.
       That FAILING unification is the wedge; naming the instance on both
       sides removes it. *)
    (□ (∀ N : uk_names Σ,
          UkSh.ush_open_console_leaf (PS := uprogSG_free) N T)
     ∨ (□ (∀ N : uk_names Σ,
             UkSh.ush_open_absent_leaf (PS := uprogSG_free) N T K) ∗ K)
     ∨ T) -∗
    init_sh_slot T (sh_pay T Wc Wb Pm Rsh n0) -∗
    (* NO [(PS := uprogSG_free)] ANY MORE: the exec supply's conclusion is
       [UkRun.udepw_at_ref] (lane KILL-PAY, K4(a), ruling R-A), whose one
       disjunct is the bundle itself -- it names no [psok], so there is no
       [uprogSG] instance left to pin. *)
    (* ...AND WHAT IT LENDS BESIDE THE POSITION AND THE LEASE (lane
       IO-LEAF, step 3): the era's credential AT THE LEDGER the child
       inherits ([UkInit.init_lend_cred]) -- prompt-shaped on the
       both-console row, banner-owed on the closed one -- which sh's
       entry puts in its loop's own slot ([UkSh.ush_wcp]).  This is the
       ONE place the two ends meet. *)
    UkInit.init_exec_sup_lend cn T st Wp Wb Rdl.
  Proof.
    intros Hpsok_free Hn0 Hst Hrl Hpm1 Hpm3 Hpmwb Hwc Hwbwc Hwbl Hwbr Hbd Hpw.
    subst st.
    iIntros "#Hdep #Hdp #Hplaw #Hcons (#Hinv & #Hcl0 & #Hgen & #Hpay)".
    (* E4: what crosses is the WHOLE pins law and each consumer projects *)
    iDestruct (sh_pins_of_fs_pure T with "Hcl0") as "#Hcl".
    (* THE LEDGER IS TAKEN AND NOT READ: sh's entry says nothing about its
       standard streams, and the only descriptor fact this constructor
       needs is [length fdv = NOFILE], which comes off the LENT authority
       ([UserFd.ufd_auth_len]) rather than off the ledger. *)
    iModIntro. iIntros (γp np N m pc l)
      "%Hpeq %Ha0 %Ha1 #Hro #Hargv Hstd Hrow Hcred Hpos Hlease Hchf Hpidf".
    rewrite /udepw_at_refR_ids.
    iIntros (M pm sz fdv gn cs pidv) "#Hmpay Hheap Hufd Hids".
    (* ---- THE TWO IDENTITY READINGS (lane EXEC-SEAM), off the lent
       authorities against the child's own fragments: the key's children
       set is EMPTY and its pid is not <init>'s.  Both are pure, so the
       fragments are spent and the authorities go straight back. ---- *)
    iDestruct (urun_ids_ch with "Hids") as "[Hcha Hidsb]".
    iDestruct (UserChildren.uch_agree with "Hcha Hchf") as %Hcs.
    iDestruct ("Hidsb" $! cs with "Hcha") as "Hids".
    iDestruct "Hpidf" as (p) "[%Hp1 Hpidf]".
    iDestruct (urun_ids_pid with "Hids") as "[Hpida Hidsb]".
    iDestruct (UserChildren.upid_agree with "Hpida Hpidf") as %Hpv.
    iDestruct ("Hidsb" with "Hpida") as "Hids".
    iClear "Hchf Hpidf".
    (* ---- the two image readings, off the lent heap ---- *)
    iAssert (⌜uimg_sub UCodeInit.init_ro M⌝)%I as %Hsro.
    { iIntros (a b Hb).
      rewrite /init_rodata /utext_img.
      iDestruct (big_sepM_lookup _ _ a b Hb with "Hro") as "Hb".
      iDestruct (uheap_text with "Hheap Hb") as %(HM & _ & _).
      iPureIntro. exact HM. }
    iAssert (⌜uimg_sub UCodeInit.init_argv_map M⌝)%I as %Hsav.
    { iIntros (a b Hb).
      rewrite /init_argv.
      iDestruct (big_sepM_lookup _ _ a b Hb with "Hargv") as "Hb".
      iDestruct (uheap_ubyte with "Hheap Hb") as %(HM & _ & _).
      iPureIntro. exact HM. }
    (* ---- the descriptor list, off the lent authority ---- *)
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    (* ...AND THE ROW SH'S ENTRY IS TOLD, read off INIT'S OWN LEDGER
       against that same authority ([UserFd.ustd_agree]): the ledger is
       spent here -- the process that execs is replaced, and the new image
       gets its ledger from its own run -- and its row ([UInitFd.ufd_row])
       is what sh's entry is told about slot 0. *)
    iDestruct (ustd_agree (ukn_fd N) fdv l with "Hufd Hstd") as %Hl.
    iAssert (UkSh.ush_fd0 T (take NSTD fdv)) with "[Hrow]" as "#Hfd0".
    { rewrite Hl /UInitFd.ufd_row. iDestruct "Hrow" as "[%Hr1 | [%Hr2 | HT]]".
      - iLeft. iPureIntro. left. exists true. rewrite Hr1. exact (ufd_l3_row0 _).
      - iLeft. iPureIntro. right. rewrite Hr2. exact ufd_l0_row0.
      - iRight. iExact "HT". }
    (* THE CREDENTIAL AND THE LEDGER STAY AT THE LEND'S OWN SHAPE UNTIL THE
       EXEC HAS SUCCEEDED (lane M6b): they go into the deposit as they are,
       so that a FAILED exec refunds them as they are
       ([UkInit.init_lend_ref]) -- the shell's slot converts the credential
       where it is built ([Hcon] below), and the refund wand hands the four
       back without looking at them. *)
    iFrame "Hheap Hufd Hids".
    (* ---- sh's constructor, at every key the image fact admits ---- *)
    (* THE PAYLOAD RIDES WITH THE PAY FACT ([SpecKexec.exec_slot_pre]): the
       kernel holds the exec'ing process's own payment across this call and
       hands it to whatever slot answers, so sh's entry gets its exit
       payload -- the console reader token -- from here and from nowhere
       else (EXEC-PAY, GENERIC-PAY). *)
    (* ...and the taint arm at the SAME payload: a tainted process runs on
       the generic family, which exists at any constant payload and HOLDS
       the resource it names ([UexecExecMint.uslot_mint_pay]).  The payload
       is literally the constant function at what the kill status names
       ([UserConsole.ucons_pay_eta]). *)
    (* ...AND THE TAINT ARM IS HANDED NOTHING AT ALL NOW (lane SELF-KILL,
       P6b): the generic family's constant payload is carried
       PERSISTENTLY ([UexecExecMint.uslot_mint_all] at
       [□ (riscv_kill_cred -∗ R)]), and the arm builds it out of the TAINT
       it is already holding ([UserConsole.ucons_pay_taint]) -- which is
       the whole reason a tainted process needs no lease. *)
    iAssert (□ (∀ W' : uvis, T -∗ my_pay (uvis_gen W') (ucons_pay cn γp T (UkInit.init_rd Rdl Wb)) -∗
                  uslot W'))%I as "#Hgen'".
    { iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! (ucons_pay cn γp T (UkInit.init_rd Rdl Wb) (-1)) W' with "HT [Hmp] []").
      - rewrite ucons_pay_eta. iExact "Hmp".
      - iModIntro. iIntros "_". iApply (ucons_pay_taint with "HT"). }
    (* THE LINEAR HALF OF [Pay] IS THE POSITION: [UInitSh.sh_pay] is
       persistent, so what actually crosses [PinnedExec]'s one linear slot
       is [UserConsole.upos] at the pair init minted for this round.  The
       exit payload is NOT there -- it arrives at the constructor wand from
       the kernel's own payment. *)
    iAssert (□ (∀ (na : nat) (alen : nat -> nat) (afun : nat -> nat -> bv 8)
                  (W' : uvis),
                  ⌜kexec_image_ok ElfUser.sh_elf na alen afun fdv W'⌝ -∗
                  (* THE TWO ROWS [SpecKexec.exec_slot_pre] carries, in
                     [PinnedExec.pex_slot]'s own order (beside
                     [kexec_image_ok], before the pay fact).  THE CWD ROW
                     is proved there from [SpecKexec.kexec_ok_exec_cwi]:
                     exec INHERITS the working directory, and /init's is
                     the root -- sh's console preamble needs it because a
                     pinned open is about a PATH ([UkRun.udepwf_at] fixes
                     the cwd).  THE LAZY ROW is [false] because exec's
                     image is EAGER (lane LAZY-FLAG's K4).  Both are read
                     off the wand here and restated nowhere. *)
                  ⌜uvis_cwd W' = FsImg.ROOTINO⌝ -∗
                  ⌜uvis_lazy W' = false⌝ -∗
                  (* ...AND THE TWO IDENTITY ROWS (lane EXEC-SEAM): the
                     key's children set and pid are the exec'ing child's,
                     read above as [∅] and as a pid other than 1. *)
                  ⌜uvis_ch W' = cs⌝ -∗
                  ⌜uvis_pid W' = pidv⌝ -∗
                  ⌜exec_args_of M (mword_of_int 0x1000 : mword 64)
                     na alen afun⌝ -∗
                  my_pay (uvis_gen W') (ucons_pay cn γp T (UkInit.init_rd Rdl Wb)) -∗
                  (sh_pay T Wc Wb Pm Rsh n0 ∗ upos γp np
                     ∗ ucons_pay cn γp T Rdl (-1)
                     ∗ (UserFd.ustd (ukn_fd N) l
                        ∗ UkInit.init_lend_cred T
                            (FdOpen true true (FdDevice ConsoleInv.CONSOLE))
                            Wp Wb l np)) -∗ uslot W'))%I
      as "#Hcon".
    { iModIntro.
      iIntros (na alen afun W')
        "%Hok %Hcwd0 %Hlzf %Hchq %Hpiq %Hargs #Hmp [[#Hp1 [#Hp2 #Htag]] [Hps [Hls [Hstd' Hcred]]]]".
      assert (Hch0 : uvis_ch W' = ∅) by (rewrite Hchq; exact Hcs).
      assert (Hpid1 : bv_unsigned (uvis_pid W') <> 1)
        by (rewrite Hpiq Hpv; exact Hp1).
      (* ...AND THE CREDENTIAL, AT THE SAME LEDGER (step 3; M6b): /init
         lent it correlated with the row ([UkInit.init_lend_cred]), so it
         lands in the loop's slot on the arm the row names -- the
         both-console arm (/init's two dups pinned fds 1 and 2 to the
         descriptor its open installed, so fd 2 IS the console, which is
         what [UShOut.ksh_w_of_link_prompt] asks of sh's table), through
         the lend's conversion [Hpw]; the closed arm (slot 2 of the
         all-closed ledger); or the affine one.  The old record's ledger
         fragment is dropped: the process that execs is replaced. *)
      iAssert (UkSh.ush_wcp Wc Wb (take NSTD fdv) np 0%nat ∨ T)%I
        with "[Hcred]" as "Hwcp".
      { rewrite Hl /UkInit.init_lend_cred /UkSh.ush_wcp.
        iDestruct "Hcred" as "[[%Hl3 Hc] | [[%Hl0 Hb] | #HT]]".
        - iLeft. iLeft. iSplitR.
          + iPureIntro. rewrite Hl3. split_and!.
            * exists true. exact (ufd_l3_row0 _).
            * exists true. exact (ufd_l3_row1 _).
            * exists true. exact (ufd_l3_row2 _).
          + iPoseProof (Hpw np) as "Hpw'". iApply ("Hpw'" with "Hc").
        - (* the all-closed ledger, with none of the preamble's opens landed
             yet (step 4: [UkSh.ush_lcl] at 0) *)
          iLeft. iRight. iFrame "Hb". iPureIntro. rewrite Hl0.
          split; [ | lia ]. exists 0%nat. split; [ lia | exact ufd_l0_lcl ].
        - (* the taint: a tainted shell runs on the generic slot, and the
             entry law's right arm is where it goes (lane EXEC-SEAM, (C)) *)
          iRight. iExact "HT". }
      iClear "Hstd'".
      destruct (init_args_det M na alen afun Hsav Hsro Hargs) as [-> Halen].
      idtac "MARK-s4b-args-det".
      (* STAGED, AND WITH BOTH CLASS ARGUMENTS GIVEN.  [sh_slot_of_kexec]
         is polymorphic in the PAIR ([UShKernel.v] binds [{SG : uexecSG}]
         and [{PS : uprogSG}] as section variables), so leaving [SG] to
         [iApply] means solving it against the goal while [PS] is already
         fixed -- and that unification runs inside [UexecSG.sbundle]'s
         tower and does not return.  The [pose proof] elaborates the
         INSTANTIATED lemma with no goal in play; the [iApply] then has
         only the resource list to do. *)
      pose proof (sh_slot_of_kexec (SG := uexecSG_xv6) (PS := uprogSG_free)
                    Hpsok_free Rsh γp cn T K (ucons_pay cn γp T (UkInit.init_rd Rdl Wb))
                    (ucons_pay cn γp T Rdl)
                    (Pm γp) Wc Wb (Hrl γp) (Hpm1 γp) (Hpm3 γp)
                    (Hpmwb γp) (Hwc γp) Hwbwc Hwbl (Hwbr γp)
                    1%nat alen afun fdv W' n0 np
                    (fun N0 l0 n1 => Hbd γp N0 l0 n1)
                    (ucons_pay_const cn γp T (UkInit.init_rd Rdl Wb)) Hok Hcwd0
                    (init_sh_room alen n0 Halen Hn0) Hlen Hlzf Hch0 Hpid1) as Hsk.
      idtac "MARK-s4c-pose-ok".
      iApply (Hsk with "[] Hdep Hdp Htag Hplaw [] [] Hcons Hgen' Hmp Hps
                        Hls Hwcp").
      - (* THE KEY'S OWN READING (lane SH-STATE): [sh_pay_state]'s wand
           takes [UShKernel.sh_pay_key], and the two facts it is derived
           from are the very ones handed to [sh_slot_of_kexec] above. *)
        iModIntro. iIntros (γt γd γs) "Hsz Hlo".
        iApply ("Hp1" $! W' γt γd γs with "[%] Hsz Hlo").
        exact (UShKernel.sh_pay_key_of_kexec 1%nat alen afun fdv W' n0 Hok
                 (init_sh_room alen n0 Halen Hn0)).
      - iIntros (N0). iApply ("Hp2" $! γp N0).
      - iExact "Hfd0". }
    iDestruct (pinned_exec_bundle fsc_fs uslot FsShPin.era0_sh_pins T
                 FsImg.ROOTINO init_sh_pl [FsImg.ROOTINO; FsShPin.SH_INO]
                 FsShPin.SH_INO ElfUser.sh_elf 1%nat
                 (sh_pay T Wc Wb Pm Rsh n0 ∗ upos γp np
                    ∗ ucons_pay cn γp T Rdl (-1)
                    ∗ (UserFd.ustd (ukn_fd N) l
                       ∗ UkInit.init_lend_cred T
                           (FdOpen true true (FdDevice ConsoleInv.CONSOLE))
                           Wp Wb l np))%I
                 (ucons_pay cn γp T (UkInit.init_rd Rdl Wb))
                 M (mword_of_int 0x9a8) (mword_of_int 0x1000) fdv cs pidv
                 init_sh_pin_resolves sh_elf_loadable
                 (init_sh_path_of M Hsro)
                 with "Hcl Hinv Hcon Hgen' [Hpos Hlease Hstd Hcred]")
      as (P Pmiss Fo) "Hb".
    { iFrame "Hpay Hpos Hlease Hstd Hcred". }
    assert (Ea0 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false))
                    (tf_arg_idx 0) = (mword_of_int 0x9a8 : mword 64))
      by (etransitivity; [ exact (tf_of_arg0 m pc) | exact Ha0 ]).
    assert (Ea1 : tf_w (uvis_tf (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false))
                    (tf_arg_idx 1) = (mword_of_int 0x1000 : mword 64))
      by (etransitivity; [ exact (tf_of_arg1 m pc) | exact Ha1 ]).
    (* THE DEPOSIT IS WANTED AT THIS PROGRAM'S OWN PAYLOAD (app-echo.md,
       "SH-LINE RULING", R1, at exec): exec's bundle READS the payload --
       it is what the kernel hands the new image's slot -- so the bundle is
       introduced AT that payload rather than re-keyed afterwards.  init's
       own is the trivial one ([Hpeq], userinit's choice). *)
    (* THE REFUND IS THE LEND ITSELF (lane KILL-PAY, K4(a), ruling R-A;
       lane M6b): what init's child put into this deposit is
       [PinnedExec]'s [Pay] -- sh's entry payload, the position, the lease,
       the ledger and the credential -- and a FAILED exec hands the last
       four back at the shapes they went in at ([UkInit.init_lend_ref]),
       which is what pays the child's diagnostic through the link and then
       its own [exit(1)] ([UkInitMain.wp_kinit_main_die_de]).  The wand
       drops only [sh_pay], which is persistent anyway. *)
    iApply (sbundle_pay_exec_intro_refR uslot
              (uvis_of_run m pc M pm sz fdv FsImg.ROOTINO gn cs pidv false)
              (ukn_pay N) _ P Pmiss Fo
              (sh_pay T Wc Wb Pm Rsh n0 ∗ upos γp np
                 ∗ ucons_pay cn γp T Rdl (-1)
                 ∗ (UserFd.ustd (ukn_fd N) l
                    ∗ UkInit.init_lend_cred T
                        (FdOpen true true (FdDevice ConsoleInv.CONSOLE))
                        Wp Wb l np))%I).
    { iIntros "!> (_ & Hps & Hls & Hstd & Hcred)".
      rewrite /UkInit.init_lend_ref. iFrame "Hstd Hps Hls Hcred". }
    { cbn [uvis_gen uvis_of_run]. iExact "Hmpay". }
    rewrite Hpeq Ea0 Ea1. iExact "Hb".
  Qed.

  (* =================================================================== *)
  (*  THE EXEC SUPPLY AS THE WALK TAKES IT (lane E2)                      *)
  (*                                                                      *)
  (*  /init's walk does not hold the console credential at its entry --   *)
  (*  which credential it is is decided by its own mknod, mid-walk -- so   *)
  (*  what the entry carries is [UkInit.init_cons_sup]: the supply as a    *)
  (*  WAND from the credential, beside the law that pays it under the      *)
  (*  taint.  Everything else the shell's slot needs is persistent and is  *)
  (*  fixed at the entry.                                                  *)
  (* =================================================================== *)
End UInitSh.
