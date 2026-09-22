(* ===================================================================== *)
(*  UShCatPay.v -- LANE EXEC-CAT, THE SUPPLY: sh's forked RIGHT child     *)
(*  runs /cat on the paid entry.                                          *)
(*                                                                       *)
(*  [UShEchoPay.v] is the mould: the U-tier exec rule                     *)
(*  ([ExecRun.udepw_at_refR_of_sup]) with sh's own supply plugged in --   *)
(*  the node read off the lent heap, the PIN as (W)'s supplier            *)
(*  ([ExecRun.exec_walk_of_pin] at [FsCatPin.era0_cat_pins], which        *)
(*  [AppPipeCons.pipe_cat_pins_acc] hands the pipeline claim), the        *)
(*  resolving arm as (E), the taint arm at the chosen payload, and the    *)
(*  refund -- the ledger fragment and the lend, WHOLE.                    *)
(*                                                                       *)
(*  ==================  WHAT THIS FILE HAD TO REPAIR  ==================  *)
(*                                                                       *)
(*  The brief says to put the image fact into [UCatPipe.pcat_image_entry] *)
(*  -- design 5.3's landed (E) half.  THAT LEMMA IS VACUOUS.  Its         *)
(*  premises include both                                                 *)
(*                                                                       *)
(*      EchoDisc.line_ok ws          and          length ws = 1%nat       *)
(*                                                                       *)
(*  and [line_ok] contains [2 <= length ws] (it must: echo prints nothing *)
(*  at argc 1, which is durable-notes' degenerate-member rule).  It also  *)
(*  contains [ws !! 0 = Some cmd_echo], so even relaxing the count leaves *)
(*  a premise saying the command is called "echo".  Both halves are       *)
(*  mechanised in [UkShCat.cat_line_premises_absurd] /                    *)
(*  [UkShCat.cat_line_head_absurd].                                       *)
(*                                                                       *)
(*  [UCatPipe.v] is another lane's file and the STOP rule forbids         *)
(*  touching it, so the repair is here and it is ADDITIVE: section 4's    *)
(*  [cat_image_entry_1w] is [pcat_image_entry]'s body at premises that    *)
(*  can be met.  It keeps [UCatPipe.pcat_pay_at] as the payment           *)
(*  interface, so [UCatPipe.pcat_pay_at_of_round] -- the landed bridge    *)
(*  from cat's round at fd 0 -- plugs into it UNCHANGED, and the only     *)
(*  thing [UCatPipe.v] owes is to restate the entry's premises the way    *)
(*  section 4 does.                                                       *)
(*                                                                       *)
(*  WHY THE REPAIR IS NOT A RESTATEMENT OF THE WORD-LIST LAYER.  Every    *)
(*  [line_ok] in [UShEcho]'s node layer ([echo_node_img],                 *)
(*  [echo_args_det], [echo_uargv_shape]) is spent on facts the GENERAL    *)
(*  argument layer already has without it -- [ExecArgs.uargv_shape],      *)
(*  [uargv_img], [uargv_det] name no word list at all.  So the right      *)
(*  command's reading is three short lemmas over [ExecArgs] (section 3)   *)
(*  and no word list appears in this file either.                         *)
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
Require Import RegFile.
Require Import ProcGeom.          (* [NOFILE] *)
Require Import UexecSlot UexecRet.
Require Import UkRun.
Require Import UserHeap.
Require Import UserFd UserCwd.
Require Import ChildTok.
Require Import ElfUser.
Require Import PageGeom.          (* [PGSIZE] *)
Require Import UmodeArith UmodeAbi.
Require Import PathElems ArgPath.
Require Import FsCfg.
Require Import FsImg FsImgCheck.
Require Import FsAbsDefs FsAbsEra.
Require Import AppCfg AppInv.
Require Import FsCatPin.
Require Import FileFsPure.
Require Import PinnedExec.
Require Import ExecEntry.
Require Import ExecArgs.
Require Import ExecRun.
Require Import SpecKexec SpecSysExec.
Require Import KexecDefs.
Require Import CtxIdDefs.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShRun UkShMain.
Require Import UkShDiag.
Require Import PipeDisc.
Require Import UserChildren.
Require User.ShSyms.
Require Import UShEcho.            (* [uargv_exec_of_cmd] / [uint_avi_moi] --
                                      the two general steps, which name no
                                      program and no word list *)
Require Import UkAbi.
Require Import UEchoKernel.   (* [uvis_argc] / [uvis_av] / [echo_arg] /
                                 [echo_args] -- the argument reading, which
                                 names no program *)
Require Import UkCatCat UkCatMain.
Require Import UShCat.             (* cat's image geometry, all of it
                                      [line_ok]-free except two lemmas this
                                      file replaces *)
Require Import UCatPipe.           (* [pcat_pay_at] / [pcat_pay_at_of_round]
                                      -- READ-ONLY, another lane's file *)
Require Import UkShCat.            (* the (W) half this supply feeds *)
Require User.CatSyms.
Local Open Scope Z_scope.
Import Defs.

Set Printing Depth 40.

(* ===================================================================== *)
(*  1.  CAT'S PATH, AND THE PIN THAT RESOLVES IT                          *)
(*                                                                       *)
(*  [UShEcho]'s sections 1-2 at /cat.  argv[0] is the pipe line's right   *)
(*  word, whose three bytes are "cat"; the pin speaks of                  *)
(*  [FsCatPin.cat_path], a list of NAMES, and [PathElems.path_elems]      *)
(*  joins them.                                                          *)
(* ===================================================================== *)
Definition cat_pl : list (bv 8) := FsImgCheck.fname_cat.

Lemma cat_path_elems : path_elems cat_pl = FsCatPin.cat_path.
Proof using . vm_compute. reflexivity. Qed.

Lemma cat_pl_len : length cat_pl = 3%nat.
Proof using . reflexivity. Qed.

(* ...and the bytes ARE the command name the pipe line's right side
   spells ([UkShPipeLex.ushq_cat], through [UkShCat.cmd_cat]) -- which is
   what ties the pin to what sh actually passes to exec. *)
Lemma cat_pl_line (j : nat) :
  (j < 3)%nat -> cat_pl !!! j = UkShCat.cmd_cat !!! j.
Proof using .
  intro Hj.
  do 3 (destruct j as [| j]; [ vm_compute; reflexivity | ]). lia.
Qed.

Lemma cat_pl_shape : arg_path_shape cat_pl.
Proof using .
  split; [ vm_compute; reflexivity | ].
  intros j b Hj.
  destruct j as [| [| [| j]]]; cbn in Hj; try discriminate Hj;
    injection Hj as <-;
    (intro Hc; apply (f_equal bv_unsigned) in Hc;
     vm_compute in Hc; discriminate Hc).
Qed.

(* no byte of the command name is a NUL, which is what pins argv[0]'s
   LENGTH: a [bb_cstr] that stopped early would have to find one *)
Lemma cmd_cat_nonul (j : nat) :
  (j < 3)%nat -> UkShCat.cmd_cat !!! j <> (mword_of_int 0 : mword 8).
Proof using .
  intro Hj.
  do 3 (destruct j as [| j];
        [ intro Hc; apply (f_equal bv_unsigned) in Hc;
          vm_compute in Hc; discriminate Hc | ]). lia.
Qed.

Lemma sh_cat_pin_resolves :
  pin_resolves FsCatPin.era0_cat_pins FsImg.ROOTINO cat_pl
    [FsImg.ROOTINO; FsCatPin.CAT_INO] FsCatPin.CAT_INO
    ElfUser.cat_elf 1%nat.
Proof using .
  split_and!.
  - (* "cat" is RELATIVE, so the walk starts at the cwd -- the root *)
    unfold FsAbsEra.um_start_of.
    destruct (decide (cat_pl !! 0%nat = Some PathElems.SLASH)); reflexivity.
  - rewrite cat_path_elems. reflexivity.
  - intros v Hv. destruct Hv as (_ & Hnode & Hrun).
    rewrite cat_path_elems. split.
    + exact Hrun.
    + rewrite Hnode. rewrite FsCatPin.cat_bytes_elf. reflexivity.
Qed.

Section UShCatPay.
  (* THE KERNEL'S INSTANCE IS AMBIENT ([UexecExecInst] declares
     [uexecSG_xv6] and [uprogSG_gen] globally): NO [Context {SG}] /
     [Context {PS}] here, exactly as in [UShEcho] and [UShEchoPay]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).

  (* =================================================================== *)
  (*  2.  THE INGREDIENTS -- [UShEcho.sh_echo_slot] at /cat               *)
  (* =================================================================== *)
  Definition sh_cat_slot (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜FsCatPin.era0_cat_pins v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Global Instance sh_cat_slot_persistent T : Persistent (sh_cat_slot T).
  Proof using . rewrite /sh_cat_slot. apply _. Qed.

  (* ...AND THE ONE SEAM A PIPELINE ERA HAS TO MEET.  The claim's law is
     stated at the WHOLE of [FileFsPure.file_fs_pure] (that is what
     [AppPipeCons.pipe_fs_pure_acc] hands out, and [pipe_cat_pins_acc] is
     the same projection one level up), so this is the projection under
     the law's own box. *)
  Definition sh_cat_slot_of_fs_pure (T : iProp Σ) : iProp Σ :=
    (app_inv fsc_fs
     ∗ □ (∀ v : aview, app_pred app_run v -∗
                         app_pred app_run v
                         ∗ (⌜FileFsPure.file_fs_pure v⌝ ∨ T))
     ∗ □ (∀ (R : iProp Σ) (W : uvis),
            T -∗ my_pay (uvis_gen W) (fun _ => R)%I -∗
            □ (app_taint -∗ R) -∗ uslot W))%I.

  Lemma sh_cat_slot_of_fs_pure_holds (T : iProp Σ) :
    sh_cat_slot_of_fs_pure T -∗ sh_cat_slot T.
  Proof using .
    iIntros "(#Hinv & #Hcl & #Hgen)".
    rewrite /sh_cat_slot. iFrame "Hinv Hgen".
    iModIntro. iIntros (v) "Hp".
    iDestruct ("Hcl" $! v with "Hp") as "[$ [%Hpure | HT]]".
    - iLeft. iPureIntro. exact (FileFsPure.file_fs_pure_cat v Hpure).
    - iRight. iExact "HT".
  Qed.

  (* =================================================================== *)
  (*  3.  THE RIGHT COMMAND'S READINGS, OVER [ExecArgs] AND NOTHING ELSE  *)
  (* =================================================================== *)

  (* THE SHAPE: one argument, three bytes, none of them a NUL, terminated
     by the cut's own zero.  [UShEcho.echo_uargv_shape] at one token --
     and with no [line_ok], because the two things that lemma spends it on
     (the word count and the line's length bound) are closed numbers
     here. *)
  Lemma cat_uargv_shape (a b : nat) (sv : Z) (gn : nat -> bv 8) :
    0 < sv + Z.of_nat a ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_shape (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)).
  Proof using .
    intros Hs0 Hbytes.
    pose proof (UkShCat.cat_argv_bytes_end a b gn Hbytes) as Hb3.
    destruct Hbytes as (_ & Hin & Hnul).
    rewrite UkShCat.cmd_cat_len in Hin.
    split.
    - rewrite UkShCat.cat_cmd_args_length. unfold MAXARG. lia.
    - intros i x Hi.
      assert (Hi0 : i = 0%nat).
      { pose proof (lookup_lt_Some _ _ _ Hi) as Hlt.
        rewrite UkShCat.cat_cmd_args_length in Hlt. lia. }
      subst i.
      rewrite (UkShCat.cat_cmd_args_lookup a b sv gn Hb3) in Hi.
      injection Hi as <-.
      cbn [UserHeap.ua_ptr UserHeap.ua_len UserHeap.ua_bytes].
      split_and!.
      + exact Hs0.
      + lia.
      + split.
        * intros j Hj. rewrite (Hin j Hj).
          exact (cmd_cat_nonul j Hj).
        * rewrite <- UShEcho.ubyte0_moi0. rewrite <- Hb3. exact Hnul.
  Qed.

  (* ...and the node IS a [uargv_exec], off the heap the deposit lends *)
  Lemma cat_uargv_exec_of_cmd (a b : nat) (gd : gname) (t sv : Z)
      (gn : nat -> bv 8) :
    0 < sv + Z.of_nat a ->
    UkShCat.cat_argv_bytes a b gn ->
    ush_cmd gd t (UkShCat.cat_cmd a b sv gn) -∗
    uargv_exec gd (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)).
  Proof using .
    intros Hs0 Hbytes. iIntros "#Hc".
    iApply (UShEcho.uargv_exec_of_cmd gd t
              (UkShMain.ush_args sv gn (UkShCat.cat_toks a b))
              (cat_uargv_shape a b sv gn Hs0 Hbytes)).
    rewrite /UkShCat.cat_cmd. iExact "Hc".
  Qed.

  (* THE VECTOR IS DETERMINED BY THE NODE.  [UShEcho.echo_args_det_holds]
     at one token; the general agreement is [ExecArgs.uargv_det] and this
     is its projection. *)
  Lemma cat_args_det_1w (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) (na : nat) (alen : nat -> nat)
      (afun : nat -> nat -> bv 8) :
    0 < sv + Z.of_nat a ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    exec_args_of Mn (mword_of_int (t + 8) : mword 64) na alen afun ->
    na = 1%nat
    /\ alen 0%nat = 3%nat
    /\ (forall j : nat, (j < 3)%nat ->
          afun 0%nat j = UkShCat.cmd_cat !!! j).
  Proof using .
    intros Hs0 Hbytes Himg Hargs.
    pose proof (UkShCat.cat_argv_bytes_end a b gn Hbytes) as Hb3.
    pose proof Hbytes as Hbb. destruct Hbb as (_ & Hin & _).
    rewrite UkShCat.cmd_cat_len in Hin.
    set (args := UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) in *.
    assert (Hnth : ua_nth args 0%nat
                   = UArg (sv + Z.of_nat a) 3%nat
                       (fun j : nat => gn (a + j)%nat))
      by exact (ua_nth_lookup args 0%nat _
                  (UkShCat.cat_cmd_args_lookup a b sv gn Hb3)).
    destruct (uargv_det Mn (t + 8) args na alen afun
                (cat_uargv_shape a b sv gn Hs0 Hbytes) Himg Hargs)
      as (Hn & Hl & Hb).
    assert (Hna : na = 1%nat)
      by (rewrite Hn; exact (UkShCat.cat_cmd_args_length a b sv gn)).
    assert (Hlen0 : alen 0%nat = 3%nat).
    { rewrite (Hl 0%nat ltac:(lia)). rewrite /ua_alen Hnth. reflexivity. }
    split_and!; [ exact Hna | exact Hlen0 | ].
    intros j Hj.
    rewrite (Hb 0%nat j ltac:(lia) ltac:(rewrite Hlen0; lia)).
    rewrite /ua_afun Hnth. cbn [UserHeap.ua_bytes].
    exact (Hin j Hj).
  Qed.

  (* THE PATH: argv[0]'s string IS "cat", terminated.
     [UShEcho.sh_echo_path_of_holds] at one token, read off the general
     layout rather than off a word-list summary. *)
  Lemma cat_path_of_holds (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) :
    0 < sv + Z.of_nat a ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    exec_path_of Mn (mword_of_int (sv + Z.of_nat a) : mword 64) cat_pl.
  Proof using .
    intros Hs0 Hbytes Himg.
    pose proof (UkShCat.cat_argv_bytes_end a b gn Hbytes) as Hb3.
    pose proof Hbytes as Hbb. destruct Hbb as (_ & Hin & Hnul).
    rewrite UkShCat.cmd_cat_len in Hin.
    destruct Himg as (_ & _ & Hhi & _ & _ & Hrow).
    pose proof (UkShCat.cat_cmd_args_lookup a b sv gn Hb3) as Hlk.
    pose proof (Hhi 0%nat _ Hlk) as Hz64.
    cbn [UserHeap.ua_ptr UserHeap.ua_len] in Hz64.
    pose proof (Hrow 0%nat _ Hlk) as Hbyte.
    cbn [UserHeap.ua_ptr UserHeap.ua_len UserHeap.ua_bytes] in Hbyte.
    split_and!.
    - exact cat_pl_shape.
    - intros j c Hj.
      assert (Hjl : (j < 3)%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hlt.
        rewrite cat_pl_len in Hlt. exact Hlt. }
      rewrite (UShEcho.uint_avi_moi (sv + Z.of_nat a) (Z.of_nat j)
                 ltac:(lia) ltac:(lia) ltac:(unfold Z64 in *; lia)).
      rewrite (Hbyte j ltac:(lia)).
      f_equal.
      rewrite <- (list_lookup_total_correct _ _ _ Hj).
      rewrite (cat_pl_line j Hjl). exact (Hin j Hjl).
    - rewrite cat_pl_len.
      rewrite (UShEcho.uint_avi_moi (sv + Z.of_nat a) (Z.of_nat 3%nat)
                 ltac:(lia) ltac:(lia) ltac:(unfold Z64 in *; lia)).
      rewrite (Hbyte 3%nat ltac:(lia)).
      f_equal. rewrite <- UShEcho.ubyte0_bv0. rewrite <- Hb3. exact Hnul.
  Qed.

  (* =================================================================== *)
  (*  4.  THE (E) HALF, REPAIRED                                          *)
  (*                                                                     *)
  (*  [UCatPipe.pcat_image_entry] with its two unsatisfiable premises     *)
  (*  replaced by the reading the node actually supports.  Everything     *)
  (*  else -- [UShCat]'s whole geometry, [UCatPipe.pcat_pay_at] and       *)
  (*  [UkCatMain.wp_kcat_start] -- is the landed proof verbatim.          *)
  (* =================================================================== *)

  (* cat's 336-byte frame fits under a one-word push.  [UShCat.cat_room]
     is [line_ok]-free already; only [cat_room_of_det] was not. *)
  Lemma cat_room_1w (na : nat) (alen : nat -> nat) :
    na = 1%nat -> alen 0%nat = 3%nat ->
    kexec_sz ElfUser.cat_elf - PGSIZE + 336
      <= kxc_sp_final (kexec_sz ElfUser.cat_elf) alen na.
  Proof using .
    intros Hna Halen. subst na.
    replace 1%nat with (length [UkShCat.cmd_cat]) by reflexivity.
    apply (UShCat.cat_room [UkShCat.cmd_cat] alen).
    rewrite /UShCat.cat_argv_fits. cbn [length kxc_span].
    rewrite Halen. unfold PGSIZE. lia.
  Qed.

  Lemma cat_image_entry_1w (a b : nat) (Mn : gmap Z (bv 8)) (sv t : Z)
      (gn : nat -> bv 8) (sts : list fdstate) (cw : Z) (cs : gset gname)
      (pidv : mword 32) (Q : Z -> iProp Σ) (Pay : iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    0 < sv + Z.of_nat a ->
    UkShCat.cat_argv_bytes a b gn ->
    uargv_img Mn (t + 8) (UkShMain.ush_args sv gn (UkShCat.cat_toks a b)) ->
    length sts = NOFILE ->
    □ (∀ W' : uvis, ⌜uvis_fd W' = sts⌝ -∗ UCatPipe.pcat_pay_at W' Q Pay) -∗
    UkRun.urun_nopipe sts -∗ udep -∗
    image_entry ElfUser.cat_elf Mn (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q Pay uslot.
  Proof using xv6G0 ufdG0.
    intros HQc Hs0 Hbytes Himg Hfdl.
    iIntros "#Hpay #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (cat_args_det_1w a b Mn sv t gn na alen afun Hs0 Hbytes Himg
                Hargs) as (Hna & Halen & Hafun).
    pose proof (cat_room_1w na alen Hna Halen) as Hroom.
    rewrite /image_entry_at.
    iIntros "!>" (W') "%Hokk %Hcwv %Hlzf _ _ Hmp HPay".
    destruct (UShCat.cat_kexec_pages na alen afun sts W' Hokk)
      as (Hpc & Hsub & Hsub2 & Hx & Hdw & Hbufb & Hwr & Hrp).
    destruct (UShCat.cat_kexec_entry_rows na alen afun sts W' Hokk Hroom
                Hfdl Hwr Hrp)
      as (Hroom336 & Hal8 & Hszv & Hstkrow & Hargsrow & Havd & Havs
          & Hfdlen & Hstop).
    pose proof (UShCat.cat_kexec_bufrow na alen afun sts W' Hokk Hroom
                  Hdw Hbufb) as Hbuf.
    pose proof (UShCat.cat_kexec_argnz na alen afun sts W' Hokk Hroom)
      as Hnz.
    pose proof (kexec_image_ok_fd _ na alen afun sts W' Hokk) as Hfd.
    assert (Hargc0 : 0 <= uvis_argc W')
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargsrow)).
    assert (Hptr : forall (j : nat) (ga : uarg),
              UShCat.cat_args W' !! j = Some ga -> UserHeap.ua_ptr ga <> 0).
    { intros j ga Hj.
      assert (Hlt : (j < Z.to_nat (uvis_argc W'))%nat).
      { pose proof (lookup_lt_Some _ _ _ Hj) as Hl.
        rewrite /UShCat.cat_args echo_args_length in Hl. exact Hl. }
      rewrite /UShCat.cat_args (echo_args_lookup (uvis_M W') (uvis_av W')
                                  (Z.to_nat (uvis_argc W')) j Hlt) in Hj.
      injection Hj as <-. cbn [UserHeap.ua_ptr echo_arg].
      exact (Hnz j Hlt). }
    (* ---- THE KEY'S OWN WORD COUNT: the node sh built has ONE word ---- *)
    assert (Hno : forall i j : nat, (i < na)%nat -> (j < alen i)%nat ->
              afun i j <> ubyte0).
    { intros i j Hi Hj.
      assert (Hi0 : i = 0%nat) by lia. subst i.
      rewrite Halen in Hj.
      rewrite (Hafun j Hj). rewrite UShEcho.ubyte0_moi0.
      exact (cmd_cat_nonul j Hj). }
    destruct (UShCat.cat_key_args_holds na alen afun sts W' Hokk Hno)
      as [Hargcna _].
    assert (Hargc1 : Z.to_nat (uvis_argc W') = 1%nat)
      by (rewrite Hargcna; exact Hna).
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iApply (UShCat.cat_entry_run W' Q Hpc Hsub Hsub2 Hx Hroom336 Hal8
              Hstkrow Hbuf Hargsrow Havd Havs Hfdlen Hstop Hlzf
              with "Hdep Hnpw' Hmp").
    iIntros (N' h) "%Hpayeq Hstd Hcwf #Hcode #Hro #Hargv #HA Hbuf' Hrun".
    pose proof (ukn_const_of_eq N' Q Hpayeq HQc) as Htc.
    iDestruct ("Hpay" $! W' with "[%]") as "Hpay'"; [ exact Hfd | ].
    iDestruct ("Hpay'" $! N'
                 with "[%] [%] Hstd Hcode Hro Hargv HPay")
      as (Ci) "[Hp HCi]";
      [ exact Hpayeq | exact Hargc1 | ].
    iApply (wp_kcat_start N' h (tf_resume_gpr0 (uvis_tf W')) (uvis_av W')
              (UShCat.cat_args W') (fun _ : nat => ubyte0) 0%nat Ci
              Hptr
              ltac:(rewrite /UShCat.cat_args echo_args_length;
                    rewrite (Z2Nat.id (uvis_argc W') Hargc0);
                    unfold uvis_argc; symmetry; apply moi_of_uint)
              ltac:(unfold uvis_av; symmetry; apply moi_of_uint)
              with "Hp Hcode Hro Hargv HCi Hbuf' Hrun").
  Qed.

  (* =================================================================== *)
  (*  5.  THE ASSEMBLY: sh's pinned bundle pays its exec supply, PAID     *)
  (*                                                                     *)
  (*  [UShEchoPay.sh_exec_sup_echo_wq_holds_at_D] at /cat.  The payload   *)
  (*  is a CONSTANT family ([fun _ => Qc]), as the pipe arm's own         *)
  (*  [Qc] is; the lend [Cr] is what the PIPE arm's split hands the right *)
  (*  child ([RcR gp]), and the refund is the ledger fragment and that    *)
  (*  lend, WHOLE -- which is why the lend is never split here.           *)
  (* =================================================================== *)
  Lemma sh_exec_sup_cat_wq_holds_at
      (Fd0 : list fdstate -> Prop) (a b : nat)
      (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (Qc Cr : iProp Σ) :
    ⊢ □ (app_taint -∗ Qc) -∗
      (* THE ENTRY'S PAYMENT: cat's round at fd 0, and what its normal
         exit leaves.  [UCatPipe.pcat_pay_at_of_round] is the bridge and
         it is landed; this premise is exactly its own. *)
      □ (∀ (N'' : uk_names Σ) (l : list fdstate),
           ⌜ukn_pay N'' = (fun _ : Z => Qc)⌝ -∗ ⌜Fd0 l⌝ -∗
           UserFd.ustd (ukn_fd N'') l -∗ Cr -∗
           ∃ I Cend : iProp Σ,
             UkCatCat.kcat_round N'' (mword_of_int 0) I Cend ∗ I
             ∗ (Cend -∗ ukn_pay N'' (-1))) -∗
      sh_cat_slot T -∗ udep -∗
      UkShCat.sh_exec_sup_cat_at Fd0 a b (fun _ : Z => Qc) Cr.
  Proof using xv6G0 ghost_varG0 ghost_varG1 ufdG0 uartGhostG0.
    iIntros "#Hqt #Hround (#Hinv & #Hcl & #Hgen) #Hdep".
    rewrite /UkShCat.sh_exec_sup_cat_at.
    iIntros "!>" (N' m pc s0 t g ld)
      "%Hpeq %Ha0 %Ha1 %Hbytes %Hfd0 Hstd #Hcmd Hcr".
    (* ---- THE TAINT ARM: the generic slot at the chosen payload ---- *)
    iAssert (image_entry_taint T (fun _ : Z => Qc) uslot)%I as "#Hgen'".
    { rewrite /image_entry_taint. iModIntro. iIntros (W') "#HT #Hmp".
      iApply ("Hgen" $! Qc W' with "HT Hmp Hqt"). }
    (* ---- ...AND THE REST IS THE U-TIER RULE. ---- *)
    iApply (udepw_at_refR_of_sup N' m pc
              (mword_of_int (s0 + Z.of_nat a)) (mword_of_int (t + 8))
              FsImg.ROOTINO T cat_pl ElfUser.cat_elf 1%nat
              (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I
              _ UShCat.cat_elf_loadable Ha0 Ha1 with "[] [] [Hstd Hcr]").
    (* THE REFUND IS THE LEDGER AND THE LEND, WHOLE *)
    { iIntros "!> $". }
    { rewrite Hpeq. iExact "Hgen'". }
    rewrite /uexec_sup_run.
    iIntros (M pm sz fdv cs pidv) "#Hnpw Hheap Hufd".
    iDestruct (UkRun.urun_rows_nopipe _ _ with "Hnpw") as "#Hnp0".
    iDestruct (cat_cmd_str a b (ukn_d N') t s0 g
                 (UkShCat.cat_argv_bytes_end a b g Hbytes) with "Hcmd")
      as "[%Hsa _]".
    iDestruct (cat_uargv_exec_of_cmd a b (ukn_d N') t s0 g
                 ltac:(lia) Hbytes with "Hcmd") as "#Hvec".
    iDestruct (uargv_img_of_uargv (ukn_t N') (ukn_d N') (ukn_s N') M pm sz
                 (t + 8) _ with "Hheap Hvec") as %Himg.
    iDestruct (ufd_auth_len with "Hufd") as %Hlen.
    iDestruct (ustd_agree (ukn_fd N') fdv ld with "Hufd Hstd") as %Hl.
    iFrame "Hheap Hufd".
    iSplitR "Hstd Hcr".
    { iPureIntro.
      exact (cat_path_of_holds a b M s0 t g ltac:(lia) Hbytes Himg). }
    iSplitR "Hstd Hcr".
    { iApply (exec_walk_of_pin FsCatPin.era0_cat_pins T FsImg.ROOTINO
                cat_pl [FsImg.ROOTINO; FsCatPin.CAT_INO]
                FsCatPin.CAT_INO
                (MkAnode (AFile ElfUser.cat_elf) 1%nat) sh_cat_pin_resolves
                with "Hcl Hinv"). }
    iSplitR "Hstd Hcr".
    { rewrite Hpeq.
      iApply (cat_image_entry_1w a b M s0 t g fdv FsImg.ROOTINO cs pidv
                (fun _ : Z => Qc)
                (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I
                ltac:(intros x y; reflexivity) ltac:(lia) Hbytes Himg Hlen
                with "[] Hnp0 Hdep").
      iIntros "!>" (W') "%Hfdw".
      iApply (UCatPipe.pcat_pay_at_of_round W' (fun _ : Z => Qc)
                (UserFd.ustd (ukn_fd N') ld ∗ Cr)%I ld
                ltac:(rewrite Hfdw; exact Hl)).
      iIntros "!>" (N'') "%Hpeq'' Hstd'' [_ Hcr'']".
      iApply ("Hround" $! N'' ld with "[%] [%] Hstd'' Hcr''").
      - exact Hpeq''.
      - exact Hfd0. }
    iFrame "Hstd Hcr".
  Qed.

  (* =================================================================== *)
  (*  6.  THE CONSUMER TEST: the two halves composed, at a dummy payment  *)
  (*                                                                     *)
  (*  The seam the round will use, exercised once at the resource level:  *)
  (*  the supply above feeds [UkShCat.wp_kshr_exec_cat_at_holds] and what *)
  (*  comes out is a WP over sh's EXEC arm, with nothing left unsaid.     *)
  (* =================================================================== *)
  Lemma wp_kshr_exec_cat_paid (Fd0 : list fdstate -> Prop) (a b : nat)
      (T : iProp Σ) `{!Persistent T} `{!Timeless T}
      (Qc Cr Cd : iProp Σ)
      (N : uk_names Σ) (Hc : ukn_const N) (h : CpuId) (m : regfile)
      (t szv s0 : Z) (g : nat -> bv 8) (ld : list fdstate) (n : nat) :
    ukn_pay N = (fun _ : Z => Qc) ->
    m !!! Regidx a0_idx = (mword_of_int t : mword 64) ->
    UkShCat.cat_argv_bytes a b g ->
    Fd0 ld ->
    UkSh.ush_fd2p ld ->
    ⊢ □ (app_taint -∗ Qc) -∗
      □ (∀ (N'' : uk_names Σ) (l : list fdstate),
           ⌜ukn_pay N'' = (fun _ : Z => Qc)⌝ -∗ ⌜Fd0 l⌝ -∗
           UserFd.ustd (ukn_fd N'') l -∗ Cr -∗
           ∃ I Cend : iProp Σ,
             UkCatCat.kcat_round N'' (mword_of_int 0) I Cend ∗ I
             ∗ (Cend -∗ ukn_pay N'' (-1))) -∗
      sh_cat_slot T -∗ udep -∗
      shk_code (ukn_t N) -∗
      UkShDiag.ush_execfail_law_at PipeDisc.alt_execR 16%nat Cr Cd -∗
      □ (Cd -∗ Qc) -∗
      ush_jtab (ukn_t N) -∗
      ush_cmd (ukn_d N) t (UkShCat.cat_cmd a b s0 g) -∗
      usz (ukn_s N) szv -∗
      UserFd.ustd (ukn_fd N) ld -∗
      UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO -∗
      UserChildren.uch_any (ukn_ch N) -∗
      Cr -∗
      urun N h m (mword_of_int ShSyms.runcmd)
        (6 + (2 + (UkShDiag.ush_Dg + n))) -∗
      mWP (Loop : expr riscv_lang).
  Proof using xv6G0 ghost_varG0 ghost_varG1 ufdG0 uartGhostG0.
    intros Hpeq Ha0 Hbytes Hfd0 Hfd2.
    iIntros "#Hqt #Hround #Hslot #Hdep #Hcode #Hxl #Hcd #Hjt #Htree
             Hsz Hstd Hcwd Hch Hcr Hrun".
    iPoseProof (sh_exec_sup_cat_wq_holds_at Fd0 a b T Qc Cr
                  with "Hqt Hround Hslot Hdep") as "#Hsup".
    iApply (UkShCat.wp_kshr_exec_cat_at_holds Fd0 a b (fun _ : Z => Qc)
              Cr Cd N Hc h m t szv s0 g ld n
              Hpeq Ha0 Hbytes Hfd0 Hfd2
              with "Hcode Hsup Hxl [] Hjt Htree Hsz Hstd Hcwd Hch Hcr Hrun").
    iIntros "!> Hc". iApply ("Hcd" with "Hc").
  Qed.

End UShCatPay.
