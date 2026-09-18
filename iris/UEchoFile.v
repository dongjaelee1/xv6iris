(* ===================================================================== *)
(*  UEchoFile.v -- ECHO'S ENTRY AT fd 1 = `f` (lane SKELETON, K1).        *)
(*                                                                       *)
(*  design/app-file.md SS5.2: [UEchoOut.v] is echo's entry at fd 1 = the  *)
(*  CONSOLE; this is the twin at fd 1 = a HELD descriptor on `f`, with    *)
(*  the deed and [UserOff.uoff] in its [Pay].  echo's code walk is        *)
(*  untouched ([UkEcho.v]): the four writes are the same [kecho_w]        *)
(*  obligations, discharged at a LEDGER slot whose row is an inode        *)
(*  instead of the console device.                                       *)
(*                                                                       *)
(*  THIS FILE IS A SKELETON.  Every proof is [Admitted] and every fact    *)
(*  the kernel or the console tier still owes is a NAMED SECTION          *)
(*  HYPOTHESIS with its exact statement, so that the obligation list is   *)
(*  known before any further kernel lane runs (design SS3.6, review SSD4). *)
(*  It is in [_CoqProject] so that it BUILDS; nothing imports it, so      *)
(*  neither audit cone sees it.                                          *)
(*                                                                       *)
(*  WHAT ECHO PRINTS AT A FILE: nothing.  The round's alternative is      *)
(*  filed by SH at its next prompt byte (design SS4.2), out of the deed    *)
(*  echo returns; so the era's console credential crosses this entry      *)
(*  UNCHANGED -- it is [Wq] below, carried in and handed back at the      *)
(*  exit -- and no [out_link] is taken anywhere in this file.  That is    *)
(*  why the console side appears here only as one opaque [iProp].         *)
(*                                                                       *)
(*  WHAT ECHO CLOSES: nothing.  user/echo.c has no [close]; the fd-1 row  *)
(*  is torn down by [exit], so the deed and the advanced fragment ride    *)
(*  the EXIT payload ([ef_exit] below) and the descriptor goes with the   *)
(*  process.                                                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import VcGen.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require Import ExecEntry.               (* [image_entry] -- the exec channel *)
Require Import SpecKexec.               (* [kexec_image_ok] *)
Require Import UkRun UkRunSys.
Require Import UexecExecInst.           (* THE INSTANCES: [uexecSG_xv6] etc. *)
Require Import SpecSysRead.             (* [sys_rw_count] *)
Require Import SpecCopyin.              (* [ubytes_at] *)
Require Import SysWriteDefs.            (* [wri_pre], [wchunks], [FW_MAX] *)
Require Import SpecFilewrite.
Require Import UkWriteLeaf.
Require Import UkWriteFile.             (* [write_file_fam], the handle-fixed leaf *)
Require Import UkAbi.
Require Import FsBlocks.
Require Import FsNode.
Require Import FsAbsDefs.
Require Import FsAbsDelta.
Require Import FsBytesGamma.
Require Import FsCfg.
Require Import AppCfg.
Require Import AppInv.
Require Import FsImg.
Require Import FsImgCheck.
Require Import FsInitPin FsShPin FsEchoPin FsCatPin.
Require Import EchoDisc.
Require Import EchoOut.
Require Import LineWords.
Require Import FileState.                (* [echo_chunks], [subseq], [sel_ok] *)
Require Import AppEcho.
Require Import AppFile.
Require Import UserOff.                  (* [uoff] -- THE PROGRAM'S HALF *)
Require Import FsAbsWriteFire.           (* [awrite_chain] and its two nodes *)
Require Import FsAbsInvFire.
Require Import UserHeap.
Require Import UCodeEcho.
Require Import UkEcho.
Require Import UEchoKernel.
Require Import UEchoOut.                 (* THE MOULD *)
Require Import ElfUser.                  (* [echo_elf] *)
Require Import UkShEcho.                 (* [echo_argv_bytes] *)
Require Import UShEcho.                  (* [echo_node_img], [echo_image_entry] *)
Require Import CtxIdDefs.
Require User.EchoSyms.
Require Import SpecWritei.               (* [wi_blocks]: the single-block shape *)
Require Import FileWrite.                (* [file_wq], [file_awrite_node] *)
Require Import FsAbs.                    (* [γtop] -- FsAbs's own rule *)
Local Open Scope Z_scope.
Import Defs.

Section UEchoFile.
  (* [UEchoOut.v]'s binder list, plus the file claim's classes.  NO
     [uexecSG] and NO [uprogSG] SECTION VARIABLE (durable-notes, "A
     section variable of a class type is a LOCAL INSTANCE"): this file
     reads row 16's CONCRETE arm and applies [UkWriteFile]'s members, so
     the instances must be the ambient [UexecExecInst] ones and the
     deposit instance is named PER LEMMA where it matters. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ}.

  (* the claim: its fixed part, its names, and the record equation every
     [AppFile] lemma is read at *)
  Context (c : file_fixed) (r : file_names).
  Context (Heq : file_app = MkAppcfg file_names (file_pred c) r).

  (* THE ERA'S CONSOLE CREDENTIAL, OPAQUE.  echo writes no console byte at
     a file, so what the fork lent ([UkShFork.ushf_wq]'s left arm) crosses
     this entry untouched and is handed back at the exit.  Keeping it
     abstract is what keeps this file out of [EchoLinks]' cone, which is
     what lane LINK-GEN is about. *)
  Context (Wq : iProp Σ).

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* =================================================================== *)
  (*  S1  THE CURSOR: THE DEED AND THE FRAGMENT AT ONE POSITION           *)
  (*                                                                     *)
  (*  [UEchoOut.ech] is echo's console cursor; this is its twin at the     *)
  (*  file.  [FileWrite.file_wq] already ties the deed's content to the    *)
  (*  chunk subset and pins the offset to its length, so the ONLY thing    *)
  (*  added here is the program's own half of the offset shadow            *)
  (*  ([UserOff.uoff]) AT THAT SAME LENGTH.  That coincidence is the       *)
  (*  whole of RELAY 2: a node whose closure holds this learns the fire's  *)
  (*  offset by [OffGv.off_gv_agree] and owes the kernel nothing.          *)
  (* =================================================================== *)
  Definition efq (i : Z) (γo : gname) (ws : wordline) (sel : list nat)
      : iProp Σ :=
    (file_wq c r i ws sel (length (subseq (echo_chunks ws) sel))
     ∗ uoff γo (length (subseq (echo_chunks ws) sel)))%I.

  (* ...AND THE CHAIN CURSOR, indexed by the node number [k] the kernel is
     at.  Write call [j] fires ONE chunk (every one of echo's chunks is a
     word of a line, so [wchunks n = 1]), so the chain's node [k] is at the
     selection extended by [k] indices beyond [sel0]. *)
  Definition efcur (i : Z) (γo : gname) (ws : wordline) (sel0 : list nat)
      (j : nat) : nat -> iProp Σ :=
    fun k => (∃ sel : list nat,
                ⌜sel = sel0 \/ sel = sel0 ++ [j]⌝
                ∗ ⌜(k = 0)%nat -> sel = sel0⌝
                ∗ efq i γo ws sel)%I.

  (* THE EXIT PAYLOAD ([UkShFork.ushf_wq]'s twin, design SS3): the era's
     credential as it was lent, the deed at WHATEVER prefix of the chunks
     landed, and the fragment advanced to that content's length.  STATUS
     INDEPENDENT, which is what [UkRun.ukn_const] asks of an entry. *)
  Definition ef_exit (i : Z) (γo : gname) (ws : wordline) : iProp Σ :=
    (Wq ∗ ∃ sel : list nat, efq i γo ws sel)%I.

  (* =================================================================== *)
  (*  S2  WHAT LANE OFF-LINK WILL MAKE [awrite_full_at] BE                *)
  (*                                                                     *)
  (*  design SS3, "THE LINK IS THE NODE": phase 2 hands the kernel's half  *)
  (*  back ADVANCED instead of unmoved, and the chain names the chunk it   *)
  (*  fires.  Both are written out here so that the two hypotheses below   *)
  (*  are statements and not gestures.  Delete the [⌜bs = bsk⌝] arrow and  *)
  (*  advance nothing and [ef_full_adv] is [FsAbsWriteFire.awrite_full_at] *)
  (*  verbatim.                                                           *)
  (* =================================================================== *)
  Definition ef_full_adv (γfs : fs_names) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (n : Z) (k : nat)
      (bsk : list (bv 8)) (REST : iProp Σ) : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
       ⌜ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k)) bs⌝ -∗
       (* RELAY 3 -- LANDED (lane WRITE-RELAY): the node carries the count
          the fire was called with, and it is the chain's own chunk. *)
       ⌜Z.of_nat (length bs) = wchunk_at n k⌝ -∗
       (* ...so the client may ALSO assume the bytes are its chunk, which is
          what [ef_full_adv_of] below discharges off [ubytes_at_inj]. *)
       ⌜bs = bsk⌝ -∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I -∗
       off_link γo (Z.of_nat off) ={appE}=∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
       app_step i I (delta_write i off bs (abs_view I)) ∗
       (∀ I' : gmap Z fs_node,
          ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
          ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
          ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ∗
          (* THE ADVANCE (lane OFF-LINK): [UserOff.uoff_advance] is exactly
             this step, holder-side -- and at a DISCONNECTED object there is
             no other half to move, so what comes back is the lend itself.
             [OffGv.off_ret] is the pair, [off_ret_adv] the arm a node that
             holds the program's half proves. *)
          off_ret γo off (length bs) ∗ REST))%I.

  (* ...the same without RELAY 3's arrow: what OFF-LINK alone leaves. *)
  Definition ef_full_adv_raw (γfs : fs_names) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (n : Z) (k : nat) (REST : iProp Σ)
      : iProp Σ :=
    (∀ (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       ⌜wri_pre (abs_view I) i off bs bs0 nl⌝ -∗
       ⌜ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k)) bs⌝ -∗
       ⌜Z.of_nat (length bs) = wchunk_at n k⌝ -∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I -∗
       off_link γo (Z.of_nat off) ={appE}=∗
       ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I ∗
       app_step i I (delta_write i off bs (abs_view I)) ∗
       (∀ I' : gmap Z fs_node,
          ⌜abs_view I' = delta_write i off bs (abs_view I)⌝ -∗
          ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ={appE}=∗
          ghost_map_auth (γtop (fs_gamma_L γfs)) (1/2) I' ∗
          off_ret γo off (length bs) ∗ REST))%I.

  (* ---- WAS HYPOTHESIS 1 ([Hoff_link]); NOW A LEMMA -------------------- *)
  (* Lane WRITE-RELAY-2 made the node's answer a CHOICE: phase 2 returns
     [OffGv.off_ret γo off (length bs)], "the borrow unmoved OR advanced by
     the chunk", and [off_ret_adv] is the arm a node that holds the
     program's half proves.  So the advanced node IS a kernel node, and the
     resource-home defect the review's SSA1 named is gone. *)
  Lemma ef_off_link (γfs : fs_names) (i : Z) (γo : gname) (M : gmap Z (bv 8))
      (ua : mword 64) (n : Z) (k : nat) (REST : iProp Σ) :
    ef_full_adv_raw γfs i γo M ua n k REST ⊢
    awrite_full_at (fs_gamma_L γfs) appE i γo M ua n k REST.
  Proof using .
    rewrite /ef_full_adv_raw /awrite_full_at.
    iIntros "Hn" (I off bs bs0 nl) "%Hpre %Hby %Hlen Hka Hg".
    iMod ("Hn" $! I off bs bs0 nl with "[//] [//] [//] Hka Hg")
      as "(Hka & Hstep & Hph2)".
    iModIntro. iFrame "Hka Hstep". iIntros (I') "%Hav Hka'".
    iMod ("Hph2" $! I' with "[//] Hka'") as "(Hka' & Hg & Hrest)".
    iModIntro. iFrame "Hka' Hrest". iExact "Hg".
  Qed.

  (* ---- WAS HYPOTHESIS 2 (RELAY 3); NOW A LEMMA ----------------------- *)
  (* [SpecCopyin.ubytes_at] is prefix-closed, so the content tie alone does
     not identify [bs] with the chunk -- but the node now carries the LENGTH
     the fire was called with, and two runs of one length at one base are
     one run ([SpecCopyin.ubytes_at_inj]).  The two premises are rows a
     writer holds about its OWN buffer. *)
  Lemma ef_full_adv_of (γfs : fs_names) (i : Z) (γo : gname)
      (M : gmap Z (bv 8)) (ua : mword 64) (n : Z) (k : nat)
      (bsk : list (bv 8)) (REST : iProp Σ) :
    ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k)) bsk ->
    Z.of_nat (length bsk) = wchunk_at n k ->
    ef_full_adv γfs i γo M ua n k bsk REST ⊢
    ef_full_adv_raw γfs i γo M ua n k REST.
  Proof using .
    intros Hbsk Hlenk. rewrite /ef_full_adv /ef_full_adv_raw.
    iIntros "Hn" (I off bs bs0 nl) "%Hpre %Hby %Hlen".
    assert (Hbs : bs = bsk).
    { apply (ubytes_at_inj M (add_vec_int ua (FW_MAX * Z.of_nat k))
               bs bsk Hby Hbsk). lia. }
    iApply ("Hn" $! I off bs bs0 nl with "[//] [//] [//] [//]").
  Qed.

  (* ---- HYPOTHESIS 3 (lane WRITE-RELAY, RELAY 4) ---------------------- *)
  (* READ-RELAY's shape one syscall over ([FsAbsReadFire.read_arms_mapped],
     [SysReadDefs.rd_fail_why_refute]): the PARTIAL arm is reachable for
     exactly one reason -- writei's copyin faulted -- so once the partial
     node carries that reason, a caller whose whole SOURCE run is mapped
     refutes its premise and the node is vacuously suppliable at ANY
     [REST].  Without it [AppFile.f_typed] cannot be re-established on
     that arm at all ([FileWrite.v]'s header (3)), and the arm is one of
     the two the kernel may pick at EVERY node. *)
  (* ---- WAS HYPOTHESIS 3 (RELAY 4); NOW A LEMMA ----------------------- *)
  (* Lane WRITE-RELAY-2 put BOTH of the arm's reasons on the node: the
     disturbed tail's ([SysWriteDefs.wr_fail_why], out of
     [SpecEitherCopyin]) and the single-block all-or-nothing
     ([SpecWritei.wi16_atomic]).  At a source run every byte of which is
     readable-mapped -- which is [UkRunSys.usrc_ok]'s SECOND conjunct, the
     write leaf's own row -- and a chunk that cannot straddle a block
     boundary, the arm is vacuous ([FsAbsWriteFire.awrite_part_at_mapped_single]).
     The straddle premise is the DEED's: it knows [off] is the content's
     length and the content is a line's worth
     ([FileDeltas.f_bytes_typed_short], [EchoDisc.line_max] = 100 < BSIZE). *)
  Lemma ef_relay4 (γfs : fs_names) (i : Z) (γo : gname) (M : gmap Z (bv 8))
      (pmv : gmap (mword 27) uperm) (sz : Z) (P : uptd)
      (ua : mword 64) (nb : nat) (f : nat -> bv 8)
      (n : Z) (k : nat) (REST : iProp Σ) :
    usrc_ok M pmv sz ua nb f ->
    ProcPtOwn.proc_pt_wf P ->
    perm_of (ud_um P) sz = pmv ->
    lazy_free (ud_um P) sz ->
    (Z.to_nat n <= nb)%nat ->
    (forall (I : gmap Z fs_node) (off : nat) (bs bs0 : list (bv 8)) (nl : nat),
       wri_pre (abs_view I) i off bs bs0 nl ->
       wi_blocks off (Z.to_nat (wchunk_at n k)) = 1%nat) ->
    ⊢ awrite_part_at (fs_gamma_L γfs) appE i γo M ua P n k REST.
  Proof using .
    intros Hsrc Hwf Hpm Hlf Hnb Hsb.
    assert (Hmap : forall j : nat, (j < Z.to_nat n)%nat ->
              uva_rmapped P (uint (add_vec_int ua (Z.of_nat j)))).
    { intros j Hj. exact (proj2 Hsrc P j Hwf Hpm Hlf ltac:(lia)). }
    iApply (awrite_part_at_mapped_single (fs_gamma_L γfs) appE i γo M ua P n k
              REST Hmap Hsb).
  Qed.

  (* =================================================================== *)
  (*  S3  THE TWO LEDGER-SLOT PIECES THE ENGINE OWES (review SSC1.4, D7)   *)
  (*                                                                     *)
  (*  [UkWriteFile.wp_uk_ecall_write_file] is HANDLE-FIXED: its           *)
  (*  descriptor knowledge is [UserFd.ufd] at [fd] with [NSTD <= fd]      *)
  (*  implicit in every caller, and its deposit is [UkRun.udepwf_st],     *)
  (*  the [fd_st_of_key]-indexed one.  echo writes fd 1, a LEDGER slot,   *)
  (*  whose knowledge is [UserFd.ustd] and whose deposit is               *)
  (*  [UkRun.udepwf_std].  These two hypotheses are that pair.            *)
  (* =================================================================== *)

  (* ---- HYPOTHESIS 4 (NEW; ~20 lines beside [udepwf_st_write_file]) --- *)
  Hypothesis Hdep1 :
    forall (N : uk_names Σ) (m : regfile) (pc : mword 64)
           (l : list fdstate) (rb : bool) (i : Z) (γo : gname)
           (om : offmode) (Q : nat -> iProp Σ) (n : Z),
      l !! 1%nat = Some (FdOpen rb true (FdInode i γo om)) ->
      bv_signed (trunc32 (m !!! Regidx a0_idx)) = 1%Z ->
      sys_rw_count (m !!! Regidx a2_idx) = n ->
      (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
         uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
         uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
         awrite_chain (fs_gamma_L fsc_fs) appE i γo M (m !!! Regidx a1_idx) n
           Q 0%nat (wchunks n)) -∗
      udepwf_std N m pc 16 (write_file_fam Q (ukn_pay N)) l.

  (* ---- HYPOTHESIS 5 (NEW; the ledger-slot write leaf) ---------------- *)
  (* [UkRunSys.wp_uk_ecall_write_at] at [K fdv := take NSTD fdv = l], i.e.
     [UkWriteFile.wp_uk_ecall_write_file] with [UserFd.ufd] replaced by
     [UserFd.ustd] and [udepwf_st] by [udepwf_std].  Nothing about the
     file is in it; it is the console leaf's twin at an arbitrary row. *)
  Hypothesis Hwrite1 :
    forall (N : uk_names Σ) (h : CpuId) (m : regfile) (pc : mword 64)
           (avail : nat) (fdep : sfam) (l : list fdstate)
           (S : iProp Σ) (nb : nat) (f : nat -> bv 8),
      usysno m = 16 ->
      bv_signed (trunc32 (m !!! Regidx a0_idx)) = 1%Z ->
      is_aligned_vaddr (Virtaddr (add_vec_int pc 4)) 2 = true ->
      (forall (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z),
         uheap (ukn_t N) (ukn_d N) (ukn_s N) M pmv sz -∗ S -∗
         ⌜usrc_ok M pmv sz (m !!! Regidx a1_idx) nb f⌝) ->
      uinstr_is (ukn_t N) pc false (ECALL tt) -∗
      urun N h m pc avail -∗
      udepwf_std N m pc 16 fdep l -∗
      UserFd.ustd (ukn_fd N) l -∗
      S -∗
      (∀ (h' : CpuId) (rv : mword 64) (W : uvis) (cw' : Z)
         (cs' : gset gname),
         ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
         ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
         ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
         ⌜take NSTD (uvis_fd W) = l⌝ -∗
         ⌜uvis_lazy W = false⌝ -∗
         ⌜usrc_ok (uvis_M W) (uvis_perm W) (uvis_sz W)
            (m !!! Regidx a1_idx) nb f⌝ -∗
         UserFd.ustd (ukn_fd N) l -∗
         S -∗
         spost_at uslot 16 fdep W rv (uvis_M W) (uvis_fd W) cw' cs' -∗
         urun N h' (<[Regidx a0_idx := rv]> m) (add_vec_int pc 4) avail -∗
         WP (Loop : expr riscv_lang)) -∗
      WP (Loop : expr riscv_lang).

  (* =================================================================== *)
  (*  S4  ONE CHUNK, AS A CHAIN NODE                                      *)
  (*                                                                     *)
  (*  [FileWrite.file_awrite_node] IS the node modulo the three relays;    *)
  (*  RELAY 1 (the row the fire is at is `f`'s) comes off the deed's own   *)
  (*  inum, RELAY 2 is [UserOff.uoff_agree_k] inside the node, and RELAY 3 *)
  (*  is LANDED -- [ef_full_adv_of] above.  What this lemma adds to        *)
  (*  [file_awrite_node] is the FRAGMENT: it goes in at [off] and comes    *)
  (*  out at [off + |chunk|] ([ef_off_link]).                              *)
  (* =================================================================== *)
  Lemma ef_node (i : Z) (γo : gname) (ws : wordline) (sel : list nat)
      (jx : nat) (M : gmap Z (bv 8)) (ua : mword 64) (n : Z) (k : nat) :
    (jx < length (echo_chunks ws))%nat ->
    Forall (fun q => (q < jx)%nat) sel ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    app_inv fsc_fs -∗ efq i γo ws sel -∗
    awrite_full_at (fs_gamma_L fsc_fs) appE i γo M ua n k
      (efq i γo ws (sel ++ [jx])).
  Proof using Heq.
  Admitted.

  (* ...AND THE WHOLE CALL'S CHAIN, at the ONE node echo's chunk needs.
     [wchunks n] is 1 for every one of echo's calls: a chunk is a word of
     a line or a single blank, and [FW_MAX] is 3072. *)
  Lemma ef_chain (i : Z) (γo : gname) (ws : wordline) (sel : list nat)
      (jx : nat) (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z)
      (ua : mword 64) (nb : nat) (f : nat -> bv 8) (n : Z) :
    usrc_ok M pmv sz ua nb f ->
    n = Z.of_nat nb ->
    (0 < nb)%nat -> (Z.of_nat nb <= FW_MAX)%Z ->
    (jx < length (echo_chunks ws))%nat ->
    Forall (fun q => (q < jx)%nat) sel ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    app_inv fsc_fs -∗ efq i γo ws sel -∗
    awrite_chain (fs_gamma_L fsc_fs) appE i γo M ua n
      (efcur i γo ws sel jx) 0%nat (wchunks n).
  Proof using Heq.
  Admitted.

  (* =================================================================== *)
  (*  S5  ONE OF ECHO'S FOUR WRITES, AT fd 1 ON `f`                       *)
  (*                                                                     *)
  (*  [UEchoOut.kecho_w_of_link_data]'s twin: where the console member     *)
  (*  spends the era's write link, this one spends the chunk chain.  The   *)
  (*  SOURCE is argv's string ([UserHeap.ubytesq], persistent) or one of   *)
  (*  echo's two .rodata bytes ([UserHeap.utext]); only the first is       *)
  (*  written here, because at a file the separator and the newline are    *)
  (*  chunks like any other and take the same member -- the TEXT-half      *)
  (*  variant differs only in which [usrc_ok] witness is produced.         *)
  (* =================================================================== *)
  Lemma ef_w_of_deed (N : uk_names Σ) (i : Z) (γo : gname) (om : offmode)
      (l : list fdstate) (rb : bool) (ws : wordline) (sel : list nat)
      (jx : nat) (ua : Z) (nb : nat) (fb : nat -> bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo om)) ->
    (0 < nb)%nat -> (Z.of_nat nb <= FW_MAX)%Z -> (Z.of_nat nb < 2 ^ 31)%Z ->
    (jx < length (echo_chunks ws))%nat ->
    Forall (fun q => (q < jx)%nat) sel ->
    echo_chunks ws !!! jx = (fun j => fb j) <$> seq 0 nb ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    app_inv fsc_fs -∗
    ubytesq (ukn_d N) DfracDiscarded ua nb fb -∗
    kecho_w N (mword_of_int ua) nb
      (UserFd.ustd (ukn_fd N) l ∗ efq i γo ws sel)
      (UserFd.ustd (ukn_fd N) l ∗ efq i γo ws (sel ++ [jx])).
  Proof using Heq Hdep1 Hwrite1.
  Admitted.

  (* =================================================================== *)
  (*  S6  THE PAYMENT -- [UEchoOut.kecho_pay_of_link]'s twin              *)
  (*                                                                     *)
  (*  The recursion is the SAME one ([UkEcho.kecho_pay] on the argument    *)
  (*  count); what changes is that the cursor is the DEED and the chunk    *)
  (*  index advances with it, so argument [q] is chunk [2*(q-1)] and the    *)
  (*  separator after it chunk [2*(q-1)+1] ([FileState.echo_args_chunks]). *)
  (* =================================================================== *)
  Lemma ef_pay_all (N : uk_names Σ) (i : Z) (γo : gname) (om : offmode)
      (l : list fdstate) (rb : bool) (ws : wordline) (av : Z)
      (args : list uarg) :
    (2 <= length ws)%nat ->
    UEchoOut.echo_out_argv ws args ->
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo om)) ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (ef_exit i γo ws -∗ ukn_pay N (-1)) -∗
    Wq -∗
    app_inv fsc_fs -∗
    uargv (ukn_d N) av args -∗
    kecho_pay_all N args
      (UserFd.ustd (ukn_fd N) l ∗ efq i γo ws [])
      (ukn_pay N (-1)).
  Proof using Heq Hdep1 Hwrite1.
  Admitted.

  (* =================================================================== *)
  (*  S7  THE PAID ENTRY -- [UEchoOut.echo_uexec_slot_at]'s mould         *)
  (*                                                                     *)
  (*  Every premise about the KEY is echo's own and is copied verbatim     *)
  (*  from the console twin; the two that are new are the LEDGER ROW       *)
  (*  (fd 1 is an inode open for writing, not the console device) and      *)
  (*  the LEND, which is the deed and the fragment instead of the era's    *)
  (*  cursor.                                                             *)
  (* =================================================================== *)
  Lemma efile_uexec_slot_at (W : uvis) (i : Z) (γo : gname) (om : offmode)
      (rb : bool) (ws : wordline) (Q : Z -> iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    (2 <= length ws)%nat ->
    UEchoOut.echo_out_argv ws
      (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))) ->
    (* THE LEDGER ROW: fd 1 is `f`, held for writing (design SS3, the
       child's REDIR arm) -- where the console twin asks for
       [FdOpen rb true (FdDevice CONSOLE)]. *)
    take NSTD (uvis_fd W) !! 1%nat
      = Some (FdOpen rb true (FdInode i γo om)) ->
    tf_resume_pc (uvis_tf W) = (mword_of_int EchoSyms.start : mword 64) ->
    echo_text_sub (uvis_M W) ->
    echo_data_sub (uvis_M W) ->
    (forall a : Z, 0 <= a < 4096 ->
       ux_addr (uvis_perm W) a /\ ~ uw_addr (uvis_perm W) a) ->
    96 <= uint (uvis_sp W) ->
    uint (uvis_sp W) mod 8 = 0 ->
    (forall j : nat, (j < 8 * 12)%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uint (uvis_sp W) - 8 * Z.of_nat 12 + Z.of_nat j)%Z)) ->
    uk_args_c (uvis_perm W) (uvis_M W) (uvis_av W) (uvis_argc W)
      (uint (uvis_sp W)) ->
    (forall j : nat, (j < 8 * Z.to_nat (uvis_argc W))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uvis_av W + Z.of_nat j)%Z)) ->
    (forall i0 j : nat, (i0 < Z.to_nat (uvis_argc W))%nat ->
       (j <= Z.to_nat (uk_slens (uvis_M W) (uvis_av W) (Z.of_nat i0)))%nat ->
       is_Some (udata_lo (uvis_M W) (uvis_perm W) (uvis_sz W)
                 !! (uk_argv_p (uvis_M W) (uvis_av W) (Z.of_nat i0)
                     + Z.of_nat j)%Z)) ->
    length (uvis_fd W) = NOFILE ->
    (forall (p : mword 27) (q : uperm), uvis_perm W !! p = Some q ->
       bv_unsigned p * 4096 < UserPtTree.pgroundup (uvis_sz W)) ->
    uvis_lazy W = false ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (ef_exit i γo ws -∗ Q (-1)) -∗
    app_inv fsc_fs -∗
    UkRun.urun_nopipe (uvis_fd W) -∗
    udep (PS := uprogSG_free) -∗
    my_pay (uvis_gen W) Q -∗
    (* ---- THE LEND, and this is [Hexec_pay]'s content: the era's
            credential, the DEED at `f` empty, and the program's own half
            of the offset shadow at ZERO. ---- *)
    Wq -∗
    efq i γo ws [] -∗
    uslot W.
  Proof using Heq Hdep1 Hwrite1.
  Admitted.

  (* =================================================================== *)
  (*  S8  THE EXEC CROSSING -- [Hexec_pay] AS A STATEMENT                 *)
  (*                                                                     *)
  (*  [ExecEntry.image_entry]'s [Pay] slot is where a process's LINEAR     *)
  (*  resources cross exec -- design SS3 says the process's resources      *)
  (*  cross exec and only the address space is replaced -- and this is     *)
  (*  what the file application puts there.                                *)
  (*  file application puts there.  Three things, and the fd-1 row is NOT  *)
  (*  one of them: it is a PURE fact about [sts], the table the exec       *)
  (*  channel carries verbatim ([SpecKexec.kexec_image_ok]'s fd clause).   *)
  (* =================================================================== *)
  Definition ef_pay (i : Z) (γo : gname) (ws : wordline) : iProp Σ :=
    (Wq ∗ efq i γo ws [])%I.

  (* ...AND THE ENTRY AT THE CHANNEL -- [UShEcho.echo_image_entry]'s
     shape, with the paid constructor and the file lend.  This is what
     lane SH-ROUND's redirect child applies after its [exec /echo]. *)
  Lemma efile_image_entry (ws : wordline) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32)
      (i : Z) (γo : gname) (om : offmode) (rb : bool) :
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t g ->
    UkShEcho.echo_argv_bytes ws g ->
    length sts = NOFILE ->
    (* THE CHILD'S fd 1 IS `f`: a pure row about the exec'ing process's
       own table, which is the child's after [close(1); open(f, 0x601)]. *)
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdInode i γo om)) ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (ef_exit i γo ws -∗ ef_exit i γo ws) -∗
    app_inv fsc_fs -∗
    UkRun.urun_nopipe sts -∗
    udep (PS := uprogSG_free) -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv (fun _ : Z => ef_exit i γo ws) (ef_pay i γo ws) uslot.
  Proof using Heq Hdep1 Hwrite1.
  Admitted.

End UEchoFile.
