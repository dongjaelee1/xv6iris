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
(*  PROVED.  It began as lane SKELETON's obligation list (design SS3.6,  *)
(*  review SSD4); every obligation has since been discharged, and         *)
(*  [UShRound] spends [efile_image_entry] (K1) through                    *)
(*  [UShRedirPay], so this file is in the file theorem's cone.  In        *)
(*  design/app-both.md SS5 it is the FILE instance of echo's output      *)
(*  endpoint: [efq] is [Out 1 S] at the deed.                            *)
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
Require Import UkAbi.
Require Import FsBlocks.
Require Import FsNode.
Require Import FsAbsDefs.
Require Import FsAbsDelta.
Require Import FsBytesGamma.
Require Import FsCfg.
Require Import AppCfg.
Require Import AppInv.
Require Import FsInitPin FsShPin FsEchoPin FsCatPin.
Require Import EchoDisc.
Require Import EchoOut.
Require Import LineWords.
Require Import FileState.                (* [echo_chunks], [subseq], [sel_ok] *)
Require Import AppFile.
Require Import FsAbsWriteFire.           (* [awrite_chain] and its two nodes *)
Require Import UserHeap.
Require Import UCodeEcho.
Require Import UkEcho.
Require Import UEchoKernel.
Require Import UEchoOut.                 (* THE MOULD *)
Require Import ElfUser.                  (* [echo_elf] *)
Require Import UkShEcho.                 (* [echo_argv_bytes] *)
Require Import UShEcho.                  (* [echo_node_img], [echo_image_entry] *)
Require Import UShEchoOut.               (* [echo_out_argv_of_image] *)
Require Import UShKernel.                (* [uimg_sub_union_l] *)
Require Import ElfFile.                  (* [elf_image] *)
Require Import CtxIdDefs.
Require User.EchoSyms.
Require Import FileWritePart.            (* [file_awrite_part_adv]: the partial arm, from the cursor *)
Require Import FileWrite.                (* [file_wq], [file_awrite_node] *)
Require Import UkWriteFile.              (* the two ledger-slot write leaves *)
Local Open Scope Z_scope.
Import Defs.

(* [UShEchoPay.echo_data_of_elf_image] duplicated here rather than
   imported: that file sits ABOVE this one (it is the shell's paid
   assembly) and this entry is below it.  Five lines, and the two halves
   of echo's ELF image commute. *)
Lemma efile_union_comm_bool :
  bool_decide (EchoInstrs.echo_bytes ∪ EchoData.echo_data
               = EchoData.echo_data ∪ EchoInstrs.echo_bytes) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma efile_data_of_elf_image (M : gmap Z (bv 8)) :
  uimg_sub (elf_image ElfUser.echo_elf) M -> echo_data_sub M.
Proof.
  intros H. rewrite ElfUser.echo_elf_image in H.
  apply UShKernel.uimg_sub_union_l in H.
  rewrite (bool_decide_eq_true_1 _ efile_union_comm_bool) in H.
  exact (UShKernel.uimg_sub_union_l _ _ _ H).
Qed.

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
  (* RULING EFQ.  The landed cursor was the CONJUNCTION

       file_wq c r i ws sel (length (subseq (echo_chunks ws) sel))
       ∗ uoff γo (length (subseq (echo_chunks ws) sel))

     and that is not a statable cursor: [file_wq] is itself a pipe (its
     right arm is [file_taint c]), so the conjunction pins the program's
     half to the CONTENT'S LENGTH even on the arm where nobody owes
     anything about the content.  Nothing supplies that -- a hijacker who
     moved [f->off] left the shadow wherever it liked -- so the write
     node's taint arm was unprovable AT THE STATEMENT.

     The owner's shape is the pipe, and it is [FileWrite.file_cur]:

       FIRED:   file_wq at the content, and the half AT ITS LENGTH
       TAINTED: file_taint c, and the half wherever it is.

     [efq] is that cursor at this entry's claim; the definition is one
     name so that the node, the chain and the exit payload cannot drift. *)
  Definition efq (i : Z) (γo : gname) (ws : wordline) (sel : list nat)
      : iProp Σ := file_cur c r i ws sel γo.

  (* ...AND THE CHAIN CURSOR, indexed by the node number [k] the kernel is
     at.  Write call [j] fires ONE chunk (every one of echo's chunks is a
     word of a line, so [wchunks n = 1]), so the chain's node [k] is at the
     selection extended by [k] indices beyond [sel0]. *)
  (* ...AND IT IS EXACT, not a disjunction of two positions.  The landed
     cursor existentially quantified the selection and constrained it only
     at [k = 0], which cannot be the shape: the write's own post hands back
     [Q (length bss)] at the number of chunks that fired, and a caller that
     cannot read the selection off that index learns nothing from a
     completed write.  [k] DECIDES the selection here. *)
  Definition efcur (i : Z) (γo : gname) (ws : wordline) (sel0 : list nat)
      (j : nat) : nat -> iProp Σ :=
    fun k => efq i γo ws (match k with
                          | O => sel0
                          | S _ => sel0 ++ [j]
                          end).

  (* THE CURSOR AT SOME SELECTION BELOW A CHUNK INDEX.  A write can FAIL
     -- [f]'s next block may not be allocatable, and no application-tier
     claim can see the bitmap (design/app-file.md SS0, limit 1) -- and then
     the chunk did not land and the cursor comes back where it was.  So a
     caller that has made [k] calls knows only that its selection lies
     below the next chunk index, and THAT is what composes: it is what
     each write takes and what each write returns, one index further on. *)
  Local Lemma forall_lt_weaken (sel : list nat) (b b' : nat) :
    (b <= b')%nat ->
    Forall (fun q => (q < b)%nat) sel ->
    Forall (fun q => (q < b')%nat) sel.
  Proof using .
    intros Hle. rewrite !Forall_forall. intros Hf q Hq.
    specialize (Hf q Hq). lia.
  Qed.

  Definition efany (i : Z) (γo : gname) (ws : wordline) (b : nat) : iProp Σ :=
    (∃ sel : list nat,
       ⌜Forall (fun q => (q < b)%nat) sel⌝ ∗ efq i γo ws sel)%I.

  Lemma efany_of (i : Z) (γo : gname) (ws : wordline) (b : nat)
      (sel : list nat) :
    Forall (fun q => (q < b)%nat) sel ->
    efq i γo ws sel -∗ efany i γo ws b.
  Proof using . iIntros (Hf) "Hq". iExists sel. by iFrame "Hq". Qed.

  Lemma efany_mono (i : Z) (γo : gname) (ws : wordline) (b b' : nat) :
    (b <= b')%nat -> efany i γo ws b -∗ efany i γo ws b'.
  Proof using .
    iIntros (Hle) "Hq". iDestruct "Hq" as (sel) "[%Hf Hq]".
    iExists sel. iFrame "Hq". iPureIntro.
    exact (forall_lt_weaken sel b b' Hle Hf).
  Qed.

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

  (* [ef_relay4] -- the partial arm made vacuous from a PURE single-block
     row over every abstract view -- is GONE (the PROGRAM STREAM, stretch
     9): that row is false as stated, so the lemma could only be applied
     vacuously.  The arm is [FileWritePart.file_awrite_part_adv], built
     from the cursor at [ef_chain]'s one node. *)

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

  (* ---- WAS HYPOTHESIS 4; DISCHARGED (kernel stream, L5).  Restated at
         the row echo's fd 1 ACTUALLY HAS -- [OffHeld], which is what the
         redirect open installs since L4 -- and at the CLIENT-ADVANCED
         chain, which is what a held row's write takes
         ([SpecFilewrite.filewrite_in_held]'s link arm).  The landed
         hypothesis bound [om] free and asked for the PARKED chain, which is
         unpayable at a held row: there is no supplier for it.  It is now
         [UkWriteFile.udepwf_std_write_file_held] on the nose. ---- *)
  Lemma Hdep1 :
    forall (N : uk_names Σ) (m : regfile) (pc : mword 64)
           (l : list fdstate) (rb : bool) (i : Z) (γo : gname)
           (Q : nat -> iProp Σ) (n : Z),
      l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
      bv_signed (trunc32 (m !!! Regidx a0_idx)) = 1%Z ->
      sys_rw_count (m !!! Regidx a2_idx) = n ->
      (∀ (M : gmap Z (bv 8)) (pm : gmap (mword 27) uperm) (sz : Z),
         uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz -∗
         uheap (ukn_t N) (ukn_d N) (ukn_s N) M pm sz ∗
         (* the chain under the write guard at the key's own three values
            -- what the kernel discharges at [fw_au_st_init]. *)
         (∀ P : uptd, ⌜wr_tb pm sz false P⌝ -∗
            awrite_chain_adv (fs_gamma_L fsc_fs) appE i γo M
              (m !!! Regidx a1_idx) P n Q 0%nat (wchunks n))) -∗
      udepwf_std N m pc 16 (write_file_fam Q (ukn_pay N)) l.
  Proof using . exact udepwf_std_write_file_held. Qed.

  (* ---- HYPOTHESIS 5 (NEW; the ledger-slot write leaf) ---------------- *)
  (* [UkRunSys.wp_uk_ecall_write_at] at [K fdv := take NSTD fdv = l], i.e.
     [UkWriteFile.wp_uk_ecall_write_file] with [UserFd.ufd] replaced by
     [UserFd.ustd] and [udepwf_st] by [udepwf_std].  Nothing about the
     file is in it; it is the console leaf's twin at an arbitrary row. *)
  (* ...AND IT IS DISCHARGED (kernel stream, L5): the statement below is
     [UkWriteFile.wp_uk_ecall_write_std] verbatim, which lane OFF-LINK's L5
     named and no lane applied. *)
  Lemma Hwrite1 :
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
         mWP (Loop : expr riscv_lang)) -∗
      mWP (Loop : expr riscv_lang).
  Proof using . exact wp_uk_ecall_write_std. Qed.

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
  (* ...AND IT IS THE CLIENT-ADVANCED NODE, not the parked one: a held
     descriptor's write takes [FsAbsWriteFire.awrite_full_adv], whose
     phase 2 hands the box's arm back ADVANCED, and only the party holding
     the half can prove that.  This entry is that party.

     THE TWO ROWS ABOUT THE WRITER'S OWN BUFFER are new premises and they
     are not a weakening: the landed statement could not be proved at all
     without them, because [SpecCopyin.ubytes_at] is prefix-closed and
     nothing else identifies the bytes that land with the chunk (RELAY 3).
     THE TAINT BRIDGE is the program's own equation, the one lane
     KERNEL-STREAM's item 2 landed on the read side. *)
  Lemma ef_node (i : Z) (γo : gname) (ws : wordline) (sel : list nat)
      (jx : nat) (M : gmap Z (bv 8)) (ua : mword 64) (n : Z) (k : nat) :
    (jx < length (echo_chunks ws))%nat ->
    Forall (fun q => (q < jx)%nat) sel ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat k))
      (echo_chunks ws !!! jx) ->
    Z.of_nat (length (echo_chunks ws !!! jx)) = wchunk_at n k ->
    □ (app_taint -∗ file_taint c) -∗
    app_inv fsc_fs -∗ efq i γo ws sel -∗
    awrite_full_adv (fs_gamma_L fsc_fs) appE i γo M ua n k
      (efq i γo ws (sel ++ [jx])).
  Proof using Heq.
    intros Hjx Hlt Hi1 Hi2 Hi3 Hi4 Hbsk Hlenk.
    iIntros "#Hbr #Hinv Hq". rewrite /efq.
    iApply (file_awrite_node_adv fsc_fs c r i ws sel jx γo M ua n k
              Heq Hjx Hlt Hi1 Hi2 Hi3 Hi4 Hbsk Hlenk with "Hbr Hinv Hq").
  Qed.

  (* ...AND THE WHOLE CALL'S CHAIN, at the ONE node echo's chunk needs.
     [wchunks n] is 1 for every one of echo's calls: a chunk is a word of
     a line or a single blank, and [FW_MAX] is 3072. *)
  Lemma ef_chain (i : Z) (γo : gname) (ws : wordline) (sel : list nat)
      (jx : nat) (M : gmap Z (bv 8)) (pmv : gmap (mword 27) uperm) (sz : Z)
      (P : uptd) (ua : mword 64) (nb : nat) (f : nat -> bv 8) (n : Z) :
    usrc_ok M pmv sz ua nb f ->
    (* the three facts about the caller's table the write guard carries
       ([SpecFilewrite.wr_tb], RULING WR-TB): the chain is handed the
       table under exactly them, and this is where they are spent -- on
       the PARTIAL arm's refutation and nowhere else. *)
    ProcPtOwn.proc_pt_wf P ->
    perm_of (ud_um P) sz = pmv ->
    lazy_free (ud_um P) sz ->
    n = Z.of_nat nb ->
    (0 < nb)%nat -> (Z.of_nat nb <= FW_MAX)%Z ->
    (* THE CHUNK IS AT MOST A LINE.  It used to be a pure "single block"
       row quantified over every abstract view, which nobody can supply
       (a long file at [i] refutes it); the partial arm is built from the
       CURSOR instead ([FileWritePart.file_awrite_part_adv]), which agrees
       the fire's offset to the content's length and needs only this. *)
    (nb <= EchoDisc.line_max)%nat ->
    (jx < length (echo_chunks ws))%nat ->
    Forall (fun q => (q < jx)%nat) sel ->
    (* the writer's own two rows about its buffer, at the ONE node *)
    ubytes_at M ua (echo_chunks ws !!! jx) ->
    length (echo_chunks ws !!! jx) = nb ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (app_taint -∗ file_taint c) -∗
    app_inv fsc_fs -∗ efq i γo ws sel -∗
    awrite_chain_adv (fs_gamma_L fsc_fs) appE i γo M ua P n
      (efcur i γo ws sel jx) 0%nat (wchunks n).
  Proof using Heq.
    intros Hsrc Hwf Hpm Hlf Hn Hnb0 Hnbm Hsb Hjx Hlt Hby Hlenb Hi1 Hi2 Hi3 Hi4.
    (* EVERY ONE OF ECHO'S WRITES IS ONE CHUNK: a chunk is a word of a
       line or a single separator byte, and [FW_MAX] is 3072. *)
    assert (Hone : wchunks n = 1%nat)
      by (apply wchunks_one; lia).
    assert (Hmap : forall j : nat, (j < Z.to_nat n)%nat ->
              uva_rmapped P (uint (add_vec_int ua (Z.of_nat j)))).
    { intros j Hj. exact (proj2 Hsrc P j Hwf Hpm Hlf ltac:(lia)). }
    (* the chunk at node 0 IS the whole count *)
    assert (Hw0 : wchunk_at n 0%nat = n)
      by (rewrite /wchunk_at; cbn; lia).
    assert (Hby0 : ubytes_at M (add_vec_int ua (FW_MAX * Z.of_nat 0))
                     (echo_chunks ws !!! jx)).
    { replace (FW_MAX * Z.of_nat 0)%Z with 0%Z by lia.
      by rewrite avi0. }
    assert (Hlen0 : Z.of_nat (length (echo_chunks ws !!! jx))
                    = wchunk_at n 0%nat)
      by (rewrite Hw0 Hlenb; lia).
    iIntros "#Hbr #Hinv Hq". rewrite Hone.
    cbn [awrite_chain_adv efcur]. iSplit.
    - (* THE CURSOR AT NODE 0: the chain's own entry, at [sel] *)
      iExact "Hq".
    - iSplit.
      + (* THE ONE NODE, and what it leaves IS the chain's cursor at node 1 *)
        iApply (ef_node i γo ws sel jx M ua n 0%nat Hjx Hlt Hi1 Hi2 Hi3 Hi4
                  Hby0 Hlen0 with "Hbr Hinv Hq").
      + (* THE PARTIAL ARM, FROM THE SAME CURSOR: refuted where the cursor
           is fired (the offset is the content's length, a line's worth),
           paid where it is tainted *)
        rewrite /efq.
        iApply (file_awrite_part_adv fsc_fs c r i ws sel (sel ++ [jx]) γo M ua
                  P n 0%nat Heq Hmap
                  ltac:(rewrite Hw0 Hn Nat2Z.id; exact Hnb0)
                  ltac:(rewrite Hw0 Hn Nat2Z.id; exact Hsb)
                  with "Hbr Hq").
  Qed.

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
  (* THE ROW IS HELD, not free.  echo's fd 1 on [f] is the row the
     redirect open installs, and since lane KERNEL-STREAM's L4 that row is
     [OffHeld]: the program answers for its own offset.  A free [om] cannot
     be right here -- the supplier [Hdep1] is the HELD one, and a parked
     row's write has no client-advanced chain to take. *)
  Lemma ef_w_of_deed (N : uk_names Σ) (i : Z) (γo : gname)
      (l : list fdstate) (rb : bool) (ws : wordline) (b : nat)
      (jx : nat) (ua : Z) (nb : nat) (fb : nat -> bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    (0 < nb)%nat -> (Z.of_nat nb <= FW_MAX)%Z -> (Z.of_nat nb < 2 ^ 31)%Z ->
    (jx < length (echo_chunks ws))%nat ->
    (b <= jx)%nat ->
    echo_chunks ws !!! jx = (fun j => fb j) <$> seq 0 nb ->
    (* THE CHUNK IS AT MOST A LINE.  It used to be a pure "single block"
       row quantified over every abstract view, which nobody can supply
       (a long file at [i] refutes it); the partial arm is built from the
       CURSOR instead ([FileWritePart.file_awrite_part_adv]), which agrees
       the fire's offset to the content's length and needs only this. *)
    (nb <= EchoDisc.line_max)%nat ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (app_taint -∗ file_taint c) -∗
    app_inv fsc_fs -∗
    ubytesq (ukn_d N) DfracDiscarded ua nb fb -∗
    kecho_w (SG := uexecSG_xv6) (PS := uprogSG_free) N (mword_of_int ua) nb
      (UserFd.ustd (ukn_fd N) l ∗ efany i γo ws b)
      (UserFd.ustd (ukn_fd N) l ∗ efany i γo ws (S jx)).
  Proof using Heq.
    intros Hl1 Hnb0 Hnbm Hnb31 Hjx Hb Hchunk Hsb Hi1 Hi2 Hi3 Hi4.
    iIntros "#Hbr #Hinv #Hbs" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hq] Hrun Hcont".
    iDestruct "Hq" as (sel) "[%Hlt0 Hq]".
    assert (Hlt : Forall (fun q => (q < jx)%nat) sel).
      by exact (forall_lt_weaken sel b jx Hb Hlt0).
    (* THE SOURCE'S BASE, off the run: a byte the program owns is a byte
       the image maps, and the heap bounds every mapped address. *)
    assert (Hs0 : seq 0 nb !! 0%nat = Some 0%nat)
      by (destruct nb as [| nb']; [ lia | reflexivity ]).
    iDestruct (big_sepL_lookup_acc _ (seq 0 nb) 0%nat 0%nat Hs0 with "Hbs")
      as "[#Hb0 _]".
    iDestruct (urun_ubyte_bnd N h m _ avail DfracDiscarded
                 (ua + Z.of_nat 0) (fb 0%nat) with "Hrun Hb0") as %Hbnd.
    change (2 ^ 38) with 274877906944 in Hbnd.
    assert (Hua : uint (m !!! Regidx a1_idx) = ua)
      by (rewrite Ha1; apply uint_moi; unfold Z64; lia).
    (* THE THREE ARGUMENT REGISTERS, past echo's [c.li a7,16] *)
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat nb) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = 1%Z)
      by (rewrite Ham0; vm_compute; reflexivity).
    pose proof (UEchoOut.echo_count_is nb Hnb31) as Hcz.
    assert (Hcnt : sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx) = Z.of_nat nb)
      by (rewrite Ham2; exact Hcz).
    assert (Hlenb : length (echo_chunks ws !!! jx) = nb)
      by (rewrite Hchunk length_fmap length_seq; reflexivity).
    iApply (wp_kecho_write_chain (SG := uexecSG_xv6) (PS := uprogSG_free) N h m avail
              (write_file_fam (efcur i γo ws sel jx) (ukn_pay N)) l
              DfracDiscarded nb fb with "Hcode Hrun [Hq] Hstd [Hbs]");
      last first.
    { (* ---- THE POST.  Either the chunk landed, and the cursor is at
            [sel ++ [jx]], or the write failed -- [f]'s next block was not
            allocatable, which no claim at this tier can see -- and the
            cursor is back at [sel].  Both are [efany] at [S jx], which is
            exactly why the caller's cursor is stated that way. ---- *)
      iIntros (h' ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hbuf Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_file_fam (efcur i γo ws sel jx) (ukn_pay N)) W
                   ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                      !!! Regidx a0_idx)
                   ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                      !!! Regidx a1_idx)
                   ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                      !!! Regidx a2_idx)
                   (uvis_fd W) (uvis_M W) ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as "(_ & %P & _ & _ & _ & Hp)".
      assert (Hkey : fd_st_of_key
                       ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                          !!! Regidx a0_idx) (uvis_fd W)
                     = FdOpen rb true (FdInode i γo OffHeld))
        by exact (uwr_fd_st_std _ (uvis_fd W) l 1%nat
                    (FdOpen rb true (FdInode i γo OffHeld))
                    Hi0 ltac:(unfold NSTD; lia) Htk Hl1).
      iEval (rewrite Hkey Hcnt;
             cbn [write_file_fam xfam_wr wf_Q];
             rewrite /filewrite_extra /=) in "Hp".
      rewrite /write_arms_at /write_post_ok_at /write_post_fail_at.
      iAssert (∃ k : nat, efcur i γo ws sel jx k)%I with "[Hp]" as "Hc".
      { iDestruct "Hp" as "[[_ Hp] | [_ Hp]]".
        - iDestruct "Hp" as (bss) "(_ & _ & _ & Hch)".
          iExists (length bss). iApply (awrite_chain_at_cursor with "Hch").
        - iDestruct "Hp" as (bss x) "(_ & _ & _ & _ & Hch)".
          iExists (length bss + x)%nat.
          iApply (awrite_chain_at_cursor with "Hch"). }
      iDestruct "Hc" as (k) "Hc".
      iApply ("Hcont" $! h' ret with "[Hstd Hc] Hrun").
      iFrame "Hstd".
      destruct k as [| k'].
      - iApply (efany_of i γo ws (S jx) sel with "Hc").
        exact (forall_lt_weaken sel jx (S jx) ltac:(lia) Hlt).
      - iApply (efany_of i γo ws (S jx) (sel ++ [jx]) with "Hc").
        apply Forall_app. split.
        + exact (forall_lt_weaken sel jx (S jx) ltac:(lia) Hlt).
        + apply Forall_singleton. lia. }
    { (* ---- THE SOURCE, at the register the leaf names it by ---- *)
      rewrite Hua. iExact "Hbs". }
    { (* ---- THE DEPOSIT: the held row's supplier at echo's chain ---- *)
      iApply (udepwf_std_write_file_held N
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2)
                l rb i γo (efcur i γo ws sel jx) (Z.of_nat nb)
                Hl1 Hi0 Hcnt).
      iIntros (M pm sz) "Hheap".
      iDestruct (usrc_ok_ubytesq (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   DfracDiscarded (m !!! Regidx a1_idx) nb fb
                   with "Hheap [Hbs]") as %Hsrc; [ by rewrite Hua | ].
      (* the chunk IS the run the source row names, index for index *)
      assert (Hby : ubytes_at M (m !!! Regidx a1_idx) (echo_chunks ws !!! jx)).
      { intros d cb Hd. rewrite Hchunk in Hd.
        apply list_lookup_fmap_Some in Hd as [d' [Hd' Hcb]].
        apply lookup_seq in Hd' as [Hde Hlt']. subst d'. subst cb.
        exact (proj1 Hsrc d ltac:(lia)). }
      iFrame "Hheap". rewrite Ham1.
      iIntros (P) "%Htb".
      destruct Htb as (Hwf & Hpm & Hlf).
      iApply (ef_chain i γo ws sel jx M pm sz P (m !!! Regidx a1_idx) nb fb
                (Z.of_nat nb) Hsrc Hwf Hpm (Hlf eq_refl) eq_refl Hnb0 Hnbm
                Hsb Hjx Hlt Hby Hlenb
                Hi1 Hi2 Hi3 Hi4 with "Hbr Hinv Hq"). }
  Qed.

  (* ...AND THE SAME AT A .rodata BYTE.  echo's separator and its newline
     are chunks like any other at a file; what differs is the SOURCE half
     -- they are X and not W, filed under the TEXT gname, and no
     [ubytesq] of them exists -- so this is the same member over the
     engine's text leaf ([UkEcho.wp_kecho_write_chain_txt]).  The address
     bound is a premise here, as it is at the console twin: a [utext] byte
     is not enough to place it. *)
  Lemma ef_w_of_deed_txt (N : uk_names Σ) (i : Z) (γo : gname)
      (l : list fdstate) (rb : bool) (ws : wordline) (b : nat)
      (jx : nat) (ua : Z) (bt : bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    (jx < length (echo_chunks ws))%nat ->
    (b <= jx)%nat ->
    echo_chunks ws !!! jx = [bt] ->
    0 <= ua < 2 ^ 38 ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (app_taint -∗ file_taint c) -∗
    app_inv fsc_fs -∗
    utext (ukn_t N) ua bt -∗
    kecho_w (SG := uexecSG_xv6) (PS := uprogSG_free) N (mword_of_int ua) 1%nat
      (UserFd.ustd (ukn_fd N) l ∗ efany i γo ws b)
      (UserFd.ustd (ukn_fd N) l ∗ efany i γo ws (S jx)).
  Proof using Heq.
    intros Hl1 Hjx Hb Hchunk Hrange Hi1 Hi2 Hi3 Hi4.
    change (2 ^ 38) with 274877906944 in Hrange.
    iIntros "#Hbr #Hinv #Hbt" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hq] Hrun Hcont".
    iDestruct "Hq" as (sel) "[%Hlt0 Hq]".
    assert (Hlt : Forall (fun q => (q < jx)%nat) sel)
      by exact (forall_lt_weaken sel b jx Hb Hlt0).
    assert (Hua : uint (m !!! Regidx a1_idx) = ua)
      by (rewrite Ha1; apply uint_moi; unfold Z64; lia).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = 1%Z)
      by (rewrite Ham0; vm_compute; reflexivity).
    pose proof (UEchoOut.echo_count_is 1%nat ltac:(cbn; lia)) as Hcz.
    assert (Hcnt : sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx) = Z.of_nat 1%nat)
      by (rewrite Ham2; exact Hcz).
    assert (Hlenb : length (echo_chunks ws !!! jx) = 1%nat)
      by (rewrite Hchunk; reflexivity).
    iApply (UkEcho.wp_kecho_write_chain_txt (SG := uexecSG_xv6) (PS := uprogSG_free) N h m avail
              (write_file_fam (efcur i γo ws sel jx) (ukn_pay N)) l
              1%nat (fun _ => bt) with "Hcode Hrun [Hq] Hstd [Hbt]");
      last first.
    { (* ---- THE POST, [ef_w_of_deed]'s exactly ---- *)
      iIntros (h' ret W cw' cs')
        "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hpost Hrun".
      iDestruct (spost_at_write_elim_at uslot
                   (write_file_fam (efcur i γo ws sel jx) (ukn_pay N)) W
                   ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                      !!! Regidx a0_idx)
                   ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                      !!! Regidx a1_idx)
                   ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                      !!! Regidx a2_idx)
                   (uvis_fd W) (uvis_M W) ret (uvis_M W) (uvis_fd W) cw' cs'
                   Hka0 Hka1 Hka2 eq_refl eq_refl with "Hpost")
        as "(_ & %P & _ & _ & _ & Hp)".
      assert (Hkey : fd_st_of_key
                       ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                          !!! Regidx a0_idx) (uvis_fd W)
                     = FdOpen rb true (FdInode i γo OffHeld))
        by exact (uwr_fd_st_std _ (uvis_fd W) l 1%nat
                    (FdOpen rb true (FdInode i γo OffHeld))
                    Hi0 ltac:(unfold NSTD; lia) Htk Hl1).
      iEval (rewrite Hkey Hcnt;
             cbn [write_file_fam xfam_wr wf_Q];
             rewrite /filewrite_extra /=) in "Hp".
      rewrite /write_arms_at /write_post_ok_at /write_post_fail_at.
      iAssert (∃ k : nat, efcur i γo ws sel jx k)%I with "[Hp]" as "Hc".
      { iDestruct "Hp" as "[[_ Hp] | [_ Hp]]".
        - iDestruct "Hp" as (bss) "(_ & _ & _ & Hch)".
          iExists (length bss). iApply (awrite_chain_at_cursor with "Hch").
        - iDestruct "Hp" as (bss x) "(_ & _ & _ & _ & Hch)".
          iExists (length bss + x)%nat.
          iApply (awrite_chain_at_cursor with "Hch"). }
      iDestruct "Hc" as (k) "Hc".
      iApply ("Hcont" $! h' ret with "[Hstd Hc] Hrun").
      iFrame "Hstd".
      destruct k as [| k'].
      - iApply (efany_of i γo ws (S jx) sel with "Hc").
        exact (forall_lt_weaken sel jx (S jx) ltac:(lia) Hlt).
      - iApply (efany_of i γo ws (S jx) (sel ++ [jx]) with "Hc").
        apply Forall_app. split.
        + exact (forall_lt_weaken sel jx (S jx) ltac:(lia) Hlt).
        + apply Forall_singleton. lia. }
    { (* ---- THE SOURCE: one .rodata byte ---- *)
      cbn [seq]. rewrite big_sepL_singleton Hua Z.add_0_r. iExact "Hbt". }
    { (* ---- THE DEPOSIT ---- *)
      iApply (udepwf_std_write_file_held N
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int EchoSyms.write : mword 64) 2)
                l rb i γo (efcur i γo ws sel jx) (Z.of_nat 1%nat)
                Hl1 Hi0 Hcnt).
      iIntros (M pm sz) "Hheap".
      iDestruct (usrc_ok_utext (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   (m !!! Regidx a1_idx) 1%nat (fun _ => bt)
                   with "Hheap [Hbt]") as %Hsrc;
        [ cbn [seq]; rewrite big_sepL_singleton Hua Z.add_0_r; iExact "Hbt" | ].
      assert (Hby : ubytes_at M (m !!! Regidx a1_idx) (echo_chunks ws !!! jx)).
      { intros d cb Hd. rewrite Hchunk in Hd.
        destruct d as [| d']; cbn in Hd; [| discriminate ].
        injection Hd as <-.
        exact (proj1 Hsrc 0%nat ltac:(lia)). }
      iFrame "Hheap". rewrite Ham1.
      iIntros (P) "%Htb".
      destruct Htb as (Hwf & Hpm & Hlf).
      iApply (ef_chain i γo ws sel jx M pm sz P (m !!! Regidx a1_idx) 1%nat
                (fun _ => bt) (Z.of_nat 1%nat) Hsrc Hwf Hpm (Hlf eq_refl)
                eq_refl ltac:(lia) ltac:(cbn; unfold FW_MAX; lia)
                ltac:(unfold EchoDisc.line_max; lia) Hjx Hlt Hby Hlenb
                Hi1 Hi2 Hi3 Hi4 with "Hbr Hinv Hq"). }
  Qed.

  (* =================================================================== *)
  (*  S5b  THE DICTIONARY, AT THE LINE                                    *)
  (*                                                                     *)
  (*  echo's payment recursion walks ARGUMENTS (index [i], 1-based over   *)
  (*  the line's words); the deed's cursor walks CHUNKS.  [FileState]'s   *)
  (*  four lemmas are the dictionary on the tail; these read them at [ws] *)
  (*  and at the argument index the recursion actually carries.           *)
  (* =================================================================== *)
  Local Lemma ef_chunks_length (ws : wordline) :
    (2 <= length ws)%nat ->
    length (echo_chunks ws) = (2 * (length ws - 1))%nat.
  Proof using .
    intros H2. rewrite /echo_chunks.
    rewrite (echo_args_chunks_length (drop 1 ws)
               ltac:(intros Hnil;
                     assert (Hl : length (drop 1 ws) = 0%nat)
                       by (rewrite Hnil; reflexivity);
                     rewrite length_drop in Hl; lia)).
    rewrite length_drop. reflexivity.
  Qed.

  Local Lemma ef_chunk_word (ws : wordline) (i : nat) (w : list (bv 8)) :
    (1 <= i)%nat -> ws !! i = Some w ->
    echo_chunks ws !!! (2 * (i - 1))%nat = w.
  Proof using .
    intros Hi Hw. rewrite /echo_chunks.
    assert (Hd : drop 1 ws !! (i - 1)%nat = Some w)
      by (rewrite ws_drop; [exact Hw | exact Hi]).
    assert (Hlt : (i - 1 < length (drop 1 ws))%nat)
      by (apply lookup_lt_Some in Hd; lia).
    apply list_lookup_total_correct.
    rewrite (echo_args_chunks_word (drop 1 ws) (i - 1)%nat Hlt). exact Hd.
  Qed.

  Local Lemma ef_chunk_sep (ws : wordline) (i : nat) :
    (1 <= i)%nat -> (S i < length ws)%nat ->
    echo_chunks ws !!! (2 * (i - 1) + 1)%nat = [wl_sp].
  Proof using .
    intros Hi Hlt. rewrite /echo_chunks. apply list_lookup_total_correct.
    apply echo_args_chunks_sep. rewrite length_drop. lia.
  Qed.

  Local Lemma ef_chunk_nl (ws : wordline) (i : nat) :
    (1 <= i)%nat -> S i = length ws ->
    echo_chunks ws !!! (2 * (i - 1) + 1)%nat = [wl_nl].
  Proof using .
    intros Hi Hlast. rewrite /echo_chunks. apply list_lookup_total_correct.
    apply echo_args_chunks_nl. rewrite length_drop. lia.
  Qed.

  (* ...AND THE WORD'S BYTES ARE ARGV'S.  [UEchoOut.out_argv_at] ties the
     argument to the ALTERNATIVE's bytes at the word's offset, because the
     console cursor is about the alternative; the deed's content is about
     [ws] itself, so the tie has to be pushed one step
     ([LineWords.wl_line_word]). *)
  Local Lemma ef_word_bytes (ws : wordline) (i : nat) (w : list (bv 8))
      (g : uarg) :
    (1 <= i)%nat -> ws !! i = Some w ->
    ua_len g = length (ws !!! i) ->
    (forall j : nat, (j < ua_len g)%nat ->
       line_alts_of ws !!! 0%nat !! (out_cur ws i + j)%nat
       = Some (ua_bytes g j)) ->
    w = (fun j => ua_bytes g j) <$> seq 0 (ua_len g).
  Proof using .
    intros Hi Hw Hlen Hby.
    assert (Hwt : ws !!! i = w) by (apply list_lookup_total_correct; exact Hw).
    rewrite Hwt in Hlen.
    assert (Hd : drop 1 ws !! (i - 1)%nat = Some w)
      by (rewrite ws_drop; [exact Hw | exact Hi]).
    apply list_eq. intros j.
    destruct (decide (j < length w)%nat) as [Hj | Hj]; last first.
    { rewrite lookup_ge_None_2; [| lia].
      rewrite lookup_ge_None_2; [reflexivity |].
      rewrite length_fmap length_seq. lia. }
    rewrite list_lookup_fmap.
    assert (Hsq : seq 0 (ua_len g) !! j = Some j).
    { rewrite (lookup_seq_lt 0%nat (ua_len g) j ltac:(lia)). reflexivity. }
    rewrite Hsq. cbn [fmap option_fmap].
    (* the alternative's byte at the word's offset IS the word's *)
    pose proof (Hby j ltac:(lia)) as Hbj.
    rewrite (alt0_out ws (out_cur ws i + j)%nat
               (out_cur_lt ws i w j Hi Hw ltac:(lia))) in Hbj.
    apply list_lookup_total_correct in Hbj.
    assert (Hwj : wl_line (drop 1 ws) !!! (out_cur ws i + j)%nat = w !!! j).
    { rewrite /out_cur.
      exact (wl_line_word (drop 1 ws) (i - 1)%nat w j Hd ltac:(lia)). }
    rewrite Hbj in Hwj.
    rewrite (list_lookup_lookup_total_lt w j ltac:(lia)).
    by rewrite <- Hwj.
  Qed.

  (* =================================================================== *)
  (*  S6  THE PAYMENT -- [UEchoOut.kecho_pay_of_link]'s twin              *)
  (*                                                                     *)
  (*  The recursion is the SAME one ([UkEcho.kecho_pay] on the argument    *)
  (*  count); what changes is that the cursor is the DEED and the chunk    *)
  (*  index advances with it, so argument [q] is chunk [2*(q-1)] and the    *)
  (*  separator after it chunk [2*(q-1)+1] ([FileState.echo_args_chunks]). *)
  (* =================================================================== *)
  (* THE CHAIN, BY INDUCTION OVER THE ARGUMENTS ([UEchoOut]'s
     [kecho_pay_of_link_from_at] one file over).  echo writes [argv[ix]],
     then a separator or the closing newline depending on whether another
     argument follows -- and at a FILE both are chunks, so the cursor
     advances by ONE chunk index at each, not by a byte count.  Argument
     [ix] is chunk [2 * (ix - 1)] and the byte after it chunk
     [2 * (ix - 1) + 1] ([FileState]'s dictionary, read at S5b). *)
  Lemma ef_pay_from (N : uk_names Σ) (i : Z) (γo : gname)
      (l : list fdstate) (rb : bool) (ws : wordline) (av : Z)
      (args : list uarg) :
    EchoDisc.line_ok ws ->
    UEchoOut.echo_out_argv ws args ->
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    forall k ix : nat,
      (1 <= ix)%nat -> (ix + k)%nat = (length ws - 1)%nat ->
      □ (ef_exit i γo ws -∗ ukn_pay N (-1)) -∗
      □ (app_taint -∗ file_taint c) -∗
      app_inv fsc_fs -∗
      echo_rodata (ukn_t N) -∗
      uargv (ukn_d N) av args -∗
      Wq -∗
      kecho_pay (SG := uexecSG_xv6) (PS := uprogSG_free) N args k ix
        (UserFd.ustd (ukn_fd N) l ∗ efany i γo ws (2 * (ix - 1))%nat)
        (ukn_pay N (-1)).
  Proof using Heq.
    intros Hline Hargv Hl1 Hi1 Hi2 Hi3 Hi4.
    pose proof Hargv as (Hlen & Hargs).
    pose proof (EchoDisc.line_ok_wf ws Hline) as Hwf.
    pose proof (EchoDisc.line_ok_len ws Hline) as Hlmax.
    pose proof (EchoDisc.line_ok_ge2 ws Hline) as Hws2.
    (* the chunk table's length, once *)
    assert (Hclen : length (echo_chunks ws) = (2 * (length ws - 1))%nat)
      by exact (ef_chunks_length ws Hws2).
    induction k as [| k IH]; intros ix Hix Hik;
      iIntros "#Hq #Hbr #Hinv #Hro #Hargv HWq"; cbn [kecho_pay];
      iIntros (g) "%Hg";
      pose proof (Hargs ix g Hix Hg) as [Hgl Hgb];
      (assert (Hiw : (ix < length ws)%nat)
         by (apply lookup_lt_Some in Hg; lia));
      (assert (Hwsx : is_Some (ws !! ix))
         by (apply lookup_lt_is_Some_2; exact Hiw));
      (destruct Hwsx as [w Hw]);
      (assert (Hwt : ws !!! ix = w)
         by (apply list_lookup_total_correct; exact Hw));
      (assert (Hwpos : (0 < length w)%nat)
         by exact (wl_word_pos w (Forall_lookup_1 _ _ _ _ Hwf Hw)));
      (assert (Hwshort : (length w < EchoDisc.line_max)%nat)
         by (pose proof (wl_off_lt_line ws ix w (length w) Hw ltac:(lia));
             unfold EchoDisc.line_max in *; lia));
      (assert (Hbytes : w = (fun j => ua_bytes g j) <$> seq 0 (ua_len g))
         by (apply (ef_word_bytes ws ix w g Hix Hw);
             [ exact Hgl | exact Hgb ]));
      (assert (Hcw : echo_chunks ws !!! (2 * (ix - 1))%nat = w)
         by exact (ef_chunk_word ws ix w Hix Hw));
      (assert (Hglw : ua_len g = length w) by (rewrite Hgl Hwt; reflexivity));
      (assert (Hjw : (2 * (ix - 1) < length (echo_chunks ws))%nat)
         by (rewrite Hclen; lia));
      (assert (Hjb : (2 * (ix - 1) + 1 < length (echo_chunks ws))%nat)
         by (rewrite Hclen; lia));
      (assert (Hgshort : (ua_len g <= EchoDisc.line_max)%nat)
         by (rewrite Hglw; lia));
      iDestruct (uargv_acc (ukn_d N) av args ix g Hg with "Hargv")
        as "[[_ (_ & _ & #Hbs & _)] _]".
    - (* THE LAST ARGUMENT: its bytes, then the newline, which ends the
         output and pays the exit.  [Wq] never enters a member's [Ci]: it
         is this proof's own resource and it is spent, once, in the wand
         that turns the last member's answer into the exit payload. *)
      assert (Hlast : S ix = length ws) by lia.
      iExists (UserFd.ustd (ukn_fd N) l
               ∗ efany i γo ws (S (2 * (ix - 1)))%nat)%I.
      iSplitR "HWq".
      { iApply (ef_w_of_deed N i γo l rb ws (2 * (ix - 1))%nat
                  (2 * (ix - 1))%nat (ua_ptr g) (ua_len g) (ua_bytes g)
                  Hl1 ltac:(lia)
                  ltac:(unfold FW_MAX, EchoDisc.line_max in *; lia)
                  ltac:(unfold EchoDisc.line_max in *;
                        change (2 ^ 31)%Z with 2147483648%Z; lia)
                  Hjw ltac:(lia)
                  ltac:(rewrite Hcw Hbytes; reflexivity)
                  Hgshort Hi1 Hi2 Hi3 Hi4 with "Hbr Hinv Hbs"). }
      iApply (kecho_w_mono (SG := uexecSG_xv6) (PS := uprogSG_free) N (mword_of_int UkEcho.echo_nl_ptr) 1%nat
                (UserFd.ustd (ukn_fd N) l
                 ∗ efany i γo ws (S (2 * (ix - 1)))%nat)
                (UserFd.ustd (ukn_fd N) l
                 ∗ efany i γo ws (S (2 * (ix - 1) + 1))%nat)
                (ukn_pay N (-1)) with "[HWq] []").
      { iIntros "[_ Hc]". iApply "Hq". rewrite /ef_exit. iFrame "HWq".
        iDestruct "Hc" as (sel) "[_ Hc]". by iExists sel. }
      iApply (ef_w_of_deed_txt N i γo l rb ws (S (2 * (ix - 1)))%nat
                (2 * (ix - 1) + 1)%nat UkEcho.echo_nl_ptr wl_nl
                Hl1 Hjb ltac:(lia)
                ltac:(exact (ef_chunk_nl ws ix Hix Hlast))
                ltac:(unfold UkEcho.echo_nl_ptr;
                      change (2 ^ 38)%Z with 274877906944%Z; lia)
                Hi1 Hi2 Hi3 Hi4 with "Hbr Hinv [Hro]").
      iApply (UEchoOut.echo_rodata_byte (ukn_t N) UkEcho.echo_nl_ptr wl_nl
                UEchoOut.echo_nl_ro with "Hro").
    - (* ...AND ANOTHER FOLLOWS: its bytes, then the separator, and the
         cursor lands one chunk index further on. *)
      assert (Hnext : (S ix < length ws)%nat) by lia.
      iExists (UserFd.ustd (ukn_fd N) l
               ∗ efany i γo ws (S (2 * (ix - 1)))%nat)%I.
      iExists (UserFd.ustd (ukn_fd N) l
               ∗ efany i γo ws (2 * (S ix - 1))%nat)%I.
      iSplitR "HWq".
      { iApply (ef_w_of_deed N i γo l rb ws (2 * (ix - 1))%nat
                  (2 * (ix - 1))%nat (ua_ptr g) (ua_len g) (ua_bytes g)
                  Hl1 ltac:(lia)
                  ltac:(unfold FW_MAX, EchoDisc.line_max in *; lia)
                  ltac:(unfold EchoDisc.line_max in *;
                        change (2 ^ 31)%Z with 2147483648%Z; lia)
                  Hjw ltac:(lia)
                  ltac:(rewrite Hcw Hbytes; reflexivity)
                  Hgshort Hi1 Hi2 Hi3 Hi4 with "Hbr Hinv Hbs"). }
      iSplitR "HWq".
      { iApply (kecho_w_mono (SG := uexecSG_xv6) (PS := uprogSG_free) N (mword_of_int UkEcho.echo_sep_ptr) 1%nat
                  (UserFd.ustd (ukn_fd N) l
                   ∗ efany i γo ws (S (2 * (ix - 1)))%nat)
                  (UserFd.ustd (ukn_fd N) l
                   ∗ efany i γo ws (S (2 * (ix - 1) + 1))%nat)
                  (UserFd.ustd (ukn_fd N) l
                   ∗ efany i γo ws (2 * (S ix - 1))%nat) with "[] []").
        { iIntros "[$ Hc]".
          iApply (efany_mono i γo ws (S (2 * (ix - 1) + 1))%nat
                    (2 * (S ix - 1))%nat ltac:(lia) with "Hc"). }
        iApply (ef_w_of_deed_txt N i γo l rb ws (S (2 * (ix - 1)))%nat
                  (2 * (ix - 1) + 1)%nat UkEcho.echo_sep_ptr wl_sp
                  Hl1 Hjb ltac:(lia)
                  ltac:(exact (ef_chunk_sep ws ix Hix Hnext))
                  ltac:(unfold UkEcho.echo_sep_ptr;
                        change (2 ^ 38)%Z with 274877906944%Z; lia)
                  Hi1 Hi2 Hi3 Hi4 with "Hbr Hinv [Hro]").
        iApply (UEchoOut.echo_rodata_byte (ukn_t N) UkEcho.echo_sep_ptr wl_sp
                  UEchoOut.echo_sep_ro with "Hro"). }
      iApply (IH (S ix) ltac:(lia) ltac:(lia)
                with "Hq Hbr Hinv Hro Hargv HWq").
  Qed.

  Lemma ef_pay_all (N : uk_names Σ) (i : Z) (γo : gname)
      (l : list fdstate) (rb : bool) (ws : wordline) (av : Z)
      (args : list uarg) :
    EchoDisc.line_ok ws ->
    UEchoOut.echo_out_argv ws args ->
    l !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (ef_exit i γo ws -∗ ukn_pay N (-1)) -∗
    □ (app_taint -∗ file_taint c) -∗
    Wq -∗
    app_inv fsc_fs -∗
    echo_rodata (ukn_t N) -∗
    uargv (ukn_d N) av args -∗
    kecho_pay_all (SG := uexecSG_xv6) (PS := uprogSG_free) N args
      (UserFd.ustd (ukn_fd N) l ∗ efany i γo ws 0%nat)
      (ukn_pay N (-1)).
  Proof using Heq.
    intros Hline Hargv Hl1 Hi1 Hi2 Hi3 Hi4.
    pose proof Hargv as (Hlen & _).
    pose proof (EchoDisc.line_ok_ge2 ws Hline) as Hws2.
    iIntros "#Hq #Hbr HWq #Hinv #Hro #Hargv".
    rewrite /kecho_pay_all. iSplit.
    - (* [argc <= 1]: echo prints nothing, and the entry cursor pays the
         exit unchanged. *)
      iIntros "%Hsmall [_ Hc]". iApply "Hq". rewrite /ef_exit.
      iFrame "HWq". iDestruct "Hc" as (sel) "[_ Hc]". by iExists sel.
    - iIntros "_".
      (* the recursion starts at argument 1, whose word is chunk 0 *)
      pose proof (ef_pay_from N i γo l rb ws av args Hline Hargv Hl1
                    Hi1 Hi2 Hi3 Hi4 (length args - 2)%nat 1%nat
                    ltac:(lia) ltac:(lia)) as Hfrom.
      assert (Hz : (2 * (1 - 1))%nat = 0%nat) by lia.
      rewrite Hz in Hfrom.
      iApply (Hfrom with "Hq Hbr Hinv Hro Hargv HWq").
  Qed.

  (* =================================================================== *)
  (*  S7  THE PAID ENTRY -- [UEchoOut.echo_uexec_slot_at]'s mould         *)
  (*                                                                     *)
  (*  Every premise about the KEY is echo's own and is copied verbatim     *)
  (*  from the console twin; the two that are new are the LEDGER ROW       *)
  (*  (fd 1 is an inode open for writing, not the console device) and      *)
  (*  the LEND, which is the deed and the fragment instead of the era's    *)
  (*  cursor.                                                             *)
  (* =================================================================== *)
  Lemma efile_uexec_slot_at (W : uvis) (i : Z) (γo : gname)
      (rb : bool) (ws : wordline) (Q : Z -> iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    EchoDisc.line_ok ws ->
    UEchoOut.echo_out_argv ws
      (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))) ->
    (* THE LEDGER ROW: fd 1 is `f`, held for writing (design SS3, the
       child's REDIR arm) -- where the console twin asks for
       [FdOpen rb true (FdDevice CONSOLE)]. *)
    take NSTD (uvis_fd W) !! 1%nat
      = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
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
    □ (app_taint -∗ file_taint c) -∗
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
  Proof using Heq ghost_varG0 ghost_varG1 ufdG0.
    intros HQc Hline Hargv1 Hl1 Hpc Hsub Hsub2 Hx Hroom Hal8 Hstk Hargs
           Havd Havs Hfdlen Hstop Hlzf Hi1 Hi2 Hi3 Hi4.
    iIntros "#Hq #Hbr #Hinv #Hnpw #Hdep Hpay HWq Hc".
    assert (Hsp0 : 0 <= uint (uvis_sp W)) by lia.
    assert (Hargc0 : 0 <= uvis_argc W)
      by exact (proj1 (uka_argc _ _ _ _ _ _ Hargs)).
    iApply (uslot_of_urun_ro (SG := uexecSG_xv6) (PS := uprogSG_free) W 12 Q
              Hal8
              ltac:(unfold uvis_sp in Hroom; lia) Hstk Hfdlen Hstop Hlzf
              with "Hdep Hnpw Hpay").
    iIntros (N h) "%Hpayeq %Hsz Hszf #Ht Hstd _ _ _ #HA Hrun".
    pose proof (ukn_const_of_eq N _ Hpayeq HQc) as Htc.
    rewrite Hpc.
    iApply (wp_kecho_start (SG := uexecSG_xv6) (PS := uprogSG_free) N h (tf_resume_gpr0 (uvis_tf W))
              (uvis_av W)
              (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W))) 0
              (UserFd.ustd (ukn_fd N) (take NSTD (uvis_fd W))
               ∗ efany i γo ws 0%nat)%I
              ltac:(rewrite echo_args_length;
                    rewrite (Z2Nat.id (uvis_argc W) Hargc0);
                    unfold uvis_argc; symmetry; apply moi_of_uint)
              ltac:(unfold uvis_av; symmetry; apply moi_of_uint)
              with "[HWq] [] [] [Hstd Hc] Hrun").
    { iApply (ef_pay_all N i γo (take NSTD (uvis_fd W)) rb ws (uvis_av W)
                (echo_args (uvis_M W) (uvis_av W) (Z.to_nat (uvis_argc W)))
                Hline Hargv1 Hl1 Hi1 Hi2 Hi3 Hi4
                with "[] Hbr HWq Hinv [] []").
      { rewrite Hpayeq. iExact "Hq". }
      - iApply (echo_rodata_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                  Hsub2 Hx with "Ht").
      - iApply (echo_uargv_of_area (ukn_d N) (uvis_M W) (uvis_perm W)
                  (uvis_sz W) (uvis_av W) (uint (uvis_sp W)) (uvis_argc W)
                  Hsp0 Hargs Havd Havs with "HA"). }
    { iApply (echo_code_of_text (ukn_t N) (uvis_M W) (uvis_perm W)
                Hsub Hx with "Ht"). }
    { iApply (echo_uargv_of_area (ukn_d N) (uvis_M W) (uvis_perm W)
                (uvis_sz W) (uvis_av W) (uint (uvis_sp W)) (uvis_argc W)
                Hsp0 Hargs Havd Havs with "HA"). }
    { iFrame "Hstd". iApply (efany_of i γo ws 0%nat [] ltac:(constructor)
                               with "Hc"). }
  Qed.

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
     lane SH-ROUND's redirect child applies after its [exec /echo].

     THE PAYLOAD IS A PARAMETER (the PROGRAM STREAM's era step).  It used
     to conclude at [fun _ => ef_exit i γo ws] with a vestigial
     [□ (ef_exit -∗ ef_exit)] premise, and that was unusable: a generation's
     payload is what the FORK chose ([ChildTok.my_pay_agree] makes
     [ExecEntry.image_entry]'s [Q] slot rigid, and sh's fork chose
     [UkShFork.ushf_wq Wcf I]), so no conversion moves the entry from one
     [Q] to another after the fact.  [efile_uexec_slot_at] below already
     takes [Q] with exactly this wand; this is that lemma packaged at a
     parameter instead of at the identity. *)
  Lemma efile_image_entry (ws : wordline) (M : gmap Z (bv 8))
      (s0 t : Z) (g : nat -> bv 8) (sts : list fdstate)
      (cw : Z) (cs : gset gname) (pidv : mword 32)
      (i : Z) (γo : gname) (rb : bool)
      (Q : Z -> iProp Σ) :
    (forall x y : Z, Q x = Q y) ->
    EchoDisc.line_ok ws ->
    UShEcho.echo_node_img ws M s0 t g ->
    UkShEcho.echo_argv_bytes ws g ->
    length sts = NOFILE ->
    (* THE CHILD'S fd 1 IS `f`: a pure row about the exec'ing process's
       own table, which is the child's after [close(1); open(f, 0x601)] --
       and the row is HELD since lane KERNEL-STREAM's L4. *)
    take NSTD sts !! 1%nat = Some (FdOpen rb true (FdInode i γo OffHeld)) ->
    i <> INIT_INO -> i <> SH_INO -> i <> ECHO_INO -> i <> CAT_INO ->
    □ (ef_exit i γo ws -∗ Q (-1)) -∗
    □ (app_taint -∗ file_taint c) -∗
    app_inv fsc_fs -∗
    UkRun.urun_nopipe sts -∗
    udep (SG := uexecSG_xv6) (PS := uprogSG_free) -∗
    image_entry ElfUser.echo_elf M (mword_of_int (t + 8) : mword 64) sts
      cw cs pidv Q (ef_pay i γo ws) uslot.
  Proof using Heq ghost_varG0 ghost_varG1 ufdG0.
    intros HQc Hline Himg Hbytes Hfdl Hl1 Hi1 Hi2 Hi3 Hi4.
    iIntros "#Hq #Hbr #Hinv #Hnpw #Hdep".
    iApply image_entry_of_at. iIntros "!>" (na alen afun) "%Hargs".
    destruct (UShEcho.echo_args_det_holds ws Hline M s0 t g na alen afun
                Himg Hbytes Hargs) as (Hna & Halen & Hafun).
    rewrite /image_entry_at. iIntros "!>" (W') "%Hokk _ %Hlzf _ _ Hmp HPay".
    destruct (UShEcho.echo_kexec_pages na alen afun sts W' Hokk)
      as (Hpc & Hsub & Hx & Hwr & Hrp).
    destruct (UShEcho.echo_kexec_entry_rows na alen afun sts W' Hokk
                (UShEcho.echo_room_of_det ws na alen Hline Hna Halen) Hfdl
                Hwr Hrp)
      as (Hroom96 & Hal8 & Hstkrow & Hargsrow & Havd & Havs & Hfdlen & Hstop).
    pose proof (echo_out_argv_of_image ws na alen afun sts W'
                  Hline Hokk Hna Halen Hafun) as Hargv.
    (* the child's table IS the one the channel carried *)
    assert (Hfd : uvis_fd W' = sts)
      by exact (kexec_image_ok_fd _ _ _ _ _ _ Hokk).
    assert (Hsub2 : echo_data_sub (uvis_M W')).
    { unfold kexec_image_ok in Hokk. cbv zeta in Hokk.
      destruct Hokk as (_ & _ & _ & _ & _ & Himg' & _).
      exact (efile_data_of_elf_image _ Himg'). }
    iAssert (UkRun.urun_nopipe (uvis_fd W')) as "#Hnpw'";
      [ rewrite Hfd; iExact "Hnpw" | ].
    iDestruct "HPay" as "[HWq Hc]".
    iApply (efile_uexec_slot_at W' i γo rb ws Q HQc Hline Hargv
              ltac:(rewrite Hfd; exact Hl1) Hpc Hsub Hsub2 Hx
              Hroom96 Hal8 Hstkrow Hargsrow Havd Havs Hfdlen Hstop Hlzf
              Hi1 Hi2 Hi3 Hi4
              with "Hq Hbr Hinv Hnpw' Hdep Hmp HWq Hc").
  Qed.

End UEchoFile.
