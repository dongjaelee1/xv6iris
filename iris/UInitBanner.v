(* ===================================================================== *)
(*  UInitBanner.v -- WHAT PAYS FOR /init's BANNER                         *)
(*  (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane IO-LEAF, M1(e).)    *)
(*                                                                       *)
(*  <init> prints "init: starting sh\n" at the head of every round of its *)
(*  restart loop, and round 0 is the one round it enters holding the      *)
(*  era's own credential ([EchoOut.eturn], carried by the boot).  What    *)
(*  the walk spends is [UkInit.kinit_banner_pay] -- "give me the          *)
(*  descriptor table and I give you a per-byte family for the eighteen    *)
(*  bytes" -- and THIS FILE IS WHERE THE ONE BECOMES THE OTHER.           *)
(*                                                                       *)
(*  WHY IT IS A FILE OF ITS OWN, and why the walk cannot do it itself:    *)
(*  the conversion needs row 16's CONCRETE reading -- the console chain   *)
(*  it deposits ([UkWriteLeaf.uwrite_chain_sup]) and the arms it reads    *)
(*  back ([uwrite_no_short]) -- and every file of init's walk sits BELOW  *)
(*  the file system ([UkWriteLeaf]'s header: "UkRunSys sits below the     *)
(*  file system and cannot name a row").  So the walk takes the payment   *)
(*  abstractly and the payment is proved here, exactly the way sh's read  *)
(*  leaf reaches [UkSh] from [UShLine].                                   *)
(*                                                                       *)
(*  ONE ARM (lane IO-LEAF, M1(f)).  There used to be two: /init's ledger  *)
(*  head pinned SLOT 0 only, because a failing [dup] was not refutable,   *)
(*  so "fd 1 is the console" was not a theorem of init's code and the     *)
(*  payment had to answer for every row fd 1 could be at -- read-only,    *)
(*  inode, other-device, closed, and absent -- each of which spent the    *)
(*  FREE WRITE LAW ([UkRun.udepw_law] 16), which is why this lemma took   *)
(*  [(⊢ udepw_law 16)] as a premise.  Lane DUP-ROW gave the dup row its   *)
(*  reason and M1(f) carried the NAMED ledger through both dups, so the   *)
(*  payment is now asked for at [UInitFd.ufd_l3] of the console           *)
(*  descriptor, whose row 1 IS the console ([UInitFd.ufd_l3_row1]).  The  *)
(*  five other rows are gone and so is the premise: the era's write link  *)
(*  pays each byte and the cursor moves, on the one row there is.  (The   *)
(*  head's CLOSED and TAINT arms never ask for the payment at all --      *)
(*  [UkInitMain.wp_kinit_banner] prints through the flagged deposit       *)
(*  there, as it does on every round after the first.)                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes ObsTrace.
Require Import RegFile.
(* the ghost binder list, each module IMPORTED and not merely required --
   see [UkWriteLeaf.v]'s header *)
Require Import Xv6Cameras.
Require Import Xv6G.
Require Import FdSlots.
Require Import IrefSlots.
Require Import ProcAvail.
Require Import FileInvDefs.
Require Import UserFd.
Require Import UserHeap.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UserCwd UserChildren.
Require Import UmodeArith UmodeAbi.
Require Import ProcGeom.
Require Import VcGen.
Require Import PieceFam.
Require Import FsTree.
Require Import ChildTok.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunSys.
Require Import UexecExecInst.      (* THE INSTANCE: [uexecSG_xv6] *)
Require Import SpecArgfd.
Require Import SpecFilewrite.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import FsCfg.
Require Import FsAbsDefs.
Require Import WpUart.
Require Import UkWriteLeaf.        (* the supply and the post, at row 16 *)
Require Import UCodeInit.
Require Import UInitFd.            (* [ufd_l3] / [ufd_l3_row1] *)
Require Import UkInit UkInitLit UkInitMain.
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import EchoLinks.
Require Import UShOut.              (* [sh_prompt_pay_of_ushpr]: what the
                                       shell will SPEND the credential on *)
Require Import TsoCtx.
Require User.InitSyms.
Local Open Scope Z_scope.
Import Defs.

Section UInitBanner.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation LIT_START := 0x978.

  (* =================================================================== *)
  (*  S1  THE PURE HALF: init's rodata banner IS the era's                *)
  (* =================================================================== *)
  Lemma init_banner_bytes_bool :
    forallb (fun j : nat =>
               match u_banner !! j with
               | Some x => Z.eqb (bv_unsigned x)
                                 (bv_unsigned (init_lit LIT_START j))
               | None => false
               end) (seq 0 18) = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma init_banner_bytes (j : nat) :
    (j < 18)%nat -> u_banner !! j = Some (init_lit LIT_START j).
  Proof.
    intros Hj. pose proof init_banner_bytes_bool as H.
    rewrite forallb_forall in H.
    specialize (H j ltac:(apply in_seq; lia)).
    destruct (u_banner !! j) as [x |] eqn:Hx; [| discriminate ].
    apply Z.eqb_eq in H. f_equal. by apply bv_eq.
  Qed.

  (* ...AND WHAT THE WRITE LINK ASKS FOR AT ROUND 0.  No [vm_compute] on
     the stream: [EchoOut.proc_upto_round_banner_open] is the arbitrary-
     round lemma (lane PROLOGUE-ALTS-2) and round 0 is it at [pre := []],
     [j := 0], where every offset it adds is zero. *)
  Lemma proc_upto0_banner (i : nat) :
    (i < 18)%nat -> proc_upto [] [] 1%nat !! i = Some (init_lit LIT_START i).
  Proof.
    intros Hi.
    pose proof (proc_upto_round_banner_open [] [] 0%nat 0%nat i
                  (init_lit LIT_START i)
                  ltac:(vm_compute; reflexivity)
                  (or_introl eq_refl)
                  ltac:(vm_compute; reflexivity)
                  (init_banner_bytes i Hi)) as H.
    revert H.
    replace (length (proc_upto [] [] 0%nat)
             + length (if decide (0%nat = 0%nat) then []
                       else line_alts !!! 3%nat)
             + pro_round * 0 + i)%nat with i
      by (vm_compute; reflexivity).
    by intros H.
  Qed.

  Lemma pro_pin_zero (ps cs : list nat) : pro_pin ps cs 0%nat.
  Proof. intros q Hq. lia. Qed.

  (* the frame byte, in two halves: the deposit's closure needs one to
     read the image ([UkRunSys.uheap_ubytes_wat] at a map the closure
     binds) and the leaf needs the other to buy the [uva_rmapped] row *)
  Lemma ubyte_halves (γd : gname) (a : Z) (b : bv 8) :
    ubyte γd a b ⊣⊢
    ubyteq γd (DfracOwn (1/2)) a b ∗ ubyteq γd (DfracOwn (1/2)) a b.
  Proof.
    rewrite /ubyte /ubyteq.
    apply (fractional_half _ (fun q => (a ↪[γd]{DfracOwn q} b)%I) 1%Qp _).
  Qed.

  Lemma ubyte_split (γd : gname) (a : Z) (b : bv 8) :
    ubyte γd a b -∗
    ubyteq γd (DfracOwn (1/2)) a b ∗ ubyteq γd (DfracOwn (1/2)) a b.
  Proof. rewrite (ubyte_halves γd a b). by iIntros "$". Qed.

  Lemma ubyte_join (γd : gname) (a : Z) (b : bv 8) :
    ubyteq γd (DfracOwn (1/2)) a b -∗ ubyteq γd (DfracOwn (1/2)) a b -∗
    ubyte γd a b.
  Proof. rewrite (ubyte_halves γd a b). iIntros "H1 H2". iFrame. Qed.

  Lemma ubytesq_one (γd : gname) (dq : dfrac) (a : Z) (b : bv 8) :
    ubyteq γd dq a b ⊣⊢ ubytesq γd dq a 1%nat (fun _ => b).
  Proof. by rewrite /ubytesq /= Z.add_0_r right_id. Qed.

  Lemma ubytesq_of_one (γd : gname) (dq : dfrac) (a : Z) (b : bv 8) :
    ubyteq γd dq a b -∗ ubytesq γd dq a 1%nat (fun _ => b).
  Proof. rewrite (ubytesq_one γd dq a b). by iIntros "$". Qed.

  Lemma ubytesq_to_one (γd : gname) (dq : dfrac) (a : Z) (b : bv 8) :
    ubytesq γd dq a 1%nat (fun _ => b) -∗ ubyteq γd dq a b.
  Proof. rewrite (ubytesq_one γd dq a b). by iIntros "$". Qed.

  (* =================================================================== *)
  (*  S2  ONE BYTE, THROUGH THE ERA'S WRITE LINK                          *)
  (* =================================================================== *)
  (* the ecall leaves take [UexecSG.sfam] and an [xfam]-typed argument is
     not one until the instance is fixed -- [UShLine.ush_rd_fam]'s mould *)
  Definition kbn_fam (N : uk_names Σ) (Q : nat -> iProp Σ) : sfam :=
    xfam_wr Q (ukn_pay N).

  (* WHAT THE WALK CARRIES, at the round the credential names (lane
     IO-LEAF, M6a(2)): the era's cursor [i] banner bytes into the round's
     own block, or the taint.  Round 0 is this at [n = 0]; a restart round
     is this at whatever count the shell that died left behind.  The shape
     is [EchoLinks]'s, so nothing about the prologue's arithmetic lives in
     this file any more. *)
  Definition bnr (v : era_pins) (n : nat) (i : nat) : iProp Σ :=
    EchoLinks.ewc_ban T v n i.

  Lemma kinit_w1_of_link (N : uk_names Σ) (v : era_pins) (n : nat)
      (l : list fdstate) (rb : bool) (i : nat) (b : bv 8) :
    l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    u_banner !! i = Some b ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    UkInit.kinit_w1 N (mword_of_int 1 : mword 64) b
      (UserFd.ustd (ukn_fd N) l ∗ bnr v n i)
      (UserFd.ustd (ukn_fd N) l ∗ bnr v n (S i)).
  Proof.
    intros Hli Hb.
    iIntros "#Hpin #Hlk" (h m avail) "%Ha0 %Ha2 #Hcode Hbuf [Hl Hbnd] Hrun Hcont".
    (* the two halves *)
    iDestruct (ubyte_split with "Hbuf") as "[Hb1 Hb2]".
    set (ua := m !!! Regidx a1_idx).
    (* the cursor family the deposit is stated at: the closure's half of
       the byte, and the era's cursor before and after this byte *)
    set (Q := (fun k : nat =>
                 ubyteq (ukn_d N) (DfracOwn (1/2)) (uint ua) b
                 ∗ match k with O => bnr v n i | _ => bnr v n (S i) end)%I).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = ua)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx = (mword_of_int 1 : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 1%nat)
      by (rewrite Ham2; vm_compute; reflexivity).
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 1)
      by (rewrite Ham0; vm_compute; reflexivity).
    iApply (UkInit.wp_kinit_write_chain N h m avail
              (kbn_fam N Q) l (DfracOwn (1/2)) 1%nat (fun _ => b)
              with "Hcode Hrun [Hb1 Hbnd] Hl [Hb2]").
    { (* THE DEPOSIT: the caller's own chain at its own cursor *)
      iApply (uwrite_chain_sup N Q
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int InitSyms.write : mword 64) 2)
                l 1%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hli).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   (DfracOwn (1/2)) ua 1%nat (fun _ => b)
                   with "Hheap [Hb1]") as %HM;
        [ iApply (ubytesq_of_one with "Hb1") | ].
      iFrame "Hheap".
      rewrite Ham1 Hcnt. cbn [cons_out_chain].
      iSplit.
      - (* the cursor, unmoved: what the SHORT arm would hand back *)
        rewrite /Q. iFrame "Hb1 Hbnd".
      - iIntros (b') "%Hb'".
        assert (Hbb : b' = b).
        { pose proof (HM 0%nat ltac:(lia)) as HM0.
          cbn in HM0. rewrite HM0 in Hb'. by injection Hb'. }
        subst b'.
        iApply (EchoLinks.echo_banner_step T γ (S gen_id) v n i b (Q 1%nat)
                  Hb with "Hpin Hlk Hbnd [Hb1]").
        iIntros "Hres". rewrite /Q. iFrame "Hb1". rewrite /bnr. iExact "Hres". }
    { iApply (ubytesq_of_one with "Hb2"). }
    iIntros (h' ret W cw' cs') "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hl Hb2 Hpost Hrun".
    (* THE POST: the short arm is refuted from the run the caller owns *)
    iDestruct (uwrite_no_short Q (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 1%nat rb 1%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hli
                 ltac:(rewrite Hka2 Ha2; vm_compute; reflexivity)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    rewrite /Q. iDestruct "HQ" as "[Hb1 Hbnd]".
    iDestruct (ubytesq_to_one with "Hb2") as "Hb2".
    iDestruct (ubyte_join with "Hb1 Hb2") as "Hbuf".
    iApply ("Hcont" $! h' ret with "Hbuf [$Hl $Hbnd] Hrun").
  Qed.

  (* =================================================================== *)
  (*  S3  THE PAYMENT, AT AN ARBITRARY ROUND                              *)
  (* =================================================================== *)
  (* THE CONSOLE DESCRIPTOR /init's OPEN INSTALLS.  Spelt out rather than
     taken from [UInitCons.init_cons_fd]: that file is the application's
     side of the console prologue and this one only needs the fdstate. *)
  Local Notation stc_cons := (FdOpen true true (FdDevice CONSOLE)).

  (* THE TWO CREDENTIALS THE BANNER STANDS BETWEEN, at a count and with
     the era's pin beside them (nothing below this file can produce one).
     [kinit_ban n] is /init's own loop head -- the round's banner owed --
     and [kinit_own n] is what the eighteenth byte leaves: the PROMPT's
     credential, which is what /init lends the shell it forks. *)
  Definition kinit_ban (n : nat) : iProp Σ :=
    (∃ v : era_pins, era_pin γ (S gen_id) v ∗ EchoLinks.ewc_ban T v n 0%nat)%I.

  Definition kinit_own (n : nat) : iProp Σ :=
    (∃ v : era_pins, era_pin γ (S gen_id) v ∗ EchoLinks.ewc_owed T v n)%I.

  Global Instance kinit_ban_timeless n : Timeless (kinit_ban n).
  Proof. rewrite /kinit_ban. apply _. Qed.
  Global Instance kinit_own_timeless n : Timeless (kinit_own n).
  Proof. rewrite /kinit_own. apply _. Qed.

  (* ...AND THE READER'S HALF OF THE DELIVERED COUNT, SPLIT OFF HERE (lane
     IO-LEAF, M5).  [EchoOut.eturn] carries FIVE things and the banner
     spends four of them; the fifth is the reader's half of the era's
     delivered count, which is not the writer's business at all -- it is
     the credential the SHELL needs to read the console, and it travels on
     the console lease ([UserConsole.ucons_pay]'s [Rd]).  So the payment
     hands it straight back, at the era's own pin, and /init's boot bundle
     puts it where the lease is minted. *)
  Definition kinit_dl0 : iProp Σ :=
    (∃ v : era_pins, era_pin γ (S gen_id) v ∗ dl_cnt v (1/2) 0%nat)%I.

  (* THE ERA'S TURN AT STAGE 0 IS ROUND 0's BANNER-OWED CREDENTIAL.  Both
     halves of [EchoOut.eturn] come apart here: the write half becomes
     [kinit_ban 0] ([EchoLinks.wr_ban_round0] is the shape) and the read
     half [kinit_dl0]. *)
  Lemma kinit_ban0_of_eturn :
    eturn γ (S gen_id) -∗ kinit_dl0 ∗ kinit_ban 0%nat.
  Proof.
    iIntros "Hturn".
    iDestruct "Hturn" as (v) "(#Hpin & Htn & Hdl & #Hcs & #Hps & #HE)".
    iSplitL "Hdl"; [ rewrite /kinit_dl0; iExists v; iFrame "Hpin Hdl" | ].
    rewrite /kinit_ban. iExists v. iFrame "Hpin".
    rewrite /EchoLinks.ewc_ban. iLeft. iExists [], [], 0%nat.
    rewrite Nat.add_0_r. iFrame "Htn Hps Hcs HE".
    iPureIntro. exact EchoLinks.wr_ban_round0.
  Qed.

  (* THE BANNER AS A PERSISTENT CONVERSION (lane IO-LEAF, M6a(2)).  What
     /init's walk holds is the credential, and what it needs is the
     payment; the conversion between them is closed under the era's links,
     so it is a [□] and /init's restart loop spends it at EVERY round. *)
  Lemma kinit_banner_law_holds :
    echo_links T γ -∗
    □ (∀ (n : nat) (N : uk_names Σ),
         kinit_ban n -∗ UkInitMain.kinit_banner0 N stc_cons (kinit_own n)).
  Proof.
    iIntros "#Hlk !>" (n N) "Hban".
    rewrite /UkInitMain.kinit_banner0 /UkInit.kinit_banner_pay.
    iIntros "Hl".
    iDestruct "Hban" as (v) "[#Hpin Hbnr]".
    iExists (fun i => UserFd.ustd (ukn_fd N) (ufd_l3 stc_cons) ∗ bnr v n i)%I.
    iSplitR "Hbnr Hl".
    { iIntros "!>" (j) "%Hj".
      iApply (kinit_w1_of_link N v n (ufd_l3 stc_cons) true j
                (init_lit LIT_START j)
                (ufd_l3_row1 stc_cons) (init_banner_bytes j Hj)
                with "Hpin Hlk"). }
    iSplitL; [ iFrame "Hl Hbnr" | ].
    iIntros "[$ Hbnd]". rewrite /kinit_own. iExists v. iFrame "Hpin".
    iApply (EchoLinks.ewc_ban_done T v n with "[Hbnd]").
    rewrite /bnr.
    by replace (length u_banner) with 18%nat by (vm_compute; reflexivity).
  Qed.

  (* =================================================================== *)
  (*  S4  THE CREDENTIAL, AS THE SHELL WILL SPEND IT (lane IO-LEAF,       *)
  (*      M4a(3)).                                                        *)
  (*                                                                     *)
  (*  /init's walk carries what the banner leaves behind OPAQUELY --      *)
  (*  [UkInit.init_exec_sup_pos]'s [Rt] -- because init may name no era   *)
  (*  and sh's walk may name no era either.  So the two ends have to      *)
  (*  agree on ONE proposition, and this is where it is chosen: the pair  *)
  (*  [UShKernel.sh_prompt_pay], the cursor at the round's prompt         *)
  (*  together with the conversion of it into sh's prompt call            *)
  (*  ([UShOut.ksh_w_of_link_prompt]).  Nothing new is OWED by this: the  *)
  (*  conversion is proved, and it is proved here rather than one file    *)
  (*  down because row 16's concrete reading lives above the file system. *)
  (* =================================================================== *)
  (* [kinit_banner_pay]'s [Rt] occurs POSITIVELY (it is what the last
     byte's continuation hands back), so a payment that leaves one
     credential behind leaves any consequence of it behind. *)
  Lemma kinit_banner0_mono (N : uk_names Σ) (Rt Rt' : iProp Σ) :
    (Rt -∗ Rt') -∗
    UkInitMain.kinit_banner0 N stc_cons Rt -∗
    UkInitMain.kinit_banner0 N stc_cons Rt'.
  Proof.
    iIntros "Hm H".
    rewrite /UkInitMain.kinit_banner0 /UkInit.kinit_banner_pay.
    iIntros "Hl". iDestruct ("H" with "Hl") as (Ch) "(#Hst & H0 & Hfin)".
    iExists Ch. iFrame "Hst H0".
    iIntros "HC". iDestruct ("Hfin" with "HC") as "[$ Hrt]".
    iApply ("Hm" with "Hrt").
  Qed.

  (* ...and what /init's banner leaves behind IS the shell's prompt pair,
     at the round's own count. *)
  Lemma sh_prompt_pay_of_kinit_own (n : nat) :
    echo_links T γ -∗ kinit_own n -∗ UShKernel.sh_prompt_pay.
  Proof.
    iIntros "#Hlk Ht". rewrite /kinit_own.
    iDestruct "Ht" as (v) "[#Hpin Hc]".
    iApply (UShOut.sh_prompt_pay_of_ushpr T γ v n with "Hpin Hlk [Hc]").
    rewrite /UShOut.ushpr. iExact "Hc".
  Qed.

  Lemma kinit_banner0_pay_holds :
    echo_links T γ -∗
    eturn γ (S gen_id) -∗
    kinit_dl0
    ∗ ∀ N : uk_names Σ,
        UkInitMain.kinit_banner0 N stc_cons UShKernel.sh_prompt_pay.
  Proof.
    iIntros "#Hlk Hturn".
    iDestruct (kinit_ban0_of_eturn with "Hturn") as "[Hdl Hban]".
    iDestruct (kinit_banner_law_holds with "Hlk") as "#Hlaw".
    iSplitL "Hdl"; [ iExact "Hdl" | ].
    iIntros (N).
    iApply (kinit_banner0_mono N (kinit_own 0%nat) UShKernel.sh_prompt_pay
              with "[] [Hban]"); last first.
    { iApply ("Hlaw" $! 0%nat N with "Hban"). }
    iIntros "Ht". iApply (sh_prompt_pay_of_kinit_own 0%nat with "Hlk Ht").
  Qed.

End UInitBanner.
