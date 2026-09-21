(* ===================================================================== *)
(*  UShPipeAssembly.v -- THE PIPELINE ROUND'S ASSEMBLY LEAVES             *)
(*  (lane SH-PIPE-ROUND-8; design claude-notes/design/app-pipe.md         *)
(*  SS4.3o-SS4.3q).                                                       *)
(*                                                                       *)
(*  SS4.3q ruled that the round's one remaining hole is a TOKEN in        *)
(*  [UShPipeChild.wp_kshm_child_pipe_paid_line] -- its exit-payment wand  *)
(*  becoming a fancy update.  Measuring the round against the landed      *)
(*  pieces found that ruling wrong in both directions (see the lane's     *)
(*  Findings block and [UShPipeChild]'s S0) and found THREE OTHER holes,  *)
(*  each of which is generic and each of which is closed here:            *)
(*                                                                       *)
(*   S1  [ksh_w1_acc] / [exf_law_fupd]: an exec-failed diagnostic law is  *)
(*       closed under a FANCY UPDATE on the credential it is paid from,   *)
(*       as long as it writes at least one byte.  This is what lets the   *)
(*       [pipe(2)]-failed tail be paid from the two-writer FAMILY: the    *)
(*       family unwinds to the lend ([UShPipeRound2.pipe_round_unwind],   *)
(*       a fupd), and the unwind happens at the diagnostic's FIRST WRITE  *)
(*       -- a WP point -- rather than at the law's pure entry.            *)
(*   S2  [ksh_w1_of_step]: one console byte of ANY step family, through   *)
(*       [UkShDiag.ksh_w1].  [UShPanic.ksh_w1_of_link_blk_at] is this at  *)
(*       the LINK RECORD's own block family; the round's three console    *)
(*       chains ([PipeBoth.pblk2_cstep_L], [pblk2_cstep_R_t] and          *)
(*       [pblk2_fork1_chain]) have the same [out_link] step shape and no  *)
(*       record behind them, so the byte is stated once at an abstract    *)
(*       family here.                                                     *)
(*   S3  the PROTOCOL'S NAMES, ALLOCATED BEFORE [pipe(2)].                *)
(*       [PipeProto.pipe_proto_alloc] mints [pnames] and the invariant    *)
(*       together, inside the [pipe(2)] registrar -- but the round's      *)
(*       family ([PipeBoth.blk2_inv]) has to be allocated BEFORE          *)
(*       [pipe(2)] (it is the lend, and the [pipe(2)]-failed tail is paid *)
(*       from it), and its two exclusion witnesses are PIPE-EXEC-ECHO's   *)
(*       [XL := wcur pn 0] / [YR := pws_lb pn (take 1 L)], which name     *)
(*       [pn].  So the allocation is split in two: the names and the      *)
(*       body's half here, the invariant at the registrar.                *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl agree csum.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import own ghost_map ghost_var invariants.
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
Require Import UserHeap.
Require Import UserPerm.
Require Import ProcPtOwn.
Require Import UserPtTree.
Require Import UmodeArith.
Require Import ProcGeom.
Require Import UexecSlot UexecRet UexecSG.
Require Import UkRun UkRunLeaf UkRunSys.
Require Import SpecConsolewrite.   (* [cons_out_chain] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import ConsoleInv.         (* [CONSOLE] *)
Require Import WpUart.             (* [out_link] *)
Require Import UkWriteLeaf.
Require Import UCodeShK.
Require Import UkSh.
Require Import UkShDiag.
Require Import UShOut.
Require Import UShPanic.           (* the mould: [ksh_w1_of_link_blk_at] *)
Require Import PipeNames.
Require Import PipeQueue.
Require Import PipeReg.
Require Import PipeProto.
Require Import ObsTrace.
Require Import ConsLog.
Require Import LineWords.
Require Import EchoDisc.
Require Import PipeDisc.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import AppEcho.
Require Import PipeOutPure.
Require Import PipeOut.
Require Import PipeBothPure.
Require Import PipeBoth.
Require Import PipeLinks.
Require Import PipeLinksLine.
Require Import PipeLinkInst.
Require Import UkShFork.
Require Import UkShPipeFork.      (* [pterm_shape] -- the terminal payload *)
Require Import UShPipeRound2.     (* [blk2N] and the round's two ends *)
Require Import CtxIdDefs.
Require User.ShSyms.
Local Open Scope list_scope.

(* ===================================================================== *)
(*  S1/S2  THE TWO GENERIC LEAVES                                        *)
(* ===================================================================== *)
Section UShPipeAssemblyGen.
  (* [UShPanic.v]'s [UShPanicGen] binder list, MINUS the link record --
     nothing here reads one -- and minus [echoOutG]. *)
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  (* A FANCY UPDATE IN FRONT OF THE TRIVIAL-POST WP ([UConsOpen.
     fupd_wp_triv] restated; that file is not in this one's cone). *)
  Local Lemma fupd_mwp (e : expr riscv_lang) : (|={⊤}=> mWP e) ⊢ mWP e.
  Proof using . rewrite /wp_triv. iIntros "H". iApply fupd_wp. iExact "H". Qed.

  (* =================================================================== *)
  (*  S1  A BYTE'S WRITE IS AN ACCESSOR ON ITS OWN PRECONDITION           *)
  (*                                                                     *)
  (*  [UkShDiag.ksh_w1]'s conclusion is a [mWP], so the resource it is    *)
  (*  paid with may be handed over under a FANCY UPDATE.  This is the     *)
  (*  whole of SS4.3q's problem, moved from the law's pure entry (where   *)
  (*  it cannot be paid) to the first byte (where it can).                *)
  (* =================================================================== *)
  Lemma ksh_w1_acc (N : uk_names Σ) (fdv : mword 64) (b : bv 8)
      (Ci Co : iProp Σ) :
    □ (Ci ={⊤}=∗ ∃ D : iProp Σ, D ∗ ksh_w1 N fdv b D Co) -∗
    ksh_w1 N fdv b Ci Co.
  Proof using .
    iIntros "#Hacc" (ua h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hb HCi] Hrun Hcont".
    iApply fupd_mwp.
    iMod ("Hacc" with "HCi") as (D) "[HD Hw]". iModIntro.
    iApply ("Hw" $! ua h m avail with "[%] [%] [%] Hcode [Hb HD] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ]. iFrame "Hb HD".
  Qed.

  (* ...AND THE LAW, AT A CREDENTIAL THAT ONLY A FUPD REACHES.  [0 < n] is
     what makes it true: the caller's own [Cr] is handed on unchanged as
     [Pf 0], and every later index is the WITNESSED law's, so the end
     ([Pf n -* Cd], a PURE wand) is the witnessed law's own end. *)
  Lemma exf_law_fupd (dg : list (bv 8)) (n : nat) (Cr Cr' Cd : iProp Σ) :
    (0 < n)%nat ->
    □ (Cr ={⊤}=∗ Cr') -∗
    ush_execfail_law_at dg n Cr' Cd -∗
    ush_execfail_law_at dg n Cr Cd.
  Proof using .
    intro Hn. iIntros "#Hup #Hlaw". rewrite /ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd Hc".
    pose (G := fun p : nat =>
                 (∃ Pf : nat -> iProp Σ,
                    Pf p
                    ∗ □ (∀ (q : nat) (b : bv 8),
                           ⌜ dg !! q = Some b ⌝ -∗
                           ksh_w1 N (mword_of_int 2 : mword 64) b
                             (UserFd.ustd (ukn_fd N) l ∗ Pf q)
                             (UserFd.ustd (ukn_fd N) l ∗ Pf (S q)))
                    ∗ □ (Pf n -∗ Cd))%I).
    iExists (fun p : nat => match p with O => Cr | S q => G (S q) end).
    iSplitL "Hc"; [ iExact "Hc" | ].
    iSplit.
    - iIntros "!>" (p b) "%Hb".
      iApply (ksh_w1_acc N (mword_of_int 2 : mword 64) b).
      iIntros "!> [Hl Hp]".
      destruct p as [| q].
      + (* THE FIRST BYTE: the fupd is spent here *)
        iMod ("Hup" with "Hp") as "Hp".
        iDestruct ("Hlaw" $! N l with "[%] Hp")
          as (Pf) "(H0 & #Hs & #He)"; [ exact Hfd | ].
        iModIntro. iExists (UserFd.ustd (ukn_fd N) l ∗ Pf 0%nat)%I.
        iSplitL; [ iFrame "Hl H0" | ].
        iApply (ksh_w1_mono N (mword_of_int 2 : mword 64) b
                  (UserFd.ustd (ukn_fd N) l ∗ Pf 0%nat)%I
                  (UserFd.ustd (ukn_fd N) l ∗ Pf 1%nat)%I
                  with "[] [Hs]").
        { iIntros "!> [$ Hq]". rewrite /G. iExists Pf. by iFrame "Hq Hs He". }
        { iApply ("Hs" $! 0%nat b). by iPureIntro. }
      + (* EVERY LATER BYTE: the witness is opened and re-packed *)
        rewrite /G. iDestruct "Hp" as (Pf) "(Hq & #Hs & #He)".
        iModIntro. iExists (UserFd.ustd (ukn_fd N) l ∗ Pf (S q))%I.
        iSplitL; [ iFrame "Hl Hq" | ].
        iApply (ksh_w1_mono N (mword_of_int 2 : mword 64) b
                  (UserFd.ustd (ukn_fd N) l ∗ Pf (S q))%I
                  (UserFd.ustd (ukn_fd N) l ∗ Pf (S (S q)))%I
                  with "[] [Hs]").
        { iIntros "!> [$ Hq']". rewrite /G. iExists Pf.
          by iFrame "Hq' Hs He". }
        { iApply ("Hs" $! (S q) b). by iPureIntro. }
    - destruct n as [| n']; [ lia | ].
      iIntros "!> Hp". rewrite /G. iDestruct "Hp" as (Pf) "(Hn & _ & #He)".
      iApply ("He" with "Hn").
  Qed.

  (* =================================================================== *)
  (*  S2  ONE CONSOLE BYTE OF AN ABSTRACT STEP FAMILY                     *)
  (*                                                                     *)
  (*  [UShPanic.ksh_w1_of_link_blk_at]'s proof with the record's block    *)
  (*  family and its step replaced by a parameter: the call does not      *)
  (*  care which family the byte moves, only that the byte HAS a link     *)
  (*  step.  ([UShPanic.ksh_w_of_link_prompt_fam] is the same move one    *)
  (*  call up, for the prompt's two bytes.)                               *)
  (* =================================================================== *)
  Lemma ksh_w1_of_step (N : uk_names Σ) (F : nat -> iProp Σ)
      (l : list fdstate) (rb : bool) (i : nat) (b : bv 8) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    □ (∀ Φ : iProp Σ,
         F i -∗ (F (S i) -∗ Φ) -∗ out_link Uart0 (S gen_id) b Φ) -∗
    ksh_w1 N (mword_of_int 2 : mword 64) b
      (UserFd.ustd (ukn_fd N) l ∗ F i)
      (UserFd.ustd (ukn_fd N) l ∗ F (S i)).
  Proof using .
    intros Hl2.
    iIntros "#Hstep" (ua h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hbuf [Hl Hc]] Hrun Hcont".
    subst ua.
    iDestruct (ubyte_split with "Hbuf") as "[Hb1 Hb2]".
    set (ua := m !!! Regidx a1_idx).
    set (Q := (fun k : nat =>
                 ubyteq (ukn_d N) (DfracOwn (1/2)) (uint ua) b
                 ∗ match k with
                   | O => F i
                   | _ => F (S i)
                   end)%I).
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = ua)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 1%nat) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 1%nat)
      by (rewrite Ham2; vm_compute; reflexivity).
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 2)
      by (rewrite Ham0; vm_compute; reflexivity).
    iApply (wp_ksh_write_chain_buf N h m avail
              (UShOut.ksh_fam N Q) l (DfracOwn (1/2)) 1%nat (fun _ => b)
              with "Hcode Hrun [Hb1 Hc] Hl [Hb2]").
    { iApply (uwrite_chain_sup N Q
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int ShSyms.write : mword 64) 2)
                l 2%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl2).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_ubytes_wat (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   (DfracOwn (1/2)) ua 1%nat (fun _ => b)
                   with "Hheap [Hb1]") as %HM;
        [ iApply (ubytesq_of_one with "Hb1") | ].
      iFrame "Hheap".
      rewrite Ham1 Hcnt. cbn [cons_out_chain].
      iSplit.
      - rewrite /Q. iFrame "Hb1 Hc".
      - iIntros (b') "%Hb'".
        assert (Hbb : b' = b).
        { pose proof (HM 0%nat ltac:(lia)) as HM0.
          cbn in HM0. rewrite HM0 in Hb'. by injection Hb'. }
        subst b'.
        iApply ("Hstep" $! (Q 1%nat) with "Hc [Hb1]").
        iIntros "Hres". rewrite /Q. iFrame "Hb1". iExact "Hres". }
    { iApply (ubytesq_of_one with "Hb2"). }
    iIntros (h' ret W cw' cs') "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hl Hb2 Hpost Hrun".
    iDestruct (uwrite_no_short Q (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 2%nat rb 1%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl2
                 ltac:(rewrite Hka2 Ha2; vm_compute; reflexivity)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    rewrite /Q. iDestruct "HQ" as "[Hb1 Hc]".
    iDestruct (ubytesq_to_one with "Hb2") as "Hb2".
    iDestruct (ubyte_join with "Hb1 Hb2") as "Hbuf".
    iApply ("Hcont" $! h' ret with "[Hbuf Hl Hc] Hrun").
    iFrame "Hbuf Hl". iExact "Hc".
  Qed.

End UShPipeAssemblyGen.

(* ===================================================================== *)
(*  S3  THE PROTOCOL'S NAMES, BEFORE [pipe(2)]                           *)
(* ===================================================================== *)
Section UShPipeAssemblyProto.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{!pipeProtoG Σ}.

  (* THE BODY'S OWN HALF at the initial state, which is what
     [PipeProto.pipe_proto_alloc] puts inside the invariant it allocates.
     Splitting the allocation in two is what lets the round name [pn]
     BEFORE [pipe(2)] -- see the header. *)
  Definition pipe_pre (pn : pnames) : iProp Σ :=
    (pws_auth pn [] ∗ PipeProto.wcur pn 0%nat ∗ PipeProto.rcur pn 0%nat
     ∗ eof_pending pn ∗ ro_pending pn)%I.

  Lemma pipe_names_alloc :
    ⊢ |==> ∃ pn : pnames,
        pipe_pre pn ∗ wtok pn ∗ rtok pn ∗ side_L pn ∗ side_R pn.
  Proof using .
    iIntros "".
    iMod (own_alloc (●ML ([] : list (leibnizO (bv 8))))) as (gh) "Hh";
      [ apply mono_list_auth_valid |].
    iMod (own_alloc (Cinl (Excl ()) : pipe_eofR)) as (ge) "He"; [ done |].
    iMod (own_alloc (Cinl (Excl ()) : pipe_roR)) as (go) "Ho"; [ done |].
    iMod (ghost_var_alloc (0%nat)) as (gw) "Hw".
    iMod (ghost_var_alloc (0%nat)) as (gr) "Hr".
    iMod (own_alloc (Excl ())) as (gl) "Hsl"; [ done |].
    iMod (own_alloc (Excl ())) as (gs) "Hsr"; [ done |].
    iDestruct (ghost_var_split (pn_wcur (MkPNames gh ge go gw gr gl gs))
                 0%nat (1/2) (1/2) with "[Hw]") as "[Hw1 Hw2]";
      [ by rewrite Qp.half_half | ].
    iDestruct (ghost_var_split (pn_rcur (MkPNames gh ge go gw gr gl gs))
                 0%nat (1/2) (1/2) with "[Hr]") as "[Hr1 Hr2]";
      [ by rewrite Qp.half_half | ].
    iModIntro. iExists (MkPNames gh ge go gw gr gl gs).
    rewrite /pipe_pre /wtok /rtok /side_L /side_R /pws_auth /PipeProto.wcur
            /PipeProto.rcur /eof_pending /ro_pending /=.
    by iFrame "Hh Hw1 Hr1 He Ho Hw2 Hr2 Hsl Hsr".
  Qed.

  (* ...AND THE SECOND HALF, at the registrar: the queue's fragment joins
     the names and the invariant is allocated.  [PipeProto.pipe_proto_alloc]
     is this composed with the one above. *)
  Lemma pipe_inv_alloc_at (pn : pnames) (gp : pipe_names)
      (L : list (bv 8)) :
    pipe_pre pn -∗ pipe_qfrag (pn_queue gp) pst0 ={⊤}=∗
    pipe_inv pn gp L ∗ pipe_reg gp.
  Proof using .
    iIntros "(Hh & Hw & Hr & He & Ho) Hfrag".
    iMod (inv_alloc pipeN ⊤ (pipe_body pn gp L)
            with "[Hfrag Hh Hw Hr He Ho]") as "#Hinv".
    { iNext. iExists pst0. rewrite /pst0 /=. iFrame "Hfrag Hh Hw Hr".
      iSplitR; [ iPureIntro; apply prefix_nil | ].
      iSplitR; [ iPureIntro; cbn; lia | ].
      iSplitL "He"; [ by iLeft | by iLeft ]. }
    iModIntro. rewrite /pipe_inv. iFrame "Hinv".
    iApply (pipe_reg_of_inv pn gp L with "Hinv").
  Qed.

End UShPipeAssemblyProto.

(* ===================================================================== *)
(*  S4  THE RUNCMD CHILD'S OWN [fork1] PANIC, AS A DIAGNOSTIC LAW        *)
(*                                                                       *)
(*  The round hands each [fork1] tail [Cx gp] and takes back             *)
(*  [ukn_pay N (-1)] through [Bx gp] ([UShPipeChild.                     *)
(*  wp_kshm_child_pipe_paid_line]'s last two premises).  At the pipeline *)
(*  era the payload is [UkShPipeFork.pterm_pay I], whose SECOND ARM is   *)
(*  the terminal shape at cursor 5 -- so this law IS design SS4.3h's      *)
(*  terminal round, in the shape the walk consumes:                      *)
(*                                                                       *)
(*    [Cx gp] := the family's right and mode halves, both at 0           *)
(*    [Bx gp] := [UkShPipeFork.pterm_shape g I 5]                        *)
(*                                                                       *)
(*  It needs TWO of this file's leaves and nothing else: the mode's fire *)
(*  to 3 ([PipeBoth.blk2_mode_fire]) is a FANCY UPDATE and is spent at   *)
(*  the first byte through [exf_law_fupd]; each of `fork\n''s five bytes *)
(*  is [PipeBoth.pblk2_cstep_R_t] through [ksh_w1_of_step].              *)
(* ===================================================================== *)
Section UShPipeAssemblyFork.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!uartGhostG Σ}.
  Context `{!echoOutG Σ, !pipeOutG Σ}.
  Context (g : pipe_gn).
  Local Notation γ := (pgn_cl g).
  Context (Hcons : @riscv_cons_res Σ (@riscv_fixedGS Σ _) = pecl g).
  Context `{PS : uprogSG Σ}.

  Local Notation PT := (echo_taint γ).

  (* the five bytes of `fork\n' are [alt_forkc]'s first five *)
  Local Lemma fork_panic_byte (p : nat) (b : bv 8) :
    alt_panic !! p = Some b -> alt_forkc !! p = Some b.
  Proof using .
    intro Hb. rewrite alt_forkc_panic. by apply lookup_app_l_Some.
  Qed.

  (* THE LAW.  Everything persistent the family's byte step asks for is a
     premise here, so what the round lends the two [fork1] tails is the
     two ghost halves and nothing else. *)
  Lemma pipe_fork_panic_law (v : era_pins) (I L : list (bv 8))
      (ws : list (list (bv 8))) (gL gR gM : gname) (XL YR : iProp Σ) :
    Timeless XL -> Timeless YR ->
    pline_at I = LPipe ws ->
    pipe_link_taint g -∗
    era_pin γ (S gen_id) v -∗
    inp_lb v I -∗
    blk2_inv g blk2N (S gen_id) v I L gL gR gM XL YR -∗
    ush_execfail_law_at alt_panic 5%nat
      (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat)
      (UkShPipeFork.pterm_shape g I 5%nat).
  Proof using Hcons.
    intros HTX HTY Hline.
    iIntros "#Ht #Hpin #Hlb #Hinv".
    assert (Hbl : pboth_line I) by (exists ws; exact Hline).
    assert (Hwitt : forall sel : list bool,
               sel_wf2 alt_forkc sel -> pblk2_wit_t I alt_forkc sel)
      by (intros sel Hs; exact (pblk2_wit_t_forkc I ws sel Hline Hs)).
    (* ---- (1) THE MODE FIRES AT THE FIRST BYTE, under [exf_law_fupd] ---- *)
    iApply (exf_law_fupd alt_panic 5%nat
              (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 0%nat)%I
              (PipeBoth.wcur gR (1/2) 0%nat ∗ PipeBoth.wcur gM (1/2) 3%nat)%I
              (UkShPipeFork.pterm_shape g I 5%nat) ltac:(lia) with "[] []").
    { iIntros "!> [HcR HcM]".
      iMod (blk2_mode_fire g ⊤ blk2N (S gen_id) v I L gL gR gM XL YR 3%nat
              HTX HTY ltac:(apply top_subseteq) ltac:(by right; right)
              with "Hinv HcM HcR []") as "[HcM HcR]".
      { iIntros "%Hq". discriminate Hq. }
      iModIntro. iFrame "HcR HcM". }
    (* ---- (2) THE FIVE BYTES, each [pblk2_cstep_R_t] ---- *)
    rewrite /ush_execfail_law_at.
    iIntros "!>" (N l) "%Hfd2 Hc". destruct Hfd2 as [rb Hl2].
    iExists (fun p : nat =>
               (PipeBoth.wcur gR (1/2) p ∗ PipeBoth.wcur gM (1/2) 3%nat
                ∗ (match p with
                   | O => True
                   | _ => cs_frozen_at v (nlines I - 1)%nat ∨ PT
                   end))%I)%I.
    iSplitL "Hc"; [ by iDestruct "Hc" as "[$ $]" | ].
    iSplit.
    - iIntros "!>" (p b) "%Hb".
      (* THE FAMILY IS NAMED AND NOT SEARCHED: with [_] here the elaborator
         has to solve [?F p =?= ...] and [?F (S p) =?= ...] together and
         does not come back (measured: >10 min, then [Set Default Timeout]
         cut it). *)
      iApply (ksh_w1_of_step N
                (fun q : nat =>
                   (PipeBoth.wcur gR (1/2) q ∗ PipeBoth.wcur gM (1/2) 3%nat
                    ∗ (match q with
                       | O => True
                       | _ => cs_frozen_at v (nlines I - 1)%nat ∨ PT
                       end))%I)
                l rb p b Hl2).
      iIntros "!>" (Φ) "Hf HΦ".
      iDestruct "Hf" as "(HcR & HcM & _)".
      iApply (pblk2_cstep_R_t g Hcons blk2N (S gen_id) v I L gL gR gM XL YR
                p b Φ HTX HTY blk2N_uart (fork_panic_byte p b Hb) Hwitt
                with "[] Ht Hpin Hinv HcR HcM").
      { iApply pblk2_ecl_R_t_holds. }
      iIntros "HcR HcM #Hfz". iApply "HΦ". iFrame "HcR HcM". iExact "Hfz".
    - iIntros "!> (HcR & HcM & #Hfz)".
      rewrite /UkShPipeFork.pterm_shape.
      iExists v, L, gL, gR, gM, XL, YR.
      iSplitR; [ iPureIntro; split_and!; assumption | ].
      iFrame "Hpin Hlb". rewrite /pwc_fork_exit.
      by iFrame "Hinv HcR HcM Hfz".
  Qed.

End UShPipeAssemblyFork.
