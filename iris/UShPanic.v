(* ===================================================================== *)
(*  UShPanic.v -- WHAT PAYS FOR SH'S PANIC LINE AND FOR ITS PROMPT AFTER  *)
(*  A CHILD (app-echo.md, "E5 -- THE CONSOLE I/O CLAIM"; lane             *)
(*  SH-LINE-CRED, the per-call obligations M3b core wires into the walk). *)
(*                                                                       *)
(*  Two obligations of the shell's walk are met here by the era's links,  *)
(*  at the credential shapes [EchoLinksLine] carries:                     *)
(*                                                                       *)
(*    [ksh_w1_of_link_panic]  one byte of "fork\n" ([EchoDisc.line_alts   *)
(*        !!! 3]) through [UkShDiag.ksh_w1], the diagnostic tower's       *)
(*        per-byte obligation at fd 2 -- sh's [fork1] panics when fork    *)
(*        fails, [printf]'s putc spills the byte on its own STACK and     *)
(*        calls [write(2, &c, 1)].  The credential moves from             *)
(*        [ewc_panic v n i] to [ewc_panic v n (S i)]; five bytes on it    *)
(*        is the next round's banner ([EchoLinksLine.ewc_panic_done]).    *)
(*    [ksh_w_of_link_prompt_post] / [ksh_w_of_link_lcred]  the prompt     *)
(*        "$ " as ONE two-byte call ([UkSh.ksh_w] at [getcmd]'s write),   *)
(*        from the block a child wrote up to its prompt ([ewc_post]) or   *)
(*        from the widened boundary credential ([ewc_lcred _ _ 0]), to    *)
(*        the settled round ([ewc_open_t] / [ewc_lcred _ _ 2]);           *)
(*        [sh_prompt_law_holds_line] is [UShKernel.sh_prompt_law] at the  *)
(*        widened family, so the shell's [Wc] can be instantiated at      *)
(*        [ewc_lcred] with nothing in [UkSh] touched.                     *)
(*                                                                       *)
(*  WHY A FILE OF ITS OWN: [UShOut]'s reason -- the conversion needs row  *)
(*  16's CONCRETE reading ([UkWriteLeaf.uwrite_chain_sup] /              *)
(*  [uwrite_no_short]) and every file of sh's walk sits below the file    *)
(*  system.  It is [UShOut] at the shapes a child leaves behind.          *)
(*                                                                       *)
(*  THE STACK BYTE.  The panic's bytes go out one at a time from putc's   *)
(*  frame ([UserHeap.ubyte] in the WRITABLE half), and the short arm of   *)
(*  the write is refuted from that byte's own page -- which needs the    *)
(*  leaf that carries the source run ([UkRunSys.wp_uk_ecall_write_chain_ *)
(*  buf]).  [UkSh.wp_ksh_write_chain] hands the leaf no run, so sh's      *)
(*  three-instruction write stub is restated over the run-carrying leaf   *)
(*  here ([wp_ksh_write_chain_buf], [UkInit.wp_kinit_write_chain]'s       *)
(*  twin at sh); the prompt's literal takes [UkSh.wp_ksh_write_chain_txt] *)
(*  as before.                                                            *)
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
Require Import UserBits.
Require Import ProcGeom.
Require Import VcGen.
Require Import PieceFam.
Require Import FsTree.
Require Import ChildTok.
Require Import UexecSlot UexecRet UsysMemOk UexecSG.
Require Import UkRun UkRunLeaf UkRunSys.
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
Require Import UCodeShK.           (* [shk_ro] / [shk_rodata] / [uis_shk_*] *)
Require Import UkSh.               (* [ksh_w] / [wp_ksh_write_chain_txt] *)
Require Import UkShDiag.           (* [ksh_w1]: the diagnostic tower's byte *)
Require Import UShKernel.          (* [sh_prompt_law] *)
Require Import UShOut.             (* the prompt's pure half and its call *)
Require Import EchoDisc.
Require Import EchoOutPure.
Require Import EchoOut.
Require Import EchoLinks.
Require Import EchoLinksLine.
Require Import TsoCtx.
Require User.ShSyms.
(* as in EchoDisc / UEchoOut / UShOut: the Sail imports leave string_scope
   on top and [++] would elaborate as String.append *)
Local Open Scope list_scope.

Local Lemma shp_write : ShSyms.write = 0xca6%Z.
Proof. reflexivity. Qed.

Section UShPanic.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!echoOutG Σ}.
  Context (T : iProp Σ) (γ : echo_gn).
  Context `{!Persistent T} `{!Timeless T}.
  (* NO [ctokG] AND NO [uexecSG] VARIABLE, for [UInitBanner]'s reasons:
     [Xv6G.xv6_ctok] is an instance and this file reads row 16's CONCRETE
     arm, so the deposit instance has to be the xv6 one. *)
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation sh_prompt_pv := UkSh.sh_prompt_pv.

  (* =================================================================== *)
  (*  S1  THE FRAME BYTE, IN TWO HALVES ([UInitBanner]'s five lines,      *)
  (*      restated so that this file sits where its row says)             *)
  (* =================================================================== *)
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
  (*  S2  SH'S WRITE STUB OVER THE RUN-CARRYING LEAF                      *)
  (*      ([UkSh.wp_ksh_write_chain] instruction for instruction, with    *)
  (*      [UkRunSys.wp_uk_ecall_write_chain_buf] at the ecall)            *)
  (* =================================================================== *)
  Lemma wp_ksh_write_chain_buf (N : uk_names Σ) (h : CpuId) (m : regfile)
      (avail : nat) (fdep : sfam) (l : list fdstate)
      (dq : dfrac) (nb : nat) (fb : nat -> bv 8) :
    shk_code (ukn_t N) -∗
    urun N h m (mword_of_int ShSyms.write) avail -∗
    udepwf_std N (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      (add_vec_int (mword_of_int ShSyms.write : mword 64) 2) 16 fdep l -∗
    UserFd.ustd (ukn_fd N) l -∗
    ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb fb -∗
    (∀ (h' : CpuId) (ret : mword 64) (W : uvis) (cw' : Z) (cs' : gset gname),
       ⌜tf_w (uvis_tf W) (tf_arg_idx 0) = m !!! Regidx a0_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 1) = m !!! Regidx a1_idx⌝ -∗
       ⌜tf_w (uvis_tf W) (tf_arg_idx 2) = m !!! Regidx a2_idx⌝ -∗
       ⌜take NSTD (uvis_fd W) = l⌝ -∗
       ⌜uvis_lazy W = false⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat j))) ⌝ -∗
       UserFd.ustd (ukn_fd N) l -∗
       ubytesq (ukn_d N) dq (uint (m !!! Regidx a1_idx)) nb fb -∗
       spost_at uslot 16 fdep W ret (uvis_M W) (uvis_fd W) cw' cs' -∗
       urun N h'
         (<[Regidx a0_idx := ret]>
            (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m))
         (ret_pc (m !!! Regidx ra_idx)) avail -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros "#Hcode Hrun Hsb Hstd Hbuf Hcont".
    rewrite shp_write.
    (* ---- 0xca6  c.li a7,16 ---- *)
    iApply (wp_uk_cli N h m (mword_of_int 0xca6)
              (mword_of_int 16 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply (uis_shk_ca6 with "Hcode"). }
    assert (Eca6 : add_vec_int (mword_of_int 0xca6 : mword 64) 2
                   = mword_of_int 0xca8)
      by (apply bv_eq; vm_compute; reflexivity).
    assert (Em : <[Regidx a7_idx
                   := regval_into_reg (sign_extend' 64 (mword_of_int 16 : mword 6)
                                       : mword 64)]> m
                 = <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
      by (f_equal; apply bv_eq; vm_compute; reflexivity).
    rewrite Eca6 Em.
    iIntros (h1) "Hrun".
    set (m1 := <[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m).
    assert (Hm1a1 : m1 !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    (* ---- 0xca8  ecall -- THE CHAIN-PAYING WRITE, with the run ---- *)
    iApply (wp_uk_ecall_write_chain_buf N h1 m1 (mword_of_int 0xca8) avail
              fdep l dq nb fb
              ltac:(unfold m1, usysno;
                    rewrite (upd_eq m (Regidx a7_idx)
                               (mword_of_int 16 : mword 64));
                    vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun Hsb Hstd [Hbuf]").
    { iApply (uis_shk_ca8 with "Hcode"). }
    { rewrite Hm1a1. iExact "Hbuf". }
    assert (Eca8 : add_vec_int (mword_of_int 0xca8 : mword 64) 4
                   = mword_of_int 0xcac)
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Eca8.
    iIntros (h2 ret W cw' cs') "%Ha0 %Ha1 %Ha2 %Htk %Hlz %Hnf Hstd Hbuf Hpost Hrun".
    set (m2 := <[Regidx a0_idx := ret]> m1).
    (* ---- 0xcac  c.jr ra ---- *)
    assert (Hra : m2 !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold m2, m1.
      exact (eq_trans
               (upd_ne m1 (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx)
                  (mword_of_int 16 : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 m2 (mword_of_int 0xcac) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity)
              with "[] Hrun").
    { iApply (uis_shk_cac with "Hcode"). }
    iIntros (h3) "Hrun".
    (* the three argument words are the CALLER's: the stub writes a7 and
       then a0, and neither is a0/a1/a2 before the bump *)
    assert (Hm1a0 : m1 !!! Regidx a0_idx = m !!! Regidx a0_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Hm1a2 : m1 !!! Regidx a2_idx = m !!! Regidx a2_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
                  ltac:(vm_compute; discriminate)).
    rewrite Hm1a1 in Ha1 Hnf.
    iApply ("Hcont" $! h3 ret W cw' cs' with "[%] [%] [%] [%] [%] [%] Hstd [Hbuf] Hpost Hrun").
    { rewrite Ha0. exact Hm1a0. }
    { exact Ha1. }
    { rewrite Ha2. exact Hm1a2. }
    { exact Htk. }
    { exact Hlz. }
    { exact Hnf. }
    { rewrite Hm1a1. iExact "Hbuf". }
  Qed.

  (* =================================================================== *)
  (*  S3  ONE BYTE OF THE PANIC LINE, THROUGH THE ERA'S LINK              *)
  (*      ([UInitBanner.kinit_w1_of_link]'s mould at sh's fd 2)           *)
  (* =================================================================== *)
  Lemma ksh_w1_of_link_panic (N : uk_names Σ) (v : era_pins) (n : nat)
      (l : list fdstate) (rb : bool) (i : nat) (b : bv 8) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    line_alts !!! 3%nat !! i = Some b ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    UkShDiag.ksh_w1 N (mword_of_int 2 : mword 64) b
      (UserFd.ustd (ukn_fd N) l ∗ EchoLinksLine.ewc_panic T v n i)
      (UserFd.ustd (ukn_fd N) l ∗ EchoLinksLine.ewc_panic T v n (S i)).
  Proof.
    intros Hl2 Hb.
    iIntros "#Hpin #Hlk" (ua h m avail) "%Ha0 %Ha1 %Ha2 #Hcode [Hbuf [Hl Hc]] Hrun Hcont".
    subst ua.
    (* the two halves *)
    iDestruct (ubyte_split with "Hbuf") as "[Hb1 Hb2]".
    set (ua := m !!! Regidx a1_idx).
    (* the cursor family the deposit is stated at: the closure's half of
       the byte, and the era's cursor before and after this byte *)
    set (Q := (fun k : nat =>
                 ubyteq (ukn_d N) (DfracOwn (1/2)) (uint ua) b
                 ∗ match k with
                   | O => EchoLinksLine.ewc_panic T v n i
                   | _ => EchoLinksLine.ewc_panic T v n (S i)
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
    { (* THE DEPOSIT: the caller's own chain at its own cursor *)
      iApply (uwrite_chain_sup N Q
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
      - (* the cursor, unmoved: what the SHORT arm would hand back *)
        rewrite /Q. iFrame "Hb1 Hc".
      - iIntros (b') "%Hb'".
        assert (Hbb : b' = b).
        { pose proof (HM 0%nat ltac:(lia)) as HM0.
          cbn in HM0. rewrite HM0 in Hb'. by injection Hb'. }
        subst b'.
        iApply (EchoLinksLine.echo_panic_step T γ (S gen_id) v n i b (Q 1%nat)
                  Hb with "Hpin Hlk Hc [Hb1]").
        iIntros "Hres". rewrite /Q. iFrame "Hb1". iExact "Hres". }
    { iApply (ubytesq_of_one with "Hb2"). }
    iIntros (h' ret W cw' cs') "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hl Hb2 Hpost Hrun".
    (* THE POST: the short arm is refuted from the run the caller owns *)
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

  (* =================================================================== *)
  (*  S4  THE PROMPT AS ONE CALL, AT ANY STEP FAMILY                      *)
  (*                                                                     *)
  (*  [UShOut.ksh_w_of_link_prompt] proved for the loose family with the  *)
  (*  step baked in; the call itself does not care which family the two  *)
  (*  bytes move, only that each byte has a link step.  So the chain and  *)
  (*  the call are stated once at an abstract [F] with the step as a      *)
  (*  persistent premise, and the two families below are instances.      *)
  (* =================================================================== *)
  Definition prompt_step (F : nat -> iProp Σ) : iProp Σ :=
    (□ (∀ (p : nat) (b : bv 8) (Φ : iProp Σ),
          ⌜u_prompt !! p = Some b⌝ -∗ ⌜(p < 2)%nat⌝ -∗
          F p -∗ (F (S p) -∗ Φ) -∗ out_link Uart0 (S gen_id) b Φ))%I.

  Lemma prompt_chain (F : nat -> iProp Σ) (M : gmap Z (bv 8))
      (ua : mword 64) (fb : nat -> bv 8) :
    forall (c i : nat),
    (i + c <= 2)%nat ->
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       u_prompt !! j = Some (fb j)) ->
    (forall j : nat, (i <= j)%nat -> (j < i + c)%nat ->
       M !! uint (add_vec_int ua (Z.of_nat j)) = Some (fb j)) ->
    prompt_step F -∗
    F i -∗
    cons_out_chain (S gen_id) M ua F i c.
  Proof.
    intros c. induction c as [| c IH]; intros i Hle Hline HM.
    - iIntros "_ Hc". cbn [cons_out_chain]. iExact "Hc".
    - iIntros "#Hst Hc". cbn [cons_out_chain]. iSplit.
      + iExact "Hc".
      + iIntros (b) "%Hbm".
        assert (Hbb : b = fb i).
        { rewrite (HM i ltac:(lia) ltac:(lia)) in Hbm. by injection Hbm. }
        subst b.
        iApply ("Hst" $! i (fb i) _ with "[%] [%] Hc").
        { exact (Hline i ltac:(lia) ltac:(lia)). }
        { lia. }
        iIntros "Hc".
        iApply (IH (S i) ltac:(lia)
                  ltac:(intros j H1 H2; apply Hline; lia)
                  ltac:(intros j H1 H2; apply HM; lia) with "Hst Hc").
  Qed.

  (* THE CALL: [write(2, "$ ", 2)], paid by two link steps and answered on
     the ONE ledger row it asks for -- [UShOut.ksh_w_of_link_prompt]'s
     proof at [F]. *)
  Lemma ksh_w_of_link_prompt_fam (N : uk_names Σ) (F : nat -> iProp Σ)
      (l : list fdstate) (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    prompt_step F -∗
    shk_rodata (ukn_t N) -∗
    UkSh.ksh_w N (mword_of_int 2 : mword 64)
      (mword_of_int sh_prompt_pv) 2%nat
      (UserFd.ustd (ukn_fd N) l ∗ F 0%nat)
      (UserFd.ustd (ukn_fd N) l ∗ F 2%nat).
  Proof.
    intros Hl2.
    iIntros "#Hst #Hro" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
    assert (Hua : uint (m !!! Regidx a1_idx) = sh_prompt_pv)
      by (rewrite Ha1; apply uint_moi; unfold UkSh.sh_prompt_pv, Z64; lia).
    (* the two keys the console chain is indexed by, as plain addresses:
       the buffer is a .rodata literal at 0x1280, so neither add wraps *)
    assert (Havi0 : uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat 0))
                    = sh_prompt_pv).
    { assert (Hhi : uint (m !!! Regidx a1_idx) + Z.of_nat 0
                    < 18446744073709551616)
        by (rewrite Hua; unfold UkSh.sh_prompt_pv; lia).
      rewrite (uint_avi_small (m !!! Regidx a1_idx) (Z.of_nat 0)
                 ltac:(lia) Hhi).
      rewrite Hua. lia. }
    assert (Havi1 : uint (add_vec_int (m !!! Regidx a1_idx) (Z.of_nat 1))
                    = (sh_prompt_pv + 1)%Z).
    { assert (Hhi : uint (m !!! Regidx a1_idx) + Z.of_nat 1
                    < 18446744073709551616)
        by (rewrite Hua; unfold UkSh.sh_prompt_pv; lia).
      rewrite (uint_avi_small (m !!! Regidx a1_idx) (Z.of_nat 1)
                 ltac:(lia) Hhi).
      rewrite Hua. lia. }
    (* the two literal bytes, off sh's own .rodata *)
    iAssert (utext (ukn_t N) sh_prompt_pv sh_dollar_b) as "#Hb0".
    { iApply (UShOut.shk_rodata_byte (ukn_t N) sh_prompt_pv sh_dollar_b
                sh_dollar_ro with "Hro"). }
    iAssert (utext (ukn_t N) (sh_prompt_pv + 1)%Z sh_space_b) as "#Hb1".
    { iApply (UShOut.shk_rodata_byte (ukn_t N) (sh_prompt_pv + 1)%Z sh_space_b
                sh_space_ro with "Hro"). }
    iAssert ([∗ list] j ∈ seq 0 2%nat,
               utext (ukn_t N) (uint (m !!! Regidx a1_idx) + Z.of_nat j)%Z
                 (u_prompt !!! j))%I as "#Hbs".
    { rewrite Hua. cbn [seq]. rewrite big_sepL_cons big_sepL_singleton.
      iSplitL.
      - rewrite Z.add_0_r.
        replace (u_prompt !!! 0%nat) with sh_dollar_b
          by (vm_compute; reflexivity).
        iExact "Hb0".
      - replace (u_prompt !!! 1%nat) with sh_space_b
          by (vm_compute; reflexivity).
        replace (sh_prompt_pv + Z.of_nat 1)%Z with (sh_prompt_pv + 1)%Z by lia.
        iExact "Hb1". }
    assert (Ham1 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a1_idx = m !!! Regidx a1_idx)
      by exact (upd_ne m (Regidx a7_idx) (Regidx a1_idx) _
                  ltac:(vm_compute; discriminate)).
    assert (Ham0 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a0_idx = (mword_of_int 2 : mword 64)).
    { rewrite <- Ha0.
      exact (upd_ne m (Regidx a7_idx) (Regidx a0_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Ham2 : (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                     !!! Regidx a2_idx
                   = (mword_of_int (Z.of_nat 2%nat) : mword 64)).
    { rewrite <- Ha2.
      exact (upd_ne m (Regidx a7_idx) (Regidx a2_idx) _
               ltac:(vm_compute; discriminate)). }
    assert (Hi0 : bv_signed (trunc32
                    ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                       !!! Regidx a0_idx)) = Z.of_nat 2)
      by (rewrite Ham0; vm_compute; reflexivity).
    assert (Hcnt : Z.to_nat (sys_rw_count
                     ((<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                        !!! Regidx a2_idx)) = 2%nat)
      by (rewrite Ham2 sh_count2; lia).
    iApply (UkSh.wp_ksh_write_chain_txt N h m avail
              (UShOut.ksh_fam N F) l
              2%nat (fun j : nat => u_prompt !!! j)
              with "Hcode Hrun [Hc] Hstd Hbs").
    { (* THE DEPOSIT: sh's own chain at its own cursor *)
      iApply (uwrite_chain_sup N F
                (<[Regidx a7_idx := (mword_of_int 16 : mword 64)]> m)
                (add_vec_int (mword_of_int ShSyms.write : mword 64) 2)
                l 2%nat rb CONSOLE Hi0 ltac:(unfold NSTD; lia) Hl2).
      iIntros (M pm sz) "Hheap".
      iDestruct (uheap_text (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   sh_prompt_pv sh_dollar_b with "Hheap Hb0") as %(HM0 & _ & _).
      iDestruct (uheap_text (ukn_t N) (ukn_d N) (ukn_s N) M pm sz
                   (sh_prompt_pv + 1)%Z sh_space_b
                   with "Hheap Hb1") as %(HM1 & _ & _).
      iFrame "Hheap".
      (* the two keys the chain is indexed by, as plain addresses *)
      rewrite Ham1 Hcnt.
      iApply (prompt_chain F M (m !!! Regidx a1_idx)
                (fun j : nat => u_prompt !!! j) 2%nat 0%nat ltac:(lia)
                ltac:(intros j _ Hj;
                      destruct j as [| [| j]];
                      [ vm_compute; reflexivity
                      | vm_compute; reflexivity
                      | exfalso; lia ])
                ltac:(intros j _ Hj;
                      destruct j as [| [| j]];
                      [ rewrite Havi0 HM0; vm_compute; reflexivity
                      | rewrite Havi1 HM1; vm_compute; reflexivity
                      | exfalso; lia ])
                with "Hst Hc"). }
    iIntros (h' ret W cw' cs')
      "%Hka0 %Hka1 %Hka2 %Htk %Hlz %Hnf Hstd Hpost Hrun".
    iDestruct (uwrite_no_short F
                 (ukn_pay N) W ret (uvis_M W) (uvis_fd W)
                 cw' cs' l 2%nat rb 2%nat
                 ltac:(rewrite Hka0 Ha0; vm_compute; reflexivity)
                 ltac:(unfold NSTD; lia) Htk Hl2
                 ltac:(rewrite Hka2 Ha2; exact sh_count2)
                 Hlz
                 ltac:(rewrite Hka1; exact Hnf)
                 with "Hpost") as "[_ HQ]".
    iApply ("Hcont" $! h' ret with "[$Hstd $HQ] Hrun").
  Qed.

  (* ---- the step at the widened boundary, [EchoLinksLine.ewc_lpr] ---- *)
  Lemma prompt_step_lpr (v : era_pins) (n : nat) :
    era_pin γ (S gen_id) v -∗ echo_links T γ -∗
    prompt_step (fun p : nat => EchoLinksLine.ewc_lpr T v n p).
  Proof.
    iIntros "#Hpin #Hlk". rewrite /prompt_step.
    iIntros "!>" (p b Φ) "%Hb %Hp Hc HΦ".
    iApply (EchoLinksLine.ewc_lpr_step T γ (S gen_id) v n p b Φ Hb Hp
              with "Hpin Hlk Hc HΦ").
  Qed.

  (* =================================================================== *)
  (*  S5  THE PROMPT AFTER A CHILD: from the block written up to its       *)
  (*      prompt to the settled round, as one call                        *)
  (* =================================================================== *)
  Lemma ksh_w_of_link_prompt_post (N : uk_names Σ) (v : era_pins) (n a : nat)
      (l : list fdstate) (rb : bool) :
    (a < 3)%nat ->
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    era_pin γ (S gen_id) v -∗
    echo_links T γ -∗
    shk_rodata (ukn_t N) -∗
    UkSh.ksh_w N (mword_of_int 2 : mword 64)
      (mword_of_int sh_prompt_pv) 2%nat
      (UserFd.ustd (ukn_fd N) l ∗ EchoLinksLine.ewc_post T v n a)
      (UserFd.ustd (ukn_fd N) l ∗ EchoLinksLine.ewc_open_t T v n).
  Proof.
    intros Ha Hl2. iIntros "#Hpin #Hlk #Hro" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
    iDestruct (prompt_step_lpr v n with "Hpin Hlk") as "#Hst".
    iApply (ksh_w_of_link_prompt_fam N
              (fun p : nat => EchoLinksLine.ewc_lpr T v n p) l rb Hl2
              with "Hst Hro [%] [%] [%] Hcode [$Hstd Hc] Hrun Hcont");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    cbn [EchoLinksLine.ewc_lpr].
    iApply (EchoLinksLine.ewc_line_of_post T v n a Ha with "Hc").
  Qed.

  (* =================================================================== *)
  (*  S6  THE SAME CALL AT THE LOOP'S OWN CREDENTIAL, WIDENED             *)
  (*      ([UShOut.ksh_w_of_link_cred] / [sh_prompt_law_holds] at         *)
  (*      [EchoLinksLine.ewc_lcred]): the era's pin travels INSIDE the    *)
  (*      credential, the call reads it out and puts it back.             *)
  (* =================================================================== *)
  Lemma ksh_w_of_link_lcred (N : uk_names Σ) (n : nat) (l : list fdstate)
      (rb : bool) :
    l !! 2%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
    echo_links T γ -∗
    shk_rodata (ukn_t N) -∗
    UkSh.ksh_w N (mword_of_int 2 : mword 64)
      (mword_of_int sh_prompt_pv) 2%nat
      (UserFd.ustd (ukn_fd N) l ∗ EchoLinksLine.ewc_lcred T γ (S gen_id) n 0%nat)
      (UserFd.ustd (ukn_fd N) l ∗ EchoLinksLine.ewc_lcred T γ (S gen_id) n 2%nat).
  Proof.
    intros Hl2. iIntros "#Hlk #Hro" (h m avail)
      "%Ha0 %Ha1 %Ha2 #Hcode [Hstd Hc] Hrun Hcont".
    rewrite /EchoLinksLine.ewc_lcred. iDestruct "Hc" as (v) "[#Hpin Hc]".
    iDestruct (prompt_step_lpr v n with "Hpin Hlk") as "#Hst".
    iApply (ksh_w_of_link_prompt_fam N
              (fun p : nat => EchoLinksLine.ewc_lpr T v n p) l rb Hl2
              with "Hst Hro [%] [%] [%] Hcode [$Hstd $Hc] Hrun [Hcont]");
      [ exact Ha0 | exact Ha1 | exact Ha2 | ].
    iIntros (h' ret) "[Hstd Hc] Hrun".
    iApply ("Hcont" $! h' ret with "[$Hstd Hc] Hrun").
    iExists v. iFrame "Hpin Hc".
  Qed.

  Lemma sh_prompt_law_holds_line :
    echo_links T γ -∗
    UShKernel.sh_prompt_law (EchoLinksLine.ewc_lcred T γ (S gen_id)).
  Proof.
    iIntros "#Hlk". rewrite /UShKernel.sh_prompt_law.
    iIntros "!>" (N) "#Hro". rewrite /UkSh.ush_prompt_law.
    iIntros "!>" (n l) "%Hfd2". destruct Hfd2 as [rb Hl2].
    iApply (ksh_w_of_link_lcred N n l rb Hl2 with "Hlk Hro").
  Qed.

End UShPanic.
