(* ===================================================================== *)
(* UkStub.v -- THE SYSCALL STUB, ONCE: user/usys.S puts the same three     *)
(* instructions in every binary,                                          *)
(*                                                                        *)
(*      c.li  a7, NUM                                                     *)
(*      ecall                                                             *)
(*      c.jr  ra                                                          *)
(*                                                                        *)
(* at that binary's addresses, and every landed program proof walks them  *)
(* per program AND per leaf ([UkEcho.wp_kecho_write_chain] and its [_txt] *)
(* twin, [UkCat.wp_kcat_read], ...).  A HANDLER of the tree payment       *)
(* (design/program-specs.md SS3.4) funds a hole that starts at the stub's  *)
(* entry and ends at its return, running the ecall leaf of ITS choice in  *)
(* between -- so what it needs is the stub with the ecall abstracted:     *)
(*                                                                        *)
(*   [stub_law code num addr]: from the entry with the code, reach the     *)
(*   ecall with a7 = NUM (the caller is handed the ecall's instruction     *)
(*   fact and the run there, and hands back the run after it, a0 = the    *)
(*   answer), and the stub returns to [ret_pc ra] with that register file. *)
(*                                                                        *)
(* [stub_run] proves it from the three instruction facts at any address   *)
(* and number, with the successor pcs and the a7 value as EQUATIONS the   *)
(* instance discharges by computation; the seven instances at the end    *)
(* (echo's two stubs, cat's five) are one line each.  The exit stub has   *)
(* no return.                                                             *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys.
Require Import FdSlots UserFd.
Require Import UCodeEcho UCodeCat.
Require Import CtxIdDefs.
Require Import ChildTok.
Require Import UexecSlot UexecRet UexecSG.
Require User.EchoSyms User.CatSyms.
Local Open Scope Z_scope.
Import Defs.

Section UkStub.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Context (N : uk_names Σ).

  Local Notation γt := (ukn_t N).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a7_idx := (mword_of_int 17 : mword 5).

  (* the register file at the stub's return *)
  Definition stub_ret (m : regfile) (num : Z) (ret : mword 64) : regfile :=
    <[Regidx a0_idx := ret]> (<[Regidx a7_idx := (mword_of_int num : mword 64)]> m).

  (* ------------------------------------------------------------------- *)
  (*  1.  the law a handler uses                                          *)
  (* ------------------------------------------------------------------- *)

  Definition stub_law (code : iProp Σ) (num addr : Z) : iProp Σ :=
    (□ ∀ (h : CpuId) (m : regfile) (avail : nat),
       code -∗
       urun N h m (mword_of_int addr) avail -∗
       (∀ h1 : CpuId,
          uinstr_is γt (mword_of_int (addr + 2)) false (ECALL tt) -∗
          urun N h1 (<[Regidx a7_idx := (mword_of_int num : mword 64)]> m)
            (mword_of_int (addr + 2)) avail -∗
          (∀ (h2 : CpuId) (ret : mword 64),
             urun N h2 (stub_ret m num ret) (mword_of_int (addr + 6)) avail -∗
             mWP (Loop : expr riscv_lang)) -∗
          mWP (Loop : expr riscv_lang)) -∗
       (∀ (h3 : CpuId) (ret : mword 64),
          urun N h3 (stub_ret m num ret) (ret_pc (m !!! Regidx ra_idx)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* the exit stub never returns *)
  Definition exit_stub_law (code : iProp Σ) (addr : Z) : iProp Σ :=
    (□ ∀ (h : CpuId) (m : regfile) (avail : nat),
       code -∗
       urun N h m (mword_of_int addr) avail -∗
       (∀ h1 : CpuId,
          uinstr_is γt (mword_of_int (addr + 2)) false (ECALL tt) -∗
          urun N h1 (<[Regidx a7_idx := (mword_of_int 2 : mword 64)]> m)
            (mword_of_int (addr + 2)) avail -∗
          mWP (Loop : expr riscv_lang)) -∗
       mWP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------- *)
  (*  2.  the three instructions, once                                    *)
  (* ------------------------------------------------------------------- *)

  Lemma stub_run (code : iProp Σ) `{!Persistent code} (num addr : Z) :
    add_vec_int (mword_of_int addr : mword 64) 2 = mword_of_int (addr + 2) ->
    add_vec_int (mword_of_int (addr + 2) : mword 64) 4 = mword_of_int (addr + 6) ->
    (regval_into_reg (sign_extend' 64 (mword_of_int num : mword 6) : mword 64)
       : mword 64) = mword_of_int num ->
    □ (code -∗ uinstr_is γt (mword_of_int addr) true
                 (C_LI (mword_of_int num : mword 6, Regidx a7_idx))) -∗
    □ (code -∗ uinstr_is γt (mword_of_int (addr + 2)) false (ECALL tt)) -∗
    □ (code -∗ uinstr_is γt (mword_of_int (addr + 6)) true (C_JR (Regidx ra_idx))) -∗
    stub_law code num addr.
  Proof using .
    intros E2 E6 Ea7. iIntros "#Hli #Hec #Hjr !>" (h m avail) "#Hcode Hrun Hmid Hcont".
    iApply (wp_uk_cli N h m (mword_of_int addr) (mword_of_int num : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply ("Hli" with "Hcode"). }
    rewrite E2 Ea7. iIntros (h1) "Hrun".
    iApply ("Hmid" $! h1 with "[] Hrun").
    { iApply ("Hec" with "Hcode"). }
    iIntros (h2 ret) "Hrun".
    assert (Hra : stub_ret m num ret !!! Regidx ra_idx = m !!! Regidx ra_idx).
    { unfold stub_ret.
      exact (eq_trans
               (upd_ne _ (Regidx a0_idx) (Regidx ra_idx) ret
                  ltac:(vm_compute; discriminate))
               (upd_ne m (Regidx a7_idx) (Regidx ra_idx) (mword_of_int num : mword 64)
                  ltac:(vm_compute; discriminate))). }
    iApply (wp_uk_cjr N h2 (stub_ret m num ret) (mword_of_int (addr + 6)) ra_idx
              (ret_pc (m !!! Regidx ra_idx)) avail
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hra; reflexivity) with "[] Hrun").
    { iApply ("Hjr" with "Hcode"). }
    iIntros (h3) "Hrun".
    iApply ("Hcont" $! h3 ret with "Hrun").
  Qed.

  Lemma exit_stub_run (code : iProp Σ) `{!Persistent code} (addr : Z) :
    add_vec_int (mword_of_int addr : mword 64) 2 = mword_of_int (addr + 2) ->
    (regval_into_reg (sign_extend' 64 (mword_of_int 2 : mword 6) : mword 64)
       : mword 64) = mword_of_int 2 ->
    □ (code -∗ uinstr_is γt (mword_of_int addr) true
                 (C_LI (mword_of_int 2 : mword 6, Regidx a7_idx))) -∗
    □ (code -∗ uinstr_is γt (mword_of_int (addr + 2)) false (ECALL tt)) -∗
    exit_stub_law code addr.
  Proof using .
    intros E2 Ea7. iIntros "#Hli #Hec !>" (h m avail) "#Hcode Hrun Hmid".
    iApply (wp_uk_cli N h m (mword_of_int addr) (mword_of_int 2 : mword 6) a7_idx avail
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate) with "[] Hrun").
    { iApply ("Hli" with "Hcode"). }
    rewrite E2 Ea7. iIntros (h1) "Hrun".
    iApply ("Hmid" $! h1 with "[] Hrun").
    iApply ("Hec" with "Hcode").
  Qed.

  (* ------------------------------------------------------------------- *)
  (*  3.  the instances                                                   *)
  (* ------------------------------------------------------------------- *)

  Local Ltac stub_inst code num addr lem_li lem_ec lem_jr :=
    (iApply (stub_run code num addr
              ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
              ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
              ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity));
     [ iIntros "!> #Hc"; iApply (lem_li with "Hc")
     | iIntros "!> #Hc"; iApply (lem_ec with "Hc")
     | iIntros "!> #Hc"; iApply (lem_jr with "Hc") ]).

  Lemma echo_stub_write : ⊢ stub_law (echo_code γt) 16 EchoSyms.write.
  Proof using .
    destruct echo_syms_pins as (_ & _ & _ & _ & ->).
    stub_inst (echo_code γt) 16 0x352 uis_echo_352 uis_echo_354 uis_echo_358.
  Qed.

  Lemma echo_stub_exit : ⊢ exit_stub_law (echo_code γt) EchoSyms.exit.
  Proof using .
    destruct echo_syms_pins as (_ & _ & _ & -> & _).
    iApply (exit_stub_run (echo_code γt) 0x332
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity));
      [ iIntros "!> #Hc"; iApply (uis_echo_332 with "Hc")
      | iIntros "!> #Hc"; iApply (uis_echo_334 with "Hc") ].
  Qed.

  Lemma cat_stub_read : ⊢ stub_law (cat_code γt) 5 CatSyms.read.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (cat_code γt) 5 0x3c4 uis_cat_3c4 uis_cat_3c6 uis_cat_3ca.
  Qed.

  Lemma cat_stub_write : ⊢ stub_law (cat_code γt) 16 CatSyms.write.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (cat_code γt) 16 0x3cc uis_cat_3cc uis_cat_3ce uis_cat_3d2.
  Qed.

  Lemma cat_stub_close : ⊢ stub_law (cat_code γt) 21 CatSyms.close.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (cat_code γt) 21 0x3d4 uis_cat_3d4 uis_cat_3d6 uis_cat_3da.
  Qed.

  Lemma cat_stub_open : ⊢ stub_law (cat_code γt) 15 CatSyms.open.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & -> & _).
    stub_inst (cat_code γt) 15 0x3ec uis_cat_3ec uis_cat_3ee uis_cat_3f2.
  Qed.

  Lemma cat_stub_exit : ⊢ exit_stub_law (cat_code γt) CatSyms.exit.
  Proof using .
    destruct cat_syms_pins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ->).
    iApply (exit_stub_run (cat_code γt) 0x3ac
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity)
             ltac:(apply (proj2 (bv_eq _ _ _)); vm_compute; reflexivity));
      [ iIntros "!> #Hc"; iApply (uis_cat_3ac with "Hc")
      | iIntros "!> #Hc"; iApply (uis_cat_3ae with "Hc") ].
  Qed.

End UkStub.
