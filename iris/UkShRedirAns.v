(* ===================================================================== *)
(* UkShRedirAns.v -- sh's open STUB SHAPE WITH A -1 PAYLOAD (lane        *)
(* F-OPEN-2, deliverable 3; the one thing lane SH-ROUND needs first).     *)
(*                                                                       *)
(* Lane F-OPEN's finding, restated: [UkShRedir.ush_open_ans]'s [-1] arm   *)
(* carries NO application payload -- it is [r = -1] beside the ledger,    *)
(* while its fd arm carries [K ty].  The FILE application's              *)
(* open(f, O_WRONLY|O_CREATE|O_TRUNC) has THREE outcomes, not two:        *)
(*                                                                       *)
(*   fd 1, the deed at [Some (i, [])]            -- the create fired and  *)
(*                                                  the descriptor landed *)
(*   -1,   the deed UNCHANGED                    -- the walk or the       *)
(*                                                  create failed         *)
(*   -1,   the deed at [Some (i, [])]            -- the create FIRED and  *)
(*                                                  [filealloc] failed    *)
(*                                                  past it               *)
(*                                                                       *)
(* The third is not a hypothetical: it is                                 *)
(* [SpecSysOpen.open_post_fail_create]'s arm (a), and the fs mutation of  *)
(* a failed open is real -- so a redirect whose [-1] arm carries nothing  *)
(* DROPS THE DEED on a path the kernel spec says is reachable, and the    *)
(* child can never hand it back to sh at [exit].                          *)
(*                                                                       *)
(* WHY THIS IS A NEW FILE AND NOT A DEFINITION BESIDE THE LANDED ONE.     *)
(* [iris/UkShRedir.v] lives on branch app-file/sh-redir, which lane       *)
(* SH-PARSE-2 had checked out and dirty while this lane ran, and the      *)
(* brief's own fallback is this file.  The definitions below are          *)
(* therefore stated FROM SCRATCH rather than as a wrapper: they are       *)
(* [ush_open_ans] / [ush_open_call] with one extra parameter, and the     *)
(* lane that merges the two branches should MOVE them next to their       *)
(* twins (or replace the twins outright -- at [Kf := emp] the two are     *)
(* the same proposition, which is why no consumer of the landed pair      *)
(* loses anything).                                                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UsysMemOk.
Require Import UexecSG.
Require Import UserHeap UkRun UkRunLeaf UkRunMem UkRunSys UkRunBr.
Require Import UCodeShK.
Require Import CtxIdDefs.
Require User.ShSyms.
Require Import FdSlots UserFd.
Require Import ChildTok.
Require Import UserCwd.
Local Open Scope Z_scope.
Import Defs.

Section UkShRedirAns.
  (* [UkShRedir]'s binder list verbatim, so the two pairs are typed in the
     same scope when a merge lane brings them together. *)
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).

  (* ------------------------------------------------------------------ *)
  (*  1.  THE ANSWER, WITH BOTH PAYLOADS                                  *)
  (* ------------------------------------------------------------------ *)

  (* [K ty] is what the fd arm hands the application -- the receipt at the
     descriptor's TYPE, which is where the file lane parks its moved deed
     ([FileOpen.file_open_create_au]'s second receipt arm, instantiated as
     [K ty := ∃ i γo, ⌜ty = FdInode i γo OffParked⌝ ∗ fown r (Some (i, []))]).

     [Kf] is what the [-1] arm hands it, and it is NOT [emp] for this
     application: the create may have fired before [filealloc] failed, so
     the honest instance is the DISJUNCTION
     [Kf := fown r s ∨ ∃ i, fown r (Some (i, []))].  A caller that does not
     move anything takes [Kf := emp] and gets exactly the landed shape. *)
  Definition ush_open_ans2 (N : uk_names Σ) (l : list fdstate)
      (K : fdtype -> iProp Σ) (Kf : iProp Σ) (r : mword 64) : iProp Σ :=
    ((∃ ty : fdtype,
        ⌜ r = (mword_of_int 1 : mword 64) ⌝ ∗
        UserFd.ustd (ukn_fd N) (<[1%nat := FdOpen false true ty]> l) ∗ K ty)
     ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗
        UserFd.ustd (ukn_fd N) l ∗ Kf))%I.

  (* ...AND THE CALL.  [ShSyms.open]'s entry pc in, the stub's return
     address out; the cwd crosses unchanged (open does not move it) and is
     what an application's bundle is stated at
     ([UkRunSys.wp_uk_ecall_open_recv_img]). *)
  Definition ush_open_call2 (N : uk_names Σ) (cwdv file mode : Z)
      (l : list fdstate) (K : fdtype -> iProp Σ) (Kf : iProp Σ) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (av : nat),
       ⌜ m !!! Regidx a0_idx = (mword_of_int file : mword 64) ⌝ -∗
       ⌜ m !!! Regidx a1_idx = (mword_of_int mode : mword 64) ⌝ -∗
       shk_code (ukn_t N) -∗
       UserCwd.ucwd (ukn_cwd N) cwdv -∗
       UserFd.ustd (ukn_fd N) l -∗
       urun N h m (mword_of_int User.ShSyms.open) av -∗
       (∀ (h' : CpuId) (m' : regfile) (r : mword 64),
          ⌜ ucallee_saved m m' ⌝ -∗
          ⌜ m' !!! Regidx a0_idx = r ⌝ -∗
          UserCwd.ucwd (ukn_cwd N) cwdv -∗
          ush_open_ans2 N l K Kf r -∗
          urun N h' m' (ret_pc (m !!! Regidx ra_idx)) av -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* ------------------------------------------------------------------ *)
  (*  2.  THE TWO MOVES A CONSUMER NEEDS                                  *)
  (* ------------------------------------------------------------------ *)

  (* THE PAYLOAD IS MONOTONE in both slots, so a supplier that proves a
     STRONGER answer serves a weaker consumer; this is what lets sh's walk
     stay stated at whatever the application hands it. *)
  Lemma ush_open_ans2_mono (N : uk_names Σ) (l : list fdstate)
      (K K' : fdtype -> iProp Σ) (Kf Kf' : iProp Σ) (r : mword 64) :
    (∀ ty : fdtype, K ty -∗ K' ty) -∗ (Kf -∗ Kf') -∗
    ush_open_ans2 N l K Kf r -∗ ush_open_ans2 N l K' Kf' r.
  Proof using .
    iIntros "HK HF H". rewrite /ush_open_ans2.
    iDestruct "H" as "[Hfd | Hm1]".
    - iDestruct "Hfd" as (ty) "(%Hr & Hstd & Hk)".
      iLeft. iExists ty. iSplitR; [ by iPureIntro | ]. iFrame "Hstd".
      iApply ("HK" with "Hk").
    - iDestruct "Hm1" as "(%Hr & Hstd & Hk)".
      iRight. iSplitR; [ by iPureIntro | ]. iFrame "Hstd".
      iApply ("HF" with "Hk").
  Qed.

  (* ...AND THE LEDGER, READ WITHOUT THE PAYLOAD: what a caller that only
     wants to know which descriptor it has gets.  [ush_open_ans] (the
     landed pair, on branch app-file/sh-redir) is exactly this at
     [Kf := emp]; the move below is the one a merge lane takes to show
     nothing was lost. *)
  Lemma ush_open_ans2_drop (N : uk_names Σ) (l : list fdstate)
      (K : fdtype -> iProp Σ) (Kf : iProp Σ) (r : mword 64) :
    ush_open_ans2 N l K Kf r -∗
      ((∃ ty : fdtype,
          ⌜ r = (mword_of_int 1 : mword 64) ⌝ ∗
          UserFd.ustd (ukn_fd N) (<[1%nat := FdOpen false true ty]> l) ∗ K ty)
       ∨ (⌜ r = (mword_of_int (-1) : mword 64) ⌝ ∗
          UserFd.ustd (ukn_fd N) l)).
  Proof using .
    rewrite /ush_open_ans2. iIntros "[Hfd | (%Hr & Hstd & _)]".
    - iLeft. iExact "Hfd".
    - iRight. iSplitR; [ by iPureIntro | ]. iExact "Hstd".
  Qed.

End UkShRedirAns.
