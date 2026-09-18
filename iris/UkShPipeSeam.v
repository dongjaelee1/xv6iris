(* ===================================================================== *)
(* UkShPipeSeam.v -- THE PIPE NODE BECOMES THE RUNNER'S TREE,             *)
(* lane SH-PARSE-PIPE (design/app-pipe.md SS5.1: the node catalogue        *)
(* [UkShRun.ush_cmd g t (UPipe (UExec l) (UExec r))] built from the two    *)
(* EXEC nodes).                                                           *)
(*                                                                        *)
(* [UkShMain.ush_cmd_of_ushp_gen] is the EXEC conversion at what it        *)
(* actually needs -- the line ALREADY PERSISTED plus three facts about it  *)
(* (each token is inside the line, its END byte is zero, no byte of its    *)
(* BODY is) -- and being stated that way is exactly what lets this file    *)
(* call it TWICE on one line, once per side of the pipe.  So the PIPE      *)
(* conversion is forty lines and no new mathematics:                       *)
(*                                                                        *)
(*   - the type word and the two child pointers are DISCARDED here (that   *)
(*     is what makes the runner's tree persistent, hence what lets it      *)
(*     cross sh's two forks as a payload -- [UkShRun.ush_cmd_forkable]);   *)
(*   - the node's address bound [p < 2 ^ 38] is read off the RUN's own     *)
(*     heap, as the EXEC conversion reads it, not assumed;                 *)
(*   - the two [ush_args] lists are cut from THE SAME line [g], which is   *)
(*     what [UkShPipeParse.wp_kshp_nulterminate_pipe] leaves behind        *)
(*     ([ushp_nulfold toksr (ushp_nulfold toksl g)]), so the caller hands  *)
(*     one line and gets both commands.                                    *)
(*                                                                        *)
(* This is a LEAF and it is the node lane SH-PIPE consumes: everything     *)
(* above it (parseexec at the pipe line, parsepipe's turn, the parser      *)
(* theorem) is reported, not landed.                                      *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseCmd.
Require Import UkShRun.
Require Import UkShMain.
Require Import UkShPipeParse.
Require Import UexecSG.
Local Open Scope Z_scope.
Import Defs.

Section UkShPipeSeam.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation ushp_tree := (UkShParse.ushp_tree N).
  Local Notation ushp_pipe_node := (UkShPipeParse.ushp_pipe_node N).
  Local Notation ush_args := (UkShMain.ush_args).
  Local Notation ush_cmd_of_ushp_gen := (UkShMain.ush_cmd_of_ushp_gen N).
  Local Notation ubytes_persist := (UkShMain.ubytes_persist).
  Local Notation uword_persist := (UkShMain.uword_persist).
  Local Notation urun_ubytes_bnd := (UkShMain.urun_ubytes_bnd N).

  (* the three facts the EXEC conversion needs about ONE token list in the
     line, named once so the statement below reads *)
  Definition ushq_cut_ok (len : nat) (g : nat -> bv 8)
      (toks : list (nat * nat)) : Prop :=
    (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
       (fst tk < snd tk)%nat /\ (snd tk <= len)%nat)
    /\ (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
          g (snd tk) = ubyte0)
    /\ (forall (i : nat) (tk : nat * nat), toks !! i = Some tk ->
          forall j : nat, (j < snd tk - fst tk)%nat ->
            g (fst tk + j)%nat <> ubyte0).

  Lemma ush_cmd_of_ushp_pipe (h : CpuId) (m : regfile) (pc : mword 64)
      (avail : nat) (s0 p pl pr : Z) (len : nat) (g : nat -> bv 8)
      (toksl toksr : list (nat * nat)) :
    ushq_cut_ok len g toksl ->
    ushq_cut_ok len g toksr ->
    Z.of_nat len < 2 ^ 31 ->
    0 < s0 -> s0 + Z.of_nat len < 2 ^ 38 ->
    urun N h m pc avail -∗
    ushp_pipe_node p pl pr -∗
    ushp_tree s0 pl (UshpExec toksl) -∗
    ushp_tree s0 pr (UshpExec toksr) -∗
    ubytesq γd DfracDiscarded s0 (S len) g ==∗
    urun N h m pc avail ∗
    ush_cmd γd p (UPipe (UExec (ush_args s0 g toksl))
                        (UExec (ush_args s0 g toksr))).
  Proof using .
    intros (Hinl & Hendl & Hbodl) (Hinr & Hendr & Hbodr) Hlen31 Hs0 Hs0hi.
    iIntros "Hrun Hn Hl Hr #Hline".
    rewrite /UkShPipeParse.ushp_pipe_node.
    iDestruct "Hn" as "(%Hp0 & %Hp8 & %Hpz & [Hty _] & Hleft & Hright)".
    iDestruct (urun_ubytes_bnd h m pc avail p 4
                 (nth_byte (mword_of_int 3 : mword 32))
                 with "Hrun Hty") as %Hpb.
    assert (Hp : 0 < p < 2 ^ 38).
    { split; [ exact Hp0 | ].
      destruct (Hpb 0%nat ltac:(lia)) as [_ Hhi]. lia. }
    iMod (ubytes_persist γd p 4 (nth_byte (mword_of_int 3 : mword 32))
            with "Hty") as "#Hty".
    iMod (uword_persist γd (p + 8) (mword_of_int pl) with "Hleft")
      as "#Hleft".
    iMod (uword_persist γd (p + 16) (mword_of_int pr) with "Hright")
      as "#Hright".
    iMod (ush_cmd_of_ushp_gen h m pc avail s0 pl len g toksl
            Hinl Hendl Hbodl Hlen31 Hs0 Hs0hi with "Hrun Hl Hline")
      as "[Hrun #Hcl]".
    iMod (ush_cmd_of_ushp_gen h m pc avail s0 pr len g toksr
            Hinr Hendr Hbodr Hlen31 Hs0 Hs0hi with "Hrun Hr Hline")
      as "[Hrun #Hcr]".
    iModIntro. iFrame "Hrun".
    cbn [ush_cmd ush_ty].
    iSplitR; [ iPureIntro; exact Hp | ].
    iSplitR; [ iPureIntro; exact Hp8 | ].
    iSplitR; [ rewrite /ush_w32; iExact "Hty" | ].
    iSplitL.
    - iExists pl. rewrite /ush_ptr. iFrame "Hleft Hcl".
    - iExists pr. rewrite /ush_ptr. iFrame "Hright Hcr".
  Qed.

End UkShPipeSeam.
