(* ===================================================================== *)
(*  UCatLend.v -- what the file application lends cat and what cat owes   *)
(*  back, plus the three count helpers the pipeline's cat round reads.    *)
(*                                                                       *)
(*  RELOCATED from [UCatKernel.v] by the file sweep (program-specs        *)
(*  SS3.4g): that file's per-program payers are dead since the round's    *)
(*  children run from the tree route ([UkFileEntries]), and these five    *)
(*  are all that live code still names.  [catq_cat] and [cat_lend] are    *)
(*  read by [UkFileEntries], [UkFileIface] and [UShRound]; [cat_count_is], *)
(*  [cat_moi_uint] and [cat_fam] by [UShPipeCatRound].                    *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_map ghost_var invariants mono_nat own.
From iris.algebra.lib Require Import mono_list.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras RiscvModelBytes.
Require Import RegFile.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunSys.
Require Import VcGen.              (* [trunc32_subrange] -- a2 read as a C [int] *)
Require Import SpecSysRead.        (* [sys_rw_count] *)
Require Import UkWriteLeaf.        (* [xfam_wr] *)
Require Import FdSlots ProcGeom UserFd UserCwd.
Require Import UexecSG.            (* [sfam] *)
Require Import AppCfg AppInv AppFile FileOpen FsCfg FsImgCheck.
Require Import Xv6Cameras Xv6G IrefSlots ProcAvail FileInvDefs.
Require Import LineWords EchoDisc.
Require Import FileState FileDisc FileOut.
Require Import EchoOut AppEcho.
Require Import UCatOut.
Require Import CtxIdDefs.
Import Defs.

Local Open Scope Z_scope.

Section UCatCount.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (N : uk_names Σ).

  (* the syscall's count register, read as the C [int] it is.  The same
     reading as [UEchoOut.echo_count_is] and [UShOut]'s, at the WORD
     rather than at a [nat]: the payer may not compute the count from the
     walk's [nb] (above 2^64 the equation [ret = mword_of_int nb] does not
     identify it), so everything below reads it off [bv_unsigned].  Its
     home is [SpecSysRead.v], whose cone is the whole read/write tower. *)
  Lemma cat_count_is (nb : nat) :
    (Z.of_nat nb < 2 ^ 31)%Z ->
    sys_rw_count (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb.
  Proof using .
    intros Hlt. change (2 ^ 31)%Z with 2147483648%Z in Hlt.
    assert (Hu : uint (mword_of_int (Z.of_nat nb) : mword 64) = Z.of_nat nb)
      by (apply uint_moi; unfold Z64; lia).
    rewrite uint_unsigned in Hu.
    rewrite /sys_rw_count. unfold bv_signed.
    rewrite trunc32_subrange subrange_31_0_unsigned Hu.
    rewrite (Z.mod_small (Z.of_nat nb) 4294967296); [| lia].
    assert (Hhm : bv_half_modulus 32 = 2147483648) by (vm_compute; reflexivity).
    rewrite bv_swrap_small; [ reflexivity | rewrite Hhm; lia ].
  Qed.

  (* ...and a word IS the machine integer of its own unsigned value, which
     is how the count the payer reads off the word gets back into the
     [mword_of_int] shape the walk's equation is stated at. *)
  Lemma cat_moi_uint (v : mword 64) :
    (mword_of_int (bv_unsigned v) : mword 64) = v.
  Proof using . rewrite <- uint_unsigned. apply moi_of_uint. Qed.

  (* the deposit family row 16 is read at, at cat's own cursor
     ([UEchoOut.kec_fam]'s mould: an [xfam]-typed argument is not an
     [sfam] until the instance is fixed) *)
  Definition cat_fam (Q : nat -> iProp Σ) : sfam := xfam_wr Q (ukn_pay N).
End UCatCount.

Section UCatLend.
  Context `{HRg : !riscvGS Σ}.
  Context `{!xv6G Σ, !bioslotG Σ, !fdslotG Σ, !fileG Σ,
            !irefslotG Σ, !pavG Σ, !wchG Σ, !ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!echoOutG Σ, !inG Σ (mono_listR (leibnizO Z)), !fileAppG Σ,
            !fileOutG Σ}.
  Context (g : file_gn).

  (* THE PAYLOAD SH IS OWED, as a DISJUNCTION of the two alternatives
     cat's round can file.  [UCatOut]'s header says it in words already:
     an ABSENT deed and a CONTENT round file [RCRan], a PRESENT file
     whose open returned [-1] files [RCNoOpen], and WHICH ONE is read off
     the deed -- which the entry cannot know, because the open's own
     return decides it.  So what crosses the exit is one of the two,
     and both disjuncts are [UCatOut.catq_filed] at CAT'S OWN END CURSOR
     ([UCatOut.cat_out_len]: [length bs] at [RCRan] with a present deed,
     NINETEEN at [RCRan] with an absent one and at [RCNoOpen] always). *)
  (* ...AND IT RETURNS WHAT SH LENT (RULING CAT-DEED, amended 2026-09-21):
     ONE fraction of `f`'s ghost state goes in ([cat_lend]) and THE SAME
     fraction, at the same value, comes out -- cat only reads -- or the
     application is out of spec.  The split the open needs (one piece on
     the path walk, one on the final observation) is cat's own business
     and does not show here. *)
  Definition catq_cat (c : file_fixed) (r : file_names) (q : Qp) (s : dst)
      (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
    : Z -> iProp Σ :=
    fun _ =>
      ((UCatOut.catq_filed g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P (-1)
        ∨ UCatOut.catq_filed g v vf ps0 cs0 s0 I0 (ralt_enc RCNoOpen) P (-1))
       ∗ (fdq r q s ∨ file_taint c))%I.

  (* WHAT SH LENDS cat (RULING CAT-DEED, amended 2026-09-21): ONE fraction
     of `f`'s ghost state, at whatever state `f` is in, and the era's
     console cursor at the round's own start.  Nothing else: the laws cat's
     open and read run on are cat's own. *)
  Definition cat_lend (r : file_names) (q : Qp) (s : dst)
      (v : era_pins) (vf : file_era)
      (ps0 cs0 : list nat) (s0 : fstate) (I0 : list (bv 8)) (P : nat)
    : iProp Σ :=
    (fdq r q s
     ∗ UCatOut.cch g v vf ps0 cs0 s0 I0 (ralt_enc RCRan) P 0%nat)%I.

End UCatLend.
