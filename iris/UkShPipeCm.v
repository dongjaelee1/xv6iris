(* ===================================================================== *)
(* UkShPipeCm.v -- parsepipe's TURN, lane SH-PARSE-PIPE part 2            *)
(* (design/app-pipe.md SS5.1: parsepipe is walked at the '>' shape         *)
(* ([UkShRedirCm.wp_kshp_parsepipe_gt]) and must turn ONCE for the pipe.)  *)
(*                                                                        *)
(* The landed walk is this one with the guard REFUTED: on a symbol-free or *)
(* a redirect line the peek for '|' answers 0 and [parsepipe] returns its  *)
(* sub-command unchanged.  The pipe line is the first line that makes it   *)
(* TURN, and the turn is THIRTEEN instructions -- 0x6c2..0x6e0 -- which    *)
(* rejoin the landed walk's own tail at 0x6b0, so the prologue, the guard, *)
(* the tail and the epilogue are all the landed text.                     *)
(*                                                                        *)
(* WHAT IS DISCHARGED HERE, of the turn's three calls:                     *)
(*                                                                        *)
(*   0x6ca [gettoken] -- [UkShPipeTok.wp_kshp_gettoken_syms] at the '|':   *)
(*     it answers 124 and leaves the cursor at [S (S gp)], the right       *)
(*     command's first byte, with BOTH out-parameters NULL (which is       *)
(*     [UkShParseTok.ushp_cell]'s left disjunct, free).                    *)
(*   0x6d2 [parsepipe] -- THE RECURSION, and it is the LANDED symbol-free  *)
(*     walk on the line's own suffix ([UkShPipeRight.                       *)
(*     wp_kshp_parsepipe_right]).  Nothing about the right-hand side of a  *)
(*     pipe needed a new walk.                                            *)
(*                                                                        *)
(* WHAT IS A CALL PREMISE (SH-REDIR's [ush_open_call] shape, §1):          *)
(*                                                                        *)
(*   0x698 [parseexec] -- the LEFT command's parse.  It is a RE-STATEMENT  *)
(*     of the landed walks at [UkShParseSym.ushs_toks] (the loop's exit is *)
(*     [UkShPipeEx.wp_kshp_pex_bar] and its last [parseredirs] is          *)
(*     [UkShPipePr.wp_kshp_parseredirs_miss], both landed by this lane);   *)
(*     this lane did not finish the ~2,400 lines of re-statement itself.   *)
(*   0x6da [pipecmd] -- its 48 instructions are in NO catalog              *)
(*     (`skipfunc pipecmd` in tools/ucode_shp.txt) and cannot be put in    *)
(*     one from this worktree: [make gen-ucode] shells out to [coqc] and   *)
(*     needs a BUILT iris/, which the lane's local tree has not got.  See  *)
(*     the lane's findings for exactly what it needs.                      *)
(*                                                                        *)
(* So the arm compiles TODAY, before either of those exists, and the lane  *)
(* that lands them instantiates two premises and nothing else.             *)
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
Require Import WpMmodeLeafBase.
Require Import WpUmodeBranch.
Require Import UmodeArith UmodeAbi.
Require Import UserHeap UkRun UkRunLeaf UkRunMem.
Require Import UCodeShP.
Require Import CtxIdDefs.
Require User.ShSyms User.ShInstrs.
Require Import ChildTok.  (* [genF] -- the capacity the slot's fork arms name *)
Local Open Scope Z_scope.
Import Defs.
Require Import UserFd.
Require Import UkShParse.
Require Import UkShParseSym.
Require Import UkShParseLex.
Require Import UkShParseTok.
Require Import UkShParseRedir.
Require Import UkShRedirLex.
Require Import UkShRedirGtk.
Require Import UkShRedirCmd.
Require Import UkShRedirPr.
Require Import UkShRedirEx.
Require Import UkShRedirPex.

Require Import UexecSG.   (* [uexecSG] / [uprogSG]: the ARM deposit class *)

Require Import UkShRedirCm.
Require Import UkShPipeLex.
Require Import UkShPipeTok.
Require Import UkShPipeParse.
Require Import UkShPipeEx.
Require Import UkShPipeCmd.
Require Import UkShPipePex.
Require Import UkShPipeRight.

Section UkShPipeCm.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  (* ...and the children set's ([Xv6Cameras.uchG]), which [UkRun.urun]
     carries beside the cwd's *)
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  (* THIS PROGRAM'S EXIT OWES ITS PARENT NOTHING at this lane, as a
     CLASS so that it reaches the exit ecall without an argument at every
     call site ([UkRun.ukn_const]). *)
  Context `{Hpay : !ukn_const N}.
  (* the fields, under the names the engine has always used *)
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  (* [ChildTok.ctokG]: the slot's fork arms name the generation's pieces,
     and this file binds no whole-system bundle. *)
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.

  Local Notation x0_idx := (mword_of_int 0 : mword 5).
  Local Notation ra_idx := (mword_of_int 1 : mword 5).
  Local Notation s0_idx := (mword_of_int 8 : mword 5).
  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a0_idx := (mword_of_int 10 : mword 5).
  Local Notation a1_idx := (mword_of_int 11 : mword 5).
  Local Notation a2_idx := (mword_of_int 12 : mword 5).
  Local Notation a3_idx := (mword_of_int 13 : mword 5).
  Local Notation a4_idx := (mword_of_int 14 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation s2_idx := (mword_of_int 18 : mword 5).
  Local Notation s3_idx := (mword_of_int 19 : mword 5).
  Local Notation s4_idx := (mword_of_int 20 : mword 5).
  Local Notation s5_idx := (mword_of_int 21 : mword 5).
  Local Notation s6_idx := (mword_of_int 22 : mword 5).
  Local Notation s7_idx := (mword_of_int 23 : mword 5).
  Local Notation s8_idx := (mword_of_int 24 : mword 5).
  Local Notation s9_idx := (mword_of_int 25 : mword 5).
  Local Notation s10_idx := (mword_of_int 26 : mword 5).
  Local Notation s11_idx := (mword_of_int 27 : mword 5).


(*ALIASES-BEGIN*)
  (* ---- what the earlier files of the parser define, at this
         file's own ghost names.  Everything else they export is a
         PURE constant and comes in with the [Require Import]. ---- *)
  Local Notation urun_x0 := (UkShParse.urun_x0 N).
  Local Notation ushp_exec_at := (UkShParse.ushp_exec_at N).
  Local Notation ushp_exec_pre := (UkShParse.ushp_exec_pre N).
  Local Notation ushp_exec_pre_at := (UkShParse.ushp_exec_pre_at N).
  Local Notation ushp_frame_join := (UkShParse.ushp_frame_join N).
  Local Notation ushp_frame_split := (UkShParse.ushp_frame_split N).
  Local Notation ushp_lit_str := (UkShParseLex.ushp_lit_str N).
  Local Notation ushp_malloc_ty := (UkShParse.ushp_malloc_ty_le N 168).
  Local Notation ushp_slots_cap := (UkShParse.ushp_slots_cap N).
  Local Notation ushp_slots_upd := (UkShParse.ushp_slots_upd N).
  Local Notation ushp_type_at := (UkShParse.ushp_type_at N).
  Local Notation wp_kshp_frame_epi := (UkShParse.wp_kshp_frame_epi N).
  Local Notation wp_kshp_frame_pro := (UkShParse.wp_kshp_frame_pro N).
  Local Notation ushp_redir_node := (UkShRedirCmd.ushp_redir_node N).
  Local Notation ushp_pipe_node := (UkShPipeParse.ushp_pipe_node N).
  Local Notation wp_kshp_peek := (UkShParseLex.wp_kshp_peek N).
  Local Notation wp_kshp_restore := (UkShParse.wp_kshp_restore N).
  Local Notation wp_kshp_spill := (UkShParse.wp_kshp_spill N).

  (* THREE allocator capabilities, chained: a pipe line makes THREE
     constructor calls (an [execcmd] per side of the '|' and one
     [pipecmd]), and the chain is funded -- UkShPipeSeam's
     [ushq_malloc_le_third] is the third link and no chain had to be
     extended.  UM0 -> UM1 is the LEFT [execcmd] (inside premise (i)),
     UM1 -> UM2 the RIGHT one (inside the recursion, so it is a real
     Hypothesis here), UM2 -> UM3 [pipecmd] (inside premise (ii)). *)
  Context (UM0 UM1 UM2 UM3 : iProp Σ).
  Hypothesis ushp_malloc_ok12 : ushp_malloc_ty UM1 UM2.
  (* ===================================================================== *)
  (* §1 THE TWO CALL PREMISES                                               *)
  (*                                                                        *)
  (* SH-REDIR's [ush_open_call] shape: the call stated as the CONCLUSION a   *)
  (* walk of it would have, so the arm compiles before the walk exists and   *)
  (* the lane that lands the walk instantiates the premise and nothing else. *)
  (* ===================================================================== *)

  (* (i) the LEFT command's [parseexec].  Its answer is the exec node for
     the line's OWN token list [args], and it leaves the cursor AT the '|'
     -- which is exactly what the guard's peek then reads. *)
  Definition ushq_pex_left (dq dw dv : dfrac) (ps s0 : Z) (len gp : nat)
      (f : nat -> bv 8) (args : list (nat * nat)) (Pex : iProp Σ)
      (av : nat) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (rpc : mword 64),
       ⌜ m !!! Regidx a0_idx = mword_of_int ps ⌝ -∗
       ⌜ m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ⌝ -∗
       (* the RETURN PC as a parameter, so the caller hands the equation in
          and the answer arrives at the pc it wants *)
       ⌜ ret_pc (m !!! Regidx ra_idx) = rpc ⌝ -∗
       shp_code γt -∗
       shp_rodata γt -∗
       uword γd ps (mword_of_int s0) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
       UM0 -∗
       □ (Pex -∗ ukn_pay N (-1)) -∗
       Pex -∗
       urun N h m (mword_of_int ShSyms.parseexec) av -∗
       (∀ pl : Z,
          ⌜ pl + 168 < Z64 ⌝ -∗
          ushp_exec_at s0 pl args -∗
          uword γd ps (mword_of_int (s0 + Z.of_nat gp)) -∗
          ustr γd dq s0 len f -∗
          ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
          ustr γd dv ushp_symbols 7 ushp_sym_f -∗
            ∀ (h' : CpuId) (m' : regfile),
              ⌜ ucallee_saved m m' ⌝ -∗
              ⌜ m' !!! Regidx a0_idx = mword_of_int pl ⌝ -∗
              UM1 -∗
              Pex -∗
              urun N h' m' rpc av -∗
              WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* (ii) [pipecmd] (0x260).  Stated as [UkShRedirCmd.wp_kshp_redircmd_n] is:
     the two subtrees ride through in an ABSTRACT [Sub], because the node
     and its children are relayed SEPARATELY all the way up to the parser
     theorem (SH-PARSE-2's shape fact), and what comes back is the node with
     both child pointers NAMED. *)
  Definition ushq_pipecmd_call (Pex : iProp Σ) (av : nat) : iProp Σ :=
    (∀ (h : CpuId) (m : regfile) (pl pr : Z) (rpc : mword 64)
       (Sub : iProp Σ),
       ⌜ m !!! Regidx a0_idx = mword_of_int pl ⌝ -∗
       ⌜ m !!! Regidx a1_idx = mword_of_int pr ⌝ -∗
       ⌜ ret_pc (m !!! Regidx ra_idx) = rpc ⌝ -∗
       shp_code γt -∗
       UM2 -∗
       □ (Pex -∗ ukn_pay N (-1)) -∗
       Pex -∗
       Sub -∗
       urun N h m (mword_of_int 0x260) av -∗
       (∀ (h' : CpuId) (m' : regfile) (t : Z),
          ⌜ ucallee_saved m m' ⌝ -∗
          ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
          ushp_pipe_node t pl pr -∗
          Sub -∗
          UM3 -∗
          Pex -∗
          urun N h' m' rpc av -∗
          WP (Loop : expr riscv_lang)) -∗
       WP (Loop : expr riscv_lang))%I.

  (* NON-VACUITY, for premise (i).  A premise nobody can satisfy is worse
     than no premise (durable-notes, Vacuity), so here is [ushq_pex_left]'s
     SHAPE inhabited: at [gp := len] -- a line whose parse runs to the end
     -- it is exactly the LANDED [UkShParseExec.wp_kshp_parseexec]'s
     conclusion, so the pipe line's instance differs from a proved one only
     in WHERE the cursor stops.  (Premise (ii) cannot be witnessed this way:
     nothing in the tree fetches an instruction of [pipecmd] -- see the
     lane's findings.) *)
  Lemma ushq_pex_left_nosym {Pex : iProp Σ} (dq dw dv : dfrac)
      (ps s0 : Z) (len : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_no_symbols len f ->
    ushp_tokens len f 0%nat args ->
    (length args < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    ⊢ ushq_pex_left dq dw dv ps s0 len len f args Pex (16 + (24 + nn)).
  Proof using .
    intros Hm01 Hns Htoks Hlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros (h m rpc) "%Ha0 %Ha1 %Erpc #Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hrun Hcont".
    iApply (UkShParseExec.wp_kshp_parseexec N UM0 UM1 Hm01 h m dq dw dv
              ps s0 len 0%nat f (mword_of_int s0) args nn
              Ha0 Ha1 ltac:(lia)
              ltac:(rewrite Z.add_0_r; reflexivity)
              Hns Htoks Hlen Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay Hrun").
    iIntros (q) "%Hqsz Hnode Hcur Hstr Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM1 Hpay Hrun".
    rewrite Erpc.
    iApply ("Hcont" $! q with "[] Hnode Hcur Hstr Hws Hsy [] [] HM1 Hpay Hrun").
    - iPureIntro. exact Hqsz.
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
  Qed.

  (* PREMISE (ii) IS DISCHARGED: [pipecmd]'s twenty-seven instructions are
     walked ([UkShPipeCmd.wp_kshp_pipecmd]) now that its catalog row exists,
     so the turn below needs only premise (i).  The budget arithmetic is the
     only thing to say: the walk asks for [6 + (10 + nn')] and the turn's
     call site has [16 + (24 + (8 + nn))], so [nn' := 32 + nn] and the two
     are the same [48 + nn]. *)
  Lemma ushq_pipecmd_call_holds {Pex : iProp Σ} (nn : nat) :
    ushp_malloc_ty UM2 UM3 ->
    ⊢ ushq_pipecmd_call Pex (16 + (24 + (8 + nn))).
  Proof using .
    intro Hm23.
    iIntros (h m pl pr rpc Sub) "%Ha0 %Ha1 %Erpc #Hcode HM #Hpx Hpay Hsub Hrun Hcont".
    rewrite <- Erpc.
    iApply (UkShPipeCmd.wp_kshp_pipecmd N UM2 UM3 Hm23 h m pl pr Sub
              (32 + nn) Ha0 Ha1
              with "Hcode HM Hpx Hpay Hsub Hrun").
    iIntros (h' m' t) "%Hcs %Ha0' %Htb Hnode Hsub HM' Hpay Hrun".
    iApply ("Hcont" $! h' m' t with "[] [] Hnode Hsub HM' Hpay Hrun").
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
  Qed.

  (* ===================================================================== *)
  (* §2 THE TURN                                                            *)
  (*                                                                        *)
  (* [UkShRedirCm.wp_kshp_parsepipe_gt] is this walk with the guard REFUTED. *)
  (* The pipe line is the first line that makes it TURN, and the turn is     *)
  (* THIRTEEN instructions, 0x6c2..0x6e0, rejoining the landed walk's own    *)
  (* tail at 0x6b0:                                                         *)
  (*                                                                        *)
  (*   0x6c2 c.li a3,0 ; 0x6c4 c.li a2,0 ; 0x6c6 c.mv a1,s1                 *)
  (*   0x6c8 c.mv a0,s4 ; 0x6ca jal gettoken   -- consumes the '|'          *)
  (*   0x6ce c.mv a1,s1 ; 0x6d0 c.mv a0,s4                                  *)
  (*   0x6d2 jal parsepipe                     -- THE RECURSION             *)
  (*   0x6d6 c.mv a1,a0 ; 0x6d8 c.mv a0,s3                                  *)
  (*   0x6da jal pipecmd                        -- the PIPE node            *)
  (*   0x6de c.mv s3,a0 ; 0x6e0 c.j 6b0                                     *)
  (*                                                                        *)
  (* Two of its three calls are DISCHARGED here: [gettoken] by              *)
  (* [UkShPipeTok.wp_kshp_gettoken_syms] (it answers 124 and advances the    *)
  (* cursor to [S (S gp)]) and the RECURSION by                              *)
  (* [UkShPipeRight.wp_kshp_parsepipe_right] (the landed symbol-free walk    *)
  (* on the line's own suffix).  The other two are CALL PREMISES in          *)
  (* SH-REDIR's [ush_open_call] style: the LEFT [parseexec], whose walk is   *)
  (* a re-statement this lane did not finish, and [pipecmd], whose 48        *)
  (* instructions are in NO catalog (`skipfunc pipecmd`) and cannot be put   *)
  (* in one from this worktree -- see the lane's findings.                   *)
  (* ===================================================================== *)

  Lemma wp_kshp_parsepipe_bar {Pex : iProp Σ} (h : CpuId) (m : regfile)
      (dq dw dv : dfrac) (ps s0 : Z) (len gp ge : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (nn : nat) :
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    ushq_pipe len f gp ge ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int s0) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    (* (i) the LEFT command's parse, as a CALL PREMISE *)
    ushq_pex_left dq dw dv ps s0 len gp f args Pex (16 + (24 + (8 + nn))) -∗
    (* (ii) [pipecmd], as a CALL PREMISE *)
    ushq_pipecmd_call Pex (16 + (24 + (8 + nn))) -∗
    urun N h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + (8 + nn)))) -∗
    (∀ t pl pr : Z,
       ⌜ pl + 168 < Z64 ⌝ -∗
       ⌜ pr + 168 < Z64 ⌝ -∗
       ushp_pipe_node t pl pr -∗
       ushp_exec_at s0 pl args -∗
       ushp_exec_at s0 pr [(S (S gp), ge)] -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM3 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + (8 + nn)))) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok12.
    intros Ha0 Ha1 Hpq Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hleft Hpipec Hrun Hcont".
    rewrite shpp_parsepipe.
    (* the cursor the LEFT parse leaves is AT the '|', so the guard's own
       blank scan does not move and the peek answers at [gp] itself *)
    assert (Egp0 : (gp + ushp_skipws (len - gp) gp f)%nat = gp)
      by (rewrite (ushq_skipws_at_bar len f gp ge (len - gp)%nat Hpq); lia).
    assert (Hgplt : (gp < len)%nat) by exact (ushq_pipe_lt len f gp ge Hpq).
    assert (Hgple : (gp <= len)%nat) by lia.
    set (vals := fun i : nat =>
                   match i with
                   | 0%nat => m !!! Regidx ra_idx
                   | 1%nat => m !!! Regidx s0_idx
                   | 2%nat => m !!! Regidx s1_idx
                   | 3%nat => m !!! Regidx s2_idx
                   | 4%nat => m !!! Regidx s3_idx
                   | _ => m !!! Regidx s4_idx end).
    (* ---- 0x682..0x690  the prologue ---- *)
    iApply (wp_kshp_frame_pro 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] 0x682
              (fun i : nat => match i with
                              | 0%nat => 0x684 | 1%nat => 0x686
                              | 2%nat => 0x688 | 3%nat => 0x68a
                              | 4%nat => 0x68c | 5%nat => 0x68e
                              | _ => 0x690 end)
              (mword_of_int 61 : mword 6) (mword_of_int 12 : mword 8)
              vals (16 + (24 + (8 + nn))) h m
              ltac:(cbn [length]; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(cbn; lia)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ vm_compute; discriminate | reflexivity ] ]))
              with "[] [] [] Hrun").
    { iApply (uis_shp_682 with "Hcode"). }
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_684 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_686 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_688 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68a with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68c with "Hcode") | ].
      iSplit; [ iApply (uis_shp_68e with "Hcode") | done ]. }
    { iApply (uis_shp_690 with "Hcode"). }
    iIntros (h1 v) "%Hal8 %Hlo %Hhi Hsl Hloc Hrun". cbn [length].
    set (sp0 := m !!! Regidx csp_rs1) in *.
    set (spn := add_vec_int sp0 (- (8 * Z.of_nat 6))).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg spn]> m).
    set (mA := <[Regidx s0_idx := regval_into_reg v]> m1).
    assert (Hm1 : forall q : mword 5, Regidx q <> Regidx csp_rs1 ->
                    m1 !!! Regidx q = m !!! Regidx q)
      by (intros q Hq; exact (upd_ne m (Regidx csp_rs1) (Regidx q) _ Hq)).
    assert (HmA : forall q : mword 5, Regidx q <> Regidx s0_idx ->
                    mA !!! Regidx q = m1 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m1 (Regidx s0_idx) (Regidx q) _ Hq)).
    assert (HspA : mA !!! Regidx csp_rs1 = spn).
    { rewrite (HmA csp_rs1 ltac:(vm_compute; discriminate)).
      exact (upd_eq m (Regidx csp_rs1) (regval_into_reg spn)). }
    (* ---- 0x692  c.mv s2,a0 ---- *)
    iApply (wp_uk_cmv N h1 mA (mword_of_int 0x692) s2_idx a0_idx
              (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_692 with "Hcode"). }
    iIntros (h2) "Hrun".
    set (m2 := <[Regidx s2_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> mA).
    assert (Hm2 : forall q : mword 5, Regidx q <> Regidx s2_idx ->
                    m2 !!! Regidx q = mA !!! Regidx q)
      by (intros q Hq; exact (upd_ne mA (Regidx s2_idx) (Regidx q) _ Hq)).
    (* ---- 0x694  c.mv s4,a0 ---- *)
    iApply (wp_uk_cmv N h2 m2 (mword_of_int 0x694) s4_idx a0_idx
              (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm2 a0_idx ltac:(vm_compute; discriminate))
                      (HmA a0_idx ltac:(vm_compute; discriminate))
                      (Hm1 a0_idx ltac:(vm_compute; discriminate)) Ha0;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_694 with "Hcode"). }
    iIntros (h3) "Hrun".
    set (m3 := <[Regidx s4_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> m2).
    assert (Hm3 : forall q : mword 5, Regidx q <> Regidx s4_idx ->
                    m3 !!! Regidx q = m2 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m2 (Regidx s4_idx) (Regidx q) _ Hq)).
    (* ---- 0x696  c.mv s1,a1 ---- *)
    iApply (wp_uk_cmv N h3 m3 (mword_of_int 0x696) s1_idx a1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm3 a1_idx ltac:(vm_compute; discriminate))
                      (Hm2 a1_idx ltac:(vm_compute; discriminate))
                      (HmA a1_idx ltac:(vm_compute; discriminate))
                      (Hm1 a1_idx ltac:(vm_compute; discriminate)) Ha1;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_696 with "Hcode"). }
    iIntros (h4) "Hrun".
    set (m4 := <[Regidx s1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m3).
    assert (Hm4 : forall q : mword 5, Regidx q <> Regidx s1_idx ->
                    m4 !!! Regidx q = m3 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m3 (Regidx s1_idx) (Regidx q) _ Hq)).
    (* ---- 0x698  jal 590 <parseexec> ---- *)
    iApply (wp_uk_jal N h4 m4 (mword_of_int 0x698)
              (mword_of_int 2096888 : mword 21) ra_idx
              (mword_of_int 0x590) (mword_of_int 0x69c) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_698 with "Hcode"). }
    iIntros (h5) "Hrun".
    set (m5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x69c : mword 64)]> m4).
    assert (Hm5 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                    m5 !!! Regidx q = m4 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m4 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret5 : ret_pc (m5 !!! Regidx ra_idx) = mword_of_int 0x69c).
    { rewrite (upd_eq m4 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x69c : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_5 : m5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm5 a0_idx ltac:(vm_compute; discriminate))
              (Hm4 a0_idx ltac:(vm_compute; discriminate))
              (Hm3 a0_idx ltac:(vm_compute; discriminate))
              (Hm2 a0_idx ltac:(vm_compute; discriminate))
              (HmA a0_idx ltac:(vm_compute; discriminate))
              (Hm1 a0_idx ltac:(vm_compute; discriminate)). exact Ha0. }
    assert (Ha1_5 : m5 !!! Regidx a1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm5 a1_idx ltac:(vm_compute; discriminate))
              (Hm4 a1_idx ltac:(vm_compute; discriminate))
              (Hm3 a1_idx ltac:(vm_compute; discriminate))
              (Hm2 a1_idx ltac:(vm_compute; discriminate))
              (HmA a1_idx ltac:(vm_compute; discriminate))
              (Hm1 a1_idx ltac:(vm_compute; discriminate)). exact Ha1. }
    rewrite <- shpp_parseexec.
    (* ---- 0x698  jal 590 <parseexec> -- THE LEFT COMMAND, premise (i) -- *)
    iApply ("Hleft" $! h5 m5 (mword_of_int 0x69c)
              with "[] [] [] Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay Hrun").
    { iPureIntro. exact Ha0_5. }
    { iPureIntro. exact Ha1_5. }
    { iPureIntro. exact Eret5. }
    iIntros (pl) "%Hplsz Hnodel Hcur Hstr Hws Hsy".
    iIntros (h6 m6) "%Hcs56 %Ha0_6 HM1 Hpay Hrun".
    (* ---- 0x69c  c.mv s3,a0 ---- *)
    iApply (wp_uk_cmv N h6 m6 (mword_of_int 0x69c) s3_idx a0_idx
              (mword_of_int pl) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_6; symmetry; exact (ushp_mv_val pl))
              with "[] Hrun").
    { iApply (uis_shp_69c with "Hcode"). }
    iIntros (h7) "Hrun".
    set (m7 := <[Regidx s3_idx
                 := regval_into_reg (mword_of_int pl : mword 64)]> m6).
    assert (Hm7 : forall q : mword 5, Regidx q <> Regidx s3_idx ->
                    m7 !!! Regidx q = m6 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m6 (Regidx s3_idx) (Regidx q) _ Hq)).
    (* ---- 0x69e/0x6a2  the pipe table ---- *)
    iApply (wp_uk_auipc N h7 m7 (mword_of_int 0x69e)
              (mword_of_int 1 : mword 20) a2_idx
              (mword_of_int 0x169e) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_69e with "Hcode"). }
    iIntros (h8) "Hrun".
    set (m8 := <[Regidx a2_idx
                 := regval_into_reg (mword_of_int 0x169e : mword 64)]> m7).
    assert (Hm8 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m8 !!! Regidx q = m7 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m7 (Regidx a2_idx) (Regidx q) _ Hq)).
    assert (Ha2_8 : m8 !!! Regidx a2_idx = mword_of_int 0x169e)
      by exact (upd_eq m7 (Regidx a2_idx)
                  (regval_into_reg (mword_of_int 0x169e : mword 64))).
    iApply (wp_uk_addi N h8 m8 (mword_of_int 0x6a2)
              (mword_of_int 3202 : mword 12) a2_idx a2_idx
              (mword_of_int ushp_T_pipe) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha2_8; unfold ushp_T_pipe;
                    apply bv_eq; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6a2 with "Hcode"). }
    iIntros (h9) "Hrun".
    set (m9 := <[Regidx a2_idx
                 := regval_into_reg
                      (mword_of_int ushp_T_pipe : mword 64)]> m8).
    assert (Hm9 : forall q : mword 5, Regidx q <> Regidx a2_idx ->
                    m9 !!! Regidx q = m8 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m8 (Regidx a2_idx) (Regidx q) _ Hq)).
    (* ---- 0x6a6/0x6a8  peek's two other arguments ---- *)
    assert (Hs1_9 : m9 !!! Regidx s1_idx
                    = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm9 s1_idx ltac:(vm_compute; discriminate))
              (Hm8 s1_idx ltac:(vm_compute; discriminate))
              (Hm7 s1_idx ltac:(vm_compute; discriminate))
              (Hcs56 s1_idx ltac:(vm_compute; reflexivity))
              (Hm5 s1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m3 (Regidx s1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Hs2_9 : m9 !!! Regidx s2_idx = mword_of_int ps).
    { rewrite (Hm9 s2_idx ltac:(vm_compute; discriminate))
              (Hm8 s2_idx ltac:(vm_compute; discriminate))
              (Hm7 s2_idx ltac:(vm_compute; discriminate))
              (Hcs56 s2_idx ltac:(vm_compute; reflexivity))
              (Hm5 s2_idx ltac:(vm_compute; discriminate))
              (Hm4 s2_idx ltac:(vm_compute; discriminate))
              (Hm3 s2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq mA (Regidx s2_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    iApply (wp_uk_cmv N h9 m9 (mword_of_int 0x6a6) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_9; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6a6 with "Hcode"). }
    iIntros (h10) "Hrun".
    set (m10 := <[Regidx a1_idx
                  := regval_into_reg
                       (mword_of_int (s0 + Z.of_nat len) : mword 64)]> m9).
    assert (Hm10 : forall q : mword 5, Regidx q <> Regidx a1_idx ->
                     m10 !!! Regidx q = m9 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m9 (Regidx a1_idx) (Regidx q) _ Hq)).
    iApply (wp_uk_cmv N h10 m10 (mword_of_int 0x6a8) a0_idx
              s2_idx (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hm10 s2_idx ltac:(vm_compute; discriminate))
                      Hs2_9; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6a8 with "Hcode"). }
    iIntros (h11) "Hrun".
    set (m11 := <[Regidx a0_idx
                  := regval_into_reg (mword_of_int ps : mword 64)]> m10).
    assert (Hm11 : forall q : mword 5, Regidx q <> Regidx a0_idx ->
                     m11 !!! Regidx q = m10 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m10 (Regidx a0_idx) (Regidx q) _ Hq)).
    (* ---- 0x6aa  jal 448 <peek> ---- *)
    iApply (wp_uk_jal N h11 m11 (mword_of_int 0x6aa)
              (mword_of_int 2096542 : mword 21) ra_idx
              (mword_of_int 0x448) (mword_of_int 0x6ae) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6aa with "Hcode"). }
    iIntros (h12) "Hrun".
    set (m12 := <[Regidx ra_idx
                  := regval_into_reg (mword_of_int 0x6ae : mword 64)]> m11).
    assert (Hm12 : forall q : mword 5, Regidx q <> Regidx ra_idx ->
                     m12 !!! Regidx q = m11 !!! Regidx q)
      by (intros q Hq; exact (upd_ne m11 (Regidx ra_idx) (Regidx q) _ Hq)).
    assert (Eret12 : ret_pc (m12 !!! Regidx ra_idx) = mword_of_int 0x6ae).
    { rewrite (upd_eq m11 (Regidx ra_idx)
                 (regval_into_reg (mword_of_int 0x6ae : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    assert (Ha0_12 : m12 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hm12 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m10 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_12 : m12 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hm12 a1_idx ltac:(vm_compute; discriminate))
              (Hm11 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m9 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_12 : m12 !!! Regidx a2_idx = mword_of_int ushp_T_pipe).
    { rewrite (Hm12 a2_idx ltac:(vm_compute; discriminate))
              (Hm11 a2_idx ltac:(vm_compute; discriminate))
              (Hm10 a2_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m8 (Regidx a2_idx)
               (regval_into_reg (mword_of_int ushp_T_pipe : mword 64))). }
    rewrite <- shpp_peek.
    iApply (wp_kshp_peek h12 m12 dq dw true DfracDiscarded ps s0
              ushp_T_pipe len gp 1 f (ushp_lit ushp_T_pipe)
              (mword_of_int (s0 + Z.of_nat gp)) (30 + (8 + nn))
              Ha0_12 Ha1_12 Ha2_12 Hgple eq_refl Hs0 Hs64
              ltac:(unfold ushp_T_pipe; lia)
              ltac:(unfold ushp_T_pipe, Z64; lia) Hps0 Hps8 Hpssz
              with "Hcode Hcur Hstr Hws [] Hrun").
    { iApply (ushp_lit_str ushp_T_pipe 1 DfracDiscarded
                ushp_T_pipe_ok ltac:(cbn; lia) with "Hro"). }
    iIntros "Hcur Hstr Hws _" (h13 m13) "%Hcs1213 %Ha0_13 Hrun".
    rewrite Eret12 Egp0.
    rewrite Egp0 in Ha0_13.
    (* THE GUARD TURNS.  peek's table at 0x1320 is the one byte '|', and the
       byte at the cursor IS it -- the one fact no landed walk could produce
       ([UkShPipeEx.ushq_peek_pipe_hit_pipe]). *)
    rewrite (ushq_peek_pipe_hit_pipe len f gp ge Hpq) in Ha0_13.
    (* ---- the register file the turn starts from ---- *)
    assert (Hs1_13 : m13 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hcs1213 s1_idx ltac:(vm_compute; reflexivity))
              (Hm12 s1_idx ltac:(vm_compute; discriminate))
              (Hm11 s1_idx ltac:(vm_compute; discriminate))
              (Hm10 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_9. }
    assert (Hs4_13 : m13 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hcs1213 s4_idx ltac:(vm_compute; reflexivity))
              (Hm12 s4_idx ltac:(vm_compute; discriminate))
              (Hm11 s4_idx ltac:(vm_compute; discriminate))
              (Hm10 s4_idx ltac:(vm_compute; discriminate))
              (Hm9 s4_idx ltac:(vm_compute; discriminate))
              (Hm8 s4_idx ltac:(vm_compute; discriminate))
              (Hm7 s4_idx ltac:(vm_compute; discriminate))
              (Hcs56 s4_idx ltac:(vm_compute; reflexivity))
              (Hm5 s4_idx ltac:(vm_compute; discriminate))
              (Hm4 s4_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m2 (Regidx s4_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Hs3_13 : m13 !!! Regidx s3_idx = mword_of_int pl).
    { rewrite (Hcs1213 s3_idx ltac:(vm_compute; reflexivity))
              (Hm12 s3_idx ltac:(vm_compute; discriminate))
              (Hm11 s3_idx ltac:(vm_compute; discriminate))
              (Hm10 s3_idx ltac:(vm_compute; discriminate))
              (Hm9 s3_idx ltac:(vm_compute; discriminate))
              (Hm8 s3_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq m6 (Regidx s3_idx)
               (regval_into_reg (mword_of_int pl : mword 64))). }
    (* ---- 0x6ae  c.bnez a0 -- TAKEN: there IS a pipe ---- *)
    iApply (wp_uk_cbnez N h13 m13 (mword_of_int 0x6ae)
              (mword_of_int 10 : mword 8) (mword_of_int 2 : mword 3)
              a0_idx true (mword_of_int 0x6c2) (16 + (24 + (8 + nn)))
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite Ha0_13; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros _; vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6ae with "Hcode"). }
    iIntros (h14) "Hrun".
    (* ---- 0x6c2  c.li a3,0 ---- *)
    iApply (wp_uk_cli N h14 m13 (mword_of_int 0x6c2)
              (mword_of_int 0 : mword 6) a3_idx (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_6c2 with "Hcode"). }
    rewrite (ushp_pc_step 0x6c2 2). iIntros (h15) "Hrun".
    set (q1 := <[Regidx a3_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> m13).
    assert (Hq1 : forall r : mword 5, Regidx r <> Regidx a3_idx ->
                    q1 !!! Regidx r = m13 !!! Regidx r)
      by (intros r Hr; exact (upd_ne m13 (Regidx a3_idx) (Regidx r) _ Hr)).
    assert (Ha3_q1 : q1 !!! Regidx a3_idx = mword_of_int 0).
    { rewrite (upd_eq m13 (Regidx a3_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x6c4  c.li a2,0 ---- *)
    iApply (wp_uk_cli N h15 q1 (mword_of_int 0x6c4)
              (mword_of_int 0 : mword 6) a2_idx (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              with "[] Hrun").
    { iApply (uis_shp_6c4 with "Hcode"). }
    rewrite (ushp_pc_step 0x6c4 2). iIntros (h16) "Hrun".
    set (q2 := <[Regidx a2_idx
                 := regval_into_reg
                      (sign_extend' 64 (mword_of_int 0 : mword 6)
                       : mword 64)]> q1).
    assert (Hq2 : forall r : mword 5, Regidx r <> Regidx a2_idx ->
                    q2 !!! Regidx r = q1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q1 (Regidx a2_idx) (Regidx r) _ Hr)).
    assert (Ha2_q2 : q2 !!! Regidx a2_idx = mword_of_int 0).
    { rewrite (upd_eq q1 (Regidx a2_idx)
                 (regval_into_reg
                    (sign_extend' 64 (mword_of_int 0 : mword 6) : mword 64))).
      apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x6c6  c.mv a1,s1  --  es ---- *)
    iApply (wp_uk_cmv N h16 q2 (mword_of_int 0x6c6) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hq2 s1_idx ltac:(vm_compute; discriminate))
                      (Hq1 s1_idx ltac:(vm_compute; discriminate)) Hs1_13;
                    symmetry; exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6c6 with "Hcode"). }
    rewrite (ushp_pc_step 0x6c6 2). iIntros (h17) "Hrun".
    set (q3 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> q2).
    assert (Hq3 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    q3 !!! Regidx r = q2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q2 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x6c8  c.mv a0,s4  --  &s ---- *)
    iApply (wp_uk_cmv N h17 q3 (mword_of_int 0x6c8) a0_idx s4_idx
              (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hq3 s4_idx ltac:(vm_compute; discriminate))
                      (Hq2 s4_idx ltac:(vm_compute; discriminate))
                      (Hq1 s4_idx ltac:(vm_compute; discriminate)) Hs4_13;
                    symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6c8 with "Hcode"). }
    rewrite (ushp_pc_step 0x6c8 2). iIntros (h18) "Hrun".
    set (q4 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> q3).
    assert (Hq4 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    q4 !!! Regidx r = q3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q3 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x6ca  jal 310 <gettoken> -- consumes the '|' ---- *)
    iApply (wp_uk_jal N h18 q4 (mword_of_int 0x6ca)
              (mword_of_int 2096198 : mword 21) ra_idx
              (mword_of_int 0x310) (mword_of_int 0x6ce) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6ca with "Hcode"). }
    iIntros (h19) "Hrun".
    set (q5 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6ce : mword 64)]> q4).
    assert (Hq5 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    q5 !!! Regidx r = q4 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q4 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Eret_g : ret_pc (q5 !!! Regidx ra_idx) = mword_of_int 0x6ce);
      [ rewrite (upd_eq q4 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x6ce : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_q5 : q5 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hq5 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq q3 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_q5 : q5 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hq5 a1_idx ltac:(vm_compute; discriminate))
              (Hq4 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq q2 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    assert (Ha2_q5 : q5 !!! Regidx a2_idx = mword_of_int 0).
    { rewrite (Hq5 a2_idx ltac:(vm_compute; discriminate))
              (Hq4 a2_idx ltac:(vm_compute; discriminate))
              (Hq3 a2_idx ltac:(vm_compute; discriminate)). exact Ha2_q2. }
    assert (Ha3_q5 : q5 !!! Regidx a3_idx = mword_of_int 0).
    { rewrite (Hq5 a3_idx ltac:(vm_compute; discriminate))
              (Hq4 a3_idx ltac:(vm_compute; discriminate))
              (Hq3 a3_idx ltac:(vm_compute; discriminate))
              (Hq2 a3_idx ltac:(vm_compute; discriminate)). exact Ha3_q1. }
    rewrite <- shpp_gettoken.
    (* gettoken at EITHER symbol byte: here it is the '|', it answers 124,
       and it leaves the cursor at [S (S gp)] -- the right command's first
       byte ([UkShPipeLex.ushq_gettok_fin_bar]).  Both out-parameters are
       NULL, which is [UkShParseTok.ushp_cell]'s left disjunct. *)
    iApply (UkShPipeTok.wp_kshp_gettoken_syms N h19 q5 dq dw dv ps 0 0 s0
              len gp f (mword_of_int (s0 + Z.of_nat gp))
              (mword_of_int 0) (mword_of_int 0) (38 + nn)
              Ha0_q5 Ha1_q5 Ha2_q5 Ha3_q5 Hgple eq_refl
              (ushq_sym_ok_pipe len f gp ge Hpq) Hs0 Hs64
              Hps0 Hps8 Hpssz
              with "Hcode Hcur [] [] Hstr Hws Hsy Hrun").
    { iLeft. iPureIntro. reflexivity. }
    { iLeft. iPureIntro. reflexivity. }
    iIntros "Hcur _ _ Hstr Hws Hsy" (h20 g1) "%Hcsg %Ha0_g Hrun".
    rewrite Eret_g.
    (* the cursor gettoken leaves: [S (S gp)], the right command's first
       byte ([UkShPipeLex.ushq_gettok_fin_bar]) *)
    rewrite Egp0.
    rewrite (ushq_gettok_fin_bar len f gp ge Hpq).
    (* ---- 0x6ce  c.mv a1,s1 ---- *)
    assert (Hs1_g1 : g1 !!! Regidx s1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hcsg s1_idx ltac:(vm_compute; reflexivity))
              (Hq5 s1_idx ltac:(vm_compute; discriminate))
              (Hq4 s1_idx ltac:(vm_compute; discriminate))
              (Hq3 s1_idx ltac:(vm_compute; discriminate))
              (Hq2 s1_idx ltac:(vm_compute; discriminate))
              (Hq1 s1_idx ltac:(vm_compute; discriminate)). exact Hs1_13. }
    assert (Hs4_g1 : g1 !!! Regidx s4_idx = mword_of_int ps).
    { rewrite (Hcsg s4_idx ltac:(vm_compute; reflexivity))
              (Hq5 s4_idx ltac:(vm_compute; discriminate))
              (Hq4 s4_idx ltac:(vm_compute; discriminate))
              (Hq3 s4_idx ltac:(vm_compute; discriminate))
              (Hq2 s4_idx ltac:(vm_compute; discriminate))
              (Hq1 s4_idx ltac:(vm_compute; discriminate)). exact Hs4_13. }
    iApply (wp_uk_cmv N h20 g1 (mword_of_int 0x6ce) a1_idx s1_idx
              (mword_of_int (s0 + Z.of_nat len)) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs1_g1; symmetry;
                    exact (ushp_mv_val (s0 + Z.of_nat len)))
              with "[] Hrun").
    { iApply (uis_shp_6ce with "Hcode"). }
    rewrite (ushp_pc_step 0x6ce 2). iIntros (h21) "Hrun".
    set (g2 := <[Regidx a1_idx
                 := regval_into_reg
                      (mword_of_int (s0 + Z.of_nat len) : mword 64)]> g1).
    assert (Hg2 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    g2 !!! Regidx r = g1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g1 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x6d0  c.mv a0,s4 ---- *)
    iApply (wp_uk_cmv N h21 g2 (mword_of_int 0x6d0) a0_idx s4_idx
              (mword_of_int ps) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hg2 s4_idx ltac:(vm_compute; discriminate))
                      Hs4_g1; symmetry; exact (ushp_mv_val ps))
              with "[] Hrun").
    { iApply (uis_shp_6d0 with "Hcode"). }
    rewrite (ushp_pc_step 0x6d0 2). iIntros (h22) "Hrun".
    set (g3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int ps : mword 64)]> g2).
    assert (Hg3 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    g3 !!! Regidx r = g2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g2 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x6d2  jal 682 <parsepipe> -- THE RECURSION ---- *)
    iApply (wp_uk_jal N h22 g3 (mword_of_int 0x6d2)
              (mword_of_int 2097072 : mword 21) ra_idx
              (mword_of_int 0x682) (mword_of_int 0x6d6) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6d2 with "Hcode"). }
    iIntros (h23) "Hrun".
    set (g4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6d6 : mword 64)]> g3).
    assert (Hg4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    g4 !!! Regidx r = g3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne g3 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Eret_r : ret_pc (g4 !!! Regidx ra_idx) = mword_of_int 0x6d6);
      [ rewrite (upd_eq g3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x6d6 : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_g4 : g4 !!! Regidx a0_idx = mword_of_int ps).
    { rewrite (Hg4 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq g2 (Regidx a0_idx)
               (regval_into_reg (mword_of_int ps : mword 64))). }
    assert (Ha1_g4 : g4 !!! Regidx a1_idx
                     = mword_of_int (s0 + Z.of_nat len)).
    { rewrite (Hg4 a1_idx ltac:(vm_compute; discriminate))
              (Hg3 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq g1 (Regidx a1_idx)
               (regval_into_reg
                  (mword_of_int (s0 + Z.of_nat len) : mword 64))). }
    rewrite <- shpp_parsepipe.
    (* the recursive call is the LANDED symbol-free walk, on the line's own
       SUFFIX ([UkShPipeRight.wp_kshp_parsepipe_right]) *)
    iApply (UkShPipeRight.wp_kshp_parsepipe_right N UM1 UM2 ushp_malloc_ok12
              h23 g4 dq dw dv ps s0 len gp ge f (2 + nn)
              Ha0_g4 Ha1_g4 Hpq Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM1 Hpx Hpay Hrun").
    iIntros (pr) "%Hprsz Hnoder Hcur Hstr Hws Hsy".
    iIntros (h24 r1) "%Hcsr %Ha0_r HM2 Hpay Hrun".
    rewrite Eret_r.
    (* ---- 0x6d6  c.mv a1,a0  --  the RIGHT node ---- *)
    iApply (wp_uk_cmv N h24 r1 (mword_of_int 0x6d6) a1_idx a0_idx
              (mword_of_int pr) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_r; symmetry; exact (ushp_mv_val pr))
              with "[] Hrun").
    { iApply (uis_shp_6d6 with "Hcode"). }
    rewrite (ushp_pc_step 0x6d6 2). iIntros (h25) "Hrun".
    set (r2 := <[Regidx a1_idx
                 := regval_into_reg (mword_of_int pr : mword 64)]> r1).
    assert (Hr2 : forall r : mword 5, Regidx r <> Regidx a1_idx ->
                    r2 !!! Regidx r = r1 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r1 (Regidx a1_idx) (Regidx r) _ Hr)).
    (* ---- 0x6d8  c.mv a0,s3  --  the LEFT node ---- *)
    assert (Hs3_r1 : r1 !!! Regidx s3_idx = mword_of_int pl).
    { rewrite (Hcsr s3_idx ltac:(vm_compute; reflexivity))
              (Hg4 s3_idx ltac:(vm_compute; discriminate))
              (Hg3 s3_idx ltac:(vm_compute; discriminate))
              (Hg2 s3_idx ltac:(vm_compute; discriminate))
              (Hcsg s3_idx ltac:(vm_compute; reflexivity))
              (Hq5 s3_idx ltac:(vm_compute; discriminate))
              (Hq4 s3_idx ltac:(vm_compute; discriminate))
              (Hq3 s3_idx ltac:(vm_compute; discriminate))
              (Hq2 s3_idx ltac:(vm_compute; discriminate))
              (Hq1 s3_idx ltac:(vm_compute; discriminate)). exact Hs3_13. }
    iApply (wp_uk_cmv N h25 r2 (mword_of_int 0x6d8) a0_idx s3_idx
              (mword_of_int pl) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite (Hr2 s3_idx ltac:(vm_compute; discriminate))
                      Hs3_r1; symmetry; exact (ushp_mv_val pl))
              with "[] Hrun").
    { iApply (uis_shp_6d8 with "Hcode"). }
    rewrite (ushp_pc_step 0x6d8 2). iIntros (h26) "Hrun".
    set (r3 := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int pl : mword 64)]> r2).
    assert (Hr3 : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    r3 !!! Regidx r = r2 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r2 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* ---- 0x6da  jal 260 <pipecmd> -- premise (ii) ---- *)
    iApply (wp_uk_jal N h26 r3 (mword_of_int 0x6da)
              (mword_of_int 2096006 : mword 21) ra_idx
              (mword_of_int 0x260) (mword_of_int 0x6de) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6da with "Hcode"). }
    iIntros (h27) "Hrun".
    set (r4 := <[Regidx ra_idx
                 := regval_into_reg (mword_of_int 0x6de : mword 64)]> r3).
    assert (Hr4 : forall r : mword 5, Regidx r <> Regidx ra_idx ->
                    r4 !!! Regidx r = r3 !!! Regidx r)
      by (intros r Hr; exact (upd_ne r3 (Regidx ra_idx) (Regidx r) _ Hr)).
    assert (Eret_c : ret_pc (r4 !!! Regidx ra_idx) = mword_of_int 0x6de);
      [ rewrite (upd_eq r3 (Regidx ra_idx)
                   (regval_into_reg (mword_of_int 0x6de : mword 64)));
        apply bv_eq; vm_compute; reflexivity | ].
    assert (Ha0_r4 : r4 !!! Regidx a0_idx = mword_of_int pl).
    { rewrite (Hr4 a0_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r2 (Regidx a0_idx)
               (regval_into_reg (mword_of_int pl : mword 64))). }
    assert (Ha1_r4 : r4 !!! Regidx a1_idx = mword_of_int pr).
    { rewrite (Hr4 a1_idx ltac:(vm_compute; discriminate))
              (Hr3 a1_idx ltac:(vm_compute; discriminate)).
      exact (upd_eq r1 (Regidx a1_idx)
               (regval_into_reg (mword_of_int pr : mword 64))). }
    iApply ("Hpipec" $! h27 r4 pl pr (mword_of_int 0x6de)
              (ushp_exec_at s0 pl args ∗ ushp_exec_at s0 pr [(S (S gp), ge)])%I
              with "[] [] [] Hcode HM2 Hpx Hpay [Hnodel Hnoder] Hrun").
    { iPureIntro. exact Ha0_r4. }
    { iPureIntro. exact Ha1_r4. }
    { iPureIntro. exact Eret_c. }
    { iSplitL "Hnodel"; [ iExact "Hnodel" | iExact "Hnoder" ]. }
    iIntros (h28 q11 t) "%Hcsc %Ha0_c Hpnode [Hnodel Hnoder] HM3 Hpay Hrun".
    (* ---- 0x6de  c.mv s3,a0  --  the PIPE node becomes the answer ---- *)
    iApply (wp_uk_cmv N h28 q11 (mword_of_int 0x6de) s3_idx a0_idx
              (mword_of_int t) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha0_c; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_6de with "Hcode"). }
    rewrite (ushp_pc_step 0x6de 2). iIntros (h29) "Hrun".
    set (q12 := <[Regidx s3_idx
                  := regval_into_reg (mword_of_int t : mword 64)]> q11).
    assert (Hq12 : forall r : mword 5, Regidx r <> Regidx s3_idx ->
                     q12 !!! Regidx r = q11 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q11 (Regidx s3_idx) (Regidx r) _ Hr)).
    assert (Hs3_q12 : q12 !!! Regidx s3_idx = mword_of_int t)
      by exact (upd_eq q11 (Regidx s3_idx)
                  (regval_into_reg (mword_of_int t : mword 64))).
    (* ---- 0x6e0  c.j 6b0 -- into the landed walk's own tail ---- *)
    iApply (wp_uk_cj N h29 q12 (mword_of_int 0x6e0)
              (mword_of_int 2024 : mword 11) (mword_of_int 0x6b0)
              (16 + (24 + (8 + nn)))
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              with "[] Hrun").
    { iApply (uis_shp_6e0 with "Hcode"). }
    iIntros (h30) "Hrun".
    (* ---- 0x6b0  c.mv a0,s3 -- the landed walk's own tail, unchanged ---- *)
    iApply (wp_uk_cmv N h30 q12 (mword_of_int 0x6b0) a0_idx
              s3_idx (mword_of_int t) (16 + (24 + (8 + nn)))
              ltac:(unfold unot_sp; vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Hs3_q12; symmetry; exact (ushp_mv_val t))
              with "[] Hrun").
    { iApply (uis_shp_6b0 with "Hcode"). }
    iIntros (h31) "Hrun".
    set (me := <[Regidx a0_idx
                 := regval_into_reg (mword_of_int t : mword 64)]> q12).
    assert (Hme : forall r : mword 5, Regidx r <> Regidx a0_idx ->
                    me !!! Regidx r = q12 !!! Regidx r)
      by (intros r Hr; exact (upd_ne q12 (Regidx a0_idx) (Regidx r) _ Hr)).
    (* the whole body, as one preservation fact.  Every one of the three
       calls preserves the callee-saved set, so the chain is the a-register
       writes plus s3 (which the turn overwrites with the PIPE node). *)
    assert (Hkeep : forall r : mword 5, ucallee_saved_idx r = true ->
              Regidx r <> Regidx csp_rs1 -> Regidx r <> Regidx s0_idx ->
              Regidx r <> Regidx s1_idx -> Regidx r <> Regidx s2_idx ->
              Regidx r <> Regidx s3_idx -> Regidx r <> Regidx s4_idx ->
              me !!! Regidx r = m !!! Regidx r).
    { intros r Hr Hsp Hx0 Hx1 Hx2 Hx3 Hx4.
      rewrite (Hme r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq12 r Hx3)
              (Hcsc r Hr)
              (Hr4 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr3 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hr2 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hcsr r Hr)
              (Hg4 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hg3 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hg2 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hcsg r Hr)
              (Hq5 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq4 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq3 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq2 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hq1 r (ushp_cs_ne r a3_idx Hr ltac:(vm_compute; reflexivity)))
              (Hcs1213 r Hr)
              (Hm12 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm11 r (ushp_cs_ne r a0_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm10 r (ushp_cs_ne r a1_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm9 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm8 r (ushp_cs_ne r a2_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm7 r Hx3) (Hcs56 r Hr)
              (Hm5 r (ushp_cs_ne r ra_idx Hr ltac:(vm_compute; reflexivity)))
              (Hm4 r Hx1) (Hm3 r Hx4) (Hm2 r Hx2) (HmA r Hx0) (Hm1 r Hsp).
      reflexivity. }
    assert (Hspe : me !!! Regidx csp_rs1
                   = add_vec_int sp0 (- (8 * Z.of_nat 6))).
    { rewrite (Hme csp_rs1 ltac:(vm_compute; discriminate))
              (Hq12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcsc csp_rs1 ltac:(vm_compute; reflexivity))
              (Hr4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hr3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hr2 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcsr csp_rs1 ltac:(vm_compute; reflexivity))
              (Hg4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hg3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hg2 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcsg csp_rs1 ltac:(vm_compute; reflexivity))
              (Hq5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hq4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hq3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hq2 csp_rs1 ltac:(vm_compute; discriminate))
              (Hq1 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs1213 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm12 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm11 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm10 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm9 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm8 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm7 csp_rs1 ltac:(vm_compute; discriminate))
              (Hcs56 csp_rs1 ltac:(vm_compute; reflexivity))
              (Hm5 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm4 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm3 csp_rs1 ltac:(vm_compute; discriminate))
              (Hm2 csp_rs1 ltac:(vm_compute; discriminate)). exact HspA. }
    (* ---- 0x6b2..0x6c0  the epilogue ---- *)
    iApply (wp_kshp_frame_epi 6 0 [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] (mword_of_int 5 : mword 6)
              (fun i : nat => match i with
                              | 0%nat => 0x6b2 | 1%nat => 0x6b4
                              | 2%nat => 0x6b6 | 3%nat => 0x6b8
                              | 4%nat => 0x6ba | 5%nat => 0x6bc
                              | _ => 0x6be end)
              (mword_of_int 3 : mword 6) sp0
              (mword_of_int (uint sp0 - 8 * Z.of_nat 6)) vals
              (16 + (24 + (8 + nn))) h31 me
              ltac:(cbn [length]; reflexivity)
              Hal8 ltac:(cbn; lia) Hhi
              ltac:(apply uint_moi; cbn; lia)
              Hspe
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(intros i Hi;
                    destruct i as [| [| [| [| [| [| [| i ]]]]]]];
                    cbn in Hi |- *; try reflexivity; lia)
              ltac:(intros i r u Hi;
                    destruct i as [| [| [| [| [| [| i ]]]]]];
                    cbn in Hi; try discriminate Hi;
                    injection Hi as Hr Hu0; subst;
                    (split;
                     [ vm_compute uoff_sdsp; lia
                     | split; [ unfold unot_sp; vm_compute; discriminate
                              | vm_compute; discriminate ] ]))
              ltac:(reflexivity)
              ltac:(ushp_ne_vm)
              with "Hcode [] [] [] Hsl Hloc Hrun").
    { rewrite !big_sepL_cons big_sepL_nil.
      iSplit; [ iApply (uis_shp_6b2 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b4 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b6 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6b8 with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6ba with "Hcode") | ].
      iSplit; [ iApply (uis_shp_6bc with "Hcode") | done ]. }
    { iApply (uis_shp_6be with "Hcode"). }
    { iApply (uis_shp_6c0 with "Hcode"). }
    iIntros (hf) "Hrun".
    iApply ("Hcont" $! t pl pr
              with "[] [] Hpnode Hnodel Hnoder Hcur Hstr Hws Hsy [] [] HM3 Hpay Hrun").
    - iPureIntro. exact Hplsz.
    - iPureIntro. exact Hprsz.
    - iPureIntro.
      apply (ushp_frame_cs [(ra_idx, mword_of_int 5 : mword 6);
               (s0_idx, mword_of_int 4 : mword 6);
               (s1_idx, mword_of_int 3 : mword 6);
               (s2_idx, mword_of_int 2 : mword 6);
               (s3_idx, mword_of_int 1 : mword 6);
               (s4_idx, mword_of_int 0 : mword 6)] vals m me sp0 eq_refl).
      + intros i r u Hi.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; reflexivity.
      + intros q Hq Hqsp Hmiss.
        exact (Hkeep q Hq Hqsp
                 (Hmiss 1%nat s0_idx (mword_of_int 4 : mword 6) eq_refl)
                 (Hmiss 2%nat s1_idx (mword_of_int 3 : mword 6) eq_refl)
                 (Hmiss 3%nat s2_idx (mword_of_int 2 : mword 6) eq_refl)
                 (Hmiss 4%nat s3_idx (mword_of_int 1 : mword 6) eq_refl)
                 (Hmiss 5%nat s4_idx (mword_of_int 0 : mword 6) eq_refl)).
    - iPureIntro.
      rewrite (upd_ne _ (Regidx csp_rs1) (Regidx a0_idx) _
                 ltac:(vm_compute; discriminate)).
      apply ushp_spillback_eq.
      + intros _.
        exact (upd_eq q12 (Regidx a0_idx)
                 (regval_into_reg (mword_of_int t : mword 64))).
      + intros i r u Hi He.
        destruct i as [| [| [| [| [| [| i ]]]]]];
          cbn in Hi; try discriminate Hi;
          injection Hi as Hr Hu0; subst; vm_compute in He; discriminate.
  Qed.

  (* ===================================================================== *)
  (* §3 BOTH PREMISES DISCHARGED: THE TURN, CLOSED                          *)
  (*                                                                        *)
  (* Premise (i) is [UkShPipePex.wp_kshp_parseexec_bar] (the LEFT command's  *)
  (* parse, the re-statement this lane finished) and premise (ii) is         *)
  (* [UkShPipeCmd.wp_kshp_pipecmd] (the constructor, walkable now that its   *)
  (* catalog row exists).  So [parsepipe] at the pipe shape is a closed      *)
  (* walk: the only things it still takes are the LINE, the two allocator    *)
  (* links, and the exit payload every parser walk takes.                    *)
  (* ===================================================================== *)

  Lemma ushq_pex_left_holds {Pex : iProp Σ} (dq dw dv : dfrac)
      (ps s0 : Z) (len gp ge : nat) (f : nat -> bv 8)
      (args : list (nat * nat)) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    ⊢ ushq_pex_left dq dw dv ps s0 len gp f args Pex
        (16 + (24 + (8 + nn))).
  Proof using .
    intros Hm01 Hpq Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros (h m rpc)
      "%Ha0 %Ha1 %Erpc #Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hrun Hcont".
    rewrite <- Erpc.
    iApply (UkShPipePex.wp_kshp_parseexec_bar N UM0 UM1 Hm01 h m dq dw dv
              ps s0 len 0%nat f (mword_of_int s0) args gp ge nn
              Ha0 Ha1 ltac:(lia) ltac:(f_equal; lia)
              Hpq Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay Hrun").
    iIntros (pl) "%Hplsz Hnodel Hcur Hstr Hws Hsy".
    iIntros (h' m') "%Hcs %Ha0' HM1 Hpay Hrun".
    iApply ("Hcont" $! pl with "[] Hnodel Hcur Hstr Hws Hsy [] [] HM1 Hpay Hrun").
    - iPureIntro. exact Hplsz.
    - iPureIntro. exact Hcs.
    - iPureIntro. exact Ha0'.
  Qed.

  (* THE TURN, with nothing left to instantiate. *)
  Corollary wp_kshp_parsepipe_bar_closed {Pex : iProp Σ} (h : CpuId)
      (m : regfile) (dq dw dv : dfrac) (ps s0 : Z) (len gp ge : nat)
      (f : nat -> bv 8) (args : list (nat * nat)) (nn : nat) :
    ushp_malloc_ty UM0 UM1 ->
    ushp_malloc_ty UM2 UM3 ->
    m !!! Regidx a0_idx = mword_of_int ps ->
    m !!! Regidx a1_idx = mword_of_int (s0 + Z.of_nat len) ->
    ushq_pipe len f gp ge ->
    ushs_toks len f gp 0%nat args ->
    (0 < length args)%nat ->
    (length args < 10)%nat ->
    0 <= s0 -> s0 + Z.of_nat len < Z64 ->
    0 < ps -> ps mod 8 = 0 -> ps + 8 < Z64 ->
    shp_code γt -∗
    shp_rodata γt -∗
    uword γd ps (mword_of_int s0) -∗
    ustr γd dq s0 len f -∗
    ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
    ustr γd dv ushp_symbols 7 ushp_sym_f -∗
    UM0 -∗
    □ (Pex -∗ ukn_pay N (-1)) -∗
    Pex -∗
    urun N h m (mword_of_int ShSyms.parsepipe)
      (6 + (16 + (24 + (8 + nn)))) -∗
    (∀ t pl pr : Z,
       ⌜ pl + 168 < Z64 ⌝ -∗
       ⌜ pr + 168 < Z64 ⌝ -∗
       ushp_pipe_node t pl pr -∗
       ushp_exec_at s0 pl args -∗
       ushp_exec_at s0 pr [(S (S gp), ge)] -∗
       uword γd ps (mword_of_int (s0 + Z.of_nat len)) -∗
       ustr γd dq s0 len f -∗
       ustr γd dw ushp_whitespace 5 ushp_ws_f -∗
       ustr γd dv ushp_symbols 7 ushp_sym_f -∗
         ∀ (h' : CpuId) (m' : regfile),
           ⌜ ucallee_saved m m' ⌝ -∗
           ⌜ m' !!! Regidx a0_idx = mword_of_int t ⌝ -∗
           UM3 -∗
           Pex -∗
           urun N h' m' (ret_pc (m !!! Regidx ra_idx))
             (6 + (16 + (24 + (8 + nn)))) -∗
           WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof using ushp_malloc_ok12.
    intros Hm01 Hm23 Ha0 Ha1 Hpq Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz.
    iIntros "#Hcode #Hro Hcur Hstr Hws Hsy HM0 #Hpx Hpay Hrun Hcont".
    iApply (wp_kshp_parsepipe_bar h m dq dw dv ps s0 len gp ge f args nn
              Ha0 Ha1 Hpq Hs0 Hs64 Hps0 Hps8 Hpssz
              with "Hcode Hro Hcur Hstr Hws Hsy HM0 Hpx Hpay [] [] Hrun Hcont").
    - iApply (ushq_pex_left_holds dq dw dv ps s0 len gp ge f args nn
                Hm01 Hpq Htoks Hpos Hlen Hs0 Hs64 Hps0 Hps8 Hpssz).
    - iApply (ushq_pipecmd_call_holds nn Hm23).
  Qed.

End UkShPipeCm.
