(* ===================================================================== *)
(* UkShRedirBody.v -- SH'S BODY AT THE REDIRECT LINE, and the THREE-WAY   *)
(* CASE the file application's command loop turns on (lane SH-CHILD;      *)
(* design/app-file.md §5.1, SKELETON's obligation 18).                    *)
(*                                                                        *)
(* WHAT THE LANE FOUND, and it is what decides this file's shape: sh's     *)
(* body reads its line EXACTLY ONCE, at 0x97a, and only to see that the    *)
(* first byte is not 'c'.  Everything else the walk does with the line is  *)
(* to hand it to the CHILD's law.  So [UkShFork.wp_kshm_body_at] is        *)
(* abstract in the line shape, [wp_kshm_body_redir] below is that lemma at *)
(* the redirect shape and costs ONE fact ([ushs_lp0]), and the three-way   *)
(* case is not three walks but two plus cat's.                             *)
(*                                                                        *)
(* THE THREE ARMS.                                                         *)
(*   [LEcho ws]  -- [echo a b], first byte 'e': [UkShFork.wp_kshm_body_at] *)
(*     at [UkSh.ush_line_is], i.e. [UkShFork.ushf_body_law_echo].          *)
(*   [LEchoF ws] -- [echo a b > f], first byte 'e' TOO (the redirect is a  *)
(*     suffix): the SAME walk, at [ushs_lp], closing on the redirect       *)
(*     child's law.                                                       *)
(*   [LCat]      -- [cat f], first byte 'c': the [bne] at 0x97a is NOT     *)
(*     taken and control goes into the three-byte [cd] test, a walk this   *)
(*     tree does not have ([UkShCd.wp_kshc_cd] was deleted when the        *)
(*     disciplined line made the arm unreachable).  It is [Hcat_body], a   *)
(*     NAMED HYPOTHESIS at exactly the law the other two arms are, and the *)
(*     only thing in this file that is owed.                               *)
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
Require Import UserHeap UkRun UkRunLeaf.
Require Import FdSlots UserFd.
Require Import UCodeShK UCodeShP.
Require Import LineWords.
Require Import EchoDisc.
Require Import FileDisc.        (* [uline]: the three lines the file
                                   discipline admits *)
Require Import UkSh.
Require Import UkShParse.
Require Import UkShDiag.
Require Import UkShMalloc.
Require Import UkShLoop.
Require Import UkShParseCmd.    (* [ushp_setb] / [ushp_nulfold]: the cut *)
Require Import UkShRedirPc.     (* [ushs_nulcut]: the redirect line's cut *)
Require Import UkShWords.       (* [wl_cut_in] / [wl_cut_end] *)
Require Import UkShEcho.        (* [echo_argv_bytes] and the exec arm *)
Require Import UkShRedir.       (* [ush_open_call]: the open as a premise *)
Require Import UkShRedirSeam.   (* [wp_kshm_child_alloc_redir]: the walk *)
Require Import UShLexRedir.     (* [ush_line_toks_holds_redir] *)
Require Import UserPerm.        (* [usz_ok] *)
Require Import PipeNames.
Require Import UkShRedirLine.   (* [ushs_line_is] and the typed bridge *)
Require Import UkShFork.        (* [ushf_body_law] / [wp_kshm_body_at] *)
Require Import CtxIdDefs.
Require Import UexecSG.
Require Import UserCwd.
Require Import UserChildren.
Require Import UserPerm.        (* [usz_ok] *)
Require Import UserPtTree.
Require Import Xv6Cameras.
Local Open Scope Z_scope.
Import Defs.

Section UkShRedirBody.
  Context `{!riscvGS Σ}.
  Context `{!ufdG Σ}.
  Context `{GEN : GenId} `{XI : CurCtx}.
  Context `{!ghost_varG Σ Z}.
  Context `{!ghost_varG Σ (gset gname)}.
  Context (N : uk_names Σ).
  Context `{Hpay : !ukn_const N}.
  Context `{!uartGhostG Σ}.
  Context (γp : gname).
  Context (T : iProp Σ).
  Context `{HT : !Persistent T}.
  Context (Wc : list (bv 8) -> nat -> iProp Σ).
  Context (Wb : list (bv 8) -> iProp Σ).
  Context (Pm : list (bv 8) -> iProp Σ).
  Local Notation γt := (ukn_t N).
  Local Notation γd := (ukn_d N).
  Local Notation γs := (ukn_s N).
  Local Notation γfd := (ukn_fd N).
  Local Notation γcwd := (ukn_cwd N).
  Local Notation γch := (ukn_ch N).
  Context `{!ctokG Σ}.
  Context {SG : uexecSG Σ}.
  Context `{PS : uprogSG Σ}.
  Hypothesis Hpsok_free : forall k : Z, free_num k -> psok k.
  Context `{HWct : forall (I : list (bv 8)) (p : nat), Timeless (Wc I p)}.

  Local Notation s1_idx := (mword_of_int 9 : mword 5).
  Local Notation a5_idx := (mword_of_int 15 : mword 5).
  Local Notation ushl_dat := (UkShLoop.ushl_dat γd).
  Local Notation ushl_head := (UkShLoop.ushl_head N γp T Wc Wb Pm).

  (* =================================================================== *)
  (*  §1  THE REDIRECT LINE, AS A LINE SHAPE                              *)
  (*                                                                     *)
  (*  The file name is existential because the WALK never reads it: what  *)
  (*  reads it is the child, off its own copy of the line.  At the file   *)
  (*  application it is [FileDisc.fname_f] and [ushs_lp_of_at] says so.   *)
  (* =================================================================== *)
  Definition ushs_lp (ws : list (list (bv 8))) (g : nat -> bv 8)
      (k len : nat) : Prop :=
    exists file : list (bv 8), UkShRedirLine.ushs_line_is ws file g k len.

  Lemma ushs_lp0 (ws : list (list (bv 8))) (g : nat -> bv 8) (k len : nat) :
    ushs_lp ws g k len -> bv_unsigned (g k) = 101%Z.
  Proof using .
    intros [ file Hl ].
    exact (UkShRedirLine.ushs_line_is_byte0 ws file g k len Hl).
  Qed.

  Lemma ushs_lp_of_at (ws : list (list (bv 8))) (f : nat -> bv 8)
      (k len : nat) :
    UkSh.ush_line_at (LEchoF ws) f k len ->
    ushs_lp ws (fun j : nat => f (k + j)%nat) 0%nat len.
  Proof using .
    intro H. exists fname_f.
    exact (UkShRedirLine.ushs_line_is_shift ws fname_f f k len
             (UkShRedirLine.ushs_line_is_of_at ws f k len H)).
  Qed.

  (* =================================================================== *)
  (*  §2  THE BODY AT THE REDIRECT LINE (deliverable 2)                   *)
  (*                                                                     *)
  (*  [UkShFork.wp_kshm_body_at] at [ushs_lp].  The prefix walk -- fork1, *)
  (*  the diagnostic, the [cd] refutation -- is SHARED with the echo      *)
  (*  line's, character for character, because the refutation reads only  *)
  (*  the first byte and both lines carry the same [EchoDisc.line_ok].    *)
  (*  What differs is the CHILD's law, and that is the parameter.         *)
  (* =================================================================== *)
  Lemma wp_kshm_body_redir
      (h : CpuId) (m : regfile) (f : nat -> bv 8) (k len : nat)
      (ws : list (list (bv 8))) (file : list (bv 8))
      (sz : Z) (l : list fdstate) (n : nat) :
    UkSh.ush_regs m ->
    m !!! Regidx s1_idx = mword_of_int (sh_buf + Z.of_nat k) ->
    m !!! Regidx a5_idx = mword_of_int (bv_unsigned (f k)) ->
    (forall j : nat, (j < len)%nat -> f (k + j)%nat <> ubyte0) ->
    f (k + len)%nat = ubyte0 ->
    (k + len < sh_nbuf)%nat ->
    (* THE LINE IS THE REDIRECT SHAPE *)
    UkShRedirLine.ushs_line_is ws file (fun j : nat => f (k + j)%nat)
      0%nat len ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall n' : nat,
       ⊢ UkSh.ush_at N γp n' -∗
         ∃ I : list (bv 8), ⌜length I = n'⌝ ∗ UkSh.ush_lease N γp T Pm I) ->
    (forall I : list (bv 8),
       ⊢ Pm I -∗ Wb I -∗ UkSh.ush_at N γp (length I)) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkSh.ush_gen_slot N T -∗
    ushl_head l sz -∗
    UCodeShK.shk_code γt -∗
    UCodeShK.shk_rodata γt -∗ UCodeShP.shp_code γt -∗ UkSh.ush_jtab γt -∗
    UkShFork.ushf_kill_law Wc -∗
    (* THE REDIRECT CHILD'S LAW, which is [sh_redir_child_law] below *)
    UkShFork.ushf_child_law_at Wc ushs_lp -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    ⌜ UkSh.ush_fd0p l ⌝ -∗
    UkSh.ush_bstate N γp T Wc Wb Pm l ws -∗
    ushl_dat -∗ usz γs sz -∗
    ubytes γd sh_buf sh_nbuf f -∗
    urun N h m (mword_of_int 0x97a) (16 + (80 + n)) -∗
    WP (Loop : expr riscv_lang).
  Proof using HT HWct Hpay Hpsok_free.
    intros Hregs Hs1 Ha5 Hnn Hnul Hkl Hline Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl.
    exact (UkShFork.wp_kshm_body_at N γp T Wc Wb Pm Hpsok_free ushs_lp
             h m f k len ws sz l n ushs_lp0 Hregs Hs1 Ha5 Hnn Hnul Hkl
             (ex_intro _ file Hline) Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl).
  Qed.

  (* =================================================================== *)
  (*  §2b  THE ARGV BYTES AT THE REDIRECT CUT (lane SH-CHILD-2, item 3)   *)
  (*                                                                     *)
  (*  [UkShEcho.echo_argv_bytes_of_line_holds] is this at the SYMBOL-FREE *)
  (*  cut, [ushp_nulfold (echo_toks ws) (ushp_ext len f)].  The redirect  *)
  (*  child's tree is built over [UkShRedirPc.ushs_nulcut], which is that *)
  (*  cut with ONE MORE terminator -- [nulterminate]'s REDIR arm zeroes   *)
  (*  the file name's end too -- and SH-LEX-REDIR's ruling makes the      *)
  (*  token list the SAME ([wl_toks ws], echo's own).  So the whole proof *)
  (*  is: the extra store is at [fe], every argument byte and every       *)
  (*  argument's terminator is below [|wl_body ws| < fe], and underneath  *)
  (*  it the two cuts are the same function.                             *)
  (* =================================================================== *)
  Lemma echo_argv_bytes_of_redir (ws : list (list (bv 8)))
      (file : list (bv 8)) (f : nat -> bv 8) (k len fe : nat) :
    UkShRedirLine.ushs_line_is ws file f k len ->
    fe = (length (wl_body ws) + 3 + length file)%nat ->
    UkShEcho.echo_argv_bytes ws
      (UkShRedirPc.ushs_nulcut (wl_toks ws) len
         (fun j : nat => f (k + j)%nat) fe).
  Proof using .
    intros Hl Hfe. pose proof Hl as HL.
    destruct HL as (Hok & Hfile & Hlen & Hbody & _ & _ & _ & _ & _).
    assert (Hfpos : (0 < length file)%nat)
      by (destruct Hfile as [ Hne _ ]; destruct file; [ done | cbn; lia ]).
    split.
    - intros i j Hi Hj.
      pose proof (line_ok_at ws i Hok Hi) as Hw.
      rewrite /UkShEcho.echo_alen in Hj.
      assert (Hle : (UkShEcho.echo_off ws i + (j + 1)
                     <= 0 + length (wl_body ws))%nat)
        by exact (wl_off_le_body ws 0%nat i (ws !!! i) (j + 1)%nat Hw
                    ltac:(lia)).
      rewrite /UkShEcho.echo_off in Hle |- *.
      rewrite /UkShRedirPc.ushs_nulcut /ushp_setb.
      rewrite (proj2 (Nat.eqb_neq (wl_off 0%nat ws i + j)%nat fe)
                 ltac:(lia)).
      rewrite (wl_cut_in ws (fun x : nat => f (k + x)%nat) len i
                 (ws !!! i) j Hw Hj ltac:(lia)).
      rewrite (Hbody (wl_off 0%nat ws i + j)%nat ltac:(lia)).
      symmetry.
      exact (wl_lta_app_l (wl_body ws) [wl_nl]
               (wl_off 0%nat ws i + j)%nat ltac:(lia)).
    - intros i Hi.
      pose proof (line_ok_at ws i Hok Hi) as Hw.
      assert (Hle : (UkShEcho.echo_off ws i + length (ws !!! i)
                     <= 0 + length (wl_body ws))%nat)
        by exact (wl_off_le_body ws 0%nat i (ws !!! i) (length (ws !!! i))
                    Hw ltac:(lia)).
      rewrite /UkShEcho.echo_off /UkShEcho.echo_alen in Hle |- *.
      rewrite /UkShRedirPc.ushs_nulcut /ushp_setb.
      rewrite (proj2 (Nat.eqb_neq
                        (wl_off 0%nat ws i + length (ws !!! i))%nat fe)
                 ltac:(lia)).
      exact (wl_cut_end ws (fun x : nat => f (k + x)%nat) len i
               (ws !!! i) Hw).
  Qed.

  (* =================================================================== *)
  (*  §3  THE REDIRECT CHILD'S LAW (SKELETON's obligation 18)             *)
  (*                                                                     *)
  (*  [UShRound.sh_redir_child_law] is [UkShFork.ushf_child_law]'s body   *)
  (*  with [UkSh.ush_line_is] replaced by [UkShRedirLine.ushs_line_is],   *)
  (*  the file name bound OUTSIDE.  That is this file's [ushf_child_law_at *)
  (*  ushs_lp] with the existential pulled out, and the two are           *)
  (*  interderivable -- [sh_redir_child_law_at] is the direction the body  *)
  (*  above consumes, which is the one [UShRound] owes.                    *)
  (* =================================================================== *)
  Definition sh_redir_child_law : iProp Σ :=
    (□ (∀ (N' : uk_names Σ) (h : CpuId) (m : regfile) (dw dv : dfrac)
          (s0 : Z) (len : nat) (ws : list (list (bv 8)))
          (file : list (bv 8)) (fb : nat -> bv 8)
          (sz : Z) (ld : list fdstate) (n : nat) (I : list (bv 8)),
          ⌜ ukn_pay N' = (fun _ : Z => UkShFork.ushf_wq Wc I) ⌝ -∗
          ⌜ m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ⌝ -∗
          ⌜ UkShRedirLine.ushs_line_is ws file fb 0%nat len ⌝ -∗
          ⌜ ws = last_ws I ⌝ -∗
          ⌜ 0 < s0 ⌝ -∗ ⌜ s0 + Z.of_nat len + 1 < Z64 ⌝ -∗
          ⌜ s0 + Z.of_nat len < 2 ^ 38 ⌝ -∗
          ⌜ 8344 <= sz ⌝ -∗ ⌜ UserPtTree.pgroundup sz = sz ⌝ -∗
          ⌜ usz_ok (sz + 65536) ⌝ -∗
          ⌜ UkSh.ush_fd0c ld /\ UkSh.ush_fd1p ld /\ UkSh.ush_fd2p ld ⌝ -∗
          UCodeShK.shk_code (ukn_t N') -∗
          UCodeShP.shp_code (ukn_t N') -∗
          UCodeShP.shp_rodata (ukn_t N') -∗
          UkSh.ush_jtab (ukn_t N') -∗
          ustr (ukn_d N') (DfracOwn 1) s0 len fb -∗
          ustr (ukn_d N') dw ushp_whitespace 5 ushp_ws_f -∗
          ustr (ukn_d N') dv ushp_symbols 7 ushp_sym_f -∗
          UserFd.ustd (ukn_fd N') ld -∗
          UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
          UserChildren.uch_any (ukn_ch N') -∗
          UkShMalloc.ushm_fresh N' sz -∗
          Wc I 3%nat -∗
          urun N' h m (mword_of_int 0x9c0)
            (60 + (8 + (UkShDiag.ush_Dg + n))) -∗
          WP (Loop : expr riscv_lang)))%I.

  Global Instance sh_redir_child_law_persistent :
    Persistent sh_redir_child_law.
  Proof using . rewrite /sh_redir_child_law. apply _. Qed.

  (* the two shapes, one step apart: the walk takes the file name out of
     the line fact, the law binds it. *)
  Lemma ushf_child_law_at_of_redir :
    sh_redir_child_law -∗ UkShFork.ushf_child_law_at Wc ushs_lp.
  Proof using .
    iIntros "#Hl". rewrite /UkShFork.ushf_child_law_at.
    iIntros "!>" (N' h m dw dv s0 len ws g sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hws Hsy Hstd Hcwd Hch HM Hcr Hrun".
    destruct Hline as [ file Hline ].
    iApply ("Hl" $! N' h m dw dv s0 len ws file g sz ld n I
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hcode Hpcode Hpro Hjt Hstr Hws Hsy Hstd Hcwd Hch HM
                    Hcr Hrun");
      [ exact Hpeq | exact Hs1 | exact Hline | exact Hlws
      | exact Hs0 | exact Hs64 | exact Hs38 | exact Hszlo | exact Hszal
      | exact Hszok | exact Hrows ].
  Qed.

  (* ...and the other way, so the two shapes are interderivable and a
     supplier may prove whichever is convenient. *)
  Lemma sh_redir_child_law_of_at :
    UkShFork.ushf_child_law_at Wc ushs_lp -∗ sh_redir_child_law.
  Proof using .
    iIntros "#Hl". rewrite /sh_redir_child_law.
    iIntros "!>" (N' h m dw dv s0 len ws file g sz ld n I)
      "%Hpeq %Hs1 %Hline %Hlws %Hs0 %Hs64 %Hs38 %Hszlo %Hszal %Hszok
       %Hrows #Hcode #Hpcode #Hpro #Hjt Hstr Hws Hsy Hstd Hcwd Hch HM Hcr Hrun".
    iApply ("Hl" $! N' h m dw dv s0 len ws g sz ld n I
              with "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%]
                    Hcode Hpcode Hpro Hjt Hstr Hws Hsy Hstd Hcwd Hch HM
                    Hcr Hrun");
      [ exact Hpeq | exact Hs1 | by exists file | exact Hlws
      | exact Hs0 | exact Hs64 | exact Hs38 | exact Hszlo | exact Hszal
      | exact Hszok | exact Hrows ].
  Qed.

  (* =================================================================== *)
  (*  §3b  THE REDIRECT CHILD'S WALK (lane SH-CHILD-2, item 4)            *)
  (*                                                                     *)
  (*  From 0x9c0 to the exec, at the line the fork lent it.  Two halves:  *)
  (*  [UkShRedirSeam.wp_kshm_child_alloc_redir] -- parse, close(1),       *)
  (*  open(file), and out at runcmd with the EXEC sub-tree and the        *)
  (*  receipt -- and then [UkShEcho.wp_kshr_exec_echo_at_holds] at the    *)
  (*  fd-1 row the open left, which is the ONE thing echo's arm had to    *)
  (*  become abstract in.                                                 *)
  (*                                                                     *)
  (*  THE LEND PAYS EVERY EXIT.  The child's payload is                   *)
  (*  [UkShFork.ushf_wq Wc I] and the walk can leave at three places --   *)
  (*  the parser's NULL store, the open's failure and the exec's -- so    *)
  (*  the lend [Wc I 3] goes in and the law that turns it into the        *)
  (*  payload is one [iLeft].                                            *)
  (*                                                                     *)
  (*  THE OPEN AND THE SUPPLY ARE PREMISES, not hypotheses: both are the  *)
  (*  APPLICATION's ([UShRound.Hopen_hand] and K1's entry), and both come *)
  (*  out of the credential family the fork lent -- which is why they are *)
  (*  resources here and not [Hypothesis]es.                             *)
  (* =================================================================== *)
  Definition ushs_fd1f (ty : fdtype) (l : list fdstate) : Prop :=
    l !! 1%nat = Some (FdOpen false true ty).

  Lemma wp_kshm_child_file_redir
      (N' : uk_names Σ) (Hc : ukn_const N')
      (h : CpuId) (m : regfile) (dw dv : dfrac)
      (s0 : Z) (len : nat) (ws : list (list (bv 8))) (file : list (bv 8))
      (fb : nat -> bv 8) (sz : Z) (ld : list fdstate) (st1 : fdstate)
      (n : nat) (I : list (bv 8)) (K : fdtype -> iProp Σ) :
    ukn_pay N' = (fun _ : Z => UkShFork.ushf_wq Wc I) ->
    m !!! Regidx s1_idx = (mword_of_int s0 : mword 64) ->
    UkShRedirLine.ushs_line_is ws file fb 0%nat len ->
    0 < s0 -> s0 + Z.of_nat len + 1 < Z64 -> s0 + Z.of_nat len < 2 ^ 38 ->
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    ld !! 1%nat = Some st1 ->
    st1 <> FdClosed ->
    (forall (rb wb : bool) (gn : PipeNames.pipe_names),
       st1 <> FdOpen rb wb (FdPipe gn)) ->
    UkSh.ush_fd2p ld ->
    UkSh.sh_deps -∗
    UCodeShK.shk_code (ukn_t N') -∗
    UkSh.ush_jtab (ukn_t N') -∗
    UCodeShP.shp_code (ukn_t N') -∗
    UCodeShP.shp_rodata (ukn_t N') -∗
    ustr (ukn_d N') (DfracOwn 1) s0 len fb -∗
    ustr (ukn_d N') dw ushp_whitespace 5 ushp_ws_f -∗
    ustr (ukn_d N') dv ushp_symbols 7 ushp_sym_f -∗
    UserFd.ustd (ukn_fd N') ld -∗
    UserCwd.ucwd (ukn_cwd N') FsImg.ROOTINO -∗
    UserChildren.uch_any (ukn_ch N') -∗
    UkShMalloc.ushm_fresh N' sz -∗
    (* the open, as the application's CALL premise *)
    UkShRedir.ush_open_call N' FsImg.ROOTINO
      (s0 + Z.of_nat (S (S (length (wl_body ws) + 1)))) 1537
      (<[1%nat := FdClosed]> ld) K -∗
    (* ...and the child's exec supply AT THE FILE the open returned *)
    (∀ ty : fdtype,
       K ty -∗
       UkShEcho.sh_exec_sup_echo_at (ushs_fd1f ty) ws
         (fun _ : Z => UkShFork.ushf_wq Wc I) (Wc I 3%nat)) -∗
    (* ...the diagnostic's law at the two ends of the credential *)
    UkShDiag.ush_execfail_law (Wc I 3%nat) (Wc I 0%nat) -∗
    Wc I 3%nat -∗
    urun N' h m (mword_of_int 0x9c0)
      (68 + (8 + (UkShDiag.ush_Dg + n))) -∗
    WP (Loop : expr riscv_lang).
  Proof using Hpsok_free.
    intros Hpeq Hs1 Hline Hs0 Hs64 Hs38 Hszlo Hszal Hszok
           Hst1 Hne Hnp Hfd2.
    iIntros "#Hdp #Hcode #Hjt #Hpcode #Hpro Hstr Hws Hsy Hstd Hcwd Hch HM
             Hopen Hsup #Hxl Hcr Hrun".
    (* the parser's premises, off the line (lane SH-LEX-REDIR) *)
    destruct (UShLexRedir.ush_line_toks_holds_redir ws file fb 0%nat len
                Hline) as (Hred & Htoks & Hpos & Htlen).
    pose proof (proj1 Hline) as Hok.
    (* the lend pays every exit *)
    iAssert (□ (Wc I 3%nat -∗ ukn_pay N' (-1)))%I as "#Hpxw".
    { iIntros "!> Hc". rewrite Hpeq /UkShFork.ushf_wq. iLeft. iExact "Hc". }
    (* the ledger's length, for the two inserts *)
    pose proof (lookup_lt_Some ld 1%nat st1 Hst1) as Hlen1.
    iApply (UkShRedirSeam.wp_kshm_child_alloc_redir N' (Hpay := Hc)
              Hpsok_free h m dw dv s0 FsImg.ROOTINO len fb (wl_toks ws)
              (length (wl_body ws) + 1)%nat
              (length (wl_body ws) + 3 + length file)%nat
              sz ld st1 n K (Wc I 3%nat)
              Hs1 Hred Htoks Hpos Htlen Hs0 Hs64 Hs38 Hst1 Hne Hnp
              Hszlo Hszal Hszok
              with "Hdp Hcode Hjt Hpcode Hpro Hstr Hws Hsy Hstd Hcwd HM
                    Hopen Hpxw Hcr Hrun").
    iIntros (hf mf q ty) "%Ha0f #Hsub Hstd Hcwd HK HM2 Hcr Hrun".
    (* the two rows the exec arm reads off the ledger the open left *)
    assert (Hfd1' : ushs_fd1f ty
              (<[1%nat := FdOpen false true ty]>
                 (<[1%nat := FdClosed]> ld))).
    { rewrite /ushs_fd1f. apply list_lookup_insert.
      rewrite length_insert. exact Hlen1. }
    assert (Hfd2' : UkSh.ush_fd2p
              (<[1%nat := FdOpen false true ty]>
                 (<[1%nat := FdClosed]> ld))).
    { destruct Hfd2 as [ rb Hrb ]. exists rb.
      rewrite list_lookup_insert_ne; [ | lia ].
      rewrite list_lookup_insert_ne; [ exact Hrb | lia ]. }
    (* the break, out of the free list the parse left *)
    iDestruct "HM2" as (R') "[_ HM2]".
    rewrite /UkShMalloc.ushm_one.
    iDestruct "HM2" as (cq) "(_ & _ & _ & _ & _ & Hsz)".
    (* the argv bytes at the REDIRECT cut *)
    pose proof (echo_argv_bytes_of_redir ws file fb 0%nat len
                  (length (wl_body ws) + 3 + length file)%nat Hline eq_refl)
      as Hbytes.
    replace (UkShDiag.ush_Dg + (70 + n))%nat
      with (6 + (2 + (UkShDiag.ush_Dg + (62 + n))))%nat by lia.
    iApply (UkShEcho.wp_kshr_exec_echo_at_holds (ushs_fd1f ty) ws
              (fun _ : Z => UkShFork.ushf_wq Wc I)
              (Wc I 3%nat) (Wc I 0%nat) N' Hc hf mf q (sz + 65536) s0
              (UkShRedirPc.ushs_nulcut (wl_toks ws) len
                 (fun j : nat => fb (0 + j)%nat)
                 (length (wl_body ws) + 3 + length file)%nat)
              (<[1%nat := FdOpen false true ty]> (<[1%nat := FdClosed]> ld))
              (62 + n)%nat
              Hok Hpeq Ha0f Hbytes Hfd1' Hfd2'
              with "Hcode [HK Hsup] Hxl [] Hjt Hsub Hsz Hstd Hcwd Hch Hcr
                    Hrun").
    - iApply ("Hsup" $! ty with "HK").
    - (* a failed exec's child exits on the block written up to its prompt *)
      iIntros "!> Hc". rewrite Hpeq /UkShFork.ushf_wq. iRight. iExact "Hc".
  Qed.

  (* =================================================================== *)
  (*  §4  THE THREE-WAY CASE (deliverable 3)                              *)
  (*                                                                     *)
  (*  [D] is the file era's: every constructor of [FileDisc.uline].  The  *)
  (*  case is on the CONSTRUCTOR and nothing else -- the era's tag law     *)
  (*  ([FileOut.ftag], [FileDisc.disc_f]) is what says the buffer holds    *)
  (*  one of them, and this is where that turns into a walk.              *)
  (* =================================================================== *)
  Definition ush_line_file (l : uline) : Prop := True.

  (* ---- THE CAT ARM, NAMED (lane CAT-GEOM's, not this one's) ---------- *)
  (*  [cat f] begins with 'c', so 0x97a's [bne] is NOT taken and the walk  *)
  (*  goes into the three-byte [cd] test -- which this tree deleted with   *)
  (*  [UkShCd.wp_kshc_cd].  What is owed is that walk, at exactly the law  *)
  (*  the other two arms are: the body at [l = LCat], closing on cat's     *)
  (*  own exec.  Stated, not proved.                                      *)
  Hypothesis Hcat_body :
    forall sz : Z,
      8344 <= sz ->
      UserPtTree.pgroundup sz = sz ->
      usz_ok (sz + 65536) ->
      ⊢ UkShFork.ushf_body_law N γp T Wc Wb Pm
          (fun l : uline => l = LCat) sz.

  Lemma ushf_body_law_file (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law Wc -∗
    sh_redir_child_law -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkShFork.ushf_body_law N γp T Wc Wb Pm ush_line_file sz.
  Proof using HT HWct Hpay Hpsok_free Hcat_body.
    intros Hszlo Hszal Hszok Hwbl.
    iIntros "#Hkl #Hchl #Hred #Hplaw".
    iPoseProof (UkShFork.ushf_body_law_echo N γp T Wc Wb Pm Hpsok_free sz
                  Hszlo Hszal Hszok Hwbl with "Hkl Hchl Hplaw") as "#Hecho".
    iPoseProof (Hcat_body sz Hszlo Hszal Hszok) as "#Hcat".
    iPoseProof (ushf_child_law_at_of_redir with "Hred") as "#Hchr".
    rewrite /UkShFork.ushf_body_law.
    iIntros "!>" (lu h m f k len l n)
      "%Hd %Hlat %Hregs %Hs1 %Ha5 %Hnn %Hnul %Hkl2 %Hpm1 %Hpmwb %Hfd0
       #Hgen #Hcode #Hjt Hhead Hstd Hdat Hsz Hbuf Hrun".
    destruct lu as [ ws | ws | ].
    - (* [echo a b] -- the landed walk *)
      iApply ("Hecho" $! (LEcho ws) h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ by exists ws | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
    - (* [echo a b > f] -- the SAME walk at the redirect child's law *)
      iDestruct (UkSh.ush_jtab_ro γt with "Hjt") as "#Hro".
      iApply (UkShFork.wp_kshm_body_at N γp T Wc Wb Pm Hpsok_free ushs_lp
                h m f k len ws sz l n ushs_lp0 Hregs Hs1 Ha5 Hnn Hnul Hkl2
                (ushs_lp_of_at ws f k len Hlat)
                Hszlo Hszal Hszok Hpm1 Hpmwb Hwbl
                with "Hgen Hhead Hcode Hro [] Hjt Hkl Hchr Hplaw [%] Hstd
                      Hdat Hsz Hbuf Hrun").
      + iApply (UkShFork.ushf_code_shp with "Hcode").
      + exact Hfd0.
    - (* [cat f] -- the 'c' arm, owed *)
      iApply ("Hcat" $! LCat h m f k len l n with
                "[%] [%] [%] [%] [%] [%] [%] [%] [%] [%] [%] Hgen Hcode Hjt
                 Hhead Hstd Hdat Hsz Hbuf Hrun");
        [ reflexivity | exact Hlat | exact Hregs | exact Hs1 | exact Ha5
        | exact Hnn | exact Hnul | exact Hkl2 | exact Hpm1 | exact Hpmwb
        | exact Hfd0 ].
  Qed.

  (* ...AND THE OBLIGATION ITSELF, at the file era's lines.  This is what
     [UShRound.sh_round_holds_file] applies. *)
  Lemma ushf_rest_of_body_file (sz : Z) :
    8344 <= sz ->
    UserPtTree.pgroundup sz = sz ->
    usz_ok (sz + 65536) ->
    (forall I : list (bv 8), ⊢ Wc I 3%nat -∗ Wc I 0%nat) ->
    UkShFork.ushf_kill_law Wc -∗
    UkShFork.ushf_child_law Wc -∗
    sh_redir_child_law -∗
    UkShDiag.ush_panic_law Wc Wb -∗
    UkSh.ush_rest_l_at N γp T Wc Wb Pm ush_line_file
      (UkShLoop.ushl_R N sz).
  Proof using HT HWct Hpay Hpsok_free Hcat_body.
    intros Hszlo Hszal Hszok Hwbl.
    iIntros "#Hkl #Hchl #Hred #Hplaw".
    iApply (UkShFork.ushf_rest_of_body_at N γp T Wc Wb Pm Hpsok_free
              ush_line_file sz Hszlo Hszal Hszok Hwbl).
    iApply (ushf_body_law_file sz Hszlo Hszal Hszok Hwbl
              with "Hkl Hchl Hred Hplaw").
  Qed.

End UkShRedirBody.
