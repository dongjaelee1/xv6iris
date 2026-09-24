(* ===================================================================== *)
(* PipesFire.v -- THE N-STAGE ROUND'S COMMITS, ADMITTED BY THE MODEL     *)
(* (design claude-notes/design/pipes-general.md SS2.2, SS3.2; cut C7).   *)
(*                                                                        *)
(* Pure.  The family ([PipeBothN]) reads the committed sources with every *)
(* uncommitted writer SILENT and asks that vector to be a complete run    *)
(* ([PipeBothNPure.runS]); a commit is admitted iff the vector with the   *)
(* committer's source is still one, or a committed writer's deposit       *)
(* refutes the committer's ([EXf]).  This file is that question at the    *)
(* pipeline [echo .. | cat | .. | cat] of [n] cats, read off the VALUES:  *)
(*                                                                        *)
(*   [real] / [realT]  a vector is a run / a terminal vector iff its      *)
(*                     values are what the stages may print and the one  *)
(*                     data demand -- the last cat's content -- is met by *)
(*                     the stages above it ([run_real] / [real_run],      *)
(*                     [terms_realT] / [realT_terms]);                    *)
(*   [fire_nt] / [fire_t1] / [fire_t2]  every commit the round's          *)
(*                     processes make keeps the vector real (or           *)
(*                     terminal), or meets a committed writer [EXf]       *)
(*                     names.                                            *)
(*                                                                        *)
(* The exclusions [EXf] are design SS2.2's: content against an exec       *)
(* failure (the flow chain), a node's panic against the writers it never *)
(* forked (the one-shots) -- and every source no process of the round     *)
(* commits ([gsrc]), whose deposit is unpayable.                          *)
(* ===================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list countable bitvector.definitions.
Require Import RiscvLang ObsTrace.
Require Import LineWords EchoDisc LineBytes LineModel PipeDisc.
Require Import ProgTree ProgTreePipes PipesPair PipesDisc.
Require Import PipeBothNPure.
From stdpp Require Import list.
Local Open Scope nat_scope.

(* ===================================================================== *)
(*  0.  THE WRITERS, THE DIAGNOSTICS, THE EXCLUSIONS                      *)
(* ===================================================================== *)

Lemma wids_from_elem (k n : nat) (w : wid) :
  w ∈ wids_from k n <->
  match w with WSh j | WLeft j => k <= j < k + n | WLast => True end.
Proof using.
  revert k. induction n as [| n IH]; intros k; cbn [wids_from].
  - rewrite elem_of_list_singleton. destruct w; split; try lia; try done.
  - rewrite !elem_of_cons, IH. destruct w as [j | j |]; split.
    + intros [Hq | [Hq | Hq]]; [injection Hq as ->; lia | discriminate | lia].
    + intros Hj. destruct (decide (j = k)) as [-> | Hne]; [by left | right; right; lia].
    + intros [Hq | [Hq | Hq]]; [discriminate | injection Hq as ->; lia | lia].
    + intros Hj. destruct (decide (j = k)) as [-> | Hne]; [by right; left | right; right; lia].
    + intros _. done.
    + intros _. by right; right.
Qed.

Lemma wids_elem (n : nat) (w : wid) :
  w ∈ wids n <-> match w with WSh j | WLeft j => j < n | WLast => True end.
Proof using. unfold wids. rewrite wids_from_elem. destruct w; lia || done. Qed.

(* sh's [exec %s failed] at stage [k]: argv[0] is [echo] at the producer
   and [cat] below it ([PipesDisc.st_dg_exec]) *)
Definition dg_st (k : nat) : list (bv 8) :=
  match k with O => dg_execL | S _ => dg_execR end.

Lemma dg_st_ne (k : nat) : dg_st k <> [].
Proof using. destruct k; vm_compute; discriminate. Qed.

Lemma dg_st_len (k : nat) : length (dg_st k) = match k with O => 17 | S _ => 16 end.
Proof using. destruct k; vm_compute; reflexivity. Qed.

Lemma dg_st_ne_write (k : nat) : dg_st k <> cat_dg_write.
Proof using. destruct k; vm_compute; discriminate. Qed.

Lemma dg_pipe_ne_fork : dg_pipe_b <> alt_forkc.
Proof using. vm_compute. discriminate. Qed.

Lemma dg_pipe_b_len : length dg_pipe_b = 5.
Proof using. vm_compute. reflexivity. Qed.

Lemma alt_forkc_len : length alt_forkc = 7.
Proof using. vm_compute. reflexivity. Qed.

Lemma dg_execL_ne_R : dg_execL <> dg_execR.
Proof using. vm_compute. discriminate. Qed.

Definition panic_src (s : list (bv 8)) : Prop := s = dg_pipe_b \/ s = alt_forkc.

(* THE COMMITS the round's processes make, source by writer *)
Definition fire_src (L : list (bv 8)) (w : wid) (s : list (bv 8)) : Prop :=
  match w with
  | WSh _ => panic_src s
  | WLeft k => s = dg_st k \/ (k <> 0 /\ s = cat_dg_write)
  | WLast => s = L \/ s = dg_execR
  end.

Global Instance fire_src_dec L w s : Decision (fire_src L w s).
Proof using. destruct w; unfold fire_src, panic_src; apply _. Defined.

(* a source no process of the round commits *)
Definition gsrc (L : list (bv 8)) (w : wid) (s : list (bv 8)) : Prop :=
  s <> [] /\ ~ fire_src L w s.

(* THE EXCLUSIONS a commit of source [s] by writer [w] spends (design
   SS2.2): every committed writer [w'] at [s'] whose deposit refutes this
   one's.  [nc] is the number of cats, [L] the line's content. *)
Definition EXf (nc : nat) (L : list (bv 8)) (w : wid) (s : list (bv 8))
    (w' : wid) (s' : list (bv 8)) : Prop :=
  gsrc L w' s'
  \/ match w with
     | WSh k =>
         (exists j, w' = WSh j /\ (j < nc)%nat /\ j <> k /\ panic_src s')
         \/ (exists j, w' = WLeft j /\ (j < nc)%nat
               /\ (if bool_decide (s = dg_pipe_b) then (k <= j)%nat else (k < j)%nat)
               /\ s' <> [])
         \/ (w' = WLast /\ s' <> [])
     | WLeft k =>
         (exists j, w' = WSh j /\ (j < nc)%nat
               /\ (((j <= k)%nat /\ s' = dg_pipe_b) \/ ((j < k)%nat /\ s' = alt_forkc)))
         \/ (s = dg_st k /\ w' = WLast /\ s' = L /\ L <> dg_execR)
     | WLast =>
         (exists j, w' = WSh j /\ (j < nc)%nat /\ panic_src s')
         \/ (s = L /\ L <> dg_execR /\ exists j, w' = WLeft j /\ (j < nc)%nat /\ s' = dg_st j)
     end.

(* ===================================================================== *)
(*  1.  THE PIPELINE'S RUNS, READ OFF THE VALUES                          *)
(* ===================================================================== *)

Section real.
  Context (fc : bytes -> option bytes) (ws : list bytes) (n : nat).
  Hypothesis Hn : 1 <= n.
  Local Notation L := (wl_line (drop 1 ws)).
  Local Notation lp := (LPipes (PrEcho ws) n).

  (* what each stage may print on the console *)
  Definition aP (s : bytes) : Prop := s = [] \/ s = dg_execL.
  Definition aM (s : bytes) : Prop := s = [] \/ s = dg_execR \/ s = cat_dg_write.
  Definition aT (s : bytes) : Prop := s = dg_execR \/ s `prefix_of` L.
  Definition aS (j : nat) (s : bytes) : Prop := match j with O => aP s | S _ => aM s end.

  (* THE ONE DATA DEMAND: the last cat's content [D] came down the chain --
     from a middle cat that halted (the ruled corner), with only silent
     stages below it, or from echo itself through silent stages *)
  Definition upok (v : wid -> bytes) (D : bytes) : Prop :=
    (exists i, 1 <= i < n /\ v (WLeft i) = cat_dg_write
               /\ forall i', i < i' < n -> v (WLeft i') = [])
    \/ ((forall i, 1 <= i < n -> v (WLeft i) = []) /\ v (WLeft 0) = [] /\ D = L).

  (* node [k]'s pipe(2) failed *)
  Definition realP (v : wid -> bytes) (k : nat) : Prop :=
    k < n /\ v (WSh k) = dg_pipe_b /\ (forall j, j < n -> j <> k -> v (WSh j) = [])
    /\ (forall j, k <= j < n -> v (WLeft j) = []) /\ v WLast = []
    /\ (forall j, j < k -> aS j (v (WLeft j))).

  (* the round ran *)
  Definition realN (v : wid -> bytes) : Prop :=
    (forall j, j < n -> v (WSh j) = []) /\ (forall j, j < n -> aS j (v (WLeft j)))
    /\ aT (v WLast)
    /\ (forall D, v WLast = D -> D <> [] -> D <> dg_execR -> upok v D).

  Definition real (v : wid -> bytes) : Prop := (exists k, realP v k) \/ realN v.

  (* node [k]'s fork failed: the TERMINAL vector *)
  Definition realT (v : wid -> bytes) (k : nat) : Prop :=
    k < n /\ v (WSh k) = alt_forkc /\ (forall j, j <> k -> v (WSh j) = [])
    /\ (forall j, k < j -> v (WLeft j) = []) /\ v WLast = []
    /\ (forall j, j <= k -> aS j (v (WLeft j))).

  (* ---- the stages' outcomes, chosen ---- *)
  Definition so_prod (s : bytes) : st_out := MkSO s None (Some WrNone).
  Definition so_mid (s : bytes) : st_out :=
    if decide (s = cat_dg_write) then MkSO cat_dg_write (Some RdGone) (Some (WrHalt []))
    else MkSO s (Some RdGone) (Some WrNone).
  Definition so_copy (D : bytes) : st_out := MkSO [] (Some (RdEof D)) (Some (WrAll D)).
  Definition so_lastd (s : bytes) : st_out :=
    if decide (s = dg_execR) then MkSO dg_execR (Some RdGone) None
    else if decide (s = []) then MkSO [] (Some RdGone) None
    else MkSO s (Some (RdEof s)) None.

  Lemma so_prod_ok s : aP s -> stage_out fc L (SProd (PrEcho ws)) (so_prod s).
  Proof using.
    intros [-> | ->]; unfold so_prod.
    - exact (so_silent fc L (SProd (PrEcho ws))).
    - exact (so_exec fc L (SProd (PrEcho ws))).
  Qed.

  Lemma so_mid_ok s : aM s -> stage_out fc L SMid (so_mid s).
  Proof using.
    intros Hs. unfold so_mid. case_decide as Hw.
    - subst s. exact (so_mid_halt fc L [] (prefix_nil _)).
    - destruct Hs as [-> | [-> | ->]]; [| | by destruct Hw].
      + exact (so_silent fc L SMid).
      + exact (so_exec fc L SMid).
  Qed.

  Lemma so_mid_cons s : so_cons (so_mid s) = s.
  Proof using. unfold so_mid. case_decide as Hw; [by subst s | reflexivity]. Qed.

  Lemma so_mid_rd s : rd_of (so_mid s) = RdGone.
  Proof using. unfold so_mid. case_decide; reflexivity. Qed.

  Lemma so_lastd_ok s : aT s -> stage_out fc L SLast (so_lastd s).
  Proof using.
    intros Hs. unfold so_lastd. case_decide as He; [subst s; exact (so_exec fc L SLast) |].
    case_decide as Hz; [subst s; exact (so_silent fc L SLast) |].
    destruct Hs as [Hs | Hs]; [by destruct He |]. exact (so_last fc L s Hs).
  Qed.

  Lemma so_lastd_cons s : so_cons (so_lastd s) = s.
  Proof using.
    unfold so_lastd. case_decide as He; [by subst s |]. case_decide as Hz; [by subst s |].
    reflexivity.
  Qed.

  Lemma so_copy_ok D : D `prefix_of` L -> stage_out fc L SMid (so_copy D).
  Proof using. intros HD. exact (so_mid_copy fc L D HD). Qed.

End real.

(* ---- building the suffix from an outcome per stage ---- *)
Section build.
  Context (fc : bytes -> option bytes) (ws : list bytes).
  Local Notation L := (wl_line (drop 1 ws)).

  Lemma rep_S2 {A : Type} (x : A) (m : nat) :
    replicate (2 * S m) x = x :: replicate (2 * m + 1) x.
  Proof using. replace (2 * S m) with (S (2 * m + 1)) by lia. reflexivity. Qed.

  Lemma wids_from_nil (src : wid -> bytes) (k m : nat) :
    (forall j, k <= j < k + m -> src (WSh j) = [] /\ src (WLeft j) = []) -> src WLast = [] ->
    src <$> wids_from k m = replicate (2 * m + 1) [].
  Proof using.
    revert k. induction m as [| m IH]; intros k Hs Hl; cbn [wids_from].
    - rewrite fmap_cons, fmap_nil, Hl. reflexivity.
    - destruct (Hs k ltac:(lia)) as [H1 H2]. rewrite !fmap_cons, H1, H2.
      rewrite (IH (S k)); [| intros j Hj; apply Hs; lia | exact Hl].
      replace (2 * S m + 1) with (S (S (2 * m + 1))) by lia. reflexivity.
  Qed.

  Lemma sfx_build (v : wid -> bytes) (so : nat -> st_out) (m : nat) :
    forall (j : nat) (win : wr_out) (wc : bool),
    (forall i, j <= i < j + m ->
       v (WSh i) = [] /\ stage_out fc L SMid (so i) /\ so_cons (so i) = v (WLeft i)) ->
    stage_out fc L SLast (so (j + m)) -> so_cons (so (j + m)) = v WLast ->
    pipe_pairB L wc win (rd_of (so j)) ->
    (forall i, j <= i < j + m -> pipe_pairB L true (wr_of (so i)) (rd_of (so (S i)))) ->
    sfx_runV fc L (S m) win wc (v <$> wids_from j m).
  Proof using.
    induction m as [| m IH]; intros j win wc Hst Hl Hlc Hp Hps.
    - rewrite Nat.add_0_r in Hl, Hlc. cbn [wids_from]. rewrite fmap_cons, fmap_nil.
      rewrite <- Hlc. exact (srv_last fc L win wc (so j) Hl Hp).
    - cbn [wids_from]. rewrite !fmap_cons.
      destruct (Hst j ltac:(lia)) as (Hsh & Hso & Hc). rewrite Hsh, <- Hc.
      apply (srv_node fc L m win wc (so j) _ Hso Hp).
      apply (IH (S j) (wr_of (so j)) true).
      + intros i Hi. apply Hst. lia.
      + replace (S j + m) with (j + S m) by lia. exact Hl.
      + replace (S j + m) with (j + S m) by lia. exact Hlc.
      + exact (Hps j ltac:(lia)).
      + intros i Hi. apply Hps. lia.
  Qed.

  (* ...and with node [j + d]'s pipe(2) failing *)
  Lemma sfx_build_pf (v : wid -> bytes) (so : nat -> st_out) (d : nat) :
    forall (j m : nat) (win : wr_out) (wc : bool),
    d < S m ->
    (forall i, j <= i < j + d ->
       v (WSh i) = [] /\ stage_out fc L SMid (so i) /\ so_cons (so i) = v (WLeft i)) ->
    v (WSh (j + d)) = dg_pipe_b ->
    (forall i, j + d < i < j + S m -> v (WSh i) = []) ->
    (forall i, j + d <= i < j + S m -> v (WLeft i) = []) -> v WLast = [] ->
    (0 < d -> pipe_pairB L wc win (rd_of (so j))) ->
    (forall i, j <= i -> S i < j + d -> pipe_pairB L true (wr_of (so i)) (rd_of (so (S i)))) ->
    sfx_runV fc L (S (S m)) win wc (v <$> wids_from j (S m)).
  Proof using.
    induction d as [| d IH]; intros j m win wc Hd Hst Hpf Hsh Hlf Hlast Hp Hps.
    - rewrite Nat.add_0_r in Hpf, Hsh, Hlf. cbn [wids_from]. rewrite !fmap_cons.
      rewrite Hpf, (Hlf j ltac:(lia)).
      assert (Hrest : v <$> wids_from (S j) m = replicate (2 * m + 1) []).
      { apply (wids_from_nil v (S j) m); [| exact Hlast].
        intros i Hi. split; [apply Hsh | apply Hlf]; lia. }
      rewrite Hrest.
      rewrite <- rep_S2. exact (srv_pipe_fail fc L m win wc).
    - destruct m as [| m]; [lia |].
      cbn [wids_from]. rewrite !fmap_cons.
      destruct (Hst j ltac:(lia)) as (Hsj & Hso & Hc). rewrite Hsj, <- Hc.
      apply (srv_node fc L (S m) win wc (so j) _ Hso (Hp ltac:(lia))).
      apply (IH (S j) m (wr_of (so j)) true ltac:(lia)).
      + intros i Hi. apply Hst. lia.
      + replace (S j + d) with (j + S d) by lia. exact Hpf.
      + intros i Hi. apply Hsh. lia.
      + intros i Hi. apply Hlf. lia.
      + exact Hlast.
      + intros Hd0. apply Hps; lia.
      + intros i Hi1 Hi2. apply Hps; lia.
  Qed.
End build.

(* ---- the runs' shapes, one constructor at a time ---- *)
Section inv.
  Context (fc : bytes -> option bytes) (L : bytes).

  Lemma sfx_runV_1_inv win wc vs :
    sfx_runV fc L 1 win wc vs ->
    exists so, vs = [so_cons so] /\ stage_out fc L SLast so /\ pipe_pairB L wc win (rd_of so).
  Proof using.
    intros H. remember 1 as mm eqn:Hmm.
    destruct H as [win' wc' so Hso Hp | m' win' wc' | m' win' wc' so vs' Hso Hp Hr];
      [| lia | lia].
    exists so. done.
  Qed.

  Lemma sfx_runV_SS_inv m win wc a b vs :
    sfx_runV fc L (S (S m)) win wc (a :: b :: vs) ->
    (a = dg_pipe_b /\ b :: vs = replicate (2 * S m) [])
    \/ exists so, a = [] /\ b = so_cons so /\ stage_out fc L SMid so
                  /\ pipe_pairB L wc win (rd_of so) /\ sfx_runV fc L (S m) (wr_of so) true vs.
  Proof using.
    intros H. remember (S (S m)) as mm eqn:Hmm. remember (a :: b :: vs) as l eqn:Hl.
    destruct H as [win' wc' so Hso Hp | m' win' wc' | m' win' wc' so vs' Hso Hp Hr].
    - lia.
    - injection Hmm as ->. left. split; congruence.
    - injection Hmm as ->. injection Hl as Ha Hb Hvs. subst. right. exists so. done.
  Qed.

  Lemma replicate_nil_elem (vs : list bytes) (k : nat) (x : bytes) :
    vs = replicate k [] -> x ∈ vs -> x = [].
  Proof using. intros -> Hx. by apply elem_of_replicate in Hx as [-> _]. Qed.
End inv.

Section real2.
  Context (fc : bytes -> option bytes) (ws : list bytes).
  Local Notation L := (wl_line (drop 1 ws)).
  Local Notation aT := (aT ws).

  (* the suffix from stage [j], [m] middle stages above the last *)
  Definition sreal (v : wid -> bytes) (j m : nat) (win : wr_out) (wc : bool) : Prop :=
    (exists k, j <= k < j + m /\ v (WSh k) = dg_pipe_b
       /\ (forall i, j <= i < k -> v (WSh i) = [] /\ aM (v (WLeft i)))
       /\ (forall i, k < i < j + m -> v (WSh i) = [])
       /\ (forall i, k <= i < j + m -> v (WLeft i) = []) /\ v WLast = [])
    \/ ((forall i, j <= i < j + m -> v (WSh i) = [] /\ aM (v (WLeft i))) /\ aT (v WLast)
        /\ (forall D, v WLast = D -> D <> [] -> D <> dg_execR ->
              (exists i, j <= i < j + m /\ v (WLeft i) = cat_dg_write
                         /\ forall i', i < i' < j + m -> v (WLeft i') = [])
              \/ ((forall i, j <= i < j + m -> v (WLeft i) = [])
                  /\ pipe_pairB L wc win (RdEof D)))).

  Lemma fmap_wids_nil (v : wid -> bytes) (k m : nat) (x : wid) :
    (v <$> wids_from k m) = replicate (2 * m + 1) [] -> x ∈ wids_from k m -> v x = [].
  Proof using.
    intros Heq Hx. apply (replicate_nil_elem (v <$> wids_from k m) (2 * m + 1)); [exact Heq |].
    apply elem_of_list_fmap. by exists x.
  Qed.

  Lemma sfx_inv (v : wid -> bytes) (m : nat) :
    forall (j : nat) (win : wr_out) (wc : bool),
    sfx_runV fc L (S m) win wc (v <$> wids_from j m) -> sreal v j m win wc.
  Proof using.
    induction m as [| m IH]; intros j win wc H.
    - cbn [wids_from] in H. rewrite fmap_cons, fmap_nil in H.
      destruct (sfx_runV_1_inv fc L win wc _ H) as (so & Heq & Hso & Hp).
      injection Heq as Hv. right. split; [intros i Hi; lia |].
      destruct (stage_out_last_inv fc L so Hso) as [-> | [-> | (D & HD & ->)]];
        cbn in Hv, Hp |- *; rewrite Hv.
      + split; [left; reflexivity | intros D -> _ HD; by destruct HD].
      + split; [right; apply prefix_nil | intros D -> HD; by destruct HD].
      + split; [right; exact HD |]. intros D' <- _ _. right.
        split; [intros i Hi; lia | exact Hp].
    - cbn [wids_from] in H. rewrite !fmap_cons in H.
      destruct (sfx_runV_SS_inv fc L m win wc _ _ _ H)
        as [[Hsh Hrest] | (so & Hsh & Hl & Hso & Hp & Hr)].
      + (* node j's pipe(2) failed *)
        assert (Hall : forall x, x ∈ wids_from (S j) m -> v x = []).
        { intros x Hx. apply (fmap_wids_nil v (S j) m x); [| exact Hx].
          rewrite rep_S2 in Hrest. by injection Hrest as _ ->. }
        assert (Hlj : v (WLeft j) = []).
        { rewrite rep_S2 in Hrest. by injection Hrest as ->. }
        left. exists j. split; [lia |]. split; [exact Hsh |].
        split; [intros i Hi; lia |].
        split; [intros i Hi; apply Hall, wids_from_elem; lia |].
        split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne];
                  [exact Hlj | apply Hall, wids_from_elem; lia] |].
        apply Hall, wids_from_elem. done.
      + (* it forked: stage j, then the suffix below *)
        pose proof (IH (S j) (wr_of so) true Hr) as Hs.
        assert (Hj : v (WSh j) = [] /\ aM (v (WLeft j))).
        { split; [exact Hsh |]. rewrite Hl.
          destruct (stage_out_mid_inv fc L so Hso)
            as [-> | [-> | [(D & _ & ->) | (D & _ & ->)]]]; cbn; unfold aM; tauto. }
        destruct Hs as [(k & Hk & Hpf & Hab & Hbl & Hlf & Hlast) | (Hab & HT & Hch)].
        * left. exists k. split; [lia |]. split; [exact Hpf |].
          split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne]; [exact Hj | apply Hab; lia] |].
          split; [intros i Hi; apply Hbl; lia |].
          split; [intros i Hi; apply Hlf; lia | exact Hlast].
        * right. split; [intros i Hi; destruct (decide (i = j)) as [-> | Hne];
                          [exact Hj | apply Hab; lia] |].
          split; [exact HT |].
          intros D HD Hne Hnx. destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib) | (Hall & Hpp)].
          -- left. exists i. split; [lia |]. split; [exact Hic |].
             intros i' Hi'. apply Hib. lia.
          -- destruct (stage_out_mid_inv fc L so Hso)
               as [Hso' | [Hso' | [(D0 & HD0 & Hso') | (D0 & HD0 & Hso')]]]; subst so; cbn in *.
             ++ exfalso. apply Hne. exact Hpp.
             ++ exfalso. apply Hne. exact Hpp.
             ++ right. subst D0. split; [| exact Hp].
                intros i Hi. destruct (decide (i = j)) as [-> | Hne']; [exact Hl | apply Hall; lia].
             ++ left. exists j. split; [lia |]. split; [exact Hl |].
                intros i' Hi'. apply Hall. lia.
  Qed.
End real2.

Lemma line_runV_SS_inv (fc : bytes -> option bytes) (p : producer) (n : nat) (a b : bytes)
    (vs : list bytes) :
  line_runV fc (LPipes p n) (a :: b :: vs) ->
  (a = dg_pipe_b /\ b :: vs = replicate (2 * n) [])
  \/ exists so, a = [] /\ b = so_cons so /\ stage_out fc (prod_content fc p) (SProd p) so
                /\ sfx_runV fc (prod_content fc p) n (wr_of so) (prod_cat p) vs.
Proof using.
  intros H. remember (LPipes p n) as l eqn:Hl. remember (a :: b :: vs) as ls eqn:Hls.
  destruct H as [ws' | ws' | ws' | p' n' Hn' | p' n' so vs' Hso Hr]; try discriminate Hl.
  - injection Hl as -> ->. left. split; congruence.
  - injection Hl as -> ->. injection Hls as Ha Hb Hvs. subst. right. exists so. done.
Qed.

Lemma aS_mid (i : nat) (s : bytes) : 1 <= i -> aS i s -> aM s.
Proof using. intros Hi Hs. destruct i as [| i]; [lia | exact Hs]. Qed.

Section real3.
  Context (fc : bytes -> option bytes) (ws : list bytes) (n : nat).
  Hypothesis Hn : 1 <= n.
  Local Notation L := (wl_line (drop 1 ws)).
  Local Notation lp := (LPipes (PrEcho ws) n).

  Lemma echo_aP (so : st_out) :
    stage_out fc L (SProd (PrEcho ws)) so -> aP (so_cons so).
  Proof using.
    intros Hso. destruct (stage_out_echo_inv fc L ws so Hso)
      as [-> | [-> | [(_ & ->) | (D & _ & _ & ->)]]]; cbn; unfold aP; tauto.
  Qed.

  (* A RUN IS REAL *)
  Lemma run_real (v : wid -> bytes) : runN fc lp v -> real ws n v.
  Proof using Hn.
    intros H. unfold runN in H. cbn [lcats] in H.
    destruct n as [| m] eqn:Hnm; [lia |]. unfold wids in H. cbn [wids_from] in H.
    rewrite !fmap_cons in H.
    destruct (line_runV_SS_inv fc (PrEcho ws) (S m) _ _ _ H)
      as [[Hsh Hrest] | (so & Hsh & Hl & Hso & Hr)].
    - (* the top node's pipe(2) failed *)
      assert (Hrest' : v (WLeft 0) :: (v <$> wids_from 1 m) = [] :: replicate (2 * m + 1) [])
        by (rewrite Hrest; replace (2 * S m) with (S (2 * m + 1)) by lia; reflexivity).
      injection Hrest' as Hl0 Hall.
      assert (Hall' : forall x, x ∈ wids_from 1 m -> v x = []).
      { intros x Hx. exact (fmap_wids_nil v 1 m x Hall Hx). }
      left. exists 0. split; [lia |]. split; [exact Hsh |].
      split; [intros j Hj Hj0; apply Hall', wids_from_elem; lia |].
      split; [intros j Hj; destruct j as [| j]; [exact Hl0 | apply Hall', wids_from_elem; lia] |].
      split; [apply Hall', wids_from_elem; done | intros j Hj; lia].
    - pose proof (sfx_inv fc ws v m 1 (wr_of so) false Hr) as Hs.
      assert (H0 : aS 0 (v (WLeft 0))) by (cbn; rewrite Hl; exact (echo_aP so Hso)).
      destruct Hs as [(k & Hk & Hpf & Hab & Hbl & Hlf & Hlast) | (Hab & HT & Hch)].
      + left. exists k. split; [lia |]. split; [exact Hpf |].
        split; [intros j Hj Hjk; destruct j as [| j]; [exact Hsh |];
                destruct (decide (S j < k)) as [Hlt | Hge]; [apply Hab; lia | apply Hbl; lia] |].
        split; [intros j Hj; apply Hlf; lia |]. split; [exact Hlast |].
        intros j Hj. destruct j as [| j]; [exact H0 | cbn; apply Hab; lia].
      + right. split; [intros j Hj; destruct j as [| j]; [exact Hsh | apply Hab; lia] |].
        split; [intros j Hj; destruct j as [| j]; [exact H0 | cbn; apply Hab; lia] |].
        split; [exact HT |].
        intros D HD Hne Hnx. destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib) | (Hall & Hpp)].
        * left. exists i. split; [lia |]. split; [exact Hic |]. intros i' Hi'. apply Hib. lia.
        * right. destruct (stage_out_echo_inv fc L ws so Hso)
            as [Hso' | [Hso' | [(_ & Hso') | (D0 & _ & _ & Hso')]]]; subst so; cbn in *.
          -- exfalso. exact (Hne Hpp).
          -- exfalso. exact (Hne Hpp).
          -- split; [intros i Hi; apply Hall; lia |]. split; [exact Hl | exact Hpp].
          -- destruct Hpp as [Hf _]. discriminate Hf.
  Qed.

  (* A REAL VECTOR IS A RUN *)
  Lemma real_run (v : wid -> bytes) : real ws n v -> runN fc lp v.
  Proof using Hn.
    intros Hre. unfold runN. cbn [lcats]. destruct n as [| m] eqn:Hnm; [lia |].
    unfold wids. cbn [wids_from]. rewrite !fmap_cons.
    destruct Hre as [(k & Hk & Hpf & Hsh & Hlf & Hlast & Hab) | (Hsh & Hab & HT & Hch)].
    - destruct k as [| k'].
      + (* the top node's pipe(2) failed *)
        rewrite Hpf, (Hlf 0 ltac:(lia)).
        rewrite (wids_from_nil v 1 m); [| intros j Hj; split; [apply Hsh; lia | apply Hlf; lia] | exact Hlast].
        rewrite <- rep_S2. exact (lrv_pipe_fail fc (PrEcho ws) (S m) Hn).
      + (* node [S k']'s *)
        destruct m as [| m']; [lia |].
        rewrite (Hsh 0 ltac:(lia) ltac:(lia)).
        set (so := fun i : nat => so_mid (v (WLeft i))).
        pose proof (so_prod_ok fc ws (v (WLeft 0)) (Hab 0 ltac:(lia))) as Hso0.
        rewrite <- (so_mid_cons (v (WLeft 0))) at 1.
        replace (so_cons (so_mid (v (WLeft 0)))) with (so_cons (so_prod (v (WLeft 0))))
          by (rewrite so_mid_cons; reflexivity).
        apply (lrv_node fc (PrEcho ws) (S (S m')) (so_prod (v (WLeft 0))) _ Hso0).
        apply (sfx_build_pf fc ws v so k' 1 m' WrNone false ltac:(lia)).
        * intros i Hi. split; [apply Hsh; lia |].
          split; [unfold so; apply (so_mid_ok fc ws); exact (aS_mid i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
        * replace (1 + k') with (S k') by lia. exact Hpf.
        * intros i Hi. apply Hsh; lia.
        * intros i Hi. apply Hlf; lia.
        * exact Hlast.
        * intros _. unfold so. rewrite so_mid_rd. exact I.
        * intros i Hi1 Hi2. unfold so. rewrite so_mid_rd. destruct (wr_of _); exact I.
    - (* THE ROUND RAN *)
      rewrite (Hsh 0 ltac:(lia)).
      destruct (decide (v WLast = [] \/ v WLast = dg_execR)) as [Hnd | Hd].
      + (* no data demand: every stage's outcome is its own, every reader gone *)
        set (so := fun i : nat => if decide (i = S m) then so_lastd (v WLast) else so_mid (v (WLeft i))).
        rewrite <- (so_mid_cons (v (WLeft 0))) at 1.
        replace (so_cons (so_mid (v (WLeft 0)))) with (so_cons (so_prod (v (WLeft 0))))
          by (rewrite so_mid_cons; reflexivity).
        apply (lrv_node fc (PrEcho ws) (S m) (so_prod (v (WLeft 0))) _
                 (so_prod_ok fc ws (v (WLeft 0)) (Hab 0 ltac:(lia)))).
        apply (sfx_build fc ws v so m 1 WrNone false).
        * intros i Hi. unfold so. rewrite decide_False by lia.
          split; [apply Hsh; lia |].
          split; [apply (so_mid_ok fc ws); exact (aS_mid i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
        * unfold so. rewrite decide_True by lia. exact (so_lastd_ok fc ws _ HT).
        * unfold so. rewrite decide_True by lia. apply so_lastd_cons.
        * unfold so. destruct (decide (1 = S m)).
          -- unfold so_lastd. destruct Hnd as [-> | ->]; repeat case_decide; try congruence; exact I.
          -- rewrite so_mid_rd. exact I.
        * intros i Hi. unfold so. destruct (decide (S i = S m)).
          -- unfold so_lastd. destruct Hnd as [-> | ->]; repeat case_decide; try congruence;
               destruct (wr_of _); exact I.
          -- rewrite so_mid_rd. destruct (wr_of _); exact I.
      + (* THE CONTENT: it came down the chain *)
        assert (Hne : v WLast <> []) by tauto. assert (Hnx : v WLast <> dg_execR) by tauto.
        set (D := v WLast).
        assert (HDL : D `prefix_of` L) by (destruct HT as [HT | HT]; [by destruct Hnx | exact HT]).
        assert (Hlast : so_lastd D = MkSO D (Some (RdEof D)) None).
        { unfold so_lastd. rewrite decide_False by exact Hnx. rewrite decide_False by exact Hne.
          reflexivity. }
        destruct (Hch D eq_refl Hne Hnx) as [(i0 & Hi0 & Hic & Hib) | (Hall & Hl0 & HDe)].
        * (* a middle cat halted, the stages below it copied what came *)
          set (so := fun i : nat =>
                       if decide (i = S m) then so_lastd D
                       else if decide (i0 < i) then so_copy D else so_mid (v (WLeft i))).
          rewrite <- (so_mid_cons (v (WLeft 0))) at 1.
          replace (so_cons (so_mid (v (WLeft 0)))) with (so_cons (so_prod (v (WLeft 0))))
            by (rewrite so_mid_cons; reflexivity).
          apply (lrv_node fc (PrEcho ws) (S m) (so_prod (v (WLeft 0))) _
                   (so_prod_ok fc ws (v (WLeft 0)) (Hab 0 ltac:(lia)))).
          apply (sfx_build fc ws v so m 1 WrNone false).
          -- intros i Hi. unfold so. rewrite decide_False by lia.
             split; [apply Hsh; lia |]. destruct (decide (i0 < i)) as [Hlt | Hge].
             ++ split; [exact (so_copy_ok fc ws D HDL) |]. cbn. symmetry. apply Hib. lia.
             ++ split; [apply (so_mid_ok fc ws); exact (aS_mid i _ ltac:(lia) (Hab i ltac:(lia))) | apply so_mid_cons].
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. exact (so_last fc L D HDL).
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. reflexivity.
          -- unfold so. rewrite decide_False by lia. rewrite decide_False by lia.
             rewrite so_mid_rd. exact I.
          -- intros i Hi. unfold so. rewrite (decide_False (P := i = S m)) by lia.
             destruct (decide (S i = S m)) as [Hsi | Hsi].
             ++ rewrite Hlast. cbn [rd_of so_rd].
                destruct (decide (i0 < i)) as [Hlt | Hge].
                ** cbn. reflexivity.
                ** assert (i = i0) by lia. subst i. unfold so_mid.
                   rewrite Hic, decide_True by reflexivity. cbn. split; [reflexivity | exact HDL].
             ++ destruct (decide (i0 < S i)) as [Hlt | Hge].
                ** cbn [so_copy rd_of so_rd]. destruct (decide (i0 < i)) as [Hlt' | Hge'].
                   --- cbn. reflexivity.
                   --- assert (i = i0) by lia. subst i. unfold so_mid.
                       rewrite Hic, decide_True by reflexivity. cbn. split; [reflexivity | exact HDL].
                ** rewrite decide_False by lia. rewrite so_mid_rd. destruct (wr_of _); exact I.
        * (* echo wrote the line whole, every stage copied it *)
          set (so := fun i : nat => if decide (i = S m) then so_lastd D else so_copy D).
          assert (Hecho : stage_out fc L (SProd (PrEcho ws)) (MkSO [] None (Some (WrAll L))))
            by exact (so_echo fc L ws eq_refl).
          rewrite Hl0.
          change (@nil (bv 8)) with (so_cons (MkSO [] None (Some (WrAll L)))) at 1.
          apply (lrv_node fc (PrEcho ws) (S m) (MkSO [] None (Some (WrAll L))) _ Hecho).
          apply (sfx_build fc ws v so m 1 (WrAll L) false).
          -- intros i Hi. unfold so. rewrite decide_False by lia.
             split; [apply Hsh; lia |]. split; [exact (so_copy_ok fc ws D HDL) |].
             cbn. symmetry. apply Hall. lia.
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. exact (so_last fc L D HDL).
          -- unfold so. rewrite decide_True by lia. rewrite Hlast. reflexivity.
          -- unfold so. destruct (decide (1 = S m)).
             ++ rewrite Hlast. cbn. exact HDe.
             ++ cbn. exact HDe.
          -- intros i Hi. unfold so. rewrite (decide_False (P := i = S m)) by lia.
             destruct (decide (S i = S m)); [rewrite Hlast |]; cbn; reflexivity.
  Qed.
End real3.

(* ---- the terminal vectors ---- *)
Section term.
  Context (fc : bytes -> option bytes) (ws : list bytes).
  Local Notation L := (wl_line (drop 1 ws)).

  Lemma sfx_term_build (v : wid -> bytes) (d : nat) :
    forall (j m : nat) (win : wr_out) (wc : bool),
    d < S m -> (forall i, j <= i <= j + d -> aM (v (WLeft i))) ->
    sfx_term fc L (S (S m)) win wc ((v <$> (WLeft <$> seq j d)) ++ [dg_fork_b])
      (v (WLeft (j + d))).
  Proof using.
    induction d as [| d IH]; intros j m win wc Hd Ha.
    - rewrite Nat.add_0_r. cbn [seq fmap list_fmap app].
      rewrite <- (so_mid_cons (v (WLeft j))).
      exact (stt_here fc L m win wc (so_mid (v (WLeft j))) (so_mid_ok fc ws _ (Ha j ltac:(lia)))).
    - destruct m as [| m]; [lia |].
      cbn [seq]. rewrite !fmap_cons. cbn [app].
      rewrite <- (so_mid_cons (v (WLeft j))) at 1.
      apply (stt_next fc L (S m) win wc (so_mid (v (WLeft j))) _ _
               (so_mid_ok fc ws _ (Ha j ltac:(lia)))).
      + rewrite so_mid_rd. destruct win; exact I.
      + replace (j + S d) with (S j + d) by lia.
        apply (IH (S j) m); [lia |]. intros i Hi. apply Ha. lia.
  Qed.

  Lemma sfx_term_inv (v : wid -> bytes) (d : nat) :
    forall (j m : nat) (win : wr_out) (wc : bool) (W : list bytes) (sv : bytes),
    sfx_term fc L m win wc W sv ->
    W = (v <$> (WLeft <$> seq j d)) ++ [dg_fork_b] -> sv = v (WLeft (j + d)) ->
    forall i, j <= i <= j + d -> aM (v (WLeft i)).
  Proof using.
    induction d as [| d IH]; intros j m win wc W sv H HW Hsv i Hi.
    - rewrite Nat.add_0_r in Hsv. cbn [seq fmap list_fmap app] in HW.
      destruct H as [m' win' wc' so Hso | m' win' wc' so W' s' Hso Hp Hr].
      + assert (i = j) by lia. subst i.
        destruct (stage_out_mid_inv fc L so Hso) as [-> | [-> | [(D & _ & ->) | (D & _ & ->)]]];
          cbn in Hsv; rewrite <- Hsv; unfold aM; tauto.
      + exfalso. injection HW as _ HW'. destruct Hr; discriminate HW'.
    - cbn [seq] in HW. rewrite !fmap_cons in HW. cbn [app] in HW.
      destruct H as [m' win' wc' so Hso | m' win' wc' so W' s' Hso Hp Hr].
      + exfalso. injection HW as _ HW'. destruct (seq (S j) d); cbn in HW'; discriminate HW'.
      + injection HW as Hl0 HW'.
        destruct (decide (i = j)) as [-> | Hne].
        * rewrite <- Hl0.
          destruct (stage_out_mid_inv fc L so Hso) as [-> | [-> | [(D & _ & ->) | (D & _ & ->)]]];
            cbn; unfold aM; tauto.
        * apply (IH (S j) _ _ _ W' s' Hr HW'); [| lia].
          rewrite Hsv. f_equal. f_equal. lia.
  Qed.
End term.

Section term2.
  Context (fc : bytes -> option bytes) (ws : list bytes) (n : nat).
  Hypothesis Hn : 1 <= n.
  Local Notation L := (wl_line (drop 1 ws)).
  Local Notation lp := (LPipes (PrEcho ws) n).

  Lemma waitedN_S (k : nat) : waitedN (S k) = WLeft 0 :: (WLeft <$> seq 1 k).
  Proof using. unfold waitedN. cbn [seq]. rewrite fmap_cons. reflexivity. Qed.

  Lemma realT_terms (v : wid -> bytes) (k : nat) : realT n v k -> termsN fc lp v.
  Proof using Hn.
    intros (Hk & Hf & Hsh & Hlf & Hlast & Hab). exists k.
    split; [exact Hk |]. split; [exact Hf |]. split; [exact Hsh |].
    split; [exact Hlf |]. split; [exact Hlast |].
    destruct k as [| k'].
    - unfold waitedN. cbn [seq fmap list_fmap app].
      exact (lt_here fc (PrEcho ws) n (so_prod (v (WLeft 0))) Hn
               (so_prod_ok fc ws _ (Hab 0 ltac:(lia)))).
    - rewrite waitedN_S, fmap_cons. cbn [app].
      change (v (WLeft 0)) with (so_cons (so_prod (v (WLeft 0)))) at 1.
      apply (lt_next fc (PrEcho ws) n (so_prod (v (WLeft 0))) _ _
               (so_prod_ok fc ws _ (Hab 0 ltac:(lia)))).
      destruct n as [| [| m]]; [lia | lia |].
      replace (S k') with (1 + k') by lia.
      apply (sfx_term_build fc ws v k' 1 m WrNone false); [lia |].
      intros i Hi. apply (aS_mid i); [lia | apply Hab; lia].
  Qed.

  Lemma line_term_inv (v : wid -> bytes) (k : nat) (W : list bytes) (sv : bytes) :
    line_term fc lp W sv -> W = (v <$> waitedN k) ++ [dg_fork_b] -> sv = v (WLeft k) ->
    forall j, j <= k -> aS j (v (WLeft j)).
  Proof using Hn.
    intros H HW Hsv j Hj. remember lp as l eqn:Hl.
    destruct H as [p n' so Hn' Hso | p n' so W' s' Hso Hr];
      injection Hl as Hp Hnn; subst p; cbn [prod_content prod_cat] in *.
    - destruct k as [| k'].
      + assert (j = 0) by lia. subst j. cbn. rewrite <- Hsv. exact (echo_aP fc ws so Hso).
      + exfalso. rewrite waitedN_S, fmap_cons in HW. cbn [app] in HW.
        injection HW as _ HW'. destruct (seq 1 k'); cbn in HW'; discriminate HW'.
    - destruct k as [| k'].
      + exfalso. unfold waitedN in HW. cbn [seq fmap list_fmap app] in HW.
        injection HW as _ HW'. destruct Hr; discriminate HW'.
      + rewrite waitedN_S, fmap_cons in HW. cbn [app] in HW. injection HW as Hl0 HW'.
        destruct j as [| j].
        * cbn. rewrite <- Hl0. exact (echo_aP fc ws so Hso).
        * cbn. apply (sfx_term_inv fc ws v k' 1 _ _ _ W' s' Hr HW'); [| lia].
          by rewrite Hsv.
  Qed.

  Lemma terms_realT (v : wid -> bytes) : termsN fc lp v -> exists k, realT n v k.
  Proof using Hn.
    intros (k & Hk & Hf & Hsh & Hlf & Hlast & Hlt). exists k.
    split; [exact Hk |]. split; [exact Hf |]. split; [exact Hsh |].
    split; [exact Hlf |]. split; [exact Hlast |].
    exact (line_term_inv v k _ _ Hlt eq_refl eq_refl).
  Qed.
End term2.

(* ===================================================================== *)
(*  2.  EVERY COMMIT OF THE ROUND: ADMITTED, OR REFUTED                   *)
(* ===================================================================== *)

Definition vupd (v : wid -> bytes) (w : wid) (s : bytes) : wid -> bytes :=
  fun x => if decide (x = w) then s else v x.

Lemma vupd_self v w s : vupd v w s w = s.
Proof using. unfold vupd. by rewrite decide_True. Qed.
Lemma vupd_other v w s x : x <> w -> vupd v w s x = v x.
Proof using. intros Hx. unfold vupd. by rewrite decide_False. Qed.

(* a bounded search, and its last hit *)
Lemma range_dec (P : nat -> Prop) `{!forall i, Decision (P i)} (a b : nat) :
  (exists i, a <= i < b /\ P i) \/ (forall i, a <= i < b -> ~ P i).
Proof using.
  induction b as [| b IH]; [right; intros i Hi; lia |].
  destruct (decide (a <= b /\ P b)) as [[Hab Hb] | Hn]; [left; exists b; split; [lia | exact Hb] |].
  destruct IH as [(i & Hi & Hp) | Hno]; [left; exists i; split; [lia | exact Hp] |].
  right. intros i Hi Hp. destruct (decide (i = b)) as [-> | Hne].
  - apply Hn. split; [lia | exact Hp].
  - exact (Hno i ltac:(lia) Hp).
Qed.

Lemma range_max (P : nat -> Prop) `{!forall i, Decision (P i)} (a b : nat) :
  (exists i, a <= i < b /\ P i /\ forall i', i < i' < b -> ~ P i')
  \/ (forall i, a <= i < b -> ~ P i).
Proof using.
  induction b as [| b IH]; [right; intros i Hi; lia |].
  destruct (decide (a <= b /\ P b)) as [[Hab Hb] | Hn].
  - left. exists b. split; [lia |]. split; [exact Hb | intros i' Hi'; lia].
  - destruct IH as [(i & Hi & Hp & Hup) | Hno].
    + left. exists i. split; [lia |]. split; [exact Hp |]. intros i' Hi' Hp'.
      destruct (decide (i' = b)) as [-> | Hne]; [apply Hn; split; [lia | exact Hp'] |].
      exact (Hup i' ltac:(lia) Hp').
    + right. intros i Hi Hp. destruct (decide (i = b)) as [-> | Hne].
      * apply Hn. split; [lia | exact Hp].
      * exact (Hno i ltac:(lia) Hp).
Qed.

Lemma not_ne_nil (s : bytes) : ~ s <> [] -> s = [].
Proof using. intros H. destruct (decide (s = [])) as [He | He]; [exact He | by destruct (H He)]. Qed.

Section fire.
  Context (ws : list bytes) (n : nat).
  Hypothesis Hn : 1 <= n.
  Local Notation L := (wl_line (drop 1 ws)).

  (* the conflicting committed writer *)
  Definition EXw (v : wid -> bytes) (w : wid) (s : bytes) : Prop :=
    exists w', v w' <> [] /\ EXf n L w s w' (v w').

  Lemma fire_src_aS (k : nat) (s : bytes) : fire_src L (WLeft k) s -> aS k s.
  Proof using.
    intros [-> | [Hk ->]]; destruct k as [| k]; cbn; unfold aP, aM; tauto.
  Qed.

  (* A NON-TERMINAL COMMIT *)
  Lemma fire_nt (v : wid -> bytes) (w : wid) (s : bytes) :
    real ws n v -> v w = [] -> w ∈ wids n -> fire_src L w s -> termw w s = false ->
    real ws n (vupd v w s) \/ EXw v w s.
  Proof using Hn.
    intros Hre Hw0 Hw Hf Ht. rewrite wids_elem in Hw.
    destruct w as [k | k |].
    - (* ---- sh node k's pipe panic ---- *)
      assert (Hs : s = dg_pipe_b).
      { destruct Hf as [-> | ->]; [reflexivity |]. cbn in Ht. rewrite bool_decide_true in Ht; done. }
      subst s.
      destruct Hre as [(k0 & Hk0 & Hpf0 & Hsh0 & Hlf0 & Hlast0 & Hab0) | (Hsh & Hab & HT & Hch)].
      + right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
        left. exists k0. split; [reflexivity |]. split; [exact Hk0 |].
        split; [intros ->; rewrite Hpf0 in Hw0; vm_compute in Hw0; discriminate Hw0 | by left].
      + destruct (range_dec (fun j => v (WLeft j) <> []) k n) as [(j & Hj & Hnz) | Hnone].
        * right. exists (WLeft j). split; [exact Hnz |]. right. right. left.
          exists j. split; [reflexivity |]. split; [lia |].
          rewrite bool_decide_true; [| reflexivity]. split; [lia | exact Hnz].
        * destruct (decide (v WLast = [])) as [Hl0 | Hl0].
          -- left. left. exists k. split; [exact Hw |]. split; [apply vupd_self |].
             split; [intros j Hj Hjk; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
             split; [intros j Hj; rewrite vupd_other; [exact (not_ne_nil _ (Hnone j Hj)) | congruence] |].
             split; [rewrite vupd_other; [exact Hl0 | congruence] |].
             intros j Hj. rewrite vupd_other; [apply Hab; lia | congruence].
          -- right. exists WLast. split; [exact Hl0 |]. right. right. right. split; [reflexivity | exact Hl0].
    - (* ---- stage k's exec failure, or a middle cat's write error ---- *)
      pose proof (fire_src_aS k s Hf) as HaS.
      destruct Hre as [(k0 & Hk0 & Hpf0 & Hsh0 & Hlf0 & Hlast0 & Hab0) | (Hsh & Hab & HT & Hch)].
      + destruct (decide (k0 <= k)) as [Hle | Hgt].
        * right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
          left. exists k0. split; [reflexivity |]. split; [exact Hk0 |]. left. split; [exact Hle | reflexivity].
        * left. left. exists k0. split; [exact Hk0 |].
          split; [rewrite vupd_other; [exact Hpf0 | congruence] |].
          split; [intros j Hj Hjk; rewrite vupd_other; [exact (Hsh0 j Hj Hjk) | congruence] |].
          split; [intros j Hj; rewrite vupd_other; [exact (Hlf0 j Hj) | intros Hq; injection Hq; lia] |].
          split; [rewrite vupd_other; [exact Hlast0 | congruence] |].
          intros j Hj. destruct (decide (j = k)) as [-> | Hne].
          -- rewrite vupd_self. exact HaS.
          -- rewrite vupd_other; [exact (Hab0 j Hj) | congruence].
      + destruct Hf as [Hex | [Hk0 Hwr]].
        * (* THE EXEC FAILURE: nothing may have come down to the content writer *)
          destruct (decide (v WLast = [] \/ v WLast = dg_execR)) as [Hnd | Hd].
          -- left. right. split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
             split; [intros j Hj; destruct (decide (j = k)) as [-> | Hne];
                     [rewrite vupd_self; exact HaS | rewrite vupd_other; [exact (Hab j Hj) | congruence]] |].
             split; [rewrite vupd_other; [exact HT | congruence] |].
             intros D HD Hne Hnx. rewrite vupd_other in HD; [| congruence].
             exfalso. destruct Hnd as [Hq | Hq]; rewrite Hq in HD; subst D; [exact (Hne eq_refl) | exact (Hnx eq_refl)].
          -- right. exists WLast. split; [tauto |].
             destruct (decide (v WLast = L)) as [HL | HL].
             ++ right. right. split; [exact Hex |]. split; [reflexivity |].
                split; [exact HL |]. rewrite <- HL. tauto.
             ++ left. split; [tauto |]. intros [Hq | Hq]; [exact (HL Hq) | tauto].
        * (* A WRITE ERROR: a halted cat is a source of the corner *)
          subst s. left. right.
          split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
          split; [intros j Hj; destruct (decide (j = k)) as [-> | Hne];
                  [rewrite vupd_self; exact HaS | rewrite vupd_other; [exact (Hab j Hj) | congruence]] |].
          split; [rewrite vupd_other; [exact HT | congruence] |].
          intros D HD Hne Hnx. rewrite vupd_other in HD; [| congruence].
          destruct (Hch D HD Hne Hnx) as [(i & Hi & Hic & Hib) | (Hall & Hl0 & HDL)].
          -- left. assert (Hik : i <> k) by (intros ->; rewrite Hic in Hw0; vm_compute in Hw0; discriminate).
             destruct (decide (k < i)) as [Hlt | Hge].
             ++ exists i. split; [exact Hi |]. split; [rewrite vupd_other; [exact Hic | congruence] |].
                intros i' Hi'. rewrite vupd_other; [apply Hib; lia | intros Hq; injection Hq; lia].
             ++ exists k. split; [lia |]. split; [apply vupd_self |].
                intros i' Hi'. rewrite vupd_other; [apply Hib; lia | intros Hq; injection Hq; lia].
          -- left. exists k. split; [lia |]. split; [apply vupd_self |].
             intros i' Hi'. rewrite vupd_other; [apply Hall; lia | intros Hq; injection Hq; lia].
    - (* ---- the last cat: content, or its exec failure ---- *)
      destruct Hre as [(k0 & Hk0 & Hpf0 & Hsh0 & Hlf0 & Hlast0 & Hab0) | (Hsh & Hab & HT & Hch)].
      + right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
        left. exists k0. split; [reflexivity |]. split; [exact Hk0 | by left].
      + assert (Hrest : forall s', s' = dg_execR \/ s' `prefix_of` L ->
                  (forall D, s' = D -> D <> [] -> D <> dg_execR -> upok ws n (vupd v WLast s') D) ->
                  real ws n (vupd v WLast s')).
        { intros s' HT' Hch'. right.
          split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
          split; [intros j Hj; rewrite vupd_other; [exact (Hab j Hj) | congruence] |].
          split; [rewrite vupd_self; exact HT' |].
          intros D HD. rewrite vupd_self in HD. exact (Hch' D HD). }
        destruct (decide (s = dg_execR)) as [-> | Hsx].
        * left. apply Hrest; [by left |]. intros D HD Hne Hnx. by destruct (Hnx (eq_sym HD)).
        * destruct Hf as [HsL | Hsx']; [| by destruct (Hsx Hsx')]. subst s.
          destruct (range_max (fun i => v (WLeft i) <> []) 1 n) as [(i & Hi & Hnz & Hup) | Hnone].
          -- destruct i as [| i]; [lia |].
             destruct (Hab (S i) ltac:(lia)) as [Hq | Hq]; [exact (False_rect _ (Hnz Hq)) |].
             destruct Hq as [Hq | Hq].
             ++ right. exists (WLeft (S i)). split; [exact Hnz |]. right. right.
                split; [reflexivity |]. split; [exact Hsx |]. exists (S i).
                split; [reflexivity |]. split; [lia | exact Hq].
             ++ left. apply Hrest; [right; reflexivity |]. intros D HD Hne Hnx. left.
                exists (S i). split; [lia |]. split; [rewrite vupd_other; [exact Hq | congruence] |].
                intros i' Hi'. rewrite vupd_other; [exact (not_ne_nil _ (Hup i' Hi')) | congruence].
          -- destruct (Hab 0 ltac:(lia)) as [Hq | Hq].
             ++ left. apply Hrest; [right; reflexivity |]. intros D HD Hne Hnx. right.
                split; [intros i Hi; rewrite vupd_other; [exact (not_ne_nil _ (Hnone i Hi)) | congruence] |].
                split; [rewrite vupd_other; [exact Hq | congruence] | by rewrite HD].
             ++ right. exists (WLeft 0). split; [rewrite Hq; vm_compute; discriminate |]. right. right.
                split; [reflexivity |]. split; [exact Hsx |]. exists 0.
                split; [reflexivity |]. split; [lia | exact Hq].
  Qed.
  Lemma alt_forkc_ne_pipe : alt_forkc <> dg_pipe_b.
  Proof using. vm_compute. discriminate. Qed.

  (* THE TERMINAL COMMIT: node [k]'s fork failed on a run *)
  Lemma fire_t1 (v : wid -> bytes) (k : nat) :
    real ws n v -> (forall x, x ∉ wids n -> v x = []) -> v (WSh k) = [] -> k < n ->
    realT n (vupd v (WSh k) alt_forkc) k \/ EXw v (WSh k) alt_forkc.
  Proof using.
    clear Hn. intros Hre Hdom Hw0 Hk.
    assert (Hout : forall j, n <= j -> v (WSh j) = [] /\ v (WLeft j) = []).
    { intros j Hj. split; apply Hdom; rewrite wids_elem; lia. }
    destruct Hre as [(k0 & Hk0 & Hpf0 & _) | (Hsh & Hab & HT & Hch)].
    - right. exists (WSh k0). rewrite Hpf0. split; [vm_compute; discriminate |]. right.
      left. exists k0. split; [reflexivity |]. split; [exact Hk0 |].
      split; [intros ->; rewrite Hpf0 in Hw0; vm_compute in Hw0; discriminate Hw0 | by left].
    - destruct (range_dec (fun j => v (WLeft j) <> []) (S k) n) as [(j & Hj & Hnz) | Hnone].
      + right. exists (WLeft j). split; [exact Hnz |]. right. right. left.
        exists j. split; [reflexivity |]. split; [lia |].
        rewrite bool_decide_false; [| exact alt_forkc_ne_pipe]. split; [lia | exact Hnz].
      + destruct (decide (v WLast = [])) as [Hl0 | Hl0].
        * left. split; [exact Hk |]. split; [apply vupd_self |].
          split.
          { intros j Hj. rewrite vupd_other; [| congruence].
            destruct (decide (j < n)); [exact (Hsh j ltac:(lia)) | exact (proj1 (Hout j ltac:(lia)))]. }
          split.
          { intros j Hj. rewrite vupd_other; [| congruence].
            destruct (decide (j < n));
              [exact (not_ne_nil _ (Hnone j ltac:(lia))) | exact (proj2 (Hout j ltac:(lia)))]. }
          split; [rewrite vupd_other; [exact Hl0 | congruence] |].
          intros j Hj. rewrite vupd_other; [exact (Hab j ltac:(lia)) | congruence].
        * right. exists WLast. split; [exact Hl0 |]. right. right. right. split; [reflexivity | exact Hl0].
  Qed.

  (* A COMMIT AFTER THE TERMINAL ONE: admitted by the terminal vector, or
     refuted by the failed fork's own deposit *)
  Lemma fire_t2 (v : wid -> bytes) (i : nat) (w : wid) (s : bytes) :
    realT n v i -> v w = [] -> w ∈ wids n -> fire_src L w s ->
    realT n (vupd v w s) i \/ EXw v w s.
  Proof using.
    clear Hn. intros (Hi & Hf & Hsh & Hlf & Hlast & Hab) Hw0 Hw Hfs. rewrite wids_elem in Hw.
    destruct w as [k | k |].
    - right. exists (WSh i). rewrite Hf. split; [vm_compute; discriminate |]. right. left.
      exists i. split; [reflexivity |]. split; [exact Hi |].
      split; [intros ->; rewrite Hf in Hw0; vm_compute in Hw0; discriminate Hw0 | by right].
    - destruct (decide (k <= i)) as [Hle | Hgt].
      + left. split; [exact Hi |]. split; [rewrite vupd_other; [exact Hf | congruence] |].
        split; [intros j Hj; rewrite vupd_other; [exact (Hsh j Hj) | congruence] |].
        split; [intros j Hj; rewrite vupd_other; [exact (Hlf j Hj) | intros Hq; injection Hq; lia] |].
        split; [rewrite vupd_other; [exact Hlast | congruence] |].
        intros j Hj. destruct (decide (j = k)) as [-> | Hne].
        * rewrite vupd_self. exact (fire_src_aS k s Hfs).
        * rewrite vupd_other; [exact (Hab j Hj) | congruence].
      + right. exists (WSh i). rewrite Hf. split; [vm_compute; discriminate |]. right. left.
        exists i. split; [reflexivity |]. split; [exact Hi |]. right. split; [lia | reflexivity].
    - right. exists (WSh i). rewrite Hf. split; [vm_compute; discriminate |]. right. left.
      exists i. split; [reflexivity |]. split; [exact Hi | by right].
  Qed.

  (* every commit of the round has a source *)
  Lemma fire_src_ne (w : wid) (s : bytes) : fire_src L w s -> s <> [].
  Proof using.
    destruct w as [k | k |]; cbn [fire_src]; unfold panic_src.
    - intros [-> | ->]; vm_compute; discriminate.
    - intros [-> | [_ ->]]; [destruct k; vm_compute; discriminate | vm_compute; discriminate].
    - intros [-> | ->]; [| vm_compute; discriminate].
      unfold wl_line. intros Hq. apply app_eq_nil in Hq as [_ Hq]. discriminate Hq.
  Qed.
End fire.
