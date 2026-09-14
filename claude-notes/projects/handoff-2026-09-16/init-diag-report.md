# lane INIT-DIAG (M6b preparation) -- report

Checkout `/shared/xv6iris-2-sup`, branch `lane/init-diag`, based at
`17c05c746` (= origin/main's code `b7c49dea2` plus notes commits; origin/main
is now `914636f01`, notes-only since -- no rebase needed).
COMMIT: `aff0a688b` "INIT-DIAG: init's two payable diagnostics through the
era's links (M6b preparation)" -- two NEW files + two `_CoqProject` rows,
765 insertions; no existing `iris/*.v` touched; not pushed.

Terms used below.  A CREDENTIAL is the linear resource a process must hold
to put bytes on the console wire under the application's claim: the era's
write cursor `turn v P` (a ghost half saying "P process bytes are out this
era") together with two persistent lower bounds `ps_lb v ps` / `cs_lb v cs`
(which prologue-round and line alternatives the transcript has already
resolved) and `E_lb v n` (at least `n` typed bytes echoed), all pinned to the
era by `era_pin γ k v`.  A LINK (`echo_links`) is the persistent law that
lets a byte through the kernel's console contract (`out_link`) at the
credential and hands the credential back one byte on.  A pure SHAPE
(`wr_pro`, `wr_blk`, `wr_ban`, ...) says where in the transcript the cursor
stands.  `pro_alts` is the list of the three things the wire may say after
init's banner (`"$ "`, `"init: exec sh failed\n"`, `"init: fork failed\n"`);
`pro_round = 39` is one failed sub-round in wire bytes (banner 18 + exec
diagnostic 21).  TAINT `T` is the persistent proposition that stands in for
any credential once the application's claim has been forfeited (a killed
process); every family below has `∨ T` as its right arm.  AFFINE means a
resource may be dropped without proof obligation.

## Files

- `iris/EchoLinksPro.v` (383 lines; requires EchoLinks; `_CoqProject` row
  right after `EchoLinks.v`): the pure shapes and the Iris credential
  families, in EchoLinks's own section mould (`Context (T) (γ)`,
  `Persistent T`, `Timeless T`, `riscvGS`).
- `iris/UInitDiag.v` (380 lines; requires UInitBanner, EchoLinksPro; row
  right after `UInitBanner.v`): init's per-byte obligation at a diagnostic
  and the two payments, on UInitBanner's mould.  UkWriteClosed was not
  needed.  (Its header comment cites `user/init.c:30` / `:35`; that is
  upstream xv6-riscv's `user/init.c` -- the C source is not in this tree,
  only its Rocq image `user-rocq/Init*.v`.)

## (1) THE ROUND-OPEN CREDENTIAL, EXACTLY

```coq
Definition ewc_pro (v : era_pins) (n : nat) : iProp Σ :=
  ((∃ ps cs P : _, ⌜wr_pro ps cs n P⌝ ∗ turn v P ∗ ps_lb v ps
      ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.
Global Instance ewc_pro_timeless v n : Timeless (ewc_pro v n).
Lemma ewc_pro_taint v n : T -∗ ewc_pro v n.
Lemma ewc_owed_of_pro (v : era_pins) (n : nat) : ewc_pro v n -∗ ewc_owed T v n.
Lemma ewc_ban_done_pro (v : era_pins) (n : nat) :
  ewc_ban T v n (length u_banner) -∗ ewc_pro v n.
```

(`ewc_ban_done_pro` is `EchoLinks.ewc_ban_done`'s proof stopped one step
early: `wr_ban_pro` gives `wr_pro` at `P + length u_banner`.)

`ewc_pro_of_owed_round_start` is NOT provable and was not written.  Which
fact would refute `wr_blk`: NONE that init holds.  The two arms of `wr_owed`
differ only in the line-choice count (`wr_pro`: `n/17 = length cs`, the
last line's block was the shell's fork panic, the prologue is open;
`wr_blk`: `n/17 = S (length cs)`, the last line's block is still owed) and
init names no line choice; the era's bounds are persistent LOWER bounds, so
`cs_lb v [3]` and `cs_lb v []` are jointly consistent.  The witness, proved
in the file:

```coq
Lemma wr_owed_ambiguous :
  wr_pro [0%nat] [3%nat] 17%nat 43%nat /\ wr_blk [0%nat] [] 17%nat 20%nat.
```

(both shapes at count 17 -- one line typed -- with prefix-comparable
`cs`).  So the disjunction, once introduced, cannot be undone from the
holder's side.  THE CLEAR STATEMENT: FORK-REFUND (`UkFork.wp_uk_ecall_fork`'s
`-1` arm, `⌜r = -1⌝ ∗ uch Sc ∗ Rc`) returns `Rc` whole, so if `Rc` carries
the `ewc_pro`-shaped credential there is nothing to refute -- the fork
diagnostic is paid from the refunded `Rc` through `echo_link_pro` at a = 2
directly.  What has to change for that is only the SHAPE init keeps:
`UInitBanner.kinit_own n` (stated at `ewc_owed`) must not be what init
holds across its fork; `UInitDiag.kinit_pro n` (below) is, with
`kinit_own_of_pro` as the lend to sh (`kinit_own` is the shape
`UShOut.sh_prompt_pay_of_ushpr` (UShOut.v:424) takes) and
`kinit_banner_law_pro_holds` as the banner law that leaves it.

## (2) THE DIAGNOSTIC'S BYTES THROUGH THE LINKS

The pure shape after byte 0 (from `wr_pro_dollar`'s proof, generalised to
any alternative `a`): the open prologue `replicate j 1` becomes
`replicate j 1 ++ [a]` and the block grows by `pro_alts !!! a` (and, at
a = 1 only, by the next banner: `pro_of_replicate_snoc`); the cursor is the
round's base plus `pro_round * j` plus the banner plus `i` bytes.

```coq
Definition wr_pdiag (ps cs : list nat) (n P a i : nat) : Prop :=
  pro_pin ps cs n
  /\ (n `mod` length echo_line)%nat = 0%nat
  /\ (n `div` length echo_line)%nat = length cs
  /\ (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat)
  /\ (exists j : nat,
        pro_from (pro_idx cs (n `div` length echo_line)) ps
        = replicate j 1%nat ++ [a]
        /\ P = (length (proc_upto ps cs n) + length (wr_pre cs n)
                + pro_round * j + length u_banner + i)%nat).

Lemma wr_pdiag_byte (ps cs : list nat) (n P a i : nat) (b : bv 8) :
  wr_pdiag ps cs n P a i -> pro_alts !!! a !! i = Some b ->
  proc_upto ps cs (S n) !! P = Some b.
Lemma wr_pdiag_1_of_pro (ps cs : list nat) (n P a : nat) :
  wr_pro ps cs n P -> wr_pdiag (ps ++ [a]) cs n (S P) a 1%nat.
Lemma wr_pdiag_S (ps cs : list nat) (n P a i : nat) :
  wr_pdiag ps cs n P a i -> wr_pdiag ps cs n (S P) a (S i).
Lemma wr_pdiag_done_1 (ps cs : list nat) (n P i : nat) :
  i = length (pro_alts !!! 1%nat) ->
  wr_pdiag ps cs n P 1%nat i -> wr_ban ps cs n P.
```

The Iris family (`0` IS `ewc_pro`, definitionally):

```coq
Definition ewc_pdg (v : era_pins) (n a i : nat) : iProp Σ :=
  ((∃ ps cs P : _, ⌜wr_pdiag ps cs n P a i⌝ ∗ turn v P ∗ ps_lb v ps
      ∗ cs_lb v cs ∗ E_lb v n) ∨ T)%I.
Definition ewc_pdiag (v : era_pins) (n a i : nat) : iProp Σ :=
  match i with O => ewc_pro v n | S _ => ewc_pdg v n a i end.
Global Instance ewc_pdg_timeless v n a i : Timeless (ewc_pdg v n a i).
Global Instance ewc_pdiag_timeless v n a i : Timeless (ewc_pdiag v n a i).
Lemma ewc_pdiag_taint v n a i : T -∗ ewc_pdiag v n a i.
Lemma ewc_pdiag_0 (v : era_pins) (n a : nat) : ewc_pro v n -∗ ewc_pdiag v n a 0%nat.
Lemma echo_pdiag_step (k : nat) (v : era_pins) (n a i : nat) (b : bv 8) (Φ : iProp Σ) :
  pro_alts !!! a !! i = Some b ->
  era_pin γ k v -∗ echo_links T γ -∗ ewc_pdiag v n a i -∗
  (ewc_pdiag v n a (S i) -∗ Φ) -∗
  out_link Uart0 k b Φ.
Lemma ewc_pdiag_done_1 (v : era_pins) (n : nat) :
  ewc_pdiag v n 1%nat (length (pro_alts !!! 1%nat)) -∗ ewc_ban T v n 0%nat.
```

`echo_pdiag_step`: byte 0 through `echo_links_pro` (files `ps ++ [a]`;
`a < length pro_alts` is derived from the lookup by
`pro_alts_lt_of_lookup`), bytes 1.. through `echo_links_w`, the taint arm
through `echo_links_taint` exactly as `echo_banner_step`.  End shape for
a = 1: `wr_ban` with one more failed sub-round (`∃ j` becomes `S j`,
`replicate_S_end`) at the SAME count `n` -- what `UInitBanner.kinit_ban n`
is built from.  For a = 2 there is no end shape; the last byte hands back
`ewc_pdiag v n 2 18`, which the payment drops (affine).

Pure facts established about the literals (all by `vm_compute`/`reflexivity`
in closed lemmas, no variables in any `vm_compute` goal):

```coq
Lemma pro_alts_1_length : length (pro_alts !!! 1%nat) = 21%nat.
Lemma pro_alts_2_length : length (pro_alts !!! 2%nat) = 18%nat.
Lemma pro_round_alts :
  pro_round = (length u_banner + length (pro_alts !!! 1%nat))%nat.
Lemma pro_alts_lt_of_lookup (a i : nat) (b : bv 8) :
  pro_alts !!! a !! i = Some b -> (a < length pro_alts)%nat.
Lemma pro_of_replicate_snoc (j a : nat) :
  pro_of (replicate j 1%nat ++ [a])
  = pro_of (replicate j 1%nat) ++ pro_alts !!! a ++ pro_more a u_banner.
Lemma pending_n_round_wr_pre (ps cs : list nat) (n : nat) :
  (n `mod` length echo_line)%nat = 0%nat ->
  (n = 0%nat \/ cs !!! (n `div` length echo_line - 1)%nat = 3%nat) ->
  pending_n ps cs n
  = wr_pre cs n ++ pro_of (pro_from (pro_idx cs (n `div` length echo_line)) ps).
```

(inside `wr_pdiag_done_1`, also `length u_banner = 18`, `pro_round = 39`,
`length (pro_alts !!! 1) = 21` as local asserts by `vm_compute`;
`pending_n_round_wr_pre` is `EchoOutPure.pending_n_round_pre` spelt with
`EchoLinks.wr_pre`).  Nothing I needed failed to be established; no goal
was left open.

## (3) INIT'S PER-BYTE OBLIGATION AT THE DIAGNOSTIC, AND THE PAYMENTS

`init_lit a j` is the `j`-th byte of init's rodata string at address `a`
(`UkInitLit`); `LIT_EXEC := 0x9b0`, `LIT_FORK := 0x990` (local notations,
as in `UkInitMain`'s table).

```coq
Lemma init_execfail_bytes (j : nat) :
  (j < 21)%nat -> pro_alts !!! 1%nat !! j = Some (init_lit 0x9b0 j).
Lemma init_forkfail_bytes (j : nat) :
  (j < 18)%nat -> pro_alts !!! 2%nat !! j = Some (init_lit 0x990 j).
```

(each from a `forallb ... (seq 0 len) = true` closed lemma by `vm_compute`,
then `forallb_forall` + `bv_eq`, the pattern of `UInitBanner.init_banner_bytes`.)

```coq
Definition pdg (v : era_pins) (n a i : nat) : iProp Σ := EchoLinksPro.ewc_pdiag T v n a i.

Lemma kinit_w1_of_link_pdiag (N : uk_names Σ) (v : era_pins) (n : nat)
    (l : list fdstate) (rb : bool) (a i : nat) (b : bv 8) :
  l !! 1%nat = Some (FdOpen rb true (FdDevice CONSOLE)) ->
  pro_alts !!! a !! i = Some b ->
  era_pin γ (S gen_id) v -∗ echo_links T γ -∗
  UkInit.kinit_w1 N (mword_of_int 1 : mword 64) b
    (UserFd.ustd (ukn_fd N) l ∗ pdg v n a i)
    (UserFd.ustd (ukn_fd N) l ∗ pdg v n a (S i)).

Definition kinit_pro (n : nat) : iProp Σ :=
  (∃ v : era_pins, era_pin γ (S gen_id) v ∗ EchoLinksPro.ewc_pro T v n)%I.
Global Instance kinit_pro_timeless n : Timeless (kinit_pro n).
Lemma kinit_own_of_pro (n : nat) : kinit_pro n -∗ UInitBanner.kinit_own T γ n.
Lemma kinit_banner_law_pro_holds :
  echo_links T γ -∗
  □ (∀ (n : nat) (N : uk_names Σ),
       UInitBanner.kinit_ban T γ n -∗
       UkInitMain.kinit_banner0 N stc_cons (kinit_pro n)).
Lemma kinit_execfail_law_holds :
  echo_links T γ -∗
  □ (∀ (n : nat) (N : uk_names Σ),
       kinit_pro n -∗
       UkInit.kinit_banner_pay N stc_cons 21%nat (init_lit 0x9b0)
         (UInitBanner.kinit_ban T γ n)).
Lemma kinit_forkfail_law_holds :
  echo_links T γ -∗
  □ (∀ (n : nat) (N : uk_names Σ),
       kinit_pro n -∗
       UkInit.kinit_banner_pay N stc_cons 18%nat (init_lit 0x990) emp).
```

(`stc_cons := FdOpen true true (FdDevice CONSOLE)`, the console descriptor
/init's open installs, as in UInitBanner.)  `UkInit.kinit_banner_pay N stc
len f Rt` (UkInit.v:1354) is generic in the literal -- "give me the
descriptor table at `ufd_l3 stc` and I give you a per-byte family `Ch` for
the `len` bytes `f` at fd 1, its start token, and `Ch len -∗ table ∗ Rt`"
-- and it is exactly the `∃ Ch` that `UkInitPrintf.wp_kinit_printf_chain`
(UkInitPrintf.v:107) consumes, so the two laws are in the shape the die
sites will spend.  `kinit_w1_of_link_pdiag` is `UInitBanner.kinit_w1_of_link`
(UInitBanner.v:184) with `EchoLinksPro.echo_pdiag_step` in
`echo_banner_step`'s place and otherwise the same proof (the byte split,
the deposit at the caller's cursor family via `uwrite_chain_sup`, the short
arm refuted by `uwrite_no_short`).

## HOW EACH DIE DIAGNOSTIC IS WRITTEN TODAY, AND WHAT IT WOULD NEED

There are no identifiers `die_de` / `die_df` / `die_dw`; they are the
suffixes of the three lemmas `UkInitMain.wp_kinit_main_die_de` / `_df` /
`_dw`.  All three have the SAME premise shape (UkInitMain.v:167-174,
279-286, 391-398): `ukn_pay N' (-1) -∗ udepw_law 16 -∗ init_code -∗
init_rodata -∗ urun N' h m <pc> _ -∗ WP Loop` -- i.e. they are NOT threaded
with a per-byte family; each spends the free write law `udepw_law 16` (out
of `UkInit.init_deps`) through the free form of the printf tower.  So per
the brief I did not thread them (M6b proper, in UkInit*/UkInitMain).

- "init: exec sh failed\n" (21 B): `wp_kinit_main_die_de` (UkInitMain.v:279;
  `udepw_law 16 -∗` at :283); the write at :353 `wp_kinit_printf N' 0x9b0
  21%nat (init_lit 0x9b0) ...` with `"Hwr Hcode Hstrde Hrun"`.
  `UkInitPrintf.wp_kinit_printf` (UkInitPrintf.v:661) is
  `wp_kinit_printf_chain` at `Ch := fun _ => emp`, each byte paid by
  `UkInit.kinit_w1_of_law` (UkInit.v:1309) from `udepw_law 16`.  Reached
  from `wp_kinit_main_child` (:520)'s failing-exec arm at :715-716
  (`with "Hpayret Hwr Hcode Hro Hrun"`).  THIS ARM IS THE CHILD's.  It
  would need: the credential init lent at the fork (`Rc`, the `kinit_pro n`
  shape after M6a(3) step 3), the ledger `ustd (ukn_fd N') (ufd_l3
  stc_cons)` at the site (the child's table is its parent's), and the call
  replaced by `wp_kinit_printf_chain 0x9b0 21 (init_lit 0x9b0) Ch` with the
  `∃ Ch` of `kinit_execfail_law_holds` opened; the `Ch 21 -∗ table ∗
  kinit_ban n` it leaves is the banner credential the child's exit payload
  must carry back to init (`Rd n` in `Q`).  The lemma's statement gains the
  credential (or an opaque `Bn` plus the persistent law, `kinit_ban_law`
  (:1030)'s pattern) and the ledger.
- "init: fork failed\n" (18 B): `wp_kinit_main_die_df` (UkInitMain.v:167;
  `udepw_law 16 -∗` at :171); the write at :241 `wp_kinit_printf N' 0x990
  18%nat (init_lit 0x990) ...`, same free form.  Reached from
  `wp_kinit_main_loop` (:1116)'s fork `-1` arm at :1334-1335
  (`iDestruct Hpayfree as "Hpay". iApply (wp_kinit_main_die_df N hp2 _ n
  with "Hpay Hwr Hcode Hro Hrun")`).  TODAY'S REFUND IS DROPPED:
  `wp_kinit_fork` (:757) lends `Rc := upos γ np ∗ ucons_pay cn γ T Rd (-1)
  ∗ (Rt ∨ True)` to `UkFork.wp_uk_ecall_fork` at :881-883, and at :937 its
  `-1` arm destructs the ecall's `⌜r = -1⌝ ∗ uch Sc ∗ Rc` as `(%Hm1 & Hf &
  _)` -- the `_` is the refunded `Rc`, thrown away (the comment at :934-936
  says so: "threading it out to init's 'init: fork failed' print is lane
  IO-LEAF's").  So `wp_kinit_fork`'s `-1` post hands the caller only
  `⌜r = -1⌝ ∗ uch Sc`.  It would need: `wp_kinit_fork`'s `-1` arm to keep
  the `Rt` conjunct of the refund and put it in its post (`Rt` instantiated
  at `kinit_pro n` -- `Rt ∨ True` today, so the arm is `kinit_pro n ∨ True`
  and the `True` side has nothing to pay with unless the lend stops being
  `∨ True` for round 0), the ledger at the site, and `wp_kinit_printf_chain
  0x990 18 (init_lit 0x990) Ch` with `kinit_forkfail_law_holds`'s `Ch`;
  nothing comes back (`Rt := emp`).
- "init: wait returned an error\n" (29 B): `wp_kinit_main_die_dw`
  (UkInitMain.v:391; write at :465 `wp_kinit_printf N' 0x9c8 29%nat
  (init_lit 0x9c8)`), reached from `wp_kinit_main_loop` at :1678-1679 (also
  from `Hpayfree`).  No `pro_alts` entry; not payable by any link; per the
  M6a(2) finding (a) not deletable either (a killed init) -- the owner
  question in the M6a(3) review note.  Untouched here.

## Gate

Build: the previous attempt's `./gcp-rocq/vmbuild.sh xv6iris-2-sup id-4`
(rebased full build) on the VM tree `/mnt/rocq/trees/_shared_xv6iris-2-sup`;
local md5s of `iris/EchoLinksPro.v` (`caa8aac0388eed933effaabd95049900`),
`iris/UInitDiag.v` (`806b56cf71e79a9165b56a87df2c358d`) and
`iris/_CoqProject` (`783156d047885afba7b2a506a5e7efdb`) equal the VM tree's
copies, so no rebuild was run.

```
/tmp/id-4.log:  EXIT=0            (line 32)
grep -c "^Error" /tmp/id-4.log  -> 0
grep -c "ROCQ compile" /tmp/id-4.log -> 4   (COMPILED=4)
VM: make -f CoqMakefile -n | grep -c "ROCQ compile" -> 0
python3 tools/lemma_diff.py --ref origin/main
  -> 2 file(s) checked -- CLEAN (nothing dropped, nothing admitted, no new assumption)
grep -n 'Admitted\|admit\.' iris/EchoLinksPro.v iris/UInitDiag.v -> (no matches)
./gcp-rocq/run-on-gcp --check-dumps
  -> ==> syncing /shared/xv6iris-2-sup -> /mnt/rocq/trees/_shared_xv6iris-2-sup
     ==> already up to date
     ==> the VM's tracked dumps match this checkout
VM: make audit-only 2>&1 | grep -v '^make\|^cd ' | md5sum
  -> 57f7327206c4b276d05035342fea8ecf  -      (= the expected value: proof-side only)
```

Commit: `aff0a688b` on `lane/init-diag`, explicit paths (`git add
iris/EchoLinksPro.v iris/UInitDiag.v iris/_CoqProject`), author = the
checkout's config, message ends with the Co-Authored-By and Claude-Session
lines; `git status --short` is empty after the commit.  Not pushed.
