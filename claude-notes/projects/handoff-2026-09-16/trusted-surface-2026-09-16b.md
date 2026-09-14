# The trusted surface since 09-16 (249b751c2 -> 5c48c3aa2) -- ADDENDUM

Owner's review document, 2026-09-16.  ADDENDUM to
`trusted-surface-2026-09-16.md`, which was written at `249b751c2`; it
extends that document and does not repeat it.  Scope: every
TRUSTED-STATEMENT change the applications project landed on `main` in the
forty-three commits since -- the lanes PROLOGUE-ALTS-2, IO-LEAF (M1 a-f,
M2, M3a, M3b(1), M3c, M4a(1)/(2a)/(3), M5a), TXT-ROW, DUP-ROW,
TRAP-ROWS M2 parts 1 and 2, and TRAP-ROWS-3 T4(c).  A TRUSTED STATEMENT is,
as before, the top theorem's statement and hypotheses, the pure predicates
on the run's trace that it is stated over, and the kernel-spec rows the
program proofs read.  Line numbers are of `5c48c3aa2` (`origin/main` is
`46e3685b4`, a notes-only commit on top).

WHAT CHANGED IN WHAT THE THEOREM ASSUMES.  Nothing, textually: the
hypothesis list is the same six facts about the starting state and the disk
image plus the same `Hsh_owed`, verbatim -- `iris/UInitBootAdequacy.v` has
no diff in this range.  `Hphi` was already gone at `249b751c2` and did not
come back.  What moved is the WORK BEHIND the third `Hsh_owed` conjunct --
sh's console READ LEAF, the one entailment lane IO-LEAF owes.  The lane
landed five of its six milestones: /init's banner, echo's four writes, sh's
fork and wait, sh's prompt and, in M5a, the read leaf itself at the era's
own read link -- proved as `UShLine.ush_read_recv_era`, whose supply is a
credential riding sh's console lease.  The conjunct is not yet closed
because that credential has to reach sh at the entry of EVERY round of
/init's restart loop; the ruling of 2026-09-16 (M5b) is that it rides the
SHELL'S EXIT PAYLOAD, which is a change to `UserConsole.ucons_pay` and so
IS a trusted change -- planned, not landed (section 4).

WHAT DID NOT CHANGE.  The CONCLUSION: `app_phi app_echo g2 κs` at the same
`AppEcho.echo_phi`, `iris/AppEcho.v` untouched.  The DISCIPLINE'S TRUSTED
DEFINITIONS: `iris/EchoDisc.v` is purely additive in this range (+96 lines,
no deletion) -- `line_alts` including `line_alts !!! 3 = "fork\n"`,
`pro_alts`, `sess_n`, `expected_rel`, `disc_seg'`, `disc_seg`, `disc` and
`good_out` are byte-for-byte what the predecessor quoted, and what
PROLOGUE-ALTS-2 added there are five pure lemmas about `pro_from`/`pro_of`
(`pro_from_app_le`, `pro_from_nil`, `pro_tail_open_snoc`,
`pro_of_open_snoc_lt`, `pro_of_open_app_inj`), no definition.  THE AUDIT:
thirteen assumptions, unchanged (section 5).

## 1. THE THEOREM

`UInitBootAdequacy.echo_adequacy_modulo_phi` (iris/UInitBootAdequacy.v:98,
`Qed`) is UNCHANGED -- the file has an empty diff over the range -- so the
predecessor's quotation stands.  Its one owed hypothesis, verbatim:

```coq
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)
         /\ (forall (c : app_fixed app_echo) (γp : gname)
                    (N : UkRun.uk_names Σ) (l : list FdSlots.fdstate),
               UkRun.ukn_pay N
                 = UserConsole.ucons_pay FsCfg.fsc_cons γp (echo_taint c) ->
               ⊢ UkSh.ush_read_recv_leaf (PS := uprogSG_free) N γp
                   (echo_taint c) FsCfg.fsc_cons l))
```

The three conjuncts, one plain sentence each, and their state now:

1. **`sh_deps`** -- "the shell may make a `write(2)` system call": the
   permission (a DEPOSIT, the Iris resource a process must hand the kernel
   at an `ecall` to be allowed to make it) for system-call number 16, at
   the free program instance.  `UkSh.sh_deps := udepw_law 16`, still
   textually identical.  STATE: still owed, and still needed -- IO-LEAF has
   moved /init's banner and echo's and sh's own writes OFF it onto the
   application's links, but /init's failure diagnostics and rounds after
   the first still print through it (M4b/M6).
2. **`sh_pay_rest sh_Rsh`** -- "the shell's main loop, from the first
   prompt onwards, is correct at the named resource family `sh_Rsh`".
   Unchanged, still SH-LINE 2b R2/R3's.
3. **the READ LEAF** -- "a shell whose exit payload is the console LEASE
   (`ucons_pay`: the reader token for the console ring, or the taint) can
   run the `read(0, buf, n)` at the head of `getcmd` and report which bytes
   it got".  BEING CLOSED NOW, and how: M5a proved exactly this statement's
   body as `UShLine.ush_read_recv_era` (iris/UShLine.v:668), taking beside
   the lease a CREDENTIAL `ush_rd_cred T v n := dl_cnt v (1/2) n ∨ T`
   (iris/UShLine.v:629) -- half of the era's delivered-byte counter, or the
   taint -- and running the leaf through the era's own read link rather
   than the boundary's flat input licence.  Its -1 arm, which the flat
   licence could not refute, is now refuted from the kernel: at an open
   readable console descriptor a read does not return -1 (section 3.1).
   What remains is to put that credential where sh can reach it on every
   round, which is M5b.

NET: the hypothesis list is unchanged; one of its three conjuncts now has a
proof whose only gap is where its supply is parked.

## 2. THE APPLICATION-TO-PROGRAM INTERFACE THAT APPEARED

The application's transcript claim and the programs' walks live in
different tiers: the program tier (`UkInit*`, `UkSh*`, `UkEcho`) may not
name the application's record at all, and the application tier does not
know row 16 of the syscall table.  Three new objects carry payment across
that line.  In each, what crosses is an OPAQUE RESOURCE (a credential the
program cannot look inside) plus a PERSISTENT CONVERSION (a `□`-boxed wand,
freely duplicable, turning the credential into the per-call obligation the
program's walk actually spends).

### 2.1 `EchoLinks.echo_links` -- the console laws as one persistent law

New file `iris/EchoLinks.v`, sitting between `EchoOut` and `AppEcho`.  A
LINK is the application's permission for one byte to reach the wire (or one
window to be consumed by a read) while its transcript claim is preserved.

```coq
(* iris/EchoLinks.v:139 *)
  Definition echo_links : iProp Σ :=
    (echo_link_w ∗ echo_link_blk ∗ echo_link_pro ∗ echo_link_taint
     ∗ echo_link_rd ∗ echo_link_rd_taint)%I.
```

SIX conjuncts (M1(a,b) landed four, M1(d) added the third, M5a the sixth),
each `□`-boxed, each `Persistent`, with `echo_links_holds : ⊢ echo_links`
proved under the record's four equations.  In plain terms: (w) an ordinary
output byte at the era's cursor; (blk) the FIRST byte of a line's
continuation, which files WHICH of the four `line_alts` this line took;
(pro) the first byte of a PROLOGUE round's alternative, which files an
entry of `ps` rather than `cs` (PROLOGUE-ALTS-2's `echo_write_link_pro`,
below); (taint) any byte at all once the application is tainted; (rd) a
console read at the era's delivered count; (rd_taint) a console read on the
taint arm, which must still move the boundary's delivered list.  Two
verbatim, the ones the predecessor had no counterpart for:

```coq
(* iris/EchoLinks.v:98 *)
  Definition echo_link_pro : iProp Σ :=
    (□ ∀ (k : nat) (v : era_pins) (P n0 a : nat) (b : bv 8)
         (ps0 cs0 : list nat) (Φ : iProp Σ),
        ⌜(n0 `mod` length echo_line)%nat = 0%nat⌝ -∗
        ⌜n0 = 0%nat \/ cs0 !!! (n0 `div` length echo_line - 1)%nat = 3%nat⌝ -∗
        ⌜((n0 `div` length echo_line) <= length cs0)%nat⌝ -∗
        ⌜pro_pin ps0 cs0 n0⌝ -∗
        ⌜~ pro_done (pro_from (pro_idx cs0 (n0 `div` length echo_line)) ps0)⌝ -∗
        ⌜P = length (proc_upto ps0 cs0 (S n0))⌝ -∗
        ⌜(a < length pro_alts)%nat⌝ -∗
        ⌜pro_alts !!! a !! 0%nat = Some b⌝ -∗
        era_pin γ k v -∗ turn v P -∗ ps_lb v ps0 -∗ cs_lb v cs0 -∗
        E_lb v n0 -∗
        (((turn v (S P) ∗ ps_lb v (ps0 ++ [a]) ∗ cs_lb v cs0 ∗ E_lb v n0)
          ∨ T) -∗ Φ) -∗
        out_link Uart0 k b Φ)%I.

(* iris/EchoLinks.v:135 *)
  Definition echo_link_rd_taint : iProp Σ :=
    (□ ∀ (k : nat) (ws : list (list mobs * bv 8)) (Φ : iProp Σ),
        T -∗ (T -∗ Φ) -∗ read_link k ws Φ)%I.
```

The claim-side law `echo_link_pro` is quantified is `EchoOut.echo_write_link_pro`
(iris/EchoOut.v:3321), whose statement is the same eight premises; it is
PROLOGUE-ALTS-2's, and it is paid for by a fourth pure conjunct in the
output claim `eout`:

```coq
(* iris/EchoOut.v:343 *)
Definition ps_len_ok (so : ostage) : Prop :=
  pro_from (S (ps_round so)) (o_ps so) = []
  /\ (ps_opens so ->
      forall ps' : list nat, ps' `prefix_of` o_ps so ->
        pro_of (pro_from (ps_round so) ps')
          <> pro_of (pro_from (ps_round so) (o_ps so)) ->
        (length (pending_n ps' (o_cs so) (length (o_E so)))
         < length (o_w so))%nat).
```

PLAIN READING: (A) nothing is filed for a prologue round that has not yet
opened; (B) at a round-opening block, any shorter resolution of the
prologue was written past strictly -- so "the round is settled" is readable
off how far the writer got.  This is CLAIM-INTERNAL: `eout`'s statement
(iris/EchoOut.v:1651) gains `ps_len_ok so` in its pure conjunct, and the
four landed link statements and the discipline did not move.

### 2.2 `init_boot_pay`'s `Rt` -- what /init's banner leaves behind

/init prints `"init: starting sh\n"` at the head of every round of its
restart loop.  Round 0 is the round it enters holding the era's own
credential, so its eighteen bytes are now paid by the application's links
and not by the flagged write deposit.  The boot bundle changed twice in
this range -- M1(a,b) made the era's turn concrete, M1(e) made it a
per-byte payment, M4a(2a) added `Rt` -- and the NET is:

```coq
(* OLD, 249b751c2, iris/UInitKernel.v *)
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Tn : iProp Σ) : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat ∗ Tn)%I.

(* NEW, iris/UInitKernel.v:585 *)
  Definition init_boot_pay (T Cns : iProp Σ) (cn : cons_names)
      (stc : fdstate) (Rt : iProp Σ) : iProp Σ :=
    (init_cons_dance_all T Cns stc ∗ ucons_reader cn 0%nat
     ∗ ∀ N' : uk_names Σ, UkInitMain.kinit_banner0 N' stc Rt)%I.
```

`Tn` was an opaque `iProp` nobody read.  The third conjunct is now a real
obligation, at the concrete descriptor ledger `ufd_l3 stc` (/init's table
after its open and two dups, where fd 1 IS the console):

```coq
(* iris/UkInitMain.v:1016 *)
  Definition kinit_banner0 (stc : fdstate) (Rt : iProp Σ) : iProp Σ :=
    UkInit.kinit_banner_pay N stc 18%nat (init_lit LIT_START) Rt.

(* iris/UkInit.v:1354 *)
  Definition kinit_banner_pay (stc : fdstate) (len : nat) (f : nat -> bv 8)
      (Rt : iProp Σ) : iProp Σ :=
    (UserFd.ustd γfd (ufd_l3 stc) -∗
     ∃ Ch : nat -> iProp Σ,
       □ (∀ j : nat, ⌜(j < len)%nat⌝ -∗
            kinit_w1 (mword_of_int 1 : mword 64) (f j) (Ch j) (Ch (S j)))
       ∗ Ch 0%nat ∗ (Ch len -∗ UserFd.ustd γfd (ufd_l3 stc) ∗ Rt))%I.
```

"Give me /init's descriptor table and I give you a per-byte chain for the
eighteen bytes, plus the table back AND a residue `Rt`."  `Rt` is a
parameter because what the last byte leaves behind is the application's to
say and this tier cannot name it.  `wp_kinit_start` (iris/UkInitMain.v:2538)
takes `(stc : fdstate) (Rt : iProp Σ)` and the premise
`kinit_banner0 stc Rt -∗` where it took the opaque `Tn -∗`.  The application
side is:

```coq
(* iris/UInitBanner.v:316 *)
  Lemma kinit_banner0_holds :
    echo_links T γ -∗
    eturn γ (S gen_id) -∗
    ∀ N : uk_names Σ, UkInitMain.kinit_banner0 N stc_cons kinit_turn0.
```

with `kinit_turn0 := ∃ v, era_pin γ (S gen_id) v ∗ bnr v 18%nat`
(iris/UInitBanner.v:313).  Note what M1(f) bought: the lemma LOST the
`(⊢ udepw_law 16)` premise and its six-row case split on fd 1, because
DUP-ROW made a failing `dup` refutable and so pinned the table.
`echo_Hinit_boot` and `Hsh_owed` are untouched -- `Rt` is instantiated
inside the proof.

### 2.3 `sh_prompt_pay` -- the pair /init and sh agree on

`getcmd`'s `write(2, "$ ", 2)` prints the `'$'` that RESOLVES round 0 of
the prologue, so it too must be paid by the era's link.  /init's walk names
no era and sh's walk names no syscall number, so what crosses their fork is
a pair:

```coq
(* iris/UShKernel.v:390 *)
  Definition sh_prompt_pay : iProp Σ :=
    (∃ C : iProp Σ,
       C ∗ □ (∀ (N : uk_names Σ) (l : list fdstate),
                ⌜ UkSh.ush_fd2p l ⌝ -∗
                shk_rodata (ukn_t N) -∗
                UkSh.ksh_w N (mword_of_int 2)
                  (mword_of_int UkSh.sh_prompt_pv) 2%nat
                  (ustd (ukn_fd N) l ∗ C) (ustd (ukn_fd N) l)))%I.

(* iris/UShKernel.v:406 *)
  Definition sh_prompt_at (l : list fdstate) : iProp Σ :=
    ((⌜ UkSh.ush_fd2p l ⌝ ∗ sh_prompt_pay) ∨ True)%I.
```

`C` is the opaque credential; the `□` is the conversion into `ksh_w`, sh's
per-call write obligation at a descriptor the pair names (fd 2).
`ush_fd2p l` is a PURE row -- "slot 2 of this ledger is the console" --
preserved across sh's own console preamble.  `sh_prompt_at` is AFFINE (the
`∨ True`): a shell entered without a credential prints through the flagged
deposit, exactly as every shell did before.  It is a new premise of
`UShKernel.sh_uexec_slot` (:548) and `sh_slot_of_kexec` (:698).  The
application instantiates `Rt` at it -- `UInitBanner.kinit_banner0_pay_holds`
(:380) is `kinit_banner0_holds` composed with
`UShOut.sh_prompt_pay_of_ushpr` -- so `init_boot_pay`, `echo_Hinit_boot`
and `Hsh_owed` do not move for it.  Route, end to end: banner's 18th byte
-> `Rt` -> /init's fork lends `(Rt ∨ True)` beside the lease -> the child's
`exec` carries it in `PinnedExec`'s `Pay` -> `sh_prompt_at` -> sh's loop ->
`getcmd` spends it at +0x1c.

## 3. THE KERNEL ROWS SINCE THE PREDECESSOR

A ROW is a clause of a kernel spec's postcondition that a program proof
reads.  Six landed here.

### 3.1 The read's -1 reason, and the resume's pure row (TRAP-ROWS T2)

```coq
(* OLD, 249b751c2, iris/SpecFileread.v -- the -1 arm carried no reason *)
  Definition console_receipt (P : uptd) (Rd : nat -> nat -> iProp Σ) ... :=
    ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
      ∃ cur d' : nat, Rd cur d')
     ∨ ...

(* NEW, iris/SpecFileread.v:1031 *)
  Definition console_receipt (gn : gname) (P : uptd) (Rd : nat -> nat -> iProp Σ)
      (Rin : list (list mobs * bv 8) -> iProp Σ)
      (n : Z) (r : mword 64)
      (M' : gmap Z (bv 8)) (addr : mword 64) : iProp Σ :=
    ((⌜r = (mword_of_int (-1) : mword 64)⌝ ∗
      (⌜(n < 0)%Z⌝ ∨ ChildTok.kill_shot gn) ∗
      ∃ cur d' : nat, Rd cur d')
     ∨ ...
```

THE C FACT: at an open readable console descriptor exactly two exits return
-1 -- `fileread`'s own `n < 0` sign guard at +0x1a, before the type
dispatch, and `consoleread`'s `killed(p)` test inside its wait loop.  A
null `devsw` slot and an out-of-range major do not reach it.  Both
disjuncts are PERSISTENT (a `kill_shot` is a fired one-shot ghost token,
freely duplicable), so a caller reads the reason off without spending the
arm -- `console_receipt_m1_why` (:1163).

That is cashed by a PURE row on the resume path.  `usertrap`'s second
`if(killed(p)) exit(-1)` after `syscall()` means a process that comes BACK
to user mode was not killed, so the shot is impossible and only the sign
guard is left:

```coq
(* NEW, iris/SpecUsertrap.v:699 *)
Definition ut_live_out (sc_v : mword 64) (tf : list (mword 64))
    (sts : list fdstate) (r : mword 64) (cs' : gset gname) : Prop :=
  (sc_v = uecall_scause -> usys_num tf = USYS_read ->
   (0 <= sys_rw_count (tf !!! tf_arg_idx 2))%Z ->
   forall rb : bool,
     fd_st_of_key (tf !!! tf_arg_idx 0) sts
       = FdOpen true rb (FdDevice CONSOLE) ->
     r <> (mword_of_int (-1) : mword 64))
  /\
  (sc_v = uecall_scause -> usys_num tf = USYS_wait ->
   uint (tf !!! tf_arg_idx 0) = 0%Z ->
   r = (mword_of_int (-1) : mword 64) ->
   cs' = (∅ : gset gname)).
```

Its U-tier spelling, threaded once through `uexec_ret_cont_gen`
(iris/UexecRet.v:1315, one new pure premise
`⌜uexec_live_ok n (uvis_tf W) (uvis_fd W) r cs'⌝`), reads the descriptor by
INDEX because a program holds its table as a list:

```coq
(* NEW, iris/UexecRet.v:1266 *)
  Definition uexec_live_ok (n : Z) (tf : list (mword 64))
      (sts : list fdstate) (r : mword 64) (cs' : gset gname) : Prop :=
    (n = USYS_read ->
     (0 <= bv_signed (trunc32 (tf_w tf (tf_arg_idx 2))))%Z ->
     forall rb : bool,
       (0 <= usys_argfd tf < Z.of_nat NOFILE)%Z ->
       sts !! Z.to_nat (usys_argfd tf) = Some (FdOpen true rb (FdDevice 1)) ->
       r <> (mword_of_int (-1) : mword 64))
    /\
    (n = USYS_wait ->
     uint (tf_w tf (tf_arg_idx 0)) = 0%Z ->
     r = (mword_of_int (-1) : mword 64) ->
     cs' = (∅ : gset gname)).
```

This is what refutes the -1 arm of sh's read leaf (section 1, conjunct 3).

### 3.2 The additive pair at a killing cause (TRAP-ROWS T3)

At a trap whose cause kills the process, the process used to hand over
either the death payment or nothing.  It now offers BOTH SIDES OF AN
ADDITIVE CONJUNCTION (`∧`: the kernel may take either one, but not both --
which is exactly "one resource, two possible uses"):

```coq
(* OLD, 249b751c2, iris/UexecRet.v:1372 *)
  Definition uexec_kill_arm_F (X : uvis -d> iPropO Σ) (sc : mword 64)
      (W : uvis) (f : sfam) : iProp Σ := (X W)%I.

(* NEW, iris/UexecRet.v:1562 *)
  Definition uexec_kill_arm_F (X : uvis -d> iPropO Σ) (sc : mword 64)
      (W : uvis) (f : sfam) : iProp Σ :=
    (ukill_cred_at (uvis_gen W) sc ∧ X W)%I.
```

and at the kernel's own spelling, where the row also pins whose
incarnation the charge lands on, plus a new row for the slot the kernel did
NOT take:

```coq
(* OLD, 249b751c2, iris/SpecUsertrap.v:882 *)
Definition ut_kill_in `{!riscvGS Σ, !xv6G Σ} (gn : gname) (sc_v : mword 64)
    : iProp Σ :=
  ukill_cred_at gn sc_v.

(* NEW, iris/SpecUsertrap.v:1089 and :1105 *)
Definition ut_kill_in `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
    {SG : uexecSG Σ}
    (f : sfam) (sc_v : mword 64) (W : uvis) (gn : gname) : iProp Σ :=
  (⌜uvis_gen W = gn⌝ ∗
   (if decide (sc_v = uecall_scause) then emp
    else uexec_kill_arm sc_v W f))%I.

Definition ut_kill_out `{!riscvGS Σ, !xv6G Σ, !fileG Σ} `{GEN : GenId} `{XI : CurCtx}
    {SG : uexecSG Σ}
    (sc_v : mword 64) (W : uvis) : iProp Σ :=
  (if decide (sc_v = uecall_scause) then emp else uslot W)%I.
```

WHY: a process that faults ON PURPOSE at a LINEAR exit payload -- sh's
forked child storing through the NULL `malloc` returned it -- must pay for
its own death with a resource, and the leaf that dies must still be able to
hand back the resume slot on the path where it does not.  Step 5's denied
store leaf, which the predecessor recorded at a Coq-level free payload,
therefore takes the payload as a RESOURCE:

```coq
(* OLD, 249b751c2, iris/UkStore.v *)
    (* the payload at the kill status, free at a forked child's record *)
    (⊢ (Qp (-1) : iProp Σ)) ->
    uvb C pt Rfd Rut sz π fdv cw gn cs pidv false M m pc -∗
    ChildTok.my_pay gn Qp -∗
    WP (Loop : expr riscv_lang).

(* NEW, iris/UkStore.v:1742 (wp_uk_store_denied) *)
    uvb C pt Rfd Rut sz π fdv cw gn cs pidv false M m pc -∗
    ChildTok.my_pay gn Qp -∗
    Qp (-1) -∗
    WP (Loop : expr riscv_lang).
```

The engine's three statements above it (`uk_store_fault_post_fetch`,
`uk_store_obl_base`, `uk_store_obl_rvc`) gain a parameter `Kcx` and carry
`Kcx ∧ uslot …` whole to the leaf, with the deposit premise weakened from
`⊢ (my_pay gn Qp -∗ …)` to `⊢ (Kcx ∗ my_pay gn Qp -∗ …)`;
`UkRunMem.wp_uk_sb_denied` likewise.

### 3.3 The kill flag's monotonicity (`kill_row`)

```coq
(* OLD, 249b751c2, iris/SchedCtx.v *)
  Definition kill_row (gn : gname) (kl : mword 32) : iProp Σ :=
    ((⌜kl = (mword_of_int 0 : mword 32)⌝ ∗ ChildTok.kill_pend gn)
     ∨ (ChildTok.kill_shot gn ∗
        (ChildTok.kill_owed gn ∨ ChildTok.taken_at gn)))%I.

(* NEW, iris/SchedCtx.v:262 *)
  Definition kill_row (gn : gname) (kl : mword 32) : iProp Σ :=
    ((⌜kl = (mword_of_int 0 : mword 32)⌝ ∗ ChildTok.kill_pend gn)
     ∨ (⌜kl <> (mword_of_int 0 : mword 32)⌝ ∗ ChildTok.kill_shot gn ∗
        (ChildTok.kill_owed gn ∨ ChildTok.taken_at gn)))%I.
```

THE C FACT: the one-shot fires exactly when `kkill` or `setkilled` stores 1,
and the only store of 0 is `freeproc`'s, on a dead slot where the row is
gone -- so within a live incarnation `p->killed` is MONOTONE.  Saying so
here buys `kill_paid_shot_nz`: holding the shot proves the flag reads
nonzero, which is what lets `usertrap`'s second killed check refute its own
resume branch and so prove section 3.1's row.

### 3.4 Wait's -1 reason, and the pid range (TRAP-ROWS T4, T4(c))

```coq
(* OLD, 249b751c2, iris/UserChildren.v:171 *)
  Definition wait_ans (rv : mword 32) (xs : Z) (cs cs' : gset gname) : iProp Σ :=
    (⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝
     ∨ ∃ γ' : gname,
         ⌜cs' = cs ∖ {[γ']}⌝ ∗ exit_tok γ' rv xs ∗ gen_uniq cs rv γ')%I.

(* NEW, iris/UserChildren.v:218 and :234 *)
  Definition wait_why (cs : gset gname) (gn : gname) (nullst : bool) : iProp Σ :=
    (⌜nullst = false⌝ ∨ ⌜cs = (∅ : gset gname)⌝ ∨ kill_shot gn)%I.

  Definition wait_ans (rv : mword 32) (xs : Z) (cs cs' : gset gname)
      (gn : gname) (nullst : bool) : iProp Σ :=
    (⌜rv = (mword_of_int (-1) : mword 32) /\ cs' = cs⌝ ∗ wait_why cs gn nullst
     ∨ ∃ γ' : gname,
         ⌜cs' = cs ∖ {[γ']} /\ (1 <= bv_unsigned rv <= PIDMAX)%Z⌝ ∗
         exit_tok γ' rv xs ∗ gen_uniq cs rv γ')%I.
```

THE C FACT: `wait()` returns -1 on three exits -- no children, the caller
was killed, or `copyout` of the status word failed.  The third is guarded
by `addr != 0` in the C, and every `wait` leaf in the tree forces a NULL
status pointer, so `nullst` is a GUARD and not a claim: at a null pointer
only the first two survive.  Separately, `allocpid` hands out every pid in
`[1, PIDMAX]`, so the reaping arm's `rv` sign-extends to a small positive
word and can never be the -1 a failing wait returns -- which is what makes
the two arms disjoint at the return value and proves `ut_live_out`'s wait
clause.  That range moved onto the process block's registration:

```coq
(* OLD, 249b751c2, iris/SlotGen.v *)
  Definition gen_halves_at pa pid g : iProp Σ :=
    (⌜bv_unsigned pid <> 0⌝ ∗
     slot_gen pa (DfracOwn (1/4)) g ∗ pid_reg pid (DfracOwn qeighth) g)%I.

(* NEW, iris/SlotGen.v:403 *)
  Definition gen_halves_at pa pid g : iProp Σ :=
    (⌜(1 <= bv_unsigned pid <= PIDMAX)%Z⌝ ∗
     slot_gen pa (DfracOwn (1/4)) g ∗ pid_reg pid (DfracOwn qeighth) g)%I.
```

The U tier gets it as a pure row on a new leaf:

```coq
(* NEW, iris/UkRunSys.v:2131, wp_uk_ecall_wait_null_live's continuation *)
    (∀ (h' : CpuId) (r : mword 64) (Sc' : gset gname),
       ⌜r = (mword_of_int (-1) : mword 64) -> Sc' = (∅ : gset gname)⌝ -∗
       uwait_ans r Sc Sc' -∗ ...
```

`wp_uk_ecall_wait_null` keeps its statement verbatim, so `wp_kinit_wait`
and `wp_kshr_wait` are untouched.

### 3.5 The write leaves' ownership rows (IO-LEAF M1(c,d), TXT-ROW)

The predecessor recorded T1's `SpecFilewrite.write_cons_short` /
`write_cons_arms` -- "a short console write means some byte at or after the
cursor sat on a page the kernel could not read through the writer's own
page table".  Those are UNCHANGED (`iris/SpecFilewrite.v` has no diff).
What appeared is the U-tier leaf that lets a program REFUTE that arm, by
handing the leaf its own source bytes and getting back the positive twin:

```coq
(* NEW, iris/UkRunSys.v:3599, wp_uk_ecall_write_chain_buf -- the two new
   post rows; the leaf also takes and returns
   [UserHeap.ubytesq (ukn_d N) dq (uint (m !!! Regidx (mword_of_int 11))) nb f] *)
       ⌜uvis_lazy W = false⌝ -∗
       ⌜ forall (P : uptd) (j : nat),
           ProcPtOwn.proc_pt_wf P ->
           perm_of (ud_um P) (uvis_sz W) = uvis_perm W ->
           lazy_free (ud_um P) (uvis_sz W) ->
           (j < nb)%nat ->
           UserPtTree.uva_rmapped P
             (uint (add_vec_int (m !!! Regidx (mword_of_int 11))
                      (Z.of_nat j))) ⌝ -∗
```

`wp_uk_ecall_write_chain` keeps its statement verbatim as the `nb = 0`
instance, so every existing wrapper is untouched.  TXT-ROW added the TEXT
half beside it (iris/UkRunSys.v:3815): `wp_uk_ecall_write_chain_txt` takes
`[∗ list] j ∈ seq 0 nb, UserHeap.utext (ukn_t N) (… + j) (f j)` -- a
persistent run, so it comes back free -- and gives the same
`uva_rmapped` row, because a page the key's projection lists at all is a
real user leaf.  This is what a program writing a `.rodata` LITERAL needs;
echo's separator and newline and every literal sh prints are exactly that.
The consequence recorded in the notes: the engine now owes NOTHING for
echo's output.

### 3.6 Dup's reasons on both arms (DUP-ROW)

```coq
(* OLD, 249b751c2, iris/UsysMemOk.v -- the dup case of usys_fd_ok *)
     \/ (r = (mword_of_int (-1) : mword 64) /\ sts' = sts))

(* NEW, iris/UsysMemOk.v:389 (the dup case; the success arm gains one
   conjunct and the failure arm two reasons) *)
        fd_least_closed sts fd1 /\
        sts !! Z.to_nat (usys_argfd tf) <> Some FdClosed /\
        sts' = <[fd1 := sts !!! Z.to_nat (usys_argfd tf)]> sts)
     \/ (r = (mword_of_int (-1) : mword 64) /\ sts' = sts
         /\ ((forall (fd : nat) (st : fdstate),
                 usys_argfd tf = Z.of_nat fd -> sts !! fd = Some st ->
                 st = FdClosed)
              \/ fd_lowest_closed sts = None)))
```

THE C FACT: `sys_dup` is `argfd; fdalloc; filedup` and nothing else --
`argint` cannot fail, `argfd` rejects exactly an out-of-range index or a
null `p->ofile` slot, `fdalloc` fails exactly when its scan finds no closed
slot, `filedup` never fails.  Hence two reasons for -1, and a success
implies the source was open.  The failure reason is stated at a `nat` index
because `Z.to_nat` of a negative argument is 0 and `dup(-1)` must not be
licensed to say anything about slot 0.  The kernel spec needed nothing --
`SpecSysDup.sys_dup_post` always named both; `ProofSyscall` was discarding
them.  The U-tier leaf relays the second, the caller's own claim refuting
the first:

```coq
(* NEW, iris/UkRunSys.v:978, wp_uk_ecall_dup's failure arm *)
        ∨ (⌜r = (mword_of_int (-1) : mword 64)
            /\ fd_lowest_closed l = None⌝ ∗
           ustd (ukn_fd N) l ∗ ufd_own (ukn_fd N) l fd0 st)) -∗
```

(OLD: `⌜r = (mword_of_int (-1) : mword 64)⌝ ∗ …`.)  THE CONSUMER is /init:
after `open("console", O_RDWR)` returns fd 0 its ledger has slots 1 and 2
CLOSED, which refutes the arm by computation, so both dups provably land on
1 and 2.  That is what let `UInitFd`'s head become a NAMED ledger:

```coq
(* OLD, 249b751c2, iris/UInitFd.v:181 *)
  Definition ufd_head (T : iProp Σ) (st : fdstate) (γfd : gname) : iProp Σ :=
    ((∃ l : list fdstate, ufd_std_at γfd st l)
     ∨ ustd γfd ufd_l0
     ∨ (ustd_any γfd ∗ T))%I.

(* NEW, iris/UInitFd.v:221-234 *)
  Definition ufd_headL (T : iProp Σ) (γfd : gname) (l : list fdstate)
      : iProp Σ :=
    (ustd γfd l ∨ ustd γfd ufd_l0 ∨ (ustd_any γfd ∗ T))%I.

  Definition ufd_head1 (T : iProp Σ) (st : fdstate) (γfd : gname) : iProp Σ :=
    ufd_headL T γfd (ufd_l1 st).

  Definition ufd_head (T : iProp Σ) (st : fdstate) (γfd : gname) : iProp Σ :=
    ufd_headL T γfd (ufd_l3 st).
```

The three arms read: the console arm at the ONE ledger the prologue leaves
(`ufd_l3 st` = the console in slots 0, 1 and 2), the CLOSED arm (the mknod
or the open failed), and the TAINT arm.  The existential list is gone, and
with it the six-row case split `kinit_banner0_holds` used to carry.

## 4. IN FLIGHT -- PLANNED, NOT LANDED

Nothing below is on `main`.

**The reaping-arm row (TRAP-ROWS-3 T4(b), now lane TRAP-ROWS-4).**  A
`wait` that reaps gives `cs' = cs ∖ {[γ']}` but not `γ' ∈ cs` -- and sh,
which never reads the returned pid, cannot apply the uniqueness lemma
/init does.  In the C, `reparent` moves orphans to `initproc` ONLY, so a
non-init caller reaps only its own child.  Two obstacles were ruled on
2026-09-16.  THE DESIGN IS "THE U TIER SEES NUMBERS": `wchG` is not a class
the U tier declares (naming a ghost fact would put a `Context` in 54
files), and `urun` binds the pid existentially with no resource beside it.
So `wait_ans`'s reaping arm becomes `⌜γ' ∈ cs⌝ ∨ ⌜the caller's pid = ip⌝`
for a PURE parameter `ip`; `ut_caps` gains a pure `un_ipid : mword 32` tied
kernel-side by `init_pid_is (un_ipid N)`; the U-tier record `uk_names` gains
a ghost name `ukn_pid` (with `urun` carrying `upid_auth (ukn_pid N) pidv`
and the program holding `upid`) and a pure `ukn_ipid : mword 32`; and
`wp_uk_ecall_wait_null_live` hands the program `⌜γ' ∈ Sc⌝ ∨ ⌜p = ukn_ipid N⌝`
against its `upid`.  The fork side's child arm carries the pure
`⌜pidc <> ukn_ipid N'⌝`.  Milestone B waits on IO-LEAF M5b.

**The credential riding the console lease (IO-LEAF M5b).**  This closes
`Hsh_owed`'s third conjunct, and it IS a trusted change: today

```coq
(* iris/UserConsole.v:273, unchanged in this range *)
  Definition ucons_pay (cn : cons_names) (γ : gname) (T : iProp Σ)
    : Z -> iProp Σ :=
    fun _ => ((∃ n : nat, ucons_reader cn n ∗ upos_a γ n) ∨ T)%I.
```

and the ruling is `ucons_pay cn γ T Rd := fun _ => (∃ n, ucons_reader cn n ∗
upos_a γ n ∗ Rd n) ∨ T`, with `Rd 0` supplied from `eturn`'s `dl_cnt` half
at the boot mint.  WHY THE LEASE: the credential must be at sh's entry on
EVERY round of /init's restart loop, and the `(Rt ∨ True)` route only ever
has one at round 0 -- whereas the lease already round-trips through /init's
`wait`.  `ush_at` does not change.  The same slot is M6's route for the
write-side turn's return.

**The shell child's payload (IO-LEAF M3b core).**  M3b(1) and M3c landed
the pieces: sh's child is forked at a payload SH CHOOSES (`ukn_triv` gone
from the child's path, its three jobs now premises), and the child's death
pays with a resource rather than the Coq-level `⊢ ukn_pay N (-1)`.  The
core is blocked on M5: the payload sh wants to lend is the era's bundle at
the LINE BOUNDARY, and sh only reaches that stage once the seventeen echoed
bytes have advanced the read side through its own lease.

**The diagnostics (IO-LEAF M4b, M6).**  /init's "init: exec sh failed" and
"init: fork failed", sh's "fork", and rounds k > 0 of the banner still
print through the flagged write deposit `udepw_law 16`.  Taking them off it
is what finally retires `Hsh_owed`'s FIRST conjunct.  FORK-REFUND's `Rc`
(landed before this range, still no consumer) is the route: a parent that
could not get its lend back could not print the failure.

## 5. AUDIT

`make audit-only` (`SystemAssumptions.v`) reports THIRTEEN assumptions, and
the number and the list are UNCHANGED by every lane in this range -- each
landing note in `app-echo.md` records "audit the thirteen".  They are, as
in the predecessor:

```
PrimInt63.sub : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimString.string : Set
xv6iris_extras.resv_matches : forall n : BinNums.Z, Values.mword n -> bool
xv6iris_extras.resv_is_valid : bool
PrimInt63.lsr : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lsl : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.lor : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.land : PrimInt63.int -> PrimInt63.int -> PrimInt63.int
PrimInt63.int : Set
PrimString.get : PrimString.string -> PrimInt63.int -> PrimString.char63
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
PrimInt63.eqb : PrimInt63.int -> PrimInt63.int -> bool
PrimString.cat : PrimString.string -> PrimString.string -> PrimString.string
```

Nine are Rocq's own primitive-integer and primitive-string operations, one
is functional extensionality, and two (`resv_matches`, `resv_is_valid`) are
the Sail model's load-reserved/store-conditional reservation hooks.  Nothing
in this range added, removed or changed one.  Every landing note in the
range also records `no Admitted`.  (Not re-run for this document, per
instruction; taken from the landing notes.)
