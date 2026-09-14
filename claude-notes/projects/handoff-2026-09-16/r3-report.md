# SH-LINE R3 -- STOPPED before any edit: the brief's plan cannot close the conjunct

Checkout `/shared/xv6iris-2-disc`, branch `lane/sh-line-r3` at `a43341d28`
(= main's "IO-LEAF M6a(3)a"). NO FILE WAS CHANGED, NO BUILD WAS STARTED, NO
COMMIT WAS MADE. `git status --porcelain` is empty; the green committed state
is `a43341d28` itself.

Terms used below. A WEAKEST-PRECONDITION (WP) proof says "from these
resources the program runs safely". A RECORD `N : uk_names Σ` is the bundle of
ghost names a running user process is stated over; its PAYLOAD `ukn_pay N :
Z -> iProp` is what the process must hand its parent at exit code `x`. The
TAINT `T` is the application's persistent "the console discipline was
broken" fact; once it holds, nothing more is claimed. The GENERIC SLOT
`UkSh.ush_gen_slot N T := □ (∀ W, T -∗ my_pay (uvis_gen W) (ukn_pay N) -∗
uslot W)` is the WP of a tainted process at ANY key `W`: it exists only when
the process can still pay its exit -- `UexecExecMint.uslot_mint_all` builds it
from a CONSTANT payload `fun _ => R` plus the PERSISTENT conversion `□
(riscv_kill_cred -∗ R)` (the kill credential is the taint). The EXEC SUPPLY is
the resource an `exec` syscall spends: `UkRun.uxsup` is the GENERIC one ("this
process may exec any path at the trivial payload") and
`UkShEcho.sh_exec_sup_echo` the PINNED one (only `/echo`, only from the root
directory). `UkSh.ush_rest_l N γp T R` is the shell's TAIL OBLIGATION: "from
the point after `gets` returned, with the line fact (the line in the buffer
is `echo hello world`, or the taint) and the loop's carried state `R`, the
rest of the command-loop body runs safely and re-enters the loop head".

## 1. What the brief asked and why it is not achievable as stated

`Hsh_owed`'s second conjunct `(⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)` is
`∀ γp N T, ⌜Persistent T⌝ -∗ ush_rest_l N γp T (sh_Rsh …)`. The brief's route
was `UkShFork.ushf_rest_of_body` (the only lemma in the tree proving
`ush_rest_l`). Its premises (iris/UkShFork.v:959-978) are

```
UkShLoop.ush_line_lexable -> 8344 <= sz -> pgroundup sz = sz -> usz_ok (sz + 65536) ->
UkSh.sh_deps -∗ uxsup -∗ UkSh.ush_gen_slot N T -∗ UkSh.ush_rest_l N γp T (UkShLoop.ushl_R N sz)
```

plus its section's `Context {Hpay : !ukn_const N}` and `Hypothesis Hpsok_free`.
Of these, TWO cannot be supplied at the top, and the second is not a
collision-rule problem but a fact about the tree:

**(A) `uxsup` -- the generic exec supply -- does not exist at the top and
cannot.** `grep -rn uxsup iris/*.v` finds only CONSUMERS (`UkInit.
init_exec_sup_of_uxsup`, `UkRun.udepw_of_uxsup`, `uxsup_at_triv`, the three
UkShFork walks). `UexecSG.free_num` (iris/UexecSG.v:712) is `n <> USYS_exec /\
…`, so exec is a CLAIM number and the free deposit supplier `udep (PS :=
uprogSG_free)` cannot mint it. The only thing that could is the generic
supply `app_sup`, and at echo `app_sup ⊣⊢ echo_taint γ` (`Htsw`/`Hstw`,
iris/UInitBoot.v:704-711) -- i.e. it is available only UNDER THE TAINT, while
`ushf_rest_of_body` spends `uxsup` on the DISCIPLINED arm (`wp_kshm_body` →
`wp_kshf_fork` → runcmd's generic EXEC arm; iris/UkShFork.v:625, :259). The
application pins exec at `/echo` only (`sh_exec_sup_echo`, iris/UkShEcho.v:447;
`UShEcho.sh_exec_sup_of_echo_slot_closed`, iris/UShEcho.v:1322). So
`ushf_rest_of_body` is the GENERIC body and can never be the top's discharger.
What R3 needs instead is the lemma app-echo.md's lane list calls "the
composer with E4's dispatch" (app-echo.md:210, :5015, :5054): main's body from
0x97a with the child arm going to `UkShEcho.wp_kshm_child_echo_holds`
(iris/UkShEcho.v:779) and the parent to `wait` and the loop head, at
`sh_exec_sup_echo`. E4's landed note says exactly this is NOT REACHED --
"nothing CALLS `wp_kshm_child_echo` -- the dispatch belongs in
`wp_kshf_fork`'s child arm, which cannot see UkShEcho: SH-LINE 2b builds it in
a file above UkShEcho.v" (app-echo.md:5105-5109). That lemma does not exist,
and writing it means re-walking or re-parametrising `wp_kshm_body` /
`wp_kshf_fork` (iris/UkShFork.v:602, :237), which are in the frozen files.

**(B) `UkSh.ush_gen_slot N T` is per-RECORD and the top cannot build it for
the arbitrary `N` that `sh_pay_rest` (and `sh_pay`, and
`UShKernel.sh_uexec_slot`'s premise) quantify.** This is the endgame audit's
blocker, but its option (a) ("add `ush_gen_slot N T -∗` inside `sh_pay_rest`'s
∀; `sh_pay_of_parts` supplies it from `echo_Hinit_boot`") does not work
either: the top holds `init_sh_slot_core`'s third conjunct `□ (∀ R W, T -∗
my_pay (uvis_gen W) (fun _ => R) -∗ □ (riscv_kill_cred -∗ R) -∗ uslot W)`
(iris/UInitSh.v:775-782), which yields `ush_gen_slot N T` only for a record
whose constant payload `R` the taint can pay -- and that conversion exists
only at sh's real payload (`ucons_pay_taint`, used at iris/UInitSh.v:1097-1101
and iris/UShKernel.v:630-631 at `Hpayeq : ukn_pay N = Q`), not at an
arbitrary `N`. Inside the obligation's body the shell holds `ukn_pay N (-1)`
LINEARLY (`ush_pstate` → `ush_posb` → `ush_at n := upos γp n ∗ ukn_pay N (-1)`,
iris/UkSh.v:1565-1590), but the mint wants the persistent conversion, not the
linear payload ("a single LINEAR R cannot serve both legs of a return",
iris/UexecExecMint.v:236-241). So every shape of `sh_pay_rest` that is provable
needs `ush_gen_slot N T` handed in PER RECORD, and the only place that has it
is `UShKernel.sh_uexec_slot` (iris/UShKernel.v:626-631: `iPoseProof ("Hrest" $!
N)` right beside `Hgen'`). Threading it costs either (i) UkSh.v: put
`ush_gen_slot` inside `ush_rest_l`'s `□` beside `⌜ukn_const N⌝`/`shk_code`/
`ush_jtab` (the SH-LINE 2b(b) precedent, which is exactly why those three are
there: iris/UkShFork.v:985-992's comment) and have `wp_ksh_loop` pay it (it
holds `ush_gen_slot` at iris/UkSh.v:6192/7541/7828/8109); or (ii) UShKernel.v
+ UInitSh.v: `sh_pay`'s second conjunct and `sh_uexec_slot`/`sh_slot_of_kexec`'s
premise become `∀ N, ush_gen_slot N T -∗ ush_rest_l …` (iris/UShKernel.v:564,
:626, :732 and the UInitSh call site :1155). (i) is the clean one and leaves
`sh_pay_rest`, `sh_pay`, `sh_pay_of_parts`, UShKernel and UInitSh untouched --
NO trusted-statement change at all beyond deleting `Hsh_owed`'s conjunct.
Both are in files the collision rules freeze.

**(C) A third seam the brief does not name: the working directory.** E4's
pinned dispatch is stated at `UserCwd.ucwd (ukn_cwd N) FsImg.ROOTINO`
(iris/UkShEcho.v:453, :516, :795) because `/echo` is resolved from the root,
while `ush_rest_l`'s body receives `ush_pstate l := ush_std l ∗ ucwd_any γcwd ∗
…` (iris/UkSh.v:6283) -- the cwd's VALUE is hidden under an existential
(`ucwd` is a half `ghost_var`, iris/UserCwd.v:44-48; `ucwd_any` cannot be
turned back into `ucwd ROOTINO`). E4's note lists it as open: "`ucwd (ukn_cwd
N) ROOTINO` at sh's entry (SH-OPEN's row exists; `sh_uexec_slot` still starts
at `ucwd_any` -- E2/2b produce it)" (app-echo.md:5107-5109). So a pinned
composer at `ush_rest_l`'s CURRENT interface is unprovable (an exec of "echo"
from an unknown cwd is not what the pin pays), and stating it as a Coq-level
premise of `sh_rest_holds` would be the vacuity trap durable-notes forbids.
Fix: `ush_pstate`'s cwd conjunct pins `ROOTINO` (sh's `cd` arm is only walked
on the disciplined line, which is refuted there by `f k = 'e'`; the taint arm
leaves for the generic slot before the cd check, iris/UkShFork.v:995-1006),
threaded through `UkShFork.ushf_pstate_at`, `UkShCd`, `UkShEcho.ush_pstate_at`
and `UShKernel.sh_uexec_slot`'s entry (SH-OPEN's `uvis_cwd W = ROOTINO` row).
UkSh.v / UkShFork.v / UShKernel.v again.

Conclusion: with UkSh*.v, UShKernel.v, UShLine.v frozen, there is no
restatement of `sh_pay_rest` in UInitSh.v that is both provable and keeps
`sh_pay`'s consumers compiling, and `Hsh_owed`'s second conjunct cannot be
deleted. The two textual changes I was allowed (`sh_pay_rest`, `sh_pay_of_parts`)
would either be unprovable (any ∀-over-`N` form without the per-record slot)
or break `sh_pay_of_parts` (any form with it). I therefore made none.

## 2. What the coordinator has to rule before R3 can run

In dependency order, all in the frozen files, all small except (3):

1. UkSh.v: `ush_gen_slot` inside `ush_rest_l`'s `□` (after `ush_jtab γt -∗`),
   paid by `wp_ksh_loop`; `UkShFork.ushf_rest_of_body` takes it from inside
   instead of as a wand. (Seam B.) ~10 lines.
2. UkSh.v + UkShFork.v + UkShCd.v + UkShEcho.v + UShKernel.v: `ush_pstate`'s
   `ucwd_any` → `ucwd (ukn_cwd N) ROOTINO`; entry from SH-OPEN's row. (Seam C.)
3. A new file above UkShEcho.v and UkShFork.v (in `_CoqProject` after
   `UkShEcho.v`, before `UShEcho.v`): the pinned composer --
   `ush_rest_l N γp T (ushl_R N sz)` from `sh_deps`, `sh_exec_sup_echo`,
   `ush_line_toks_holds`, the three closed bounds, with the child arm at
   `wp_kshm_child_echo_holds`. Either `wp_kshm_body`/`wp_kshf_fork` gain an
   abstract child continuation (durable-notes: "A block lemma that names its
   syscall's postcondition cannot be reused by a parallel proof; one that
   takes an abstract continuation can") -- UkShFork.v -- or the ~0x97a-0x9c0
   stretch is re-walked in the new file (duplication; not recommended). (Seam A.)
4. THEN R3 proper, in `iris/UShRest.v` (before `UInitBoot.v`):
   `sh_rest_holds : (⊢ UkSh.sh_deps (PS := uprogSG_free)) -> ⊢ udep -∗
   sh_echo_slot T -∗ UInitSh.sh_pay_rest UInitSh.sh_Rsh` -- with
   `sh_pay_rest`'s TEXT UNCHANGED (the composer is at arbitrary persistent
   `T`, as UkShFork's section is) -- `sh_exec_sup_echo` from
   `UShEcho.sh_exec_sup_of_echo_slot_closed` (iris/UShEcho.v:1322, needs `udep`,
   `udepw_law 16` = `sh_deps`, and `sh_echo_slot T`, which is
   `init_sh_slot_core`'s pins law through `UInitSh.echo_pins_of_fs_pure`,
   iris/UInitSh.v:820); discharge at iris/UInitBoot.v:695-697 (replace `iApply
   Hsh_rest`), delete the premise at :562, delete the conjunct at
   iris/UInitBootAdequacy.v:139 and adapt the `destruct` at :243-244.
   The three closed bounds are at `kexec_sz sh_elf = 0x5000` (iris/UInitSh.v:618-622).

## 3. Verbatim texts (UNCHANGED)

`Hsh_owed` (iris/UInitBootAdequacy.v:123-139), OLD = NEW:
```
      (Hsh_owed : forall (HR : riscvGS Σ) (GEN : GenId)
         `{HBs : !bioslotG Σ, HFd : !fdslotG Σ, HIr : !irefslotG Σ,
           HPav : !pavG Σ, HWc : !wchG Σ, HF : !fileG Σ},
         (⊢ UkSh.sh_deps (PS := uprogSG_free))
         /\ (⊢ UInitSh.sh_pay_rest UInitSh.sh_Rsh)
```
`sh_pay_rest` (iris/UInitSh.v:509-514), OLD = NEW:
```
  Definition sh_pay_rest (Rsh : gname -> gname -> gname -> iProp Σ)
      : iProp Σ :=
    (∀ (γp : gname) (N : uk_names Σ) (T : iProp Σ),
       ⌜ Persistent T ⌝ -∗
       ush_rest_l (PS := uprogSG_free) N γp T
         (Rsh (ukn_t N) (ukn_d N) (ukn_s N)))%I.
```
`sh_rest_holds`: not stated (see §1; every statable form today either has an
unsatisfiable premise or does not type against `sh_pay`'s consumers).

## 4. Gate

Not run on the VM: no source changed, so a build would only re-confirm
`a43341d28`, which the main lane built; starting a 30-60 minute cone rebuild
in `_shared_xv6iris-2-disc` for that would compete with the other agent's
builds for nothing. Local lines: `python3 tools/lemma_diff.py --ref a43341d28`
→ "No *.v differs from a43341d28 under iris/"; `grep -n Admitted iris/*.v` →
18 hits, all inside comments (no `Admitted.`); `git status --porcelain` empty.
Audit md5 / `make -n` / `--check-dumps`: not run (nothing to check).

## 5. Files

None changed. Read in full: claude-notes/README.md, durable-notes.md,
projects/checkpoint-2026-09-16.md, handoff-2026-09-16/endgame-audit.md §3-4,
app-echo.md's SH-LINE / SH-STATE / M5(3) / E4 notes; iris/UShLine.v S4 block,
UInitSh.v (sh_pay_state/sh_pay_rest/sh_pay/sh_pay_of_parts/sh_Rsh/
init_sh_slot_core/init_exec_sup_of_sh_slot), UkSh.v (ush_gen_slot/ush_gen_run/
ush_rest_l/ush_rest_line/ush_loop_head/ush_pstate/ush_at/ush_posb/sh_deps/
ush_tag_law), UkShFork.v (wp_kshf_fork/wp_kshm_body/ushf_rest_of_body),
UkShLoop.v, UkShEcho.v, UkShMain.v, UkRun.v (ukn_const/urun_gen/uxsup/urun),
UexecExecMint.v, UexecSG.free_num, UShKernel.v (sh_uexec_slot/sh_slot_of_kexec),
UShEcho.v, UInitBoot.v (echo_Hinit_boot), UInitBootAdequacy.v, _CoqProject.
