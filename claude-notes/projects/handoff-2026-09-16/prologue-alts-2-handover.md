# PROLOGUE-ALTS-2 handover -- ONE commit green on `lane/prologue-alts-2`

Checkout /shared/xv6iris-2-sup, branch `lane/prologue-alts-2`, HEAD `ca914ff85`,
rebased onto origin/main `ef245363f` (IO-LEAF M1(a,b), which landed
`iris/EchoLinks.v`).  One commit, three files: `iris/EchoDisc.v`,
`iris/EchoOutPure.v`, `iris/EchoOut.v` (+832/-5).  NOTHING is owed.

## GATE (whole tree)
build `pb2` (5 files after the rebase; `pb1` = 29 before it), zero Error,
EXIT=0; `make -f CoqMakefile -n` on the VM prints 0 `ROCQ compile`;
`make audit-only | md5sum` = 57f7327206c4b276d05035342fea8ecf (the thirteen);
`lemma_diff --ref origin/main` CLEAN; no `Admitted`; `--check-dumps` clean.

## THE THREE DELIVERABLES
1. `ps_len_ok` -- a FOURTH pure conjunct of `eout`'s bracket, beside
   `cs_len_ok` (not inside `eout_pure`: `cs_len_ok`, its twin, is not either,
   and `eout_pure`'s eleven-way destructuring is spent in six places).  TWO
   conjuncts, both needed:
     (A) `pro_from (S (ps_round so)) (o_ps so) = []`
     (B) at a ROUND-OPENING block (`ps_opens`), any prefix of the resolution
         with a SHORTER prologue than the stage's own was passed STRICTLY.
   THE HANDOVER'S PROPOSED IFF IS FALSE IN BOTH DIRECTIONS: at the choice byte
   `o_w` IS the whole `pending_n` and the round is open; one byte after it the
   round is settled and `o_w` is a proper prefix.  (A) is what (B) needs at
   the two moves that OPEN a round (`_blk` with `a = 3`, `_echo` at a line
   boundary).  Moves: `ps_len_ok_write` / `_blk` / `_echo` / `_pro`, plus
   `ps_len_ok_0` and `ps_len_ok_empty_above`.  `eout_step_write`/`_blk`/
   `eout_step_echo`, all four links and `read_ret` keep their statements
   BYTE FOR BYTE.
2. `eout_step_write_pro` + `echo_write_link_pro`.  Reconciliation:
   (B) -> the two resolutions have the same prologue -> `pro_of_prefix_free`
   -> the claim's round is open -> `pro_of_open_app_inj` -> the lists are
   EQUAL, which is what makes `ps_lb v (ps0 ++ [a])` payable.
   `pending_n_round_det` (the handover's) is used inside the `length E = n0`
   refutation, not in the reconciliation.
3. `proc_upto_round_banner` (abstract `pre`) and `proc_upto_round_banner_open`
   (`pre` read off the round-opening premise).  Round and `j` are variables.
   Anti-vacuity: `pro_choice_round1_live`, round 1, `vm_compute`.

## WHAT IS STILL OPEN, for IO-LEAF
`EchoLinks.v`'s own header says `echo_write_link_pro` "becomes a fifth
conjunct when it lands, and the four projections below are what every
consumer goes through, so adding one costs the consumers nothing".  IT HAS
LANDED; I did NOT touch `EchoLinks.v` (IO-LEAF's file, in flight elsewhere).
The fifth conjunct is ~20 lines: an `echo_link_pro` mirroring `echo_link_blk`
with the eight premises of `echo_write_link_pro`, a persistence instance, a
projection `echo_links_pro`, and one bullet in `echo_links_holds`.

## Process notes (unchanged from PROLOGUE-ALTS, plus)
- Edit loop `scratchpad/warm.sh <File.v>`; after editing EchoDisc/EchoOutPure
  run `make -f CoqMakefile <F>.vo` on the VM before warming the next file.
- Full build `./gcp-rocq/vmbuild.sh xv6iris-2-sup pb3` (pb1, pb2 used).
- `make audit-only` must run ON THE VM (`run-on-gcp -q --no-sync bash -c
  "cd /mnt/rocq/trees/_shared_xv6iris-2-sup && make audit-only ..."`); the
  local tree has no `.vo` and the target fails with a logical-path error.
- New gotchas: `etrans; [apply Nat.Div0.div_le_mono; lia | exact H]` leaves a
  metavariable and `lia` answers "Cannot find witness" -- name the middle term
  in an `assert` instead; `lia` cannot evaluate `17 `div` 17`, so
  `vm_compute (17 `div` 17)%nat` first; `pro_idx_S3`/`_Sne` need the SAME list
  on both sides, so `pro_idx_app_le` has to be rewritten in before them.
