# Worklist: app-both — ONE application by abstraction (Route B), then the union

Design of record: [`../design/app-both.md`](../design/app-both.md) (RULED
2026-09-22: Route B; the union replaces the file and pipe applications).
Opened 2026-09-22.  Nothing built yet.

## 0. The abstraction, read off the three instances

`LinkRec` (`iris/LinkRec.v`) is the era's console-output record: ~20 data
fields (the era's taint/pins/links, the per-line pure hooks `lk_ab`/
`lk_apr`/`lk_pan`/`lk_exf`/`lk_exfb`/`lk_noc`, twelve credential families
indexed by era, pins, input and position, the read receipt, the reader's
residue, the turn) and ~60 laws.  Its three instances (`EchoLinkInst`,
`FileLinkInst.file_link_inst_at s0`, `PipeLinkInst.pipe_link_inst_at`) are
built by hand, ~5k lines each, and every family in all three has ONE
shape:

    (∃ ps cs P, ⌜wr_X ps cs [s0] I P⌝ ∗ cursor v ps cs I P [∗ state witness]) ∨ [head arm] ∨ T

where `wr_X` is a PURE predicate on the app's session model (`sess`,
`sessf`, `sessp`: prologue ++ per-line blocks ++ partial line, the block
being the echoed line ++ the alternative's continuation), the cursor is the
era's ghost (`turn ∗ ps_lb ∗ cs_lb ∗ inp_lb`) and the state witness is the
file's boot-ledger entry (`f0w s0`; absent at echo/pipe, whose state is
`unit`).  The per-app differences are exactly:

1. **the LINE MODEL**: the line grammar, the alternatives per shape, their
   continuation bytes, and the STATE they thread (`FileDisc.fsm`; the
   identity at echo/pipe) — a pure record;
2. **the BLOCK ARM of one shape**: how the console family looks while that
   shape's continuation is being written — one writer (echo, file), or the
   pipe's TWO writers with the per-round ledger and terminal flag
   (`PipeBoth.pwc_blk2`, `pwc_line2`'s third arm) and the loop's widened
   credential (`UkShPipeFork.pterm_wc`);
3. **the CHILD LAW of one shape** (`UkShFork.ushf_child_law_at` at the
   shape's line predicate: echo's, `UkShRedirBody.sh_redir_child_law`,
   `UShRound.Hchild_cat`, `UShPipeLaw`'s);
4. **the per-cycle console claim's STAGE** (`FileOut.fostage` with `f0`;
   `PipeOut.postage` with the two-writer cursor), where the write/read
   steps are proved.

So a SHAPE MODULE is (2)+(3) plus its contribution to (1) and (4), and an
application is a line model assembled from modules, a claim stage
assembled from their extensions, and the generic families/laws/round/init
proved ONCE over that.

## 1. Milestones

- **M1 — the line model, pure.**  `LineModel.v`: a record `lmodel` (state
  type, line type with parse/print, alternatives with encoding/`ok`/
  panic/exec/silent classification, continuation at a state, the state
  step) and, over it, the session (`sess`), the `wr_*` predicates, the
  round pointer, and the DETERMINACY theorem (`sess_prefix_det`) proved
  once from the byte facts every instance already proves (`$`-free runs
  and prompts; the pipe's interleavings are a module's alternatives).
  `EchoDisc`/`FileDisc`/`PipeDisc`'s sessions as instances, with the
  landed definitions recovered BY CONVERSION (the `LinkRec` rule: consumers
  name families partially applied, so an instance must be definitionally
  the landed thing, not merely equivalent).  Anti-vacuity demos.
  Exit: the three `*_prefix_det` theorems are corollaries; nothing
  downstream moves.  **DONE 2026-09-23** (the file's and the pipe's are
  corollaries; echo's stays its own, see RESUME HERE; the demos are the
  models' own, unchanged).
- **M2 — the generic families.**  `GenLinksLine.v`: the twelve families,
  the read residue, the turn and the ~60 laws over an `lmodel`, a cursor
  and a state-witness family (`f0w` at the file, `emp` elsewhere), with
  a per-shape BLOCK ARM hook; the echo and file instances by conversion;
  the pipe's two-writer arm as the first non-trivial block module (this
  is where RULINGS §4.3f–p live; they are not re-argued, they are
  re-housed).  Exit: `EchoLinkInst`/`FileLinkInst`/`PipeLinkInst` are
  applications of the generic record; the three tiers' link files
  deleted.
- **M3 — the generic console claim.**  `GenOut.v`: the stage as the
  model's stage + a per-shape extension; the write/read/drain steps once;
  `EchoOut`/`FileOut`/`PipeOut` as instances.
- **M4 — the child laws as modules.**  Each child law re-stated at the
  generic families (its proof is line-shape-local, so this is renaming),
  and the generic round `UShGenRound` dispatching over the module list;
  `UShRound`/`UShPipeRound` deleted.
- **M5 — the union.**  The four-module application: `BothDisc` is the
  model at the four shapes (a listing), the claim `file_pred`, /init by the
  generic mould, `UBothBootAdequacy`, `BothAssumptions`; `file_phi` and
  `pipe_phi` as corollaries; `UFileBootAdequacy`/`UPipeBootAdequacy` and
  their audits retired.

## 2. Rules for the campaign

- Every milestone lands with the three existing theorems still closed and
  the four audits unmoved (system 13, tree 13, file 14, pipe 14); a
  milestone that cannot keep a landed statement recovers it by conversion
  or by a one-line corollary, never by a restatement.
- The whole-tree gate before every landing (durable-notes); no
  section-level instance binder goes into a shared file unmeasured.
- Cleanups owed to this campaign from before it: SLOT-WS (the fork
  interface at the parsed line — M4 is where it is paid), NAME-PATTERN.

## RESUME HERE (2026-09-22, late)

M1 STARTED.  Landed: `iris/LineModel.v` -- the record `lmodel` (state,
line, alternatives with their code and panic bit, continuation at a
state, step) and over it `lm_at`, `lm_pro_idx`, `lm_upto`, `lm_cont_at`,
`lm_blk`, `lm_seq`, `lm_sess`, `lm_after`, `lm_pro_ok`, `lm_pro_pin`
(+ `lm_pro_pin_of_ok`); `iris/LineModelInst.v` -- `file_lm`, `pipe_lm`,
`echo_lm` and the equations `sessf_lm`, `sessp_lm`, `sess_lm`.  FOUND:
the file's and the pipe's sessions are the generic fold BY CONVERSION
(`alt_seq_f_lm`/`alt_seq_p_lm` are `reflexivity` -- Coq compares the
fixpoints structurally), echo's is not (its panic test is `decide`, the
model's `bool_decide`), hence an equation.  Nothing imports the two files
yet.

SECOND CUT (same day): `lmodel` gained `lm_ok` (admissibility),
`lm_body_ok`/`lm_body_byte` (the input discipline's two readings);
`LineModel.v` now has `lm_alts_ok`, `lm_disc_input`, the stream folds
(`lm_pending_at`, `lm_proc_before_from`, `lm_proc_before`,
`lm_proc_stream`) and the writer's stages (`lm_wr_pro/blk/open/owed/sp/
ban/tail/blk_t/sp_t/open_t/banp`, `lm_wr_pre`, `lm_blkcs`).
`LineModelInst.v` (registered after `PipeOutPure`): `alts_ok`,
`disc_input_{f,p}`, `pending_at_{f,p}` by conversion; the stream folds by
induction (the state is a fixpoint PARAMETER: the file's at `option
fstate`, the pipe's absent, so those fixes do not convert).
`LineModelWr.v` (after `PipeLinksLine`, since the `wr_*` predicates live
in the Iris-tier link files): all fifteen file/pipe writer equations,
the base ones by rewriting the stream equations, the derived ones
(`owed`, `sp`, `blk_t`, `banp`) through the base ones (`banp`'s S arm by
`functional_extensionality`, already an axiom of the tree).  Echo's
writer equations are NOT stated (echo is the pipe's corollary; its
`decide`-vs-`bool_decide` panic test makes them lemmas, not
conversions -- state them only if M2 needs the echo instance directly).

THIRD CUT (2026-09-23): DETERMINACY ONCE.  `lmodel` gained four fields
(`lm_line_ok`, `lm_st_ok`; `lm_term` the coverage-ending arm, `lm_merge`
what it can have written) and a laws record `lm_laws M` (body parses to a
well-formed line; the step keeps `lm_st_ok`; a panic prints `alt_panic`;
a coverage-ending arm never panics and prints a mergeable output;
`lm_merge` is prefix-closed; `lml_cont_shape`: every other continuation is
a `$`-free run then the prompt AND, put beside the panic line on one
wire, IS the panic line -- stated in that consequence form because the
file proves it from a newline-shape disjunction and the pipe from a
three-way one).  `LineModel.v` §3 (section `determinacy`, `Context (L :
lm_laws M)`): `lm_cont_pair_det` (the block step, the pipe's four cases
with D4's two guards), `lm_seq_prefix_det` (the induction, at two states
and with the round-by-round block equality), `lm_sess_prefix_det` (AT
TWO STATES `s s'`).  The byte facts both models had proved twice
(`fd_*`/`pd_*`: the `$`-split, prompt-of-`$`, the out-vs-panic
collision, the list helpers) moved to a new pure `iris/LineBytes.v`
(`lb_*`, `nodollar`), registered after `EchoDisc`; `FileDisc` and
`PipeDisc` `Require Export` it and `Require Import LineModel`.
`FileDisc` §6 and `PipeDisc` §7 (the two ~700-line determinacy
sections) are DELETED and replaced by the instances (`file_lm`,
`pipe_lm`, the session/pointer/range/discipline equations, which moved
there from `LineModelInst`), the laws (`file_lm_laws`, `pipe_lm_laws`:
each a `constructor` over the landed byte lemmas) and the landed
theorems as one-line corollaries: `FileDisc.sessf_prefix_det2` (two
states; MOVED from `FileOutPure` §8, whose own 70-line proof is gone),
`FileDisc.sessf_prefix_det` (its `s' := s` case),
`PipeDisc.sessp_prefix_det` (the D4 guards discharged by
`palt_isforkS_inv`/`palt_ok_forkS_pipe`).  `LineModelInst.v` keeps only
the stream-fold equations and `echo_lm`.  Net: -614 lines.  Echo's
`EchoOutPure.sess_prefix_det` is NOT a corollary: its statement is at
`cs_ok` (every code below 4 at every index), not the model's range
condition, and echo is the pipe's corollary in the landed tree; it goes
with the echo tier at M5.  Gotchas met: a variable named `I` shadows
`True`'s constructor (`Logic.I`); comments must not contain `"`.

M1 EXIT REACHED once the whole-tree gate passes (this landing).  NEXT:
M2 -- `GenLinksLine.v`, the twelve families over an `lmodel`, a cursor
and a state-witness family, with the per-shape block arm hook; read
`FileLinksLine.v`/`PipeLinksLine.v` side by side first and write the
family-shape table into this file before coding.
