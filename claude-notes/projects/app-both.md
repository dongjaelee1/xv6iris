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
  downstream moves.
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

## RESUME HERE (2026-09-22)

Nothing built.  Start M1: read `FileDisc.v` §§1–5 (the line model as it
exists at `fstate`), `PipeDisc.v` §1 (the alternatives with interleavings)
and `EchoDisc.v` §2 (the session) side by side, and write `LineModel.v`'s
record so that `FileDisc.sessf` IS `sess file_lmodel` by conversion.
