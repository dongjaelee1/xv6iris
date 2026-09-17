# Design: the FILE application (`AppFile`) — `echo … > f` survives a power cycle, `cat f` prints it

Status: DESIGN OF RECORD (2026-09-17, Fable).  The worklist is
[`../projects/app-file.md`](../projects/app-file.md).  This page builds on
[`applications.md`](applications.md) (the two-instance claim, the
transport, the record), the echo application (`iris/AppEcho.v`,
`iris/EchoDisc.v`, `iris/EchoOut.v`, `iris/EchoOutPure.v`: the console
discipline, the per-era STAGE and the ledger), [`user-write.md`](user-write.md)
/ [`user-read.md`](user-read.md) (the file members, the offset) and
[`user-fd.md`](user-fd.md) (the descriptor ledger, which is what makes
sh's `close(1); open(f)` land on 1).

## 0. The target, in one paragraph

The same image, the same /init and /sh.  A user types, at the console,
lines of three shapes: `echo w1 … wn` (the echo application's line),
`echo w1 … wn > f`, and `cat f`.  The claim: **the file `f` never holds
anything but what an `echo … > f` line put there** — after a completed
`echo hello world > f` round, `cat f` prints `hello world`, in this era
or in any later one (the file system is durable); the alternatives are
exactly the visible failures (sh's exec/open/fork diagnostics, cat's
"cannot open"), an empty `f` (a round whose exec failed after the open
truncated), or — after a power cycle — a chunk-subsequence of an earlier
echo line (the round in flight at the cut).  `f` never contains junk.

**THREE HONEST LIMITS, stated up front, each with its price named:**

1. **A file write can fail, and the failure is invisible.**  Since this
   xv6 revision `balloc` returns 0 when the disk is full and `writei`
   stops (`kernel/fs.c:88`), so `filewrite`'s `-1` arm is real and
   `SpecFilewrite.write_post_fail_at` admits "nothing landed".  Echo
   ignores write's return.  So a completed round's `f` is, honestly, the
   concatenation of the SUBSET of echo's chunks (`"hello"`, `" "`,
   `"world"`, `"\n"`) that landed — in practice all of them, since the
   file needs one block and the image has ~1900 free; but "the disk is
   not full" is a bitmap fact no application-tier claim can see.  The
   model carries the subset (`sel`).  Refuting it is a kernel-tier lane
   (a capacity conjunct in the abstract view) and is NOT taken.
2. **Across a power cycle the theorem is weaker than reality.**  The
   durable claim is the copy made at the LAST COMMIT, and no syscall's
   post says its transaction committed (durability receipts are the
   durable campaign's open lane F; `sys_sync`'s `flushed` receipt is the
   one that exists).  So at a boot the model admits `f` to be the
   subsequence of ANY earlier `echo … > f` line, or absent.  Within an
   era the model is EXACT.  The commit receipt at `write` is priced in
   §6 and is milestone 2.
3. **`echo`'s alternative 2** ("the child died before printing", `$ `)
   is kept for the new round shapes with the f-effect "truncated" — it is
   sh's `argv[0] == 0` exit and unreachable under the discipline, as in
   the echo application.

## 1. The pure model (`iris/FileDisc.v`)

Iris-free, over `EchoDisc`/`LineWords`, so the statement can be read and
refuted without the logic.

**Lines.**  `f` is the literal name `fname_f := "f"` (one file; the name
is a constant of the model, so generalising to a name is an index, not a
redesign).

    Inductive uline := LEcho (ws) | LEchoF (ws) | LCat.
    line_bytes (LEcho ws)  := wl_line ws                       -- "echo a b\n"
    line_bytes (LEchoF ws) := wl_body ws ++ " > f" ++ [wl_nl]   -- "echo a b > f\n"
    line_bytes LCat        := "cat f\n"
    uline_ok (LEcho ws) := EchoDisc.line_ok ws
    uline_ok (LEchoF ws) := EchoDisc.line_ok ws /\ length (line_bytes _) < line_max
    uline_ok LCat := True

`parse_line : list (bv 8) -> option uline` is the inverse on the bodies
`LineWords.bodies_of` cuts, decidable, prefix-closed the way `disc_input`
is (`disc_input_f`).  sh's lexer sees `>` as a symbol token; the redirect
is canonical (one blank each side, at the end), which is what the sh walk
(§5.1) is stated at.

**The file's content.**  echo writes its arguments as separate `write`s:

    echo_chunks ws := interleave (drop 1 ws) with [" "], closed by ["\n"]
                      -- ["hello"; " "; "world"; "\n"]
    subseq cs sel  := concat (map (cs !!!) sel)     -- sel strictly increasing, < length cs

    Definition fst := option (list (bv 8)).      -- None: absent; Some bs: present with bytes bs

THE STATE IS THE CONTENT, not a (words, subset) pair: the content is a
FUNCTION OF THE VIEW (`fcontent_of av`), which is what lets the claim's
transport allocate the copy's ghost at the view's own value outside the
later, exactly as `echo_xfer` allocates its flag at `cons_inum av`.  The
words and the subset live in the ALTERNATIVE that produced the content.

**Rounds and alternatives.**  A round is one typed line; its console
continuation and its f-effect are decided by ONE alternative:

    Inductive ralt :=
      | REcho (a : nat)                -- the echo application's four, unchanged; f unchanged
      | RFRan (sel)                    -- "$ ";                   f := Some (subseq (echo_chunks ws) sel)
      | RFExec                         -- "exec echo failed\n$ ";  f := Some []
      | RFOpenU                        -- "open f failed\n$ ";     f unchanged (create/filealloc failed, f present or absent)
      | RFOpenM                        -- "open f failed\n$ ";     f := Some []   (created, then filealloc failed; only from None)
      | RFSilent                       -- "$ ";                    f := Some []   (limit 3)
      | RFFork                         -- "fork\n";                f unchanged
      | RCRan                          -- fcontent, or "cat: cannot open f\n"; then "$ "
      | RCNoOpen                       -- "cat: cannot open f\n$ " (f present: filealloc/fdalloc failed)
      | RCExec | RCSilent | RCFork.    -- "exec cat failed\n$ ", "$ ", "fork\n"

    ralt_ok (l : uline) (a : ralt) : Prop      -- which alternatives a line shape admits, and sel's shape
    fsm (s : fst) (l : uline) (a : ralt) : fst  -- the f-effect above; RFOpenM only at s = None
    cont (s : fst) (l : uline) (a : ralt) : list (bv 8)   -- the continuation bytes (EchoDisc.line_alts_of at REcho)

`RFOpenU`/`RFOpenM` print the same bytes and differ in f: the observer
cannot tell and does not need to (the echo application's determinacy
argument, `EchoOutPure.sess_prefix_det`, is what carries this; "same
bytes, different index" is already the shape it handles).

**The session, per cycle, with the f-state threaded.**  `EchoDisc.sess`
with `alt_blk` replaced by a fold that carries `s`:

    sessf (ps cs : list nat) (s0 : fst) (I : list (bv 8)) : list (bv 8)
      := pro_of ps ++ blocks (the parsed lines of I, resolved by cs, starting at s0) ++ rest_of I

where `cs !!! i` now indexes `ralt` (an injective `nat` encoding, so the
stage's `cs_auth`/`cs_lb` machinery is reused verbatim; `ralt_ok` is the
decidable range condition where `c < 4` was).  `fst_after ps cs s0 I` is
the state after the last complete line.

**The theorem's conclusion.**  `f` persists, so the statement is over
the whole history, cycle by cycle, with the boot state of each cycle
chosen existentially inside the admissible set:

    fadm_boot (Ls : list (list (list (bv 8)))) : fst -> Prop :=
      fun s => s = None \/ exists ws sel, ws ∈ Ls /\ sel_ok (echo_chunks ws) sel /\ s = Some (subseq (echo_chunks ws) sel)
    -- Ls = the `echo … > f` word lists typed in ALL earlier cycles (limit 2)

    good_out_f (Ls : …) (s0 : fst) (seg : list mobs) : Prop :=
      exists ps cs, pro_ok ps cs _ /\ Forall2 ralt_ok (lines of ins seg) cs
                    /\ obs_wire Uart0 seg `prefix_of` sessf ps cs s0 (ins seg)

    file_phi h := disc_f h ->
      exists s0s : list fst, length s0s = length (cycles_of h)
        /\ s0s !! 0 = Some None                               -- the mkfs image has no `f`
        /\ (forall k s, s0s !! S k = Some s -> fadm_boot (echof_lines_before h (S k)) s)
        /\ Forall2 (good_out_f …) s0s (cycles_of h).

`disc_f` is `EchoDisc.disc` with `disc_input_f` and `sessf` at the
rate bound (`disc_pt` reads `sessf`, so D1/D2 are unchanged in shape).
Five machine transcripts are checked as witnesses by `vm_compute`
(`FileDisc.demo_*`), including "echo, power off, cat" and "echo, crash
mid-round, cat shows a prefix" — the vacuity rule of `durable-notes.md`.

## 2. The claim (`iris/AppFile.v`)

    file_fixed := EchoOut.echo_gn * gname                    -- echo's, plus γfl: THE LINE LIST (§4)
    file_names := echo_names * gname                         -- echo's console pair, plus γd: THE DEED

    fdeed r (s : fst) := ghost_var (fdeed_gn r) (1/2) s      -- the PROCESS CHAIN's half (§3)

    f_typed c None := emp
    f_typed c (Some bs) := ∃ ls, mono_list_lb (fl_gn c) ls
                           ∗ ⌜∃ ws sel, ws ∈ ls /\ sel_ok (echo_chunks ws) sel /\ bs = subseq (echo_chunks ws) sel⌝
    f_state c r av := ∃ s : fst, ghost_var (fdeed_gn r) (1/2) s ∗ f_typed c s ∗ ⌜f_ok av s⌝
    f_ok av None := astep av ROOTINO fname_f = None
    f_ok av (Some bs) := ∃ i, astep av ROOTINO fname_f = Some i /\ av !! i = Some (MkAnode (AFile bs) 1)

The lb sits only in the `Some` arm: a lower bound of the fixed-part list
is not mintable from nothing (`◯ML []` is not a unit), and era 0 has no
`f`.  `f_ok av s` determines `s` (`f_ok_fcontent : f_ok av s -> fcontent_of
av = s`), which is what the transport allocates the copy's ghost at.

    file_pred c r av := echo_taint c.1
                        ∨ (⌜file_fs_pure av⌝ ∗ cons_state c r.1 av ∗ f_state c r av)

`file_fs_pure := echo_fs_pure ∧ era0_cat_pins` (the /cat binary pinned
beside /init, /sh, /echo — `iris/FsCatPin.v`, `FsEchoPin`'s twin at
cat's inum).  The pins are PER NAME (`astep` facts), so an entry `f` in
the root contradicts none of them, and the console state is untouched by
anything `f` does.  `file_pred` is TIMELESS (every fire strips it) and
NOT persistent (the deed's half), exactly as `echo_pred`.

**Why a deed and not a pure arm.**  A pure predicate "f is a
subsequence of some typed line" cannot be STEPPED by echo's writes: the
step must know that the row it is appending to is ITS line's, and no
pure fact about the view survives another process's move.  The deed is
the ghost_var half the process chain holds; agreement with the claim's
half makes the claim's `s` KNOWN to the holder, and `ghost_var_update_2`
inside the fire (AppInv's `app_step` is a basic update since SEAM-I)
moves both.  A tree-layer deed (`AppTree`) was considered and declined:
its ownership is per subtree and hands DOWN at fork, while this claim's
owner is the shell across every round — the deed here is one ghost_var,
and the whole tree machinery is unnecessary weight for one file at the
root (the user's ruling: "go directly on the inode abstract state").

**The steps** (every one an instance of `AppInv.app_top_update_bupd`'s
premise, the holder's half in hand):

- **create** (the child's `open(f, O_WRONLY|O_CREATE|O_TRUNC)` at
  `f_ok av None`): the four create legs at a length-0 parent prefix, on
  `TreeMove.tree_open_create_au`'s mould — the arm leg is invisible to
  `f_ok` (a fresh inum has no name), the parent leg moves `None → Some
  []` (both halves updated), dots/unarm free; the dlookup family reads
  `astep … = None` off the claim.
- **truncate** (`f_ok av (Some bs')`, the open's exists arm): the
  trunc piece `delta_trunc i` moves to `Some []`.
- **append** (echo's chunk `j`, `awrite_full_at`'s `wri_pre av i off bs
  bs0 nl` with `off = |bs0|` — §3 on why the offset is known): `Some bs0
  → Some (bs0 ++ chunk_j)`; echo's own proof carries the words and the
  landed subset purely and re-proves `f_typed` at the new content.  `write_post_fail_at` with nothing
  fired moves nothing and the deed stays; echo's next chunk is at the
  same `s` — that is where `sel` skips.
- **read**: no step; `f_ok` at the deed's `s` is the pinned content
  `PinnedObs.pobs_aopen`'s three lines read (`UkTreeRead.tree_read_piece`'s
  shape, at a pure pin and the deed's agreement instead of a frozen
  tree).
- **every other move** (mknod of the console, init's opens): `f_ok` is
  preserved by inspection (the console's name is not `f`; the fresh inum
  is unnamed) — `cons_state`'s steps carry `f_state` untouched.

**The transport** (`app_xfer_raw`): the copy gets a FRESH ghost_var
allocated at `fcontent_of av` OUTSIDE the later (`echo_xfer`'s shape
exactly), and under the later the arm's `s` is that value by
`f_ok_fcontent`; one half goes into the copy, the other is DROPPED — a
durable copy is never stepped.  The lb duplicates under the later.  The lb duplicates.  **The boot transport**
(`app_xfer_boot_raw`): the same, and the fresh name's other half is the
era's boot resource:

    file_boot c k r := echo_boot c.1 k r.1 ∗ ∃ s, fdeed r s ∗ ▷ f_typed c s

(the typed part stays under one later: it is read off the original arm,
which the transport only sees under `▷`; /init strips it at its first
step, the lb being timeless).

carried by the kernel to /init (`App.al_programs`), handed by /init to
/sh with the console credentials, and never re-minted (`app_boot`'s
producer is the transport, applications.md §3).

**Era 0** (`Happ_init`): `f_ok av_img None` is a computation on the
image — `FsImgCheck`'s root map has no entry `f` (`fsimg_root_no_f`,
one `vm_compute` on `TreeImg.img_root_blk`'s reading, the rule of
user-tree.md §8.1: state the form to compute with).

## 3. The deed's life, and the offset

- **sh holds the deed between rounds** (its slot's payload gains it,
  beside the console credential).  `fork` LENDS it to the child through
  the fork payload (a non-address-space resource: it goes to ONE side at
  the leaf's `∗`, user-heap.md's fork rule), and the child's `exit`
  hands it back through `UkShFork.ushf_wq`'s exit payload beside the
  era's write credential; `wait` returns it to sh.  A fork that fails
  leaves it with sh.  A kill taints (echo's `app_kill`).
- **the child's REDIR arm**: `close(1)` shuts slot 1 of the ledger
  (`wp_uk_ecall_close_std`), `open(f, 0x601)` lands on 1
  (`UserFd.ualloc` at `[console; closed; console]`), the create/truncate
  step above runs with the deed (the child's proof tracks its own line's
  words and the chunk subset PURELY; the deed carries only the content),
  and the receipt is `FdOpen false true
  (FdInode i γo OffHeld)` **with the offset HELD**: `UserOff.uoff γo 0`.
  On `-1` the child prints `open f failed` (the deed is unchanged, or at
  `Some []` if the create leg fired before `filealloc` failed — the
  receipt's arm says which) and exits 1.
- **exec /echo** carries the deed, the held offset and the fd-1 row into
  echo's entry (the process's resources cross exec; only the address
  space is replaced).  Under the taint (the line was not disciplined)
  the child PARKS the offset (`uoff_park`) before the ecall — the generic
  slot for an unverified image needs every row parked (§5.3) — and the
  deed is dropped into the taint arm.
- **echo at a file**: four writes on the held-offset file member; at
  each, phase 1 agrees the deed, `off = |bs0|` from `uoff`, the delta is
  the append, phase 2 returns the deed at the appended content and `uoff` at
  `off + |chunk|`.  `exit` returns the deed to sh.
- **sh's prompt link** records `s` (§4) and keeps the deed.
- **cat**: fork lends the deed; `open(f, O_RDONLY)` at the deed's `s`
  (present: `FdInode i γo OffHeld` on the node `f_ok` names, `uoff γo
  0`; absent: `-1`, refuted-present); `read(fd, buf, 512)` at the held
  offset 0 learns `bytes = subseq …` exactly (`read_arms_file_learn` at
  the claim's pin), the second read returns 0 at offset `|content|`;
  the console writes pay the stage's pending (§4); `close`; `exit`
  returns the deed.

**WHY THE OFFSET MUST BE HELD** (the one kernel-tier lane this design
needs, OFF-HAND in the worklist).  The append step needs `off = |bs0|`.
The fire hands `off` as a number; the fd's offset is the open-file
object's, and in mode `park` (every open today) the user half sits in
`off_user_inv γo`, an existential nobody can read.  RD-1 landed the
other mode at the ghost level — `UserOff.uoff`, `off_pub_hand`,
`off_supply_held` — and RD-2 chose the report-not-own route for the
generic members.  What blocks mode `hand` is ONE pure pin,
`FileInvDefs.fdstate_ok`'s FD_INODE arm ("the offset mode is parked"),
which the generic user-safety WP relies on (a held row has no
`off_user_inv`, so the generic fire supplier cannot pay it).  The lane:
the pin comes off; the generic slot's mint takes `FdSlots.fdv_all_parked`
of its key's table as an EXPLICIT premise, discharged at its three sites
(userinit's `fdt0`; fork's child from a generic parent, and `FdPark`'s
park for a verified one — user-read.md §4's ruling; exec's taint arm,
where the U-tier leaf makes the caller park first); `ProofSysOpenPub`
branches on a mode bit the U-tier open family carries; and the three
held members (`wp_uk_ecall_open_recv_img_held`, `_write_file_held`,
`_read_file_held`) are the landed members with `off_supply_held`.
`FdSlots.foff_row` already answers `emp` at `OffHeld`.

## 4. The console side: the stage grows an f-state history

The echo application's per-era STAGE (`EchoOut.ostage`: `ps`, `cs`,
`E`, `w`) and its pure account `ecl_pure` are kept; two things are added.

1. **`o_fh : list fst`, the f-state HISTORY**, a per-era `mono_list`
   whose gname joins `EchoOut.era_pins` (allocated by `al_pow` with the
   others).  Entry `i` is the f-state at the START of round `i`; sh's
   prompt link appends `fst_after`'s value read off its deed, and the
   stage's pure part requires `o_fh !! S i = fsm (o_fh !!! i) line_i
   (cs !!! i)`.  Entry 0 is the ERA'S BOOT STATE, appended at sh's FIRST
   prompt from the deed `file_boot` handed it, with `fadm_boot` proved
   from the deed's `lb` against the ledger's (below).  `pending` for a
   cat round reads `o_fh`, so the process byte a cat link owes is a
   function of the stage, as every process byte is.
   **The tie to the claim is the deed alone**: cat's link holds the
   deed at `s` and `mono_list_lb (fh_gn v) fh` with `last fh = s`
   (lent by sh at the fork); the stage's `o_fh ⊒ fh` and — the stage's
   invariant — `length o_fh = the round index + 1`, so the entry cat's
   round reads IS `s`.  No fs invariant is opened from a console link and
   no console invariant from an fs fire.
2. **The ledger's LINE LIST.**  `file_R c h := echo_led … ∗
   mono_list_auth (fl_gn c) 1 (echof_lines_of h)`; the rx wand appends
   the words when a `LEchoF` line's newline arrives (pure: the parse of
   `ins` so far); the input tag gains `mono_list_lb (fl_gn c)
   (echof_lines_of h)`, which is how the line reaches the child's create
   step (sh's console read yields the tag, `UConsLine.ush_tag_law`).
   `al_pow` puts `mono_list_lb (fl_gn c) (echof_lines_of h)` into the
   fresh stage, so sh's first record can compare the boot deed's `ls`
   against it (both lbs of one list are comparable).  `Hphi` reads
   `file_phi` off the ledger as `echo_R_phi` does: the boot states are
   the stages' entry-0 values, which the ledger's tx wand copied out at
   each era's first prompt (a pure value beside `echo_led`'s phi
   conjunct).

Everything else — the taint, the tag's discipline arm, the kill
credential, the console claim's `EvOpen`/`EvByte`/`EvClose`/`EvRead`
steps, the turn — is `AppEcho`'s verbatim at the projection `c.1`,
`r.1`.

## 5. Programs

### 5.1 sh: the redirect

The line `echo a b > f` lexes to `echo`, `a`, `b`, `>`, `f`; `parseexec`
calls `parseredirs` after every token, so after `b` the tree becomes
`URedir (UExec [echo;a;b]) "f" 0x601 1`; `nulterminate` NULs the file
name.  `UkShRun.ush_simple` admits one top-level `URedir` over an
`UExec` (the two arms that move the descriptor table were refuted only
because the walk did not carry the ledger — it does now).  The REDIR arm
is `close(1); open(file, mode) < 0 → fprintf(2, "open %s failed\n"); exit(1)
| runcmd(sub)`; the open is a CALL PREMISE of the walk (user-heap.md's
"a call can be a premise"), instantiated by the application's supplier
(§2), so the code walk is claim-free.  The lexable-line premise
`UkShFork.ushf_lexable` grows the redirect shape.

### 5.2 echo at a file

`UEchoOut` is echo's entry at fd 1 = console.  `UEchoFile` is the twin at
fd 1 = `FdInode i γo OffHeld` with the deed and `uoff γo 0` in its Pay:
the four writes on `wp_uk_ecall_write_file_held` with the chain at the
deed (phase 1 agrees, decides `sel ++ [j]`, phase 2 returns the deed
and the offset), no console byte, `exit` returning the deed.  echo's
code walk is untouched (`UkEcho`).

### 5.3 cat

`UkCat*` is the code walk (user-heap.md, "what cat cost").  `UCatKernel`
is its entry at the claim: the argv is `["cat"; "f"]` (read off sh's
node as `UShEcho` reads echo's), the open at `f` from the deed (present /
absent / `-1`), the read at the held offset, the console writes at the
stage's pending (cat's first byte chooses `RCRan`; the "cannot open"
diagnostic is `fprintf(2, …)` through `UkCatFprintf`'s `%s` arm, at the
stage), `close`, `exit`.  The `cat: read error` tail is REFUTED (the
read's `-1` arm at an inode needs a copyout failure, which the mapped row
excludes) — if the kernel spec's arm cannot be refuted at the U tier the
alternative joins §1's list instead; the lane says which.

### 5.4 sh execs cat, and the dispatch

`UShCat` is `UShEcho` at `FsCatPin`; sh's child branches on the parsed
line's shape (a pure case on `parse_line` of the buffer, which sh's own
`ush_tag_law` ties to the typed line), so each shape runs its own
entry: `UShEcho` (echo, console), `UEchoFile` through the REDIR arm,
`UShCat`.

## 6. Milestone 2: the exact durable statement (priced, not taken)

Limit 2 goes away with a COMMIT RECEIPT at `write`: a persistent witness,
produced when `end_op` commits, that the crash slot's application copy is
at or after the fire's state.  The shape that fits this tree: the
application's `app_xfer_raw` returns, beside the copy, `mono_list_lb (fh
… ) …`-style evidence of the arm it copied; the commit law's `dur_pair`
carries it out of `fs_commit_L_seq_permit`; `end_op`'s post (`SpecLog`)
and `filewrite`'s (`SpecFilewrite`, row 16) carry it to the U tier, where
echo's last write puts it in the deed's value and sh's prompt link makes
`o_fh`'s entry EXACT for the next era's boot.  The stage/ledger side of
this design already has the slot for it (`fadm_boot` becomes a
singleton when the receipt is present).  Cost: the WAL's commit
interface (`LogSnapLaw`, `fs_rec_permit`), `SpecLog`/`ProofEndop`,
`SpecFilewrite`/`ProofFilewrite`, `UexecExecInst` row 16 — a durable
lane, not an application one.

## 7. Rejected on the way

- **A pure arm over the view with no deed.**  Not steppable by echo
  (§2).
- **Per-round records agreed between the fs claim and the stage by
  gname.**  Two invariants with no shared authority cannot identify
  gnames; the deed, held by the one process chain, is the identification
  and needs no agreement across invariants.
- **The ledger's tx wand opening `app_inv`.**  Changes `App.v`'s laws
  and buys nothing without a commit receipt.
- **Reporting the offset instead of holding it (R-c).**  The append needs
  `off = |bs0|`; a reported offset is a number with no tie to the row.
