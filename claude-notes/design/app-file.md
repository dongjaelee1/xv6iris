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
   WHAT IS REFUTED, on the other hand, is a PARTIAL chunk: `writei`'s
   "disturbed region" (a partially copied block committed, kernel defect
   D1's fix) exists only because `either_copyin` can fail on the user
   arm, and `SpecCopyin`'s failure arm names an unreadable address — so
   the held write chain's partial node carries that reason (design §3,
   RELAY 4) and a caller whose source run is mapped, as every U-tier
   write's is (`usrc_ok`'s mapped row), meets no partial arm.  A chunk
   either lands whole or not at all; nothing unnamed ever reaches `f`.
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

`parse_line : list (bv 8) -> option uline` inverts `line_body` (the
line without its newline: the bodies `LineWords.bodies_of` cuts have it
stripped), decidable; `disc_input_f` is prefix-closed the way
`disc_input` is, with the partial line's bytes `fbody_byte := wl_body_byte
∨ '>'` (a user halfway through `echo hi > f` is at a `>`).  sh's lexer
sees `>` as a symbol token; the redirect is canonical (one blank each
side, at the end), which is what the sh walk (§5.1) is stated at.

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
                                                --   (xv6 truncates only AFTER filealloc succeeds, so an open
                                                --    that fails at a PRESENT f moved nothing: that is RFOpenU)
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

    good_out_f (s0 : fst) (seg : list mobs) : Prop :=
      exists ps cs, pro_ok_f ps cs _ /\ alts_ok (ins seg) cs      -- Forall2 ralt_ok against lines_of, pinning length cs
                    /\ obs_wire Uart0 seg `prefix_of` sessf ps cs s0 (ins seg)

    file_phi h := disc_f h ->
      exists s0s : list fst, length s0s = length (cycles_of h)
        /\ (forall s, s0s !! 0 = Some s -> s = None)          -- the mkfs image has no `f` (guarded: the empty history has no cycle)
        /\ (forall k s, s0s !! S k = Some s -> fadm_boot (echof_lines_before h (S k)) s)
        /\ Forall2 (good_out_f …) s0s (cycles_of h).

`disc_f` is `EchoDisc.disc` with `disc_input_f` and `sessf` at the
rate bound (`disc_pt` reads `sessf`, so D1/D2 are unchanged in shape).
Five machine transcripts are checked as witnesses by `vm_compute`
(`FileDisc.demo_*`), including "echo, power off, cat" and "echo, crash
mid-round, cat shows a prefix", and one NEGATIVE witness (`demo_f_bad`:
`cat f` printing `goodbye` after only `echo hello world > f` is refuted) —
the vacuity rule of `durable-notes.md`.  The determinacy proof
(`sessf_prefix_det`) runs on one observation, `cont_shape`: every
non-panic alternative's output is a `$`-free run followed by the prompt,
so no table of alternatives is compared.

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

**WHY THE OFFSET MUST BE HELD** (the one kernel-tier campaign this design
needs; lanes OFF-HAND-2/3 in the worklist).  The append step needs `off =
|bs0|`.  The fire hands `off` as a number; the fd's offset is the open-file
object's, and in mode `park` (every open today) the user half sits in
`off_user_inv γo`, an existential nobody can read.  Reporting the offset
(RD-2's route R-c) does not help: a reported number has no tie to the
row, and between two fires nothing says the object's offset did not
move.  RD-1 landed the other mode at the ghost level — `UserOff.uoff`,
`off_pub_hand`, `off_supply_held` — and lane OFF-HAND (its findings are
in the worklist) checked what stands between it and a held U-tier
member.  FOUR coupled facts, each adopted as a ruling:

1. **The mode is a per-file-object constant.**  `FileInvDefs.fdstate_ok`
   pinned every inode row at `OffParked`; with the mode free,
   `fdstate_ok_inj` (two descriptors on one file report one state) is
   false.  So the mode joins the payload names (`fpnames.fp_om`) beside
   the inum, the row's mode is `fp_om` of its object, and dup and fork
   share one mode by construction (user-read.md §4).
2. **Successor-parkedness moves from the pure table relation to the
   family's post.**  `UsysMemOk.usys_fd_ok`'s open arm asserted the new
   row parked, tier-free, and the generic user-safety Löb read its
   successor's parkedness there.  Now the open's RECEIPT carries the mode
   as the caller's family chose it (`xfam`'s `of_mode`); the generic
   family fixes `OffParked` and reads its successor off its own post.
3. **The publish reads the caller's mode** (`ProofSysOpenPub`:
   `off_pub_park` or `off_pub_hand`, `fp_om` set to match, the held half
   `uoff γo 0` in the receipt at `OffHeld`).
4. **The exec crossing takes the surrender bundle — on the TAINT arm only.**
   A generic slot's mint needed `fdv_all_parked` of the whole table; lane
   OFF-HAND-2 put that row on the exec crossing's wands, kernel-paid from
   the pin, and OFF-HAND-3 relayed it into every ENTRY as a received
   premise.  That is right for the taint arm (the generic mint is the
   row's only consumer) and WRONG for a verified entry: an entry that
   receives "the table is all parked" can never be entered with a held
   row, and the redirect child execs /echo holding `f` at a held offset.
   RULED (2026-09-17): the verified entries (`image_entry`,
   `image_entry_at`) DROP the row — the held halves reach the new image
   through `my_pay`, which both arms receive at the call — and the taint
   arm (`image_entry_taint`, the generic mint) takes the SURRENDER bundle
   `FdPark.uoff_surr_at` instead, which the caller's taint-arm proof
   builds itself under a fancy update from the `uoff`s in its payload
   (`uoff_park`, one persistent `off_user_inv` per held row).  The
   carrier is the SET of descriptors a record may hold, `ukn_held : gset
   nat` on `uk_names` (OFF-HAND-3's static bit generalised: `∅` is
   "answers for its offsets"; the row `urun_rows` keeps is "every held
   row of the table is in the set"; a hand-open needs its slot in the
   set; a forking parent chooses the child's set; the redirect child's is
   `{1}`, cat's is the tail `[NSTD, NOFILE)`), because a program that
   execs must know WHICH rows to surrender and a count cannot say
   (OFF-HAND-3's finding 2).  A ghost carrier is refuted three ways
   (OFF-HAND-3's finding 1) and is not to be re-proposed.  The generic
   slot is minted at the key and its surrender bundle, its Löb carrying
   the bundle across rounds (a generic process never hand-opens; dup
   shares the object's surrender; close drops the row).

Lane OFF-HAND-2 landed the exec crossing's all-parked row (the kernel pays
it) and found that facts 1–3 sit BEHIND the counter: the generic
builders of a read/write chain (`FsAbsInvFire.fsabs_filewrite_in`) serve
an arbitrary row and need `⌜fdst_parked st⌝`, which only a program that
can state its own table's parkedness supplies.  So OFF-HAND-3 goes
counter first (`uheld` inside `urun`, a fact about the whole table, the
shape of `urun_nopipe`), then the mode in `fpnames`, then the HELD BRANCH
of `filewrite_in`/`fileread_in`, whose chain nodes RELAY what the claim's
step cannot otherwise know (lane F-WRITE's findings): the fire's offset
is the caller's anchor (`off = off0 + p`), the node's run is the whole
chunk, and the partial node carries `either_copyin`'s reason (RELAY 4,
§0), so a mapped source refutes it; then the hand-mode open leaf and the
two held members.  `FdSlots.foff_row` already answers `emp` at `OffHeld`.

## 4. The console side: the stage carries the era's boot state, the ledger the line list

The echo application's per-era STAGE (`EchoOut.ostage`: `ps`, `cs`,
`E`, `w`) with its pure account `ecl_pure`, its four per-era authorities
(`era_pins`), its links (`echo_write_link`, `_blk`, `_pro`,
`echo_read_link`) and its ledger (`echo_led`) are the shape.  The file
application's are THE SAME SHAPE with two additions, in NEW files
(`FileOutPure.v`, `FileOut.v`) that reuse `EchoOut`'s ghost algebra and
never edit the echo files — the echo theorem and its audit stay exactly
as they are.  (A functor over a line model was considered and declined:
the generic links take one more argument than the echo ones, so the
thirty files above `EchoOut` would move for a statement-preserving
refactor's sake.  The pure stage machine is ~1,500 lines of list
algebra; its twin at `FileDisc`'s session is the price.)

### 4.1 What the stage adds: ONE value per era

The transcript of a cycle is `FileDisc.sessf ps cs s0 I`: the session
resolved by `ps`/`cs` as before, threaded through the f-state from the
ERA'S BOOT STATE `s0`.  Every round's state is DETERMINED by `s0`, the
lines and the alternatives (`fsm`), so the stage carries no history of
states — only `s0`:

    Record fostage := MkFO { o_ps; o_cs; o_E; o_w; o_f0 : option fst }.

`o_f0` is `None` until the era's FIRST process byte and `Some s0` from
then on; `feout_pure` says `o_f0 = None -> o_E = [] /\ o_w = []` (under
the discipline no input precedes init's banner, and under the taint the
arm does not matter), and `pending_f`/`D_f` read `o_f0`'s value where
`EchoOutPure.pending_at`/`D` read nothing.  `cs` entries are `ralt`s in
`FileDisc`'s `nat` encoding; `ralt_ok` replaces `< 4`.

The per-era ghost: `f0_auth v l` / `f0_lb v s0`, a `mono_list` at one
more gname per era (`AppEcho`'s `cons_made` trick: `●ML []` before,
`●ML [s0]` after, `◯ML [s0]` the PERSISTENT witness), kept in a second
per-era record the file ledger allocates beside `era_pins` at `al_pow`
(a `ghost_map nat gname`; `EchoOut.era_pins` is not edited).

**Who files `s0`, and with what.**  The era's first write link — init's
first banner byte, at cursor `P = 0`, `file_write_link_first` — takes
the deed's typed witness from `file_boot` (`▷ (f_typed c s0 ∨ taint)`,
stripped: `fl_lb c ls ∗ ⌜f_bytes_typed ls s0⌝`, or `s0 = None`, or the
taint) and files `o_f0 := Some s0`, keeping the witness as a persistent
conjunct of the stage (`f0_typed`) for the ledger to read (4.3).  init
holds the deed at that moment (`file_boot` reaches it through
`App.al_programs`), so the value is its own.

**The process side.**  `file_write_link k v P b ps0 cs0 s0 I0 Φ` is
`echo_write_link` with `f0_lb v s0` beside the three bounds and the
premise `proc_stream_f ps0 cs0 s0 I0 !! P = Some b`; `_blk` files an
alternative `a` with `ralt_ok (line of last_ws I0) a`; `_pro`,
`read_link`, the taint routes and the drain are the echo ones at the file
stage.  A program proves its byte is the stream's from the same facts as
before PLUS the state before its round, which it computes from `s0`, the
lines and the choices — all of which it holds lower bounds of.

### 4.2 The deed meets the stage in sh's proof, purely

The stage never sees the deed and the claim never sees the stage.  What
ties them is a PURE invariant the shell carries: "my deed's content is
the model's state at my round index" — true at the era's start (sh
receives the deed from init with the fact that `s0` was filed at its
value) and re-established at every round because the process that files
the round's alternative knows its effect exactly: sh files `RFRan sel` at
its prompt byte after `wait` with `sel` from echo's exit payload (echo's
proof tracks the landed chunks purely), `RFOpenU`/`RFFork` with the deed
unchanged, the child files `RFExec`/`RFOpenM` with the deed at `Some []`,
cat files `RCRan` and returns the deed unchanged.  cat's own byte
premise is then `proc_stream_f … !! P = Some b` with its round's block
being `content (state before) ++ "$ "`, and `content (state before)` IS
the bytes its `read` delivered, by the deed's agreement and sh's
invariant handed down with the deed.

### 4.3 The ledger: the line list and the conclusion

    file_led c h := echo_led-shaped:
        mono_nat_auth (taint) ∗ pin_map h ∗ f0_map h
      ∗ AppFile.fl_auth c (efl_of h)                      -- THE LINE LIST
      ∗ (⌜file_good h⌝ ∨ T)

`efl_of h : list wordline` is the pure parse: the words of every complete
`LEchoF` line the console has received, over the whole history.  The rx
wand appends when a newline completes such a line (`FileDisc.lines_of`
at the new input; `disc_input_f` says the body parses), and mints the
tag with the lower bound: `file_tag c h := etag h ∗ fl_lb c (efl_of h)`.
The tag is how the line reaches the child's create step (`file_typed_some`
needs `ws ∈ ls`), through the console read (`UConsLine.ush_tag_law`) and
sh's fork lend.

`file_good h` is `file_phi`'s body without its antecedent: `∃ s0s`, one
boot state per cycle, `s0s !! 0 = Some None`, every later one in
`fadm_boot (efl_before h k)`, and `Forall2 (good_out_f …) s0s (cycles_of
h)`.  The tx wand's drain (`fecl_drain`, `EchoOut.ecl_drain`'s twin) hands
the ledger `good_out_f Ls s0 (open_seg h ++ [out b])` for the stage's
own `s0` together with `f0_typed`'s witness; the ledger fixes the era's
`s0` at the era's first drain (it keeps `f0_lb v s0` from then on and
agrees at every later one) and proves `fadm_boot` from the witness
against its own `fl_auth`: the lb's `ls` is a prefix of `efl_of h`, and
under the discipline no `LEchoF` line of THIS era precedes init's first
byte, so `ls ⊑ efl_before h k` (under the taint the conjunct is `T`).
`al_pow`'s seed is `fecl` at the empty stage with `o_f0 = None`, plus
the turn.  `Hphi` reads `file_phi` off the ledger as `echo_R_phi` does.

### 4.3a What lane STAGE landed, and the two rulings (2026-09-17)

STAGE landed 4.1–4.4 in `FileOutPure.v`, `FileOut.v`, `FileLinks.v`,
`AppFileRec.v` (whole tree green, both audits unchanged) with these
corrections to the text above, which are now the design:

- **The tag is at the FILE discipline**: `ftag h := ⌜trace_shape h true⌝
  ∗ (⌜disc_f h⌝ ∨ file_taint c) ∗ fl_lb c (efl_of h)` — NOT `etag ∗ lb`,
  because `disc_f h` does not imply `disc h` (a `cat` line is not an echo
  line).  The ledger's counter is at `decide (disc_f h)`.
- **No total range condition**: the stage carries the POINTWISE
  `alts_pre I cs` and `FileDisc.alts_ok` is reached by padding
  (`alts_pad`), which moves no prologue round.
- **`feout_pure`'s `o_f0` clause is an IFF** (`o_f0 = None <-> o_E = []
  /\ o_w = []`).
- **The era's first byte is a prologue-choice write**: at `ps0 = []` the
  plain link's premise is unsatisfiable, so `file_write_link_first` is the
  `_pro` shape at the empty stage and needs no stage premise.
- **The record's fixed part is `FileOut.file_gn`** (AppFile's
  `file_fixed` paired with the era map's gname); AppFile's lemmas are read
  at `fgn_cl g`.
- **The read exports a truncated choice list** (`fread_ret`).
- **Determinacy at two boot states** (`sessf_prefix_det2`): the
  discipline's witness and the claim's own need not agree, and
  `alt_seq_f_prefix_det` already takes them apart.
- **`al_programs` is a section hypothesis** of `AppFileRec.file_laws`
  until SH-ROUND lands (the preferred shape).

STAGE named two blockers.  RULINGS:

**Blocker 1 — `Decision (disc_f h)` is a section hypothesis of `FileOut`.**
The ledger's counter must decide the file discipline at every rx.
`disc_f`'s `∃ s : fst` ranges over all byte lists; the rest (`∃ ps cs`)
ports from `EchoDisc.disc_seg'_dec` (`pro_cands`, `bounded_lists`, plus
an enumerator of `sel`s).  THE FIX IS A CANONICALISATION LEMMA, not a
change to the discipline: a boot state's content surfaces on the wire
only through an `RCRan` round whose state is `s0` itself (the state
before a round is `s0` exactly, or a reset value `Some []`/`Some (subseq
…)` that does not depend on `s0` — `fsm` never modifies `s0`, and
`RFOpenM` keeps a present state), and there it is printed VERBATIM
(`cont (Some bs) LCat RCRan = bs ++ u_prompt`) inside a checked
transcript, hence a contiguous substring of that prefix's wire.  If no
checked transcript (`p ∈ in_pres seg`) contains such a round, every
checked transcript is IDENTICAL at `Some []` (the state chains agree
pointwise except at `s0`-derived positions, and `cont` reads the state
only at `RCRan`).  So `(∃ s, fst_ok s /\ disc_seg_f' s seg) <-> (∃ s ∈
scands seg, …)` with `scands seg := None :: Some [] :: (Some <$>
substrings (obs_wire Uart0 seg))` — finite — and `fcont_ok` is decidable
(`last bs = Some wl_nl` and `Forall wl_body_byte` of the rest).  Lane
FILE-DEC (`iris/FileDiscDec.v`): `Global Instance disc_f_dec h :
Decision (disc_f h)`, then `FileOut`'s `Hdf` context goes.  Not on any
program lane's critical path.

**Blocker 2 — `file_phi`'s `echof_lines_before` IS reachable; no claim
change.**  STAGE compared the deed's witness against the ledger's line
list at EVERY drain and dropped `file_phi`'s antecedent.  Both are the
error.  The ledger's conclusion is `FileDisc.file_phi h` VERBATIM (the
antecedent `disc_f h` included; `disc_f` is prefix-closed —
`FileOutPure.disc_f_prefix` — so the induction at each step assumes the
discipline of the NEW history and gets the old one's witnesses), and the
era's boot state is FIXED AT THE ERA'S FIRST DRAIN, where the cycle's
input is empty: under `disc_f h`, a cycle whose wire is empty has no
input byte (D2 at the prefix before its first input byte would put
`pro_of ps` — nonempty under `pro_ok_f` — on an empty wire), so
`efl_of h = echof_lines_before h (obs_boots h)` exactly there, and
`f0_typed_adm` reads the witness's `ls ⊑ efl_of h` AS `fadm_boot
(echof_lines_before h k) s0`.  At cycle 0 the same reading refutes the
`Some` arm (`ws ∈ ls ⊑ []`), which is the guarded first clause.  The
ledger keeps, per era, the state it fixed: `f0_lb vf s0` from
`fdrain_ret` (which hands the era pin and the lower bound beside the
witness; the stage holds `f0_auth vf [s0]`), and every later drain's
`s0` agrees with it (two lower bounds of a list of length ≤ 1).  The
pure carrier is `∃ s0s, ⌜disc_f h -> file_phi_body h s0s⌝` with the
current era's entry pinned by the lower bound once the era has drained
(`obs_wire Uart0 (open_seg h) ≠ []`, a pure condition), and `None`
provisionally at `al_pow` (an empty cycle is good at any state; `None`
is admissible anywhere), REPLACED at the first drain.  Lane STAGE-2, in
`FileOut.v`/`FileOutPure.v` only; `AppFileRec.file_phi := fun _ h =>
FileDisc.file_phi h`.

### 4.4 The record (AppFile layer B)

`app_file := MkApp file_fixed file_cl file_names file_pred file_boot
file_R file_ifc file_turn file_phi` with `file_ifc` = echo's tag grown
by the lb, echo's kill credential (the taint), and `fecl` at the file
taint; every `xv6_app_laws` field but `al_programs` discharged at the
projections (`AppEcho`'s lemmas through `file_pred_cons`, the ledger's
five at `file_led`), `Happ_init` = `file_init_img`, `al_xfer` =
`file_xfer_boot`.

## 5. Programs

### 5.1 sh: the redirect

The line `echo a b > f` lexes to `echo`, `a`, `b`, `>`, `f`; `parseexec`
calls `parseredirs` after every token, so after `b` the tree becomes
`URedir (UExec [echo;a;b]) "f" 0x601 1`; `nulterminate` NULs the file
name.  `UkShRedir.ush_top` is the scope one level wider than
`UkShRun.ush_simple`: one top-level `URedir` over a simple tree (the two
arms that move the descriptor table were refuted only because the walk
did not carry the ledger; a structural `Fixpoint` cannot say "at the top
and nowhere deeper", so the widening is a layer, not an edit).  The REDIR arm
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
