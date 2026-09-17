/-
Link `setkilled`, `killed` and `kkill`: the sealed proof instances clients
import.  All three take the proc lock, so they close over the linked
`acquire` / `release`.
-/
import Xv6.ProofKilled
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

/-- The proved `setkilled` interface. -/
theorem Setkilled : SETKILLED := setkilled_proof Acquire Release

/-- The proved `killed` interface. -/
theorem Killed : KILLED := killed_proof Acquire Release

/-- The proved `kkill` interface. -/
theorem Kkill : KKILL := kkill_proof Acquire Release

end Xv6
