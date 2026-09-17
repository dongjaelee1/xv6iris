/-
Link `kexit`: the sealed proof instance clients import.
-/
import Xv6.ProofKexit
import Xv6.LinkMyproc
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkReparent
import Xv6.LinkWakeup
import Xv6.LinkSched

namespace Xv6

/-- The proved `kexit` interface, given the process, lock, fs and scheduler
boundaries. -/
theorem Kexit : KEXIT :=
  kexit_proof Myproc Acquire Release (Reparent Wakeup) Wakeup Sched

end Xv6
