/-
Link `kfree`: the sealed proof instance clients import.
-/
import Xv6.ProofKfree

namespace Xv6

/-- The proved `kfree` interface, given `acquire`, `release` and `memset`. -/
theorem Kfree (AC : ACQUIRE) (RE : RELEASE) (MS : MEMSET) : KFREE := kfree_proof AC RE MS

end Xv6
