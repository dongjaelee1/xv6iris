/-
`uvmalloc`'s and `uvmdealloc`'s interfaces, from their proofs and the
interfaces of `uvmunmap`, `kalloc`, `kfree`, `memset`, `mappages` (the
uncounted contract) and the trapframe-disjointness fact (`TFDISJ`).
-/
import Xv6.ProofUvmalloc

namespace Xv6

open Xv6.UPtAlloc

/-- `uvmdealloc` meets its freeing contract, given `uvmunmap`'s. -/
theorem Uvmdealloc (UM : UVMUNMAP) : UVMDEALLOC := uvmdealloc_proof UM

/-- `uvmalloc` meets its contract, given `kalloc`, `kfree`, `memset`,
`mappages` (uncounted), `uvmunmap` (for the rollback via `uvmdealloc`) and
`TFDISJ`. -/
theorem Uvmalloc (KA : KALLOC) (KF : KFREE) (MS : MEMSET) (MA : MAPPAGES_ANY)
    (UM : UVMUNMAP) (TF : TFDISJ) : UVMALLOC :=
  uvmalloc_proof KA KF MS MA (uvmdealloc_proof UM) TF

end Xv6
