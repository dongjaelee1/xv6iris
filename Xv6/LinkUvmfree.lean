/-
`uvmfree`'s interface, from its proof and the interfaces of `freewalk` and
of `uvmunmap` at the bare-table altitude (`Xv6.UPtFree.UVMUNMAP_BARE`; see
`Xv6/UPtFreeLemmas.lean` for why `SpecUvmunmap`'s freeing contract, stated
over `procPtAt`, cannot serve this caller).
-/
import Xv6.ProofUvmfree

namespace Xv6

open Xv6.UPtFree

/-- `uvmfree` meets its specification, given `freewalk`'s and `uvmunmap`'s
(the bare-table arm). -/
theorem Uvmfree (UB : UVMUNMAP_BARE) (FW : FREEWALK) : UVMFREE := uvmfree_proof UB FW

end Xv6
