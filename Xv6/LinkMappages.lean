/-
`mappages`' interface, from its proof and the interface of `walk`.
-/
import Xv6.ProofMappages

namespace Xv6

/-- `mappages` meets its specification, given `walk`'s. -/
theorem Mappages (W : WALK) : MAPPAGES := mappages_proof W

end Xv6
