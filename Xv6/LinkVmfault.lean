/-
`vmfault`'s and `uvmclear`'s interfaces, from their proofs and the
interfaces of the callees (`ismapped`, `kalloc`, `kfree`, `memset`, the
uncounted `mappages`, and `walk`), plus `vmfault`'s residual `UPTWF_TFP`
assumption.
-/
import Xv6.ProofVmfault

namespace Xv6

/-- `vmfault` meets its specification, given `ismapped`, `kalloc`, `kfree`,
`memset`, the general `mappages` contract, and the `UPTWF_TFP` fact. -/
theorem Vmfault (IM : ISMAPPED) (KA : KALLOC) (KF : KFREE) (MS : MEMSET)
    (MA : MAPPAGES_ANY) (TF : UPTWF_TFP) : VMFAULT :=
  vmfault_proof IM KA KF MS MA TF

/-- `uvmclear` meets its specification, given non-allocating `walk`. -/
theorem Uvmclear (W : WALK_NOALLOC) : UVMCLEAR := uvmclear_proof W

end Xv6
