/-
Link `proc_pagetable` / `proc_freepagetable`: the proof instances clients
import.  Both build on the user-memory functions of `vm.c`, whose
interfaces stay parameters here, so a client may close them with the
linked ones or with its own.
-/
import Xv6.ProofProcPagetable

namespace Xv6

/-- `proc_pagetable` meets its specification, given `uvmcreate`'s,
`mappages`' (uncounted), `uvmunmap`'s and `uvmfree`'s. -/
theorem ProcPagetable (UC : UVMCREATE) (MP : MAPPAGES_ANY) (UM : UVMUNMAP) (UF : UVMFREE) :
    PROC_PAGETABLE := proc_pagetable_proof UC MP UM UF

/-- `proc_freepagetable` meets its specification, given `uvmunmap`'s and
`uvmfree`'s. -/
theorem ProcFreepagetable (UM : UVMUNMAP) (UF : UVMFREE) : PROC_FREEPAGETABLE :=
  proc_freepagetable_proof UM UF

end Xv6
