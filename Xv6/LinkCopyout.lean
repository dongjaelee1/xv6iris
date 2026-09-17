/-
Link `copyout`: the proof instance clients import.  `copyout` copies kernel
bytes into a process's address space, walking its page table and faulting in
lazily-allocated pages on the way.  It calls `walkaddr`, `vmfault`, `walk`
(no-alloc) and `memmove`; those interfaces stay parameters here, so a client
may close them with the linked ones or with its own.

Note: `ProofCopyout` currently proves only `copyout`.  The sibling interfaces
`COPYIN` and `COPYINSTR` (declared in `Xv6.SpecCopyout`) are not yet proved --
`copyin_proof`/`copyinstr_proof` do not exist -- so this file links only
`COPYOUT`.
-/
import Xv6.ProofCopyout

namespace Xv6

/-- The proved `copyout` interface, given its callees. -/
theorem Copyout (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE) :
    COPYOUT :=
  copyout_proof WA VF W MM

end Xv6
