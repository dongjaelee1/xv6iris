/-
Link `copyout`, `copyin` and `copyinstr`: the proof instances clients import.
Each copies bytes between the kernel and a process's address space, walking
its page table and faulting in lazily-allocated pages on the way.  Their
callees stay parameters here, so a client may close them with the linked ones
or with its own.

Note: `copyin` and `copyinstr` do not call `walk` (only `copyout` does, for
its `PTE_W` check), and `copyinstr` copies byte-by-byte rather than through
`memmove`; the interfaces below take exactly the callees each proof uses.
-/
import Xv6.ProofCopyout

namespace Xv6

/-- The proved `copyout` interface, given its callees. -/
theorem Copyout (WA : WALKADDR) (VF : VMFAULT) (W : WALK_NOALLOC) (MM : MEMMOVE) :
    COPYOUT :=
  copyout_proof WA VF W MM

/-- The proved `copyin` interface.  `copyin` calls `walkaddr`, `vmfault`
(no-alloc's job is done by `walkaddr` here) and `memmove`; it does not call
`walk`. -/
theorem Copyin (WA : WALKADDR) (VF : VMFAULT) (MM : MEMMOVE) :
    COPYIN :=
  copyin_proof WA VF MM

end Xv6
