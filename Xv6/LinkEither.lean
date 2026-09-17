/-
Link `either_copyout` / `either_copyin`: the proof instances clients
import.  Both call `myproc` and `memmove`, and one of `copyout` /
`copyin`; the interfaces stay parameters here, so a client may close them
with the linked ones (`LinkMyproc`, `LinkMemmove`, ...) or with its own.
-/
import Xv6.ProofEither

namespace Xv6

/-- The proved `either_copyout` interface, given `myproc`, `copyout` and `memmove`. -/
theorem EitherCopyout (MP : MYPROC) (CO : COPYOUT) (MM : MEMMOVE) : EITHER_COPYOUT :=
  either_copyout_proof MP CO MM

/-- The proved `either_copyin` interface, given `myproc`, `copyin` and `memmove`. -/
theorem EitherCopyin (MP : MYPROC) (CI : COPYIN) (MM : MEMMOVE) : EITHER_COPYIN :=
  either_copyin_proof MP CI MM

end Xv6
