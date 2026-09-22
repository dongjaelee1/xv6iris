/-
`pipeclose` meets its interface, given the interfaces of `acquire`
(cancellable), `wakeup`, `release` (normal and DESTROYING) and `kfree` (over
reclaimed memory).

The credential blocker on the non-freeing `release` is RESOLVED (`pc_release`
now uses `RELEASE_REFUTE`; see `Xv6/ProofPipeclose.lean`).  Still BLOCKED on
`ProofPipeclose.pipeclose_proof`, whose full instruction-stepping body is not
yet written (its six stepping lemmas are green).  The intended statement, to be
uncommented once that proof lands:

    theorem Pipeclose (Acq : ACQUIRE_GEN) (Wk : WAKEUP) (Rel : RELEASE_REFUTE)
        (RelC : RELEASE_CANCEL) (Kf : KFREE_FREE) : PIPECLOSE :=
      pipeclose_proof Acq Wk Rel RelC Kf

This file imports `ProofPipeclose` (the only Proof file it may import) and
compiles green in the meantime.
-/
import Xv6.ProofPipeclose

namespace Xv6

theorem Pipeclose (Acq : ACQUIRE_GEN) (Wk : WAKEUP) (Rel : RELEASE_REFUTE)
    (RelC : RELEASE_CANCEL) (Kf : KFREE_FREE) : PIPECLOSE :=
  pipeclose_proof Acq Wk Rel RelC Kf

end Xv6
