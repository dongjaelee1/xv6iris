/-
`pipewrite` meets its interface, given the interfaces of `myproc`,
`acquire`/`release` (cancellable), `wakeup`, `sleep_prepare`/`sleep`,
`killed` and `copyin`.  This file imports `ProofPipewrite` (the only Proof
file it may import).
-/
import Xv6.ProofPipewrite

namespace Xv6

theorem Pipewrite (MP : MYPROC) (AC : ACQUIRE_GEN) (RE : RELEASE_GEN) (WK : WAKEUP)
    (SP : SLEEP_PREPARE) (SL : SLEEP) (KL : KILLED) (CI : COPYIN) : PIPEWRITE :=
  pipewrite_proof MP AC RE WK SP SL KL CI

end Xv6
