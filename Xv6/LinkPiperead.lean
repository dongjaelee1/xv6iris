/-
`piperead` meets its interface, given the interfaces of `myproc`,
`acquire`/`release` (cancellable), `wakeup`, `sleep_prepare`/`sleep`,
`killed` and `copyout`.  This file imports `ProofPiperead` (the only Proof
file it may import).
-/
import Xv6.ProofPiperead

namespace Xv6

theorem Piperead (MP : MYPROC) (AC : ACQUIRE_GEN) (RE : RELEASE_GEN) (WK : WAKEUP)
    (SP : SLEEP_PREPARE) (SL : SLEEP) (KL : KILLED) (CO : COPYOUT) : PIPEREAD :=
  piperead_proof MP AC RE WK SP SL KL CO

end Xv6
