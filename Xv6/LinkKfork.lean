/-
Link `kfork`: the proof instance clients import.  `kfork` calls `myproc`,
`allocproc`, `uvmcopy`, `freeproc`, `safestrcpy`, `acquire` and `release`
(and takes `wait_lock`/`pid_lock`/`kmem` as `isLock`s and the file-system
boundary `[FsEnv]` and the newborn resume wand `[ForkretIs]` in its
contract); the callee interfaces stay parameters here.
-/
import Xv6.ProofKfork

namespace Xv6

/-- The proved `kfork` interface, given `myproc`, `acquire`, `release`,
`allocproc`, `uvmcopy`, `freeproc` and `safestrcpy`. -/
theorem Kfork (MP : MYPROC) (AC : ACQUIRE) (RE : RELEASE) (AL : ALLOCPROC)
    (UV : UVMCOPY) (FP : FREEPROC) (SS : SAFESTRCPY) : KFORK :=
  kfork_proof MP AC RE AL UV FP SS

end Xv6
