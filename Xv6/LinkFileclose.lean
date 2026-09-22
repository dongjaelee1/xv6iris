/-
`fileclose` meets its specification, given `acquire`, `release` and
`pipeclose`.
-/
import Xv6.ProofFileclose

namespace Xv6

theorem Fileclose (AC : ACQUIRE) (RE : RELEASE) (PC : PIPECLOSE) : FILECLOSE := fileclose_proof AC RE PC

end Xv6
