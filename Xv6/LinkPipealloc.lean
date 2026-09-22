/-
`pipealloc` meets its specification, given `filealloc`, `kalloc`, `initlock`
and `fileclose`.
-/
import Xv6.ProofPipealloc

namespace Xv6

theorem Pipealloc (FA : FILEALLOC) (KA : KALLOC) (IL : INITLOCK) (FC : FILECLOSE) : PIPEALLOC :=
  pipealloc_proof FA KA IL FC

end Xv6
