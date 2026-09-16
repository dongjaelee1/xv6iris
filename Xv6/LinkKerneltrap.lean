/-
Link `kerneltrap`: the proof instance clients import.  kerneltrap calls
`devintr`, `myproc` and `yield`; myproc is closed with its linked
interface, devintr and yield remain parameters until their cones are
modeled.
-/
import Xv6.ProofKerneltrap
import Xv6.LinkMyproc

namespace Xv6

/-- The proved `kerneltrap` interface, given `devintr` and `yield`. -/
theorem Kerneltrap (DI : DEVINTR) (YI : YIELD) : KERNELTRAP := kerneltrap_proof DI Myproc YI

end Xv6
