/-
`sys_close` meets its specification, given `argfd`, `myproc` and `fileclose`.
-/
import Xv6.ProofSysClose

namespace Xv6

theorem SysClose (AF : ARGFD) (MP : MYPROC) (FC : FILECLOSE) : SYSCLOSE := sys_close_proof AF MP FC

end Xv6
