import PvsNP.Complexity

/-!
# The P vs NP problem

The top-level statement of the project. `P_ne_NP` is the famous open problem and is the
permanent `sorry` of the development (unless someone solves it). The other `sorry`s
(`bgs_separation`, `bgs_collapse` in `PvsNP.Relativization`) are work in progress and are listed
in the README.
-/

namespace PvsNP

/-- **P ≠ NP** (open problem; Clay Millennium Problem). Intentionally left unproved. -/
theorem P_ne_NP : P ≠ NP := sorry

end PvsNP
