module

public import Mathlib.Analysis.RCLike.Basic

public section

namespace RCLike
variable {K : Type*} [RCLike K]

@[simp] lemma enorm_ofReal (r : ℝ) : ‖(r : K)‖ₑ = ‖r‖ₑ := by simp [enorm]

end RCLike
