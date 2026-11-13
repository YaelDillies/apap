module

public import Mathlib.Analysis.RCLike.Basic

public section

namespace RCLike
variable {K : Type*} [RCLike K]

@[simp] lemma eNorm_ofReal (r : ℝ) : ‖(r : K)‖ₑ = ‖r‖ₑ := by simp [eNorm]

end RCLike
