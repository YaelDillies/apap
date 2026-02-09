import Mathlib.Analysis.RCLike.Basic

namespace RCLike
variable {K : Type*} [RCLike K]

@[simp] lemma enorm_ofReal (r : ℝ) : ‖(r : K)‖ₑ = ‖r‖ₑ := by simp [enorm]

end RCLike
