module

public import Mathlib.Analysis.Real.Sqrt

public section

namespace Real
variable {x : ℝ}

@[simp] lemma sqrt_le_self : √x ≤ x ↔ x = 0 ∨ 1 ≤ x := by
  obtain hx | hx := le_or_gt x 0
  · simp [sqrt_eq_zero_of_nonpos hx, le_antisymm_iff, hx, not_le.2 (hx.trans_lt zero_lt_one)]
  · simp [sqrt_le_iff, sq, le_mul_iff_one_le_right hx, hx.le, hx.ne']

@[simp] lemma le_sqrt_self : x ≤ √x ↔ x ≤ 1 := by
  obtain hx | hx := le_or_gt x 0
  · simp [hx.trans]
  · rw [le_sqrt' hx, sq, mul_le_iff_le_one_left hx]

end Real
