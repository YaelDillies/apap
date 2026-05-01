module

public import Mathlib.Data.Real.Sqrt

public section

namespace Real
variable {x : ℝ}

@[simp] lemma sqrt_le_self : √x ≤ x ↔ x = 0 ∨ 1 ≤ x where
  mp := sorry
  mpr := by
    rintro (rfl | hx)
    · simp
    · exact sqrt_le_iff.2 ⟨zero_le_one.trans hx, le_self_pow₀ hx two_ne_zero⟩

@[simp] lemma le_sqrt_self : x ≤ √x ↔ x ≤ 1 := by
  obtain hx | hx := le_or_gt x 0
  · exact iff_of_true (hx.trans x.sqrt_nonneg) (hx.trans zero_le_one)
  · rw [le_sqrt' hx, sq, mul_le_iff_le_one_left hx]

end Real
