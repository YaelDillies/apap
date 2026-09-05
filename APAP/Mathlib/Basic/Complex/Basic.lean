module

public import AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Basic.Complex.Basic

public section

open scoped Indicator

variable {α : Type*}

namespace Complex

@[simp, norm_cast] lemma ofReal_indicator_one (s : Set α) (x : α) : ↑(𝟭_[s, ℝ] x) = 𝟭_[s, ℂ] x :=
  Set.map_indicator_one ofRealHom ..

@[simp] lemma ofReal_comp_indicator_one (s : Set α) : (↑) ∘ 𝟭_[s, ℝ] = 𝟭_[s, ℂ] := by
  ext; exact ofReal_indicator_one ..

end Complex
