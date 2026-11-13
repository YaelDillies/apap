module

public import AddCombi.Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Star.Conjneg

public section

open scoped ComplexConjugate Indicator Pointwise

variable {G R : Type*}

section CommSemiring
variable [CommSemiring R] [StarRing R] [AddCommGroup G]

@[simp] lemma conjneg_indicator_one (s : Set G) : conjneg 𝟭_[s, R] = 𝟭_[-s] := by
  classical ext; simp [Set.indicator_apply]

end CommSemiring
