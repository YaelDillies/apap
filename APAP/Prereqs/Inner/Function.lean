import APAP.Prereqs.Function.Indicator.Defs
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.RCLike.Inner

open Finset RCLike
open scoped BigOperators ComplexConjugate mu

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

lemma indicate_wInner_one (s : Finset ι) (f : ι → 𝕜) : ⟪𝟭 s, f⟫_[𝕜] = ∑ i ∈ s, f i := by
  simp [wInner_one_eq_sum, indicate_apply]

lemma wInner_one_indicate (f : ι → 𝕜) (s : Finset ι) : ⟪f, 𝟭 s⟫_[𝕜] = ∑ i ∈ s, conj (f i) := by
  simp [wInner_one_eq_sum, indicate_apply]

lemma mu_wInner_one (s : Finset ι) (f : ι → 𝕜) : ⟪μ s, f⟫_[𝕜] = 𝔼 i ∈ s, f i := by
  simp [wInner_one_eq_sum]; simp [mu_apply, expect_eq_sum_div_card, sum_mul, div_eq_mul_inv]

lemma wInner_one_mu (f : ι → 𝕜) (s : Finset ι) : ⟪f, μ s⟫_[𝕜] = 𝔼 i ∈ s, conj (f i) := by
  simp [wInner_one_eq_sum, mu_apply, expect_eq_sum_div_card, mul_sum, div_eq_inv_mul]
