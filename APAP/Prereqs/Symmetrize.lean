module

public import Mathlib.Probability.IdentDistrib

import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Positivity.Finset

open Finset Fintype Function Nat MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

@[expose] public section

variable {ι Ω E : Type*} {A : Finset ι} {m : ℕ} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {X : ι → Ω → E}

def symmetrize [DecidableEq ι] (A : Finset ι) (X : ι → Ω → E) (i : ι) : Ω × Ω → E :=
  if i ∈ A then (X i ∘ Prod.fst - X i ∘ Prod.snd) else 0

omit [InnerProductSpace ℝ E] [MeasurableSpace E] in
lemma memLp_symmetrize [DecidableEq ι] [IsProbabilityMeasure μ]
    (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) (i : ι)
    (hi : i ∈ A) : MemLp (symmetrize A X i) (2 * m) (μ.prod μ) := by
  simp only [symmetrize, if_pos hi]
  exact ((h_lp i hi).comp_measurePreserving measurePreserving_fst).sub
    ((h_lp i hi).comp_measurePreserving measurePreserving_snd)

omit [MeasurableSpace Ω] [IsFiniteMeasure μ] [MeasurableSpace E] [InnerProductSpace ℝ E] in
lemma symmetrize_le_norm_pow [DecidableEq ι] (ω : Ω × Ω) :
    (∑ i ∈ A, ‖symmetrize A X i ω‖ ^ 2) ^ m ≤
      2 ^ (2 * m - 1) * ((∑ i ∈ A, ‖X i ω.1‖ ^ 2) ^ m + (∑ i ∈ A, ‖X i ω.2‖ ^ 2) ^ m) := by
  have h_le i (hi : i ∈ A) : ‖symmetrize A X i ω‖ ^ 2 ≤ 2 * (‖X i ω.1‖ ^ 2 + ‖X i ω.2‖ ^ 2) := by
    calc
      ‖symmetrize A X i ω‖ ^ 2
        ≤ (‖X i ω.1‖ + ‖X i ω.2‖) ^ 2 := by
          gcongr
          dsimp [symmetrize]
          rw [if_pos hi]
          exact norm_sub_le _ _
      _ ≤ 2 * (‖X i ω.1‖ ^ 2 + ‖X i ω.2‖ ^ 2) := add_sq_le
  calc
    (∑ i ∈ A, ‖symmetrize A X i ω‖ ^ 2) ^ m
    _ ≤ (2 * ((∑ i ∈ A, ‖X i ω.1‖ ^ 2) + ∑ i ∈ A, ‖X i ω.2‖ ^ 2)) ^ m := by
        gcongr
        rw [← sum_add_distrib, mul_sum]
        exact sum_le_sum fun i hi ↦ h_le i hi
    _ = 2 ^ m * ((∑ i ∈ A, ‖X i ω.1‖ ^ 2) + ∑ i ∈ A, ‖X i ω.2‖ ^ 2) ^ m := mul_pow ..
    _ ≤ 2 ^ m * (2 ^ (m - 1) *
        ((∑ i ∈ A, ‖X i ω.1‖ ^ 2) ^ m + (∑ i ∈ A, ‖X i ω.2‖ ^ 2) ^ m)) := by
        gcongr
        exact add_pow_le (by positivity) (by positivity) m
    _ = 2 ^ (2 * m - 1) * ((∑ i ∈ A, ‖X i ω.1‖ ^ 2) ^ m + (∑ i ∈ A, ‖X i ω.2‖ ^ 2) ^ m) := by
      rw [← mul_assoc, ← pow_add]
      grind

omit [IsFiniteMeasure μ] in
lemma norm_pow_le_integral_norm_sub_pow [IsProbabilityMeasure μ] [SecondCountableTopology E]
    [BorelSpace E] [CompleteSpace E] {S : Ω → E} (h_mem_lp_s : MemLp S ↑(2 * m) μ)
    (h_zero : ∫ ω, S ω ∂μ = 0) (hm : m ≠ 0) (ω₁ : Ω) :
    ‖S ω₁‖ ^ (2 * m) ≤ ∫ ω₂, ‖S ω₁ - S ω₂‖ ^ (2 * m) ∂μ := by
  have h_int_s : Integrable S μ := h_mem_lp_s.integrable (by
    norm_cast
    lia)
  have h_int_g : Integrable (fun ω₂ ↦ S ω₁ - S ω₂) μ := (integrable_const _).sub h_int_s
  have h_int_g_pow : Integrable (fun ω₂ ↦ ‖S ω₁ - S ω₂‖ ^ (2 * m)) μ :=
    ((memLp_const _).sub h_mem_lp_s).integrable_norm_pow (by lia)
  calc
    ‖S ω₁‖ ^ (2 * m) = ‖∫ ω₂, (S ω₁ - S ω₂) ∂μ‖ ^ (2 * m) := by
      rw [integral_sub (integrable_const _) h_int_s, h_zero, sub_zero, integral_const]
      simp
    _ = ‖∫ ω₂, (S ω₁ - S ω₂) ∂μ‖ ^ (2 * m) := rfl
    _ ≤ (∫ ω₂, ‖S ω₁ - S ω₂‖ ∂μ) ^ (2 * m) := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ ≤ ∫ ω₂, ‖S ω₁ - S ω₂‖ ^ (2 * m) ∂μ := by
      simpa using (convexOn_pow (2 * m)).map_integral_le
        (continuous_pow _).continuousOn isClosed_Ici
        (ae_of_all _ fun ω₂ ↦ Set.mem_Ici.2 (norm_nonneg _))
        h_int_g.norm h_int_g_pow

omit [IsFiniteMeasure μ] in
lemma symmetrize_inequality [DecidableEq ι] [SecondCountableTopology E] [BorelSpace E]
    [CompleteSpace E]
    (h_indep : iIndepFun X μ) (h_int : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_lp : ∀ i ∈ A, MemLp (X i) (2 * m) μ) (hm : m ≠ 0) :
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ ≤
      ∫ ω, ‖∑ i ∈ A, symmetrize A X i ω‖ ^ (2 * m) ∂μ.prod μ := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have h_eq : (2 * (m : ℝ≥0∞)) = ↑(2 * m) := by simp
  have h_mem_lp_s : MemLp (fun ω ↦ ∑ i ∈ A, X i ω) ↑(2 * m) μ :=
    h_eq ▸ memLp_finsetSum A h_lp
  have h_int_ss_pow : Integrable (fun ω : Ω × Ω ↦ ‖(∑ i ∈ A, X i ω.1) - ∑ i ∈ A, X i ω.2‖ ^ (2 * m))
      (μ.prod μ) := by
    have : 2 * m ≠ 0 := by lia
    exact ((h_mem_lp_s.comp_measurePreserving measurePreserving_fst).sub
      (h_mem_lp_s.comp_measurePreserving measurePreserving_snd)).integrable_norm_pow this
  have h_int_X (i : ι) (hi : i ∈ A) : Integrable (X i) μ := by
    have : 1 ≤ (2 * m : ℝ≥0∞) := by
      norm_cast
      lia
    exact (h_lp i hi).integrable this
  have h_zero : ∫ ω, ∑ i ∈ A, X i ω ∂μ = 0 := by
    rw [integral_finsetSum _ h_int_X]
    simp [h_int]
  have sum_symmetrize (ω : Ω × Ω) :
      ∑ i ∈ A, symmetrize A X i ω = (∑ i ∈ A, X i ω.1) - ∑ i ∈ A, X i ω.2 := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i hi ↦ by simp [symmetrize, hi]
  simp_rw [sum_symmetrize]
  calc
    ∫ ω, ‖∑ i ∈ A, X i ω‖ ^ (2 * m) ∂μ
      ≤ ∫ ω₁, ∫ ω₂, ‖(∑ i ∈ A, X i ω₁) - (∑ i ∈ A, X i ω₂)‖ ^ (2 * m) ∂μ ∂μ :=
        integral_mono (h_mem_lp_s.integrable_norm_pow (by lia))
          h_int_ss_pow.integral_prod_left (norm_pow_le_integral_norm_sub_pow h_mem_lp_s h_zero hm)
    _ = ∫ ω, ‖(∑ i ∈ A, X i ω.1) - (∑ i ∈ A, X i ω.2)‖ ^ (2 * m) ∂(μ.prod μ) :=
        integral_integral
          (f := fun ω₁ ω₂ ↦ ‖(∑ i ∈ A, X i ω₁) - (∑ i ∈ A, X i ω₂)‖ ^ (2 * m)) h_int_ss_pow
