import LeanAPAP.Prereqs.Inner.Hoelder.Discrete
import LeanAPAP.Prereqs.LpNorm.Compact

/-! # Inner product -/

open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat

variable {ι κ 𝕜 : Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}

@[simp] lemma wInner_cWeight_self (f : ι → 𝕜) :
    ⟪f, f⟫ₙ_[𝕜] = ((‖f‖ₙ_[2] : ℝ) : 𝕜) ^ 2 := by
  simp_rw [← algebraMap.coe_pow, ← NNReal.coe_pow]
  simp [cL2Norm_sq_eq_expect_nnnorm, wInner_cWeight_eq_expect]

lemma cL1Norm_mul (f g : ι → 𝕜) : ‖f * g‖ₙ_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫ₙ_[ℝ] := by
  simp [wInner_cWeight_eq_expect, cL1Norm_eq_expect_nnnorm, mul_comm]

/-- **Cauchy-Schwarz inequality** -/
lemma wInner_cWeight_le_cL2Norm_mul_cL2Norm (f g : ι → ℝ) : ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[2] * ‖g‖ₙ_[2] := by
  simp only [wInner_cWeight_eq_smul_wInner_one, cL2Norm_eq_expect_nnnorm, ← NNReal.coe_mul, expect,
    ← NNRat.cast_smul_eq_nnqsmul ℝ≥0, smul_eq_mul, ← NNReal.mul_rpow, mul_mul_mul_comm, ← sq]
  simp only [NNReal.mul_rpow, ← dL2Norm_eq_sum_nnnorm, card_univ]
  rw [← NNReal.rpow_two, NNReal.rpow_rpow_inv two_ne_zero, NNReal.smul_def, smul_eq_mul]
  push_cast
  gcongr
  exact wInner_one_le_dL2Norm_mul_dL2Norm _ _

end RCLike

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma cL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖ₙ_[1] = ⟪f, g⟫ₙ_[ℝ] := by
  convert cL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

/-- **Hölder's inequality**, binary case. -/
lemma wInner_cWeight_le_cLpNorm_mul_cLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  sorry
  -- have hp := hpq.ne_zero
  -- have hq := hpq.symm.ne_zero
  -- norm_cast at hp hq
  -- rw [wInner_cWeight_eq_expect, expect_eq_sum_div_card, cLpNorm_eq_expect_nnnorm hp,
  --   cLpNorm_eq_expect_nnnorm hq, expect_eq_sum_div_card, expect_eq_sum_div_card,
  --   NNReal.div_rpow, NNReal.div_rpow, ← NNReal.coe_mul, div_mul_div_comm, ← NNReal.rpow_add',
  --   hpq.coe.inv_add_inv_conj, NNReal.rpow_one]
  -- swap
  -- · simp [hpq.coe.inv_add_inv_conj]
  -- push_cast
  -- gcongr
  -- rw [← dLpNorm_eq_sum_norm hp, ← dLpNorm_eq_sum_norm hq, ← wInner_one_eq_sum]
  -- exact wInner_one_le_dLpNorm_mul_dLpNorm hpq.coe_ennreal _ _

/-- **Hölder's inequality**, binary case. -/
lemma abs_wInner_cWeight_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    |⟪f, g⟫ₙ_[ℝ]| ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  (abs_wInner_le fun _ ↦ by dsimp; positivity).trans <|
    (wInner_cWeight_le_cLpNorm_mul_cLpNorm p q).trans_eq <| by simp_rw [cLpNorm_abs]

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

lemma norm_wInner_cWeight_le (f g : α → 𝕜) :
    ‖⟪f, g⟫ₙ_[𝕜]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := by
  simpa [wInner_cWeight_eq_expect, norm_mul, mul_comm]
    using norm_expect_le (K := ℝ) (f := fun i ↦ conj (f i) * g i)

/-- **Hölder's inequality**, binary case. -/
lemma nnnorm_wInner_cWeight_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖⟪f, g⟫ₙ_[𝕜]‖₊ ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := norm_wInner_cWeight_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖ₙ_[p] * ‖fun a ↦ ‖g a‖‖ₙ_[q] := wInner_cWeight_le_cLpNorm_mul_cLpNorm _ _
    _ = ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by simp_rw [cLpNorm_norm]

omit [Fintype α]

variable [Finite α]

/-- **Hölder's inequality**, binary case. -/
lemma cLpNorm_mul_le (p q : ℝ≥0∞) (hr₀ : r ≠ 0) [hpqr : ENNReal.HolderTriple p q r] :
    ‖f * g‖ₙ_[r] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  cases nonempty_fintype α
  obtain rfl | p := p
  · sorry
  obtain rfl | q := q
  · sorry
  obtain rfl | r := r
  · sorry
  -- The following two come from `HolderTriple p q r`
  have hp₀ : p ≠ 0 := sorry
  have hq₀ : q ≠ 0 := sorry
  simp only [ENNReal.some_eq_coe] at *
  norm_cast at hr₀
  have : (‖(f * g) ·‖ ^ (r : ℝ)) = (‖f ·‖ ^ (r : ℝ)) * (‖g ·‖ ^ (r : ℝ)) := by ext; simp [mul_rpow]
  rw [cLpNorm_eq_cL1Norm_rpow, NNReal.rpow_inv_le_iff_of_pos, this, ← NNReal.coe_le_coe]
  any_goals positivity
  push_cast
  rw [cL1Norm_mul_of_nonneg, mul_rpow, ← NNReal.coe_rpow, ← NNReal.coe_rpow, cLpNorm_rpow',
    cLpNorm_rpow']
  any_goals intro a; dsimp
  any_goals positivity
  have := hpqr.holderConjugate_div_div _ _ _ (mod_cast hr₀) ENNReal.coe_ne_top
  exact wInner_cWeight_le_cLpNorm_mul_cLpNorm _ _

/-- **Hölder's inequality**, binary case. -/
lemma cL1Norm_mul_le (p q : ℝ≥0∞) [hpq : ENNReal.HolderConjugate p q] :
    ‖f * g‖ₙ_[1] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := cLpNorm_mul_le _ _ one_ne_zero

/-- **Hölder's inequality**, finitary case. -/
lemma cLpNorm_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0)
    (q : ℝ≥0) (hpq : ∑ i ∈ s, ((p i)⁻¹ : ℝ≥0∞) = (q : ℝ≥0∞)⁻¹) (f : ι → α → 𝕜) :
    ‖∏ i ∈ s, f i‖ₙ_[q] ≤ ∏ i ∈ s, ‖f i‖ₙ_[p i] := by
  induction hs using Finset.Nonempty.cons_induction generalizing q with
  | singleton => simp_all
  | cons i s hi hs ih =>
  simp_rw [prod_cons]
  rw [sum_cons, ← inv_inv (∑ _ ∈ _, _)] at hpq
  have : ENNReal.HolderTriple (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹ q := ⟨sorry⟩
  grw [cLpNorm_mul_le (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹ , ih]
  · rw [← ENNReal.coe_inv, inv_inv]
    · push_cast
      congr! with i
      exact (ENNReal.coe_inv <| hp _).symm
    · simpa [hp]
  · norm_cast
    rintro rfl
    simp [hp] at hpq

end Hoelder
end MeasureTheory
