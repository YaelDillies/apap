module

public import APAP.Prereqs.LpNorm.Discrete.Defs
public import Mathlib.Analysis.RCLike.Inner

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Count

/-! # Inner product -/

public section

open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal NNRat

variable {ι 𝕜 S : Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}

@[simp] lemma wInner_one_self {_ : MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f : ι → 𝕜) :
    ⟪f, f⟫_[𝕜] = ((‖f‖_[2] : ℝ) : 𝕜) ^ 2 := by
  simp_rw [← algebraMap.coe_pow]
  simp [dL2Norm_sq_eq_sum_norm, wInner_one_eq_sum]

set_option backward.isDefEq.respectTransparency false in
lemma dL1Norm_mul (f g : ι → 𝕜) : ‖f * g‖_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫_[ℝ] := by
  simp [wInner_one_eq_sum, dL1Norm_eq_sum_norm, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- **Cauchy-Schwarz inequality** -/
lemma wInner_one_le_dL2Norm_mul_dL2Norm (f g : ι → ℝ) : ⟪f, g⟫_[ℝ] ≤ ‖f‖_[2] * ‖g‖_[2] := by
  simpa [dL2Norm_eq_sum_norm, PiLp.norm_eq_of_L2, sqrt_eq_rpow, wInner_one_eq_inner]
    using real_inner_le_norm ((WithLp.equiv 2 _).symm f) _

end RCLike

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0∞}
  {f g : α → ℝ}

lemma dL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖_[1] = ⟪f, g⟫_[ℝ] := by
  convert dL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

/-- **Hölder's inequality**, binary case. -/
lemma wInner_one_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [hpq : p.HolderConjugate q] :
    ⟪f, g⟫_[ℝ] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  have hp0 : p ≠ 0 := ENNReal.HolderConjugate.ne_zero p q
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  have hwInner : ⟪f, g⟫_[ℝ] = ∑ i, f i * g i := by
    rw [wInner_one_eq_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change (inner ℝ (f i) (g i) : ℝ) = f i * g i
    exact mul_comm (g i) (f i)
  have hfg : ∀ i, f i * g i ≤ ‖f i‖ * ‖g i‖ := fun i =>
    (le_abs_self _).trans_eq (by rw [abs_mul]; simp [Real.norm_eq_abs])
  by_cases hpi : p = ∞
  · have hq1 : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one p q).mp hpi
    subst hpi; subst hq1
    rw [hwInner, dLinftyNorm_eq_iSup_norm, dL1Norm_eq_sum_norm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ (hfg i).trans
      (mul_le_mul_of_nonneg_right
        (le_ciSup (f := fun j ↦ ‖f j‖) (Finite.bddAbove_range _) i) (norm_nonneg _))
  by_cases hqi : q = ∞
  · have hp1 : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).mp hqi
    subst hqi; subst hp1
    rw [hwInner, dLinftyNorm_eq_iSup_norm, dL1Norm_eq_sum_norm, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ (hfg i).trans
      (mul_le_mul_of_nonneg_left
        (le_ciSup (f := fun j ↦ ‖g j‖) (Finite.bddAbove_range _) i) (norm_nonneg _))
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpi
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqi
  have hreal : Real.HolderConjugate p.toReal q.toReal := by
    have := ENNReal.HolderTriple.toReal (p := p) (q := q) (r := 1) hpr hqr
    simpa using this
  rw [hwInner, dLpNorm_eq_sum_norm' hp0 hpi, dLpNorm_eq_sum_norm' hq0 hqi]
  have key := Real.inner_le_Lp_mul_Lq Finset.univ f g hreal
  simp only [one_div] at key
  simpa [Real.norm_eq_abs] using key

/-- **Hölder's inequality**, binary case. -/
lemma abs_wInner_one_le_dLpNorm_mul_dLpNorm [p.HolderConjugate q] (f g : α → ℝ) :
    |⟪f, g⟫_[ℝ]| ≤ ‖f‖_[p] * ‖g‖_[q] :=
  (abs_wInner_le zero_le_one).trans <| (wInner_one_le_dLpNorm_mul_dLpNorm p q).trans_eq <| by
    simp_rw [dLpNorm_abs .of_discrete]

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

set_option backward.isDefEq.respectTransparency false in
lemma norm_wInner_one_le (f g : α → 𝕜) : ‖⟪f, g⟫_[𝕜]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] :=
  (norm_sum_le _ _).trans <| by simp [wInner_one_eq_sum]

/-- **Hölder's inequality**, binary case. -/
lemma nnnorm_wInner_one_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖⟪f, g⟫_[𝕜]‖₊ ≤ ‖f‖_[p] * ‖g‖_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] := norm_wInner_one_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖_[p] * ‖fun a ↦ ‖g a‖‖_[q] := wInner_one_le_dLpNorm_mul_dLpNorm _ _
    _ = ‖f‖_[p] * ‖g‖_[q] := by simp_rw [dLpNorm_norm .of_discrete]

omit [Fintype α]
variable [Finite α]

/-- **Hölder's inequality**, binary case. -/
lemma dLpNorm_mul_le (p q : ℝ≥0∞) (_hr₀ : r ≠ 0) [hpqr : ENNReal.HolderTriple p q r] :
    ‖f * g‖_[r] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  cases nonempty_fintype α
  change lpNorm (f * g) r .count ≤ lpNorm f p .count * lpNorm g q .count
  have hf : AEStronglyMeasurable f .count := .of_discrete
  have hg : AEStronglyMeasurable g .count := .of_discrete
  have hfg : AEStronglyMeasurable (f * g) .count := .of_discrete
  rw [← toReal_eLpNorm hf, ← toReal_eLpNorm hg, ← toReal_eLpNorm hfg,
      ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono ?_ ?_
  · exact (ENNReal.mul_lt_top eLpNorm_lt_top_of_finite eLpNorm_lt_top_of_finite).ne
  · have hsmul : (f : α → 𝕜) • g = f * g := rfl
    rw [← hsmul]
    exact eLpNorm_smul_le_mul_eLpNorm hg hf

/-- **Hölder's inequality**, binary case. -/
lemma dL1Norm_mul_le (p q : ℝ≥0∞) [hpq : ENNReal.HolderConjugate p q] :
    ‖f * g‖_[1] ≤ ‖f‖_[p] * ‖g‖_[q] := dLpNorm_mul_le _ _ one_ne_zero

/-- **Hölder's inequality**, finitary case. -/
lemma dLpNorm_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {p : ι → ℝ≥0} (hp : ∀ i, p i ≠ 0)
    (q : ℝ≥0) (hpq : ∑ i ∈ s, ((p i)⁻¹ : ℝ≥0∞) = (q : ℝ≥0∞)⁻¹) (f : ι → α → 𝕜) :
    ‖∏ i ∈ s, f i‖_[q] ≤ ∏ i ∈ s, ‖f i‖_[p i] := by
  induction s using Finset.cons_induction generalizing q with
  | empty => cases not_nonempty_empty hs
  | cons i s hi ih =>
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp only [sum_cons, sum_empty, add_zero, inv_inj] at hpq
      simp [← hpq]
    simp_rw [prod_cons]
    rw [sum_cons, ← inv_inv (∑ _ ∈ _, _)] at hpq
    have : ENNReal.HolderTriple (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹ q := ⟨by
      simpa [ENNReal.coe_inv (by simpa [hp] :
        (∑ j ∈ s, (p j)⁻¹ : ℝ≥0) ≠ 0), ENNReal.coe_inv, hp] using hpq⟩
    grw [dLpNorm_mul_le (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹, ih hs]
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
