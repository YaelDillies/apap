module

public import APAP.Prereqs.LpNorm.Compact
public import Mathlib.Analysis.RCLike.Inner

import APAP.Prereqs.Inner.Hoelder.Discrete
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity

/-! # Inner product -/

public section

open Finset hiding card
open Fintype (card)
open Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat

variable {ι κ 𝕜 : Type*} [Fintype ι]

namespace RCLike
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}

@[simp] lemma wInner_cWeight_self (f : ι → 𝕜) :
    ⟪f, f⟫ₙ_[𝕜] = ((‖f‖ₙ_[2] : ℝ) : 𝕜) ^ 2 := by
  simp_rw [← algebraMap.coe_pow]
  simp [cL2Norm_sq_eq_expect_norm, wInner_cWeight_eq_expect]

set_option backward.isDefEq.respectTransparency false in
lemma cL1Norm_mul (f g : ι → 𝕜) : ‖f * g‖ₙ_[1] = ⟪fun i ↦ ‖f i‖, fun i ↦ ‖g i‖⟫ₙ_[ℝ] := by
  simp [wInner_cWeight_eq_expect, cL1Norm_eq_expect_norm, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- **Cauchy-Schwarz inequality** -/
lemma wInner_cWeight_le_cL2Norm_mul_cL2Norm (f g : ι → ℝ) : ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[2] * ‖g‖ₙ_[2] := by
  simp only [wInner_cWeight_eq_smul_wInner_one, ← NNRat.cast_smul_eq_nnqsmul ℝ≥0, NNRat.cast_inv,
    NNRat.cast_natCast, NNReal.smul_def, NNReal.coe_inv, NNReal.coe_natCast, smul_eq_mul,
    cL2Norm_eq_expect_norm, expect, card_univ, norm_eq_abs, sq_abs]
  rw [mul_rpow, mul_rpow, mul_mul_mul_comm, ← sq, ← rpow_two, rpow_inv_rpow]
  any_goals positivity
  gcongr
  simpa [dL2Norm_eq_sum_norm] using wInner_one_le_dL2Norm_mul_dL2Norm f g

end RCLike

/-! ### Hölder inequality -/

namespace MeasureTheory

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

omit [Fintype α]
variable [Finite α]

/-- **Hölder's inequality**, binary case. -/
lemma cLpNorm_mul_le (p q : ℝ≥0∞) (_hr₀ : r ≠ 0) [hpqr : ENNReal.HolderTriple p q r] :
    ‖f * g‖ₙ_[r] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  cases nonempty_fintype α
  set μ := ProbabilityTheory.uniformOn (Set.univ : Set α) with hμ_def
  have hμfin : IsFiniteMeasure μ := by rw [hμ_def]; infer_instance
  have hm_r : MemLp (f * g) r μ := MemLp.of_discrete
  have hm_p : MemLp f p μ := MemLp.of_discrete
  have hm_q : MemLp g q μ := MemLp.of_discrete
  have hbd : ∀ᵐ x ∂μ, ‖f x * g x‖₊ ≤ (1 : NNReal) * ‖f x‖₊ * ‖g x‖₊ :=
    .of_forall fun x ↦ by rw [one_mul]; exact nnnorm_mul_le _ _
  have key : eLpNorm (fun x ↦ f x * g x) r μ
      ≤ ((1 : NNReal) : ℝ≥0∞) * eLpNorm f p μ * eLpNorm g q μ :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := p) (q := q) (r := r)
      hm_p.aestronglyMeasurable hm_q.aestronglyMeasurable (· * ·) 1 hbd
  change lpNorm _ _ μ ≤ lpNorm _ _ μ * lpNorm _ _ μ
  rw [← toReal_eLpNorm hm_r.aestronglyMeasurable,
      ← toReal_eLpNorm hm_p.aestronglyMeasurable,
      ← toReal_eLpNorm hm_q.aestronglyMeasurable,
      ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · exact ENNReal.mul_ne_top hm_p.eLpNorm_ne_top hm_q.eLpNorm_ne_top
  · simpa using key

end Hoelder

section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma cL1Norm_mul_of_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f * g‖ₙ_[1] = ⟪f, g⟫ₙ_[ℝ] := by
  convert cL1Norm_mul f g using 2 <;> ext a <;> refine (norm_of_nonneg ?_).symm; exacts [hf _, hg _]

/-- **Hölder's inequality**, binary case. -/
lemma wInner_cWeight_le_cLpNorm_mul_cLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ⟪f, g⟫ₙ_[ℝ] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  -- Step 1: `⟪f, g⟫ₙ_[ℝ] ≤ ⟪|f|, |g|⟫ₙ_[ℝ]` (dominate by absolute value)
  have h_abs : ⟪f, g⟫ₙ_[ℝ] ≤ ⟪fun i ↦ |f i|, fun i ↦ |g i|⟫ₙ_[ℝ] := by
    simp_rw [wInner_cWeight_eq_expect]
    refine expect_le_expect fun i _ ↦ ?_
    exact (le_abs_self _).trans (abs_mul _ _).le
  refine h_abs.trans ?_
  -- Step 2: Now both arguments are nonneg; the target becomes the Hölder inequality
  -- `⟪|f|, |g|⟫ₙ_[ℝ] ≤ ‖|f|‖ₙ_[p] * ‖|g|‖ₙ_[q]` which we rewrite back to f, g using
  -- `cLpNorm_abs` / `cLpNorm_fun_abs`.
  have hfabs : ‖fun i ↦ |f i|‖ₙ_[p] = ‖f‖ₙ_[p] := by
    simpa using cLpNorm_fun_abs (f := f) (p := p) .of_discrete
  have hgabs : ‖fun i ↦ |g i|‖ₙ_[q] = ‖g‖ₙ_[q] := by
    simpa using cLpNorm_fun_abs (f := g) (p := q) .of_discrete
  rw [← hfabs, ← hgabs]
  rw [show ⟪fun i ↦ |f i|, fun i ↦ |g i|⟫ₙ_[ℝ]
        = ‖(fun i ↦ |f i|) * (fun i ↦ |g i|)‖ₙ_[1] from
        (cL1Norm_mul_of_nonneg (f := fun i ↦ |f i|) (g := fun i ↦ |g i|)
          (fun i ↦ abs_nonneg _) (fun i ↦ abs_nonneg _)).symm]
  exact cLpNorm_mul_le p q one_ne_zero

/-- **Hölder's inequality**, binary case. -/
lemma abs_wInner_cWeight_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    |⟪f, g⟫ₙ_[ℝ]| ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  (abs_wInner_le fun _ ↦ by dsimp; positivity).trans <|
    (wInner_cWeight_le_cLpNorm_mul_cLpNorm p q).trans_eq <| by simp [cLpNorm_abs .of_discrete]

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

set_option backward.isDefEq.respectTransparency false in
lemma norm_wInner_cWeight_le (f g : α → 𝕜) :
    ‖⟪f, g⟫ₙ_[𝕜]‖₊ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := by
  simpa [wInner_cWeight_eq_expect, norm_mul, mul_comm]
    using norm_expect_le (K := ℝ) (f := fun i ↦ conj (f i) * g i)

/-- **Hölder's inequality**, binary case. -/
lemma norm_wInner_cWeight_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖⟪f, g⟫ₙ_[𝕜]‖₊ ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫ₙ_[ℝ] := norm_wInner_cWeight_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖ₙ_[p] * ‖fun a ↦ ‖g a‖‖ₙ_[q] := wInner_cWeight_le_cLpNorm_mul_cLpNorm _ _
    _ = ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by simp_rw [cLpNorm_norm .of_discrete]

omit [Fintype α]
variable [Finite α]

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
  have : ENNReal.HolderTriple (p i) ↑(∑ i ∈ s, (p i)⁻¹)⁻¹ q := by
    have : (∑ j ∈ s, (p j)⁻¹ : ℝ≥0) ≠ 0 := by simpa [hp]
    constructor
    simpa [ENNReal.coe_inv, *] using hpq
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
