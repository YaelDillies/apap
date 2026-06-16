module

public import APAP.Prereqs.Convolution.Discrete.Defs
public import APAP.Prereqs.LpNorm.Discrete.Defs
public import Mathlib.Analysis.RCLike.Inner

import APAP.Prereqs.LpNorm.Discrete.Basic
import Mathlib.Algebra.Order.Star.Conjneg
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity

/-!
# Norm of a convolution

This file characterises the L1-norm of the convolution of two functions and proves the Young
convolution inequality.
-/

@[expose] public section

open Finset Function MeasureTheory RCLike Real
open scoped ComplexConjugate ENNReal NNReal Pointwise translate

variable {G 𝕜 : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section RCLike
variable [RCLike 𝕜] {p : ℝ≥0∞}

lemma ddconv_eq_wInner_one (f g : G → 𝕜) (a : G) :
    (f ∗ᵈ g) a = ⟪conj f, τ a fun x ↦ g (-x)⟫_[𝕜] := by
  simp [wInner_one_eq_sum, ddconv_eq_sum_sub', mul_comm]

lemma dddconv_eq_wInner_one (f g : G → 𝕜) (a : G) : (f ○ᵈ g) a = conj ⟪f, τ a g⟫_[𝕜] := by
  simp [wInner_one_eq_sum, dddconv_eq_sum_sub', map_sum, mul_comm]

lemma wInner_one_dddconv (f g h : G → 𝕜) : ⟪f, g ○ᵈ h⟫_[𝕜] = ⟪conj g, conj f ∗ᵈ conj h⟫_[𝕜] := by
  calc
    _ = ∑ b, ∑ a, g a * conj (h b) * conj (f (a - b)) := by
      simp_rw [wInner_one_eq_sum, RCLike.inner_apply, sum_dddconv_mul]
      exact sum_comm
    _ = ∑ b, ∑ a, conj (f a) * conj (h b) * g (a + b) := by
      simp_rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv ((Equiv.refl _).prodShear Equiv.subRight) _ _
        (by simp [mul_rotate, mul_right_comm])
    _ = _ := by
      simp_rw [wInner_one_eq_sum, RCLike.inner_apply, sum_ddconv_mul, Pi.conj_apply,
        RCLike.conj_conj]
      exact sum_comm

lemma wInner_one_ddconv (f g h : G → 𝕜) : ⟪f, g ∗ᵈ h⟫_[𝕜] = ⟪conj g, conj f ○ᵈ conj h⟫_[𝕜] := by
  simp_rw [wInner_one_dddconv, RCLike.conj_conj]

lemma dddconv_wInner_one (f g h : G → 𝕜) : ⟪f ○ᵈ g, h⟫_[𝕜] = ⟪conj h ∗ᵈ conj g, conj f⟫_[𝕜] := by
  rw [← conj_wInner_symm, wInner_one_dddconv, conj_wInner_symm]

lemma ddconv_wInner_one (f g h : G → 𝕜) : ⟪f ∗ᵈ g, h⟫_[𝕜] = ⟪conj h ○ᵈ conj g, conj f⟫_[𝕜] := by
  rw [← conj_wInner_symm, wInner_one_ddconv, conj_wInner_symm]

lemma dddconv_wInner_one_eq_wInner_one_ddconv (f g h : G → 𝕜) :
    ⟪f ○ᵈ g, h⟫_[𝕜] = ⟪f, h ∗ᵈ g⟫_[𝕜] := by
  rw [dddconv_wInner_one]; simp [wInner_one_eq_sum, mul_comm]

lemma wInner_one_dddconv_eq_ddconv_wInner_one (f g h : G → 𝕜) :
    ⟪f, h ○ᵈ g⟫_[𝕜] = ⟪f ∗ᵈ g, h⟫_[𝕜] := by
  rw [wInner_one_dddconv]; simp [wInner_one_eq_sum, mul_comm]

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

omit [Fintype G] in
@[simp] lemma dLpNorm_trivChar [Finite G] (hp : p ≠ 0) : ‖(trivChar : G → 𝕜)‖_[p] = 1 := by
  cases nonempty_fintype G
  obtain _ | p := p
  · simp only [ENNReal.none_eq_top, dLinftyNorm_eq_iSup_norm, trivChar_apply, apply_ite,
      norm_one, norm_zero]
    exact IsLUB.ciSup_eq ⟨by aesop (add simp mem_upperBounds), fun x hx ↦ hx ⟨0, if_pos rfl⟩⟩
  · simp at hp
    simp [dLpNorm_eq_sum_norm hp, apply_ite, hp]

/-- A special case of **Young's convolution inequality**. -/
lemma dLpNorm_ddconv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : G → 𝕜) :
    ‖f ∗ᵈ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] := by
  obtain rfl | hp := hp.eq_or_lt
  · simp_rw [ENNReal.coe_one, dL1Norm_eq_sum_norm, sum_mul_sum, ddconv_eq_sum_sub']
    calc
      ∑ x, ‖∑ y, f y * g (x - y)‖ ≤ ∑ x, ∑ y, ‖f y * g (x - y)‖ :=
        sum_le_sum fun x _ ↦ norm_sum_le _ _
      _ = _ := ?_
    rw [sum_comm]
    simp_rw [norm_mul]
    exact sum_congr rfl fun x _ ↦ Fintype.sum_equiv (Equiv.subRight x) _ _ fun _ ↦ rfl
  have hp₀ := zero_lt_one.trans hp
  rw [← rpow_le_rpow_iff _ _ hp₀, mul_rpow]
  any_goals positivity
  dsimp
  simp_rw [dLpNorm_rpow_eq_sum_norm hp₀.ne', ddconv_eq_sum_sub']
  have hpconj : (p : ℝ).HolderConjugate (1 - (p : ℝ)⁻¹)⁻¹ :=
    ⟨by simp, mod_cast hp₀, by bound⟩
  have (x : G) : ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
      (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ) := by
    rw [← le_rpow_inv_iff_of_pos, mul_rpow, ← rpow_mul, sub_one_mul, mul_inv_cancel₀]
    any_goals positivity
    calc
      _ ≤ ∑ y, ‖f y * g (x - y)‖ := norm_sum_le _ _
      _ = ∑ y, ‖f y‖ * ‖g (x - y)‖ ^ (p : ℝ)⁻¹ * ‖g (x - y)‖ ^ (1 - (p : ℝ)⁻¹) := ?_
      _ ≤ _ := inner_le_Lp_mul_Lq _ _ _ hpconj
      _ = _ := ?_
    · congr with t
      rw [norm_mul, mul_assoc, ← rpow_add' (by positivity), add_sub_cancel, rpow_one]
      simp
    · have : 1 - (p : ℝ)⁻¹ ≠ 0 := sub_ne_zero.2 (inv_ne_one.2 <| NNReal.coe_ne_one.2 hp.ne').symm
      simp [mul_rpow, rpow_nonneg, hp₀.ne', this, abs_rpow_of_nonneg]
  calc
    ∑ x, ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
        ∑ x, (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ) :=
      sum_le_sum fun i _ ↦ this _
    _ = _ := ?_
  have hg : ∀ x, ∑ y, ‖g (x - y)‖ = ‖g‖_[1] := by
    simp_rw [dL1Norm_eq_sum_norm]
    exact fun x ↦ Fintype.sum_equiv (Equiv.subLeft _) _ _ fun _ ↦ rfl
  have hg' : ∀ y, ∑ x, ‖g (x - y)‖ = ‖g‖_[1] := by
    simp_rw [dL1Norm_eq_sum_norm]
    exact fun x ↦ Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl
  simp_rw [hg]
  rw [← sum_mul, sum_comm]
  simp_rw [← mul_sum, hg']
  rw [← sum_mul, mul_assoc, ← rpow_one_add' (by positivity), add_sub_cancel]
  rw [add_sub_cancel]
  positivity

/-- A special case of **Young's convolution inequality**. -/
lemma dLpNorm_dddconv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : G → 𝕜) :
     ‖f ○ᵈ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] := by
  simpa only [ddconv_conjneg, dLpNorm_conjneg] using dLpNorm_ddconv_le hp f (conjneg g)

end RCLike

section Real
variable [MeasurableSpace G] [DiscreteMeasurableSpace G] {f g : G → ℝ} {n : ℕ}

--TODO: Include `f : G → ℂ`
lemma dL1Norm_ddconv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ∗ᵈ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] := by
  have : ∀ x, 0 ≤ ∑ y, f y * g (x - y) := fun x ↦ sum_nonneg fun y _ ↦ mul_nonneg (hf _) (hg _)
  simp [dL1Norm_eq_sum_norm, ← sum_ddconv, ddconv_eq_sum_sub', norm_of_nonneg (this _),
    norm_of_nonneg (hf _), norm_of_nonneg (hg _)]

lemma dL1Norm_dddconv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ○ᵈ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] := by
  simpa using dL1Norm_ddconv hf (conjneg_nonneg.2 hg)

end Real
