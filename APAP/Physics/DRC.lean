module

public import APAP.Prereqs.Convolution.Discrete.Defs
public import APAP.Prereqs.LpNorm.Weighted
public import APAP.Prereqs.Mu
public import Mathlib.Analysis.RCLike.Inner

import AddCombi.Mathlib.Algebra.BigOperators.Ring.Finset
import AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
import AddCombi.Mathlib.Algebra.Order.GroupWithZero.Indicator
import APAP.Mathlib.Algebra.BigOperators.Pi
import APAP.Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import APAP.Mathlib.Algebra.Group.Translate
import APAP.Prereqs.Convolution.Discrete.Basic
import APAP.Prereqs.Convolution.Norm
import APAP.Prereqs.Convolution.Order
import APAP.Prereqs.LpNorm.Discrete.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity

/-!
# Dependent Random Choice
-/

public section

open Finset Fintype Function MeasureTheory RCLike Real
open scoped ENNReal NNReal Indicator Pointwise mu

variable {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G] {p : ℕ} {B₁ B₂ A : Finset G}
  {ε δ : ℝ}

/-- Auxiliary definition for the Dependent Random Choice step. We intersect `B₁` and `B₂` with
`c p A s` for some `s`. -/
private def c (p : ℕ) (A : Finset G) (s : Fin p → G) : Finset G := univ.inf fun i ↦ s i +ᵥ A

set_option backward.isDefEq.respectTransparency false in
private lemma lemma_0 (p : ℕ) (B₁ B₂ A : Finset G) (f : G → ℝ) :
    ∑ s, ⟪𝟭_[↑(B₁ ∩ c p A s), ℝ] ○ᵈ 𝟭_[↑(B₂ ∩ c p A s)], f⟫_[ℝ] =
      (#B₁ * #B₂) • ∑ x, (μ_[ℝ] B₁ ○ᵈ μ B₂) x * (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p * f x := by
  simp_rw [mul_assoc]
  simp only [wInner_one_eq_sum, inner_apply', RCLike.conj_to_real, mul_sum, sum_mul, smul_sum,
    @sum_comm _ _ (Fin p → G), sum_dddconv_mul, dddconv_apply_sub, Fintype.sum_pow,
    Set.map_indicator_one]
  congr with b₁
  congr with b₂
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun s ↦ ?_
  rw [← smul_mul_assoc, mul_smul_mul_comm, card_smul_mu_apply, card_smul_mu_apply,
    coe_inter, coe_inter, Set.indicator_one_inter_apply, Set.indicator_one_inter_apply,
    mul_mul_mul_comm, prod_mul_distrib]
  simp [c, indicator_one_inf_apply, sub_eq_add_neg, mul_assoc, add_comm]

private lemma sum_c (p : ℕ) (B A : Finset G) : ∑ s, #(B ∩ c p A s) = #A ^ p * #B := by
  simp only [card_eq_sum_indicator_one, Set.indicator_one_inter_apply, c, indicator_one_inf_apply,
    mul_sum, sum_mul, coe_inter, coe_vadd_finset, sum_pow', @sum_comm G, Fintype.piFinset_univ,
    ← translate_indicator_one, translate_apply]
  congr with x
  exact Fintype.sum_equiv (Equiv.subLeft fun _ ↦ x) _ _ fun s ↦ mul_comm _ _

private lemma sum_cast_c (p : ℕ) (B A : Finset G) :
    ∑ s, (#(B ∩ c p A s) : ℝ) = #A ^ p * #B := by
  rw [← Nat.cast_sum, sum_c]; norm_cast

variable [MeasurableSpace G]

noncomputable def s (p : ℝ≥0) (ε : ℝ) (B₁ B₂ A : Finset G) : Finset G :=
  {x | (1 - ε) * ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] < (𝟭_[A] ○ᵈ 𝟭_[A]) x}

@[simp]
lemma mem_s {p : ℝ≥0} {ε : ℝ} {B₁ B₂ A : Finset G} {x : G} :
    x ∈ s p ε B₁ B₂ A ↔
      (1 - ε) * ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] < (𝟭_[A] ○ᵈ 𝟭_[A]) x := by simp [s]

lemma mem_s' {p : ℝ≥0} {ε : ℝ} {B₁ B₂ A : Finset G} {x : G} :
    x ∈ s p ε B₁ B₂ A ↔ (1 - ε) * ‖μ_[ℝ] A ○ᵈ μ A‖_[p, μ B₁ ○ᵈ μ B₂] < (μ A ○ᵈ μ A) x := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · simp [← card_smul_mu, -nsmul_eq_mul, smul_dddconv, dddconv_smul, wLpNorm_nsmul, hA.card_pos]

variable [DiscreteMeasurableSpace G]

set_option backward.isDefEq.respectTransparency false in
/-- If `A` is nonempty, and `B₁` and `B₂` intersect, then the `μ B₁ ○ᵈ μ B₂`-weighted Lp norm of
`𝟭_[A] ○ᵈ 𝟭_[A]` is positive. -/
private lemma dLpNorm_ddconv_pos (hp : p ≠ 0) (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    (0 : ℝ) < ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
  rw [wLpNorm_pow_eq_sum_norm (by positivity)]
  refine sum_pos' (fun x _ ↦ by positivity) ⟨0, mem_univ _, smul_pos ?_ <| pow_pos ?_ _⟩
  · rwa [pos_iff_ne_zero, ← Function.mem_support, support_dddconv, support_mu, support_mu,
      ← coe_sub, mem_coe, zero_mem_sub_iff, not_disjoint_iff_nonempty_inter] <;> exact mu_nonneg
  · rw [norm_pos_iff, ← Function.mem_support, support_dddconv, Set.support_indicator_one]
    any_goals exact Set.indicator_one_nonneg -- positivity
    exact hA.to_set.zero_mem_sub

set_option backward.isDefEq.respectTransparency false in
lemma drc (hp₂ : 2 ≤ p) (f : G → ℝ≥0) (hf : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∈ f.support)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧
      ⟪μ_[ℝ] A₁ ○ᵈ μ A₂, (↑) ∘ f⟫_[ℝ] * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p
        ≤ 2 * ∑ x, (μ B₁ ○ᵈ μ B₂) x * (𝟭_[A, ℝ] ○ᵈ 𝟭_[A]) x ^ p * f x ∧
      (4 : ℝ) ⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p)
        ≤ #A₁ / #B₁ ∧
      (4 : ℝ) ⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p)
        ≤ #A₂ / #B₂ := by
  have := hB.mono inter_subset_left
  have := hB.mono inter_subset_right
  have hp₀ : p ≠ 0 := by positivity
  have := dLpNorm_ddconv_pos hp₀ hB hA
  set M : ℝ :=
    2 ⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p * (sqrt #B₁ * sqrt #B₂) / #A ^ p
      with hM_def
  have hM : 0 < M := by rw [hM_def]; positivity
  replace hf : 0 < ∑ x, (μ_[ℝ] B₁ ○ᵈ μ B₂) x * (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p * f x := by
    have : 0 ≤ μ_[ℝ] B₁ ○ᵈ μ B₂ * (𝟭_[A] ○ᵈ 𝟭_[A]) ^ p * (↑) ∘ f := -- positivity
      mul_nonneg (mul_nonneg (dddconv_nonneg mu_nonneg mu_nonneg) <| pow_nonneg
        (dddconv_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg) _) fun _ ↦ by simp
    refine Fintype.sum_pos <| this.lt_iff_ne'.2 <| support_nonempty_iff.1 ?_
    simp only [support_comp_eq, Set.Nonempty, and_assoc, support_mul', support_dddconv,
      Set.indicator_one_nonneg, mu_nonneg, Set.support_indicator_one, support_mu,
      NNReal.coe_eq_zero,iff_self, forall_const, Set.mem_inter_iff, ← coe_sub, mem_coe,
      support_pow' _ hp₀, hf]
  set A₁ := fun s ↦ B₁ ∩ c p A s
  set A₂ := fun s ↦ B₂ ∩ c p A s
  set g : (Fin p → G) → ℝ := fun s ↦ #(A₁ s) * #(A₂ s) with hg_def
  have hg : ∀ s, 0 ≤ g s := fun s ↦ by rw [hg_def]; dsimp; positivity
  have hgB : ∑ s, g s = #B₁ * #B₂ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
    have hAdddconv : 0 ≤ 𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A] :=
      dddconv_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg
    simpa only [wLpNorm_pow_eq_sum_norm hp₀, norm_of_nonneg (hAdddconv _), NNReal.smul_def,
      NNReal.coe_dddconv, NNReal.coe_comp_mu, wInner_one_eq_sum, Pi.one_apply, inner_apply',
      ← coe_inter, conj_to_real, mul_one, sum_dddconv, sum_indicator_one, nsmul_eq_mul,
      Nat.cast_mul, g, A₁, A₂] using! lemma_0 p B₁ B₂ A 1
  suffices ∑ s, ⟪𝟭_[A₁ s, ℝ] ○ᵈ 𝟭_[A₂ s], (↑) ∘ f⟫_[ℝ] * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p
    < ∑ s, 𝟭_[({s | M ^ 2 ≤ g s} : Finset _)] s * g s *
        (2 * ∑ x, (μ B₁ ○ᵈ μ B₂) x * (𝟭_[A, ℝ] ○ᵈ 𝟭_[A]) x ^ p * f x) by
    obtain ⟨s, -, hs⟩ := exists_lt_of_sum_lt this
    refine ⟨_, inter_subset_left (s₂ := c p A s), _, inter_subset_left (s₂ := c p A s), ?_⟩
    simp only [Set.indicator_apply, boole_mul] at hs
    split_ifs at hs with h; swap
    · simp only [zero_mul, wInner_one_eq_sum, Function.comp_apply, RCLike.inner_apply',
        RCLike.conj_to_real] at hs
      have : 0 ≤ 𝟭_[(A₁ s : Set G), ℝ] ○ᵈ 𝟭_[A₂ s] :=
        dddconv_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg
      -- positivity
      cases hs.not_ge <|
        mul_nonneg (sum_nonneg fun x _ ↦ mul_nonneg (this _) <| by positivity) <| by positivity
    have : (4 : ℝ) ⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p)
      ≤ #(A₁ s) / #B₁ * (#(A₂ s) / #B₂) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
      simpa [hg_def, hM_def, mul_pow, div_pow, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num,
        mul_div_right_comm] using h
    refine ⟨(lt_of_mul_lt_mul_left (hs.trans_eq' ?_) <| hg s).le, this.trans <|
      mul_le_of_le_one_right ?_ <| div_le_one_of_le₀ ?_ ?_, this.trans <|
      mul_le_of_le_one_left ?_ <| div_le_one_of_le₀ ?_ ?_⟩
    · simp_rw [A₁, A₂, g, ← card_smul_mu, smul_dddconv, dddconv_smul, ← Nat.cast_smul_eq_nsmul ℝ,
        wInner_smul_left, smul_eq_mul, star_trivial, mul_assoc, A₁, A₂]
    any_goals positivity
    all_goals exact Nat.cast_le.2 <| card_mono inter_subset_left
  rw [← sum_mul, lemma_0, nsmul_eq_mul, Nat.cast_mul, ← sum_mul, mul_right_comm, ← hgB,
    mul_left_comm, ← mul_assoc]
  simp only [Set.indicator_apply, boole_mul, mem_coe, mem_filter, mem_univ, true_and, ← sum_filter,
    mul_lt_mul_iff_left₀ hf, Function.comp_apply]
  by_cases h : ∀ s, g s ≠ 0 → M ^ 2 ≤ g s
  · rw [← sum_filter_ne_zero (s := filter _ _), Finset.filter_comm,
      filter_true_of_mem fun s hs ↦ h s (mem_filter.1 hs).2, ← sum_filter_ne_zero]
    refine lt_mul_of_one_lt_left (sum_pos (fun s hs ↦ (h _ (mem_filter.1 hs).2).trans_lt' <|
      by positivity) ?_) one_lt_two
    rw [← sum_filter_ne_zero] at hgB
    exact nonempty_of_sum_ne_zero <| hgB.trans_ne <| by positivity
  push Not at h
  obtain ⟨s, hs⟩ := h
  suffices h : (2 : ℝ) * ∑ s with g s < M ^ 2, g s < ∑ s, g s by
    refine (le_or_lt_of_add_le_add ?_).resolve_left h.not_ge
    simp_rw [← not_le, ← compl_filter, ← two_mul, ← mul_add, sum_compl_add_sum]
    rfl
  rw [← lt_div_iff₀' (zero_lt_two' ℝ), div_eq_inv_mul]
  calc
    ∑ s with g s < M ^ 2, g s = ∑ s with g s < M ^ 2 ∧ g s ≠ 0, sqrt (g s) * sqrt (g s)
          := by simp_rw [mul_self_sqrt (hg _), ← filter_filter, sum_filter_ne_zero]
    _ < ∑ s with g s < M ^ 2 ∧ g s ≠ 0, M * sqrt (g s)
        := sum_lt_sum_of_nonempty ⟨s, mem_filter.2 ⟨mem_univ _, hs.symm⟩⟩ ?_
    _ ≤ ∑ s, M * sqrt (g s) := sum_le_univ_sum_of_nonneg fun s ↦ by positivity
    _ = M * (∑ s, sqrt #(A₁ s) * sqrt #(A₂ s))
        := by simp_rw [mul_sum, g, sqrt_mul <| Nat.cast_nonneg _]
    _ ≤ M * (sqrt (∑ s, #(A₁ s)) * sqrt (∑ s, #(A₂ s))) := by
      gcongr; exact sum_sqrt_mul_sqrt_le _ fun i ↦ by positivity fun i ↦ by positivity
    _ = _ := ?_
  · simp only [mem_filter, mem_univ, true_and, and_imp]
    exact fun s hsM hs ↦ mul_lt_mul_of_pos_right ((sqrt_lt' hM).2 hsM) <|
      sqrt_pos.2 <| (hg _).lt_of_ne' hs
  rw [sum_cast_c, sum_cast_c, sqrt_mul', sqrt_mul', mul_mul_mul_comm (sqrt _), mul_self_sqrt,
    ← mul_assoc, hM_def, div_mul_cancel₀, ← sqrt_mul, mul_assoc, mul_self_sqrt, hgB, mul_right_comm,
    mul_assoc]
  all_goals positivity

set_option backward.isDefEq.respectTransparency false in
--TODO: When `1 < ε`, the result is trivial since `S = univ`.
lemma sifting (B₁ B₂ : Finset G) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : Even p)
    (hp₂ : 2 ≤ p) (hpε : ε⁻¹ * log (2 / δ) ≤ p) (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hf : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∉ s p ε B₁ B₂ A) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧ 1 - δ ≤ ∑ x ∈ s p ε B₁ B₂ A, (μ A₁ ○ᵈ μ A₂) x ∧
        (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤
            #A₁ / #B₁ ∧
          (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤
            #A₂ / #B₂ := by
  obtain ⟨A₁, hAB₁, A₂, hAB₂, h, hcard₁, hcard₂⟩ :=
    drc hp₂ 𝟭_[(s p ε B₁ B₂ A)ᶜ]
      (by simpa only [Set.support_indicator_one, coe_compl, Set.mem_compl_iff, mem_coe]) hB hA
  refine ⟨A₁, hAB₁, A₂, hAB₂, ?_, hcard₁, hcard₂⟩
  have hp₀ : 0 < p := by positivity
  have aux (c : Finset G) (r)
    (h : (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤ #c / r) :
    c.Nonempty := by
    simp_rw [nonempty_iff_ne_empty]
    rintro rfl
    simp [pow_mul', inv_mul_le_iff₀ (zero_lt_four' ℝ), div_nonpos_iff,
      (pow_pos (dLpNorm_ddconv_pos hp₀.ne' hB hA) 2).not_ge, hp₀.ne', hA.ne_empty] at h
  have hA₁ : A₁.Nonempty := aux _ _ hcard₁
  have hA₂ : A₂.Nonempty := aux _ _ hcard₂
  clear hcard₁ hcard₂ aux
  rw [sub_le_comm]
  calc
    _ = ∑ x ∈ (s p ε B₁ B₂ A)ᶜ, (μ A₁ ○ᵈ μ A₂) x := ?_
    _ = ⟪μ_[ℝ] A₁ ○ᵈ μ A₂, (↑) ∘ 𝟭_[(s (↑p) ε B₁ B₂ A)ᶜ, ℝ≥0]⟫_[ℝ] := by
      simp [wInner_one_eq_sum, -mem_compl, -mem_s, Set.indicator_apply]
      simp only [← ite_not (_ ∈ s p ε B₁ B₂ A), ← mem_compl, apply_ite]
      simp [-mem_compl]
    _ ≤ _ := (le_div_iff₀ <| dLpNorm_ddconv_pos hp₀.ne' hB hA).2 h
    _ ≤ _ := ?_
  · simp_rw [sub_eq_iff_eq_add', sum_add_sum_compl, sum_dddconv, map_mu]
    rw [sum_mu _ hA₁, sum_mu _ hA₂, one_mul]
  rw [div_le_iff₀ (dLpNorm_ddconv_pos hp₀.ne' hB hA), ← le_div_iff₀' (zero_lt_two' ℝ)]
  simp only [apply_ite NNReal.toReal, Set.indicator_apply, NNReal.coe_one, NNReal.coe_zero,
    mul_boole, Fintype.sum_ite_mem, mul_div_right_comm, ← coe_compl, mem_coe]
  calc
    ∑ x ∈ (s p ε B₁ B₂ A)ᶜ, (μ B₁ ○ᵈ μ B₂) x * (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p ≤
        ∑ x ∈ (s p ε B₁ B₂ A)ᶜ,
          (μ B₁ ○ᵈ μ B₂) x * ((1 - ε) * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂]) ^ p := by
      gcongr with x hx
      · exact dddconv_apply_nonneg mu_nonneg mu_nonneg x
      · exact dddconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg _
      · simpa using hx
    _ ≤ ∑ x, (μ B₁ ○ᵈ μ B₂) x * ((1 - ε) * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂]) ^ p := by
      gcongr
      · intros
        exact mul_nonneg (dddconv_apply_nonneg mu_nonneg mu_nonneg _) <| hp.pow_nonneg _
      · exact subset_univ _
    _ = ‖μ_[ℝ] B₁‖_[1] * ‖μ_[ℝ] B₂‖_[1] * ((1 - ε) ^ p * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p)
        := ?_
    _ ≤ _ :=
      mul_le_of_le_one_left (mul_nonneg (hp.pow_nonneg _) <| hp.pow_nonneg _) <|
        mul_le_one₀ dL1Norm_mu_le_one (by positivity) dL1Norm_mu_le_one
    _ ≤ _ := mul_le_mul_of_nonneg_right ?_ <| hp.pow_nonneg _
  · have : 0 ≤ μ_[ℝ] B₁ ○ᵈ μ B₂ := dddconv_nonneg mu_nonneg mu_nonneg
    simp_rw [← dL1Norm_dddconv mu_nonneg mu_nonneg, dL1Norm_eq_sum_norm,
      norm_of_nonneg (this _), sum_mul, mul_pow]
  calc
    (1 - ε) ^ p ≤ exp (-ε) ^ p := by gcongr; exact one_sub_le_exp_neg _
    _ = exp (-(ε * p)) := by rw [← neg_mul, exp_mul, rpow_natCast]
    _ ≤ exp (-log (2 / δ)) :=
      (exp_monotone <| neg_le_neg <| (inv_mul_le_iff₀ <| by positivity).1 hpε)
    _ = δ / 2 := by rw [exp_neg, exp_log, inv_div]; positivity

-- TODO: When `1 < ε`, the result is trivial since `S = univ`.
/-- Special case of `sifting` when `B₁ = B₂ = univ`. -/
lemma sifting_cor (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : Even p) (hp₀ : p ≠ 0)
    (hpε : ε⁻¹ * log (2 / δ) ≤ p) (hA : A.Nonempty) :
    ∃ A₁ A₂, 1 - δ ≤ ∑ x ∈ s p ε univ univ A, (μ A₁ ○ᵈ μ A₂) x ∧
        (4 : ℝ)⁻¹ * A.dens ^ (2 * p) ≤ A₁.dens ∧
          (4 : ℝ)⁻¹ * A.dens ^ (2 * p) ≤ A₂.dens := by
  by_cases hf :
      ∃ x, x ∈ A - A ∧ (𝟭_[A] ○ᵈ 𝟭_[A]) x ≤ (1 - ε) * ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ univ]
  · have hp₀ : p ≠ 0 := by positivity
    have :
      (4 : ℝ)⁻¹ * A.dens ^ (2 * p) ≤
        4⁻¹ * ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ univ] ^ (2 * p) / #A ^ (2 * p) := by
      rw [mul_div_assoc, ← div_pow]
      gcongr
      rw [nnratCast_dens, le_div_iff₀ (by positivity), ← mul_div_right_comm]
      have : Nonempty G := ⟨hA.choose⟩
      have hμ_univ : ∑ x : G, ((μ univ x : ℝ≥0) : ℝ≥0∞) = 1 := mod_cast sum_mu ℝ≥0 univ_nonempty
      calc
        _ = (‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[1, μ univ] : ℝ) := by
          simp [mu, wLpNorm_smul_right, dL1Norm_dddconv, card_univ, inv_mul_eq_div]
        _ ≤ _ := wLpNorm_mono_right hμ_univ
          (one_le_two.trans <| by obtain ⟨k, rfl⟩ := hp; norm_cast; lia) _
    obtain ⟨A₁, -, A₂, -, h, hcard₁, hcard₂⟩ :=
      sifting univ univ hε hε₁ hδ hp (by obtain ⟨k, rfl⟩ := hp; lia) hpε (by simp) hA (by simpa)
    exact ⟨A₁, A₂, h, this.trans <| by simpa [nnratCast_dens] using hcard₁,
      this.trans <| by simpa [nnratCast_dens] using hcard₂⟩
  · refine ⟨A, A, ?_, ?_⟩
    · rw [Fintype.sum_subset]
      · simpa [sum_dddconv, sum_mu, hA] using hδ.le
      · simpa [← Function.mem_support, ← coe_sub] using hf
    · rw [and_self]
      calc
        (4 : ℝ)⁻¹ * A.dens ^ (2 * p) ≤ 1 * A.dens ^ 1 := by
          gcongr ?_ * ?_
          · norm_num
          · exact pow_le_pow_of_le_one (by positivity) (mod_cast A.dens_le_one) (by omega)
        _ = A.dens := by simp
