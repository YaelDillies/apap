module

public import APAP.Prereqs.Convolution.Discrete.Defs
public import APAP.Prereqs.LpNorm.Weighted
public import APAP.Prereqs.Mu
public import Mathlib.Analysis.RCLike.Inner
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

import AddCombi.Mathlib.Algebra.Order.GroupWithZero.Indicator
import APAP.Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import APAP.Physics.AlmostPeriodicity
import APAP.Physics.DRC
import APAP.Physics.Unbalancing
import APAP.Prereqs.Chang
import APAP.Prereqs.Convolution.Discrete.Basic
import APAP.Prereqs.Convolution.Norm
import APAP.Prereqs.Convolution.Order
import APAP.Prereqs.Convolution.ThreeAP
import APAP.Prereqs.FourierTransform.Convolution
import APAP.Prereqs.Inner.Function
import APAP.Prereqs.Inner.Hoelder.Discrete
import APAP.Prereqs.LpNorm.Discrete.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Finset.Density
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.FieldTheory.Finiteness
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite field case
-/

attribute [-simp] Real.log_inv

open Fintype Function MeasureTheory Module RCLike Real
open Finset hiding card
open scoped ENNReal NNReal BigOperators Combinatorics.Additive Pointwise Indicator mu

universe u
variable {G : Type u} [AddCommGroup G] [Fintype G] {A C : Finset G} {x y γ ε : ℝ}

local notation3 "𝓛" x:arg => 1 + log x⁻¹

lemma one_le_curlog (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : 1 ≤ 𝓛 x := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp
  have : 0 ≤ log x⁻¹ := by bound
  linarith

lemma curlog_pos (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : 0 < 𝓛 x := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp
  have : 0 ≤ log x⁻¹ := by bound
  positivity

lemma rpow_inv_neg_curlog_le (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : x⁻¹ ^ (𝓛 x)⁻¹ ≤ exp 1 := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp [(exp_pos _).le]
  obtain rfl | hx₁ := hx₁.eq_or_lt
  · simp
  have hx := (one_lt_inv₀ hx₀).2 hx₁
  calc
    x⁻¹ ^ (𝓛 x)⁻¹ ≤ x⁻¹ ^ (log x⁻¹)⁻¹ := by
      gcongr
      · exact hx.le
      · exact log_pos hx
      · simp
    _ ≤ exp 1 := x⁻¹.rpow_inv_log_le_exp_one

lemma curlog_mul_le (hx₀ : 0 < x) (hx₁ : x ≤ 1) (hy₀ : 0 < y) (hy₁ : y ≤ 1) :
    𝓛 (x * y) ≤ x⁻¹ * 𝓛 y := by
  suffices h : log x⁻¹ - (x⁻¹ - 1) ≤ (x⁻¹ - 1) * log y⁻¹ by
    rw [← sub_nonneg] at h ⊢
    convert h using 1
    rw [mul_inv, log_mul]
    any_goals positivity
    ring
  calc
    log x⁻¹ - (x⁻¹ - 1) ≤ 0 := sub_nonpos.2 <| log_le_sub_one_of_pos <| by positivity
    _ ≤ (x⁻¹ - 1) * log y⁻¹ := mul_nonneg (sub_nonneg.2 <| (one_le_inv₀ hx₀).2 hx₁) <| by bound

lemma curlog_div_le (hx₀ : 0 < x) (hx₁ : x ≤ 1) (hy : 1 ≤ y) : 𝓛 (x / y) ≤ y * 𝓛 x := by
  simpa [div_eq_inv_mul] using curlog_mul_le (by positivity) (inv_le_one_of_one_le₀ hy) hx₀ hx₁

lemma curlog_rpow_le' (hx₀ : 0 < x) (hx₁ : x ≤ 1) (hy₀ : 0 < y) (hy₁ : y ≤ 1) :
    𝓛 (x ^ y) ≤ y⁻¹ * 𝓛 x := by
  suffices h : 1 - y⁻¹ ≤ (y⁻¹ - y) * log x⁻¹ by
    rw [← sub_nonneg] at h ⊢
    convert h using 1
    rw [← inv_rpow, log_rpow]
    any_goals positivity
    ring
  calc
    1 - y⁻¹ ≤ 0 := sub_nonpos.2 <| (one_le_inv₀ hy₀).2 hy₁
    _ ≤ (y⁻¹ - y) * log x⁻¹ := mul_nonneg (sub_nonneg.2 <| hy₁.trans <| by bound) <| by bound

lemma curlog_rpow_le (hx₀ : 0 < x) (hy : 1 ≤ y) : 𝓛 (x ^ y) ≤ y * 𝓛 x := by
  grw [← inv_rpow, log_rpow, mul_one_add, hy] <;> positivity

lemma curlog_pow_le {n : ℕ} (hx₀ : 0 < x) (hn : n ≠ 0) : 𝓛 (x ^ n) ≤ n * 𝓛 x := by
  rw [← rpow_natCast]; exact curlog_rpow_le hx₀ <| mod_cast Nat.one_le_iff_ne_zero.2 hn

lemma ceil_curlog_div_four_le_three_curlog (hx₀ : 0 < x) (hx₁ : x ≤ 2⁻¹) :
    ⌈𝓛 (x / 4)⌉₊ ≤ 3 * 𝓛 x := by
  grw [Nat.ceil_lt_add_one <| by bound, inv_div, div_eq_mul_inv, show (4 : ℝ) = 2 * 2 by norm_num,
    log_mul (by norm_num) (by positivity), log_mul (by norm_num) (by norm_num)]
  have : log 2 ≤ log x⁻¹ := by grw [hx₁, inv_inv]
  nlinarith [log_two_gt_d9]

-- Public because it is in the blueprint
public lemma global_dichotomy [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (hA : A.Nonempty) (hγC : γ ≤ C.dens) (hγ : 0 < γ)
    (hAC : ε ≤ |card G * ⟪μ_[ℝ] A ∗ᵈ μ A, μ C⟫_[ℝ] - 1|) :
    ε / (2 * card G) ≤ ‖balance (μ_[ℝ] A) ○ᵈ balance (μ A)‖_[↑(2 * ⌈𝓛 γ⌉₊), μ univ] := by
  have hC : C.Nonempty := by simpa using hγ.trans_le hγC
  have hγ₁ : γ ≤ 1 := hγC.trans (by norm_cast; exact dens_le_one)
  set p := 2 * ⌈𝓛 γ⌉₊
  have hp : 1 < p :=
    Nat.succ_le_iff.1 (le_mul_of_one_le_right zero_le <| Nat.ceil_pos.2 <| curlog_pos hγ.le hγ₁)
  have hp' : (p⁻¹ : ℝ≥0) < 1 := inv_lt_one_of_one_lt₀ <| mod_cast hp
  have hp'' : (p : ℝ≥0).HolderConjugate _ := .conjExponent <| mod_cast hp
  have : (p : ℝ≥0∞).HolderConjugate _ := hp''.coe_ennreal
  rw [mul_comm, ← div_div, div_le_iff₀ (zero_lt_two' ℝ)]
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hAC (card G).cast_nonneg
    _ = |⟪balance (μ A) ∗ᵈ balance (μ A), μ C⟫_[ℝ]| := ?_
    _ ≤ ‖balance (μ_[ℝ] A) ∗ᵈ balance (μ A)‖_[p] * ‖μ_[ℝ] C‖_[NNReal.conjExponent p] :=
        abs_wInner_one_le_dLpNorm_mul_dLpNorm _ _
    _ ≤ ‖balance (μ_[ℝ] A) ○ᵈ balance (μ A)‖_[p] * (card G ^ (-(p : ℝ)⁻¹) * γ ^ (-(p : ℝ)⁻¹)) :=
        mul_le_mul (dLpNorm_ddconv_le_dLpNorm_dddconv' (by positivity) (even_two_mul _) _) ?_
          (by positivity) (by positivity)
    _ = ‖balance (μ_[ℝ] A) ○ᵈ balance (μ A)‖_[↑(2 * ⌈𝓛 γ⌉₊), μ univ] * γ ^ (-(p : ℝ)⁻¹) := ?_
    _ ≤ _ := mul_le_mul_of_nonneg_left ?_ <| by positivity
  · rw [← balance_ddconv, balance, wInner_sub_left, wInner_one_const_left, expect_ddconv,
      sum_mu ℝ hA, expect_mu ℝ hA, sum_mu ℝ hC, conj_trivial, one_mul, one_mul, ← mul_inv_cancel₀,
      ← mul_sub, abs_mul, abs_of_nonneg, mul_div_cancel_left₀] <;> positivity
  · rw [dLpNorm_mu hp''.symm.lt.le hC, hp''.symm.coe.inv_sub_one, NNReal.coe_natCast, ← mul_rpow]
    any_goals positivity
    rw [nnratCast_dens, le_div_iff₀, mul_comm] at hγC
    any_goals positivity
    refine rpow_le_rpow_of_nonpos ?_ hγC (neg_nonpos.2 ?_) <;> positivity
  · rw [mul_comm, mu_univ_eq_const, wLpNorm_const_right, mul_right_comm, rpow_neg, ← inv_rpow]
    any_goals positivity
    · congr
    · exact ENNReal.natCast_ne_top _
  · have : 1 ≤ γ⁻¹ := (one_le_inv₀ hγ).2 hγ₁
    have : 0 ≤ log γ⁻¹ := by bound
    calc
      γ ^ (-(↑p)⁻¹ : ℝ) = √(γ⁻¹ ^ ((↑⌈1 + log γ⁻¹⌉₊)⁻¹ : ℝ)) := by
        rw [rpow_neg hγ.le, inv_rpow hγ.le]
        unfold p
        push_cast
        rw [mul_inv_rev, rpow_mul, sqrt_eq_rpow, one_div, inv_rpow] <;> positivity
      _ ≤ √(γ⁻¹ ^ ((1 + log γ⁻¹)⁻¹ : ℝ)) := by grw [← Nat.le_ceil]
      _ ≤ √ (exp 1) := by gcongr; exact rpow_inv_neg_curlog_le hγ.le hγ₁
      _ ≤ √ 2.7182818286 := by gcongr; exact exp_one_lt_d9.le
      _ ≤ 2 := by rw [sqrt_le_iff]; norm_num

variable {q n : ℕ} [Module (ZMod q) G] {A₁ A₂ : Finset G} (S : Finset G) {α : ℝ}

-- Public because it is in the blueprint
public lemma ap_in_ff [DecidableEq G] (hq : q.Prime) (hα₀ : 0 < α) (hα₂ : α ≤ 2⁻¹)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hαA₁ : α ≤ A₁.dens) (hαA₂ : α ≤ A₂.dens) :
    ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤ 2 ^ 32 * 𝓛 α ^ 2 * 𝓛 (ε * α) ^ 2 * ε⁻¹ ^ 2 ∧
          |∑ x ∈ S, (μ (Set.toFinset V) ∗ᵈ μ A₁ ∗ᵈ μ A₂) x - ∑ x ∈ S, (μ A₁ ∗ᵈ μ A₂) x| ≤ ε := by
  classical
  let : MeasurableSpace G := ⊤
  have : Fact (1 < q) := ⟨hq.one_lt⟩
  have hA₁ : A₁.Nonempty := by simpa using hα₀.trans_le hαA₁
  have hA₂ : A₂.Nonempty := by simpa using hα₀.trans_le hαA₂
  have hα₁ : α ≤ 1 := hαA₁.trans <| mod_cast A₁.dens_le_one
  have : 0 ≤ log α⁻¹ := by bound
  have : 0 ≤ log (ε * α)⁻¹ := by bound
  obtain rfl | hS := S.eq_empty_or_nonempty
  · refine ⟨⊤, inferInstance, ?_, by simp [hε₀.le]⟩
    simp only [finrank_top, tsub_self, CharP.cast_eq_zero, mul_inv_rev, inv_pow]
    positivity
  have hσA₁ : σ[A₁, univ] ≤ α⁻¹ := by grw [addConst_le_inv_dens, hαA₁, NNRat.cast_inv]
  let k : ℕ := ⌈𝓛 (ε * α / 4)⌉₊
  have hk₀ : 0 < k := Nat.ceil_pos.2 <| curlog_pos (by positivity) <| by grw [hα₁]; linarith
  obtain ⟨T, hTcard, hTε⟩ :=
    AlmostPeriodicity.linfty_almost_periodicity_boosted (3 * ε / 8) (by positivity)
      (by nlinarith [hε₁]) k (by positivity) (le_inv_of_le_inv₀ (by positivity) hα₂) hσA₁
      univ_nonempty (-S) A₂ (by simpa) hA₂
  simp only [card_neg, card_univ] at hTcard
  have hT : T.Nonempty := by
    have hTpos : 0 < (#T : ℝ) := hTcard.trans_lt' (by positivity)
    simpa using hTpos
  let Δ := largeSpec (μ T) 2⁻¹
  let V : Submodule (ZMod q) G := AddSubgroup.toZModSubmodule _ <| ⨅ γ ∈ Δ, γ.toAddMonoidHom.ker
  let V' : Finset G := Set.toFinset V
  refine ⟨V, inferInstance, ?_, ?_⟩
  · obtain ⟨Δ', -, hΔ'card, hfΔ'⟩ : ∃ Δ' ⊆ Δ, _ := chang (mu_ne_zero.2 hT) (by norm_num)
    let W : Submodule (ZMod q) G := AddSubgroup.toZModSubmodule _ <| ⨅ γ ∈ Δ', γ.toAddMonoidHom.ker
    have mem_W {x} : x ∈ W ↔ ∀ γ ∈ Δ', γ x = 1 := by simp [W]
    have hWV : W ≤ V := by
      simp only [map_iInf, SetLike.le_def, Submodule.mem_iInf, AddSubgroup.mem_toZModSubmodule,
        AddMonoidHom.mem_ker, AddChar.toAddMonoidHom_apply, ofMul_eq_zero, W, V]
      intro x hx γ hγ
      obtain ⟨coeff, -, rfl⟩ := Finset.mem_addSpan.1 <| hfΔ' hγ
      rw [AddChar.sum_apply, Finset.prod_eq_one <| by simp_all]
    have := calc
      log T.dens⁻¹ ≤ log (α⁻¹ ^ (-4096 * ⌈𝓛 (min 1 (#A₂ / #S))⌉ * k ^ 2 / (3 * ε / 8) ^ 2))⁻¹ := by
        gcongr; rwa [nnratCast_dens, le_div_iff₀]; positivity
      _ = 2 ^ 12 * log α⁻¹ * ⌈𝓛 (min 1 (#A₂ / #S))⌉ * k ^ 2 / (3 * ε / 8) ^ 2 := by
        rw [log_inv, log_rpow (by positivity)]; ring_nf
      _ ≤ 2 ^ 12 * log α⁻¹ * ⌈𝓛 (min 1 A₂.dens)⌉ * k ^ 2 / (3 * ε / 8) ^ 2 := by
        rw [nnratCast_dens, ← card_univ]; gcongr; exact S.subset_univ
      _ ≤ 2 ^ 12 * log α⁻¹ * ⌈𝓛 (min 1 α)⌉ * k ^ 2 / (3 * ε / 8) ^ 2 := by gcongr
      _ = 2 ^ 12 * log α⁻¹ * ⌈𝓛 α⌉ * k ^ 2 / (3 * ε / 8) ^ 2 := by rw [min_eq_right hα₁]
      _ ≤ 2 ^ 12 * 𝓛 α * (2 * 𝓛 α) * (3 * 𝓛 (ε * α)) ^ 2 / (3 * ε / 8) ^ 2 := by
        gcongr
        · exact le_add_of_nonneg_left zero_le_one
        · exact Int.ceil_le_two_mul <| two_inv_lt_one.le.trans <| one_le_curlog hα₀.le hα₁
        · exact ceil_curlog_div_four_le_three_curlog (by positivity) <| by grw [hε₁, hα₂, one_mul]
      _ = 2 ^ 19 * 𝓛 α ^ 2 * 𝓛 (ε * α) ^ 2 * ε⁻¹ ^ 2 := by ring_nf
    calc
      (↑(finrank (ZMod q) G - V.finrank) : ℝ)
        ≤ ↑(finrank (ZMod q) G - W.finrank) := by gcongr; exact Submodule.finrank_mono hWV
      _ ≤ #Δ' := by
        let : Fact q.Prime := ⟨hq⟩
        simpa [W] using AddChar.codim_iInf_ker_le_finsetCard (s := Δ')
      _ ≤ ⌈changConst * exp 1 * ⌈𝓛 ↑(‖μ T‖_[1] ^ 2 / ‖μ T‖_[2] ^ 2 / card G)⌉₊ / 2⁻¹ ^ 2⌉₊ := by
        gcongr
      _ = ⌈2 ^ 7 * exp 1 ^ 2 * ⌈𝓛 T.dens⌉₊⌉₊ := by
        simp [hT, ← rpow_mul_natCast, dens, changConst, -exp_one_pow, rpow_neg_one]; ring_nf
      _ ≤ ⌈2 ^ 7 * 2 ^ 3 * (2 * 𝓛 T.dens)⌉₊ := by
        gcongr
        · calc
            exp 1 ^ 2 ≤ 2.7182818286 ^ 2 := by gcongr; exact exp_one_lt_d9.le
            _ ≤ 2 ^ 3 := by norm_num
        · exact Nat.ceil_le_two_mul <| two_inv_lt_one.le.trans <|
            one_le_curlog (by positivity) <| mod_cast T.dens_le_one
      _ = ⌈2 ^ 11 * 𝓛 T.dens⌉₊ := by ring_nf
      _ ≤ 2 * (2 ^ 11 * 𝓛 T.dens) := Nat.ceil_le_two_mul <|
          calc
            (2⁻¹ : ℝ) ≤ 2 ^ 11 * 1 := by norm_num
            _ ≤ 2 ^ 11 * 𝓛 T.dens := by
              gcongr; exact one_le_curlog (by positivity) <| mod_cast T.dens_le_one
      _ = 2 ^ 12 * 𝓛 T.dens := by ring
      _ ≤ 2 ^ 12 * (1 + 2 ^ 19 * 𝓛 α ^ 2 * 𝓛 (ε * α) ^ 2 * ε⁻¹ ^ 2) := by gcongr
      _ ≤ 2 ^ 12 * (2 ^ 19 * 𝓛 α ^ 2 * 𝓛 (ε * α) ^ 2 * ε⁻¹ ^ 2 +
            2 ^ 19 * 𝓛 α ^ 2 * 𝓛 (ε * α) ^ 2 * ε⁻¹ ^ 2) := by bound
      _ = 2 ^ 32 * 𝓛 α ^ 2 * 𝓛 (ε * α) ^ 2 * ε⁻¹ ^ 2 := by ring
  · have : ∑ x ∈ S, (μ_[ℝ] V' ∗ᵈ μ A₁ ∗ᵈ μ A₂) x = 𝔼 x ∈ V', (μ A₁ ∗ᵈ μ A₂ ○ᵈ 𝟭_[S]) x := by
      have : -V' = V' := by ext; simp [V']
      rw [← mu_wInner_one, ← indicator_one_wInner_one, ddconv_rotate,
        ← dddconv_wInner_one_eq_wInner_one_ddconv, wInner_one_dddconv_eq_ddconv_wInner_one,
        ← ddconv_conjneg, conjneg_mu, this, ddconv_comm]
    have : ∑ x ∈ S, (μ_[ℝ] A₁ ∗ᵈ μ A₂) x = (μ_[ℝ] A₁ ∗ᵈ μ A₂ ○ᵈ 𝟭_[S]) 0 := by
      simp [dddconv_indicator_one_eq_sum]
    sorry

lemma ap_in_ff' [DecidableEq G] (hq : q.Prime) (hα₀ : 0 < α) (hα₂ : α ≤ 2⁻¹)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hαA₁ : α ≤ A₁.dens) (hαA₂ : α ≤ A₂.dens) :
    ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤ 2 ^ 32 * 𝓛 α ^ 2 * 𝓛 (ε * α) ^ 2 * ε⁻¹ ^ 2 ∧
          |∑ x ∈ S, (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x - ∑ x ∈ S, (μ A₁ ○ᵈ μ A₂) x| ≤ ε := by
  simpa [← conjneg_mu] using ap_in_ff S hq (A₂ := -A₂) hα₀ hα₂ hε₀ hε₁ hαA₁ (by simpa)

set_option maxHeartbeats 400000 in
-- FIXME: Get rid of raised heartbeats
-- Public because it is in the blueprint
public lemma di_in_ff [DecidableEq G] [MeasurableSpace G] [DiscreteMeasurableSpace G] (hq : q.Prime)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (hγC : γ ≤ C.dens) (hγ : 0 < γ)
    (hAC : ε ≤ |card G * ⟪μ_[ℝ] A ∗ᵈ μ A, μ C⟫_[ℝ] - 1|) :
    ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
        ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
            2 ^ 128 * 𝓛 A.dens ^ 4 * 𝓛 γ ^ 4 / ε ^ 12 ∧
          (1 + ε / 32) * A.dens ≤ ‖𝟭_[(A : Set G), ℝ] ∗ᵈ μ (Set.toFinset V)‖_[∞] := by
  have hγ₁ : γ ≤ 1 := hγC.trans (by norm_cast; exact dens_le_one)
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · refine ⟨⊤, Classical.decPred _, ?_, by simp⟩
    simp only [finrank_top, tsub_self, CharP.cast_eq_zero, dens_empty, NNRat.cast_zero, inv_zero,
      log_zero, add_zero, one_pow, mul_one]
    positivity
  have hε₁' : 1 ≤ ε⁻¹ := (one_le_inv₀ hε₀).2 hε₁.le
  let α : ℝ := A.dens
  have hα₀ : 0 < α := by positivity
  have hα₁ : α ≤ 1 := by unfold α; exact mod_cast A.dens_le_one
  have : 0 ≤ log γ⁻¹ := log_nonneg <| (one_le_inv₀ hγ).2 hγ₁
  have : 0 < 𝓛 γ := curlog_pos hγ.le hγ₁
  have : 1 ≤ 𝓛 γ := one_le_curlog hγ.le hγ₁
  let p : ℕ := 2 * ⌈𝓛 γ⌉₊
  have hpupper : p ≤ 4 * 𝓛 γ := by
    unfold p; push_cast; grw [Nat.ceil_le_two_mul (by linarith)]; grind
  have : 0 < p := by positivity
  let f : G → ℝ := balance (μ A)
  obtain ⟨p', hp'upper, unbalancing⟩ :
    ∃ p' : ℕ, p' ≤ 2 ^ 10 * (ε / 2)⁻¹ ^ 2 * p ∧
      1 + ε / 2 / 2 ≤ ‖card G • (f ○ᵈ f) + 1‖_[p', μ univ] := by
    refine unbalancing _ (mul_ne_zero two_ne_zero (Nat.ceil_pos.2 <| curlog_pos hγ.le hγ₁).ne')
      (ε / 2) (by positivity) (div_le_one_of_le₀ (hε₁.le.trans <| by norm_num) <| by norm_num)
      (card G • (balance (μ A) ○ᵈ balance (μ A))) (sqrt (card G) • balance (μ A)) (μ univ) ?_ ?_ ?_
    · ext a : 1
      simp [smul_dddconv, dddconv_smul, ← mul_assoc, ← sq, ← Complex.ofReal_pow]
    · simp
    · have global_dichotomy := global_dichotomy hA₀ hγC hγ hAC
      simpa [wLpNorm_nsmul, ← nsmul_eq_mul, div_le_iff₀' (show (0 : ℝ) < card G by positivity),
        ← div_div, rpow_neg, inv_rpow] using global_dichotomy
  have : 0 < p' := pos_iff_ne_zero.2 <| by rintro rfl; simp at unbalancing; linarith
  let q' : ℕ := max (2 * p') (2 ^ 4 * ⌈ε⁻¹ * log (64 / ε)⌉₊)
  have : 0 < q' := by positivity
  have hq'even : Even q' := by grind
  have hp'q' : p' ≤ q' := by unfold q'; grw [← le_max_left]; lia
  have hq'lower : 2 ^ 4 * ε⁻¹ * log (64 / ε) ≤ q' := by
    unfold q'; grw [mul_assoc, ← le_max_right]; push_cast; grw [← Nat.le_ceil]; norm_num
  have hq'upper : q' ≤ 2 ^ 16 * 𝓛 γ / ε ^ 2 := by
    unfold q'
    push_cast
    grw [hp'upper, hpupper, max_le_add_of_nonneg (by positivity) (by positivity),
      (64 / ε).log_le_self (by positivity)]
    ring_nf
    grw [Nat.ceil_le_two_mul <| by grw [← hε₁']; norm_num]
    ring_nf
    bound
  have : 0 < log (6 / ε) := log_pos <| (one_lt_div hε₀).2 (by linarith)
  have : 0 < log (64 / ε) := log_pos <| (one_lt_div hε₀).2 (by linarith)
  obtain ⟨A₁, A₂, hA, hA₁, hA₂⟩ : ∃ (A₁ A₂ : Finset G),
      1 - ε / 32 ≤ ∑ x ∈ s q' (ε / 16) univ univ A, (μ A₁ ○ᵈ μ A₂) x ∧
        (4⁻¹ : ℝ) * A.dens ^ (2 * q') ≤ A₁.dens ∧ (4⁻¹ : ℝ) * A.dens ^ (2 * q') ≤ A₂.dens := by
    refine sifting_cor (by positivity) (by linarith) (by positivity)
      hq'even (by positivity) ?_ hA₀
    calc
      (ε / 16)⁻¹ * log (2 / (ε / 32)) = 2 ^ 4 * ε⁻¹ * log (64 / ε) := by ring_nf
      _ ≤ q' := hq'lower
  have : card G • (f ○ᵈ f) + 1 = card G • (μ A ○ᵈ μ A) := by
    unfold f
    rw [← balance_dddconv, balance, smul_sub, smul_const, Fintype.card_smul_expect]
    simp [sum_dddconv, hA₀]
  have := calc
    1 + ε / 4 = 1 + ε / 2 / 2 := by ring
    _ ≤ ‖card G • (f ○ᵈ f) + 1‖_[p', μ univ] := unbalancing
    _ = card G • ‖(μ_[ℝ] A ○ᵈ μ A)‖_[p', μ univ] := by simp [this, wLpNorm_nsmul, -nsmul_eq_mul]
    _ ≤ card G • ‖(μ_[ℝ] A ○ᵈ μ A)‖_[q', μ univ] := by
      have : Nonempty G := hA₀.to_type
      gcongr
      exact mod_cast sum_mu ℝ≥0 univ_nonempty
  let s' : Finset G := {x | 1 + ε / 8 ≤ card G • (μ A ○ᵈ μ A) x}
  have hss' : s q' (ε / 16) univ univ A ⊆ s' := by
    simp only [subset_iff, mem_s', ENNReal.coe_natCast, mu_univ_dddconv_mu_univ,
      mem_filter, mem_univ, true_and, s']
    rintro x hx
    calc
      1 + ε / 8 ≤ (1 - ε / 16) * (1 + ε / 4) := one_add_le_one_sub_mul_one_add <| calc
          ε / 8 + ε / 16 + ε / 16 * (ε / 4) ≤ ε / 8 + ε / 16 + ε / 16 * (1 / 4) := by gcongr
          _ ≤ ε / 4 := by linarith
      _ ≤ (1 - ε / 16) * card G • ‖μ_[ℝ] A ○ᵈ μ A‖_[q', μ univ] := by gcongr; linarith
      _ = card G • ((1 - ε / 16) * ‖μ_[ℝ] A ○ᵈ μ A‖_[q', μ univ]) := mul_smul_comm ..
      _ ≤ card G • (μ A ○ᵈ μ A) x := by gcongr
  obtain ⟨V, _, hVdim, hV⟩ : ∃ (V : Submodule (ZMod q) G) (_ : DecidablePred (· ∈ V)),
    ↑(finrank (ZMod q) G - finrank (ZMod q) V) ≤
        2 ^ 32 * 𝓛 (4⁻¹ * α ^ (2 * q')) ^ 2 * 𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ^ 2 * (ε / 32)⁻¹ ^ 2
          ∧ |∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x -
            ∑ x ∈ s', (μ A₁ ○ᵈ μ A₂) x| ≤ ε / 32 :=
    ap_in_ff' _ hq (by positivity)
    (calc
      4⁻¹ * (A.dens : ℝ) ^ (2 * q') ≤ 4⁻¹ * 1 := by
        gcongr; exact pow_le_one₀ (by positivity) <| mod_cast A.dens_le_one
      _ ≤ 2⁻¹ := by norm_num) (by positivity) (by linarith) hA₁ hA₂
  replace hV :=
    calc
      1 - ε / 16 = 1 - ε / 32 - ε / 32 := by ring
      _ ≤ ∑ x ∈ s q' (ε / 16) univ univ A, (μ A₁ ○ᵈ μ A₂) x -
        |∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x - ∑ x ∈ s', (μ A₁ ○ᵈ μ A₂) x| := by gcongr
      _ ≤ ∑ x ∈ s', (μ A₁ ○ᵈ μ A₂) x -
        -(∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x - ∑ x ∈ s', (μ A₁ ○ᵈ μ A₂) x) := by
        gcongr
        · have : 0 ≤ μ_[ℝ] A₁ ○ᵈ μ A₂ := dddconv_nonneg mu_nonneg mu_nonneg
          exact fun _ _ _ ↦ this _
        · exact neg_le_abs _
      _ = ∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := by ring
  refine ⟨V, inferInstance, ?_, ?_⟩
  · calc
      ↑(finrank (ZMod q) G - finrank (ZMod q) V)
        ≤ 2 ^ 32 * 𝓛 (4⁻¹ * α ^ (2 * q')) ^ 2 *
          𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ^ 2 * (ε / 32)⁻¹ ^ 2 := hVdim
      _ ≤ 2 ^ 32 * (8 * q' * 𝓛 α) ^ 2 *
          (2 ^ 8 * q' * 𝓛 α / ε) ^ 2 * (ε / 32)⁻¹ ^ 2 := by
        have : α ^ (2 * q') ≤ 1 := by bound
        have : 4⁻¹ * α ^ (2 * q') ≤ 1 := by bound
        have : ε / 32 * (4⁻¹ * α ^ (2 * q')) ≤ 1 := by bound
        have : 0 ≤ log (ε / 32 * (4⁻¹ * α ^ (2 * q')))⁻¹ := by bound
        have : 0 ≤ log (4⁻¹ * α ^ (2 * q'))⁻¹ := by bound
        have : 0 ≤ log (α ^ (2 * q'))⁻¹ := by bound
        have := calc
          𝓛 (4⁻¹ * α ^ (2 * q')) ≤ 4⁻¹⁻¹ * 𝓛 (α ^ (2 * q')) :=
            curlog_mul_le (by norm_num) (by norm_num) (by positivity) ‹_›
          _ ≤ 4⁻¹⁻¹ * (↑(2 * q') *  𝓛 α) := by gcongr; exact curlog_pow_le hα₀ (by positivity)
          _ = 8 * q' * 𝓛 α := by push_cast; ring
        gcongr
        calc
          𝓛 (ε / 32 * (4⁻¹ * α ^ (2 * q'))) ≤ (ε / 32)⁻¹ * 𝓛 (4⁻¹ * (α ^ (2 * q'))) :=
            curlog_mul_le (by positivity) (by linarith) (by positivity) ‹_›
          _ ≤ (ε / 32)⁻¹ * (8 * q' * 𝓛 α) := by gcongr
          _ = 2 ^ 8 * q' * 𝓛 α / ε := by ring
      _ = 2 ^ 64 * q' ^ 4 * 𝓛 α ^ 4 / ε ^ 4 := by ring
      _ ≤ 2 ^ 64 * (2 ^ 16 * 𝓛 γ / ε ^ 2) ^ 4 * 𝓛 α ^ 4 / ε ^ 4 := by gcongr
      _ = 2 ^ 128 * 𝓛 α ^ 4 * 𝓛 γ ^ 4 / ε ^ 12 := by ring
  · rw [← le_div_iff₀ (by positivity)]
    have : 0 ≤ μ_[ℝ] (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂ :=
      dddconv_nonneg (ddconv_nonneg mu_nonneg mu_nonneg) mu_nonneg
    calc
      1 + ε / 32 ≤ (1 + ε / 8) * (1 - ε / 16) := one_add_le_one_add_mul_one_sub <|
        calc
          ε / 32 + ε / 16 + ε / 8 * (ε / 16) ≤ ε / 32 + ε / 16 + ε / 8 * (1 / 16) := by gcongr
          _ ≤ ε / 8 := by linarith
      _ ≤ (1 + ε / 8) * ∑ x ∈ s', (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := by gcongr
      _ = ∑ x ∈ s', (1 + ε / 8) * (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := mul_sum ..
      _ ≤ ∑ x ∈ s', card G • (μ A ○ᵈ μ A) x * (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := by
        gcongr with x hx
        · exact this _
        · exact (mem_filter.1 hx).2
      _ ≤ ∑ x, card G • (μ A ○ᵈ μ A) x * (μ (Set.toFinset V) ∗ᵈ μ A₁ ○ᵈ μ A₂) x := by
        gcongr
        · rintro x - -
          have : (0 : ℝ) ≤ _ := this x
          have : 0 ≤ μ_[ℝ] A ○ᵈ μ A := dddconv_nonneg mu_nonneg mu_nonneg
          have : (0 : ℝ) ≤ _ := this x
          positivity
        · exact subset_univ _
      _ = card G • ⟪μ_[ℝ] (Set.toFinset V) ∗ᵈ μ A, μ A ∗ᵈ μ A₂ ○ᵈ μ A₁⟫_[ℝ] := by
        rw [← wInner_one_dddconv_eq_ddconv_wInner_one, dddconv_right_comm,
          ddconv_dddconv_right_comm (μ A), wInner_one_dddconv_eq_ddconv_wInner_one,
          ← dddconv_wInner_one_eq_wInner_one_ddconv, ← conj_wInner_symm]
        simp only [nsmul_eq_mul, mul_assoc, wInner_one_eq_sum, inner_apply, conj_trivial, map_sum,
          smul_sum]
      _ ≤ card G • (‖μ_[ℝ] (Set.toFinset V) ∗ᵈ μ A‖_[∞] * ‖μ_[ℝ] A ∗ᵈ μ A₂ ○ᵈ μ A₁‖_[1]) := by
        gcongr; exact wInner_one_le_dLpNorm_mul_dLpNorm _ _
      _ = _ := by
        have : 0 < (4 : ℝ)⁻¹ * A.dens ^ (2 * q') := by positivity
        replace hA₁ : A₁.Nonempty := by simpa using this.trans_le hA₁
        replace hA₂ : A₂.Nonempty := by simpa using this.trans_le hA₂
        rw [dL1Norm_dddconv, dL1Norm_ddconv]
        · simp [eq_div_iff, hA₀.dens_ne_zero, hA₀, hA₁, hA₂, ← card_smul_mu, smul_ddconv,
            dLpNorm_nsmul, -nsmul_eq_mul]
          simp [← mul_assoc, mul_comm, ddconv_comm]
        · exact mu_nonneg
        · exact mu_nonneg
        · exact ddconv_nonneg mu_nonneg mu_nonneg
        · exact mu_nonneg

public theorem ff (hq₃ : 3 ≤ q) (hq : q.Prime) (hA₀ : A.Nonempty) (hA : ThreeAPFree (α := G) A) :
    finrank (ZMod q) G ≤ 2 ^ 148 * 𝓛 A.dens ^ 9 := by
  let n : ℝ := finrank (ZMod q) G
  let α : ℝ := A.dens
  have : 1 < (q : ℝ) := mod_cast hq₃.trans_lt' (by norm_num)
  have : 1 ≤ (q : ℝ) := this.le
  have : NeZero q := ⟨by positivity⟩
  have : Fact q.Prime := ⟨hq⟩
  have hq' : Odd q := hq.odd_of_ne_two <| by rintro rfl; simp at hq₃
  have : 1 ≤ α⁻¹ := (one_le_inv₀ (by positivity)).2 (by simp [α])
  have hα₀ : 0 < α := by positivity
  have : 0 ≤ log α⁻¹ := log_nonneg ‹_›
  have : 0 < 𝓛 α := by positivity
  have : 0 < log q := log_pos ‹_›
  obtain hα | hα := le_total (q ^ (n / 2) : ℝ) (2 * α⁻¹ ^ 2)
  · rw [rpow_le_iff_le_log, log_mul, log_pow, Nat.cast_two, ← mul_div_right_comm,
      mul_div_assoc, ← le_div_iff₀] at hα
    any_goals positivity
    calc
      _ ≤ (log 2 + 2 * log α⁻¹) / (log q / 2) := hα
      _ = 4 / log q * (log 2 / 2 + log α⁻¹) := by ring
      _ ≤ 2 ^ 148 * 𝓛 α ^ 9 := by
        grw [← hq₃, pow_succ _ 8, ← mul_assoc, log_two_lt_d9]
        gcongr
        · norm_cast
          grw [← log_three_gt_d9, ← ‹1 ≤ α⁻¹›]
          norm_num
        · bound
  have ind (i : ℕ) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Fintype V) (_ : DecidableEq V) (_ : Module (ZMod q) V)
      (B : Finset V), n ≤ finrank (ZMod q) V + 2 ^ 140 * i * 𝓛 α ^ 8 ∧ ThreeAPFree (B : Set V)
        ∧ α ≤ B.dens ∧
      (B.dens < (65 / 64 : ℝ) ^ i * α →
        2⁻¹ ≤ card V * ⟪μ_[ℝ] B ∗ᵈ μ B, μ (B.image (2 • ·))⟫_[ℝ]) := by
    induction i with
    | zero =>
      classical
      exact ⟨G, inferInstance, inferInstance, inferInstance, inferInstance, A, by simp [n], hA,
        by simp [α], by simp [α, nnratCast_dens]⟩
    | succ i ih =>
    obtain ⟨V, _, _, _, _, B, hV, hB, hαβ, hBV⟩ := ih
    obtain hB' | hB' := le_or_gt 2⁻¹ (card V * ⟪μ_[ℝ] B ∗ᵈ μ B, μ (B.image (2 • ·))⟫_[ℝ])
    · exact ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, B,
        hV.trans (by gcongr; exact i.le_succ), hB, hαβ, fun _ ↦ hB'⟩
    let : MeasurableSpace V := ⊤
    have : 0 < 𝓛 B.dens := curlog_pos (by positivity) (by simp)
    have : 2⁻¹ ≤ |card V * ⟪μ_[ℝ] B ∗ᵈ μ B, μ (B.image (2 • ·))⟫_[ℝ] - 1| := by
      rw [abs_sub_comm, le_abs, le_sub_comm]
      norm_num at hB' ⊢
      exact .inl hB'.le
    obtain ⟨V', _, hVV', hv'⟩ := di_in_ff hq (by positivity) two_inv_lt_one (by
      rwa [Finset.dens_image (Nat.Coprime.nsmul_right_bijective _)]
      simpa [Module.card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card] using hq'.pow) hα₀ this
    rw [dLinftyNorm_eq_iSup_norm, ← Finset.sup'_univ_eq_ciSup, Finset.le_sup'_iff] at hv'
    obtain ⟨x, -, hx⟩ := hv'
    let B' : Finset V' := (-x +ᵥ B).preimage (↑) Set.injOn_subtype_val
    have hβ := calc
      ((1 + 64⁻¹ : ℝ) * B.dens : ℝ) = (1 + 2⁻¹ / 32) * B.dens := by ring
      _ ≤ ‖(𝟭_[(B : Set V), ℝ] ∗ᵈ μ (V' : Set V).toFinset) x‖ := hx
      _ = B'.dens := by
        rw [Real.norm_of_nonneg (ddconv_apply_nonneg Set.indicator_one_nonneg mu_nonneg _),
          dens_addSubgroup_preimage_vadd_eq_indicator_one_ddconv_mu]
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, B', ?_, ?_, ?_,
      fun h ↦ ?_⟩
    · calc
        n ≤ finrank (ZMod q) V + 2 ^ 140 * i * 𝓛 α ^ 8 := hV
        _ ≤ finrank (ZMod q) V' + ↑(finrank (ZMod q) V - finrank (ZMod q) V') +
            2 ^ 140 * i * 𝓛 α ^ 8 := by gcongr; norm_cast; exact le_add_tsub
        _ ≤ finrank (ZMod q) V' + 2 ^ 128 * 𝓛 B.dens ^ 4 * 𝓛 α ^ 4 / 2⁻¹ ^ 12 +
            2 ^ 140 * i * 𝓛 α ^ 8 := by gcongr
        _ ≤ finrank (ZMod q) V' + 2 ^ 128 * 𝓛 α ^ 4 * 𝓛 α ^ 4 / 2⁻¹ ^ 12 +
            2 ^ 140 * i * 𝓛 α ^ 8 := by have := hα₀.trans_le hαβ; gcongr
        _ = _ := by push_cast; ring
    · exact .of_image .subtypeVal Set.injOn_subtype_val (Set.subset_univ _)
        (hB.vadd_set (a := -x) |>.mono <| by simp [B'])
    · calc
        α ≤ B.dens := hαβ
        _ ≤ (1 + 64⁻¹) * B.dens := by simp [one_add_mul, NNRat.cast_nonneg]
        _ ≤ B'.dens := hβ
    · refine (h.not_ge <| ?_).elim
      calc
        (65 / 64) ^ (i + 1) * α = (1 + 64⁻¹) * ((65 / 64) ^ i * α) := by ring
        _ ≤ (1 + 64⁻¹) * B.dens := by gcongr; simpa [hB'.not_ge] using hBV
        _ ≤ B'.dens := hβ
  obtain ⟨V, _, _, _, _, B, hV, hB, hαβ, hBV⟩ := ind ⌊𝓛 α / log (65 / 64)⌋₊
  let β : ℝ := B.dens
  have aux : 0 < log (65 / 64) := log_pos (by norm_num)
  specialize hBV <| by
    calc
      _ ≤ (1 : ℝ) := mod_cast dens_le_one
      _ < _ := ?_
    rw [← inv_lt_iff_one_lt_mul₀, lt_pow_iff_log_lt, ← div_lt_iff₀]
    any_goals positivity
    calc
      log α⁻¹ / log (65 / 64)
        < ⌊log α⁻¹ / log (65 / 64)⌋₊ + 1 := Nat.lt_floor_add_one _
      _ = ⌊(log (65 / 64) + log α⁻¹) / log (65 / 64)⌋₊ := by
        rw [add_comm (log _), ← div_add_one aux.ne', Nat.floor_add_one, Nat.cast_succ]
        bound
      _ ≤ ⌊𝓛 α / log (65 / 64)⌋₊ := by
        gcongr
        calc
          log (65 / 64) ≤ 65/64 - 1 := log_le_sub_one_of_pos <| by norm_num
          _ ≤ 1 := by norm_num
  rw [hB.wInner_one_mu_ddconv_mu_mu_two_smul_mu] at hBV
  swap
  · simpa [Module.card_eq_pow_finrank (K := ZMod q) (V := V), ZMod.card] using hq'.pow
  suffices h : (q ^ (n - 2 ^ 147 * 𝓛 α ^ 9) : ℝ) ≤ q ^ (n / 2) by
    rwa [rpow_le_rpow_left_iff ‹_›, sub_le_comm, sub_half, div_le_iff₀' zero_lt_two, ← mul_assoc,
      ← pow_succ'] at h
  calc
    _ ≤ ↑q ^ (finrank (ZMod q) V : ℝ) := by
      gcongr
      rw [sub_le_comm]
      calc
        n - finrank (ZMod q) V ≤ 2 ^ 140 * ⌊𝓛 α / log (65 / 64)⌋₊ * 𝓛 α ^ 8 := by
          rwa [sub_le_iff_le_add']
        _ ≤ 2 ^ 140 * (𝓛 α / log (65 / 64)) * 𝓛 α ^ 8 := by
          gcongr; exact Nat.floor_le (by positivity)
        _ = 2 ^ 140 * (log (65 / 64)) ⁻¹ * 𝓛 α ^ 9 := by ring
        _ ≤ 2 ^ 140 * 2 ^ 7 * 𝓛 α ^ 9 := by
          gcongr
          refine inv_le_of_inv_le₀ (by positivity) ?_
          calc
            (2 ^ 7)⁻¹ ≤ 1 - (65 / 64)⁻¹ := by norm_num
            _ ≤ log (65 / 64) := one_sub_inv_le_log_of_pos (by positivity)
        _ = 2 ^ 147 * 𝓛 α ^ 9 := by ring
    _ = ↑(card V) := by simp [Module.card_eq_pow_finrank (K := ZMod q) (V := V)]
    _ ≤ 2 * β⁻¹ ^ 2 := by
      rw [← natCast_card_mul_nnratCast_dens, mul_pow, mul_inv, ← mul_assoc,
        ← div_eq_mul_inv (card V : ℝ), ← zpow_one_sub_natCast₀ (by positivity)] at hBV
      have : 0 < (card V : ℝ) := by positivity
      simpa [le_inv_mul_iff₀, mul_inv_le_iff₀, this, zero_lt_two, mul_comm] using hBV
    _ ≤ 2 * α⁻¹ ^ 2 := by gcongr
    _ ≤ _ := hα
