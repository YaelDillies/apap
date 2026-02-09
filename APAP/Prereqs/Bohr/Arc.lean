import APAP.Prereqs.Bohr.Basic
import Mathlib.Analysis.Complex.Angle

/- ### Arc Bohr sets -/

open InnerProductGeometry Real

namespace BohrSet
variable {G : Type*} [AddCommGroup G] {B : BohrSet G} {ψ : AddChar G ℂ} {x : G}

def arcSet : Set G := {x | ∀ ψ, ‖angle (ψ x) 1‖₊ ≤ B.ewidth ψ}

lemma mem_arcSet_iff_nnnorm_ewidth : x ∈ B.arcSet ↔ ∀ ψ, ‖angle (ψ x) 1‖₊ ≤ B.ewidth ψ := Iff.rfl

lemma mem_arcSet_iff_nnnorm_width :
    x ∈ B.arcSet ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖angle (ψ x) 1‖₊ ≤ B.width ψ := by
  refine forall_congr' fun ψ => ?_
  constructor
  case mpr =>
    intro h
    rcases eq_top_or_lt_top (B.ewidth ψ) with h₁ | h₁
    case inl => simp [h₁]
    case inr =>
      have : ψ ∈ B.frequencies := by simp [mem_frequencies, h₁]
      specialize h this
      rwa [←ENNReal.coe_le_coe, coe_width this] at h
  case mp =>
    intro h₁ h₂
    rwa [←ENNReal.coe_le_coe, coe_width h₂]

lemma mem_arcSet_iff_norm_width :
    x ∈ B.arcSet ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖angle (ψ x) 1‖ ≤ B.width ψ :=
  mem_arcSet_iff_nnnorm_width

lemma arcSet_subset_chordSet [Finite G] :
    B.arcSet ⊆ B.chordSet := fun x hx ψ => by
  refine (hx ψ).trans' ?_
  rw [ENNReal.coe_le_coe, ←NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
    Real.norm_of_nonneg (angle_nonneg _ _), angle_comm]
  exact Complex.norm_sub_le_angle (by simp) (by simp)

lemma chordSet_subset_smul_arcSet [Finite G] :
    B.chordSet ⊆ ((π / 2) • B).arcSet := fun x hx ψ => by
  rw [ewidth_smul]
  split
  case isFalse => simp
  case isTrue h =>
    have := hx ψ
    simp only [←coe_width h, ENNReal.coe_le_coe, ←ENNReal.coe_mul, ←NNReal.coe_le_coe,
      coe_nnnorm, NNReal.coe_mul] at this ⊢
    rw [coe_nnabs, abs_of_nonneg pi_div_two_pos.le, Real.norm_of_nonneg (angle_nonneg _ _),
      angle_comm]
    refine (Complex.angle_le_mul_norm_sub (by simp) (by simp)).trans ?_
    gcongr

end BohrSet
