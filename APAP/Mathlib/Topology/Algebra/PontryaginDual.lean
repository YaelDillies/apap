module

public import APAP.Mathlib.Analysis.Complex.Circle
public import APAP.Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.PontryaginDual

public section

open Real Set

-- TODO: Fix in mathlib
set_option allowUnsafeReducibility true in
attribute [reducible] PontryaginDual

namespace PontryaginDual
variable {M : Type*} [Monoid M] [TopologicalSpace M]

private def rightHalfArc : Set Circle := .exp '' .Ioo (-(π / 2)) (π / 2)

private lemma isOpen_rightHalfArc : IsOpen rightHalfArc := by
  simpa [rightHalfArc] using isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo

private lemma exists_pos_cos_mul_nonpos_of_pos {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ π) :
    ∃ n > (0 : ℕ), cos ((n : ℝ) * θ) ≤ 0 := by
  refine ⟨⌈π / 2 / θ⌉₊, by positivity, cos_nonpos_of_pi_div_two_le_of_le ?_ ?_⟩
  · grw [← Nat.le_ceil]
    simp [hθ0.ne']
  · grw [Nat.ceil_lt_add_one (by positivity), add_one_mul]
    simpa [hθ0.ne', add_comm]

private lemma exists_pos_cos_mul_nonpos {θ : ℝ} (hθ₁ : -π < θ) (hθ₂ : θ ≤ π) (hθ : θ ≠ 0) :
    ∃ n > (0 : ℕ), cos ((n : ℝ) * θ) ≤ 0 := by
  obtain (_hθ | hθ) := hθ.lt_or_gt
  · simpa using exists_pos_cos_mul_nonpos_of_pos (θ := -θ) (by linarith) (by linarith)
  · exact exists_pos_cos_mul_nonpos_of_pos hθ hθ₂

private lemma eq_one_of_forall_pow_mem_rightHalfArc {z : Circle}
    (hz : ∀ n > 0, z ^ n ∈ rightHalfArc) : z = 1 := by
  rw [← Circle.arg_eq_zero]
  by_contra hθ
  obtain ⟨n, hn, hcos⟩ :=
    exists_pos_cos_mul_nonpos (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _) hθ
  obtain ⟨t, ht, hzt⟩ := hz n hn
  have : cos (n * (z : ℂ).arg) = cos t := Circle.cos_eq_cos_of_exp_eq_exp (by simp [*])
  linarith [cos_pos_of_mem_Ioo ht]

/-- A compact monoid has discrete Pontryagin dual. -/
instance [CompactSpace M] : DiscreteTopology (PontryaginDual M) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  have hopen : IsOpen {ψ : PontryaginDual M | Set.MapsTo ψ .univ rightHalfArc} :=
    isOpen_induced (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ isOpen_rightHalfArc)
  convert hopen
  ext ψ
  refine ⟨?_, fun hψ ↦ ?_⟩
  · rintro rfl _ _
    exact ⟨0, by simp [pi_pos]⟩
  · ext a : 1
    refine eq_one_of_forall_pow_mem_rightHalfArc fun n hn ↦ ?_
    simpa [map_pow] using hψ (Set.mem_univ (a ^ n))

instance [DiscreteTopology M] [CompactSpace M] : Finite (PontryaginDual M) :=
  finite_of_compact_of_discrete

noncomputable instance [DiscreteTopology M] [CompactSpace M] : Fintype (PontryaginDual M) :=
  .ofFinite _

end PontryaginDual
