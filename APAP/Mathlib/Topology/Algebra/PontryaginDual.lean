module

public import Mathlib.Topology.Algebra.PontryaginDual

public section

namespace PontryaginDual
variable {M : Type*} [Monoid M] [TopologicalSpace M]

open Complex Set

private def rightHalfArc : Set Circle :=
  Circle.exp '' Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

private lemma isOpen_rightHalfArc : IsOpen rightHalfArc := by
  simpa [rightHalfArc] using isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo

private lemma eventually_cos_mul_nonpos_of_pos {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) :
    ∃ n : ℕ, 0 < n ∧ Real.cos ((n : ℝ) * θ) ≤ 0 := by
  let n : ℕ := Nat.ceil ((Real.pi / 2) / θ)
  have hqpos : 0 < (Real.pi / 2) / θ := div_pos (half_pos Real.pi_pos) hθ0
  have hnpos : 0 < n := by
    dsimp [n]
    exact Nat.ceil_pos.mpr hqpos
  refine ⟨n, hnpos, ?_⟩
  have hceil : (Real.pi / 2) / θ ≤ (n : ℝ) := by
    dsimp [n]
    exact Nat.le_ceil _
  have hl : Real.pi / 2 ≤ (n : ℝ) * θ := by
    have h := mul_le_mul_of_nonneg_right hceil (le_of_lt hθ0)
    simpa [div_mul_cancel₀ _ (ne_of_gt hθ0)] using h
  have hceil_lt : (n : ℝ) < (Real.pi / 2) / θ + 1 := by
    dsimp [n]
    exact Nat.ceil_lt_add_one (le_of_lt hqpos)
  have hu_lt : (n : ℝ) * θ < Real.pi / 2 + θ := by
    have h := mul_lt_mul_of_pos_right hceil_lt hθ0
    simpa [add_mul, div_mul_cancel₀ _ (ne_of_gt hθ0), one_mul] using h
  have hu : (n : ℝ) * θ ≤ Real.pi + Real.pi / 2 := by
    linarith
  exact Real.cos_nonpos_of_pi_div_two_le_of_le hl hu

private lemma eventually_cos_mul_nonpos {θ : ℝ}
    (hθ₁ : -Real.pi < θ) (hθ₂ : θ ≤ Real.pi) (hθ : θ ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ Real.cos ((n : ℝ) * θ) ≤ 0 := by
  rcases lt_or_gt_of_ne hθ with _hθneg | hθpos
  · rcases eventually_cos_mul_nonpos_of_pos (show 0 < -θ by linarith)
      (show -θ ≤ Real.pi by linarith) with ⟨n, hn, hcos⟩
    refine ⟨n, hn, ?_⟩
    have harg : (n : ℝ) * θ = -((n : ℝ) * -θ) := by ring
    have hcosEq : Real.cos ((n : ℝ) * θ) = Real.cos ((n : ℝ) * -θ) := by
      rw [harg, Real.cos_neg]
    exact hcosEq.trans_le hcos
  · exact eventually_cos_mul_nonpos_of_pos hθpos hθ₂

private lemma circle_pow_exp (x : ℝ) (n : ℕ) :
    (Circle.exp x) ^ n = Circle.exp ((n : ℝ) * x) := by
  induction n with
  | zero => simp [Circle.exp_zero]
  | succ n ih =>
      rw [pow_succ, ih, ← Circle.exp_add]
      congr 1
      norm_num
      ring

private lemma circle_cos_eq_of_exp_eq {x y : ℝ} (h : Circle.exp x = Circle.exp y) :
    Real.cos x = Real.cos y := by
  have hc := congrArg (fun z : Circle => (z : ℂ)) h
  have hre := congrArg Complex.re hc
  simpa [Circle.coe_exp, Complex.exp_mul_I] using hre

private lemma circle_eq_one_of_forall_pow_mem_rightHalfArc {z : Circle}
    (hz : ∀ n : ℕ, 0 < n → z ^ n ∈ rightHalfArc) :
    z = 1 := by
  let θ : ℝ := Complex.arg (z : ℂ)
  by_cases hθ : θ = 0
  · rw [← Circle.exp_arg z, show Complex.arg (z : ℂ) = 0 from hθ]
    simp [Circle.exp_zero]
  · have hθ₁ : -Real.pi < θ := by
      dsimp [θ]
      exact Complex.neg_pi_lt_arg _
    have hθ₂ : θ ≤ Real.pi := by
      dsimp [θ]
      exact Complex.arg_le_pi _
    rcases eventually_cos_mul_nonpos hθ₁ hθ₂ hθ with ⟨n, hn, hcos⟩
    rcases hz n hn with ⟨t, ht, hzt⟩
    have hpow : z ^ n = Circle.exp ((n : ℝ) * θ) := by
      rw [← Circle.exp_arg z]
      dsimp [θ]
      exact circle_pow_exp _ n
    have hcosEq : Real.cos ((n : ℝ) * θ) = Real.cos t :=
      circle_cos_eq_of_exp_eq (hpow.symm.trans hzt.symm)
    have hcospos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht
    linarith

/-- A compact monoid has discrete Pontryagin dual. -/
instance [CompactSpace M] : DiscreteTopology (PontryaginDual M) := by
  let V : Set (PontryaginDual M) := {ψ | Set.MapsTo ψ Set.univ rightHalfArc}
  have hVopen : IsOpen V := by
    dsimp [V]
    exact isOpen_induced (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ isOpen_rightHalfArc)
  have hVeq : V = ({1} : Set (PontryaginDual M)) := by
    ext ψ
    constructor
    · intro hψ
      rw [Set.mem_singleton_iff]
      apply ContinuousMonoidHom.ext
      intro a
      have hpow : ∀ n : ℕ, 0 < n → (ψ a) ^ n ∈ rightHalfArc := by
        intro n hn
        have hmap := hψ (Set.mem_univ (a ^ n))
        simpa [map_pow] using hmap
      simpa using circle_eq_one_of_forall_pow_mem_rightHalfArc hpow
    · intro hψ
      rw [Set.mem_singleton_iff] at hψ
      subst ψ
      intro _ _
      refine ⟨0, ?_, ?_⟩
      · constructor <;> linarith [Real.pi_pos]
      · rw [Circle.exp_zero]
        rfl
  exact discreteTopology_of_isOpen_singleton_one (by simpa [hVeq] using hVopen)

instance [DiscreteTopology M] [CompactSpace M] : Finite (PontryaginDual M) :=
  finite_of_compact_of_discrete

noncomputable instance [DiscreteTopology M] [CompactSpace M] : Fintype (PontryaginDual M) :=
  .ofFinite _

end PontryaginDual
