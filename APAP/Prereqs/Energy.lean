import APAP.Prereqs.Convolution.Discrete.Basic
import APAP.Prereqs.FourierTransform.Discrete
import APAP.Prereqs.Function.Indicator.Complex

noncomputable section

open Finset Fintype Function MeasureTheory RCLike Real
open scoped Nat

variable {G : Type*} [AddCommGroup G] {s : Finset G}

def energy (n : ℕ) (s : Finset G) (ν : G → ℂ) : ℝ :=
  ∑ γ ∈ piFinset fun _ : Fin n ↦ s, ∑ δ ∈ piFinset fun _ : Fin n ↦ s, ‖ν (∑ i, γ i - ∑ i, δ i)‖

@[simp]
lemma energy_nonneg (n : ℕ) (s : Finset G) (ν : G → ℂ) : 0 ≤ energy n s ν := by
  unfold energy; positivity

lemma energy_nsmul (m n : ℕ) (s : Finset G) (ν : G → ℂ) :
    energy n s (m • ν) = m • energy n s ν := by
  simp only [energy, nsmul_eq_mul, mul_sum, Pi.natCast_def, Pi.mul_apply, norm_mul,
    Complex.norm_natCast]

@[simp] lemma energy_zero (s : Finset G) (ν : G → ℂ) : energy 0 s ν = ‖ν 0‖ := by simp [energy]

variable [DecidableEq G]

def boringEnergy (n : ℕ) (s : Finset G) : ℝ := energy n s trivChar

@[simp] lemma boringEnergy_zero (s : Finset G) : boringEnergy 0 s = 1 := by simp [boringEnergy]

lemma boringEnergy_eq [Fintype G] (n : ℕ) (s : Finset G) :
    boringEnergy n s = ∑ x, (𝟭 s ∗^ n) x ^ 2 := by
  classical
  simp only [boringEnergy, energy, apply_ite norm, trivChar_apply, norm_one, norm_zero, sum_boole,
    sub_eq_zero]
  rw [← Finset.sum_fiberwise _ fun f : Fin n → G ↦ ∑ i, f i]
  congr with x
  rw [indicate_iterConv_apply, sq, ← nsmul_eq_mul, ← sum_const]
  refine sum_congr rfl fun f hf ↦ ?_
  simp_rw [(mem_filter.1 hf).2, eq_comm]

@[simp] lemma boringEnergy_one [Finite G] (s : Finset G) : boringEnergy 1 s = #s := by
  cases nonempty_fintype G; simp [boringEnergy_eq, indicate_apply]

variable [Fintype G]

lemma cLpNorm_dft_indicate_pow [MeasurableSpace G] [DiscreteMeasurableSpace G] (n : ℕ)
    (s : Finset G) : ‖dft (𝟭 s)‖ₙ_[↑(2 * n)] ^ (2 * n) = boringEnergy n s := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  refine Complex.ofReal_injective ?_
  calc
    _ = ⟪dft (𝟭 s ∗^ n), dft (𝟭 s ∗^ n)⟫ₙ_[ℂ] := ?_
    _ = ⟪𝟭 s ∗^ n, 𝟭 s ∗^ n⟫_[ℂ] := wInner_cWeight_dft _ _
    _ = _ := ?_
  · rw [cLpNorm_pow_eq_expect_norm (by positivity)]
    simp_rw [pow_mul', ← norm_pow _ n, Complex.ofReal_expect, Complex.ofReal_pow,
      ← Complex.conj_mul', wInner_cWeight_eq_expect, inner_apply', dft_iterConv_apply]
  · simp only [wInner_one_eq_sum, inner_apply, boringEnergy_eq, Complex.ofReal_mul,
      Complex.ofReal_sum, sq, Complex.ofReal_iterConv,
      (((indicate_isSelfAdjoint _).iterConv _).apply _).conj_eq, Complex.ofReal_comp_indicate]

lemma cL2Norm_dft_indicate [MeasurableSpace G] [DiscreteMeasurableSpace G] (s : Finset G) :
    ‖dft (𝟭 s)‖ₙ_[2] = sqrt #s := by
  rw [eq_comm, sqrt_eq_iff_eq_sq (by positivity) (by positivity), eq_comm]
  simpa using cLpNorm_dft_indicate_pow 1 s
