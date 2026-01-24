import LeanAPAP.Mathlib.MeasureTheory.Function.LpSeminorm.NNLpNorm
import LeanAPAP.Prereqs.Function.Indicator.Defs
import Mathlib.Algebra.Group.Translate
import Mathlib.Algebra.Star.Conjneg
import Mathlib.Data.Fintype.Order

/-!
# Normalised Lp norms
-/

open Finset hiding card
open Function ProbabilityTheory Real
open Fintype (card)
open scoped BigOperators ComplexConjugate ENNReal NNReal translate

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {α 𝕜 R E : Type*} [MeasurableSpace α]

/-! ### Lp norm -/

namespace MeasureTheory
section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {f g h : α → E}

/-- The Lp norm of a function with the compact normalisation. -/
noncomputable def cLpNorm (p : ℝ≥0∞) (f : α → E) : ℝ≥0 := nnLpNorm f p (uniformOn .univ)

notation "‖" f "‖ₙ_[" p "]" => cLpNorm p f

@[simp] lemma cLpNorm_exponent_zero (f : α → E) : ‖f‖ₙ_[0] = 0 := by simp [cLpNorm]

@[simp] lemma cLpNorm_zero (p : ℝ≥0∞) : ‖(0 : α → E)‖ₙ_[p] = 0 := by simp [cLpNorm]
@[simp] lemma cLpNorm_zero' (p : ℝ≥0∞) : ‖(fun _ ↦ 0 : α → E)‖ₙ_[p] = 0 := by simp [cLpNorm]

@[simp] lemma cLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : ‖f‖ₙ_[p] = 0 := by
  simp [cLpNorm]

@[simp] lemma cLpNorm_neg (f : α → E) (p : ℝ≥0∞) : ‖-f‖ₙ_[p] = ‖f‖ₙ_[p] := by simp [cLpNorm]
@[simp] lemma cLpNorm_neg' (f : α → E) (p : ℝ≥0∞) : ‖fun x ↦ -f x‖ₙ_[p] = ‖f‖ₙ_[p] := by
  simp [cLpNorm]

lemma cLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) : ‖f - g‖ₙ_[p] = ‖g - f‖ₙ_[p] := by
  simp [cLpNorm, nnLpNorm_sub_comm]

@[simp] lemma cLpNorm_norm (f : α → E) (p : ℝ≥0∞) : ‖fun i ↦ ‖f i‖‖ₙ_[p] = ‖f‖ₙ_[p] :=
  nnLpNorm_norm ..

@[simp] lemma cLpNorm_abs (f : α → ℝ) (p : ℝ≥0∞) : ‖|f|‖ₙ_[p] = ‖f‖ₙ_[p] := nnLpNorm_abs ..
@[simp] lemma cLpNorm_abs' (f : α → ℝ) (p : ℝ≥0∞) : ‖fun i ↦ |f i|‖ₙ_[p] = ‖f‖ₙ_[p] :=
  nnLpNorm_abs' ..

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

lemma cLpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) :
    ‖c • f‖ₙ_[p] = ‖c‖₊ * ‖f‖ₙ_[p] := by simp [cLpNorm, nnLpNorm_const_smul]

lemma cLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) :
    ‖n • f‖ₙ_[p] = n • ‖f‖ₙ_[p] := by simp [cLpNorm, nnLpNorm_nsmul]

variable [NormedSpace ℝ 𝕜]

lemma cLpNorm_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) : ‖(n : α → 𝕜) * f‖ₙ_[p] = n * ‖f‖ₙ_[p] :=
  nnLpNorm_natCast_mul ..

lemma cLpNorm_natCast_mul' (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) : ‖(n * f ·)‖ₙ_[p] = n * ‖f‖ₙ_[p] :=
  nnLpNorm_natCast_mul' ..

lemma cLpNorm_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) : ‖f * (n : α → 𝕜)‖ₙ_[p] = ‖f‖ₙ_[p] * n :=
  nnLpNorm_mul_natCast ..

lemma cLpNorm_mul_natCast' (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) : ‖(f · * n)‖ₙ_[p] = ‖f‖ₙ_[p] * n :=
  nnLpNorm_mul_natCast' ..

lemma cLpNorm_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    ‖f / (n : α → 𝕜)‖ₙ_[p] = ‖f‖ₙ_[p] / n := nnLpNorm_div_natCast hn ..

lemma cLpNorm_div_natCast' [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    ‖(f · / n)‖ₙ_[p] = ‖f‖ₙ_[p] / n := nnLpNorm_div_natCast' hn ..

end NormedField

section RCLike
variable {p : ℝ≥0∞}

@[simp] lemma cLpNorm_conj [RCLike R] (f : α → R) : ‖conj f‖ₙ_[p] = ‖f‖ₙ_[p] := nnLpNorm_conj ..

end RCLike

section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α] [Finite α]

lemma cLpNorm_add_le (hp : 1 ≤ p) : ‖f + g‖ₙ_[p] ≤ ‖f‖ₙ_[p] + ‖g‖ₙ_[p] :=
  nnLpNorm_add_le .of_discrete .of_discrete hp

lemma cLpNorm_sub_le (hp : 1 ≤ p) : ‖f - g‖ₙ_[p] ≤ ‖f‖ₙ_[p] + ‖g‖ₙ_[p] :=
  nnLpNorm_sub_le .of_discrete .of_discrete hp

lemma cLpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hp : 1 ≤ p) :
    ‖∑ i ∈ s, f i‖ₙ_[p] ≤ ∑ i ∈ s, ‖f i‖ₙ_[p] := nnLpNorm_sum_le (fun _ _ ↦ .of_discrete) hp

lemma cLpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι} {f : ι → α → E}
    (hp : 1 ≤ p) : ‖𝔼 i ∈ s, f i‖ₙ_[p] ≤ 𝔼 i ∈ s, ‖f i‖ₙ_[p] :=
  nnLpNorm_expect_le (fun _ _ ↦ .of_discrete) hp

lemma cLpNorm_le_cLpNorm_add_cLpNorm_sub' (hp : 1 ≤ p) : ‖f‖ₙ_[p] ≤ ‖g‖ₙ_[p] + ‖f - g‖ₙ_[p] :=
  nnLpNorm_le_nnLpNorm_add_nnLpNorm_sub' .of_discrete .of_discrete hp

lemma cLpNorm_le_cLpNorm_add_cLpNorm_sub (hp : 1 ≤ p) : ‖f‖ₙ_[p] ≤ ‖g‖ₙ_[p] + ‖g - f‖ₙ_[p] :=
  nnLpNorm_le_nnLpNorm_add_nnLpNorm_sub .of_discrete .of_discrete hp

lemma cLpNorm_le_add_cLpNorm_add (hp : 1 ≤ p) : ‖f‖ₙ_[p] ≤ ‖f + g‖ₙ_[p] + ‖g‖ₙ_[p] :=
  nnLpNorm_le_add_nnLpNorm_add .of_discrete .of_discrete hp

lemma cLpNorm_sub_le_cLpNorm_sub_add_cLpNorm_sub (hp : 1 ≤ p) :
    ‖f - h‖ₙ_[p] ≤ ‖f - g‖ₙ_[p] + ‖g - h‖ₙ_[p] :=
  nnLpNorm_sub_le_nnLpNorm_sub_add_nnLpNorm_sub .of_discrete .of_discrete .of_discrete hp

end DiscreteMeasurableSpace

variable [Finite α]

@[simp] lemma cLpNorm_const [Nonempty α] {p : ℝ≥0∞} (hp : p ≠ 0) (a : E) :
    ‖fun _i : α ↦ a‖ₙ_[p] = ‖a‖₊ := by cases nonempty_fintype α; simp [cLpNorm, uniformOn, *]

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

@[simp] lemma cLpNorm_one [Nonempty α] (hp : p ≠ 0) : ‖(1 : α → 𝕜)‖ₙ_[p] = 1 := by
  cases nonempty_fintype α; simp [cLpNorm, uniformOn, *]

end NormedField

omit [Finite α]
variable [DiscreteMeasurableSpace α] [Fintype α]

lemma cLpNorm_eq_expect_norm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    ‖f‖ₙ_[p] = (𝔼 i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [cLpNorm, uniformOn, coe_nnLpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete,
    integral_fintype, cond_apply, expect_eq_sum_div_card, div_eq_inv_mul, ← mul_sum, Measure.real]

lemma cLpNorm_eq_expect_nnnorm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    ‖f‖ₙ_[p] = (𝔼 i, ‖f i‖₊ ^ p.toReal) ^ p.toReal⁻¹ := by
  ext
  simp [cLpNorm, uniformOn, coe_nnLpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete,
    integral_fintype, cond_apply, expect_eq_sum_div_card, div_eq_inv_mul, ← mul_sum, Measure.real]

lemma cLpNorm_toNNReal_eq_expect_norm {p : ℝ} (hp : 0 < p) (f : α → E) :
    ‖f‖ₙ_[p.toNNReal] = (𝔼 i, ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [cLpNorm_eq_expect_norm'] <;> simp [hp.le, hp]

lemma cLpNorm_toNNReal_eq_expect_nnnorm {p : ℝ} (hp : 0 < p) (f : α → E) :
    ‖f‖ₙ_[p.toNNReal] = (𝔼 i, ‖f i‖₊ ^ p) ^ p⁻¹ := by
  rw [cLpNorm_eq_expect_nnnorm'] <;> simp [hp.le, hp]

lemma cLpNorm_eq_expect_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] = (𝔼 i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  cLpNorm_eq_expect_norm' (by simpa using hp) (by simp) _

lemma cLpNorm_eq_expect_nnnorm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] = (𝔼 i, ‖f i‖₊ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  cLpNorm_eq_expect_nnnorm' (by simpa using hp) (by simp) _

lemma cLpNorm_rpow_eq_expect_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] ^ (p : ℝ) = 𝔼 i, ‖f i‖ ^ (p : ℝ) := by
  rw [cLpNorm_eq_expect_norm hp, Real.rpow_inv_rpow] <;> positivity

lemma cLpNorm_rpow_eq_expect_nnnorm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] ^ (p : ℝ) = 𝔼 i, ‖f i‖₊ ^ (p : ℝ) := by
  rw [cLpNorm_eq_expect_nnnorm hp, NNReal.rpow_inv_rpow]; positivity

lemma cLpNorm_pow_eq_expect_norm {p : ℕ} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] ^ p = 𝔼 i, ‖f i‖ ^ p := by
  simpa using cLpNorm_rpow_eq_expect_norm (Nat.cast_ne_zero.2 hp) f

lemma cLpNorm_pow_eq_expect_nnnorm {p : ℕ} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] ^ p = 𝔼 i, ‖f i‖₊ ^ p := by
  simpa using cLpNorm_rpow_eq_expect_nnnorm (Nat.cast_ne_zero.2 hp) f

lemma cL2Norm_sq_eq_expect_norm (f : α → E) : ‖f‖ₙ_[2] ^ 2 = 𝔼 i, ‖f i‖ ^ 2 := by
  simpa using cLpNorm_pow_eq_expect_norm two_ne_zero _

lemma cL2Norm_sq_eq_expect_nnnorm (f : α → E) : ‖f‖ₙ_[2] ^ 2 = 𝔼 i, ‖f i‖₊ ^ 2 := by
  simpa using cLpNorm_pow_eq_expect_nnnorm two_ne_zero _

lemma cL2Norm_eq_expect_norm (f : α → E) : ‖f‖ₙ_[2] = (𝔼 i, ‖f i‖ ^ 2) ^ (2⁻¹ : ℝ) := by
  simpa [sqrt_eq_rpow] using cLpNorm_eq_expect_norm two_ne_zero _

lemma cL2Norm_eq_expect_nnnorm (f : α → E) : ‖f‖ₙ_[2] = (𝔼 i, ‖f i‖₊ ^ 2) ^ (2⁻¹ : ℝ) := by
  simpa [sqrt_eq_rpow] using cLpNorm_eq_expect_nnnorm two_ne_zero _

lemma cL1Norm_eq_expect_norm (f : α → E) : ‖f‖ₙ_[1] = 𝔼 i, ‖f i‖ := by
  simp [cLpNorm_eq_expect_norm']

lemma cL1Norm_eq_expect_nnnorm (f : α → E) : ‖f‖ₙ_[1] = 𝔼 i, ‖f i‖₊ := by
  simp [cLpNorm_eq_expect_nnnorm']

omit [Fintype α]
variable [Finite α]

lemma cLinftyNorm_eq_iSup_nnnorm (f : α → E) : ‖f‖ₙ_[∞] = ⨆ i, ‖f i‖₊ := by
  cases isEmpty_or_nonempty α
  · simp
  · simp [cLpNorm, nnLinftyNorm_eq_essSup]

lemma cLinftyNorm_eq_iSup_norm (f : α → E) : ‖f‖ₙ_[∞] = ⨆ i, ‖f i‖ := by
  cases isEmpty_or_nonempty α
  · simp
  · simp [cLpNorm, nnLinftyNorm_eq_essSup]

@[simp] lemma cLpNorm_eq_zero (hp : p ≠ 0) : ‖f‖ₙ_[p] = 0 ↔ f = 0 := by
  cases nonempty_fintype α
  simp [cLpNorm, uniformOn, nnLpNorm_eq_zero .of_discrete hp, ae_eq_top.2, cond_apply]

@[simp] lemma cLpNorm_pos (hp : p ≠ 0) : 0 < ‖f‖ₙ_[p] ↔ f ≠ 0 :=
  pos_iff_ne_zero.trans (cLpNorm_eq_zero hp).not

@[gcongr] lemma cLpNorm_mono_right (hpq : p ≤ q) : ‖f‖ₙ_[p] ≤ ‖f‖ₙ_[q] := sorry

lemma cLpNorm_mono_real {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : ‖f‖ₙ_[p] ≤ ‖g‖ₙ_[p] :=
  nnLpNorm_mono_real .of_discrete h

omit [Finite α]
lemma cLpNorm_two_mul_sum_pow [Fintype α] {ι : Type*} {n : ℕ} (hn : n ≠ 0) (s : Finset ι)
    (f : ι → α → ℂ) :
    ‖∑ i ∈ s, f i‖ₙ_[2 * n] ^ (2 * n) =
      ∑ x ∈ s ^^ n, ∑ y ∈ s ^^ n, 𝔼 a, (∏ i, conj (f (x i) a)) * ∏ i, f (y i) a :=
  calc
    _ = 𝔼 a, (‖∑ i ∈ s, f i a‖ : ℂ) ^ (2 * n) := by
      norm_cast
      rw [← cLpNorm_pow_eq_expect_norm (by positivity)]
      simp_rw [← sum_apply]
      norm_cast
    _ = 𝔼 a, (∑ i ∈ s, conj (f i a)) ^ n * (∑ j ∈ s, f j a) ^ n := by
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by simp_rw [sum_pow', sum_mul_sum, expect_sum_comm]

end NormedAddCommGroup
end MeasureTheory

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory

private alias ⟨_, cLpNorm_pos_of_ne_zero⟩ := cLpNorm_pos

private lemma cLpNorm_pos_of_pos {α E : Type*} {_ : MeasurableSpace α} [DiscreteMeasurableSpace α]
    [Finite α] [NormedAddCommGroup E] [Preorder E] {p : ℝ≥0∞} {f : α → E}
    (hp : p ≠ 0) (hf : 0 < f) : 0 < ‖f‖ₙ_[p] := cLpNorm_pos_of_ne_zero hp hf.ne'

/-- The `positivity` extension which identifies expressions of the form `‖f‖ₙ_[p]`. -/
@[positivity ‖_‖ₙ_[_]] def evalcLpNorm : PositivityExt where eval {u} α _z _p e := do
  match u, α, e with
  | 0, ~q(ℝ≥0), ~q(@cLpNorm $ι $E $instιmeas $instEnorm $p $f) =>
    let some pp := (← core q(inferInstance) q(inferInstance) p).toNonzero _ _ | failure
    try
      let _pE ← synthInstanceQ q(PartialOrder $E)
      assumeInstancesCommute
      let _ ← synthInstanceQ q(Fintype $ι)
      let _ ← synthInstanceQ q(DiscreteMeasurableSpace $ι)
      let some pf := (← core q(inferInstance) q(inferInstance) f).toNonzero _ _ | failure
      return .positive q(cLpNorm_pos_of_ne_zero $pp $pf)
    catch _ =>
      assumeInstancesCommute
      let some pf ← findLocalDeclWithType? q($f ≠ 0) | failure
      let pf : Q($f ≠ 0) := .fvar pf
      let _ ← synthInstanceQ q(Fintype $ι)
      let _ ← synthInstanceQ q(DiscreteMeasurableSpace $ι)
      return .positive q(cLpNorm_pos_of_ne_zero $pp $pf)
  | _ => throwError "not cLpNorm"

section Examples
section NormedAddCommGroup
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f : α → E}

example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < ‖f‖ₙ_[p] := by positivity
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < ‖f‖ₙ_[p] := by positivity

end NormedAddCommGroup

section Complex
variable [Fintype α] [DiscreteMeasurableSpace α] {w : α → ℝ≥0} {f : α → ℂ}

open scoped ComplexOrder

example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < ‖f‖ₙ_[p] := by positivity
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < ‖f‖ₙ_[p] := by positivity

end Complex
end Examples
end Mathlib.Meta.Positivity

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma cLpNorm_rpow (hp : p ≠ 0) (hq : q ≠ 0) (hf : 0 ≤ f) :
    ‖f ^ (q : ℝ)‖ₙ_[p] = ‖f‖ₙ_[p * q] ^ (q : ℝ) := by
  cases nonempty_fintype α
  refine NNReal.rpow_left_injective (NNReal.coe_ne_zero.2 hp) ?_
  dsimp
  rw [← NNReal.rpow_mul, ← mul_comm, ← ENNReal.coe_mul, ← NNReal.coe_mul,
    cLpNorm_rpow_eq_expect_nnnorm hp, cLpNorm_rpow_eq_expect_nnnorm (mul_ne_zero hq hp)]
  ext
  simp [abs_rpow_of_nonneg (hf _), rpow_mul]

lemma cLpNorm_pow (hp : p ≠ 0) {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) :
    ‖f ^ q‖ₙ_[p] = ‖f‖ₙ_[p * q] ^ q := by
  cases nonempty_fintype α
  refine NNReal.rpow_left_injective (NNReal.coe_ne_zero.2 hp) ?_
  dsimp
  rw [← NNReal.rpow_natCast_mul, ← mul_comm, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    ← NNReal.coe_natCast, ← NNReal.coe_mul, cLpNorm_rpow_eq_expect_nnnorm hp,
    cLpNorm_rpow_eq_expect_nnnorm (by positivity)]
  simp [← NNReal.rpow_natCast_mul]

lemma cL1Norm_rpow (hq : q ≠ 0) (hf : 0 ≤ f) : ‖f ^ (q : ℝ)‖ₙ_[1] = ‖f‖ₙ_[q] ^ (q : ℝ) := by
  simpa only [ENNReal.coe_one, one_mul] using cLpNorm_rpow one_ne_zero hq hf

lemma cL1Norm_pow {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) : ‖f ^ q‖ₙ_[1] = ‖f‖ₙ_[q] ^ q := by
  simpa only [ENNReal.coe_one, one_mul] using cLpNorm_pow one_ne_zero hq f

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
  {p q : ℝ≥0} {f g : α → 𝕜}

lemma cLpNorm_eq_cL1Norm_rpow (hp : p ≠ 0) (f : α → 𝕜) :
    ‖f‖ₙ_[p] = ‖fun a ↦ ‖f a‖ ^ (p : ℝ)‖ₙ_[1] ^ (p⁻¹ : ℝ) := by
  cases nonempty_fintype α
  ext
  simp [cLpNorm_eq_expect_nnnorm hp, cL1Norm_eq_expect_nnnorm, abs_rpow_of_nonneg]

lemma cLpNorm_rpow' (hp : p ≠ 0) (hq : q ≠ 0) (f : α → 𝕜) :
    ‖f‖ₙ_[p] ^ (q : ℝ) = ‖(fun a ↦ ‖f a‖) ^ (q : ℝ)‖ₙ_[p / q] := by
  rw [← ENNReal.coe_div hq, cLpNorm_rpow (div_ne_zero hp hq) hq (fun _ ↦ norm_nonneg _),
    cLpNorm_norm, ← ENNReal.coe_mul, div_mul_cancel₀ _ hq]

end Hoelder

section
variable {α : Type*} {mα : MeasurableSpace α}

@[simp]
lemma RCLike.cLpNorm_coe_comp [RCLike 𝕜] (p) (f : α → ℝ) : ‖((↑) : ℝ → 𝕜) ∘ f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  simp only [← cLpNorm_norm (((↑) : ℝ → 𝕜) ∘ f), ← cLpNorm_norm f, Function.comp_apply,
    RCLike.norm_ofReal, Real.norm_eq_abs]

@[simp] lemma Complex.cLpNorm_coe_comp (p) (f : α → ℝ) : ‖((↑) : ℝ → ℂ) ∘ f‖ₙ_[p] = ‖f‖ₙ_[p] :=
  RCLike.cLpNorm_coe_comp ..

end
end MeasureTheory


namespace MeasureTheory
variable {ι G 𝕜 E R : Type*} [Fintype ι] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]

/-! ### Indicator -/

section Indicator
variable [RCLike R] [DecidableEq ι] {s : Finset ι} {p : ℝ≥0}

lemma cLpNorm_rpow_indicate (hp : p ≠ 0) (s : Finset ι) : ‖𝟭_[R] s‖ₙ_[p] ^ (p : ℝ) = s.dens := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simpa
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) =
    ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) := fun x ↦ by split_ifs <;> simp
  simp [cLpNorm_rpow_eq_expect_nnnorm, hp, indicate_apply, apply_ite nnnorm, expect_const,
    nnratCast_dens, hs]

lemma cLpNorm_indicate (hp : p ≠ 0) (s : Finset ι) : ‖𝟭_[R] s‖ₙ_[p] = s.dens ^ (p⁻¹ : ℝ) := by
  refine (NNReal.eq_rpow_inv_iff ?_).2 (cLpNorm_rpow_indicate ?_ _) <;> positivity

lemma cLpNorm_pow_indicate {p : ℕ} (hp : p ≠ 0) (s : Finset ι) :
    ‖𝟭_[R] s‖ₙ_[p] ^ (p : ℝ) = s.dens := by
  simpa using cLpNorm_rpow_indicate (Nat.cast_ne_zero.2 hp) s

lemma cL2Norm_sq_indicate (s : Finset ι) : ‖𝟭_[R] s‖ₙ_[2] ^ 2 = s.dens := by
  simpa using cLpNorm_pow_indicate two_ne_zero s

@[simp] lemma cL2Norm_indicate (s : Finset ι) : ‖𝟭_[R] s‖ₙ_[2] = NNReal.sqrt s.dens := by
  rw [eq_comm, NNReal.sqrt_eq_iff_eq_sq, cL2Norm_sq_indicate]

@[simp] lemma cL1Norm_indicate (s : Finset ι) : ‖𝟭_[R] s‖ₙ_[1] = s.dens := by
  simpa using cLpNorm_pow_indicate one_ne_zero s

end Indicator

/-! ### Translation -/

section cLpNorm
variable {mG : MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
  {p : ℝ≥0∞}

@[simp]
lemma cLpNorm_translate [NormedAddCommGroup E] (a : G) (f : G → E) : ‖τ a f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  cases nonempty_fintype G
  obtain p | p := p
  · simp only [cLinftyNorm_eq_iSup_nnnorm, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [cLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [cLpNorm_eq_expect_nnnorm hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.expect_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

@[simp] lemma cLpNorm_conjneg [RCLike E] (f : G → E) : ‖conjneg f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  cases nonempty_fintype G
  simp only [conjneg, cLpNorm_conj]
  obtain p | p := p
  · simp only [cLinftyNorm_eq_iSup_nnnorm, ENNReal.none_eq_top]
    exact (Equiv.neg _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [cLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [cLpNorm_eq_expect_nnnorm hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.expect_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

lemma cLpNorm_translate_sum_sub_le [NormedAddCommGroup E] (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (a : ι → G) (f : G → E) : ‖τ (∑ i ∈ s, a i) f - f‖ₙ_[p] ≤ ∑ i ∈ s, ‖τ (a i) f - f‖ₙ_[p] := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s ih hs =>
  calc
    _ = ‖τ (∑ j ∈ s, a j) (τ (a i) f - f) + (τ (∑ j ∈ s, a j) f - f)‖ₙ_[p] := by
        rw [sum_cons, translate_add', translate_sub_right, sub_add_sub_cancel]
    _ ≤ ‖τ (∑ j ∈ s, a j) (τ (a i) f - f)‖ₙ_[p] + ∑ j ∈ s, ‖(τ (a j) f - f)‖ₙ_[p] := by
      grw [cLpNorm_add_le hp, hs]
    _ = _ := by rw [cLpNorm_translate, sum_cons]

end cLpNorm
end MeasureTheory
