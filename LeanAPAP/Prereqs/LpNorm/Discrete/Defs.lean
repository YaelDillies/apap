import LeanAPAP.Mathlib.MeasureTheory.Function.LpSeminorm.NNLpNorm
import Mathlib.Data.Fintype.Order

/-!
# Lp norms
-/

open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal NNRat

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {α 𝕜 R E : Type*} [MeasurableSpace α]

namespace MeasureTheory
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {f g h : α → E}

/-- The Lp norm of a function with the compact normalisation. -/
noncomputable def dLpNorm (p : ℝ≥0∞) (f : α → E) : ℝ≥0 := nnLpNorm f p .count

notation "‖" f "‖_[" p "]" => dLpNorm p f

@[simp] lemma dLpNorm_exponent_zero (f : α → E) : ‖f‖_[0] = 0 := by simp [dLpNorm]

@[simp] lemma dLpNorm_zero (p : ℝ≥0∞) : ‖(0 : α → E)‖_[p] = 0 := by simp [dLpNorm]
@[simp] lemma dLpNorm_zero' (p : ℝ≥0∞) : ‖(fun _ ↦ 0 : α → E)‖_[p] = 0 := by simp [dLpNorm]

@[simp] lemma dLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : ‖f‖_[p] = 0 := by
  simp [dLpNorm]

@[simp] lemma dLpNorm_neg (f : α → E) (p : ℝ≥0∞) : ‖-f‖_[p] = ‖f‖_[p] := by simp [dLpNorm]
@[simp] lemma dLpNorm_neg' (f : α → E) (p : ℝ≥0∞) : ‖fun x ↦ -f x‖_[p] = ‖f‖_[p] := by
  simp [dLpNorm]

lemma dLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) : ‖f - g‖_[p] = ‖g - f‖_[p] := by
  simp [dLpNorm, nnLpNorm_sub_comm]

@[simp] lemma dLpNorm_norm (f : α → E) (p : ℝ≥0∞) : ‖fun i ↦ ‖f i‖‖_[p] = ‖f‖_[p] :=
  nnLpNorm_norm ..

@[simp] lemma dLpNorm_abs (f : α → ℝ) (p : ℝ≥0∞) : ‖|f|‖_[p] = ‖f‖_[p] := nnLpNorm_abs ..
@[simp] lemma dLpNorm_abs' (f : α → ℝ) (p : ℝ≥0∞) : ‖fun i ↦ |f i|‖_[p] = ‖f‖_[p] :=
  nnLpNorm_abs' ..

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

lemma dLpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) :
    ‖c • f‖_[p] = ‖c‖₊ * ‖f‖_[p] := by simp [dLpNorm, nnLpNorm_const_smul]

lemma dLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) :
    ‖n • f‖_[p] = n • ‖f‖_[p] := by simp [dLpNorm, nnLpNorm_nsmul]

variable [NormedSpace ℝ 𝕜]

lemma dLpNorm_natCast_mul (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) : ‖(n : α → 𝕜) * f‖_[p] = n * ‖f‖_[p] :=
  nnLpNorm_natCast_mul ..

lemma dLpNorm_natCast_mul' (n : ℕ) (f : α → 𝕜) (p : ℝ≥0∞) : ‖(n * f ·)‖_[p] = n * ‖f‖_[p] :=
  nnLpNorm_natCast_mul' ..

lemma dLpNorm_mul_natCast (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) : ‖f * (n : α → 𝕜)‖_[p] = ‖f‖_[p] * n :=
  nnLpNorm_mul_natCast ..

lemma dLpNorm_mul_natCast' (f : α → 𝕜) (n : ℕ) (p : ℝ≥0∞) : ‖(f · * n)‖_[p] = ‖f‖_[p] * n :=
  nnLpNorm_mul_natCast' ..

lemma dLpNorm_div_natCast [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    ‖f / (n : α → 𝕜)‖_[p] = ‖f‖_[p] / n := nnLpNorm_div_natCast hn ..

lemma dLpNorm_div_natCast' [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) (f : α → 𝕜) (p : ℝ≥0∞) :
    ‖(f · / n)‖_[p] = ‖f‖_[p] / n := nnLpNorm_div_natCast' hn ..

end NormedField

section RCLike
variable {p : ℝ≥0∞}

@[simp] lemma dLpNorm_conj [RCLike R] (f : α → R) : ‖conj f‖_[p] = ‖f‖_[p] := nnLpNorm_conj ..

end RCLike

section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α] [Finite α]

lemma dLpNorm_add_le (hp : 1 ≤ p) : ‖f + g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  nnLpNorm_add_le .of_discrete .of_discrete hp

lemma dLpNorm_sub_le (hp : 1 ≤ p) : ‖f - g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  nnLpNorm_sub_le .of_discrete .of_discrete hp

lemma dLpNorm_sum_le {ι : Type*} {s : Finset ι} {f : ι → α → E} (hp : 1 ≤ p) :
    ‖∑ i ∈ s, f i‖_[p] ≤ ∑ i ∈ s, ‖f i‖_[p] := nnLpNorm_sum_le (fun _ _ ↦ .of_discrete) hp

lemma dLpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι} {f : ι → α → E}
    (hp : 1 ≤ p) : ‖𝔼 i ∈ s, f i‖_[p] ≤ 𝔼 i ∈ s, ‖f i‖_[p] :=
  nnLpNorm_expect_le (fun _ _ ↦ .of_discrete) hp

lemma dLpNorm_le_dLpNorm_add_dLpNorm_sub' (hp : 1 ≤ p) : ‖f‖_[p] ≤ ‖g‖_[p] + ‖f - g‖_[p] :=
  nnLpNorm_le_nnLpNorm_add_nnLpNorm_sub' .of_discrete .of_discrete hp

lemma dLpNorm_le_dLpNorm_add_dLpNorm_sub (hp : 1 ≤ p) : ‖f‖_[p] ≤ ‖g‖_[p] + ‖g - f‖_[p] :=
  nnLpNorm_le_nnLpNorm_add_nnLpNorm_sub .of_discrete .of_discrete hp

lemma dLpNorm_le_add_dLpNorm_add (hp : 1 ≤ p) : ‖f‖_[p] ≤ ‖f + g‖_[p] + ‖g‖_[p] :=
  nnLpNorm_le_add_nnLpNorm_add .of_discrete .of_discrete hp

lemma dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub (hp : 1 ≤ p) :
    ‖f - h‖_[p] ≤ ‖f - g‖_[p] + ‖g - h‖_[p] :=
  nnLpNorm_sub_le_nnLpNorm_sub_add_nnLpNorm_sub .of_discrete .of_discrete .of_discrete hp

end DiscreteMeasurableSpace

variable [Fintype α]

@[simp]
lemma dLpNorm_const [Nonempty α] {p : ℝ≥0∞} (hp : p ≠ 0) (a : E) :
    ‖fun _i : α ↦ a‖_[p] = ‖a‖₊ * Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, *]

@[simp]
lemma dLpNorm_const' {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) (a : E) :
    ‖fun _i : α ↦ a‖_[p] = ‖a‖₊ * Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, *]

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

@[simp] lemma dLpNorm_one [Nonempty α] (hp : p ≠ 0) :
    ‖(1 : α → 𝕜)‖_[p] = Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, *]

@[simp] lemma dLpNorm_one' (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    ‖(1 : α → 𝕜)‖_[p] = Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, *]

end NormedField

variable [DiscreteMeasurableSpace α]

lemma dLpNorm_eq_sum_norm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [dLpNorm, coe_nnLpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete, integral_fintype]

lemma dLpNorm_eq_sum_nnnorm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖₊ ^ p.toReal) ^ p.toReal⁻¹ := by
  ext; push_cast; exact dLpNorm_eq_sum_norm' hp₀ hp f

lemma dLpNorm_toNNReal_eq_sum_norm {p : ℝ} (hp : 0 < p) (f : α → E) :
    ‖f‖_[p.toNNReal] = (∑ i, ‖f i‖ ^ p) ^ p⁻¹ := by
  rw [dLpNorm_eq_sum_nnnorm'] <;> simp [hp.le, hp]

lemma dLpNorm_toNNReal_eq_sum_nnnorm {p : ℝ} (hp : 0 < p) (f : α → E) :
    ‖f‖_[p.toNNReal] = (∑ i, ‖f i‖₊ ^ p) ^ p⁻¹ := by
  rw [dLpNorm_eq_sum_nnnorm'] <;> simp [hp.le, hp]

lemma dLpNorm_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  dLpNorm_eq_sum_norm' (by simpa using hp) (by simp) _

lemma dLpNorm_eq_sum_nnnorm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖₊ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  dLpNorm_eq_sum_nnnorm' (by simpa using hp) (by simp) _

lemma dLpNorm_rpow_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] ^ (p : ℝ) = ∑ i, ‖f i‖ ^ (p : ℝ) := by
  rw [dLpNorm_eq_sum_norm hp, Real.rpow_inv_rpow (by positivity) (mod_cast hp)]

lemma dLpNorm_rpow_eq_sum_nnnorm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] ^ (p : ℝ) = ∑ i, ‖f i‖₊ ^ (p : ℝ) := by
  rw [dLpNorm_eq_sum_nnnorm hp, NNReal.rpow_inv_rpow (mod_cast hp)]

lemma dLpNorm_pow_eq_sum_norm {p : ℕ} (hp : p ≠ 0) (f : α → E) : ‖f‖_[p] ^ p = ∑ i, ‖f i‖ ^ p := by
  simpa using dLpNorm_rpow_eq_sum_norm (Nat.cast_ne_zero.2 hp) f

lemma dLpNorm_pow_eq_sum_nnnorm {p : ℕ} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] ^ p = ∑ i, ‖f i‖₊ ^ p := by
  simpa using dLpNorm_rpow_eq_sum_nnnorm (Nat.cast_ne_zero.2 hp) f

lemma dL2Norm_sq_eq_sum_norm (f : α → E) : ‖f‖_[2] ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  simpa using dLpNorm_pow_eq_sum_norm two_ne_zero _

lemma dL2Norm_sq_eq_sum_nnnorm (f : α → E) : ‖f‖_[2] ^ 2 = ∑ i, ‖f i‖₊ ^ 2 := by
  simpa using dLpNorm_pow_eq_sum_nnnorm two_ne_zero _

lemma dL2Norm_eq_sum_norm (f : α → E) : ‖f‖_[2] = (∑ i, ‖f i‖ ^ 2) ^ (2⁻¹ : ℝ) := by
  simpa [sqrt_eq_rpow] using dLpNorm_eq_sum_norm two_ne_zero _

lemma dL2Norm_eq_sum_nnnorm (f : α → E) : ‖f‖_[2] = (∑ i, ‖f i‖₊ ^ 2) ^ (2⁻¹ : ℝ) := by
  simpa [sqrt_eq_rpow] using dLpNorm_eq_sum_nnnorm two_ne_zero _

lemma dL1Norm_eq_sum_norm (f : α → E) : ‖f‖_[1] = ∑ i, ‖f i‖ := by simp [dLpNorm_eq_sum_norm']
lemma dL1Norm_eq_sum_nnnorm (f : α → E) : ‖f‖_[1] = ∑ i, ‖f i‖₊ := by simp [dLpNorm_eq_sum_nnnorm']

omit [Fintype α]
variable [Finite α]

lemma dLinftyNorm_eq_iSup_nnnorm (f : α → E) : ‖f‖_[∞] = ⨆ i, ‖f i‖₊ := by
  cases isEmpty_or_nonempty α
  · simp
  · simp [dLpNorm, nnLinftyNorm_eq_essSup]

lemma dLinftyNorm_eq_iSup_norm (f : α → E) : ‖f‖_[∞] = ⨆ i, ‖f i‖ := by
  cases isEmpty_or_nonempty α
  · simp
  · simp [dLpNorm, nnLinftyNorm_eq_essSup]

lemma nnnorm_le_dLinftyNorm {i : α} : ‖f i‖₊ ≤ ‖f‖_[∞] := by
  rw [dLinftyNorm_eq_iSup_nnnorm]; exact le_ciSup (f := fun i ↦ ‖f i‖₊) (Finite.bddAbove_range _) i

lemma norm_le_dLinftyNorm {i : α} : ‖f i‖ ≤ ‖f‖_[∞] := by
  rw [dLinftyNorm_eq_iSup_norm]; exact le_ciSup (f := fun i ↦ ‖f i‖) (Finite.bddAbove_range _) i

@[simp] lemma dLpNorm_eq_zero (hp : p ≠ 0) : ‖f‖_[p] = 0 ↔ f = 0 := by
  simp [dLpNorm, nnLpNorm_eq_zero .of_discrete hp, ae_eq_top.2]

@[simp] lemma dLpNorm_pos (hp : p ≠ 0) : 0 < ‖f‖_[p] ↔ f ≠ 0 :=
  pos_iff_ne_zero.trans (dLpNorm_eq_zero hp).not

lemma dLpNorm_mono_real {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : ‖f‖_[p] ≤ ‖g‖_[p] :=
  nnLpNorm_mono_real .of_discrete h

omit [Finite α]
variable [Fintype α]

lemma dLpNorm_two_mul_sum_pow {ι : Type*} {n : ℕ} (hn : n ≠ 0) (s : Finset ι) (f : ι → α → ℂ) :
    ‖∑ i ∈ s, f i‖_[2 * n] ^ (2 * n) =
      ∑ x ∈ s ^^ n, ∑ y ∈ s ^^ n, ∑ a, (∏ i, conj (f (x i) a)) * ∏ i, f (y i) a :=
  calc
    _ = ∑ a, (‖∑ i ∈ s, f i a‖ : ℂ) ^ (2 * n) := by
      norm_cast
      rw [← dLpNorm_pow_eq_sum_norm (by positivity)]
      simp_rw [← sum_apply]
      norm_cast
    _ = ∑ a, (∑ i ∈ s, conj (f i a)) ^ n * (∑ j ∈ s, f j a) ^ n := by
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by simp_rw [sum_pow', sum_mul_sum, sum_comm (s := univ)]

end MeasureTheory

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory

private alias ⟨_, dLpNorm_pos_of_ne_zero⟩ := dLpNorm_pos

private lemma dLpNorm_pos_of_pos {α E : Type*} {_ : MeasurableSpace α} [DiscreteMeasurableSpace α]
    [Finite α] [NormedAddCommGroup E] [Preorder E] {p : ℝ≥0∞} {f : α → E}
    (hp : p ≠ 0) (hf : 0 < f) : 0 < ‖f‖_[p] := dLpNorm_pos_of_ne_zero hp hf.ne'

/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p]`. -/
@[positivity ‖_‖_[_]] def evalDLpNorm : PositivityExt where eval {u} α _z _p e := do
  match u, α, e with
  | 0, ~q(ℝ≥0), ~q(@dLpNorm $ι $E $instιmeas $instEnorm $p $f) =>
    let some pp := (← core q(inferInstance) q(inferInstance) p).toNonzero _ _ | failure
    try
      let _pE ← synthInstanceQ q(PartialOrder $E)
      assumeInstancesCommute
      let _ ← synthInstanceQ q(Fintype $ι)
      let _ ← synthInstanceQ q(DiscreteMeasurableSpace $ι)
      let some pf := (← core q(inferInstance) q(inferInstance) f).toNonzero _ _ | failure
      return .positive q(dLpNorm_pos_of_ne_zero $pp $pf)
    catch _ =>
      assumeInstancesCommute
      let some pf ← findLocalDeclWithType? q($f ≠ 0) | failure
      let pf : Q($f ≠ 0) := .fvar pf
      let _ ← synthInstanceQ q(Fintype $ι)
      let _ ← synthInstanceQ q(DiscreteMeasurableSpace $ι)
      return .positive q(dLpNorm_pos_of_ne_zero $pp $pf)
  | _ => throwError "not dLpNorm"

section Examples
section NormedAddCommGroup
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f : α → E}

example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < ‖f‖_[p] := by positivity
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < ‖f‖_[p] := by positivity

end NormedAddCommGroup

section Complex
variable [Fintype α] [DiscreteMeasurableSpace α] {f : α → ℂ}

example {p : ℝ≥0∞} (hp : p ≠ 0) (hf : f ≠ 0) : 0 < ‖f‖_[p] := by positivity
example {p : ℝ≥0∞} (hp : p ≠ 0) {f : α → ℝ} (hf : 0 < f) : 0 < ‖f‖_[p] := by positivity

end Complex
end Examples
end Mathlib.Meta.Positivity

/-! ### Hölder inequality -/

namespace MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q : ℝ≥0}
  {f g : α → ℝ}

lemma dLpNorm_rpow (hp : p ≠ 0) (hq : q ≠ 0) (hf : 0 ≤ f) :
    ‖f ^ (q : ℝ)‖_[p] = ‖f‖_[p * q] ^ (q : ℝ) := by
  cases nonempty_fintype α
  refine NNReal.rpow_left_injective (NNReal.coe_ne_zero.2 hp) ?_
  dsimp
  rw [← NNReal.rpow_mul, ← mul_comm, ← ENNReal.coe_mul, ← NNReal.coe_mul,
    dLpNorm_rpow_eq_sum_nnnorm hp, dLpNorm_rpow_eq_sum_nnnorm (mul_ne_zero hq hp)]
  ext
  simp only [Pi.pow_apply, NNReal.coe_sum, NNReal.coe_rpow, coe_nnnorm, norm_eq_abs,
    abs_rpow_of_nonneg (hf _), abs_nonneg, ← rpow_mul, NNReal.coe_mul]

lemma dLpNorm_pow (hp : p ≠ 0) {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) :
    ‖f ^ q‖_[p] = ‖f‖_[p * q] ^ q := by
  cases nonempty_fintype α
  refine NNReal.rpow_left_injective (NNReal.coe_ne_zero.2 hp) ?_
  dsimp
  rw [← NNReal.rpow_natCast_mul, ← mul_comm, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    ← NNReal.coe_natCast, ← NNReal.coe_mul, dLpNorm_rpow_eq_sum_nnnorm hp,
    dLpNorm_rpow_eq_sum_nnnorm (by positivity)]
  simp [← NNReal.rpow_natCast_mul]

lemma dL1Norm_rpow (hq : q ≠ 0) (hf : 0 ≤ f) : ‖f ^ (q : ℝ)‖_[1] = ‖f‖_[q] ^ (q : ℝ) := by
  simpa only [ENNReal.coe_one, one_mul] using dLpNorm_rpow one_ne_zero hq hf

lemma dL1Norm_pow {q : ℕ} (hq : q ≠ 0) (f : α → ℂ) : ‖f ^ q‖_[1] = ‖f‖_[q] ^ q := by
  simpa only [ENNReal.coe_one, one_mul] using dLpNorm_pow one_ne_zero hq f

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
  {p q : ℝ≥0} {f g : α → 𝕜}

lemma dLpNorm_eq_dL1Norm_rpow (hp : p ≠ 0) (f : α → 𝕜) :
    ‖f‖_[p] = ‖fun a ↦ ‖f a‖ ^ (p : ℝ)‖_[1] ^ (p⁻¹ : ℝ) := by
  cases nonempty_fintype α
  ext
  simp [dLpNorm_eq_sum_nnnorm hp, dL1Norm_eq_sum_nnnorm, abs_rpow_of_nonneg]

lemma dLpNorm_rpow' {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) (hq : q ≠ 0) (f : α → 𝕜) :
    ‖f‖_[p] ^ (q : ℝ) = ‖(fun a ↦ ‖f a‖) ^ (q : ℝ)‖_[p / q] := by
  lift p to ℝ≥0 using hp
  simp only [ne_eq, ENNReal.coe_eq_zero] at hp₀
  rw [← ENNReal.coe_div hq, dLpNorm_rpow (div_ne_zero hp₀ hq) hq (fun _ ↦ norm_nonneg _),
    dLpNorm_norm, ← ENNReal.coe_mul, div_mul_cancel₀ _ hq]

end Hoelder

section
variable {α : Type*} {mα : MeasurableSpace α}

@[simp]
lemma RCLike.dLpNorm_coe_comp [RCLike 𝕜] (p) (f : α → ℝ) : ‖((↑) : ℝ → 𝕜) ∘ f‖_[p] = ‖f‖_[p] := by
  simp only [← dLpNorm_norm (((↑) : ℝ → 𝕜) ∘ f), ← dLpNorm_norm f, Function.comp_apply,
    RCLike.norm_ofReal, Real.norm_eq_abs]

@[simp] lemma Complex.dLpNorm_coe_comp (p) (f : α → ℝ) : ‖((↑) : ℝ → ℂ) ∘ f‖_[p] = ‖f‖_[p] :=
  RCLike.dLpNorm_coe_comp ..

end
end MeasureTheory
