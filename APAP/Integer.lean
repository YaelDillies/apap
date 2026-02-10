module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.AP.Three.Defs

open Finset Real

public section

theorem int {A : Finset ℕ} {N : ℕ} (hAN : A ⊆ range N) (hA : ThreeAPFree (α := ℕ) A) :
    ∃ c > 0, #A ≤ N / exp (- c * log N ^ (12⁻¹ : ℝ)) := sorry
