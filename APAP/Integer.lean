module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Additive.AP.Three.Defs

open Finset Real

public section

theorem int :
    ∃ c > 0, ∃ C > 0, ∀ ⦃A : Finset ℕ⦄ ⦃N : ℕ⦄, A ⊆ range N → ThreeAPFree (α := ℕ) A →
      #A ≤ N / exp (c * log N ^ (12⁻¹ : ℝ)) := sorry
