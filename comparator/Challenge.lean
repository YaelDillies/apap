import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.Finset.Density
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Challenge: human-auditable theorem statements

Imports only Mathlib. To audit: read this file and check that each statement
says what it claims. A passing comparator run then guarantees the APAP
library proves these statements using only `{propext, Quot.sound, Classical.choice}`.
-/

noncomputable section

namespace Comparator

theorem ff {G : Type u} [AddCommGroup G] [Fintype G] {A : Finset G} {q : ℕ} [Module (ZMod q) G]
    (hq₃ : 3 ≤ q) (hq : Nat.Prime q) (hA₀ : A.Nonempty) (hA : ThreeAPFree (↑A : Set G)) :
    ↑(Module.finrank (ZMod q) G) ≤ (2 ^ 148 * (1 + Real.log (↑A.dens)⁻¹) ^ 9 : ℝ) := sorry

end Comparator
