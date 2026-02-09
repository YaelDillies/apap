import APAP.Prereqs.Bohr.Basic

open AddChar Complex Function
open scoped NNReal

namespace BohrSet
variable {G : Type*} [AddCommGroup G] [Finite G] {B : BohrSet G} {x : G}

/-- A Bohr set `B` is *regular* if the dilates of `B` by numbers close to `1` are of comparable size
to `B`. -/
structure IsRegular (B : BohrSet G) : Prop where
  le_card_smul (κ : ℝ) (hκ₀ : 0 ≤ κ) (hκ : κ ≤ B.rank / 100) :
    (1 - 100 * B.rank * κ) * Nat.card B ≤ Nat.card ↥((1 - κ) • B)
  card_smul_le (κ : ℝ) (hκ₀ : 0 ≤ κ) (hκ : κ ≤ B.rank / 100) :
    Nat.card ↥((1 + κ) • B) ≤ (1 + 100 * B.rank * κ) * Nat.card B

/-- **Bohr Set Regularity**. Any Bohr set can be dilated by a small amount to become a regular Bohr
set. -/
lemma regularity (B : BohrSet G) : ∃ ρ : ℝ, 2⁻¹ ≤ ρ ∧ ρ ≤ 1 ∧ (ρ • B).IsRegular := sorry

end BohrSet
