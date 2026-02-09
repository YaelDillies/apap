import Mathlib.Tactic.Positivity

/-!
# A bunch of dummy lemmas to be used in broken `positivity` extensions

The lack of pattern-matching in Qq means that we currently cannot write sound `positivity`
extensions that work on non-generic nor concrete types (eg `α → β`). So for the time being we
replace them by unsound ones using the following dummy lemmas.

We want to avoid
* breaking existing proofs
* accidentally making the proofs think they don't need some positivity assumption
-/

namespace Mathlib.Meta.Positivity
variable {α : Type*} [Zero α] [PartialOrder α] {a b c : α}

lemma dummy_pos : 0 < a := sorry
lemma dummy_nng : 0 ≤ a := sorry
lemma dummy_nzr : a ≠ 0 := sorry

lemma dummy_pos_of_pos (ha : 0 < a) : 0 < b := sorry
lemma dummy_pos_of_nzr (ha : a ≠ 0) : 0 < b := sorry
lemma dummy_nng_of_nng (ha : 0 ≤ a) : 0 ≤ b := sorry
lemma dummy_nzr_of_nzr (ha : a ≠ 0) : b ≠ 0 := sorry

lemma dummy_pos_of_pos_pos (ha : 0 < a) (hb : 0 < b) : 0 < c := sorry
lemma dummy_nng_of_pos_nng (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ c := sorry
lemma dummy_nng_of_nng_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ c := sorry
lemma dummy_nng_of_nng_nng (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ c := sorry
lemma dummy_nzr_of_pos_nzr (ha : 0 < a) (hb : b ≠ 0) : c ≠ 0 := sorry
lemma dummy_nzr_of_nzr_pos (ha : a ≠ 0) (hb : 0 < b) : c ≠ 0 := sorry
lemma dummy_nzr_of_nzr_nzr (ha : a ≠ 0) (hb : b ≠ 0) : c ≠ 0 := sorry

end Mathlib.Meta.Positivity
