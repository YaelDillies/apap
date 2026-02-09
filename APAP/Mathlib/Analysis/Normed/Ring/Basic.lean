import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.NoncommRing

variable {R : Type*} [SeminormedRing R] {a b c : R}

lemma norm_one_sub_mul (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ := by
  calc ‖c - a * b‖ = ‖(c - a) + a * (1 - b)‖ := by noncomm_ring
    _ ≤ ‖c - a‖ + ‖1 - b‖ := by grw [norm_add_le, norm_mul_le, ha, one_mul]

lemma norm_one_sub_mul' (hb : ‖b‖ ≤ 1) : ‖c - a * b‖ ≤ ‖1 - a‖ + ‖c - b‖ :=
  (norm_one_sub_mul (R := Rᵐᵒᵖ) hb).trans_eq (add_comm _ _)

lemma nnnorm_one_sub_mul (ha : ‖a‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖c - a‖₊ + ‖1 - b‖₊ :=
  norm_one_sub_mul ha

lemma nnnorm_one_sub_mul' (hb : ‖b‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖1 - a‖₊ + ‖c - b‖₊ :=
  norm_one_sub_mul' hb
