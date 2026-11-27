import Mathlib

/-!
# Fermat's theorem on sums of two squares — statement B (Gauss)

Source (Wikipedia, lead, retrieved 2026-11-26):
> an odd prime p can be expressed as p = x² + y², with x and y integers,
> if and only if p ≡ 1 (mod 4).

Mapping, source → Lean:
* "an odd prime p"                  → `p : ℕ`, `Nat.Prime p`, `p % 2 = 1`
* "can be expressed as p = x² + y²" → `∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2`
* "with x and y integers"           → `x y : ℤ` (signs and zero allowed, as in the source)
* "if and only if"                  → `↔` (both directions)
* "p ≡ 1 (mod 4)"                   → `p % 4 = 1` (remainder of the natural number p on division by 4)

Elementary phrasing on purpose: oddness and the congruence are written as `%` remainders
on `ℕ`, not via `Odd`, `Nat.ModEq` or `ZMod`.
-/

namespace TuriMath.FermatTwoSquares.B

/-- For every odd prime `p`: `p` is a sum of two integer squares iff `p % 4 = 1`. -/
def Statement : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 2 = 1 →
    ((∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2) ↔ p % 4 = 1)

/-! ## Sanity section: the hypotheses can all hold at once -/

/-- `p = 5` is an odd prime. -/
example : Nat.Prime 5 ∧ 5 % 2 = 1 := ⟨by norm_num, by norm_num⟩

/-- `p = 3` is an odd prime (the "no" side is inhabited too). -/
example : Nat.Prime 3 ∧ 3 % 2 = 1 := ⟨by norm_num, by norm_num⟩

/-! ## Concrete cases -/

/-- p = 5: 5 = 1² + 2², and 5 % 4 = 1. Both sides of the iff hold. -/
example : (∃ x y : ℤ, ((5 : ℕ) : ℤ) = x ^ 2 + y ^ 2) ∧ 5 % 4 = 1 :=
  ⟨⟨1, 2, by norm_num⟩, by norm_num⟩

/-- p = 13: 13 = 2² + 3² (also with signs: (-2)² + 3²), and 13 % 4 = 1. -/
example : (∃ x y : ℤ, ((13 : ℕ) : ℤ) = x ^ 2 + y ^ 2) ∧ 13 % 4 = 1 :=
  ⟨⟨-2, 3, by norm_num⟩, by norm_num⟩

/-- p = 3: 3 % 4 = 3 ≠ 1, and 3 is not x² + y² over ℤ (both |x|, |y| ≤ 1 would be forced). -/
example : ¬ (∃ x y : ℤ, ((3 : ℕ) : ℤ) = x ^ 2 + y ^ 2) ∧ ¬ (3 % 4 = 1) := by
  refine ⟨?_, by norm_num⟩
  rintro ⟨x, y, h⟩
  push_cast at h
  have hx : x ^ 2 ≤ 3 := by nlinarith [sq_nonneg y]
  have hy : y ^ 2 ≤ 3 := by nlinarith [sq_nonneg x]
  have hx' : -1 ≤ x ∧ x ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  have hy' : -1 ≤ y ∧ y ≤ 1 := ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hx1, hx2⟩ := hx'
  obtain ⟨hy1, hy2⟩ := hy'
  interval_cases x <;> interval_cases y <;> simp_all

/-- p = 2 is excluded by the oddness hypothesis (2 = 1² + 1² but 2 % 4 = 2). -/
example : ¬ (2 % 2 = 1) := by decide

end TuriMath.FermatTwoSquares.B
