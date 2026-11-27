import Mathlib

/-!
# Fermat's theorem on sums of two squares — statement A (Noether)

Source (issue TuriMath/fermat-two-squares#1, Wikipedia lead, retrieved 2026-11-26):
> an odd prime p can be expressed as p = x² + y², with x and y integers,
> if and only if p ≡ 1 (mod 4).
-/

namespace TuriMath.FermatTwoSquares.A

/-- Fermat's theorem on sums of two squares.

Mapping from the source quote to the Lean:
* "an odd prime p"              ↦ `∀ p : ℕ, p.Prime → Odd p → …`
  (ℕ because Mathlib's `Nat.Prime` lives there; "odd" is Mathlib's `Odd`, not a home-made `p ≠ 2`)
* "can be expressed as p = x² + y², with x and y integers"
                                ↦ `∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2`
  (x, y range over ℤ as the source says; p is cast to ℤ so the equation is in ℤ)
* "if and only if"              ↦ `↔` (both directions)
* "p ≡ 1 (mod 4)"               ↦ `p ≡ 1 [MOD 4]` (Mathlib's `Nat.ModEq`)
-/
def Statement : Prop :=
  ∀ p : ℕ, p.Prime → Odd p →
    ((∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2) ↔ p ≡ 1 [MOD 4])

/-! ## Sanity section

The hypotheses are `p.Prime` and `Odd p`. They hold together, e.g. for `p = 5`. -/

example : ∃ p : ℕ, p.Prime ∧ Odd p := ⟨5, by norm_num, by decide⟩

/-- Both sides of the `↔` are satisfiable under the hypotheses (p = 5 = 1² + 2²),
so the statement is not about an empty case. -/
example : (5 : ℕ).Prime ∧ Odd 5 ∧ (∃ x y : ℤ, ((5 : ℕ) : ℤ) = x ^ 2 + y ^ 2) ∧ 5 ≡ 1 [MOD 4] :=
  ⟨by norm_num, by decide, ⟨1, 2, by norm_num⟩, by decide⟩

/-- Both sides can also fail under the hypotheses (p = 3), so the `↔` is not trivially true
in one direction. -/
example : (3 : ℕ).Prime ∧ Odd 3 ∧ ¬ (3 ≡ 1 [MOD 4]) :=
  ⟨by norm_num, by decide, by decide⟩

end TuriMath.FermatTwoSquares.A
