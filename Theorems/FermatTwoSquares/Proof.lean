import Theorems.FermatTwoSquares.A

/-!
# Fermat's theorem on sums of two squares — proof

Calibration (Tier 1): we do not cite `Nat.Prime.sq_add_sq`.

* "only if": squares are 0 or 1 mod 4, so a sum of two squares is 0, 1 or 2 mod 4;
  an odd p must then be 1 mod 4.
* "if": −1 is a square mod p (`ZMod.exists_sq_eq_neg_one_iff`), so p ∣ k² + 1 = (k + i)(k − i)
  in GaussianInt. p divides neither factor (look at the imaginary part), so p is not prime in GaussianInt;
  as GaussianInt is Euclidean, p is not irreducible, and then p = a² + b²
  (`GaussianInt.sq_add_sq_of_nat_prime_of_not_irreducible`).
-/

namespace TuriMath.FermatTwoSquares

open GaussianInt

/-- A square of an integer is 0 or 1 mod 4. -/
lemma sq_emod_four (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rcases Int.emod_two_eq_zero_or_one x with h | h
  · obtain ⟨k, rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero h
    left; ring_nf; omega
  · have : x = 2 * (x / 2) + 1 := by omega
    rw [this]; right; ring_nf; omega

/-- "only if": an odd sum of two integer squares is 1 mod 4. -/
lemma mod_four_of_sq_add_sq (p : ℕ) (hodd : Odd p) (x y : ℤ)
    (h : (p : ℤ) = x ^ 2 + y ^ 2) : p % 4 = 1 := by
  have h2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hx := sq_emod_four x
  have hy := sq_emod_four y
  have : ((p : ℤ) % 4) = (x ^ 2 + y ^ 2) % 4 := by rw [h]
  omega

/-- "if": a prime p with p % 4 = 1 is a sum of two integer squares. -/
lemma sq_add_sq_of_mod_four (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 1) :
    ∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2 := by
  have := Fact.mk hp
  obtain ⟨m, hm⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  -- p ∣ k² + 1 in ℤ, with k = m.val
  set k : ℤ := (m.val : ℤ)
  have hdvd : (p : ℤ) ∣ k ^ 2 + 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [k, ZMod.natCast_val, ZMod.cast_id', id]
    rw [sq, ← hm]; ring
  -- p is not irreducible in GaussianInt
  have hnirr : ¬ Irreducible ((p : ℕ) : GaussianInt) := by
    intro hirr
    have hprime : Prime ((p : ℕ) : GaussianInt) := hirr.prime
    have hprod : ((p : ℕ) : GaussianInt) ∣ (⟨k, 1⟩ : GaussianInt) * ⟨k, -1⟩ := by
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : GaussianInt), ?_⟩
      ext <;> simp at * ; nlinarith [hc]
    have hp1 : ¬ ((p : ℤ) ∣ 1) := by
      rw [Int.natCast_dvd_ofNat]; exact hp.one_lt.ne' ∘ Nat.dvd_one.mp
    rcases hprime.dvd_or_dvd hprod with h | h
    · have := ((Zsqrtd.intCast_dvd (p : ℤ) _).mp (by exact_mod_cast h)).2
      exact hp1 (by simpa using this)
    · have := ((Zsqrtd.intCast_dvd (p : ℤ) _).mp (by exact_mod_cast h)).2
      exact hp1 (by simpa using this)
  obtain ⟨a, b, hab⟩ := sq_add_sq_of_nat_prime_of_not_irreducible p hnirr
  exact ⟨a, b, by exact_mod_cast hab.symm⟩

theorem main : A.Statement := by
  intro p hp hodd
  constructor
  · rintro ⟨x, y, h⟩
    exact mod_four_of_sq_add_sq p hodd x y h
  · intro h
    exact sq_add_sq_of_mod_four p hp h

end TuriMath.FermatTwoSquares
