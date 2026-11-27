import Theorems.FermatTwoSquares.A
import Theorems.FermatTwoSquares.B

namespace TuriMath.FermatTwoSquares

/-- Statements A and B agree: the hypotheses and conclusions are matched one for one
(`Odd p` ↔ `p % 2 = 1`, `p ≡ 1 [MOD 4]` ↔ `p % 4 = 1`). -/
theorem equiv : A.Statement ↔ B.Statement := by
  unfold A.Statement B.Statement
  constructor
  · intro h p hp h2
    have ho : Odd p := Nat.odd_iff.mpr h2
    rw [h p hp ho]
    exact ⟨fun h => h, fun h => h⟩
  · intro h p hp ho
    have h2 : p % 2 = 1 := Nat.odd_iff.mp ho
    rw [h p hp h2]
    exact ⟨fun h => h, fun h => h⟩

end TuriMath.FermatTwoSquares
