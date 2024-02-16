import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Lattice

theorem Nat.add_le_one {a b : ℕ} : a + b ≤ 1 → a = 0 ∨ b = 0 := by sorry

def Finset.fresh (s : Finset ℕ) : ℕ :=
  if h : s.Nonempty then
    s.max' h + 1
  else
    0
