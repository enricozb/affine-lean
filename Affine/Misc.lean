import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Sort

theorem Nat.add_le_one {a b : ℕ} : a + b ≤ 1 → a = 0 ∨ b = 0 := by sorry

namespace Finset

def fresh (s : Finset ℕ) : ℕ :=
  if h : s.Nonempty then
    s.max' h + 1
  else
    0

@[simp] theorem fresh_empty : (∅ : Finset ℕ).fresh = 0 := by rfl

@[simp] theorem fresh_not_mem (s : Finset ℕ) : s.fresh ∉ s := by
  by_cases hs : s.Nonempty
  · simp_rw [fresh, dif_pos hs]
    intro hmax'
    have h := le_max' s _ hmax'
    simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero] at h
  · simp_rw [fresh, dif_neg hs, not_nonempty_iff_eq_empty.mp hs, not_mem_empty, not_false_eq_true]

@[simp] theorem fresh_singleton_ne (x : ℕ) : ({x} : Finset ℕ).fresh ≠ x := by
  simp only [fresh, singleton_nonempty, ↓reduceDite, max'_singleton, ne_eq,
    add_right_eq_self, not_false_eq_true]

@[simp] theorem fresh_sdiff {s : Finset ℕ} {x : ℕ} (h : (s \ {x}).fresh ≠ x) :
    (s \ {x}).fresh ∉ s := by
  wlog hx : x ∈ s
  · simp only [sdiff_singleton_eq_self hx, fresh_not_mem, not_false_eq_true]
  have hs := not_and_or.mp (mem_sdiff.not.mp (fresh_not_mem (s \ {x})))
  simp only [not_not, mem_singleton, h, or_false] at hs
  exact hs

@[simp] theorem fresh_union_left (s₁ s₂ : Finset ℕ) : (s₁ ∪ s₂).fresh ∉ s₁ :=
  (not_mem_union.mp (fresh_not_mem (s₁ ∪ s₂))).left

@[simp] theorem fresh_union_right (s₁ s₂ : Finset ℕ) : (s₁ ∪ s₂).fresh ∉ s₂ :=
  (not_mem_union.mp (fresh_not_mem (s₁ ∪ s₂))).right

end Finset
