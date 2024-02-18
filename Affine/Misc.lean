import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Finset.Sort

theorem ite_le_ite {P : Prop} [Decidable P] {a b c d : ℕ} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    (if P then a else c) ≤ (if P then b else d) := by
  by_cases h : P
  · simp_rw [if_pos h, h₁]
  · simp_rw [if_neg h, h₂]

theorem ite_lt {P : Prop} [Decidable P] {a b c : ℕ} (ha : a < c) (hb : b < c) :
    (if P then a else b) < c := by
  by_cases h : P
  · simp_rw [if_pos h, ha]
  · simp_rw [if_neg h, hb]

namespace Finset

theorem inter_eq_empty [DecidableEq α] {s₁ s₂ : Finset α} (h : (s₁ ∩ s₂) = ∅) :
    ¬(x ∈ s₁ ∧ x ∈ s₂) :=
  fun hmem => not_mem_empty _ (h ▸ mem_inter.mpr hmem)

theorem sdiff_comm [DecidableEq α] {s u t : Finset α} : (s \ u) \ t = (s \ t) \ u := by
  ext v
  simp only [mem_sdiff]
  exact Iff.intro (fun ⟨⟨hs, hu⟩, ht⟩ => ⟨⟨hs, ht⟩, hu⟩) (fun ⟨⟨hs, ht⟩, hu⟩ => ⟨⟨hs, hu⟩, ht⟩)

theorem inter_union_singleton_cancel [DecidableEq α] {s₁ s₂ : Finset α} (hx : x ∉ s₂) :
    (s₁ ∪ {x}) ∩ s₂ = s₁ ∩ s₂ := by
  ext v
  simp only [mem_inter, mem_union, mem_singleton, and_congr_left_iff, or_iff_left_iff_imp]
  intro hvs₁ hvx
  absurd hx (hvx ▸ hvs₁)
  simp only [not_false_eq_true]

theorem sdiff_inter_sdiff_cancel [DecidableEq α] (s₁ s₂ u : Finset α) :
    (s₁ \ u) ∩ (s₂ \ u) = (s₁ ∩ s₂) \ u := by
  ext v
  simp only [mem_inter, mem_sdiff]
  exact Iff.intro
    (fun ⟨⟨hvs₁, hvnu⟩, hvs₂, _⟩ => ⟨⟨hvs₁, hvs₂⟩, hvnu⟩)
    (fun ⟨⟨hvs₁, hvs₂⟩, hvnu⟩ => ⟨⟨hvs₁, hvnu⟩, hvs₂, hvnu⟩)

/-- A "fresh" value not in `Finset ℕ`. -/
def fresh (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.max' h + 1 else 0

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
