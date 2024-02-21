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

theorem add_add_neq_zero {a b c : ℕ} (h : a + b + c ≠ 0) : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 := by
  by_contra h'
  simp only [ne_eq, not_or, not_not] at h'
  simp only [h'.1, h'.2.1, h'.2.2] at h
  contradiction

namespace Finset

theorem sdiff_subset_sdiff' [DecidableEq α] {s₁ s₂ : Finset α} (s₃ : Finset α) (h : s₁ ⊆ s₂) :
    s₁ \ s₃ ⊆ s₂ \ s₃ := by
  intro v hv
  simp only [mem_sdiff] at *
  exact ⟨mem_of_subset h hv.1, hv.2⟩

theorem sdiff_inter_comm [DecidableEq α] {s₁ s₂ s₃ : Finset α} :
    s₁ \ s₂ ∩ s₃ = (s₁ ∩ s₃) \ s₂ := by
  ext v
  simp only [mem_inter, mem_sdiff]
  simp_rw [and_comm (b := v ∉ s₂), and_assoc]

theorem union_inter_distrib [DecidableEq α] {s₁ s₂ s₃ : Finset α} :
    (s₁ ∪ s₂) ∩ s₃ = (s₁ ∩ s₃) ∪ (s₂ ∩ s₃) := by
  ext x
  simp [mem_inter, mem_union, or_and_right]

theorem sdiff_singleton_inter_cancel [DecidableEq α] {s₁ s₂ : Finset α} (h : x ∉ s₂) :
    s₁ \ {x} ∩ s₂ = s₁ ∩ s₂ := by
  ext v
  simp only [mem_inter, mem_sdiff, mem_singleton, and_congr_left_iff, and_iff_left_iff_imp]
  intro hvs₂ _ hvx
  exact h (hvx ▸ hvs₂)

theorem union_distrib [DecidableEq α] (s₁ s₂ s₃ : Finset α) :
    (s₁ ∪ s₂) ∪ s₃ = ((s₁ ∪ s₃) ∪ (s₂ ∪ s₃)) := by
  ext x
  simp only [mem_union]
  rw [or_assoc (b := x ∈ s₃), or_comm (a := x ∈ s₂) (b := x ∈ s₃), ← or_assoc (a := x ∈ s₃),
    or_self, or_comm (a := x ∈ s₃), or_assoc]

theorem inter_eq_empty [DecidableEq α] {s₁ s₂ : Finset α} (h : (s₁ ∩ s₂) = ∅) :
    ¬(x ∈ s₁ ∧ x ∈ s₂) :=
  fun hmem => not_mem_empty _ (h ▸ mem_inter.mpr hmem)

theorem union_inter_empty [DecidableEq α] {s₁ s₂ s₃ : Finset α} (h : (s₁ ∪ s₂) ∩ s₃ = ∅) :
    s₁ ∩ s₃ = ∅ ∧ s₂ ∩ s₃ = ∅ := by
  simp only [union_inter_distrib] at h
  exact Finset.union_eq_empty.mp h

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
