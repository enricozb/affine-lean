import «Affine».Lemmas
import «Affine».Misc

open Finset

namespace Affine

theorem substᵥ_app_free {e₁ : Affine vs₁} {e₂ : Affine vs₂} (x y : ℕ) (h : e₁.free ∩ e₂.free = ∅) :
    (if x ∈ e₁.free then e₁.free \ {x} ∪ {y} else e₁.free) ∪
    (if x ∈ e₂.free then e₂.free \ {x} ∪ {y} else e₂.free) =
    (if x ∈ (app e₁ e₂ h).free then (e₁.free ∪ e₂.free) \ {x} ∪ {y} else e₁.free ∪ e₂.free) := by
  simp only [mem_union]
  wlog hx : x ∈ e₁.free ∨ x ∈ e₂.free
  · rw [if_neg hx, if_neg (not_or.mp hx).left, if_neg (not_or.mp hx).right]

  by_cases hx₁ : x ∈ e₁.free
  · have hx₂ : x ∉ e₂.free := fun hx₂ => not_mem_empty _ (h ▸ mem_inter.mpr ⟨hx₁, hx₂⟩)
    rw [if_pos hx, if_pos hx₁, if_neg hx₂, union_sdiff_distrib, sdiff_singleton_eq_self hx₂,
      union_assoc, union_comm {y}, union_assoc]
  · have hx₂ : x ∈ e₂.free := Or.elim hx (absurd · hx₁) id
    rw [if_pos hx, if_neg hx₁, if_pos hx₂, union_sdiff_distrib, sdiff_singleton_eq_self hx₁,
      union_assoc]

theorem substᵥ_abs_free {e : Affine vs} (x y x' : ℕ) :
  (if x ∈ e.free then e.free \ {x} ∪ {y} else e.free) \ {x'} =
  (if x ∈ e.free then (e.free \ {x'}) \ {x} ∪ {y} else e.free \ {x'}) := by sorry

/-- Replaces free occurrences of variable `x` with variable `y`. -/
def substᵥ (e : Affine vs) (x y : ℕ) (hy : y ∉ vs) :
    Affine (if x ∈ e.free then vs \ {x} ∪ {y} else vs) :=
  match e with
  | .var x' =>
    if h : x = x' then by
      simp only [h, free, mem_singleton, sdiff_self, empty_union, if_pos]
      exact .var y

    else by
      simp only [free, mem_singleton, if_neg h]
      exact .var x'

  | .app e₁ e₂ h => by
    simp only [not_mem_union] at hy
    rw [← substᵥ_app_free]
    exact .app (e₁.substᵥ x y hy.1) (e₂.substᵥ x y hy.2) sorry

  | .abs x' e =>
    if h : x = x' then by
      simp only [free, mem_sdiff, mem_singleton, h, not_true, and_false, if_false]
      exact .abs x' e

    else by
      simp_rw [free, mem_sdiff, mem_singleton, h, not_false_eq_true, and_true]
      rw [← substᵥ_abs_free]
      exact .abs x' (e.substᵥ x y sorry)

@[simp] theorem size_substᵥ {e : Affine vs} (hy : y ∉ e.free) :
    (e.substᵥ x y hy).size = e.size := by
  sorry

/-- Free variables transformation when propagating substitution in `(abs x e)`. -/
theorem substₑ_abs_free {e₁ : Affine vs} (vs₂ : Finset ℕ) (hxx' : x ∈ e₁.free ∧ x ≠ x') :
    ((if x ∈ (e₁.substᵥ x' (e₁.vars ∪ vs₂).fresh (fresh_vars_not_mem_free e₁ vs₂)).free then
        (if x' ∈ e₁.free then e₁.free \ {x'} ∪ {(e₁.vars ∪ vs₂).fresh} else e₁.free) \ {x} ∪ vs₂
      else if x' ∈ e₁.free then
        e₁.free \ {x'} ∪ {(e₁.vars ∪ vs₂).fresh}
      else
        e₁.free
    ) \ {(e₁.vars ∪ vs₂).fresh}) = ((e₁.free \ {x'}) \ {x} ∪ vs₂) := by
  simp_rw [free, apply_ite (x ∈ ·), mem_union, mem_sdiff, mem_singleton, hxx',
    not_false_eq_true, true_and, true_or, ite_self, if_true]
  have hfresh₁ : (e₁.vars ∪ vs₂).fresh ∉ e₁.vars := fresh_union_left _ _
  have hfresh₂ : (e₁.vars ∪ vs₂).fresh ∉ e₁.free := hfresh₁ ∘ mem_of_subset e₁.free_subset_vars
  have hfresh₃ : (e₁.vars ∪ vs₂).fresh ∉ vs₂ := fresh_union_right _ _
  by_cases hx' : x' ∈ e₁.free
  · simp_rw [if_pos hx', union_sdiff_distrib,
      sdiff_comm (t := {(e₁.vars ∪ vs₂).fresh}),
      sdiff_self, bot_eq_empty, empty_sdiff, union_empty, sdiff_singleton_eq_self hfresh₂,
      sdiff_singleton_eq_self hfresh₃]
  · simp_rw [if_neg hx', union_sdiff_distrib, sdiff_comm (t := {(e₁.vars ∪ vs₂).fresh}),
      sdiff_singleton_eq_self hfresh₂, sdiff_singleton_eq_self hfresh₃]
    rw [← sdiff_singleton_eq_self hx']

/-- Free variables transformation when propagating substitution in `(app a₁ a₂)`. -/
theorem substₑ_app_free (a₁ : Affine vs₁) (a₂ : Affine vs₂) (vs₃ : Finset ℕ) (x : ℕ)
    (h : a₁.free ∩ a₂.free = ∅) :
    (if x ∈ a₁.free then a₁.free \ {x} ∪ vs₃ else a₁.free) ∪
    (if x ∈ a₂.free then a₂.free \ {x} ∪ vs₃ else a₂.free) =
    if x ∈ a₁.free ∪ a₂.free then (a₁.free ∪ a₂.free) \ {x} ∪ vs₃ else a₁.free ∪ a₂.free := by
  wlog h₁₂ : x ∈ a₁.free ∨ x ∈ a₂.free
  · have ⟨h₁, h₂⟩ := not_or.mp h₁₂
    simp only [if_neg h₁, if_neg h₂, if_neg h₁₂, mem_union]
  by_cases h₁ : x ∈ a₁.free
  · have h₂ : x ∉ a₂.free := ((h.symm ▸ not_mem_empty _) $ mem_inter.mpr ⟨h₁, ·⟩)
    simp_rw [if_pos h₁, if_neg h₂, mem_union, if_pos h₁₂,
      union_sdiff_distrib, sdiff_singleton_eq_self h₂, union_assoc, union_comm]
  · have h₂ : x ∈ a₂.free := Or.elim h₁₂ (absurd . h₁) id
    simp_rw [if_neg h₁, if_pos h₂, mem_union, if_pos h₁₂, union_sdiff_distrib,
      sdiff_singleton_eq_self h₁, union_assoc]

/-- Affinity condition when propagating substitution in `(app a₁ a₂)`. -/
theorem substₑ_app_affine {a₁ : Affine vs₁} {a₂ : Affine vs₂} (vs₃ : Finset ℕ) (x : ℕ)
    (h : a₁.free ∩ a₂.free = ∅) (h₁₃ : a₁.free \ {x} ∩ vs₃ = ∅) (h₂₃ : a₂.free \ {x} ∩ vs₃ = ∅) :
    (if x ∈ a₁.free then a₁.free \ {x} ∪ vs₃ else a₁.free) ∩
    (if x ∈ a₂.free then a₂.free \ {x} ∪ vs₃ else a₂.free) = ∅ := by
  wlog h₁₂ : x ∈ a₁.free ∨ x ∈ a₂.free
  · have ⟨h₁, h₂⟩ := not_or.mp h₁₂
    simp only [if_neg h₁, if_neg h₂, h]
  by_cases h₁ : x ∈ a₁.free
  · have h₂ : x ∉ a₂.free := ((h.symm ▸ not_mem_empty _) $ mem_inter.mpr ⟨h₁, ·⟩)
    rw [if_pos h₁, if_neg h₂, union_inter_distrib, sdiff_inter_comm, h, empty_sdiff,
      empty_union, inter_comm, ← sdiff_singleton_eq_self h₂, h₂₃]
  · have h₂ : x ∈ a₂.free := Or.elim h₁₂ (absurd . h₁) id
    rw [if_neg h₁, if_pos h₂, inter_comm, union_inter_distrib, sdiff_inter_comm, inter_comm, h,
      empty_sdiff, empty_union, inter_comm, ← sdiff_singleton_eq_self h₁, h₁₃]

/-- Substitutes free occurrences of variable `x` in `e₁` with `e₂`. -/
def substₑ (e₁ : Affine vs₁) (x : ℕ) (e₂ : Affine vs₂) (he : e₁.free \ {x} ∩ e₂.free = ∅) :
    Affine (if x ∈ e₁.free then vs₁ \ {x} ∪ e₂.free else vs₁) :=

  match e₁ with
  | .var x' =>
    if h : x = x' then by
      simp only [h, mem_singleton, if_true, sdiff_self, empty_union, bot_eq_empty]
      exact e₂

    else by
      simp only [mem_singleton, if_neg h]
      exact .var x'

  | .app a₁ a₂ h => by
    rw [← substₑ_app_free a₁ a₂ e₂.free x h]
    rw [free, union_sdiff_distrib, union_inter_distrib, union_eq_empty] at he
    exact .app (a₁.substₑ x e₂ he.1) (a₂.substₑ x e₂ he.2) (substₑ_app_affine e₂.free x h he.1 he.2)

  | .abs x' e₁ =>
    if hxx' : x = x' ∨ x ∉ e₁.free then by
      rw [← not_not (a := x = x'), ← not_and_or, and_comm] at hxx'
      simp only [mem_sdiff, mem_singleton, if_neg hxx']
      exact .abs x' e₁

    else if hx'e₂ : x' ∈ e₂.free then by
      rw [not_or, not_not, and_comm] at hxx'
      simp only [mem_sdiff, mem_singleton, if_pos hxx', ← substₑ_abs_free e₂.free hxx']
      let y := (e₁.vars ∪ e₂.free).fresh
      exact .abs y ((e₁.substᵥ x' y _).substₑ x e₂ sorry)

    else by
      rw [not_or, not_not, and_comm] at hxx'
      simp only [mem_sdiff, mem_singleton, if_pos hxx']
      have hfree : (if x ∈ e₁.free then e₁.free \ {x} ∪ e₂.free else e₁.free) \ {x'} =
          (e₁.free \ {x'}) \ {x} ∪ e₂.free := by
        rw [if_pos hxx'.left, union_sdiff_distrib, sdiff_comm, sdiff_singleton_eq_self hx'e₂]
      rw [← hfree]

      exact .abs x' (e₁.substₑ x e₂ sorry)

termination_by e₁.size

end Affine
