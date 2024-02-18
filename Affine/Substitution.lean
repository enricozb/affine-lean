import «Affine».Lemmas
import «Affine».Misc

namespace Lambda

/-- Replaces free occurrences of variable `x` with variable `y`. -/
def substᵥ (e : Lambda) (x y : ℕ) : Lambda :=
  match e with
  | .var x' => if x = x' then .var y else .var x'
  | .app e₁ e₂ => .app (e₁.substᵥ x y) (e₂.substᵥ x y)
  | .abs x' e => if x = x' then .abs x' e else .abs x' (e.substᵥ x y)

/-- Variable substitution preserves depth. Needed for `termination_by` in `substₑ`. -/
@[simp] theorem substᵥ_depth_eq (e : Lambda) (x y : ℕ) : (e.substᵥ x y).depth = e.depth := by
  match e with
  | .var x' => simp only [substᵥ, depth, apply_ite, ite_self]
  | .app e₁ e₂ => simp only [substᵥ, depth, substᵥ_depth_eq]
  | .abs x' e => simp only [substᵥ, apply_ite, depth, substᵥ_depth_eq, ite_self]

/-- Substitutes free occurrences of variable `x` in `e₁` with `e₂`. -/
def substₑ (e₁ : Lambda) (x : ℕ) (e₂ : Lambda) : Lambda :=
  match e₁ with
  | .var x' => if x = x' then e₂ else e₁
  | .app a₁ a₂ => .app (a₁.substₑ x e₂) (a₂.substₑ x e₂)
  | .abs x' e₁ =>
    if x = x' ∨ x ∉ e₁.free then
      .abs x' e₁
    else if x' ∈ e₂.free then
      let y := (e₁.vars ∪ e₂.free).fresh
      .abs y ((e₁.substᵥ x' y).substₑ x e₂)
    else
      .abs x' (e₁.substₑ x e₂)
termination_by e₁.depth

theorem substᵥ_count {e : Lambda} (hx : x ≠ z) (hy₁ : y ≠ z) (hy₂ : y ∉ e.vars) :
    (e.substᵥ x y).count z = e.count z := by
  match e with
  | .var x' =>
    simp_rw [substᵥ, apply_ite (count · z), count, if_neg hy₁.symm]
    by_cases hx' : x = x'
    · rw [if_pos hx', ← hx', if_neg hx.symm]
    · rw [if_neg hx']
  | .app a₁ a₂ =>
    simp only [vars, Finset.not_mem_union] at hy₂
    simp_rw [substᵥ, count, substᵥ_count hx hy₁ hy₂.left, substᵥ_count hx hy₁ hy₂.right]
  | .abs x' e =>
    simp only [vars, Finset.not_mem_union] at hy₂
    simp_rw [substᵥ, apply_ite (count · z), count, substᵥ_count hx hy₁ hy₂.left]
    by_cases hx' : x = x'
    · rw [if_pos hx']
    · rw [if_neg hx']

theorem substᵥ_free_not_mem_free {e : Lambda} (hx : x ∉ e.free) :
    (e.substᵥ x y).free = e.free := by
  match e with
  | .var x' =>
    simp only [free, Finset.mem_singleton] at hx
    simp only [substᵥ, if_neg hx]
  | .abs x' e =>
    simp only [free, Finset.mem_sdiff, not_and_or, not_not, Finset.mem_singleton] at hx
    simp only [substᵥ, free, apply_ite]
    refine' Or.elim hx (fun hxfree => _) (fun hx => _)
    · rw [substᵥ_free_not_mem_free hxfree, ite_self]
    · rw [if_pos hx]
  | .app e₁ e₂ =>
    simp only [free, Finset.not_mem_union] at hx
    have ⟨hx₁, hx₂⟩ := hx
    simp only [free, substᵥ_free_not_mem_free hx₁, substᵥ_free_not_mem_free hx₂]

theorem substᵥ_free_mem_free {e : Lambda} (he : e.is_affine) (hx : x ∈ e.free) (hy : y ∉ e.vars) :
    (e.substᵥ x y).free = e.free \ {x} ∪ {y} := by
  match e with
  | .var x' =>
    simp only [substᵥ, apply_ite, free, Finset.mem_singleton] at *
    simp only [hx, if_pos, Finset.sdiff_self, Finset.empty_union]
  | .abs x' e =>
    simp only [substᵥ, free, vars, is_affine_of_abs, Finset.mem_sdiff, Finset.mem_singleton,
      Finset.not_mem_union, apply_ite] at *
    have ⟨he, _⟩ := he
    have ⟨hxe, hxn⟩ := hx
    have ⟨hye, hyn⟩ := hy
    have hyx' : x' ∉ ({y} : Finset ℕ) := Finset.mem_singleton.not.mpr (fun h => hyn h.symm)
    rw [if_neg hxn, substᵥ_free_mem_free he hxe hye, Finset.union_sdiff_distrib,
      Finset.sdiff_singleton_eq_self hyx', Finset.sdiff_comm]
  | .app e₁ e₂ =>
    simp only [substᵥ, free, vars, is_affine_of_app, Finset.mem_union, Finset.not_mem_union,
      not_or] at *
    have ⟨hy₁, hy₂⟩ := hy
    have ⟨he₁, he₂, hfree₁₂⟩ := he
    refine' Or.elim hx (fun hxe₁ => _) (fun hxe₂ => _)
    · have hxe₂ : x ∉ e₂.free := (fun hxe₂ => Finset.inter_eq_empty hfree₁₂ ⟨hxe₁, hxe₂⟩)
      conv =>
        lhs
        rw [substᵥ_free_mem_free he₁ hxe₁ hy₁, substᵥ_free_not_mem_free hxe₂,
          ← Finset.sdiff_singleton_eq_self hxe₂, Finset.union_assoc, Finset.union_comm {y},
          ← Finset.union_assoc, ← Finset.union_sdiff_distrib]
    · have hxe₁ : x ∉ e₁.free := (fun hxe₁ => Finset.inter_eq_empty hfree₁₂ ⟨hxe₁, hxe₂⟩)
      conv =>
        lhs
        rw [substᵥ_free_mem_free he₂ hxe₂ hy₂, substᵥ_free_not_mem_free hxe₁,
          ← Finset.sdiff_singleton_eq_self hxe₁, ← Finset.union_assoc,
          ← Finset.union_sdiff_distrib]

theorem substᵥ_is_affine {e : Lambda} (he : e.is_affine) (hy : y ∉ e.vars) :
    (e.substᵥ x y).is_affine := by
  match e with
  | .var x' => simp only [substᵥ, apply_ite, is_affine, ite_self]
  | .abs x' e =>
    simp only [vars, Finset.mem_union, not_or, Finset.mem_singleton] at hy
    have ⟨he, hc⟩ := is_affine_of_abs.mp he
    by_cases hx : x = x'
    · simp_rw [substᵥ, if_pos hx, is_affine_of_abs, hc, he, and_self]
    · simp_rw [substᵥ, if_neg hx, is_affine_of_abs, substᵥ_is_affine he hy.left,
        substᵥ_count hx hy.right hy.left, hc, and_self]
  | .app a₁ a₂ =>
    simp only [vars, Finset.not_mem_union] at hy
    have ⟨hy₁, hy₂⟩ := hy
    have hy₁' : y ∉ a₁.free := fun hy₁' => hy₁ (Finset.mem_of_subset a₁.free_subset_vars hy₁')
    have hy₂' : y ∉ a₂.free := fun hy₂' => hy₂ (Finset.mem_of_subset a₂.free_subset_vars hy₂')
    have ⟨ha₁, ha₂, hfree₁₂⟩ := is_affine_of_app.mp he
    simp only [substᵥ, is_affine_of_app, substᵥ_is_affine ha₁ hy₁, substᵥ_is_affine ha₂ hy₂,
      true_and]
    by_cases hxa₁ : x ∈ a₁.free
    · have hxa₂ : x ∉ a₂.free := fun hxa₂ => Finset.inter_eq_empty hfree₁₂ ⟨hxa₁, hxa₂⟩
      rw [substᵥ_free_mem_free ha₁ hxa₁ hy₁, substᵥ_free_not_mem_free hxa₂,
        Finset.inter_union_singleton_cancel hy₂', ← Finset.sdiff_singleton_eq_self hxa₂,
        Finset.sdiff_inter_sdiff_cancel, hfree₁₂, Finset.empty_sdiff]
    · simp only [substᵥ_free_not_mem_free hxa₁]
      by_cases hxa₂ : x ∈ a₂.free
      · rw [substᵥ_free_mem_free ha₂ hxa₂ hy₂, Finset.inter_comm a₁.free,
          Finset.inter_union_singleton_cancel hy₁', ← Finset.sdiff_singleton_eq_self hxa₁,
          Finset.sdiff_inter_sdiff_cancel, Finset.inter_comm, hfree₁₂, Finset.empty_sdiff]
      · rw [substᵥ_free_not_mem_free hxa₂, hfree₁₂]

theorem substᵥ_size {e : Lambda} : (e.substᵥ x y).size = e.size := sorry

theorem substₑ_size_not_mem_free {e₁ e₂ : Lambda} (h : x ∉ e₁.free) :
    (substₑ e₁ x e₂).size = e₁.size := by sorry

theorem substₑ_size_lt {e₁ e₂ : Lambda} (h : e₁.is_affine) :
    (substₑ e₁ x e₂).size < 1 + size e₁ + size e₂ := by
  match e₁ with
  | .var x' =>
    simp only [substₑ, size, apply_ite, add_zero]
    by_cases hx : x = x'
    · simp only [if_pos hx, lt_one_add]
    · simp only [if_neg hx, add_pos_iff, zero_lt_one, true_or]
  | .app a₁ a₂ =>
    simp only [is_affine_of_app] at h
    have ⟨ha₁, ha₂, hfree₁₂⟩ := h
    simp only [substₑ, size]
    by_cases hx₁ : x ∈ a₁.free
    · have hx₂ : x ∉ a₂.free := fun hx₂ => Finset.inter_eq_empty hfree₁₂ ⟨hx₁, hx₂⟩
      rw [substₑ_size_not_mem_free hx₂, add_assoc, add_comm _ e₂.size, ← add_assoc, ← add_assoc,
        add_assoc _ _ a₁.size, add_comm e₂.size, ← add_assoc]
      apply add_lt_add_right
      exact substₑ_size_lt ha₁
    · rw [substₑ_size_not_mem_free hx₁, ← add_assoc, add_comm 1, add_assoc, add_assoc]
      apply add_lt_add_left
      simp only [← add_assoc, substₑ_size_lt ha₂]
  | .abs x' e₁ =>
    simp only [is_affine_of_abs] at h
    have ⟨he₁, _⟩ := h
    simp only [size, substₑ]
    by_cases hx : x = x' ∨ x ∉ e₁.free
    · rw [if_pos hx, size]
      calc
      1 + e₁.size ≤ (1 + e₁.size) + e₂.size := by simp only [le_add_iff_nonneg_right, zero_le]
      _ < 1 + ((1 + e₁.size) + e₂.size) := lt_one_add _
      _ = 1 + (1 + e₁.size) + e₂.size := by simp only [add_assoc]
    · simp_rw [if_neg hx, apply_ite size, size]
      rw [not_or, not_not] at hx
      by_cases hx' : x' ∈ e₂.free
      · have : (e₁.substᵥ x' (e₁.vars ∪ e₂.free).fresh).is_affine := by
          apply substᵥ_is_affine he₁
          simp only [free_eq, Finset.fresh_union_left, not_false_eq_true]
        rw [if_pos hx', add_assoc]
        have hinc := substₑ_size_lt this (e₂ := e₂) (x := x)
        rw [substᵥ_size] at hinc
        exact add_lt_add_left hinc _
      · rw [if_neg hx', add_assoc]
        exact add_lt_add_left (substₑ_size_lt he₁) _
termination_by e₁.depth


theorem substₑ_is_affine {e₁ e₂ : Lambda} (he₁ : e₁.is_affine) (he₂ : e₂.is_affine) (x : ℕ) :
    (e₁.substₑ x e₂).is_affine := by sorry

theorem substₑ_free {e₁ e₂ : Lambda} : (substₑ e₁ x e₂).free ⊆ e₁.free \ {x} ∪ e₂.free := by sorry

theorem substₑ_count {e₁ e₂ : Lambda} :
    (e₁.substₑ x' e₂).count x ≤ (if x = x' then 0 else e₁.count x) + e₂.count x := by
  sorry

end Lambda
