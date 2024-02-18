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

theorem substᵥ_size {e : Lambda} : (e.substᵥ x y).size = e.size := by
  match e with
  | .var x => simp only [size, substᵥ, apply_ite, ite_self]
  | .app e₁ e₂ => simp only [size, substᵥ, e₁.substᵥ_size, e₂.substᵥ_size]
  | .abs x e => simp only [size, substᵥ, apply_ite, e.substᵥ_size, ite_self]

theorem substₑ_not_mem_free {e₁ e₂ : Lambda} (h : x ∉ e₁.free) : substₑ e₁ x e₂ = e₁ := by
  match e₁ with
  | .var x' =>
    simp only [free, Finset.mem_singleton] at h
    simp only [substₑ, if_neg h]
  | .app a₁ a₂ =>
    simp only [free, Finset.not_mem_union] at h
    simp only [size, substₑ, substₑ_not_mem_free h.1, substₑ_not_mem_free h.2]
  | .abs x' e₁ =>
    simp only [free, Finset.mem_sdiff, not_and_or, not_not, Finset.mem_singleton] at h
    refine' Or.elim h (fun hve₁ => _) (fun hx' => _)
    · simp only [size, substₑ, if_pos (Or.inr hve₁)]
    · simp only [size, substₑ, if_pos (Or.inl hx')]

theorem substₑ_size_not_mem_free {e₁ e₂ : Lambda} (h : x ∉ e₁.free) :
    (substₑ e₁ x e₂).size = e₁.size := by rw [substₑ_not_mem_free h]

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

theorem substₑ_free {e₁ e₂ : Lambda} : (substₑ e₁ x e₂).free ⊆ e₁.free \ {x} ∪ e₂.free := by
  match e₁ with
  | .var x' =>
    simp only [free, substₑ, apply_ite]
    by_cases hx' : x = x'
    · simp only [if_pos hx', Finset.subset_union_right]
    · simp only [if_neg hx', Finset.sdiff_singleton_eq_self (Finset.mem_singleton.not.mpr hx'),
        Finset.subset_union_left]
  | .app a₁ a₂ =>
    simp only [free, substₑ, Finset.union_sdiff_distrib]
    rw [Finset.union_distrib]
    exact Finset.union_subset_union substₑ_free substₑ_free
  | .abs x' e₁ =>
    simp only [free, substₑ]
    by_cases h : x = x' ∨ x ∉ e₁.free
    · simp only [if_pos h, free]
      refine' Or.elim h (fun hx' => _) (fun hxe₁ => _)
      · rw [hx']
        intro v hv
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hv
        simp only [sdiff_idem, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
        exact Or.inl hv
      · intro v hv
        simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_union] at *
        exact Or.inl ⟨hv, (fun hvx => (hvx.symm ▸ hxe₁) hv.1)⟩
    · simp only [if_neg h]
      simp only [not_or, not_not] at h
      by_cases hx' : x' ∈ e₂.free
      · simp only [if_pos hx', free]
        intro v hv
        simp at *
        sorry
      · simp only [if_neg hx', free]
        intro v hv
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hv
        have hinc := e₁.substₑ_free (e₂ := e₂) (x := x)
        have hinc' := Finset.mem_of_subset substₑ_free hv.1
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at *
        refine' Or.elim hinc'
          (fun ⟨hve₁, hvnx⟩ => Or.inl ⟨⟨hve₁, hv.2⟩, hvnx⟩)
          Or.inr

theorem substₑ_is_affine {e₁ e₂ : Lambda} (he₁ : e₁.is_affine) (he₂ : e₂.is_affine) (x : ℕ) :
    (e₁.substₑ x e₂).is_affine := by
  match e₁ with
  | .var x' => simp only [is_affine, substₑ, apply_ite, he₂, ite_self]
  | .app a₁ a₂ =>
    simp only [is_affine_of_app] at he₁
    have ⟨ha₁, ha₂, hc⟩ := he₁
    simp only [is_affine_of_app, substₑ, substₑ_is_affine ha₁ he₂, substₑ_is_affine ha₂ he₂,
      true_and]
    sorry
  | .abs x e₁ => sorry

theorem substₑ_count {e₁ e₂ : Lambda} (he₁ : e₁.is_affine) :
    (e₁.substₑ x' e₂).count x ≤ (if x = x' then 0 else e₁.count x) + e₂.count x := by
  match e₁ with
  | .var y =>
    simp only [count, substₑ, apply_ite (count · x)]
    by_cases hx'y : x' = y
    · simp only [if_pos hx'y, le_add_iff_nonneg_left, zero_le]
    · simp only [if_neg hx'y]
      by_cases hxy : x = y
      · have hxx' : x ≠ x' := fun hxx' => hx'y (hxx' ▸ hxy)
        simp only [if_pos hxy, if_neg hxx', le_add_iff_nonneg_right, zero_le]
      · simp only [if_neg hxy, ite_self, zero_add, zero_le]
  | .app a₁ a₂ =>
    simp only [is_affine_of_app] at he₁
    simp only [substₑ, count]
    by_cases hxx' : x = x'
    · rw [if_pos hxx', zero_add, hxx']
      wlog hx' : x' ∈ a₁.free ∨ x' ∈ a₂.free
      · rw [not_or] at hx'
        have ⟨hx'₁, hx'₂⟩ := hx'
        simp only [substₑ_not_mem_free hx'₁, substₑ_not_mem_free hx'₂, count_not_mem_free hx'₁,
          count_not_mem_free hx'₂, zero_add, zero_le]

      refine' Or.elim hx' (fun hx'₁ => _) (fun hx'₂ => _)
      · have hx'₂ : x' ∉ a₂.free := fun hx'₂ => Finset.inter_eq_empty he₁.2.2 ⟨hx'₁, hx'₂⟩
        simp only [substₑ_not_mem_free hx'₂, substₑ_not_mem_free hx'₂, count_not_mem_free hx'₂,
          add_zero]
        have hinc := substₑ_count he₁.1 (e₂ := e₂) (x := x') (x' := x')
        rw [if_pos rfl, zero_add] at hinc
        exact hinc
      · have hx'₁ : x' ∉ a₁.free := fun hx'₁ => Finset.inter_eq_empty he₁.2.2 ⟨hx'₁, hx'₂⟩
        sorry

      sorry
    sorry
  | .abs x e₁ => sorry

end Lambda
