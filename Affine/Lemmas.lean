import «Affine».Affine
import «Affine».Lambda
import «Affine».Misc

namespace Lambda

theorem free_subset_vars (e : Lambda) : e.free ⊆ e.vars := by
  match e with
  | .var x => rfl
  | .app e₁ e₂ => simp only [free, vars, free_subset_vars, Finset.union_subset_union]
  | .abs x e =>
    simp only [free, vars]
    exact Finset.Subset.trans
      (Finset.sdiff_subset _ _)
      (Finset.Subset.trans e.free_subset_vars (Finset.subset_union_left e.vars {x}))

@[simp] theorem abs_depth : e.depth < (abs x e).depth := by simp only [depth, lt_one_add]

@[simp] theorem app_depth_left : e₁.depth < (app e₁ e₂).depth := by
  simp only [depth, lt_of_le_of_lt (le_max_left e₁.depth e₂.depth) (lt_one_add _)]

@[simp] theorem app_depth_right : e₂.depth < (app e₁ e₂).depth := by
  simp_rw [depth, lt_of_le_of_lt (le_max_right e₁.depth e₂.depth) (lt_one_add _)]

@[simp] theorem app_abs_depth : e₁.depth < (app (abs x' e₁) e₂).depth := by
  simp only [depth]
  calc
  e₁.depth < 1 + e₁.depth := lt_one_add _
  _ ≤ max (1 + e₁.depth) e₂.depth := le_max_left _ _
  _ < 1 + max (1 + e₁.depth) e₂.depth := lt_one_add _

@[simp] theorem is_affine_of_var : (var x).is_affine := by
  simp only [is_affine]

@[simp] theorem is_affine_of_abs : (abs x e).is_affine ↔ is_affine e ∧ count e x ≤ 1 := by
  simp only [is_affine, decide_eq_true_eq]

@[simp] theorem is_affine_of_app :
    (app e₁ e₂).is_affine ↔ is_affine e₁ ∧ is_affine e₂ ∧ e₁.free ∩ e₂.free = ∅ := by
  simp only [is_affine, decide_eq_true_eq]

@[simp] theorem vars_var : (var x).vars = {x} := by rfl

@[simp] theorem abs_var : (abs x e).vars = e.vars ∪ {x} := by rfl

@[simp] theorem app_var : (app e₁ e₂).vars = e₁.vars ∪ e₂.vars := by rfl

/-- Variables that are not free in `e` have count of `0`. -/
theorem count_not_mem_free {e : Lambda} {x : ℕ} (h : x ∉ e.free) : e.count x = 0 := by
  match e with
  | .var x' => simp only [count, if_neg (Finset.not_mem_singleton.mp h)]
  | .abs x' e =>
    simp only [free] at h
    have hx : x ∉ e.free ∨ ¬x ∉ {x'} := not_and_or.mp (Finset.mem_sdiff.not.mp h)
    by_cases hx' : x = x'
    · simp only [count, if_pos hx']
    · simp only [Finset.mem_singleton.not.mpr hx', or_false, not_not] at hx
      simp only [count, if_neg hx', count_not_mem_free hx]

  | .app e₁ e₂ =>
    have ⟨hx₁, hx₂⟩ : x ∉ e₁.free ∧ x ∉ e₂.free := Finset.not_mem_union.mp h
    simp only [count, count_not_mem_free hx₁, count_not_mem_free hx₂]

/-- A fresh variable is not free. -/
@[simp] theorem count_fresh (e : Lambda) : e.count e.free.fresh = 0 := by
  match e with
  | .var x => simp only [count, free, if_neg (Finset.fresh_singleton_ne x)]
  | .abs x e =>
    simp only [count, free]
    by_cases hx : (e.free \ {x}).fresh = x
    · rw [if_pos hx]
    · simp only [if_neg hx, count_not_mem_free (Finset.fresh_sdiff hx)]
  | .app e₁ e₂ =>
    simp only [count, free,
      count_not_mem_free (Finset.fresh_union_left e₁.free e₂.free),
      count_not_mem_free (Finset.fresh_union_right e₁.free e₂.free)]

/-- Free variables occur at most once in affine lambdas. -/
theorem affine_count_le_one {e : Lambda} (he : e.is_affine) (x : ℕ) : e.count x ≤ 1 := by
  wlog hx : x ∈ e.free
  · simp only [count_not_mem_free hx, zero_le]

  match e with
  | .var x' => simp only [count, ite_le_one (le_refl 1) (zero_le 1)]
  | .abs x' e => simp only [count, ite_le_one (zero_le 1)
    (affine_count_le_one (is_affine_of_abs.mp he).1 x)]
  | .app e₁ e₂ =>
    simp [free] at hx
    have ⟨he₁, he₂, h⟩ := is_affine_of_app.mp he
    have hn : ¬(x ∈ e₁.free ∧ x ∈ e₂.free) := by
      simp only [← Finset.mem_inter, h, Finset.not_mem_empty, not_false_eq_true]

    by_cases hx₁ : x ∈ e₁.free
    · have hx₂ : x ∉ e₂.free := fun hx₂ => hn ⟨hx₁, hx₂⟩
      simp only [count, count_not_mem_free hx₂, add_zero, affine_count_le_one he₁]
    · simp only [count, count_not_mem_free hx₁, zero_add, affine_count_le_one he₂]

@[simp] theorem free_eq (e : Affine vs) : vs = e.free := by rfl

@[simp] theorem count_β_of_abs : (abs x e).count_β = e.count_β := by rfl

@[simp] theorem count_β_of_app_var : (app (var x) e).count_β = e.count_β := by rfl

@[simp] theorem count_β_of_app_abs :
    (app (abs x e₁) e₂).count_β = 1 + e₁.count_β + e₂.count_β := by
  rfl

@[simp] theorem count_β_of_app_app :
    (app (app e₁ e₂) e₃).count_β = e₁.count_β + e₂.count_β + e₃.count_β := by
  rfl

end Lambda

namespace Affine

theorem fresh_vars_not_mem_free (e₁ : Affine vs₁) (vs₂ : Finset ℕ) :
    (e₁.vars ∪ vs₂).fresh ∉ e₁.free := by
  sorry

theorem free_subset_vars (e : Affine vs) : e.free ⊆ e.vars := by
  match e with
  | .var x => rfl
  | .app e₁ e₂ _ => simp only [vars, free_subset_vars, Finset.union_subset_union]
  | .abs x e =>
    exact Finset.Subset.trans
      (Finset.sdiff_subset _ _)
      (Finset.Subset.trans e.free_subset_vars (Finset.subset_union_left e.vars {x}))

@[simp] theorem free_eq (e : Affine vs) : vs = e.free := by rfl

@[simp] theorem count_β_of_abs : (abs x e).count_β = e.count_β := by rfl

@[simp] theorem count_β_of_app_var : (app (var x) e h).count_β = e.count_β := by rfl

@[simp] theorem count_β_of_app_abs :
    (app (abs x e₁) e₂ h).count_β = 1 + e₁.count_β + e₂.count_β := by
  rfl

@[simp] theorem count_β_of_app_app :
    (app (app e₁ e₂ h₁) e₃ h₂).count_β = e₁.count_β + e₂.count_β + e₃.count_β := by
  rfl

@[simp] theorem size_pos {e : Affine vs} : 0 < e.size := by
  match e with
  | .var _ => simp only [size, zero_lt_one]
  | .abs _ _ => simp only [size, add_pos_iff, zero_lt_one, true_or]
  | .app _ _ _ => simp only [size, add_pos size_pos size_pos]

@[simp] theorem size_lt_size_abs : e.size < (abs x e).size := by
  simp only [size, lt_add_iff_pos_left, zero_lt_one]

@[simp] theorem size_lt_size_app_left : a₁.size < (app a₁ a₂ h).size := by
  simp only [size, lt_add_iff_pos_right, size_pos]

@[simp] theorem size_lt_size_app_right : a₂.size < (app a₁ a₂ h).size := by
  simp only [size, lt_add_iff_pos_left, size_pos]

@[simp] theorem size_lt_size_app_app₁ : e₁.size < (app (app e₁ e₂ h₁) e₃ h₂).size := by
  simp_rw [size, add_assoc, lt_add_iff_pos_right, add_pos size_pos size_pos]

@[simp] theorem size_lt_size_app_app₂ : e₂.size < (app (app e₁ e₂ h₁) e₃ h₂).size := by
  simp_rw [size, add_comm e₁.size e₂.size, add_assoc, lt_add_iff_pos_right,
    add_pos size_pos size_pos]

@[simp] theorem size_lt_size_app_app₃ : e₃.size < (app (app e₁ e₂ h₁) e₃ h₂).size := by
  simp_rw [size, add_comm, lt_add_iff_pos_right, add_pos size_pos size_pos]

end Affine
