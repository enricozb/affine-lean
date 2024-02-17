import «Affine».Affine
import «Affine».Lambda
import «Affine».Misc

namespace Lambda

@[simp] theorem app_depth_left : e₁.depth < (app e₁ e₂).depth := by
  simp only [depth, lt_of_le_of_lt (le_max_left e₁.depth e₂.depth) (lt_one_add _)]

@[simp] theorem app_depth_right : e₂.depth < (app e₁ e₂).depth := by
  simp_rw [depth, lt_of_le_of_lt (le_max_right e₁.depth e₂.depth) (lt_one_add _)]

@[simp] theorem abs_depth : e.depth < (abs x e).depth := by simp only [depth, lt_one_add]

@[simp] theorem is_affine_of_var : (var x).is_affine := by
  simp only [is_affine]

@[simp] theorem is_affine_of_abs : (abs x e).is_affine ↔ is_affine e ∧ count e x ≤ 1:= by
  simp only [is_affine, decide_eq_true_eq]

@[simp] theorem is_affine_of_app :
    (app e₁ e₂).is_affine ↔ is_affine e₁ ∧
                            is_affine e₂ ∧
                            ∀ x ∈ free (app e₁ e₂), count e₁ x + count e₂ x ≤ 1 := by
  simp only [is_affine, decide_eq_true_eq]

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
  | .app e₁ e₂ => simp only [count, (is_affine_of_app.mp he).2.2 x hx]

end Lambda

namespace Affine

@[simp] theorem app_depth_left : e₁.depth < (app e₁ e₂ h).depth := by
  simp only [depth, lt_of_le_of_lt (le_max_left e₁.depth e₂.depth) (lt_one_add _)]

@[simp] theorem app_depth_right : e₂.depth < (app e₁ e₂ h).depth := by
  simp_rw [depth, lt_of_le_of_lt (le_max_right e₁.depth e₂.depth) (lt_one_add _)]

@[simp] theorem abs_depth : e.depth < (abs x e).depth := by simp only [depth, lt_one_add]

@[simp] theorem is_affine_of_var : (var x).is_affine := by simp only [is_affine]

-- @[simp] theorem is_affine_of_abs : is_affine (abs x e) ∧ count (abs x e) x ≤ 1 := by
--   simp [is_affine, count]

-- @[simp] theorem is_affine_of_app :
--     (app e₁ e₂ h).is_affine ↔ is_affine e₁ ∧
--                             is_affine e₂ ∧
--                             ∀ x ∈ free (app e₁ e₂ h), count e₁ x + count e₂ x ≤ 1 := by
--   simp only [is_affine, decide_eq_true_eq]

/-- Variables that are not free in `e` have count of `0`. -/
theorem count_not_mem_free {e : Affine vs} {x : ℕ} (h : x ∉ e.free) : e.count x = 0 := by
  match e with
  | .var x' => simp only [count, Finset.mem_singleton.not.mp h, ↓reduceIte]
  | .abs x' e =>
    have hx : x ∉ e.free ∨ ¬x ∉ {x'} := not_and_or.mp (Finset.mem_sdiff.not.mp h)
    by_cases hx' : x = x'
    · simp only [count, if_pos hx']
    · simp only [Finset.mem_singleton.not.mpr hx', or_false, not_not] at hx
      simp only [count, if_neg hx', count_not_mem_free hx]
  | .app e₁ e₂ h' =>
    have ⟨hx₁, hx₂⟩ : x ∉ e₁.free ∧ x ∉ e₂.free := Finset.not_mem_union.mp h
    simp only [count, count_not_mem_free hx₁, count_not_mem_free hx₂]

/-- Free variables occur at most once in affine lambdas. -/
theorem affine_count_le_one (e : Affine vs) (x : ℕ) : e.count x ≤ 1 := by
  wlog hx : x ∈ e.free
  · simp only [count_not_mem_free hx, zero_le]

  match e with
  | .var x' => simp only [count, ite_le_one (le_refl 1) (zero_le 1)]
  | .abs x' e => simp only [count, ite_le_one (zero_le 1) (affine_count_le_one e x)]
  | .app e₁ e₂ h =>
    apply Or.elim (Finset.mem_union.mp hx)
    · intro hx₁
      have hx₂ : x ∉ e₂.free := fun hx₂ =>
        Finset.eq_empty_iff_forall_not_mem.mp h x (Finset.mem_inter.mpr ⟨hx₁, hx₂⟩)
      simp only [count, count_not_mem_free hx₂, add_zero, affine_count_le_one e₁ x]
    · intro hx₂
      have hx₁ : x ∉ e₁.free := fun hx₁ =>
        Finset.eq_empty_iff_forall_not_mem.mp h x (Finset.mem_inter.mpr ⟨hx₁, hx₂⟩)
      simp only [count, count_not_mem_free hx₁, zero_add, affine_count_le_one e₂ x]

/-- For affine terms `e : Affine vs`, `vs` represents occurrences of free variables. -/
theorem count_ne_zero_iff (e : Affine vs) (x : ℕ) : e.count x ≠ 0 ↔ x ∈ vs := by
  unfold count

  match e with
  | .var x' => simp_rw [ne_eq, ite_eq_right_iff, imp_false, not_not, Finset.mem_singleton]
  | .abs x' e =>
    simp_rw [ne_eq, ite_eq_left_iff, not_forall, exists_prop]
    exact ⟨
      fun ⟨hne, hc⟩ =>
        Finset.mem_sdiff.mpr ⟨(count_ne_zero_iff e x).mp hc, Finset.not_mem_singleton.mpr hne⟩,
      fun hmem =>
        have ⟨h₁, h₂⟩ := Finset.mem_sdiff.mp hmem;
        ⟨Finset.not_mem_singleton.mp h₂, (count_ne_zero_iff e x).mpr h₁⟩
    ⟩

  | .app e₁ e₂ h =>
    apply Iff.intro
    · intro h_add_ne_zero
      have hc : count e₁ x ≠ 0 ∨ count e₂ x ≠ 0 := by
        by_contra hc
        simp_rw [not_or, not_not] at hc
        have ⟨h₁, h₂⟩ := hc
        simp_rw [h₁, h₂, add_zero] at h_add_ne_zero
        contradiction
      exact Or.elim hc
        (fun h₁ => Finset.mem_union_left _ ((count_ne_zero_iff e₁ x).mp h₁))
        (fun h₂ => Finset.mem_union_right _ ((count_ne_zero_iff e₂ x).mp h₂))

    · intro hmem h_add_eq_zero
      have ⟨h₁, h₂⟩ := Nat.add_eq_zero_iff.mp h_add_eq_zero

      have hmem : x ∈ e₁.free ∨ x ∈ e₂.free := Finset.mem_union.mp hmem
      have : ¬(x ∈ e₁.free ∨ x ∈ e₂.free) := not_or.mpr ⟨
        (count_ne_zero_iff e₁ x).not_right.mp h₁,
        (count_ne_zero_iff e₂ x).not_right.mp h₂
      ⟩

      contradiction

end Affine
