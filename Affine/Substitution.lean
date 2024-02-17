import «Affine».Lemmas

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
      let y := e₂.free.fresh
      .abs y ((e₁.substᵥ x' y).substₑ x e₂)
    else
      .abs x' (e₁.substₑ x e₂)
termination_by e₁.depth

theorem substₑ_count {e₁ e₂ : Lambda} :
    (e₁.substₑ x' e₂).count x ≤ (if x = x' then 0 else e₁.count x) + e₂.count x := by
  sorry
  -- match e₁ with
  -- | .var y =>
  --   simp_rw [substₑ, apply_ite (count · x), count]
  --   by_cases hy : x' = y
  --   · rw [if_pos hy]
  --     by_cases hx : x = x'
  --     · rw [if_pos hx, zero_add]
  --     · rw [if_neg hx, if_neg (hy ▸ hx), zero_add]
  --   · rw [if_neg hy]
  --     by_cases hx : x = x'
  --     · simp only [if_pos hx, if_neg (hx.symm ▸ hy), zero_le]
  --     · simp only [if_neg hx, le_add_iff_nonneg_right, zero_le]

  -- | .abs y e =>
  --   simp only [substₑ]
  --   sorry

theorem substₑ_free {e₁ e₂ : Lambda} : (substₑ e₁ x e₂).free ⊆ e₁.free \ {x'} ∪ e₂.free := by
  sorry

theorem is_affine_substₑ {e₁ e₂ : Lambda} (he₁ : e₁.is_affine) (he₂ : e₂.is_affine) (x : ℕ) :
    (e₁.substₑ x e₂).is_affine := by
  sorry

theorem substₑ_count_β {e₁ e₂ : Lambda} : (e₁.substₑ x e₂).count_β < 1 + e₁.count_β + e₂.count_β := by sorry

end Lambda
