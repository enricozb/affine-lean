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

theorem substᵥ_is_affine {e : Lambda} (he : e.is_affine) (hy : y ∉ e.vars) :
    (e.substᵥ x y).is_affine := by sorry

theorem substᵥ_count_β {e : Lambda} : (e.substᵥ x y).count_β = e.count_β := by
  match e with
  | .var x' => simp only [count_β, substᵥ, apply_ite, ite_self]
  | .abs x' e =>
    simp only [count_β, substᵥ, apply_ite, ite_self, substᵥ_count_β (e := e)]
  | .app (.var x') e₂ =>
    by_cases hx : x = x'
    · simp only [if_pos hx, count_β, substᵥ, substᵥ_count_β (e := e₂)]
    · simp only [if_neg hx, count_β, substᵥ, substᵥ_count_β (e := e₂)]
  | .app (.abs x' e₁) e₂ =>
    have : depth e₁ < depth (app (abs x' e₁) e₂) := by sorry
    by_cases hx : x = x'
    · simp_rw [count_β, substᵥ, if_pos hx, count_β, substᵥ_count_β (e := e₂)]
    · simp_rw [count_β, substᵥ, if_neg hx, count_β, substᵥ_count_β (e := e₁), substᵥ_count_β (e := e₂)]
  | .app (.app e₁ e₂) e₃ =>
    have : depth e₁ < depth (app (app e₁ e₂) e₃) := by sorry
    have : depth e₂ < depth (app (app e₁ e₂) e₃) := by sorry
    have : depth e₃ < depth (app (app e₁ e₂) e₃) := by sorry
    simp_rw [count_β, substᵥ_count_β (e := e₁), substᵥ_count_β (e := e₂), substᵥ_count_β (e := e₃)]
termination_by e.depth

theorem substₑ_count_β {e₁ e₂ : Lambda} (h₁ : e₁.is_affine) (h₂ : e₂.is_affine) :
    (e₁.substₑ x e₂).count_β < 1 + e₁.count_β + e₂.count_β := by
  match e₁ with
  | .var x' =>
    have h₁ : e₂.count_β < 1 + e₂.count_β := lt_one_add _
    have h₂ : 0 < 1 + e₂.count_β := by simp only [add_pos_iff, zero_lt_one, true_or]
    simp only [substₑ, count_β, add_zero, apply_ite, ite_lt h₁ h₂]

  | .abs x' e₁ =>
    simp only [is_affine, decide_eq_true_eq] at h₁
    simp only [substₑ, count_β, apply_ite count_β]

    wlog hx₁ : x ∈ e₁.free
    · simp only [if_pos (Or.inr hx₁), add_assoc, Nat.lt_one_add_iff.mpr, le_add_iff_nonneg_right,
        zero_le]

    wlog hxeq : x ≠ x'
    · simp only [if_pos (Or.inl (not_not.mp hxeq)), add_assoc, Nat.lt_one_add_iff.mpr,
        le_add_iff_nonneg_right, zero_le]

    rw [if_neg]

    by_cases hx' : x' ∈ e₂.free
    · rw [if_pos hx']
      let y := (e₁.vars ∪ e₂.free).fresh
      have hy : y ∉ e₁.vars :=
        (Finset.not_mem_union.mp (Finset.fresh_not_mem (e₁.vars ∪ e₂.free))).left
      have hinc := substₑ_count_β (e₁ := e₁.substᵥ x' y) (e₂ := e₂) (x := x) (substᵥ_is_affine h₁.left hy) h₂
      simp only [substᵥ_count_β] at hinc
      exact hinc
    · simp only [if_neg hx', substₑ_count_β (e₁ := e₁) h₁.left h₂]

    simp only [not_or, not_not, hx₁, hxeq, not_false_eq_true, true_and]

  | .app (.var _) e₂ => sorry
  | .app (.abs _ e₁) e₂ => sorry
  | .app (.app e₁ e₂) e₃ => sorry
termination_by e₁.depth

theorem substₑ_is_affine {e₁ e₂ : Lambda} (he₁ : e₁.is_affine) (he₂ : e₂.is_affine) (x : ℕ) :
    (e₁.substₑ x e₂).is_affine := by sorry

theorem substₑ_free {e₁ e₂ : Lambda} : (substₑ e₁ x e₂).free ⊆ e₁.free \ {x} ∪ e₂.free := by sorry

theorem substₑ_count {e₁ e₂ : Lambda} :
    (e₁.substₑ x' e₂).count x ≤ (if x = x' then 0 else e₁.count x) + e₂.count x := by
  sorry

end Lambda
