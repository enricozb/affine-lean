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
      let y := e₂.free.fresh
      .abs y ((e₁.substᵥ x' y).substₑ x e₂)
    else
      .abs x' (e₁.substₑ x e₂)
termination_by e₁.depth

@[simp] theorem substₑ_count_mem_free (e₁ e₂ : Lambda) (hx : x ∈ e₁.free) :
    (e₁.substₑ x e₂).count y = (e₁.count x) * (e₂.count y) := by
  match e₁ with
  | .var x' => simp only [substₑ, if_pos (Finset.mem_singleton.mp hx), count, one_mul]
  | .abs x' e₁ =>
    have hx : ¬(x = x' ∨ x ∉ e₁.free) := by
      simp_rw [not_or, not_not, ← Finset.mem_singleton.not, and_comm, ← Finset.mem_sdiff]
      exact hx
    simp only [substₑ, count, if_neg hx, apply_ite (count · y)]



    wlog hy : y ≠ e₂.free.fresh
    · simp only [if_pos (not_not.mp hy)]


    by_cases hx' : x' ∈ e₂.free
    · simp only [if_pos hx']



@[simp] theorem substₑ_of_not_mem_free (e₁ e₂ : Lambda) (h : x ∉ e₁.free) :
    e₁.substₑ x e₂ = e₁ := by
  match e₁ with
  | .var x' => simp only [substₑ, if_neg (Finset.mem_singleton.not.mp h)]
  | .abs x' e₁ =>
    simp only [free, Finset.mem_sdiff, not_and_or, not_not] at h
    by_cases hx : x = x'
    · simp only [substₑ, if_pos (Or.inl hx)]
    · have : x ∉ e₁.free := by simp only [Finset.mem_singleton, hx, or_false] at h; exact h
      simp only [substₑ, if_pos (Or.inr this)]
  | .app a₁ a₂ =>
    simp only [free, Finset.not_mem_union] at h
    simp only [substₑ, substₑ_of_not_mem_free a₁ e₂ h.left, substₑ_of_not_mem_free a₂ e₂ h.right]

@[simp] theorem substₑ_count_not_mem_free (e₁ e₂ : Lambda) (h : x ∉ e₁.free) :
    (e₁.substₑ x e₂).count y = e₁.count y := by
  simp only [substₑ_of_not_mem_free e₁ e₂ h]

@[simp] theorem substₑ_count_mem_free_of_affine
    (e₁ e₂ : Lambda) (h : x ∈ e₁.free) (he₁ : e₁.is_affine) :
    (e₁.substₑ x e₂).count y = e₂.count y := by
  simp only [substₑ_count_mem_free e₁ e₂ h]

theorem substₑ_free_eq (e₁ e₂ : Lambda) (x : ℕ) :
    (e₁.substₑ x e₂).free = e₁.free \ {x} ∪ e₂.free := by
  sorry

-- theorem substₑ_count_affine_le {e₁ e₂ : Lambda} : (e₁.substₑ y e₂).count y = e₂.count y := by
--   match e₁ with
--   | .var x' =>
--     simp only [substₑ, apply_ite (count · y)]
--     by_cases hx : y = x'
--     · simp only [hx, ↓reduceIte]
--     · simp [hx, count]

-- theorem substₑ_count_ne_eq {e₁ e₂ : Lambda} (h : x ≠ y) : (e₁.substₑ x e₂).count y = e₁.count x + e₂.count x := by sorry


/-- Substitution of affine terms preserves top-level affinity (free variable count at most one). -/
-- theorem substₑ_count_le {e₁ e₂ : Lambda} (he₁ : e₁.is_affine) (he₂ : e₂.is_affine) (x : ℕ) :
--     ∀ y, (e₁.substₑ x e₂).count y ≤ 1 := by
--   intro y
--   match e₁ with
--   | .var x' =>
--     have : count (var x') y ≤ 1 := by simp only [count, ite_le_one (le_refl 1) (zero_le 1)]
--     simp_rw [substₑ, apply_ite (count · y), ite_le_one (affine_count_le_one he₂ y) this]

--   | .app a₁ a₂ =>
--     have ⟨ha₁, ha₂, hc⟩ := he₁
--     simp only [substₑ, count]
--     sorry

--   | .abs x e => sorry

theorem affine_substₑ_is_affine {e₁ e₂ : Lambda} (he₁ : e₁.is_affine) (he₂ : e₂.is_affine) (x : ℕ) :
    (e₁.substₑ x e₂).is_affine := by
  unfold substₑ
  match e₁ with
  | .var x' => simp only [apply_ite, he₂, he₁, ite_self]
  | .app a₁ a₂ =>
    have ⟨ha₁, ha₂, hc⟩ := is_affine_of_app.mp he₁
    simp only [is_affine, affine_substₑ_is_affine ha₁ he₂, affine_substₑ_is_affine ha₂ he₂,
      true_and, decide_eq_true_eq]
    intro x hx


  | .abs x' e₁ => sorry

def small_step (e : Lambda) : Lambda :=
  match e with
  | .app (.abs x e₁) e₂ => e₁.substₑ x e₂
  | e => e

theorem small_step_is_affine {e : Lambda} (he : e.is_affine) : (e.small_step.is_affine) := by
  match e with
  | .var _ => simp only [small_step, is_affine]
  | .abs x e => simp only [small_step, is_affine, and_self, is_affine_of_abs.mp he, decide_True]

  | .app (.abs x e₁) e₂ =>
    have ⟨he₁, he₂, _⟩ := is_affine_of_app.mp he
    simp only [small_step, substₑ, is_affine, affine_substₑ_is_affine he₁ he₂]

  | .app (.var x) e₂ =>
    have ⟨_, he₂, hc⟩ := he
    simp only [small_step, is_affine, he₂, hc, true_and, forall_const]

  | .app (.app e₁ e₂) e₃ =>
    have ⟨⟨he₁, he₂, hc⟩, he₃, hc'⟩ := he
    simp only [small_step, is_affine, he₁, he₂, he₃, hc, hc', true_and, forall_const]

theorem small_step_free_subset (e : Lambda) : e.small_step.free ⊆ e.free := by
  match e with
  | .var x
  | .abs x e
  | .app (.var x) e₂
  | .app (.app e₁ e₂) e₃
  | .app (.abs x e₁) e₂ => simp only [free, small_step, substₑ_free_eq, Finset.Subset.refl]

end Lambda

namespace Affine

def small_step (e : Affine vs) : (vs' : Finset ℕ) × (e : Affine vs') ×' (vs' ⊆ vs) := by
  let el := e.to_lambda.small_step
  let hel : el.is_affine := Lambda.small_step_is_affine (to_lambda_is_affine e)
  let ⟨vs', e', he'⟩ := Affine.of_lambda_impl el hel
  have hvs : vs = e.to_lambda.free := by sorry
  have hvs' : vs' = el.free := by sorry
  have hsub : el.free ⊆ e.to_lambda.free := Lambda.small_step_free_subset e.to_lambda

  refine' ⟨vs', e', _⟩
  simp_rw [hvs', hvs, hsub]

#eval (Lambda.abs 2 (.var 1)).free
#eval (Lambda.app (.abs 1 (.abs 2 (.var 1))) (.var 2)).small_step
#eval (Affine.app (.abs 1 (.abs 2 (.var 1))) (.var 2) (by simp)).small_step.2.1

/-
  TODO:
  - small_step reduces number of abstractions
  - todo normalize : repeatedly apply small step
-/

end Affine
