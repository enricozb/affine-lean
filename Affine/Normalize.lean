import «Affine».Conversion
import «Affine».Substitution
import «Affine».Misc

namespace Lambda

def small_step (e : Lambda) : Lambda :=
  match e with
  | .var x => .var x
  | .abs x e => .abs x e.small_step
  | .app (.var x) e₂ => .app (.var x) e₂.small_step
  | .app (.abs x e₁) e₂ => e₁.substₑ x e₂
  | .app (.app e₁ e₂) e₃ => .app (.app e₁.small_step e₂.small_step) e₃.small_step

@[simp] theorem small_step_free (e : Lambda) : e.small_step.free ⊆ e.free := by
  match e with
  | .var x' => simp only [free, Finset.Subset.refl]
  | .abs x' e =>
    simp only [free, small_step_free e, Finset.sdiff_subset_sdiff _ (Finset.Subset.refl _)]
  | .app (.var x') e₂ =>
    simp only [free, small_step_free e₂, Finset.union_subset_union (Finset.Subset.refl _)]
  | .app (.abs x' e₁) e₂ => simp only [free, small_step, substₑ_free]
  | .app (.app e₁ e₂) e₃ =>
    simp only [count, free, small_step]
    exact Finset.union_subset_union
      (Finset.union_subset_union e₁.small_step_free e₂.small_step_free)
      e₃.small_step_free

@[simp] theorem small_step_count (e : Lambda) (x : ℕ) : e.small_step.count x ≤ e.count x := by
  match e with
  | .var x' => simp only [count, le_refl]
  | .abs x' e => simp only [count, small_step_count e x, ite_le_ite (le_refl 0)]
  | .app (.var x') e₂ => simp only [count, small_step_count e₂ x, add_le_add_iff_left]
  | .app (.abs x' e₁) e₂ => simp only [count, small_step, substₑ_count, le_refl]
  | .app (.app e₁ e₂) e₃ =>
    simp only [count, small_step, small_step_count]
    exact add_le_add
      (add_le_add (e₁.small_step_count x) (e₂.small_step_count x))
      (e₃.small_step_count x)

@[simp] theorem small_step_is_affine {e : Lambda} (h : e.is_affine) : e.small_step.is_affine := by
  match e with
  | .var x => simp only [small_step, h]

  | .abs x e =>
    have ⟨he, hc⟩ := is_affine_of_abs.mp h
    simp only [small_step, small_step_is_affine he, is_affine_of_abs, hc,
      le_trans (small_step_count e x) hc, and_self]

  | .app (.var x) e₂ =>
    simp only [is_affine_of_app, is_affine_of_var, free, true_and] at h
    have ⟨he₂, hinter⟩ := h
    simp only [small_step, is_affine_of_app, is_affine_of_var, small_step_is_affine he₂, hinter,
      small_step_free, free, true_and]
    by_cases hx : x ∈ e₂.free
    · simp only [Finset.singleton_ne_empty, Finset.singleton_inter_of_mem hx, and_false] at h
    · simp only [Finset.singleton_inter_of_not_mem hx, and_true] at h
      have := Finset.inter_subset_inter (Finset.Subset.refl {x}) (small_step_free e₂)
      apply Finset.subset_empty.mp
      simp only [← hinter, this]

  | .app (.abs x e₁) e₂ =>
    simp only [is_affine_of_app, is_affine_of_abs] at h
    have ⟨⟨he₁, _⟩, he₂, _⟩ := h
    simp only [small_step, substₑ_is_affine he₁ he₂]

  | .app (.app e₁ e₂) e₃ =>
    simp only [is_affine_of_app, free] at h
    have ⟨⟨he₁, he₂, hfree₁₂⟩, he₃, hfree₁₂₃⟩ := h
    simp only [small_step, is_affine_of_app, small_step_is_affine he₁, small_step_is_affine he₂,
      small_step_is_affine he₃, small_step_free, free, hfree₁₂, hfree₁₂₃, true_and]

    apply And.intro
    · simp_rw [← Finset.subset_empty, ← hfree₁₂,
        Finset.inter_subset_inter e₁.small_step_free e₂.small_step_free]
    · apply Finset.subset_empty.mp
      rw [← hfree₁₂₃]
      exact Finset.inter_subset_inter
        (Finset.union_subset_union e₁.small_step_free e₂.small_step_free)
        e₃.small_step_free

theorem small_step_size_le {e : Lambda} (he : e.is_affine) :
    e.small_step.size ≤ e.size := by
  match e with
  | .var x => rfl
  | .abs x e =>
    simp only [is_affine_of_abs] at he
    exact add_le_add_left (e.small_step_size_le he.1) _
  | .app (.var x) e =>
    simp only [is_affine_of_app, is_affine_of_var, true_and, free] at he
    simp only [size, zero_add, e.small_step_size_le he.1]
  | .app (.app e₁ e₂) e₃ =>
    simp only [is_affine_of_app, true_and, free] at he
    have ⟨⟨he₁, he₂, _⟩, he₃, _⟩ := he
    simp only [size]
    refine' add_le_add _ (e₃.small_step_size_le he₃)
    refine' add_le_add (e₁.small_step_size_le he₁) (e₂.small_step_size_le he₂)
  | .app (.abs x e₁) e₂ =>
    simp only [is_affine_of_app, is_affine_of_abs, free] at he
    simp only [size, small_step]
    apply le_of_lt
    exact substₑ_size_lt he.1.1

theorem small_step_size_lt {e : Lambda} (he : e.is_affine) (hβ : e.count_β ≠ 0) :
    e.small_step.size < e.size := by
  match e with
  | .var x => simp only [count_β] at hβ; contradiction
  | .abs x e =>
    simp only [count_β, is_affine_of_abs] at he hβ
    simp only [size, small_step, add_lt_add_left (small_step_size_lt he.1 hβ) 1]
  | .app (.var x) e₂ =>
    simp only [count_β_of_app_var, is_affine_of_app, is_affine_of_var, true_and] at he hβ
    simp only [size, zero_add, small_step_size_lt he.1 hβ]
  | .app (.app e₁ e₂) e₃ =>
    simp only [count_β_of_app_app, is_affine_of_app] at he hβ
    have ⟨⟨he₁, he₂, _⟩, he₃, _⟩ := he
    simp only [size]
    have hdisj := add_add_neq_zero hβ
    refine' Or.elim hdisj (fun hβ₁ => _) (fun hβ₂₃ => Or.elim hβ₂₃ (fun hβ₂ => _) (fun hβ₃ => _))
    · apply add_lt_add_of_lt_of_le
      apply add_lt_add_of_lt_of_le
      exact small_step_size_lt he₁ hβ₁
      exact small_step_size_le he₂
      exact small_step_size_le he₃
    · apply add_lt_add_of_lt_of_le
      apply add_lt_add_of_le_of_lt
      exact small_step_size_le he₁
      exact small_step_size_lt he₂ hβ₂
      exact small_step_size_le he₃
    · apply add_lt_add_of_le_of_lt
      apply add_le_add
      exact small_step_size_le he₁
      exact small_step_size_le he₂
      exact small_step_size_lt he₃ hβ₃
  | .app (.abs x e₁) e₂ =>
    simp only [count_β_of_app_abs, is_affine_of_app, is_affine_of_abs] at he hβ
    simp only [size, small_step, substₑ_size_lt he.1.1]

end Lambda

namespace Affine

def small_step_impl (e : Affine vs) : (vs' : Finset ℕ) × (Affine vs') :=
  let e' := e.to_lambda.small_step
  have he'_is_affine : e'.is_affine := Lambda.small_step_is_affine e.to_lambda_is_affine
  ⟨e'.free, Affine.of_lambda he'_is_affine⟩

def small_step_free (e : Affine vs) : Finset ℕ := e.small_step_impl.1
def small_step (e : Affine vs) : Affine e.small_step_free := e.small_step_impl.2

theorem to_lambda_small_step {e : Affine vs} :
    e.to_lambda.small_step = e.small_step.to_lambda := by
  match e with
  | .var x => rfl
  | .abs x e
  | .app (.var x) e₂ h
  | .app (.app e₁ e₂ h₁) e₃ h₂ =>
    simp only [Lambda.small_step, e.to_lambda_small_step, to_lambda, Lambda.of_lambda_to_lambda]
  | .app (.abs x e₁) e₂ h =>
    simp only [to_lambda, Lambda.small_step, small_step, small_step_impl, Lambda.small_step,
      Lambda.of_lambda_to_lambda]

theorem small_step_size_lt {e : Affine vs} (hβ : e.count_β ≠ 0) :
    e.small_step.size < e.size := by
  rw [← to_lambda_count_β_eq] at hβ
  rw [← e.small_step.to_lambda_size_eq, ← e.to_lambda_size_eq, ← e.to_lambda_small_step]
  exact Lambda.small_step_size_lt e.to_lambda_is_affine hβ

def normalize (e : Affine vs) : (vs' : Finset ℕ) × (Affine vs') :=
  if hβ : e.count_β = 0 then
    ⟨vs, e⟩
  else
    have := small_step_size_lt hβ
    normalize e.small_step
termination_by e.size

end Affine
