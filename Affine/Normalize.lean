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

theorem small_step_count_β_lt (e : Lambda) (h : e.count_β ≠ 0) : e.small_step.count_β < e.count_β := by
  match e with
  | .var x => simp only [count_β, ne_eq, not_true_eq_false] at h
  | .abs x e => simp only [count_β, small_step_count_β_lt e h]
  | .app (.var x) e₂ => sorry
  | .app (.abs x e₁) e₂ => sorry
  | .app (.app e₁ e₂) e₃ => sorry

def normalize (e : Lambda) : Lambda :=
  if h : e.count_β = 0 then
    e
  else
    have : e.small_step.count_β < e.count_β := e.small_step_count_β_lt h
    e.small_step.normalize
termination_by e.count_β

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

@[simp] theorem small_step_free (e : Lambda) : e.small_step.free ⊆ e.free := by
  match e with
  | .var x' => simp only [free, Finset.Subset.refl]
  | .abs x' e =>
    simp only [free, small_step_free e, Finset.sdiff_subset_sdiff _ (Finset.Subset.refl _)]
  | .app (.var x') e₂ =>
    simp only [free, small_step_free e₂, Finset.union_subset_union (Finset.Subset.refl _)]
  | .app (.abs x' e₁) e₂ => simp only [free, small_step, substₑ_free]
  | .app (.app e₁ e₂) e₃ =>
    simp only [count, free, small_step, small_step_count]
    exact Finset.union_subset_union
      (Finset.union_subset_union e₁.small_step_free e₂.small_step_free)
      e₃.small_step_free

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
    simp only [small_step, is_affine_substₑ he₁ he₂]

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

@[simp] theorem normalize_of_var (x : ℕ) : (var x).normalize = var x := by
  unfold normalize
  simp only [count_β, dif_pos]

@[simp] theorem normalize_of_abs (e : Lambda) (x : ℕ) : (abs x e).normalize = abs x e.normalize := by
  unfold normalize
  simp only [count_β, dif_pos]
  by_cases hc : e.count_β = 0
  · simp_rw [dif_pos hc]
  · have : e.small_step.count_β < e.count_β := small_step_count_β_lt e hc
    simp_rw [dif_neg hc, small_step, normalize_of_abs e.small_step]
termination_by e.count_β

@[simp] theorem normalize_free_eq (e : Lambda) : e.normalize.free ⊆ e.free := by
  unfold normalize
  simp only [count_β, dif_pos]
  by_cases hc : e.count_β = 0
  · simp_rw [dif_pos hc, Finset.Subset.refl]
  · have : e.small_step.count_β < e.count_β := small_step_count_β_lt e hc
    have h₁ : e.small_step.normalize.free ⊆ e.small_step.free := normalize_free_eq e.small_step
    have h₂ : e.small_step.free ⊆ e.free := small_step_free e
    simp_rw [dif_neg hc, Finset.Subset.trans h₁ h₂]
termination_by e.count_β

@[simp] theorem normalize_affine {e : Lambda} (h : e.is_affine) : e.normalize.is_affine := by
  if hβ : e.count_β = 0 then
    rw [normalize, dif_pos hβ]
    exact h
  else
    rw [normalize, dif_neg hβ]
    simp only
    have : e.small_step.count_β < e.count_β := small_step_count_β_lt e hβ
    exact normalize_affine (small_step_is_affine h)
termination_by e.count_β

end Lambda

namespace Affine

def normalize (e : Affine vs) : (vs' : Finset ℕ) × (_ : Affine vs') ×' (vs' ⊆ vs) :=
  let e' := e.to_lambda.normalize
  have he'_free_sub : e'.free ⊆ vs := by
    rw [e.free_eq, to_lambda_free_eq e]
    exact Lambda.normalize_free_eq e.to_lambda
  have he'_is_affine : e'.is_affine := Lambda.normalize_affine e.to_lambda_is_affine
  ⟨e'.free, Affine.of_lambda he'_is_affine, he'_free_sub⟩

end Affine
