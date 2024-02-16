import Mathlib.Data.Finset.Basic

/--
  Affine lambda terms, where bound variables can be used at most once.

  The choice of `Finset` over:
  - `List`: Can have duplicates.
  - `Set`: Can be infinite.
-/
inductive Affine : (vs : List ℕ) → Type
| var (x : ℕ) : Affine {x}
| abs (x : ℕ) (e : Affine vs) : Affine (vs \ {x})
| app (e₁ : Affine vs₁) (e₂ : Affine vs₂) (h : vs₁ ∩ vs₂ = ∅) : Affine (vs₁ ∪ vs₂)

namespace Affine

/-- The free variables in an affine term. -/
abbrev free (_ : Affine vs) : List ℕ := vs

def subst (e : Affine vs₁) (x : ℕ) (hx : x ∈ vs₁) (e' : Affine vs₂) : Affine ((vs₁ \ {x}) ∪ vs₂) :=
  sorry

def small_step (e : Affine vs) : (vs' : List ℕ) × Affine vs' :=
  match e with
  | .var x => ⟨_, .var x⟩
  | .abs x e => ⟨_, .abs x e⟩
  | .app e₁ e₂ h =>
    match e₁ with
    | .var x => ⟨_, .app e₁ e₂ sorry⟩
    | .app _ _ _ => ⟨_, .app e₁ e₂ sorry⟩
    | .abs x e =>
      if hx₁ : x ∈ e₁.free then
        ⟨_, e₁.subst x hx₁ e₂⟩
      else
        ⟨_, e₁⟩

theorem small_step_subset (e : Affine vs) : (small_step e).2.free ⊆ vs := by
  match e with
  | .var _ => simp only [free, small_step, List.Subset.refl]
  | .abs _ _ => simp only [free, small_step, List.Subset.refl]
  | .app (.abs x e₁) e₂ h =>
    simp [free, small_step]

  | .app (.var x) e₃ h₂ => simp only [free, small_step, List.Subset.refl]
  | .app (.app e₁ e₂ h₁) e₃ h₂ => simp only [free, small_step, List.Subset.refl]




/- A single normalization pass. -/
-- def small_step (e : Affine vs) : (vs' : Finset ℕ) × (h : vs' ⊆ vs) ×' Affine vs' :=
--   match e with
--   | .app (.abs x e₁) e₂ h =>
--     if hx₁ : x ∈ e₁.free then
--       ⟨e₁.free \ {x} ∪ e₂.free, Finset.Subset.refl _, e₁.subst x hx₁ e₂⟩
--     else
--       have : e₁.free ⊆ e₁.free \ {x} ∪ e₂.free := by
--         intro v hv
--         have : v ∉ {x} := Finset.not_mem_singleton.mpr (fun heq : v = x => hx₁ (heq ▸ hv))
--         exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, this⟩)

--       ⟨e₁.free, this, e₁⟩

--   | e => ⟨vs, Finset.Subset.refl _, e⟩
