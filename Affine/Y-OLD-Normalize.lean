import Mathlib.Data.Finset.Lattice
import «Affine».Defs

def Finset.fresh (s : Finset ℕ) : ℕ :=
  if h : s.Nonempty then
    s.max' h + 1
  else
    0

theorem Finset.fresh_not_mem (s : Finset ℕ) : s.fresh ∉ s := by
  if h : s.Nonempty then
    simp_rw [Finset.fresh, dif_pos h]
    have : s.max' h + 1 > s.max' h := by simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one]
    exact fun hmax => not_le_of_gt this (s.le_max' (s.max' h + 1) hmax)

  else
    simp_rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.not_mem_empty _, not_false_eq_true]

-- theorem Finset.fresh_not_mem_union (s₁ s₂ : Finset ℕ) :
--     (s₁ ∪ s₂).fresh ∉ s₁ ∧ (s₁ ∪ s₂).fresh ∉ s₂ :=
--   Finset.not_mem_union.mp (s₁ ∪ s₂).fresh_not_mem

namespace Affine

/-
  Replace free occurrences of variable `x` in `e` with variable `y` that occurs _nowhere_ in `e`
  (free or otherwise).
-/
-- def revar (e : Affine vs) (x : ℕ) (y : ℕ) (hx : x ∈ vs) (hy : y ∉ e.vars) : Affine (vs \ {x} ∪ {y}) :=
--   match e with
--   | .var x' => by
--     rw [Finset.mem_singleton.mp hx, Finset.sdiff_self, Finset.empty_union]
--     exact .var y

--   | .abs x' e => by
--     have hy_neq_x : y ≠ x' := Finset.mem_singleton.not.mp (Finset.not_mem_union.mp hy).right
--     have hy : y ∉ e.vars := (Finset.not_mem_union.mp hy).left
--     have hx : x ∈ e.free := (Finset.mem_sdiff.mp hx).left

--     have : (e.free \ {x} ∪ {y}) \ {x'} = (e.free \ {x'}) \ {x} ∪ {y} := by
--       ext v
--       simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, and_imp]
--       apply Iff.intro
--       · intro ⟨hv₁, hv_neq_x'⟩
--         exact Or.elim hv₁
--           (fun ⟨hv_free, hv_neq_x⟩ => Or.inl ⟨⟨hv_free, hv_neq_x'⟩, hv_neq_x⟩)
--           Or.inr

--       · refine' fun hv => Or.elim hv _ _
--         · intro ⟨⟨hv_free, hv_neq_x'⟩, hv_neq_x⟩
--           exact ⟨Or.inl ⟨hv_free, hv_neq_x⟩, hv_neq_x'⟩
--         · intro hv_eq_y
--           rw [hv_eq_y]
--           exact ⟨Or.inr rfl, hy_neq_x⟩

--     rw [← this]
--     exact .abs x' (e.revar x y hx hy)

--   | .app e₁ e₂ h => by
--     simp only [vars] at hy
--     have ⟨hy₁, hy₂⟩ := Finset.not_mem_union.mp hy

--     if hx₁ : x ∈ e₁.free then
--       have hx₂ : x ∉ e₂.free := by sorry
--       have : (e₁.free \ {x} ∪ {y}) ∩ e₂.free = e₁.free ∩ e₂.free := by sorry
--       have exp := Affine.app (e₁.revar x y hx₁ hy₁) e₂ (this ▸ h)

--       have : e₁.free \ {x} ∪ {y} ∪ e₂.free = (e₁.free ∪ e₂.free) \ {x} ∪ {y} := by sorry
--       exact (this ▸ exp)

--     else
--       have hx₂ : x ∈ e₂.free := by sorry
--       have : e₁.free ∩ (e₂.free \ {x} ∪ {y}) = e₁.free ∩ e₂.free := by sorry
--       have exp := Affine.app e₁ (e₂.revar x y hx₂ hy₂) (this ▸ h)

--       have : e₁.free ∪ (e₂.free \ {x} ∪ {y}) = (e₁.free ∪ e₂.free) \ {x} ∪ {y} := by sorry
--       exact (this ▸ exp)

def revar (e : Affine vs) (x y : ℕ) (hx : x ∈ vs) (hy : y ∉ vs) : Affine (vs \ {x} ∪ {y}) := sorry

-- theorem fresh_not_free (e : Affine vs)

theorem free_revar_free (e : Affine vs) (x x' : ℕ) (hx : x ∈ vs) (hx' : x' ∉ vs) :
    x' ∈ (e.revar x x' hx hx').free := sorry

/--
  Substitutes free occurences of `x` in `e` with `e'`.
-/
def subst (e : Affine vs₁) (x : ℕ) (hx : x ∈ vs₁) (e' : Affine vs₂) : Affine ((vs₁ \ {x}) ∪ vs₂) := sorry
  -- have : vs₁ \ {x} = vs₂ := by sorry
  -- rw [this]
  -- exact e

/-- A single normalization pass. -/
def small_step (e : Affine vs) : (vs' : Finset ℕ) × (h : vs' ⊆ vs) ×' Affine vs' :=
  match e with
  | .app (.abs x e₁) e₂ h =>
    if hx₁ : x ∈ e₁.free then
      ⟨e₁.free \ {x} ∪ e₂.free, Finset.Subset.refl _, e₁.subst x hx₁ e₂⟩
    else
      have : e₁.free ⊆ e₁.free \ {x} ∪ e₂.free := by
        intro v hv
        have : v ∉ {x} := Finset.not_mem_singleton.mpr (fun heq : v = x => hx₁ (heq ▸ hv))
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, this⟩)

      ⟨e₁.free, this, e₁⟩

  | e => ⟨vs, Finset.Subset.refl _, e⟩

end Affine
