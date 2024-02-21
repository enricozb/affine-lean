import «Affine».AffineSubstitution

namespace Affine

structure SmallStepResult (vs₀ : Finset ℕ) where
  vs : Finset ℕ
  term : Affine vs
  sub : vs ⊆ vs₀

def small_step (e : Affine vs) : SmallStepResult vs :=
  match e with
  | .var x =>
    ⟨_, .var x, Finset.Subset.refl {x}⟩

  | .abs x e' =>
    have hsub : e'.small_step.vs \ {x} ⊆ e'.free \ {x} :=
      Finset.sdiff_subset_sdiff' _ e'.small_step.sub

    ⟨_, .abs x e'.small_step.2, hsub⟩

  | .app (.var x) e₂ h =>
    have hsub : {x} ∪ e₂.small_step.vs ⊆ {x} ∪ e₂.free :=
      Finset.union_subset_union (Finset.Subset.refl _) e₂.small_step.sub
    have hinter : {x} ∩ e₂.small_step.vs = ∅ := Finset.subset_empty.mp (Finset.Subset.trans
        (Finset.inter_subset_inter (Finset.Subset.refl _) e₂.small_step.sub)
        (Finset.subset_empty.mpr h))

    ⟨_, .app (.var x) e₂.small_step.2 hinter, hsub⟩

  | .app (.abs x e₁) e₂ h =>
    have hsub :
        (if x ∈ e₁.free then e₁.free \ {x} ∪ e₂.free else e₁.free) ⊆ e₁.free \ {x} ∪ e₂.free := by
      by_cases hx : x ∈ e₁.free
      · rw [if_pos hx]
      · rw [if_neg hx, Finset.sdiff_singleton_eq_self hx]
        exact Finset.subset_union_left _ _

    ⟨_, e₁.substₑ x e₂ h, hsub⟩

  | .app (.app e₁ e₂ h₁) e₃ h₂ =>
    have hinter₁₂ : e₁.small_step.vs ∩ e₂.small_step.vs = ∅ := by sorry
    have hinter₁₂₃ : (e₁.small_step.vs ∪ e₂.small_step.vs) ∩ e₃.small_step.vs = ∅ := by sorry
    have hsub₁₂₃ :
        e₁.small_step.vs ∪ e₂.small_step.vs ∪ e₃.small_step.vs ⊆ e₁.free ∪ e₂.free ∪ e₃.free := by
      sorry

    ⟨_, .app (.app e₁.small_step.2 e₂.small_step.2 hinter₁₂) e₃.small_step.2 hinter₁₂₃, hsub₁₂₃⟩

termination_by e.size

def small_step_free (e : Affine vs) : Finset ℕ := e.small_step.1
def small_step_term (e : Affine vs) : (Affine e.small_step_free) := e.small_step.2

theorem small_step_size_lt {e : Affine vs} (h : e.count_β ≠ 0) :
    e.small_step_term.size < e.size := by sorry

/-- Applies beta reductions until none remain. -/
def normalize (e : Affine vs) : (vs' : Finset ℕ) × (Affine vs') :=
  if hβ : e.count_β = 0 then
    ⟨vs, e⟩
  else
    have := small_step_size_lt hβ
    normalize e.small_step_term
termination_by e.size

end Affine
