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

theorem substᵥ_free {e : Lambda} : (e.substᵥ x y).free = e.free \ {x} ∪ {y} := by sorry

theorem substₑ_free {e₁ e₂ : Lambda} : (substₑ e₁ x e₂).free ⊆ e₁.free \ {x} ∪ e₂.free := by
  match e₁ with
  | .var x' =>
    simp only [free, substₑ, apply_ite]
    by_cases hx : x = x'
    · simp only [if_pos hx, Finset.subset_union_right]
    · simp only [if_neg hx, Finset.subset_union_left,
        Finset.sdiff_singleton_eq_self (Finset.mem_singleton.not.mpr hx)]
  | .abs x' e₁ =>
    simp only [free, substₑ]
    wlog hx : x ≠ x'
    · simp only [not_not] at hx
      simp only [if_pos (Or.inl hx), free, hx, Finset.sdiff_sdiff_left', Finset.inter_self,
        Finset.subset_union_left]
    wlog hxfree : x ∈ e₁.free
    · simp only [if_pos (Or.inr hxfree), free]
      intro v hv
      apply Finset.mem_union_left
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton]
      have hvx : v ≠ x := by intro hvx; rw [hvx] at hv; exact hxfree hv.left
      exact ⟨hv, hvx⟩
    rw [if_neg]
    by_cases hx' : x' ∈ e₂.free
    · simp only [if_pos hx', free]
      have hinc := substₑ_free (e₁ := e₁.substᵥ x' e₂.free.fresh) (e₂ := e₂) (x := x)
      rw [substᵥ_free] at hinc
      intro v hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hv
      have ⟨hv₁, hv₂⟩ := hv
      have hv' := hinc hv₁
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, hv₂, or_false] at hv'
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
      exact hv'
    · simp only [if_neg hx', free]
      have hinc := substₑ_free (e₁ := e₁) (e₂ := e₂) (x := x)
      intro v hv
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hv
      have ⟨hv₁, hv₂⟩ := hv
      have hv' := hinc hv₁
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton, hv₂, or_false] at hv'
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
      apply Or.elim hv'
      · intro hv; exact Or.inl ⟨⟨hv.left, hv₂⟩, hv.right⟩
      · exact Or.inr

    case hnc => simp only [not_or, not_not, hx, hxfree, not_false_eq_true, true_and]
  | .app a₁ a₂ =>
    simp only [free, substₑ]
    intro v hv
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hv
    apply Or.elim hv
    · intro hv₁
      have hv₁ := substₑ_free hv₁
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hv₁
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
      exact Or.elim hv₁ (fun hv' => Or.inl ⟨Or.inl hv'.left, hv'.right⟩) Or.inr
    · intro hv₂
      have hv₂ := substₑ_free hv₂
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton] at hv₂
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
      apply Or.elim hv₂ (fun hv' => Or.inl ⟨Or.inr hv'.left, hv'.right⟩) Or.inr

termination_by e₁.depth


theorem substᵥ_count_β {e : Lambda} : (e.substᵥ x y).count_β = e.count_β := by sorry

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

theorem is_affine_substₑ {e₁ e₂ : Lambda} (he₁ : e₁.is_affine) (he₂ : e₂.is_affine) (x : ℕ) :
    (e₁.substₑ x e₂).is_affine := by
  sorry

theorem substₑ_count_β {e₁ e₂ : Lambda} (h₁ : e₁.is_affine) (h₂ : e₂.is_affine) :
    (e₁.substₑ x e₂).count_β < 1 + e₁.count_β + e₂.count_β := by
  sorry
  -- match e₁ with
  -- | .var x' =>
  --   have h₁ : e₂.count_β < 1 + e₂.count_β := lt_one_add _
  --   have h₂ : 0 < 1 + e₂.count_β := by simp only [add_pos_iff, zero_lt_one, true_or]
  --   simp only [substₑ, count_β, add_zero, apply_ite, ite_lt h₁ h₂]

  -- | .abs x' e₁ =>
  --   simp only [substₑ, count_β, apply_ite count_β]
  --   wlog hx₁ : x ∈ e₁.free
  --   · simp only [if_pos (Or.inr hx₁), add_assoc, Nat.lt_one_add_iff.mpr, le_add_iff_nonneg_right,
  --       zero_le]
  --   wlog hxeq : x ≠ x'
  --   · simp only [if_pos (Or.inl (not_not.mp hxeq)), add_assoc, Nat.lt_one_add_iff.mpr,
  --       le_add_iff_nonneg_right, zero_le]
  --   rw [if_neg]
  --   by_cases hx' : x' ∈ e₂.free
  --   · rw [if_pos hx']
  --     have hinc := substₑ_count_β (e₁ := e₁.substᵥ x' e₂.free.fresh) (e₂ := e₂) (x := x)
  --     simp [substᵥ_count_β] at hinc
  --     exact hinc
  --   · simp only [if_neg hx', substₑ_count_β (e₁ := e₁)]
  --   simp only [not_or, not_not, hx₁, hxeq, not_false_eq_true, true_and]

  -- | .app a₁ a₂ =>
  --   simp only [substₑ, count_β]
  --   have x := count_β_of_app (e₁ := substₑ a₁ x e₂) (e₂ := substₑ a₂ x e₂)

-- termination_by e₁.depth

end Lambda
