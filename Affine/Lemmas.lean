import «Affine».Defs

open Affine

/-- For affine terms `e : Affine vs`, `vs` represents free occurrences of variables. -/
theorem count_ne_zero_iff (e : Affine vs) (x : String) : e.count x ≠ 0 ↔ x ∈ vs := by
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

  | @Affine.app vs₁ vs₂ e₁ e₂ h =>
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

      have hmem : x ∈ vs₁ ∨ x ∈ vs₂ := Finset.mem_union.mp hmem
      have : ¬(x ∈ vs₁ ∨ x ∈ vs₂) := not_or.mpr ⟨
        (count_ne_zero_iff e₁ x).not_right.mp h₁,
        (count_ne_zero_iff e₂ x).not_right.mp h₂
      ⟩

      contradiction

/--
  If a term is affine then all free variables occur at most once. This is a useful lemma when
  showing that `e : Affine vs` is affine.

  Note: this does not imply a term is affine, as `e := (λ x. x x)` is not affine but has no free
  variables, and therefore `∀ x, e.count x = 0`.
-/
theorem is_affine_count_le_one (h : is_affine e) : ∀ x, e.count x ≤ 1 := by
  intro x

  match e with
  | .var x' =>
    by_cases hx' : x = x'
    · rw [count, if_pos hx']
    · simp_rw [count, if_neg hx', Nat.zero_le 1]

  | .abs x' e =>
    by_cases hx' : x = x'
    · simp_rw [count, if_pos hx', Nat.zero_le 1]
    · simp only [is_affine] at h
      simp_rw [count, if_neg hx', is_affine_count_le_one h.left x]

  | @Affine.app vs₁ vs₂ e₁ e₂ h' =>
    unfold count
    simp only [is_affine] at h
    have ⟨h_affine_e₁, h_affine_e₂, _⟩ := h
    by_cases h₁ : x ∈ vs₁
    · by_cases h₂ : x ∈ vs₂
      · have : x ∈ vs₁ ∩ vs₂ := Finset.mem_inter.mpr ⟨h₁, h₂⟩
        have : (vs₁ ∩ vs₂) ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Set.nonempty_of_mem this)
        contradiction
      · simp_rw [of_not_not ((count_ne_zero_iff e₂ x).not.mpr h₂), add_zero,
          is_affine_count_le_one h_affine_e₁ x]

    · simp_rw [of_not_not ((count_ne_zero_iff e₁ x).not.mpr h₁), zero_add,
        is_affine_count_le_one h_affine_e₂ x]

/-- Terms of type `Affine` are affine. -/
theorem affine_is_affine (e : Affine vs) : is_affine e := by
  unfold is_affine

  match e with
  | .var x => simp only
  | .abs x e => exact ⟨affine_is_affine e, is_affine_count_le_one (affine_is_affine e) x⟩
  | @Affine.app vs₁ vs₂ e₁ e₂ h =>
    refine' ⟨affine_is_affine e₁, affine_is_affine e₂, _⟩
    intro x'
    have : count e₁ x' = 0 ∨ count e₂ x' = 0 := by
      by_contra hc
      rw [not_or] at hc
      have : x' ∈ vs₁ ∩ vs₂ := Finset.mem_inter.mpr ⟨
        (count_ne_zero_iff e₁ x').mp hc.left,
        (count_ne_zero_iff e₂ x').mp hc.right
      ⟩
      rw [h] at this
      contradiction

    apply Or.elim this
    · intro h₁; simp_rw [h₁, zero_add, is_affine_count_le_one (affine_is_affine e₂) x']
    · intro h₂; simp_rw [h₂, add_zero, is_affine_count_le_one (affine_is_affine e₁) x']
