
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
  | .app e₁ e₂ h =>
    refine' ⟨affine_is_affine e₁, affine_is_affine e₂, _⟩
    intro x'
    have : count e₁ x' = 0 ∨ count e₂ x' = 0 := by
      by_contra hc
      rw [not_or] at hc
      have : x' ∈ e₁.free ∩ e₂.free := Finset.mem_inter.mpr ⟨
        (count_ne_zero_iff e₁ x').mp hc.left,
        (count_ne_zero_iff e₂ x').mp hc.right
      ⟩
      rw [h] at this
      contradiction

    apply Or.elim this
    · intro h₁; simp_rw [h₁, zero_add, is_affine_count_le_one (affine_is_affine e₂) x']
    · intro h₂; simp_rw [h₂, add_zero, is_affine_count_le_one (affine_is_affine e₁) x']

def to_lambda (e : Affine vs) : Lambda :=
  match e with
  | .var x => .var x
  | .abs x e => .abs x e.to_lambda
  | .app e₁ e₂ _ => .app e₁.to_lambda e₂.to_lambda

theorem to_lambda_is_affine (e : Affine vs) : e.to_lambda.is_affine := by sorry

theorem count_eq_to_lambda_count (e : Affine vs) : ∀ x, e.to_lambda.count x = e.count x := by
  match e with
  | .var x => simp only [Lambda.count, count, forall_const]
  | .abs x e => simp_rw [Lambda.count, count, count_eq_to_lambda_count e, forall_const]
  | .app e₁ e₂ h => simp_rw [Lambda.count, count, count_eq_to_lambda_count e₁,
    count_eq_to_lambda_count e₂, forall_const]

/--
  `Affine` from `Lambda`.

  We provide 3-tuple of the finset of free variables and a proof of equality `Affine.to_lambda`
  as it's needed during induction for the `.app` case to produce the null_intersection argument
  of `Affine.app`.
-/
def of_lambda_impl (e : Lambda) (he : e.is_affine) :
    (vs : Finset ℕ) × (e' : Affine vs) ×' (e = e'.to_lambda) :=
  match e with
  | .var x => ⟨_, .var x, by simp only [to_lambda]⟩

  | .abs x e =>
    let ⟨e_free, e, he⟩ := of_lambda_impl e he.left
    ⟨e_free \ {x}, .abs x e, by simp only [he, to_lambda]⟩

  | .app e₁ e₂ =>
    have ⟨h₁, h₂, h⟩ := he
    let ⟨⟨e₁_free, e₁', he₁⟩, ⟨e₂_free, e₂', he₂⟩⟩ :=
      (of_lambda_impl e₁ h₁, of_lambda_impl e₂ h₂)
    have h_inter : e₁_free ∩ e₂_free = ∅ := by
      simp_rw [he₁, he₂, count_eq_to_lambda_count] at h

      by_contra h_inter
      have ⟨v, hv⟩ := Finset.nonempty_of_ne_empty h_inter
      have ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
      have hv₁ := (count_ne_zero_iff e₁' v).mpr hv₁
      have hv₂ := (count_ne_zero_iff e₂' v).mpr hv₂
      exact Or.elim (Nat.add_le_one (h v)) hv₁ hv₂

    have h_eq : Lambda.app e₁ e₂ = (Affine.app e₁' e₂' h_inter).to_lambda := by
      simp only [he₁, he₂, to_lambda]

    ⟨e₁_free ∪ e₂_free, .app e₁' e₂' h_inter, h_eq⟩

def of_lambda (e : Lambda) (he : e.is_affine) : Affine (of_lambda_impl e he).1 :=
  (Affine.of_lambda_impl e he).2.1

theorem of_lambda_to_lambda (e : Lambda) (he : e.is_affine) :
    e = (Affine.of_lambda e he).to_lambda := (of_lambda_impl e he).2.2

theorem to_lambda_of_lambda_free (e : Affine vs) :
  vs = (Affine.of_lambda e.to_lambda e.to_lambda_is_affine).free := by sorry

-- theorem to_lambda_of_lambda (e : Affine vs) :
--     e = to_lambda_of_lambda_free e ▸ (Affine.of_lambda e.to_lambda _) := by
--   match e with
--   | .var x => rfl
--   | .abs x e =>
--     have he := to_lambda_of_lambda e
--     rw [of_lambda] at he
--     simp_rw [to_lambda, of_lambda, of_lambda_impl, he]


--   | .app e₁ e₂ h => sorry
