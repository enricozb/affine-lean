import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Card
import Mathlib.Data.Nat.Basic

/-- Affine lambda terms, where bound variables can be used at most once. -/
inductive Affine : (vs : Set String) → Type
| var (x : String) : Affine {x}
| abs (x : String) (e : Affine vs) : Affine (vs \ {x})
| app (e₁ : Affine vs₁) (e₂ : Affine vs₂) (h : vs₁ ∩ vs₂ = ∅) : Affine (vs₁ ∪ vs₂)

/-- How many times `x` occurs freely in `e`. -/
def count (e : Affine vs) (x : String) : ℕ :=
  match e with
  | .var x' => if x = x' then 1 else 0
  | .abs x' e => if x = x' then 0 else count e x
  | .app e₁ e₂ _ => count e₁ x + count e₂ x

/-- Affinity: Whether all variables occur at most once. -/
def is_affine (e : Affine vs) : Prop :=
  match e with
  | .var x => True
  | .abs x e => is_affine e ∧ ∀ x' ≠ x, count e x' ≤ 1
  | .app e₁ e₂ _ => is_affine e₁ ∧ is_affine e₂ ∧ ∀ x, count e₁ x + count e₂ x ≤ 1

theorem count_ne_zero_iff (e : Affine vs) (x : String) : count e x ≠ 0 ↔ x ∈ vs := by
  match e with
  | .var x' =>
    simp only [count, ne_eq, ite_eq_right_iff, imp_false, not_not, Set.mem_singleton_iff]
  | .abs x' e =>
    simp only [count, ne_eq, ite_eq_left_iff, not_forall, Set.mem_singleton_iff]
    exact ⟨
      fun ⟨hneq, hc⟩ => ⟨(count_ne_zero_iff e x).mp hc, hneq⟩,
      fun ⟨hmem, hneq⟩ => ⟨hneq, (count_ne_zero_iff e x).mpr hmem⟩
    ⟩
  | @Affine.app vs₁ vs₂ e₁ e₂ h =>
    simp only [count]
    apply Iff.intro
    · intro h_add_ne_zero
      have hc : count e₁ x ≠ 0 ∨ count e₂ x ≠ 0 := by
        by_contra hc
        simp_rw [not_or, not_not] at hc
        have ⟨h₁, h₂⟩ := hc
        rw [h₁, h₂, add_zero] at h_add_ne_zero
        contradiction
      exact Or.elim hc
        (fun h₁ => Set.mem_union_left _ ((count_ne_zero_iff e₁ x).mp h₁))
        (fun h₂ => Set.mem_union_right _ ((count_ne_zero_iff e₂ x).mp h₂))

    · intro hmem h_add_eq_zero
      have ⟨h₁, h₂⟩ := Nat.add_eq_zero_iff.mp h_add_eq_zero
      have : ¬(x ∈ vs₁ ∨ x ∈ vs₂) := not_or.mpr ⟨
        (count_ne_zero_iff e₁ x).not_right.mp h₁,
        (count_ne_zero_iff e₂ x).not_right.mp h₂
      ⟩
      contradiction

/-- If a term is affine then all variables occur at most once. -/
theorem is_affine_count_le_one (h : is_affine e) : ∀ x, count e x ≤ 1 := by
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
      · have : x ∈ vs₁ ∩ vs₂ := ⟨h₁, h₂⟩
        have : (vs₁ ∩ vs₂) ≠ ∅ := Set.nonempty_iff_ne_empty.mp (Set.nonempty_of_mem this)
        contradiction
      · simp_rw [of_not_not ((count_ne_zero_iff e₂ x).not.mpr h₂), add_zero,
          is_affine_count_le_one h_affine_e₁ x]

    · simp_rw [of_not_not ((count_ne_zero_iff e₁ x).not.mpr h₁), zero_add,
        is_affine_count_le_one h_affine_e₂ x]

/-- Terms of type `Affine` are affine. -/
theorem Affine.is_affine (e : Affine vs) : is_affine e := by
  unfold is_affine

  match e with
  | .var x => simp only
  | .abs x e => exact ⟨e.is_affine, fun x' _ => is_affine_count_le_one e.is_affine x'⟩
  | @Affine.app vs₁ vs₂ e₁ e₂ h =>
    refine' ⟨e₁.is_affine, e₂.is_affine, _⟩
    intro x'
    have : count e₁ x' = 0 ∨ count e₂ x' = 0 := by
      by_contra hc
      rw [not_or] at hc
      have : x' ∈ vs₁ ∩ vs₂ := ⟨
        (count_ne_zero_iff e₁ x').mp hc.left,
        (count_ne_zero_iff e₂ x').mp hc.right
      ⟩
      rw [h] at this
      contradiction

    apply Or.elim this
    · intro h₁; simp_rw [h₁, zero_add, is_affine_count_le_one e₂.is_affine x']
    · intro h₂; simp_rw [h₂, add_zero, is_affine_count_le_one e₁.is_affine x']

-- TODO: normalizer
-- TODO: proof of normal form
