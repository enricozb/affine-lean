import Mathlib.Data.Nat.Basic
import «Affine».Lemmas
import «Affine».Misc

inductive Lambda : Type
| var (x : ℕ) : Lambda
| abs (x : ℕ) (e : Lambda) : Lambda
| app (e₁ : Lambda) (e₂ : Lambda) : Lambda

namespace Lambda

/-- Number of times `x` occurs freely in `e`. -/
def count (e : Lambda) (x : ℕ) : ℕ :=
  match e with
  | .var x' => if x = x' then 1 else 0
  | .abs x' e => if x = x' then 0 else count e x
  | .app e₁ e₂ => count e₁ x + count e₂ x

/-- Whether all variables occur at most once. -/
def is_affine (e : Lambda) : Prop :=
  match e with
  | .var _ => True
  | .abs x e => is_affine e ∧ e.count x ≤ 1
  | .app e₁ e₂ => is_affine e₁ ∧ is_affine e₂ ∧ ∀ x, e₁.count x + e₂.count x ≤ 1

def to_string (e : Lambda) : String :=
  match e with
  | .var x => s!"{x}"
  | .abs x e => s!"(λ {x}. {e.to_string})"
  | .app e₁ e₂ => s!"{e₁.to_string} {e₂.to_string}"

end Lambda

namespace Affine

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

end Affine

instance : ToString (Affine vs) := ⟨fun e => e.to_lambda.to_string⟩

instance : ToString (Finset ℕ) := ⟨
  let trans : IsTrans String (· < ·) := sorry
  let trans : IsAntisymm String (· < ·) := sorry
  let trans : IsTotal String (· < ·) := sorry
  fun f => s!"\{{", ".intercalate (f.val.map ToString.toString |>.sort (· < ·))}}"
⟩

#eval (Affine.abs 1 (.app (.var 1) (.var 2) (by simp))) -- (λ 1. 1 2)

#eval (Affine.abs 1 (.app (.var 1) (.var 2) (by simp))).vars -- {1, 2}

-- next line will error since `1` occurs twice.
-- #eval (Affine.abs 1 (.app (.var 1) (.var 1) (by simp)))
