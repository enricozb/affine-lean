import «Affine».Lemmas
import «Affine».Misc

namespace Affine

def to_lambda (e : Affine vs) : Lambda :=
  match e with
  | .var x => .var x
  | .abs x e => .abs x e.to_lambda
  | .app e₁ e₂ _ => .app e₁.to_lambda e₂.to_lambda

theorem to_lambda_free_eq (e : Affine vs) : e.free = e.to_lambda.free := by
  match e with
  | .var x => simp only [free, to_lambda, Lambda.free]
  | .abs x e => simp only [free, to_lambda, Lambda.free, to_lambda_free_eq e]
  | .app e₁ e₂ h =>
    simp only [free, to_lambda, Lambda.free, to_lambda_free_eq e₁, to_lambda_free_eq e₂]

theorem to_lambda_count_eq (e : Affine vs) : e.count x = e.to_lambda.count x := by
  match e with
  | .var x' => simp only [count, to_lambda, Lambda.count]
  | .abs x' e => simp only [count, to_lambda, Lambda.count, to_lambda_count_eq e]
  | .app e₁ e₂ h =>
    simp only [count, to_lambda, Lambda.count, to_lambda_count_eq e₁, to_lambda_count_eq e₂]

theorem to_lambda_is_affine (e : Affine vs) : e.to_lambda.is_affine := by
  match e with
  | .var x => simp only [to_lambda, Lambda.is_affine]
  | .abs x e =>
    have he := to_lambda_is_affine e
    have hc := Lambda.affine_count_le_one he
    simp only [to_lambda, Lambda.is_affine, he, hc, true_and, decide_True]
  | .app e₁ e₂ h =>
    simp only [to_lambda, Lambda.is_affine, Lambda.free,
      to_lambda_is_affine e₁, to_lambda_is_affine e₂, true_and, decide_eq_true_eq]
    intro x hx
    rw [← to_lambda_free_eq e₁, ← to_lambda_free_eq e₂] at hx
    apply Or.elim (Finset.mem_union.mp hx)
    · intro hx₁
      have hx₂ : x ∉ e₂.free := fun hx₂ =>
        Finset.eq_empty_iff_forall_not_mem.mp h x (Finset.mem_inter.mpr ⟨hx₁, hx₂⟩)
      simp only [count, ← to_lambda_count_eq, count_not_mem_free hx₂, add_zero,
        affine_count_le_one e₁ x]
    · intro hx₂
      have hx₁ : x ∉ e₁.free := fun hx₁ =>
        Finset.eq_empty_iff_forall_not_mem.mp h x (Finset.mem_inter.mpr ⟨hx₁, hx₂⟩)
      simp only [count, ← to_lambda_count_eq, count_not_mem_free hx₁, zero_add,
        affine_count_le_one e₂ x]

end Affine

#eval (Affine.abs 1 (.app (.var 1) (.var 2) (by simp))) -- (λ 1. 1 2)
#eval (Affine.abs 1 (.app (.var 2) (.var 1) (by simp))).vars -- {1, 2}
