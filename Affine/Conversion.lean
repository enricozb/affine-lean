import «Affine».Lemmas
import «Affine».Misc

namespace Affine

def to_lambda (e : Affine vs) : Lambda :=
  match e with
  | .var x => .var x
  | .abs x e => .abs x e.to_lambda
  | .app e₁ e₂ _ => .app e₁.to_lambda e₂.to_lambda

def of_lambda {e : Lambda} (h : e.is_affine) : Affine e.free :=
  match e with
  | .var x => .var x
  | .abs x _ => .abs x (Affine.of_lambda (Lambda.is_affine_of_abs.mp h).1)
  | .app _ _ =>
    have ⟨he₁, he₂, hinter⟩ := Lambda.is_affine_of_app.mp h
    .app (Affine.of_lambda he₁) (Affine.of_lambda he₂) hinter

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
      to_lambda_is_affine e₁, to_lambda_is_affine e₂, true_and, decide_eq_true_eq,
      ← to_lambda_free_eq e₁, ← to_lambda_free_eq e₂, h]

end Affine
