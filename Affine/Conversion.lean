import «Affine».Lemmas
import «Affine».Misc

namespace Affine

/-- Converts an `e : Affine vs` to a `Lambda`. -/
def to_lambda (e : Affine vs) : Lambda :=
  match e with
  | .var x => .var x
  | .abs x e => .abs x e.to_lambda
  | .app e₁ e₂ _ => .app e₁.to_lambda e₂.to_lambda

/-- Converts an affine `e : Lambda` to an `Affine e.free`. -/
def of_lambda {e : Lambda} (h : e.is_affine) : Affine e.free :=
  match e with
  | .var x => .var x
  | .abs x _ => .abs x (Affine.of_lambda (Lambda.is_affine_of_abs.mp h).1)
  | .app _ _ =>
    .app
      (Affine.of_lambda (Lambda.is_affine_of_app.mp h).1)
      (Affine.of_lambda (Lambda.is_affine_of_app.mp h).2.1)
      (Lambda.is_affine_of_app.mp h).2.2

/-- Conversions preserve free variables. -/
theorem to_lambda_free_eq (e : Affine vs) : e.free = e.to_lambda.free := by
  match e with
  | .var _ => rfl
  | .abs _ e => simp only [free, to_lambda, Lambda.free, to_lambda_free_eq e]
  | .app e₁ e₂ h =>
    simp only [free, to_lambda, Lambda.free, to_lambda_free_eq e₁, to_lambda_free_eq e₂]

/-- Conversions preserve counts. -/
theorem to_lambda_count_eq (e : Affine vs) : e.count x = e.to_lambda.count x := by
  match e with
  | .var _ => rfl
  | .abs _ e => simp only [count, to_lambda, Lambda.count, to_lambda_count_eq e]
  | .app e₁ e₂ h =>
    simp only [count, to_lambda, Lambda.count, to_lambda_count_eq e₁, to_lambda_count_eq e₂]

/-- Conversions preserve affinity. -/
theorem to_lambda_is_affine (e : Affine vs) : e.to_lambda.is_affine := by
  match e with
  | .var _ => rfl
  | .abs _ e =>
    have he := to_lambda_is_affine e
    have hc := Lambda.affine_count_le_one he
    simp only [to_lambda, Lambda.is_affine, he, hc, true_and, decide_True]
  | .app e₁ e₂ h =>
    simp only [to_lambda, Lambda.is_affine, Lambda.free,
      to_lambda_is_affine e₁, to_lambda_is_affine e₂, true_and, decide_eq_true_eq,
      ← to_lambda_free_eq e₁, ← to_lambda_free_eq e₂, h]

theorem to_lambda_count_β_eq (e : Affine vs) : e.to_lambda.count_β = e.count_β := by
  match e with
  | .var _ => rfl
  | .abs _ _ => simp only [to_lambda, Lambda.count_β, count_β_of_abs, to_lambda_count_β_eq]
  | .app (.var _) _ _ =>
    simp only [to_lambda, Lambda.count_β, count_β_of_app_var, to_lambda_count_β_eq]
  | .app (.abs _ _) _ _ =>
    simp only [to_lambda, Lambda.count_β, count_β_of_app_abs, to_lambda_count_β_eq]
  | .app (.app _ _ _) _ _ =>
    simp only [to_lambda, Lambda.count_β, count_β_of_app_app, to_lambda_count_β_eq]

end Affine

namespace Lambda

theorem of_lambda_to_lambda {e : Lambda} (h : e.is_affine) : (Affine.of_lambda h).to_lambda = e
    := by
  match e with
  | .var _ => rfl
  | .abs _ e =>
    simp only [Affine.of_lambda, Affine.to_lambda, abs.injEq, true_and, of_lambda_to_lambda]
  | .app e₁ e₂ =>
    simp only [is_affine, decide_eq_true_eq] at h
    simp only [Affine.of_lambda, Affine.to_lambda, h, of_lambda_to_lambda]

end Lambda
