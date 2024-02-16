import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

/--
  Affine lambda terms, where bound variables can be used at most once.

  The choice of `Finset` over:
  - `List`: Can have duplicates.
  - `Set`: Can be infinite.
-/
inductive Affine : (vs : Finset String) → Type
| var (x : String) : Affine {x}
| abs (x : String) (e : Affine vs) : Affine (vs \ {x})
| app (e₁ : Affine vs₁) (e₂ : Affine vs₂) (h : vs₁ ∩ vs₂ = ∅) : Affine (vs₁ ∪ vs₂)

namespace Affine

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
  | .abs x e => is_affine e ∧ e.count x ≤ 1
  | .app e₁ e₂ _ => is_affine e₁ ∧ is_affine e₂ ∧ ∀ x, e₁.count x + e₂.count x ≤ 1

end Affine
