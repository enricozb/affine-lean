import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

/--
  Lambda terms without any restrictions to the multiplicity of bound or free variables.

  This is used for normalization and substitution `Affine vs` has complex dependent values of `vs`.
-/
inductive Lambda : Type
| var (x : ℕ) : Lambda
| abs (x : ℕ) (e : Lambda) : Lambda
| app (e₁ : Lambda) (e₂ : Lambda) : Lambda

namespace Lambda

/-- The size of a lambda, useful for `termination_by`. -/
def depth (e : Lambda) : ℕ :=
  match e with
  | .var _ => 0
  | .abs _ e => 1 + e.depth
  | .app e₁ e₂ => 1 + max e₁.depth e₂.depth

/-- Number of times `x` occurs freely in `e`. -/
def count (e : Lambda) (x : ℕ) : ℕ :=
  match e with
  | .var x' => if x = x' then 1 else 0
  | .abs x' e => if x = x' then 0 else count e x
  | .app e₁ e₂ => count e₁ x + count e₂ x

/-- Free variables in `e`. -/
def free (e : Lambda) : Finset ℕ :=
  match e with
  | .var x => {x}
  | .abs x e => e.free \ {x}
  | .app e₁ e₂ => e₁.free ∪ e₂.free

/-- Whether all variables occur at most once. -/
def is_affine (e : Lambda) : Bool :=
  match e with
  | .var _ => true
  | .abs x e => is_affine e ∧ e.count x ≤ 1
  | .app e₁ e₂ => is_affine e₁ ∧ is_affine e₂ ∧ ∀ x ∈ e.free, e₁.count x + e₂.count x ≤ 1

def to_string (e : Lambda) : String :=
  match e with
  | .var x => s!"{x}"
  | .abs x e => s!"(λ {x}. {e.to_string})"
  | .app e₁ e₂ => s!"{e₁.to_string} {e₂.to_string}"

end Lambda

instance : ToString Lambda := ⟨Lambda.to_string⟩