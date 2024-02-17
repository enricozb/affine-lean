import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Sort

/--
  Affine lambda terms, where bound variables can be used at most once.

  The choice of `Finset` over:
  - `List`: Can have duplicates.
  - `Set`: Can be infinite.
-/
inductive Affine : (vs : Finset ℕ) → Type
| var (x : ℕ) : Affine {x}
| abs (x : ℕ) (e : Affine vs) : Affine (vs \ {x})
| app (e₁ : Affine vs₁) (e₂ : Affine vs₂) (h : vs₁ ∩ vs₂ = ∅) : Affine (vs₁ ∪ vs₂)

namespace Affine

/-- The size of a lambda, useful for `termination_by`. -/
def depth (e : Affine vs) : ℕ :=
  match e with
  | .var _ => 0
  | .abs _ e => 1 + e.depth
  | .app e₁ e₂ _ => 1 + max e₁.depth e₂.depth

/-- The free variables in an affine term. -/
abbrev free (_ : Affine vs) : Finset ℕ := vs

/-- All variables in `e`. -/
abbrev vars (e : Affine vs) : Finset ℕ :=
  match e with
  | .var x => {x}
  | .abs x e => e.vars ∪ {x}
  | .app e₁ e₂ _ => e₁.vars ∪ e₂.vars

/-- Number of times `x` occurs freely in `e`. -/
def count (e : Affine vs) (x : ℕ) : ℕ :=
  match e with
  | .var x' => if x = x' then 1 else 0
  | .abs x' e => if x = x' then 0 else count e x
  | .app e₁ e₂ _ => count e₁ x + count e₂ x

/-- Number of β-reductions. That is, `(λ x. e₁) e₂`. -/
def count_β (e : Affine vs) : ℕ :=
  match e with
  | .var x => 0
  | .abs _ e => e.count_β
  | .app (.var _) e₂ _ => e₂.count_β
  | .app (.abs _ e₁) e₂ _ => 1 + e₁.count_β + e₂.count_β
  | .app (.app e₁ e₂ _) e₃ _ => e₁.count_β + e₂.count_β + e₃.count_β

/-- Whether all variables occur at most once. -/
def is_affine (e : Affine vs) : Bool :=
  match e with
  | .var _ => true
  | .abs x e => is_affine e ∧ e.count x ≤ 1
  | .app e₁ e₂ _ => is_affine e₁ ∧ is_affine e₂ ∧ ∀ x ∈ e.free, e₁.count x + e₂.count x ≤ 1

def to_string (e : Affine vs) : String :=
  match e with
  | .var x => s!"{x}"
  | .abs x e => s!"(λ {x}. {e.to_string})"
  | .app e₁ e₂ _ => s!"{e₁.to_string} {e₂.to_string}"

end Affine

instance : ToString (Affine vs) := ⟨Affine.to_string⟩
