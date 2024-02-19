# Affine Lambda Calculus in Lean

Proof that affine lambda terms always terminate when evaluated. This is done by
1. Defining `Affine` lambda terms.
2. Defining `Affine.is_normal`, which are terms that have no beta reductions remaining.
3. Defining `Affine.normalization` which applies all beta reductions.

## Definitions
- [`Affine`][1] are affine lambda terms:
```lean
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
```
This definition tracks the free variables and ensures affinity.

- [`Lambda`][2] are general lambda terms, which don't track their free variables:
```lean
inductive Lambda : Type
| var (x : ℕ) : Lambda
| abs (x : ℕ) (e : Lambda) : Lambda
| app (e₁ : Lambda) (e₂ : Lambda) : Lambda
```

## Normalization
In [`Normalize.lean`][3] we define `Affine.normalize`, which repeatedly applies
β-reductions until none are left. This is done by first converting the `Affine` term
to a `Lambda` term, since typing is easier there.

In [`Normalize.lean`][3], we also have `Affine.normalize_is_normal`, which proves that,
after normalizing, no β-reductions remain.

## Termination
Since lean only allows for functions that terminate, the fact that `Affine.normalize` type
checks, proves that it terminates, by the definition of `size` below.

Termination is proved by showing that the "size" of a lambda is strictly decreasing when
applying a small step. That is,
```lean
/-- The number of abstractions, useful for `termination_by` for normalization. -/
def size (e : Affine vs) : ℕ :=
  match e with
  | .var _ => 0
  | .abs _ e => 1 + e.size
  | .app e₁ e₂ _ => e₁.size + e₂.size

/-- Small steps are stricftly decreasing for non-normal affine terms. -/
theorem small_step_size_lt {e : Affine vs} (hβ : e.count_β ≠ 0) :
    e.small_step.size < e.size := by
  rw [← to_lambda_count_β_eq] at hβ
  rw [← e.small_step.to_lambda_size_eq, ← e.to_lambda_size_eq, ← e.to_lambda_small_step]
  exact Lambda.small_step_size_lt e.to_lambda_is_affine hβ

/-- Applies beta reductions until none remain. -/
def normalize (e : Affine vs) : (vs' : Finset ℕ) × (Affine vs') :=
  if hβ : e.count_β = 0 then
    ⟨vs, e⟩
  else
    have := small_step_size_lt hβ
    normalize e.small_step
termination_by e.size
```

## TODO
1. In retrospect I should have used [De Bruijn index][4] in order to side-step the complications
when renaming variables during substitutions.

2. Instead of converting to a `Lambda`, perhaps keeping everything in `Affine vs` would be
simpler. A lot of the substitution proofs are extremely convoluted. They are only complicated
by the fact that we need to carry around affinity assumptions around for many of them.

[1]: ./Affine/Affine.lean
[2]: ./Affine/Lambda.lean
[3]: ./Affine/Normalize.lean
[4]: https://en.wikipedia.org/wiki/De_Bruijn_index
