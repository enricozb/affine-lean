# Affine Lambda Calculus in Lean

## Definitions
- [`Affine`][1] are affine lambda terms:
```
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
```
inductive Lambda : Type
| var (x : ℕ) : Lambda
| abs (x : ℕ) (e : Lambda) : Lambda
| app (e₁ : Lambda) (e₂ : Lambda) : Lambda
```

## Normalization
In [`Normalize.lean`][3] we define `Affine.normalize`, which repeatedly applies
β-reductions until none are left. This is done by first converting the `Affine` term
to a `Lambda` term, since typing is easier there.

~Terminations is proven by counting the nubmer of β-reductions remaining, which always
decreases after an application of `small_step`, unless there are none.~

Beta reductions aren't strictly decreasing under small steps. For example, the following
small_step reduction of an affine term has one beta reduction before and after:
```
(\ x. x y) (\ z. z) -> (\ z. z) y
```

Need to find some metric that is strictly decreasing under `small_step`.

In [`Normalize.lean`][3], we also have `Affine.normalize_is_normal`, which proves that,
after normalizing, no β-reductions remain.

## TODO
In retrospect I should have used [De Bruijn index][4] in order to side-step the complications
when renaming variables during substitutions.

[1]: ./Affine/Affine.lean
[2]: ./Affine/Lambda.lean
[3]: ./Affine/Normalize.lean
[4]: https://en.wikipedia.org/wiki/De_Bruijn_index
