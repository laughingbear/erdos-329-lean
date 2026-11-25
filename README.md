# Erdős Problem 329: a Sidon set with upper density at least 1/2

A Lean 4 proof (Mathlib only) of two statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
file `FormalConjectures/ErdosProblems/329.lean`:

* `Erdos329.erdos_329.variants.lower_bound`: there is a Sidon set `A ⊆ ℕ` with
  `limsup |A ∩ [1, N]| / √N ≥ 1/2` (Erdős);
* `Erdos329.exists_sidon_pos_density`: there is a Sidon set with positive such upper density.

The definitions and both statements are copied verbatim from formal-conjectures.

**Construction.** Translates of the Erdős–Turán Sidon sets `{2pk + (k² mod p) : k < p}`
glued at rapidly growing scales. Each new block sits far enough above the previous ones, and
has large enough gaps, that the union stays Sidon. Just after each block the counting
function is about `p` while `N ≈ 4p²`, giving ratio `→ 1/2`. A short distinct-differences
bound (`|A ∩ [1, N]| ≤ 3√N`) makes the `limsup` a genuine one. Details are in the module
docstring of `Erdos329.lean`.

## Checking

Lean `v4.33.1`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` (the same pin as
formal-conjectures).

    lake exe cache get
    lake build --wfail

`#print axioms` for both theorems gives `[propext, Classical.choice, Quot.sound]`.

The proof was written with AI assistance (Claude).
