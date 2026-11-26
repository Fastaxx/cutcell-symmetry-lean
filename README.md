# cutcell-symmetry-lean

Lean 4 formalization of the discrete results of the article "Symmetry and Positive
Definiteness of a Two-Fluid Finite-Volume Method Based on Geometric Moments".
Equation numbers refer to the article.

## Build

Lean v4.34.0 and Mathlib v4.34.0.

```sh
lake exe cache get
lake build
lake env lean Axioms.lean
```

The build has no `sorry`. `Axioms.lean` shows that the main statements use only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Contents

| File | Article |
|---|---|
| `Operators.lean` | products (14), divergences (15), gradient (17)-(18), Theorem 2, Lemma 4, Assumption 2 |
| `Scheme.lean` | scheme (20), `X_lambda` and `a` (21)-(22), identity (24), Proposition 3 |
| `Symmetry.lean` | Proposition 5, uniqueness of the solution |
| `Matrices.lean` | matrix `A_red` (Section 6), existence of the solution |
| `Schur.lean` | harmonic extension (26), Proposition 6 (27)-(28), matrix `S_Gamma` |
| `Unsteady.lean` | weak form (29), energy identity (30), theta-scheme |

## Assumptions

Lemma 1 is geometric and is not proved here. It enters as the hypotheses of the structure
`Phase`. Propositions 5 and 6 assume Assumption 2 in both phases and at least one cut cell.

## License

Copyright 2026 Louis Libat. Released under the Apache License 2.0, see `LICENSE`.
