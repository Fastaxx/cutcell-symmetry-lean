# lean-verif

Lean 4 / Mathlib formalization of the proofs of the CRAS article
*Symmetry and Positive Definiteness of a Two-Fluid Finite-Volume Method Based on Geometric
Moments* (`../main.tex`). Equation and statement numbers below are those of the compiled
article.

Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (see `lakefile.toml`).

```sh
lake exe cache get        # prebuilt Mathlib (once)
lake build                # no `sorry`, no warning
lake env lean Axioms.lean # every main statement uses only propext, Classical.choice, Quot.sound
```

## The model

A piecewise constant function is identified with its coefficients, and the `L²` products
are the weighted sums (13). One phase is a structure `CutCell.Phase C F I`:

| article | Lean |
|---|---|
| active cells `𝓜^±`, active faces `𝓔^±`, interface cells `𝓜^Γ` | types `C`, `F`, `I` (`ι : I ↪ C`) |
| `n_{K,σ}·e_α` (`0` if `σ ∉ 𝓔(K)`) | `ne K σ` |
| `|K^±|, |σ^±|, |S^α_K|, |D_σ|, |Γ_K|` | `V, A, B, W, G` (the moments `V, A, B, W, Γ` of [1]) |
| `𝓔_D` | `Dir` |
| `Φ ∈ X_𝓜`, `Φ_Γ ∈ X_Γ`, `Q ∈ H_𝓔` | `C → ℝ`, `I → ℝ`, `F → ℝ` |
| `(Φ, Φ_Γ)`, two-phase state `(Φ̲^-, Φ̲^+)` | `Phase.Field` (fields `M`, `Γ`), `Pair` (fields `m`, `p`) |
| `X_λ` | `TwoPhase.InX` |
| `r̄^±` (cell means of `r^±`) | the source arguments `rm`, `rp` |

The moment formulas (14)–(15) are the definitions, written as sums over the faces with
`ne`; the forms printed in the article are `divK_eq_sections`, `divΓK_eq_sections` and
`W_mul_grad_of_twoCells`. Their derivation from the divergence theorem and Lemma 1 are
geometric and are not formalized: Lemma 1 enters as the hypotheses of `Phase` (`uncut` is
Lemma 1(c); `interior`, `dirichlet` say that a face with `|σ^±| ≠ 0` has one neighbour on
each side unless it is a Dirichlet face, which has one; positivity of `V, W, G` is Lemma
1(e) and the definition of the active sets; `TwoPhase.G_eq` is the shared `X_Γ` of Lemma
1(a)). Assumption 1 is therefore implicit in the structure.

## Correspondence

| article | Lean declaration | file |
|---|---|---|
| (13) `L²` products | `Phase.innerM`, `Phase.innerΓ`, `Phase.innerE` | `Operators` |
| §4.2 flux through `∂K^±` = wetted faces + `Γ_K` | `Phase.divWet`, `divΓK`, `divK`, `divK_eq_add` | `Operators` |
| (14) `div_𝓜`, `div_Γ` | `Phase.divM`, `divΓ`, `divK_eq_sections`, `divΓK_eq_sections` | `Operators` |
| (15)–(16) gradient | `Phase.grad`, `W_mul_grad`, `W_mul_grad_of_twoCells` | `Operators` |
| **Theorem 2**, (17) | `Phase.green` | `Operators` |
| (18) scheme | `TwoPhase.Scheme` | `Scheme` |
| (19) `X_λ`, `a` | `TwoPhase.InX`, `TwoPhase.a` | `Scheme` |
| **Proposition 3** (weak form), (20) | `TwoPhase.weak_form` | `Scheme` |
| (21) residual identity | `TwoPhase.residuals` | `Scheme` |
| **Lemma 4** (constants) | `Phase.grad_const_interior`, `Phase.grad_const_dirichlet` | `Operators` |
| Assumption 2, anchored phase | `Phase.Connected`, `Phase.Anchored` | `Operators` |
| **Proposition 5**, (22) | `TwoPhase.a_comm`, `a_self_nonneg`, `a_definite`, `a_kernel` | `Scheme`, `Symmetry` |
| unique solution (after Proposition 5) | `TwoPhase.scheme_unique`, `TwoPhase.scheme_existsUnique` | `Symmetry`, `Matrices` |
| (23) harmonic extension, existence and uniqueness | `TwoPhase.H`, `H_harmonic`, `H_existsUnique` | `Schur` |
| (23) ⟺ `div_𝓜(k^± ∇_𝒟 (ℋη)^±) = 0` | `TwoPhase.harmonic_iff_div_grad` (`harmonic_iff_div` with `Q^±`) | `Schur` |
| **Proposition 6**, (24) | `TwoPhase.s_comm`, `s_isLeast`, `s_DtN`, `s_definite`, `s_kernel` | `Schur` |
| **Proposition 6**, (25) reduction | `TwoPhase.scheme_iff_interface` | `Schur` |
| (26) semi-discrete weak form | `TwoPhase.weak_unsteady` | `Unsteady` |
| (27) energy identity | `TwoPhase.energy_rate` | `Unsteady` |
| `θ`-scheme remark (§5.4) | `TwoPhase.theta_energy` | `Unsteady` |
| §6: `A_red` = matrix of `a` | `TwoPhase.Ared`, `dotProduct_Ared`, `Ared_isSymm`, `Ared_posDef`, `Ared_kernel` | `Matrices` |
| §6: scheme = linear system | `TwoPhase.scheme_iff_Ared` | `Matrices` |
| §6: `S_Γ` = matrix of `s` | `TwoPhase.SΓ`, `dotProduct_SΓ`, `SΓ_posDef` | `Schur` |

## Modelling choices

* All Cartesian directions share the face type `F`; `B K σ` may depend on the face (more
  general than `|S^α_K|`). `divK_eq_sections` and `divΓK_eq_sections` assume `B` equal on
  the two faces of a direction, as in the article.
* The traces `Φ_Γ` live on `I` and are extended by zero to the other cells (`Phase.Γext`),
  the convention `Φ_{Γ,K} := 0` of §4.3.
* `X_λ` is parametrized by the coefficients `x = (x^-, x^+, η)` (`TwoPhase.stateOf`); the
  basis is that of §6. Existence of the solution and of `ℋη` is obtained from the
  invertibility of the positive definite matrices `A_red` and `A_bulk` (the bulk block of
  `A_red`).
* "Zero traces" `Ψ^±_Γ = 0` is written `Ψ.m.Γ = 0`; `Ψ.p.Γ = 0` then follows from `Ψ ∈ X_λ`.
* Propositions 5 and 6 assume Assumption 2 in both phases and `𝓜^Γ ≠ ∅` (`Nonempty I`).
