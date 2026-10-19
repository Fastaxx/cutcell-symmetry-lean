# lean-verif

Lean 4 / Mathlib formalization of the proofs of the CRAS note
*An Analysis of Symmetry and Positive Definiteness in a Recent Two-Fluid Cut-Cell Method*
(`../main.tex`). Equation and statement numbers below are those of the compiled note.

Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (see `lakefile.toml`).

```sh
lake exe cache get        # prebuilt Mathlib (once)
lake build                # no `sorry`, no warning
lake env lean Axioms.lean # every main statement uses only propext, Classical.choice, Quot.sound
```

## The model

A piecewise constant function is identified with its coefficients, and the `L²` products
are the weighted sums (19). One phase is a structure `CutCell.Phase C F I`:

| note | Lean |
|---|---|
| active cells `𝓜^±`, active faces `𝓔^±`, interface cells `𝓜^Γ` | types `C`, `F`, `I` (`ι : I ↪ C`) |
| `n_{K,σ}·e_α` (`0` if `σ ∉ 𝓔(K)`) | `ne K σ` |
| `V_K, A_σ, B_K^α, W_σ, |Γ_K|` | `V, A, B, W, G` |
| `𝓔_D` | `Dir` |
| `Φ^ω ∈ X_𝓜`, `Φ^γ ∈ X_Γ`, `Q ∈ H_𝓔` | `C → ℝ`, `I → ℝ`, `F → ℝ` |
| `(Φ^ω, Φ^γ)`, two-phase state `(Φ^-, Φ^+)` | `Phase.Field`, `Pair` |
| `X_λ` | `TwoPhase.InX` |
| `Π^±_𝓜 r^±` | the source arguments `rm`, `rp` (cell means) |

The moment formulas (21)–(23) and (26)–(28) are the definitions. Their derivation from the
divergence theorem and Lemma 1 are geometric and are not formalized: Lemma 1 enters as the
hypotheses of `Phase` (`uncut` is Lemma 1(c); `interior`, `dirichlet` say that a face with
`A_σ ≠ 0` has one neighbour on each side unless it is a Dirichlet face, which has one;
positivity of `V, W, |Γ_K|` is Lemma 1(e) and the definition of the active sets).

## Correspondence

| note | Lean declaration | file |
|---|---|---|
| (19) `L²` products | `Phase.innerM`, `Phase.innerΓ`, `Phase.innerE` | `Operators` |
| (21)–(24) divergences, `div_𝓜`, `div_Γ` | `Phase.divω`, `divΓK`, `divK`, `divK_eq_add`, `divM`, `divΓ` | `Operators` |
| (26)–(29) gradient | `Phase.gradω`, `gradΓ`, `grad` | `Operators` |
| **Theorem 2**, (30) | `Phase.green_ω`, `Phase.green_Γ` | `Operators` |
| **Theorem 2**, (31) | `Phase.green` | `Operators` |
| (32) jumps | `Phase.jumps_grad`, `Phase.jumps_div` | `Operators` |
| (33) scheme | `TwoPhase.Scheme` | `Scheme` |
| (34) `X_λ`, `a` | `TwoPhase.InX`, `TwoPhase.a` | `Scheme` |
| (36) residual identity | `TwoPhase.residuals` | `Scheme` |
| **Proposition 3** (weak form) | `TwoPhase.weak_form` | `Scheme` |
| **Lemma 4** (constants) | `Phase.grad_const_interior`, `Phase.grad_const_dirichlet` | `Operators` |
| Assumption 2, anchored phase | `Phase.Connected`, `Phase.Anchored` | `Operators` |
| **Proposition 5**, (37) | `TwoPhase.a_comm`, `a_self_nonneg`, `a_definite`, `a_kernel` | `Symmetry` |
| unique solution (end of §5.3) | `TwoPhase.scheme_unique`, `TwoPhase.scheme_existsUnique` | `Symmetry`, `Matrices` |
| (38) harmonic extension, existence and uniqueness | `TwoPhase.H`, `H_harmonic`, `H_existsUnique` | `Schur` |
| harmonic ⟺ `div_𝓜 Q^±_η = 0` | `TwoPhase.harmonic_iff_div` | `Schur` |
| **Proposition 6**, (39) | `TwoPhase.s_comm`, `s_min`, `s_DtN`, `s_definite`, `s_kernel` | `Schur` |
| **Proposition 6**, (40) reduction | `TwoPhase.scheme_iff_interface` | `Schur` |
| (41) semi-discrete weak form | `TwoPhase.weak_unsteady` | `Unsteady` |
| **Corollary 7** (energy) | `TwoPhase.energy_rate` | `Unsteady` |
| `θ`-scheme remark (§5.5) | `TwoPhase.theta_energy` | `Unsteady` |
| §6: `A_red` = matrix of `a` | `TwoPhase.Ared`, `dotProduct_Ared`, `Ared_isSymm`, `Ared_posDef`, `Ared_kernel` | `Matrices` |
| §6: scheme = linear system | `TwoPhase.scheme_iff_Ared` | `Matrices` |
| §6: `S_Γ` = matrix of `s` | `TwoPhase.SΓ`, `dotProduct_SΓ`, `SΓ_posDef` | `Schur` |

## Modelling choices

* All Cartesian directions share the face type `F`; `B K σ` may depend on the face (more
  general than `B_K^α`). The second identity of (32) assumes `B` equal on the two faces of a
  direction, as in the note.
* The traces `Φ^γ` live on `I` and are extended by zero to the other cells (`Phase.γext`),
  the convention `Φ^γ_K := 0` of §4.3.
* `X_λ` is parametrized by the coefficients `x = (x^-, x^+, η)` (`TwoPhase.stateOf`); the
  basis is that of §6. Existence of the solution and of `ℋη` is obtained from the
  invertibility of the positive definite matrices `A_red` and `A_ω`.
* Propositions 5 and 6 assume Assumption 2 in both phases and `𝓜^Γ ≠ ∅` (`Nonempty I`).
