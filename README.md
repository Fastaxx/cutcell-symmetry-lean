# lean-verif

Lean 4 / Mathlib formalization of the proofs of the article
*A two-fluid cut-cell discretization as a non-overlapping domain decomposition*
(`../main.tex`).

Toolchain: `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0` (see `lakefile.toml`).

```sh
lake exe cache get   # fetch the prebuilt Mathlib oleans (once)
lake build           # builds all modules; no `sorry`, no axioms beyond Mathlib's
```

## The model (`LeanVerif/Phase.lean`)

One phase is a structure `CutCell.Phase C F I`:

| article | Lean |
|---|---|
| active cells `𝓘_ω^±` | type `C` |
| active faces `⋃_α 𝓕^{α±}` (all directions gathered) | type `F` |
| mixed cells `𝓘_γ` | type `I`, injected in `C` by `ι` |
| `f = f^{α+}(K)` / `f = f^{α−}(K)` | `inc K f = 1` / `inc K f = -1` (else `0`) |
| moments `V_K, A_f, B_K^α, W_f`, coefficient `K_f` | fields `V A B W Kf` (with `B K f`, `α` = direction of `f`) |
| uncut cell has `B_K = A_f` | field `uncut_B` |
| `(Φ^ω, Φ^γ)` | `Phase.Field C I` |

Neumann exterior faces are simply absent from `F`; a homogeneous Dirichlet face has a
single adjacent cell.  In both cases the boundary residual `𝓡_{∂Ω}` of the article
vanishes, so the Green identity below carries no boundary term.

## Correspondence of statements

| article | Lean declaration |
|---|---|
| (dd-div-bulk), (dd-div-gamma), (dd-div-full) | `Phase.divBulk`, `Phase.divIface`, `Phase.divFull`, `Phase.divFull_eq_add`, `Phase.divFull_two_faces`, `Phase.divIface_two_faces` |
| (dd-grad-bulk), (dd-grad-gamma), (dd-gradient-split) | `Phase.gradBulk`, `Phase.gradIface`, `Phase.grad`, `Phase.grad_eq_add` |
| (green-amplified) face-amplified trace | `Phase.amp` |
| (green-gradient-telescopic) | `Phase.grad_two_cells`, `Phase.grad_two_cells_expanded` |
| gradient preserves constants | `Phase.grad_const` |
| **(green-sbp) discrete Green identity** | `Phase.green` |
| (kw-norm), (per-phase-bilinear-form), (bilinear-symmetry) | `Phase.energy`, `Phase.energyForm`, `Phase.energyForm_comm` |
| (dd-L-blocks) | `Phase.Lww`, `Phase.Lwg`, `Phase.Lgw`, `Phase.Lgg`, `Phase.bulkBalance_eq`, `Phase.ifaceBalance_eq` |
| (master-symmetry-relation) | `Phase.pairing_eq_energyForm` |
| **Prop. per-phase symmetry**: (Lww-Lgg-symmetry), (block-adjointness), (per-phase-energy) | `Phase.𝓛_isSymm`, `Phase.Lww_isSymm`, `Phase.Lgg_isSymm`, `Phase.neg_Lgw_eq_Lwg_transpose`, `Phase.per_phase_energy`, `Phase.𝓛_posSemidef` |
| Remark sign of interface block, (H-phase-block) | `Phase.neg_Lgg_posSemidef`, `Phase.H_eq_𝓛` |
| Assumption kernel | `Phase.Connected`, `Phase.kernel_iff` |
| **Lemma phase kernel** | `Phase.phase_kernel`, `Phase.𝓛_pos_of_not_const` |
| Boundary anchoring (`H ≻ 0`, `L^{ωω} ≻ 0`) | `Phase.𝓛_posDef`, `Phase.Lww_posDef` |
| (two-phase-reduced-operator), (schur-compact-system) | `TwoPhase.Ared`, `TwoPhase.Aω`, `TwoPhase.Bcol`, `TwoPhase.DΓ` |
| **Prop. two-phase SPD**: (two-phase-reduced-energy), (two-phase-kernel), `A_red ≻ 0` | `TwoPhase.Ared_quadratic`, `TwoPhase.Ared_isSymm`, `TwoPhase.Ared_posSemidef`, `TwoPhase.Ared_kernel`, `TwoPhase.Ared_posDef_of_anchored`, `TwoPhase.Ared_posDef` |
| variational interpretation of the flux balance | `TwoPhase.hasDerivAt_energyFunctional`, `TwoPhase.stationary_iff_flux_equilibrium` |
| (continuity-energy) | `TwoPhase.continuity_energy` |
| effect of mass terms | `TwoPhase.AredΔt_isSymm`, `TwoPhase.AredΔt_quadratic`, `TwoPhase.AredΔt_posDef` |
| (interface-schur-def), (interface-schur-cutcell), (schur-phase-sum) | `TwoPhase.SΓ`, `TwoPhase.SΓm`, `TwoPhase.SΓp`, `TwoPhase.SΓ_eq_phase_sum` |
| **Prop. SPD interface Schur complement** | `TwoPhase.SΓ_posDef` (via `J_eq`, `J_vStar`, `J_ge`) |
| Remark pure Neumann case | `TwoPhase.SΓ_posSemidef` |
| (schur-minimal-energy) | `TwoPhase.schur_minimal_energy` |
| matrix-free application | `TwoPhase.SΓ_mulVec` |
| **Cor. discrete energy estimate** (dd-energy-rate) | `TwoPhase.hasDerivAt_totalEnergy`, `TwoPhase.energy_rate_nonpos` |

## Modelling choices worth knowing

* Faces of all Cartesian directions live in the single type `F`; the article's sum over
  `α` is therefore a single sum over `F`.  `B` is allowed to depend on the face, which is
  slightly more general than `B_K^α` depending only on the direction.
* The one-sided traces live on `I` (the mixed cells) and are extended by zero to the
  other cells (`Phase.γext`); the interfacial coefficient `A_f − B_K` vanishes on uncut
  cells (`uncut_B`), so this extension is invisible, as in the article.
* The Green identity is proved exactly as in the article: swap the two sums, and
  identify the coefficient of `Q_f` with `−W_f G_f` (the telescopic identity).
* The four `L` blocks are defined by their entries (the Jacobian
  `−∂_Q(V div) K ∂_Φ grad`); `bulkBalance_eq` / `ifaceBalance_eq` check that they
  represent the balances.  Symmetry and adjointness are *not* proved from the entries but,
  as in the article, from the master relation obtained through the Green identity.
* "Assumption kernel" is `Phase.Connected` (zero gradient ⇒ constant).  Its converse
  (constants have zero gradient) is a theorem when all active faces are interior
  (`Phase.AllInterior`, pure Neumann); with Dirichlet faces it fails, which is precisely
  what anchoring means.
* Dirichlet anchoring is `Phase.Anchored` (zero gradient ⇒ zero).  For the two-phase
  operator, two anchored versions are given: the `−` phase anchored, or simply "the global
  constant mode is not a null state".
* The kernel and positivity statements require `Nonempty I` (a nonempty interface), which
  the article assumes implicitly.
* The Schur complement proposition uses Mathlib's `Matrix.schur_complement_eq₁₁` for the
  completion of the square; the positivity argument is the minimization argument of the
  article.
