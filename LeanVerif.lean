/-
Lean 4 / Mathlib formalization of the CRAS article
"Symmetry and Positive Definiteness of a Two-Fluid Finite-Volume Method Based on Geometric
Moments".

* `LeanVerif.Operators` : spaces, divergences, gradient, Theorem 2 (Green), Lemma 4 (§4, §5.2)
* `LeanVerif.Scheme`    : two-phase scheme, residual identity, Proposition 3 (§5.1)
* `LeanVerif.Symmetry`  : Proposition 5, uniqueness (§5.2)
* `LeanVerif.Matrices`  : `A_red` = matrix of `a`, existence and uniqueness (§5.2, §6)
* `LeanVerif.Schur`     : harmonic extension, Proposition 6, `S_Γ` (§5.3, §6)
* `LeanVerif.Unsteady`  : semi-discrete weak form, energy identity, θ-scheme (§5.4)
-/
import LeanVerif.Operators
import LeanVerif.Scheme
import LeanVerif.Symmetry
import LeanVerif.Matrices
import LeanVerif.Schur
import LeanVerif.Unsteady
