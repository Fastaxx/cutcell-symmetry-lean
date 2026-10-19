/-
Lean 4 / Mathlib formalization of the CRAS note
"An Analysis of Symmetry and Positive Definiteness in a Recent Two-Fluid Cut-Cell Method".

* `LeanVerif.Operators` : spaces, divergences, gradient, Theorem 2 (Green), jumps, Lemma 4 (§4, §5.3)
* `LeanVerif.Scheme`    : two-phase scheme, residual identity, Proposition 3 (§5.1–5.2)
* `LeanVerif.Symmetry`  : Proposition 5, uniqueness (§5.3)
* `LeanVerif.Matrices`  : `A_red` = matrix of `a`, existence and uniqueness (§5.3, §6)
* `LeanVerif.Schur`     : harmonic extension, Proposition 6, `S_Γ` (§5.4, §6)
* `LeanVerif.Unsteady`  : semi-discrete weak form, Corollary 7, θ-scheme (§5.5)
-/
import LeanVerif.Operators
import LeanVerif.Scheme
import LeanVerif.Symmetry
import LeanVerif.Matrices
import LeanVerif.Schur
import LeanVerif.Unsteady
