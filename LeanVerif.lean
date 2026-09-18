/-
Lean 4 / Mathlib formalization of the proofs of the article
"A two-fluid cut-cell discretization as a non-overlapping domain decomposition".

* `LeanVerif.Phase`    : cut-cell operators, telescopic identity, discrete Green identity (§2–3)
* `LeanVerif.Symmetry` : per-phase symmetry / PSD, kernel, boundary anchoring (§4.1–4.4)
* `LeanVerif.TwoPhase` : reduced two-phase operator `A_red`, kernel, variational form,
                         continuity case, mass terms (§4.5–4.8)
* `LeanVerif.Schur`    : interface Schur complement, SPD, energy interpretation (§5)
* `LeanVerif.Energy`   : discrete energy estimate (Corollary 5.1)
-/
import LeanVerif.Phase
import LeanVerif.Symmetry
import LeanVerif.TwoPhase
import LeanVerif.Schur
import LeanVerif.Energy
