/-
# The interface Schur complement

Formalization of Section 5 of the article: bulk elimination, the interface
Schur complement `S_Γ = D_Γ − Bᵀ A_ω⁻¹ B`, its phase-wise decomposition
`S_Γ = S_Γ^− + λ S_Γ^+`, Proposition `prop:schur-spd`, the energy
interpretation (eq. schur-minimal-energy) and the matrix-free application.
-/
import LeanVerif.TwoPhase

open Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

variable {Cm Fm Cp Fp I : Type*} [Fintype Cm] [Fintype Fm] [Fintype Cp] [Fintype Fp] [Fintype I]
  [DecidableEq Cm] [DecidableEq Fm] [DecidableEq Cp] [DecidableEq Fp] [DecidableEq I]

namespace TwoPhase

variable (T : TwoPhase Cm Fm Cp Fp I)

/-- The interface Schur complement `S_Γ := D_Γ − Bᵀ A_ω⁻¹ B` (eq. interface-schur-def). -/
def SΓ : Matrix I I ℝ := T.DΓ - T.Bcolᵀ * T.Aω⁻¹ * T.Bcol

/-- The `−`-phase Schur complement `S_Γ^− = −L^{γγ,−} − (L^{ωγ,−})ᵀ (L^{ωω,−})⁻¹ L^{ωγ,−}`
(eq. minus-phase-schur). -/
def SΓm : Matrix I I ℝ := -T.neg.Lgg - T.neg.Lwgᵀ * T.neg.Lww⁻¹ * T.neg.Lwg

/-- The `+`-phase Schur complement (eq. plus-phase-schur). -/
def SΓp : Matrix I I ℝ := -T.pos.Lgg - T.pos.Lwgᵀ * T.pos.Lww⁻¹ * T.pos.Lwg

/-- `A_ω⁻¹ = diag((A_ω^−)⁻¹, λ (A_ω^+)⁻¹)` when the bulk blocks are invertible. -/
lemma Aω_inv (hm : IsUnit T.neg.Lww.det) (hp : IsUnit T.pos.Lww.det) :
    T.Aω⁻¹ = fromBlocks T.neg.Lww⁻¹ 0 0 (T.lam • T.pos.Lww⁻¹) := by
  apply Matrix.inv_eq_left_inv
  unfold Aω
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.smul_mul,
    Matrix.mul_smul, nonsing_inv_mul _ hm, nonsing_inv_mul _ hp, smul_smul]
  rw [smul_zero, show 1 / T.lam * T.lam = 1 by field_simp [T.lam_pos.ne'], one_smul,
    fromBlocks_one]

/-- Eq. (interface-schur-cutcell) and (schur-phase-sum): `S_Γ = S_Γ^− + λ S_Γ^+`. -/
theorem SΓ_eq_phase_sum (hm : IsUnit T.neg.Lww.det) (hp : IsUnit T.pos.Lww.det) :
    T.SΓ = T.SΓm + T.lam • T.SΓp := by
  unfold SΓ SΓm SΓp DΓ Bcol
  rw [T.Aω_inv hm hp, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul]
  rw [smul_sub, smul_neg]
  abel

/-- The `+`-phase bulk block is invertible under Assumption `ass:kernel` (boundary
anchoring by the embedded interface, Section 4.4). -/
lemma Lww_isUnit_det (P : Phase Cm Fm I) (hc : P.Connected) [Nonempty I] :
    IsUnit P.Lww.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (P.Lww_posDef hc).isUnit

/-- `A_ω` is symmetric positive definite when both bulk blocks are (Section 5.2). -/
theorem Aω_posDef (hm : T.neg.Lww.PosDef) (hp : T.pos.Lww.PosDef) : T.Aω.PosDef := by
  have hl := T.lam_pos
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · refine Matrix.IsSymm.isHermitian_real ?_
    unfold Aω; rw [isSymm_fromBlocks_iff]
    refine ⟨T.neg.Lww_isSymm, by simp, by simp, ?_⟩
    have := T.pos.Lww_isSymm
    simp only [IsSymm, transpose_smul] at this ⊢; rw [this]
  · rw [star_trivial]
    unfold Aω
    rw [← Sum.elim_comp_inl_inr x, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add,
      smul_mulVec]
    rw [sum_elim_dotProduct, dotProduct_smul, smul_eq_mul]
    have h1 := hm.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
    have h2 := hp.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    rw [star_trivial] at h1 h2
    by_cases hx1 : x ∘ Sum.inl = 0
    · have hx2 : x ∘ Sum.inr ≠ 0 := by
        intro hx2; apply hx; ext (i | i)
        · exact congr_fun hx1 i
        · exact congr_fun hx2 i
      have := hp.dotProduct_mulVec_pos hx2
      rw [star_trivial] at this
      have : 0 < 1 / T.lam * (x ∘ Sum.inr ⬝ᵥ T.pos.Lww *ᵥ (x ∘ Sum.inr)) := by positivity
      linarith
    · have := hm.dotProduct_mulVec_pos hx1
      rw [star_trivial] at this
      have : 0 ≤ 1 / T.lam * (x ∘ Sum.inr ⬝ᵥ T.pos.Lww *ᵥ (x ∘ Sum.inr)) := by positivity
      linarith

/-- The block vector `(v, η)`. -/
def blockVec (v : Cm ⊕ Cp → ℝ) (η : I → ℝ) : (Cm ⊕ Cp) ⊕ I → ℝ := Sum.elim v η

/-- The quadratic functional `J_η(v) = [v;η]ᵀ A_red [v;η]` of the proof of
Proposition `prop:schur-spd`. -/
def J (η : I → ℝ) (v : Cm ⊕ Cp → ℝ) : ℝ := blockVec v η ⬝ᵥ (T.Ared *ᵥ blockVec v η)

/-- The minimizing bulk field `v_* = −A_ω⁻¹ B η` (discrete harmonic extension). -/
def vStar (η : I → ℝ) : Cm ⊕ Cp → ℝ := -((T.Aω⁻¹ * T.Bcol) *ᵥ η)

/-- Completion of the square (Mathlib's `schur_complement_eq₁₁`):
`J_η(v) = (v + A_ω⁻¹Bη)ᵀ A_ω (v + A_ω⁻¹Bη) + ηᵀ S_Γ η`. -/
theorem J_eq (hAω : T.Aω.PosDef) (η : I → ℝ) (v : Cm ⊕ Cp → ℝ) :
    T.J η v = (v + (T.Aω⁻¹ * T.Bcol) *ᵥ η) ⬝ᵥ (T.Aω *ᵥ (v + (T.Aω⁻¹ * T.Bcol) *ᵥ η))
      + η ⬝ᵥ (T.SΓ *ᵥ η) := by
  have : Invertible T.Aω := hAω.isUnit.invertible
  have hH : T.Aω.IsHermitian := hAω.isHermitian
  have key := Matrix.schur_complement_eq₁₁ T.Bcol T.DΓ v η hH
  rw [conjTranspose_eq_transpose_of_trivial] at key
  simp only [star_trivial] at key
  unfold J blockVec SΓ Ared
  rw [dotProduct_mulVec, key, ← dotProduct_mulVec, ← dotProduct_mulVec]

/-- The minimum of `J_η` over the bulk unknowns is attained at `v_*` and equals `ηᵀ S_Γ η`
(eq. schur-minimal-energy). -/
theorem J_vStar (hAω : T.Aω.PosDef) (η : I → ℝ) : T.J η (T.vStar η) = η ⬝ᵥ (T.SΓ *ᵥ η) := by
  rw [T.J_eq hAω]; unfold vStar; simp

theorem J_ge (hAω : T.Aω.PosDef) (η : I → ℝ) (v : Cm ⊕ Cp → ℝ) :
    η ⬝ᵥ (T.SΓ *ᵥ η) ≤ T.J η v := by
  rw [T.J_eq hAω]
  have := hAω.posSemidef.dotProduct_mulVec_nonneg (v + (T.Aω⁻¹ * T.Bcol) *ᵥ η)
  rw [star_trivial] at this
  linarith

/-- `S_Γ` is symmetric. -/
theorem SΓ_isSymm (hAω : T.Aω.PosDef) : T.SΓ.IsSymm := by
  unfold SΓ
  have hD : T.DΓ.IsSymm := (isSymm_fromBlocks_iff.mp T.Ared_isSymm).2.2.2
  have hA : T.Aω⁻¹.IsSymm := by
    have := hAω.isHermitian
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    simp only [IsSymm, transpose_nonsing_inv]; rw [this]
  simp only [IsSymm, transpose_sub, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [hD, hA]

/-- **Proposition `prop:schur-spd`**: if `A_red ≻ 0` and `A_ω ≻ 0`, then `S_Γ ≻ 0`.
The proof is the minimization argument of the article: `ηᵀ S_Γ η = min_v J_η(v) = J_η(v_*) > 0`. -/
theorem SΓ_posDef (hAred : T.Ared.PosDef) (hAω : T.Aω.PosDef) : T.SΓ.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨(T.SΓ_isSymm hAω).isHermitian_real, fun η hη => ?_⟩
  rw [star_trivial, ← T.J_vStar hAω]
  unfold J
  have hne : blockVec (T.vStar η) η ≠ 0 := by
    intro h; apply hη; ext i; exact congr_fun h (Sum.inr i)
  have := hAred.dotProduct_mulVec_pos hne
  rwa [star_trivial] at this

/-- Remark `rem:schur-neumann`: with pure Neumann data, `S_Γ` is positive semidefinite. -/
theorem SΓ_posSemidef (hAω : T.Aω.PosDef) : T.SΓ.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (T.SΓ_isSymm hAω).isHermitian_real fun η => ?_
  rw [star_trivial, ← T.J_vStar hAω]
  have := T.Ared_posSemidef.dotProduct_mulVec_nonneg (blockVec (T.vStar η) η)
  rwa [star_trivial] at this

/-- Energy interpretation (eq. schur-energy, schur-minimal-energy):
`½ ηᵀ S_Γ η = min_{v} 𝓔(v^−, v^+, η)`. -/
theorem schur_minimal_energy (hAω : T.Aω.PosDef) (η : I → ℝ) :
    (∀ v : Cm ⊕ Cp → ℝ,
      (1 / 2) * (η ⬝ᵥ (T.SΓ *ᵥ η)) ≤ T.energyFunctional (Red.ofVec (blockVec v η)))
    ∧ (1 / 2) * (η ⬝ᵥ (T.SΓ *ᵥ η)) = T.energyFunctional (Red.ofVec (blockVec (T.vStar η) η)) := by
  constructor
  · intro v
    rw [T.energyFunctional_eq, Red.vec_ofVec]
    have := T.J_ge hAω η v
    unfold J at this; linarith
  · rw [T.energyFunctional_eq, Red.vec_ofVec, ← T.J_vStar hAω]; rfl

/-- Matrix-free application (Section 5.6): `S_Γ η = D_Γ η − (B^−)ᵀ z^− − λ (B^+)ᵀ z^+`, where
`z^±` solve the two independent local problems `A_ω^± z^± = B^± η`. -/
theorem SΓ_mulVec (hm : IsUnit T.neg.Lww.det) (hp : IsUnit T.pos.Lww.det) (η : I → ℝ)
    (zm : Cm → ℝ) (zp : Cp → ℝ) (hzm : T.neg.Lww *ᵥ zm = T.neg.Lwg *ᵥ η)
    (hzp : T.pos.Lww *ᵥ zp = T.pos.Lwg *ᵥ η) :
    T.SΓ *ᵥ η = T.DΓ *ᵥ η - T.neg.Lwgᵀ *ᵥ zm - T.lam • (T.pos.Lwgᵀ *ᵥ zp) := by
  have ezm : zm = T.neg.Lww⁻¹ *ᵥ (T.neg.Lwg *ᵥ η) := by
    rw [← hzm, mulVec_mulVec, nonsing_inv_mul _ hm, one_mulVec]
  have ezp : zp = T.pos.Lww⁻¹ *ᵥ (T.pos.Lwg *ᵥ η) := by
    rw [← hzp, mulVec_mulVec, nonsing_inv_mul _ hp, one_mulVec]
  rw [T.SΓ_eq_phase_sum hm hp, ezm, ezp]
  unfold SΓm SΓp DΓ
  simp only [add_mulVec, smul_mulVec, sub_mulVec, neg_mulVec, mulVec_mulVec,
    smul_sub, smul_neg, Matrix.mul_assoc]
  abel

end TwoPhase

end CutCell

end
