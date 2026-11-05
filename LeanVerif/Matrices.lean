/-
# Matrices (Section 6 of the article) and existence of the solution

In the basis of `X_λ` made of the `𝟙_{K^-}`, the `𝟙_{K^+}` and the pairs
`(𝟙_{Γ_K}, λ𝟙_{Γ_K})`, a state of `X_λ` is a coefficient vector `x` indexed by
`J = (𝓜^- ⊕ 𝓜^+) ⊕ 𝓜^Γ` (`stateOf x`).  The matrix of `a` in this basis is `A_red`;
it is symmetric, positive definite if one phase is anchored, and its kernel is spanned
by the coefficients of `(1, λ)` otherwise.  As a consequence the scheme has a unique
solution if one phase is anchored (after Proposition 5).
-/
import LeanVerif.Symmetry

open Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

namespace TwoPhase

open Phase

variable {Cm Fm Cp Fp I : Type*} [Fintype Cm] [Fintype Fm] [Fintype Cp] [Fintype Fp] [Fintype I]
  [DecidableEq Cm] [DecidableEq Fm] [DecidableEq Cp] [DecidableEq Fp] [DecidableEq I]
variable (T : TwoPhase Cm Fm Cp Fp I)

/-- Over `ℝ` a symmetric matrix is Hermitian. -/
lemma _root_.Matrix.IsSymm.isHermitian_real {n : Type*} {M : Matrix n n ℝ} (h : M.IsSymm) :
    M.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact h

/-- A linear form is the dot product with its values on the canonical basis. -/
lemma linear_eq_dotProduct {J : Type*} [Fintype J] [DecidableEq J] (f : (J → ℝ) →ₗ[ℝ] ℝ)
    (y : J → ℝ) : f y = y ⬝ᵥ fun j => f (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Pi.single j (y j) = y j • (Pi.single j 1 : J → ℝ) by
    ext k; by_cases h : k = j <;> simp [h], map_smul, smul_eq_mul]

/-- The state of `X_λ` with coefficients `x = (x^-, x^+, η)`. -/
def stateOf (x : (Cm ⊕ Cp) ⊕ I → ℝ) : Pair Cm Cp I :=
  ⟨⟨x ∘ Sum.inl ∘ Sum.inl, x ∘ Sum.inr⟩, ⟨x ∘ Sum.inl ∘ Sum.inr, T.lam • (x ∘ Sum.inr)⟩⟩

/-- The coefficients of a pair (its trace `Ψ^-_Γ` gives the last block). -/
def coeffs (Ψ : Pair Cm Cp I) : (Cm ⊕ Cp) ⊕ I → ℝ := Sum.elim (Sum.elim Ψ.m.M Ψ.p.M) Ψ.m.Γ

lemma InX_stateOf (x : (Cm ⊕ Cp) ⊕ I → ℝ) : T.InX (T.stateOf x) := rfl

lemma stateOf_coeffs (Ψ : Pair Cm Cp I) (hΨ : T.InX Ψ) : T.stateOf (coeffs Ψ) = Ψ := by
  unfold stateOf coeffs
  ext1
  · rfl
  · ext1
    · rfl
    · exact hΨ.symm

lemma stateOf_add (x y : (Cm ⊕ Cp) ⊕ I → ℝ) :
    T.stateOf (x + y) = T.stateOf x + T.stateOf y := by
  unfold stateOf; ext <;> simp
  ring

lemma stateOf_smul (c : ℝ) (x : (Cm ⊕ Cp) ⊕ I → ℝ) :
    T.stateOf (c • x) = c • T.stateOf x := by
  unfold stateOf; ext <;> simp
  ring

lemma stateOf_eq_zero_iff (x : (Cm ⊕ Cp) ⊕ I → ℝ) : T.stateOf x = 0 ↔ x = 0 := by
  constructor
  · intro h
    ext ((K | K) | i)
    · exact congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.m.M) h) K
    · exact congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.p.M) h) K
    · exact congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.m.Γ) h) i
  · rintro rfl; unfold stateOf; ext <;> simp

/-- `x ↦ ∇_𝒟 Φ^-` for `Φ = stateOf x`, as a linear map. -/
def gradLinM : ((Cm ⊕ Cp) ⊕ I → ℝ) →ₗ[ℝ] (Fm → ℝ) where
  toFun x := T.neg.grad (T.stateOf x).m
  map_add' x y := by funext σ; rw [T.stateOf_add]; exact T.neg.grad_add _ _ σ
  map_smul' c x := by funext σ; rw [T.stateOf_smul]; exact T.neg.grad_smul c _ σ

/-- `x ↦ ∇_𝒟 Φ^+` for `Φ = stateOf x`, as a linear map. -/
def gradLinP : ((Cm ⊕ Cp) ⊕ I → ℝ) →ₗ[ℝ] (Fp → ℝ) where
  toFun x := T.pos.grad (T.stateOf x).p
  map_add' x y := by funext σ; rw [T.stateOf_add]; exact T.pos.grad_add _ _ σ
  map_smul' c x := by funext σ; rw [T.stateOf_smul]; exact T.pos.grad_smul c _ σ

/-- The gradient matrices. -/
def Gm : Matrix Fm ((Cm ⊕ Cp) ⊕ I) ℝ := LinearMap.toMatrix' T.gradLinM
def Gp : Matrix Fp ((Cm ⊕ Cp) ⊕ I) ℝ := LinearMap.toMatrix' T.gradLinP

/-- `A_red`, the matrix of `a`: `k^- G^-ᵀ diag(W^-) G^- + (k^+/λ) G^+ᵀ diag(W^+) G^+`. -/
def Ared : Matrix ((Cm ⊕ Cp) ⊕ I) ((Cm ⊕ Cp) ⊕ I) ℝ :=
  T.km • (T.Gmᵀ * diagonal T.neg.W * T.Gm) + (T.kp / T.lam) • (T.Gpᵀ * diagonal T.pos.W * T.Gp)

lemma dotProduct_GtDG {F : Type*} [Fintype F] [DecidableEq F] (G : Matrix F ((Cm ⊕ Cp) ⊕ I) ℝ)
    (W : F → ℝ) (x y : (Cm ⊕ Cp) ⊕ I → ℝ) :
    y ⬝ᵥ ((Gᵀ * diagonal W * G) *ᵥ x) = ∑ σ, W σ * (G *ᵥ x) σ * (G *ᵥ y) σ := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `A_red` is the matrix of `a`: `yᵀ A_red x = a(Φ(x), Φ(y))`. -/
theorem dotProduct_Ared (x y : (Cm ⊕ Cp) ⊕ I → ℝ) :
    y ⬝ᵥ (T.Ared *ᵥ x) = T.a (T.stateOf x) (T.stateOf y) := by
  unfold Ared
  rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    dotProduct_smul, dotProduct_GtDG, dotProduct_GtDG]
  unfold Gm Gp
  simp only [LinearMap.toMatrix'_mulVec, gradLinM, gradLinP, LinearMap.coe_mk, AddHom.coe_mk,
    smul_eq_mul]
  unfold a Phase.innerE
  ring

theorem Ared_isSymm : T.Ared.IsSymm := by
  unfold Ared
  simp only [IsSymm, transpose_add, transpose_smul, transpose_mul, transpose_transpose,
    diagonal_transpose, Matrix.mul_assoc]

theorem Ared_posSemidef : T.Ared.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg T.Ared_isSymm.isHermitian_real fun x => ?_
  rw [star_trivial, T.dotProduct_Ared]
  exact T.a_self_nonneg _

/-- Section 6: `A_red` is symmetric positive definite if one phase is anchored. -/
theorem Ared_posDef (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hanch : T.neg.Anchored ∨ T.pos.Anchored) : T.Ared.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨T.Ared_isSymm.isHermitian_real, fun x hx => ?_⟩
  rw [star_trivial, T.dotProduct_Ared]
  refine lt_of_le_of_ne (T.a_self_nonneg _) fun h => hx ?_
  exact (T.stateOf_eq_zero_iff x).mp (T.a_definite hm hp hanch _ (T.InX_stateOf x) h.symm)

/-- Section 6: without anchoring, `A_red` annihilates exactly the coefficients of the
multiples of `(1, λ)`. -/
theorem Ared_kernel (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hnm : ¬ T.neg.Anchored) (hnp : ¬ T.pos.Anchored) (x : (Cm ⊕ Cp) ⊕ I → ℝ) :
    T.Ared *ᵥ x = 0 ↔ ∃ c, T.stateOf x = T.constMode c := by
  rw [← T.Ared_posSemidef.dotProduct_mulVec_zero_iff, star_trivial, T.dotProduct_Ared]
  exact T.a_kernel hm hp hnm hnp _ (T.InX_stateOf x)

/-- The right-hand side as a linear form of the coefficients. -/
def rhsLin (rm : Cm → ℝ) (rp : Cp → ℝ) : ((Cm ⊕ Cp) ⊕ I → ℝ) →ₗ[ℝ] ℝ where
  toFun y := T.rhs rm rp (T.stateOf y)
  map_add' x y := by rw [T.stateOf_add, T.rhs_add]
  map_smul' c x := by
    rw [T.stateOf_smul]
    unfold rhs
    simp only [Pair.smul_m, Pair.smul_p, smul_M, RingHom.id_apply, smul_eq_mul]
    rw [T.neg.innerM_comm, T.pos.innerM_comm, T.neg.innerM_smul_left, T.pos.innerM_smul_left,
      T.neg.innerM_comm, T.pos.innerM_comm]
    ring

/-- The right-hand side vector `b_j = ∑_± ℓ^± ∫ r^± (e_j)^±`. -/
def bvec (rm : Cm → ℝ) (rp : Cp → ℝ) : (Cm ⊕ Cp) ⊕ I → ℝ :=
  fun j => T.rhsLin rm rp (Pi.single j 1)

lemma dotProduct_bvec (rm : Cm → ℝ) (rp : Cp → ℝ) (y : (Cm ⊕ Cp) ⊕ I → ℝ) :
    y ⬝ᵥ T.bvec rm rp = T.rhs rm rp (T.stateOf y) :=
  (linear_eq_dotProduct (T.rhsLin rm rp) y).symm

/-- The scheme is the linear system `A_red x = b`. -/
theorem scheme_iff_Ared (rm : Cm → ℝ) (rp : Cp → ℝ) (x : (Cm ⊕ Cp) ⊕ I → ℝ) :
    T.Scheme rm rp (T.stateOf x) ↔ T.Ared *ᵥ x = T.bvec rm rp := by
  rw [T.weak_form]
  constructor
  · rintro ⟨-, h⟩
    ext j
    have := h _ (T.InX_stateOf (Pi.single j 1))
    rw [← T.dotProduct_Ared, ← T.dotProduct_bvec] at this
    simpa [single_dotProduct] using this
  · intro h
    refine ⟨T.InX_stateOf x, fun Ψ hΨ => ?_⟩
    rw [← T.stateOf_coeffs Ψ hΨ, ← T.dotProduct_Ared, ← T.dotProduct_bvec, h]

/-- After Proposition 5: if one phase is anchored, the scheme has a unique solution. -/
theorem scheme_existsUnique (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hanch : T.neg.Anchored ∨ T.pos.Anchored) (rm : Cm → ℝ) (rp : Cp → ℝ) :
    ∃! Φ : Pair Cm Cp I, T.Scheme rm rp Φ := by
  have hdet : IsUnit T.Ared.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (T.Ared_posDef hm hp hanch).isUnit
  refine ⟨T.stateOf (T.Ared⁻¹ *ᵥ T.bvec rm rp), ?_, fun Φ' h' => ?_⟩
  · exact (T.scheme_iff_Ared rm rp _).mpr (by
      rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec])
  · exact T.scheme_unique hm hp hanch rm rp _ _ h'
      ((T.scheme_iff_Ared rm rp _).mpr (by
        rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]))

end TwoPhase

end CutCell

end
