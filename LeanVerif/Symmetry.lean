/-
# Per-phase symmetry and positive semidefiniteness

Formalization of Sections 4.1–4.4 of the article: the per-phase bilinear form
`a^±`, the four blocks `L^{ωω}, L^{ωγ}, L^{γω}, L^{γγ}`, Proposition
`prop:per-phase-symmetry`, Remark `rem:interface-block-sign`, Lemma
`lem:phase-kernel` and the boundary-anchoring statements.
-/
import LeanVerif.Phase

open Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

variable {C F I : Type*} [Fintype C] [Fintype F] [Fintype I]
  [DecidableEq C] [DecidableEq F] [DecidableEq I]

/-- Over `ℝ` a symmetric matrix is Hermitian. -/
lemma _root_.Matrix.IsSymm.isHermitian_real {n : Type*} {M : Matrix n n ℝ} (h : M.IsSymm) :
    M.IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]; exact h

/-- The `(i,j)` entry of a matrix is the pairing of the basis vectors `e_i`, `e_j`. -/
lemma _root_.Matrix.single_dotProduct_mulVec_single {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (i j : n) :
    Pi.single i (1 : ℝ) ⬝ᵥ (M *ᵥ Pi.single j 1) = M i j := by
  simp [single_dotProduct, mulVec_single]

namespace Phase

variable (P : Phase C F I)

/-! ### Per-phase bilinear form (eq. kw-norm, per-phase-bilinear-form) -/

/-- The per-phase bilinear form `a(Φ,Ψ) = ∑_f W_f K_f G_f[Φ] G_f[Ψ]`. -/
def energyForm (Φ Ψ : Field C I) : ℝ := ∑ f, P.W f * P.Kf f * P.grad Φ f * P.grad Ψ f

/-- The weighted diffusive energy `‖G[Φ]‖²_{K,W} = a(Φ,Φ)`. -/
def energy (Φ : Field C I) : ℝ := P.energyForm Φ Φ

/-- Eq. (bilinear-symmetry): `a(Φ,Ψ) = a(Ψ,Φ)`. -/
lemma energyForm_comm (Φ Ψ : Field C I) : P.energyForm Φ Ψ = P.energyForm Ψ Φ := by
  unfold energyForm; exact Finset.sum_congr rfl fun f _ => by ring

lemma energy_nonneg (Φ : Field C I) : 0 ≤ P.energy Φ := by
  unfold energy energyForm
  refine Finset.sum_nonneg fun f _ => ?_
  have := P.W_pos f; have := P.Kf_pos f
  rw [mul_assoc, ← sq]; positivity

/-- The energy vanishes iff the full gradient vanishes on every active face
(because `K_f > 0`, `W_f > 0`). -/
lemma energy_eq_zero_iff (Φ : Field C I) : P.energy Φ = 0 ↔ ∀ f, P.grad Φ f = 0 := by
  unfold energy energyForm
  have hnn : ∀ f ∈ (Finset.univ : Finset F), 0 ≤ P.W f * P.Kf f * P.grad Φ f * P.grad Φ f := by
    intro f _; have := P.W_pos f; have := P.Kf_pos f
    rw [mul_assoc, ← sq]; positivity
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h f
    have hf := h f (Finset.mem_univ f)
    have hW := (P.W_pos f).ne'; have hK := (P.Kf_pos f).ne'
    rw [mul_assoc, ← sq, mul_eq_zero, mul_eq_zero] at hf
    rcases hf with (h | h) | h
    · exact absurd h hW
    · exact absurd h hK
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  · intro h f _; rw [h f]; ring

/-! ### Fluxes, balances and the four blocks (eq. dd-discrete-flux, dd-L-blocks) -/

/-- The discrete constitutive relation `Q = −K G[Φ]`. -/
def flux (Φ : Field C I) (f : F) : ℝ := -P.Kf f * P.grad Φ f

/-- The bulk balance of phase `±`: `(L^{ωω}Φ^ω + L^{ωγ}Φ^γ)_K = V_K div_K(B, Q[Φ])`. -/
def bulkBalance (Φ : Field C I) (K : C) : ℝ := P.divFull (P.flux Φ) K

/-- The interfacial flux balance `𝓕 = L^{γω}Φ^ω + L^{γγ}Φ^γ = V_K div^γ_K(A,B,Q[Φ])`
on the mixed cells. -/
def ifaceBalance (Φ : Field C I) (i : I) : ℝ := P.divIface (P.flux Φ) (P.ι i)

/-- The face weight `K_f / W_f`. -/
def κ (f : F) : ℝ := P.Kf f / P.W f

/-- Bulk coefficient `inc(K,f) B_K` of the shared moments. -/
def cw (K : C) (f : F) : ℝ := P.inc K f * P.B K f

/-- Interface coefficient `inc(K,f) (A_f − B_K)` of the shared moments. -/
def cg (K : C) (f : F) : ℝ := P.inc K f * (P.A f - P.B K f)

/-- The flux in terms of the shared coefficients. -/
lemma flux_eq (Φ : Field C I) (f : F) :
    P.flux Φ f = P.κ f * (∑ K, P.cw K f * Φ.ω K + ∑ i, P.cg (P.ι i) f * Φ.γ i) := by
  unfold flux κ
  have hW := (P.W_pos f).ne'
  have hS : ∑ K, P.inc K f * P.amp Φ K f
      = ∑ K, P.cw K f * Φ.ω K + ∑ i, P.cg (P.ι i) f * Φ.γ i := by
    have := P.sum_γext_mul Φ.γ (fun K => P.cg K f)
    simp_rw [mul_comm (Φ.γ _), mul_comm (P.γext _ _)] at this
    rw [← this, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun K _ => by unfold amp cw cg; ring
  rw [← hS]; unfold grad; field_simp

/-- The matrices of eq. (dd-L-blocks), obtained by eliminating `Q = −K G[Φ]`
(`∂_Q(V div) K ∂_Φ grad`). -/
def Lww : Matrix C C ℝ := Matrix.of fun K K' => ∑ f, P.κ f * P.cw K f * P.cw K' f
def Lwg : Matrix C I ℝ := Matrix.of fun K i => ∑ f, P.κ f * P.cw K f * P.cg (P.ι i) f
def Lgw : Matrix I C ℝ := Matrix.of fun i K => -∑ f, P.κ f * P.cg (P.ι i) f * P.cw K f
def Lgg : Matrix I I ℝ := Matrix.of fun i j => -∑ f, P.κ f * P.cg (P.ι i) f * P.cg (P.ι j) f

/-- `L^{ωω}Φ^ω + L^{ωγ}Φ^γ` is the bulk balance. -/
lemma bulkBalance_eq (Φ : Field C I) :
    P.bulkBalance Φ = P.Lww *ᵥ Φ.ω + P.Lwg *ᵥ Φ.γ := by
  ext K
  have key : ∀ f, P.inc K f * P.B K f * P.flux Φ f
      = ∑ K', (P.κ f * P.cw K f * P.cw K' f) * Φ.ω K'
        + ∑ j, (P.κ f * P.cw K f * P.cg (P.ι j) f) * Φ.γ j := by
    intro f; rw [P.flux_eq]; simp only [mul_add, Finset.mul_sum]
    refine congrArg₂ (fun a b : ℝ => a + b) (Finset.sum_congr rfl fun _ _ => ?_)
      (Finset.sum_congr rfl fun _ _ => ?_) <;> simp only [cg, cw] <;> ring
  simp only [bulkBalance, divFull, Pi.add_apply, mulVec, dotProduct, Lww, Lwg, of_apply]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_comm (β := ℝ), add_comm, Finset.sum_comm (β := ℝ), add_comm]
  simp only [Finset.sum_mul]

/-- `L^{γω}Φ^ω + L^{γγ}Φ^γ` is the interfacial flux balance. -/
lemma ifaceBalance_eq (Φ : Field C I) :
    P.ifaceBalance Φ = P.Lgw *ᵥ Φ.ω + P.Lgg *ᵥ Φ.γ := by
  ext i
  have key : ∀ f, P.inc (P.ι i) f * (P.B (P.ι i) f - P.A f) * P.flux Φ f
      = ∑ K, (-(P.κ f * P.cg (P.ι i) f * P.cw K f)) * Φ.ω K
        + ∑ j, (-(P.κ f * P.cg (P.ι i) f * P.cg (P.ι j) f)) * Φ.γ j := by
    intro f; rw [P.flux_eq]; simp only [mul_add, Finset.mul_sum]
    refine congrArg₂ (fun a b : ℝ => a + b) (Finset.sum_congr rfl fun _ _ => ?_)
      (Finset.sum_congr rfl fun _ _ => ?_) <;> simp only [cg, cw] <;> ring
  simp only [ifaceBalance, divIface, Pi.add_apply, mulVec, dotProduct, Lgw, Lgg, of_apply]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_comm (β := ℝ), add_comm, Finset.sum_comm (β := ℝ), add_comm]
  simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]

/-! ### Proposition `prop:per-phase-symmetry` -/

/-- The block operator `𝓛 = [L^{ωω}, L^{ωγ}; −L^{γω}, −L^{γγ}]` (eq. phase-symmetric-operator). -/
def 𝓛 : Matrix (C ⊕ I) (C ⊕ I) ℝ := fromBlocks P.Lww P.Lwg (-P.Lgw) (-P.Lgg)

/-- The symmetric per-phase block `H = [L^{ωω}, L^{ωγ}; (L^{ωγ})ᵀ, −L^{γγ}]` (eq. H-phase-block). -/
def H : Matrix (C ⊕ I) (C ⊕ I) ℝ := fromBlocks P.Lww P.Lwg P.Lwgᵀ (-P.Lgg)

/-- A field as a vector on `C ⊕ I`. -/
def vec (Φ : Field C I) : C ⊕ I → ℝ := Sum.elim Φ.ω Φ.γ

/-- A vector on `C ⊕ I` as a field. -/
def ofVec (x : C ⊕ I → ℝ) : Field C I := ⟨x ∘ Sum.inl, x ∘ Sum.inr⟩

@[simp] lemma vec_ofVec (x : C ⊕ I → ℝ) : vec (ofVec x : Field C I) = x := by
  ext (i | i) <;> rfl

@[simp] lemma vec_eq_zero_iff (Φ : Field C I) : vec Φ = 0 ↔ Φ = 0 := by
  constructor
  · intro h; ext K
    · exact congr_fun h (Sum.inl K)
    · exact congr_fun h (Sum.inr K)
  · rintro rfl; ext (i | i) <;> rfl

/-- **Master symmetry relation** (eq. master-symmetry-relation), obtained from the discrete
Green identity with `Q = Q[Ψ] = −K G[Ψ]`:
`Φᵀ 𝓛 Ψ = Φ^ω·(L^{ωω}Ψ^ω + L^{ωγ}Ψ^γ) − Φ^γ·(L^{γω}Ψ^ω + L^{γγ}Ψ^γ) = a(Ψ,Φ)`. -/
theorem pairing_eq_energyForm (Φ Ψ : Field C I) :
    Φ.ω ⬝ᵥ P.bulkBalance Ψ - Φ.γ ⬝ᵥ P.ifaceBalance Ψ = P.energyForm Ψ Φ := by
  have hg := P.green Φ (P.flux Ψ)
  unfold bulkBalance ifaceBalance
  simp only [dotProduct]
  rw [hg]
  unfold innerW energyForm flux
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun f _ => by ring

/-- The quadratic pairing of `𝓛`. -/
theorem vec_dotProduct_𝓛_mulVec (Φ Ψ : Field C I) :
    vec Φ ⬝ᵥ (P.𝓛 *ᵥ vec Ψ) = P.energyForm Ψ Φ := by
  rw [← P.pairing_eq_energyForm, P.bulkBalance_eq, P.ifaceBalance_eq]
  unfold 𝓛 vec
  rw [fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Sum.elim_comp_inl,
    Sum.elim_comp_inr, neg_mulVec, Pi.add_apply, Pi.neg_apply]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `𝓛` is symmetric. -/
theorem 𝓛_isSymm : P.𝓛.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [← Matrix.single_dotProduct_mulVec_single P.𝓛 j i,
    ← Matrix.single_dotProduct_mulVec_single P.𝓛 i j]
  have h1 := P.vec_dotProduct_𝓛_mulVec (ofVec (Pi.single j 1)) (ofVec (Pi.single i 1))
  have h2 := P.vec_dotProduct_𝓛_mulVec (ofVec (Pi.single i 1)) (ofVec (Pi.single j 1))
  simp only [vec_ofVec] at h1 h2
  rw [h1, h2, P.energyForm_comm]

/-- Eq. (Lww-Lgg-symmetry) and (block-adjointness):
`L^{ωω} = (L^{ωω})ᵀ`, `L^{γγ} = (L^{γγ})ᵀ`, `−L^{γω} = (L^{ωγ})ᵀ`. -/
theorem Lww_isSymm : P.Lww.IsSymm := (isSymm_fromBlocks_iff.mp P.𝓛_isSymm).1
theorem Lgg_isSymm : P.Lgg.IsSymm := by
  have h := (isSymm_fromBlocks_iff.mp P.𝓛_isSymm).2.2.2
  simpa [IsSymm, transpose_neg] using h
theorem neg_Lgw_eq_Lwg_transpose : -P.Lgw = P.Lwgᵀ :=
  ((isSymm_fromBlocks_iff.mp P.𝓛_isSymm).2.1).symm

/-- The symmetric block `H` coincides with `𝓛` (Remark `rem:interface-block-sign`). -/
theorem H_eq_𝓛 : P.H = P.𝓛 := by
  unfold H 𝓛; rw [P.neg_Lgw_eq_Lwg_transpose]

/-- Eq. (per-phase-energy):
`Φ^ω·L^{ωω}Φ^ω + 2 Φ^ω·L^{ωγ}Φ^γ − Φ^γ·L^{γγ}Φ^γ = ‖G[Φ]‖²_{K,W} ≥ 0`. -/
theorem per_phase_energy (Φ : Field C I) :
    Φ.ω ⬝ᵥ (P.Lww *ᵥ Φ.ω) + 2 * (Φ.ω ⬝ᵥ (P.Lwg *ᵥ Φ.γ)) - Φ.γ ⬝ᵥ (P.Lgg *ᵥ Φ.γ)
      = P.energy Φ := by
  have h := P.pairing_eq_energyForm Φ Φ
  rw [P.bulkBalance_eq, P.ifaceBalance_eq] at h
  have hgw : Φ.γ ⬝ᵥ (P.Lgw *ᵥ Φ.ω) = -(Φ.ω ⬝ᵥ (P.Lwg *ᵥ Φ.γ)) := by
    rw [show P.Lgw = -P.Lwgᵀ by rw [← P.neg_Lgw_eq_Lwg_transpose, neg_neg],
      neg_mulVec, dotProduct_neg, mulVec_transpose, dotProduct_mulVec, dotProduct_comm]
  rw [dotProduct_add, dotProduct_add, hgw] at h
  unfold energy; rw [← h]; ring

/-- The quadratic form of `𝓛` is the diffusive energy. -/
theorem vec_dotProduct_𝓛_mulVec_self (Φ : Field C I) :
    vec Φ ⬝ᵥ (P.𝓛 *ᵥ vec Φ) = P.energy Φ :=
  P.vec_dotProduct_𝓛_mulVec Φ Φ

/-- **Proposition `prop:per-phase-symmetry`**: `𝓛` is symmetric positive semidefinite. -/
theorem 𝓛_posSemidef : P.𝓛.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg P.𝓛_isSymm.isHermitian_real fun x => ?_
  rw [star_trivial, ← vec_ofVec x, P.vec_dotProduct_𝓛_mulVec_self]
  exact P.energy_nonneg _

/-- Remark `rem:interface-block-sign`: `−L^{γγ} ⪰ 0`, since
`−Φ^γ·L^{γγ}Φ^γ = ‖G[0,Φ^γ]‖²_{K,W}`. -/
theorem neg_Lgg_quadratic (Φγ : I → ℝ) :
    -(Φγ ⬝ᵥ (P.Lgg *ᵥ Φγ)) = P.energy ⟨0, Φγ⟩ := by
  have h := P.per_phase_energy ⟨0, Φγ⟩
  simpa using h

theorem neg_Lgg_posSemidef : (-P.Lgg).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsSymm.isHermitian_real ?_
    have := P.Lgg_isSymm; simpa [IsSymm, transpose_neg] using this
  · rw [star_trivial, neg_mulVec, dotProduct_neg, P.neg_Lgg_quadratic]
    exact P.energy_nonneg _

/-- The bulk block alone: `Φ^ω·L^{ωω}Φ^ω = ‖G[Φ^ω,0]‖²_{K,W}`. -/
theorem Lww_quadratic (Φω : C → ℝ) :
    Φω ⬝ᵥ (P.Lww *ᵥ Φω) = P.energy ⟨Φω, 0⟩ := by
  have h := P.per_phase_energy ⟨Φω, 0⟩
  simpa using h

/-! ### Kernel of the phase energy (Assumption `ass:kernel`, Lemma `lem:phase-kernel`) -/

/-- Assumption `ass:kernel` (discrete connectedness): the only states with zero full
discrete gradient are the constants. (The converse direction, that constants have zero
gradient, is a theorem: `grad_const`, valid when all active faces are interior.) -/
def Connected : Prop :=
  ∀ Φ : Field C I, (∀ f, P.grad Φ f = 0) → ∃ c, Φ = const c

/-- Assumption `ass:kernel` in its two-sided form, for pure-Neumann exterior data. -/
theorem kernel_iff (hc : P.Connected) (hint : P.AllInterior) (Φ : Field C I) :
    (∀ f, P.grad Φ f = 0) ↔ ∃ c, Φ = const c :=
  ⟨hc Φ, by rintro ⟨c, rfl⟩ f; exact P.grad_const hint c f⟩

/-- **Lemma `lem:phase-kernel`**: `a(Φ,Φ) = 0 ↔ Φ = c 𝟙`. -/
theorem phase_kernel (hc : P.Connected) (hint : P.AllInterior) (Φ : Field C I) :
    P.energy Φ = 0 ↔ ∃ c, Φ = const c := by
  rw [P.energy_eq_zero_iff]; exact P.kernel_iff hc hint Φ

/-- Consequence of Lemma `lem:phase-kernel`: on the complement of the constants,
`𝓛` is positive definite (`Φᵀ𝓛Φ > 0` unless `Φ` is constant). -/
theorem 𝓛_pos_of_not_const (hc : P.Connected) (Φ : Field C I) (hΦ : ∀ c, Φ ≠ const c) :
    0 < vec Φ ⬝ᵥ (P.𝓛 *ᵥ vec Φ) := by
  rw [P.vec_dotProduct_𝓛_mulVec_self]
  refine lt_of_le_of_ne (P.energy_nonneg Φ) fun h => ?_
  obtain ⟨c, hcΦ⟩ := hc Φ ((P.energy_eq_zero_iff Φ).mp h.symm)
  exact hΦ c hcΦ

/-! ### Boundary anchoring (Section 4.4) -/

/-- Dirichlet anchoring: the only state with zero gradient is `0`
(the constant mode has been removed by exterior Dirichlet data). -/
def Anchored : Prop := ∀ Φ : Field C I, (∀ f, P.grad Φ f = 0) → Φ = 0

/-- With Dirichlet exterior data, `H = 𝓛 ≻ 0`. -/
theorem 𝓛_posDef (ha : P.Anchored) : P.𝓛.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨P.𝓛_isSymm.isHermitian_real, fun x hx => ?_⟩
  rw [star_trivial, ← vec_ofVec x, P.vec_dotProduct_𝓛_mulVec_self]
  refine lt_of_le_of_ne (P.energy_nonneg _) fun h => hx ?_
  have h0 := ha _ ((P.energy_eq_zero_iff _).mp h.symm)
  rw [← vec_ofVec x, h0]; ext (i | i) <;> rfl

/-- Independently of the exterior data, the bulk block `L^{ωω}` is positive definite as
soon as `𝓘_γ ≠ ∅`: the embedded interface acts as a Dirichlet anchor for the bulk-only
problem. -/
theorem Lww_posDef (hc : P.Connected) [Nonempty I] : P.Lww.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨P.Lww_isSymm.isHermitian_real, fun x hx => ?_⟩
  rw [star_trivial, P.Lww_quadratic]
  refine lt_of_le_of_ne (P.energy_nonneg _) fun h => hx ?_
  obtain ⟨c, hc'⟩ := hc _ ((P.energy_eq_zero_iff _).mp h.symm)
  have hγ := congr_arg Field.γ hc'
  have hω := congr_arg Field.ω hc'
  simp only [const] at hγ hω
  have hc0 : c = 0 := by
    have := congr_fun hγ (Classical.arbitrary I); simpa using this.symm
  rw [hω]; ext K; simp [hc0]

end Phase

end CutCell

end
