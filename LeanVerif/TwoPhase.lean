/-
# The symmetric two-phase operator

Formalization of Sections 4.5–4.8 of the article: the reduced two-phase
operator `A_red` (Proposition `prop:two-phase-spd`), its energy, its kernel, the
variational interpretation of the flux balance, the continuity case and the
effect of mass terms.

The two phases share the interface index set `I = 𝓘_γ`.  The trace law
`Φ^{γ+} = λ Φ^{γ−}` (homogeneous part) is used to eliminate `Φ^{γ+}`, and the
reduced unknown is `u = (Φ^{ω−}, Φ^{ω+}, η)` with `η = Φ^{γ−}`.
-/
import LeanVerif.Symmetry

open Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

/-- Dot product of two block vectors. -/
lemma sum_elim_dotProduct {m n : Type*} [Fintype m] [Fintype n] (a c : m → ℝ) (b d : n → ℝ) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

section linearity

variable {C F I : Type*} [Fintype C] [Fintype F] [Fintype I]
  [DecidableEq C] [DecidableEq F] [DecidableEq I]

namespace Phase

variable (P : Phase C F I)

lemma γext_add (a b : I → ℝ) (K : C) : P.γext (a + b) K = P.γext a K + P.γext b K := by
  unfold γext; split_ifs <;> simp

lemma γext_smul (c : ℝ) (a : I → ℝ) (K : C) : P.γext (c • a) K = c * P.γext a K := by
  unfold γext; split_ifs <;> simp

lemma grad_add (Φ Ψ : Field C I) (f : F) : P.grad (Φ + Ψ) f = P.grad Φ f + P.grad Ψ f := by
  unfold grad amp
  rw [← add_div, ← neg_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [add_ω, add_γ, Pi.add_apply, P.γext_add]; ring

lemma grad_smul (c : ℝ) (Φ : Field C I) (f : F) : P.grad (c • Φ) f = c * P.grad Φ f := by
  unfold grad amp
  rw [mul_div_assoc', ← neg_mul_eq_mul_neg, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [smul_ω, smul_γ, Pi.smul_apply, smul_eq_mul, P.γext_smul]; ring

lemma energyForm_add_left (Φ Ψ Ξ : Field C I) :
    P.energyForm (Φ + Ψ) Ξ = P.energyForm Φ Ξ + P.energyForm Ψ Ξ := by
  unfold energyForm; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun f _ => by rw [P.grad_add]; ring

lemma energyForm_smul_left (c : ℝ) (Φ Ξ : Field C I) :
    P.energyForm (c • Φ) Ξ = c * P.energyForm Φ Ξ := by
  unfold energyForm; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun f _ => by rw [P.grad_smul]; ring

lemma energyForm_add_right (Φ Ψ Ξ : Field C I) :
    P.energyForm Ξ (Φ + Ψ) = P.energyForm Ξ Φ + P.energyForm Ξ Ψ := by
  rw [P.energyForm_comm, P.energyForm_add_left, P.energyForm_comm Φ, P.energyForm_comm Ψ]

lemma energyForm_smul_right (c : ℝ) (Φ Ξ : Field C I) :
    P.energyForm Ξ (c • Φ) = c * P.energyForm Ξ Φ := by
  rw [P.energyForm_comm, P.energyForm_smul_left, P.energyForm_comm Φ]

/-- Expansion of the energy along a direction: `‖G[Φ+εΨ]‖² = ‖G[Φ]‖² + 2ε a(Φ,Ψ) + ε² ‖G[Ψ]‖²`. -/
lemma energy_add_smul (Φ Ψ : Field C I) (ε : ℝ) :
    P.energy (Φ + ε • Ψ) = P.energy Φ + 2 * ε * P.energyForm Φ Ψ + ε ^ 2 * P.energy Ψ := by
  unfold energy
  simp only [P.energyForm_add_left, P.energyForm_add_right, P.energyForm_smul_left,
    P.energyForm_smul_right]
  rw [P.energyForm_comm Ψ Φ]
  ring

/-- Section 4.5: the derivative of the phase energy with respect to the interfacial trace
is minus the interfacial flux: `a(Φ, (0,δ)) = −δ·𝓕(Φ)`. -/
lemma energyForm_iface_dir (Φ : Field C I) (δ : I → ℝ) :
    P.energyForm Φ ⟨0, δ⟩ = -(δ ⬝ᵥ P.ifaceBalance Φ) := by
  have h := P.pairing_eq_energyForm ⟨0, δ⟩ Φ
  simpa using h.symm

end Phase

end linearity

/-! ### The two-phase problem -/

variable {Cm Fm Cp Fp I : Type*} [Fintype Cm] [Fintype Fm] [Fintype Cp] [Fintype Fp] [Fintype I]
  [DecidableEq Cm] [DecidableEq Fm] [DecidableEq Cp] [DecidableEq Fp] [DecidableEq I]

/-- The two-fluid problem: two phases sharing the interface set `I`, and the Henry
coefficient `λ > 0` of the trace law `Φ^{γ+} − λ Φ^{γ−} = F_Γ`. -/
structure TwoPhase (Cm Fm Cp Fp I : Type*) where
  neg : Phase Cm Fm I
  pos : Phase Cp Fp I
  lam : ℝ
  lam_pos : 0 < lam

namespace TwoPhase

variable (T : TwoPhase Cm Fm Cp Fp I)

/-- The reduced unknown `u = (Φ^{ω−}, Φ^{ω+}, η)` (eq. reduced-two-phase-unknown). -/
@[ext]
structure Red (Cm Cp I : Type*) where
  ωm : Cm → ℝ
  ωp : Cp → ℝ
  η : I → ℝ

instance : Zero (Red Cm Cp I) := ⟨⟨0, 0, 0⟩⟩

@[simp] lemma Red.zero_ωm : (0 : Red Cm Cp I).ωm = 0 := rfl
@[simp] lemma Red.zero_ωp : (0 : Red Cm Cp I).ωp = 0 := rfl
@[simp] lemma Red.zero_η : (0 : Red Cm Cp I).η = 0 := rfl

/-- The `−`-phase field `(Φ^{ω−}, Φ^{γ−}) = (Φ^{ω−}, η)` carried by `u`. -/
def Red.fieldM (u : Red Cm Cp I) : Phase.Field Cm I := ⟨u.ωm, u.η⟩

/-- The `+`-phase field `(Φ^{ω+}, Φ^{γ+}) = (Φ^{ω+}, λη)` carried by `u` (homogeneous
closure `Φ^{γ+} = λ Φ^{γ−}`). -/
def Red.fieldP (T : TwoPhase Cm Fm Cp Fp I) (u : Red Cm Cp I) : Phase.Field Cp I :=
  ⟨u.ωp, T.lam • u.η⟩

/-- `u` as a vector on `(Cm ⊕ Cp) ⊕ I`. -/
def Red.vec (u : Red Cm Cp I) : (Cm ⊕ Cp) ⊕ I → ℝ := Sum.elim (Sum.elim u.ωm u.ωp) u.η

/-- A vector on `(Cm ⊕ Cp) ⊕ I` as a reduced unknown. -/
def Red.ofVec (x : (Cm ⊕ Cp) ⊕ I → ℝ) : Red Cm Cp I :=
  ⟨x ∘ Sum.inl ∘ Sum.inl, x ∘ Sum.inl ∘ Sum.inr, x ∘ Sum.inr⟩

@[simp] lemma Red.vec_ofVec (x : (Cm ⊕ Cp) ⊕ I → ℝ) : (Red.ofVec x).vec = x := by
  ext ((i | i) | i) <;> rfl

lemma Red.vec_eq_zero_iff (u : Red Cm Cp I) : u.vec = 0 ↔ u = 0 := by
  constructor
  · intro h; ext K
    · exact congr_fun h (Sum.inl (Sum.inl K))
    · exact congr_fun h (Sum.inl (Sum.inr K))
    · exact congr_fun h (Sum.inr K)
  · rintro rfl; ext ((i | i) | i) <;> rfl

/-- The global constant mode `c (𝟙_ω^−, λ 𝟙_ω^+, 𝟙_γ)` of eq. (two-phase-kernel). -/
def constMode (c : ℝ) : Red Cm Cp I := ⟨fun _ => c, fun _ => T.lam * c, fun _ => c⟩

/-! ### The reduced operator (eq. two-phase-reduced-operator, schur-compact-system) -/

/-- `A_ω = diag(A_ω^−, (1/λ) A_ω^+)` with `A_ω^± = L^{ωω,±}` (eq. schur-Aomega-def). -/
def Aω : Matrix (Cm ⊕ Cp) (Cm ⊕ Cp) ℝ :=
  fromBlocks T.neg.Lww 0 0 ((1 / T.lam) • T.pos.Lww)

/-- `B = [B^−; B^+]` with `B^± = L^{ωγ,±}` (eq. schur-B-def). -/
def Bcol : Matrix (Cm ⊕ Cp) I ℝ := fromRows T.neg.Lwg T.pos.Lwg

/-- `D_Γ = −L^{γγ,−} − λ L^{γγ,+}` (eq. schur-Dgamma-def). -/
def DΓ : Matrix I I ℝ := -T.neg.Lgg - T.lam • T.pos.Lgg

/-- The symmetric reduced two-phase operator `A_red = [A_ω, B; Bᵀ, D_Γ]`
(eq. two-phase-reduced-operator). -/
def Ared : Matrix ((Cm ⊕ Cp) ⊕ I) ((Cm ⊕ Cp) ⊕ I) ℝ := fromBlocks T.Aω T.Bcol T.Bcolᵀ T.DΓ

lemma Ared_mulVec (u : Red Cm Cp I) :
    T.Ared *ᵥ u.vec =
      Sum.elim
        (Sum.elim (T.neg.Lww *ᵥ u.ωm + T.neg.Lwg *ᵥ u.η)
          ((1 / T.lam) • (T.pos.Lww *ᵥ u.ωp) + T.pos.Lwg *ᵥ u.η))
        (T.neg.Lwgᵀ *ᵥ u.ωm + T.pos.Lwgᵀ *ᵥ u.ωp + T.DΓ *ᵥ u.η) := by
  unfold Ared Aω Bcol Red.vec
  rw [fromBlocks_mulVec, fromBlocks_mulVec, transpose_fromRows, fromRows_mulVec]
  ext ((i | i) | i) <;>
    simp [Sum.elim_comp_inl, Sum.elim_comp_inr, fromCols_mulVec, smul_mulVec]

/-- The `−`-phase contribution of the bulk block: `A_red` is `H̃^− + (1/λ) Tᵀ H^+ T`,
read through its quadratic form (eq. two-phase-reduced-energy):

`uᵀ A_red u = ‖G^−[Φ^{ω−},η]‖²_{K,W,−} + (1/λ) ‖G^+[Φ^{ω+},λη]‖²_{K,W,+}`. -/
theorem Ared_quadratic (u : Red Cm Cp I) :
    u.vec ⬝ᵥ (T.Ared *ᵥ u.vec)
      = T.neg.energy u.fieldM + (1 / T.lam) * T.pos.energy (u.fieldP T) := by
  rw [T.Ared_mulVec]
  unfold Red.vec
  rw [sum_elim_dotProduct, sum_elim_dotProduct]
  have hm := T.neg.per_phase_energy u.fieldM
  have hp := T.pos.per_phase_energy (u.fieldP T)
  simp only [Red.fieldM, Red.fieldP] at hm hp ⊢
  have e1 : u.η ⬝ᵥ (T.neg.Lwgᵀ *ᵥ u.ωm) = u.ωm ⬝ᵥ (T.neg.Lwg *ᵥ u.η) := by
    rw [mulVec_transpose, dotProduct_mulVec, dotProduct_comm]
  have e2 : u.η ⬝ᵥ (T.pos.Lwgᵀ *ᵥ u.ωp) = u.ωp ⬝ᵥ (T.pos.Lwg *ᵥ u.η) := by
    rw [mulVec_transpose, dotProduct_mulVec, dotProduct_comm]
  unfold DΓ
  simp only [dotProduct_add, dotProduct_smul, smul_dotProduct, mulVec_smul, sub_mulVec,
    neg_mulVec, dotProduct_sub, dotProduct_neg, smul_mulVec, smul_eq_mul] at hp ⊢
  rw [e1, e2, ← hm, ← hp]
  have hl := T.lam_pos.ne'
  field_simp
  ring

/-- `A_red` is symmetric. -/
theorem Ared_isSymm : T.Ared.IsSymm := by
  unfold Ared
  rw [isSymm_fromBlocks_iff]
  refine ⟨?_, rfl, transpose_transpose _, ?_⟩
  · unfold Aω
    rw [isSymm_fromBlocks_iff]
    refine ⟨T.neg.Lww_isSymm, by simp, by simp, ?_⟩
    have := T.pos.Lww_isSymm
    simp only [IsSymm, transpose_smul] at this ⊢; rw [this]
  · unfold DΓ
    have h1 := T.neg.Lgg_isSymm; have h2 := T.pos.Lgg_isSymm
    simp only [IsSymm, transpose_sub, transpose_neg, transpose_smul] at h1 h2 ⊢
    rw [h1, h2]

/-- **Proposition `prop:two-phase-spd`** (first part): `A_red` is symmetric positive
semidefinite. -/
theorem Ared_posSemidef : T.Ared.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg T.Ared_isSymm.isHermitian_real fun x => ?_
  rw [star_trivial, ← Red.vec_ofVec x, T.Ared_quadratic]
  have := T.lam_pos
  have h1 := T.neg.energy_nonneg (Red.ofVec x).fieldM
  have h2 := T.pos.energy_nonneg ((Red.ofVec x).fieldP T)
  positivity

/-! ### Kernel of `A_red` (eq. two-phase-kernel) -/

/-- The null states of the two-phase energy are the multiples of the global constant mode
`(𝟙_ω^−, λ 𝟙_ω^+, 𝟙_γ)`, under Assumption `ass:kernel` in both phases. -/
theorem quadratic_eq_zero_imp (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (u : Red Cm Cp I) (h : u.vec ⬝ᵥ (T.Ared *ᵥ u.vec) = 0) :
    ∃ c, u = T.constMode c := by
  rw [T.Ared_quadratic] at h
  have hl := T.lam_pos
  have h1 := T.neg.energy_nonneg u.fieldM
  have h2 := T.pos.energy_nonneg (u.fieldP T)
  have hm0 : T.neg.energy u.fieldM = 0 := by
    have : 0 ≤ (1 / T.lam) * T.pos.energy (u.fieldP T) := by positivity
    linarith
  have hp0 : T.pos.energy (u.fieldP T) = 0 := by
    have h3 : (1 / T.lam) * T.pos.energy (u.fieldP T) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h3 | h3
    · exact absurd h3 (by positivity)
    · exact h3
  obtain ⟨cm, hcm⟩ := hm _ ((T.neg.energy_eq_zero_iff _).mp hm0)
  obtain ⟨cp, hcp⟩ := hp _ ((T.pos.energy_eq_zero_iff _).mp hp0)
  simp only [Red.fieldM, Red.fieldP, Phase.const, Phase.Field.mk.injEq] at hcm hcp
  obtain ⟨hωm, hη⟩ := hcm
  obtain ⟨hωp, hlη⟩ := hcp
  -- `λ η = c₊ 𝟙` and `η = c₋ 𝟙` force `c₊ = λ c₋`
  have hc : cp = T.lam * cm := by
    have := congr_fun hlη (Classical.arbitrary I)
    rw [hη] at this; simpa using this.symm
  refine ⟨cm, ?_⟩
  ext K
  · exact congr_fun hωm K
  · rw [hωp]; simp [constMode, hc]
  · exact congr_fun hη K

/-- Conversely, with pure Neumann exterior data (all active faces interior) the global
constant mode is in the kernel of `A_red`. -/
theorem Ared_mulVec_constMode (him : T.neg.AllInterior) (hip : T.pos.AllInterior) (c : ℝ) :
    T.Ared *ᵥ (T.constMode c).vec = 0 := by
  rw [← T.Ared_posSemidef.dotProduct_mulVec_zero_iff, star_trivial, T.Ared_quadratic]
  have e1 : (T.constMode c).fieldM = Phase.const c := by
    ext <;> rfl
  have e2 : (T.constMode c).fieldP T = Phase.const (T.lam * c) := by
    ext K
    · rfl
    · simp [Red.fieldP, constMode, Phase.const]
  rw [e1, e2, (T.neg.energy_eq_zero_iff _).mpr (T.neg.grad_const him c),
    (T.pos.energy_eq_zero_iff _).mpr (T.pos.grad_const hip _)]
  ring

/-- **Proposition `prop:two-phase-spd`** (pure Neumann case), eq. (two-phase-kernel):
`ker A_red = span{(𝟙_ω^−, λ 𝟙_ω^+, 𝟙_γ)}`. -/
theorem Ared_kernel (hm : T.neg.Connected) (hp : T.pos.Connected)
    (him : T.neg.AllInterior) (hip : T.pos.AllInterior) [Nonempty I] (u : Red Cm Cp I) :
    T.Ared *ᵥ u.vec = 0 ↔ ∃ c, u = T.constMode c := by
  constructor
  · intro h
    refine T.quadratic_eq_zero_imp hm hp u ?_
    rw [h, dotProduct_zero]
  · rintro ⟨c, rfl⟩
    exact T.Ared_mulVec_constMode him hip c

/-- **Proposition `prop:two-phase-spd`** (anchored case): if an exterior Dirichlet condition
anchors the `−` phase, then `A_red ≻ 0`. -/
theorem Ared_posDef_of_anchored (hm : T.neg.Anchored) (hp : T.pos.Connected) [Nonempty I] :
    T.Ared.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨T.Ared_isSymm.isHermitian_real, fun x hx => ?_⟩
  rw [star_trivial, ← Red.vec_ofVec x]
  set u := Red.ofVec x with hu
  refine lt_of_le_of_ne ?_ fun h => hx ?_
  · rw [T.Ared_quadratic]
    have := T.lam_pos
    have h1 := T.neg.energy_nonneg u.fieldM
    have h2 := T.pos.energy_nonneg (u.fieldP T)
    positivity
  · -- the quadratic form vanishes: both phase energies vanish
    have h' := h.symm
    rw [T.Ared_quadratic] at h'
    have hl := T.lam_pos
    have h1 := T.neg.energy_nonneg u.fieldM
    have h2 := T.pos.energy_nonneg (u.fieldP T)
    have hm0 : T.neg.energy u.fieldM = 0 := by
      have : 0 ≤ (1 / T.lam) * T.pos.energy (u.fieldP T) := by positivity
      linarith
    have hp0 : T.pos.energy (u.fieldP T) = 0 := by
      have h3 : (1 / T.lam) * T.pos.energy (u.fieldP T) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h3 | h3
      · exact absurd h3 (by positivity)
      · exact h3
    -- anchoring kills the `−` field, hence `η = 0`
    have hM := hm _ ((T.neg.energy_eq_zero_iff _).mp hm0)
    simp only [Red.fieldM, Phase.Field.ext_iff, Phase.zero_ω, Phase.zero_γ] at hM
    obtain ⟨hωm, hη⟩ := hM
    -- then the `+` field is `(Φ^{ω+}, 0)`, constant by connectedness, hence zero
    obtain ⟨c, hc⟩ := hp _ ((T.pos.energy_eq_zero_iff _).mp hp0)
    simp only [Red.fieldP, hη, smul_zero, Phase.const, Phase.Field.mk.injEq] at hc
    obtain ⟨hωp, h0⟩ := hc
    have hc0 : c = 0 := by
      have := congr_fun h0 (Classical.arbitrary I); simpa using this.symm
    rw [← Red.vec_ofVec x, ← hu, Red.vec_eq_zero_iff]
    ext K
    · simp [hωm]
    · simp [hωp, hc0]
    · simp [hη]

/-- **Proposition `prop:two-phase-spd`** (general anchored case): under Assumption
`ass:kernel` in both phases, `A_red ≻ 0` as soon as the global constant mode is not a
null state (any anchoring that removes it). -/
theorem Ared_posDef (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hanch : T.Ared *ᵥ (T.constMode 1).vec ≠ 0) : T.Ared.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨T.Ared_isSymm.isHermitian_real, fun x hx => ?_⟩
  rw [star_trivial, ← Red.vec_ofVec x]
  refine lt_of_le_of_ne ?_ fun h => ?_
  · rw [T.Ared_quadratic]
    have := T.lam_pos
    have h1 := T.neg.energy_nonneg (Red.ofVec x).fieldM
    have h2 := T.pos.energy_nonneg ((Red.ofVec x).fieldP T)
    positivity
  · obtain ⟨c, hc⟩ := T.quadratic_eq_zero_imp hm hp (Red.ofVec x) h.symm
    have hker : T.Ared *ᵥ (Red.ofVec x).vec = 0 := by
      rw [← T.Ared_posSemidef.dotProduct_mulVec_zero_iff, star_trivial]; exact h.symm
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hx
      rw [← Red.vec_ofVec x, hc, Red.vec_eq_zero_iff]
      ext K <;> simp [constMode]
    apply hanch
    have hscale : (T.constMode c).vec = c • (T.constMode 1).vec := by
      ext ((i | i) | i) <;> simp [constMode, Red.vec, mul_comm]
    rw [hc, hscale, mulVec_smul] at hker
    exact (smul_eq_zero.mp hker).resolve_left hc0

/-! ### Variational interpretation of the flux balance (Section 4.5) -/

/-- The homogeneous two-phase energy `𝓔(u) = ½‖G^−[Φ^{ω−},η]‖² + (1/2λ)‖G^+[Φ^{ω+},λη]‖²`
(eq. two-phase-energy-functional). -/
def energyFunctional (u : Red Cm Cp I) : ℝ :=
  (1 / 2) * T.neg.energy u.fieldM + (1 / (2 * T.lam)) * T.pos.energy (u.fieldP T)

lemma energyFunctional_eq (u : Red Cm Cp I) :
    T.energyFunctional u = (1 / 2) * (u.vec ⬝ᵥ (T.Ared *ᵥ u.vec)) := by
  rw [T.Ared_quadratic]; unfold energyFunctional
  have := T.lam_pos.ne'; field_simp

/-- Perturbation of the interface trace only. -/
def Red.addTrace (u : Red Cm Cp I) (ε : ℝ) (δ : I → ℝ) : Red Cm Cp I :=
  ⟨u.ωm, u.ωp, u.η + ε • δ⟩

/-- The `1/λ` weighting makes the stationarity condition in `η` the `λ`-independent flux
equilibrium: `∂_η 𝓔 · δ = −δ·(𝓕^− + 𝓕^+)`, where `𝓕^±` are the interfacial flux
contributions of the two phases. -/
theorem hasDerivAt_energyFunctional (u : Red Cm Cp I) (δ : I → ℝ) :
    HasDerivAt (fun ε => T.energyFunctional (u.addTrace ε δ))
      (-(δ ⬝ᵥ (T.neg.ifaceBalance u.fieldM + T.pos.ifaceBalance (u.fieldP T)))) 0 := by
  have hfm : ∀ ε, (u.addTrace ε δ).fieldM = u.fieldM + ε • (⟨0, δ⟩ : Phase.Field Cm I) := by
    intro ε; ext K <;> simp [Red.addTrace, Red.fieldM]
  have hfp : ∀ ε, (u.addTrace ε δ).fieldP T
      = u.fieldP T + ε • (⟨0, T.lam • δ⟩ : Phase.Field Cp I) := by
    intro ε; ext K
    · simp [Red.addTrace, Red.fieldP]
    · simp [Red.addTrace, Red.fieldP]; ring
  have hfun : (fun ε => T.energyFunctional (u.addTrace ε δ)) = fun ε =>
      ((1 / 2) * T.neg.energy u.fieldM + (1 / (2 * T.lam)) * T.pos.energy (u.fieldP T))
      + ε * (T.neg.energyForm u.fieldM ⟨0, δ⟩
          + (1 / T.lam) * T.pos.energyForm (u.fieldP T) ⟨0, T.lam • δ⟩)
      + ε ^ 2 * ((1 / 2) * T.neg.energy ⟨0, δ⟩
          + (1 / (2 * T.lam)) * T.pos.energy ⟨0, T.lam • δ⟩) := by
    funext ε
    unfold energyFunctional
    rw [hfm, hfp, T.neg.energy_add_smul, T.pos.energy_add_smul]
    have := T.lam_pos.ne'
    field_simp; ring
  rw [hfun]
  have hd : HasDerivAt (fun ε : ℝ =>
      ((1 / 2) * T.neg.energy u.fieldM + (1 / (2 * T.lam)) * T.pos.energy (u.fieldP T))
      + ε * (T.neg.energyForm u.fieldM ⟨0, δ⟩
          + (1 / T.lam) * T.pos.energyForm (u.fieldP T) ⟨0, T.lam • δ⟩)
      + ε ^ 2 * ((1 / 2) * T.neg.energy ⟨0, δ⟩
          + (1 / (2 * T.lam)) * T.pos.energy ⟨0, T.lam • δ⟩))
      (0 + 1 * (T.neg.energyForm u.fieldM ⟨0, δ⟩
          + (1 / T.lam) * T.pos.energyForm (u.fieldP T) ⟨0, T.lam • δ⟩)
        + (↑(2 : ℕ) * (0 : ℝ) ^ (2 - 1) * 1) * ((1 / 2) * T.neg.energy ⟨0, δ⟩
          + (1 / (2 * T.lam)) * T.pos.energy ⟨0, T.lam • δ⟩)) 0 := by
    refine ((hasDerivAt_const _ _).add ((hasDerivAt_id' (x := 0)).mul_const _)).add ?_
    exact ((hasDerivAt_id' (x := 0)).pow 2).mul_const _
  refine hd.congr_deriv ?_
  rw [T.neg.energyForm_iface_dir, T.pos.energyForm_iface_dir]
  have := T.lam_pos.ne'
  simp only [dotProduct_add, smul_dotProduct, smul_eq_mul]
  field_simp
  ring

/-- Stationarity in `η` is equivalent to the flux equilibrium `𝓕^− + 𝓕^+ = 0`. -/
theorem stationary_iff_flux_equilibrium (u : Red Cm Cp I) :
    (∀ δ : I → ℝ, δ ⬝ᵥ (T.neg.ifaceBalance u.fieldM + T.pos.ifaceBalance (u.fieldP T)) = 0)
      ↔ T.neg.ifaceBalance u.fieldM + T.pos.ifaceBalance (u.fieldP T) = 0 := by
  constructor
  · intro h; ext i
    have := h (Pi.single i 1)
    simpa [single_dotProduct] using this
  · intro h δ; rw [h, dotProduct_zero]

/-! ### Continuity case (Section 4.6) -/

/-- Eq. (continuity-energy): for `λ = 1` the energy is the unweighted sum of the two
phase energies, with a common trace `Φ^γ`. -/
theorem continuity_energy (hl1 : T.lam = 1) (u : Red Cm Cp I) :
    u.vec ⬝ᵥ (T.Ared *ᵥ u.vec) = T.neg.energy ⟨u.ωm, u.η⟩ + T.pos.energy ⟨u.ωp, u.η⟩ := by
  rw [T.Ared_quadratic]
  simp [Red.fieldM, Red.fieldP, hl1]

/-! ### Effect of mass terms (Section 4.7) -/

/-- The time-discrete reduced operator `A_red^{Δt}` (interface row scaled by `1/θ`),
with diagonal mass matrices `M^± = (C^±/Δt) V^±`. -/
def AredΔt (Mm : Cm → ℝ) (Mp : Cp → ℝ) (θ : ℝ) :
    Matrix ((Cm ⊕ Cp) ⊕ I) ((Cm ⊕ Cp) ⊕ I) ℝ :=
  fromBlocks
    (fromBlocks (diagonal Mm + θ • T.neg.Lww) 0 0
      ((1 / T.lam) • (diagonal Mp + θ • T.pos.Lww)))
    T.Bcol T.Bcolᵀ ((1 / θ) • T.DΓ)

/-- The scaled unknown `(Φ^{ω−}, Φ^{ω+}, η/θ)`. -/
def Red.scaleTrace (u : Red Cm Cp I) (θ : ℝ) : Red Cm Cp I := ⟨u.ωm, u.ωp, (1 / θ) • u.η⟩

/-- `A_red^{Δt}` is symmetric. -/
theorem AredΔt_isSymm (Mm : Cm → ℝ) (Mp : Cp → ℝ) (θ : ℝ) : (T.AredΔt Mm Mp θ).IsSymm := by
  unfold AredΔt
  rw [isSymm_fromBlocks_iff]
  refine ⟨?_, rfl, transpose_transpose _, ?_⟩
  · rw [isSymm_fromBlocks_iff]
    have h1 := T.neg.Lww_isSymm; have h2 := T.pos.Lww_isSymm
    simp only [IsSymm, transpose_smul, transpose_add, diagonal_transpose] at h1 h2 ⊢
    exact ⟨by rw [h1], by simp, by simp, by rw [h2]⟩
  · have := (isSymm_fromBlocks_iff.mp T.Ared_isSymm).2.2.2
    simp only [IsSymm, transpose_smul] at this ⊢; rw [this]

lemma AredΔt_mulVec (Mm : Cm → ℝ) (Mp : Cp → ℝ) (θ : ℝ) (u : Red Cm Cp I) :
    T.AredΔt Mm Mp θ *ᵥ u.vec =
      Sum.elim
        (Sum.elim (diagonal Mm *ᵥ u.ωm + θ • (T.neg.Lww *ᵥ u.ωm) + T.neg.Lwg *ᵥ u.η)
          ((1 / T.lam) • (diagonal Mp *ᵥ u.ωp + θ • (T.pos.Lww *ᵥ u.ωp)) + T.pos.Lwg *ᵥ u.η))
        (T.neg.Lwgᵀ *ᵥ u.ωm + T.pos.Lwgᵀ *ᵥ u.ωp + (1 / θ) • (T.DΓ *ᵥ u.η)) := by
  unfold AredΔt Bcol Red.vec
  rw [fromBlocks_mulVec, fromBlocks_mulVec, transpose_fromRows, fromRows_mulVec]
  ext ((i | i) | i) <;>
    simp [Sum.elim_comp_inl, Sum.elim_comp_inr, fromCols_mulVec, smul_mulVec, add_mulVec]

/-- The quadratic form of `A_red^{Δt}`: the mass terms plus `θ` times the quadratic form
of `A_red` evaluated on `(Φ^{ω−}, Φ^{ω+}, η/θ)`. -/
theorem AredΔt_quadratic (Mm : Cm → ℝ) (Mp : Cp → ℝ) {θ : ℝ} (hθ : θ ≠ 0) (u : Red Cm Cp I) :
    u.vec ⬝ᵥ (T.AredΔt Mm Mp θ *ᵥ u.vec)
      = u.ωm ⬝ᵥ (diagonal Mm *ᵥ u.ωm) + (1 / T.lam) * (u.ωp ⬝ᵥ (diagonal Mp *ᵥ u.ωp))
        + θ * ((u.scaleTrace θ).vec ⬝ᵥ (T.Ared *ᵥ (u.scaleTrace θ).vec)) := by
  rw [T.Ared_mulVec, T.AredΔt_mulVec]
  unfold Red.vec Red.scaleTrace
  simp only
  rw [sum_elim_dotProduct, sum_elim_dotProduct, sum_elim_dotProduct, sum_elim_dotProduct]
  have e3 : u.η ⬝ᵥ (T.neg.Lwgᵀ *ᵥ u.ωm) = u.ωm ⬝ᵥ (T.neg.Lwg *ᵥ u.η) := by
    rw [mulVec_transpose, dotProduct_mulVec, dotProduct_comm]
  have e4 : u.η ⬝ᵥ (T.pos.Lwgᵀ *ᵥ u.ωp) = u.ωp ⬝ᵥ (T.pos.Lwg *ᵥ u.η) := by
    rw [mulVec_transpose, dotProduct_mulVec, dotProduct_comm]
  simp only [dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul, mulVec_smul, e3, e4]
  have := T.lam_pos.ne'
  field_simp
  ring

/-- Section 4.7: for an implicit time step the mass terms remove the constant null mode:
`A_red^{Δt} ≻ 0` even with pure Neumann exterior data. -/
theorem AredΔt_posDef (Mm : Cm → ℝ) (Mp : Cp → ℝ) (hMm : ∀ K, 0 < Mm K) (hMp : ∀ K, 0 < Mp K)
    {θ : ℝ} (hθ : 0 < θ) (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    [Nonempty Cm] : (T.AredΔt Mm Mp θ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr
    ⟨(T.AredΔt_isSymm Mm Mp θ).isHermitian_real, fun x hx => ?_⟩
  rw [star_trivial, ← Red.vec_ofVec x, T.AredΔt_quadratic Mm Mp hθ.ne']
  set u := Red.ofVec x with hu
  have hdm : u.ωm ⬝ᵥ (diagonal Mm *ᵥ u.ωm) = ∑ K, Mm K * u.ωm K ^ 2 := by
    simp [dotProduct, mulVec_diagonal]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hdp : u.ωp ⬝ᵥ (diagonal Mp *ᵥ u.ωp) = ∑ K, Mp K * u.ωp K ^ 2 := by
    simp [dotProduct, mulVec_diagonal]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hq := T.Ared_posSemidef.dotProduct_mulVec_nonneg (u.scaleTrace θ).vec
  rw [star_trivial] at hq
  have hl := T.lam_pos
  have hsm : 0 ≤ ∑ K, Mm K * u.ωm K ^ 2 := Finset.sum_nonneg fun K _ => by
    have := hMm K; positivity
  have hsp : 0 ≤ ∑ K, Mp K * u.ωp K ^ 2 := Finset.sum_nonneg fun K _ => by
    have := hMp K; positivity
  rw [hdm, hdp]
  refine lt_of_le_of_ne (by positivity) fun h => hx ?_
  have h' := h.symm
  -- all three nonnegative terms vanish
  have hA : (1 / T.lam) * ∑ K, Mp K * u.ωp K ^ 2 ≥ 0 := by positivity
  have hB : θ * ((u.scaleTrace θ).vec ⬝ᵥ (T.Ared *ᵥ (u.scaleTrace θ).vec)) ≥ 0 := by positivity
  have hm0 : ∑ K, Mm K * u.ωm K ^ 2 = 0 := by linarith
  have hp0 : ∑ K, Mp K * u.ωp K ^ 2 = 0 := by
    have : (1 / T.lam) * ∑ K, Mp K * u.ωp K ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  have hq0 : (u.scaleTrace θ).vec ⬝ᵥ (T.Ared *ᵥ (u.scaleTrace θ).vec) = 0 := by
    have : θ * ((u.scaleTrace θ).vec ⬝ᵥ (T.Ared *ᵥ (u.scaleTrace θ).vec)) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hθ.ne'
    · exact h1
  have hωm : u.ωm = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun K _ => by have := hMm K; positivity)] at hm0
    ext K
    have := hm0 K (Finset.mem_univ K)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (hMm K).ne'
    · simpa using h1
  have hωp : u.ωp = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun K _ => by have := hMp K; positivity)] at hp0
    ext K
    have := hp0 K (Finset.mem_univ K)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (hMp K).ne'
    · simpa using h1
  -- the remaining trace is a constant mode with zero bulk part, hence zero
  obtain ⟨c, hc⟩ := T.quadratic_eq_zero_imp hm hp (u.scaleTrace θ) hq0
  have hcm := congr_arg Red.ωm hc
  simp only [Red.scaleTrace, hωm, constMode] at hcm
  have hc0 : c = 0 := by
    have := congr_fun hcm (Classical.arbitrary Cm); simpa using this.symm
  have hη := congr_arg Red.η hc
  simp only [Red.scaleTrace, constMode, hc0] at hη
  have hη0 : u.η = 0 := by
    have : (1 / θ) • u.η = 0 := by rw [hη]; rfl
    rcases smul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  rw [← Red.vec_ofVec x, ← hu, Red.vec_eq_zero_iff]
  ext K
  · rw [hωm]; rfl
  · rw [hωp]; rfl
  · rw [hη0]; rfl

end TwoPhase

end CutCell

end
