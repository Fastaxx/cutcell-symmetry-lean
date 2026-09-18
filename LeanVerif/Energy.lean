/-
# Discrete energy estimate

Formalization of Corollary `cor:energy-estimate` of the article: for the
semi-discrete two-fluid diffusion problem with homogeneous transmission
conditions (flux equilibrium and trace law `Φ^{γ+} = λ Φ^{γ−}`), the weighted
discrete energy

`𝓔(t) = ½ C^− (Φ^{ω−},Φ^{ω−})_ω^− + (1/λ) ½ C^+ (Φ^{ω+},Φ^{ω+})_ω^+`

satisfies `d𝓔/dt = −‖G^−[Φ^−]‖²_{K,W,−} − (1/λ) ‖G^+[Φ^+]‖²_{K,W,+} ≤ 0`.

The semi-discrete balance of phase `±` is `C^± V_K ∂_t Φ^{ω±}_K + (L^{ωω,±}Φ^{ω±} +
L^{ωγ,±}Φ^{γ±})_K = 0` (no source).  Exterior faces carry no residual in the
present model (homogeneous Neumann faces are absent from `F`).
-/
import LeanVerif.TwoPhase

open Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

variable {C F I : Type*} [Fintype C] [Fintype F] [Fintype I]
  [DecidableEq C] [DecidableEq F] [DecidableEq I]

namespace Phase

variable (P : Phase C F I)

/-- The weighted bulk inner product `(Φ,Ψ)_ω = ∑_K V_K Φ_K Ψ_K` (eq. dd-inner-products). -/
def innerV (Φ Ψ : C → ℝ) : ℝ := ∑ K, P.V K * Φ K * Ψ K

/-- Testing the bulk balance with `Φ^ω` yields the phase energy plus the interfacial work
`(Φ^γ)ᵀ 𝓕`: this is the discrete Green identity with `Q = −K G`. -/
lemma dotProduct_bulkBalance (Φ : Field C I) :
    Φ.ω ⬝ᵥ P.bulkBalance Φ = P.energy Φ + Φ.γ ⬝ᵥ P.ifaceBalance Φ := by
  have h := P.pairing_eq_energyForm Φ Φ
  unfold energy; linarith

/-- Per-phase energy balance along a semi-discrete trajectory: if
`C V_K Φ'_K + (bulk balance)_K = 0`, then `d/dt ½ C (Φ^ω,Φ^ω)_ω = −‖G[Φ]‖² − Φ^γ·𝓕`. -/
theorem hasDerivAt_phase_energy (Cc : ℝ) (Φω : ℝ → C → ℝ) (Φω' : C → ℝ) (Φγ : I → ℝ) (t : ℝ)
    (hd : ∀ K, HasDerivAt (fun s => Φω s K) (Φω' K) t)
    (ode : ∀ K, Cc * P.V K * Φω' K + P.bulkBalance ⟨Φω t, Φγ⟩ K = 0) :
    HasDerivAt (fun s => (1 / 2) * Cc * P.innerV (Φω s) (Φω s))
      (-P.energy ⟨Φω t, Φγ⟩ - Φγ ⬝ᵥ P.ifaceBalance ⟨Φω t, Φγ⟩) t := by
  have hsum : HasDerivAt (fun s => ∑ K, P.V K * Φω s K * Φω s K)
      (∑ K, P.V K * (Φω' K * Φω t K + Φω t K * Φω' K)) t := by
    refine HasDerivAt.fun_sum fun K _ => ?_
    have := ((hd K).mul (hd K)).const_mul (P.V K)
    simpa [mul_assoc] using this
  have := hsum.const_mul ((1 / 2) * Cc)
  refine this.congr_deriv ?_
  have hb := P.dotProduct_bulkBalance ⟨Φω t, Φγ⟩
  simp only at hb
  have hlhs : (Φω t) ⬝ᵥ P.bulkBalance ⟨Φω t, Φγ⟩ = -∑ K, Cc * P.V K * Φω' K * Φω t K := by
    simp only [dotProduct]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun K _ => ?_
    have := ode K
    have : P.bulkBalance ⟨Φω t, Φγ⟩ K = -(Cc * P.V K * Φω' K) := by linarith
    rw [this]; ring
  rw [hlhs] at hb
  rw [Finset.mul_sum]
  have : ∑ K, (1 / 2) * Cc * (P.V K * (Φω' K * Φω t K + Φω t K * Φω' K))
      = ∑ K, Cc * P.V K * Φω' K * Φω t K := Finset.sum_congr rfl fun K _ => by ring
  rw [this]; linarith

end Phase

variable {Cm Fm Cp Fp : Type*} [Fintype Cm] [Fintype Fm] [Fintype Cp] [Fintype Fp]
  [DecidableEq Cm] [DecidableEq Fm] [DecidableEq Cp] [DecidableEq Fp]

namespace TwoPhase

variable (T : TwoPhase Cm Fm Cp Fp I)

/-- The weighted discrete energy `𝓔(t)` of eq. (dd-total-energy). -/
def totalEnergy (Cm' Cp' : ℝ) (Φm : Cm → ℝ) (Φp : Cp → ℝ) : ℝ :=
  (1 / 2) * Cm' * T.neg.innerV Φm Φm + (1 / T.lam) * ((1 / 2) * Cp' * T.pos.innerV Φp Φp)

/-- **Corollary `cor:energy-estimate`** (eq. dd-energy-rate): along a solution of the
semi-discrete two-fluid problem with flux equilibrium `𝓕^− + 𝓕^+ = 0` and trace law
`Φ^{γ+} = λ Φ^{γ−}`,
`d𝓔/dt = −‖G^−[Φ^−]‖²_{K,W,−} − (1/λ) ‖G^+[Φ^+]‖²_{K,W,+}`. -/
theorem hasDerivAt_totalEnergy (Cm' Cp' : ℝ)
    (Φm : ℝ → Cm → ℝ) (Φp : ℝ → Cp → ℝ) (Φm' : Cm → ℝ) (Φp' : Cp → ℝ) (η : I → ℝ) (t : ℝ)
    (hdm : ∀ K, HasDerivAt (fun s => Φm s K) (Φm' K) t)
    (hdp : ∀ K, HasDerivAt (fun s => Φp s K) (Φp' K) t)
    (odem : ∀ K, Cm' * T.neg.V K * Φm' K + T.neg.bulkBalance ⟨Φm t, η⟩ K = 0)
    (odep : ∀ K, Cp' * T.pos.V K * Φp' K + T.pos.bulkBalance ⟨Φp t, T.lam • η⟩ K = 0)
    (hflux : T.neg.ifaceBalance ⟨Φm t, η⟩ + T.pos.ifaceBalance ⟨Φp t, T.lam • η⟩ = 0) :
    HasDerivAt (fun s => T.totalEnergy Cm' Cp' (Φm s) (Φp s))
      (-T.neg.energy ⟨Φm t, η⟩ - (1 / T.lam) * T.pos.energy ⟨Φp t, T.lam • η⟩) t := by
  have h1 := T.neg.hasDerivAt_phase_energy Cm' Φm Φm' η t hdm odem
  have h2 := (T.pos.hasDerivAt_phase_energy Cp' Φp Φp' (T.lam • η) t hdp odep).const_mul
    (1 / T.lam)
  refine (h1.add h2).congr_deriv ?_
  -- the interfacial work cancels: `η·𝓕^− + (1/λ)(λη)·𝓕^+ = η·(𝓕^− + 𝓕^+) = 0`
  have hw : η ⬝ᵥ T.neg.ifaceBalance ⟨Φm t, η⟩
      + (1 / T.lam) * ((T.lam • η) ⬝ᵥ T.pos.ifaceBalance ⟨Φp t, T.lam • η⟩) = 0 := by
    rw [smul_dotProduct, smul_eq_mul, ← mul_assoc, show 1 / T.lam * T.lam = 1 by
      field_simp [T.lam_pos.ne'], one_mul, ← dotProduct_add, hflux, dotProduct_zero]
  linear_combination -hw

/-- The energy is non-increasing: its derivative is `≤ 0`. -/
theorem energy_rate_nonpos (Φm : Cm → ℝ) (Φp : Cp → ℝ) (η : I → ℝ) :
    -T.neg.energy ⟨Φm, η⟩ - (1 / T.lam) * T.pos.energy ⟨Φp, T.lam • η⟩ ≤ 0 := by
  have := T.lam_pos
  have h1 := T.neg.energy_nonneg ⟨Φm, η⟩
  have h2 := T.pos.energy_nonneg ⟨Φp, T.lam • η⟩
  have : 0 ≤ (1 / T.lam) * T.pos.energy ⟨Φp, T.lam • η⟩ := by positivity
  linarith

end TwoPhase

end CutCell

end
