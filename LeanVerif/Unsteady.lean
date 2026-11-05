/-
# Unsteady problem (Section 5.4 of the article)

The semi-discrete scheme replaces `div_𝓜 Q^± = r̄^±` by
`ϱ^± ∂_tΦ^± + div_𝓜 Q^± = r̄^±`, the flux balance and the trace law holding at
each time.  Its weak form is eq. (26), and eq. (27) is the energy identity.  The last
statement is the `θ`-scheme remark that closes Section 5.4.
-/
import LeanVerif.Symmetry

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

namespace Phase

variable {C F I : Type*} [Fintype C] [Fintype F] [Fintype I]
  [DecidableEq C] [DecidableEq F] [DecidableEq I]
variable (P : Phase C F I)

lemma innerM_self_nonneg (f : C → ℝ) : 0 ≤ P.innerM f f := by
  unfold innerM
  refine Finset.sum_nonneg fun K _ => ?_
  have := P.V_pos K
  rw [mul_assoc, ← sq]; positivity

/-- `d/dt ∫ (Φ)² = 2 ∫ ∂_tΦ Φ`. -/
lemma hasDerivAt_innerM_self (x : ℝ → C → ℝ) (dx : C → ℝ) (t : ℝ)
    (hd : ∀ K, HasDerivAt (fun s => x s K) (dx K) t) :
    HasDerivAt (fun s => P.innerM (x s) (x s)) (2 * P.innerM dx (x t)) t := by
  unfold innerM
  have h : HasDerivAt (fun s => ∑ K, P.V K * x s K * x s K)
      (∑ K, P.V K * (dx K * x t K + x t K * dx K)) t := by
    refine HasDerivAt.fun_sum fun K _ => ?_
    have := ((hd K).mul (hd K)).const_mul (P.V K)
    simpa [mul_assoc] using this
  refine h.congr_deriv ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `∫ (x₁ − x₀)(θx₁ + (1−θ)x₀) = ½∫x₁² − ½∫x₀² + (θ − ½)∫(x₁ − x₀)²`. -/
lemma innerM_theta (x0 x1 : C → ℝ) (θ : ℝ) :
    P.innerM (x1 - x0) (θ • x1 + (1 - θ) • x0)
      = 1 / 2 * P.innerM x1 x1 - 1 / 2 * P.innerM x0 x0
        + (θ - 1 / 2) * P.innerM (x1 - x0) (x1 - x0) := by
  unfold innerM
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun _ _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Phase

namespace TwoPhase

open Phase

variable {Cm Fm Cp Fp I : Type*} [Fintype Cm] [Fintype Fm] [Fintype Cp] [Fintype Fp] [Fintype I]
  [DecidableEq Cm] [DecidableEq Fm] [DecidableEq Cp] [DecidableEq Fp] [DecidableEq I]
variable (T : TwoPhase Cm Fm Cp Fp I)

/-- The semi-discrete scheme at one time, with `dm = ∂_tΦ^-`, `dp = ∂_tΦ^+`. -/
def SemiScheme (ϱm ϱp : ℝ) (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ : Pair Cm Cp I)
    (dm : Cm → ℝ) (dp : Cp → ℝ) : Prop :=
  ϱm • dm + T.neg.divM (T.Qm Φ) = rm ∧ ϱp • dp + T.pos.divM (T.Qp Φ) = rp
    ∧ T.neg.divΓ (T.Qm Φ) + T.pos.divΓ (T.Qp Φ) = 0 ∧ T.InX Φ

lemma semiScheme_iff (ϱm ϱp : ℝ) (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ : Pair Cm Cp I)
    (dm : Cm → ℝ) (dp : Cp → ℝ) :
    T.SemiScheme ϱm ϱp rm rp Φ dm dp ↔ T.Scheme (rm - ϱm • dm) (rp - ϱp • dp) Φ := by
  unfold SemiScheme Scheme
  rw [eq_sub_iff_add_eq', eq_sub_iff_add_eq']

/-- Eq. (26): the proof of Proposition 3 is unchanged. -/
theorem weak_unsteady (ϱm ϱp : ℝ) (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ : Pair Cm Cp I)
    (dm : Cm → ℝ) (dp : Cp → ℝ) :
    T.SemiScheme ϱm ϱp rm rp Φ dm dp ↔ T.InX Φ ∧ ∀ Ψ, T.InX Ψ →
      ϱm * T.neg.innerM dm Ψ.m.M + 1 / T.lam * (ϱp * T.pos.innerM dp Ψ.p.M) + T.a Φ Ψ
        = T.rhs rm rp Ψ := by
  rw [T.semiScheme_iff, T.weak_form]
  have e : ∀ Ψ : Pair Cm Cp I, T.rhs (rm - ϱm • dm) (rp - ϱp • dp) Ψ
      = T.rhs rm rp Ψ - (ϱm * T.neg.innerM dm Ψ.m.M + 1 / T.lam * (ϱp * T.pos.innerM dp Ψ.p.M)) := by
    intro Ψ
    unfold rhs
    rw [T.neg.innerM_sub_left, T.pos.innerM_sub_left, T.neg.innerM_smul_left,
      T.pos.innerM_smul_left]
    ring
  simp_rw [e]
  constructor
  · rintro ⟨hX, h⟩; exact ⟨hX, fun Ψ hΨ => by rw [h Ψ hΨ]; ring⟩
  · rintro ⟨hX, h⟩; exact ⟨hX, fun Ψ hΨ => by rw [← h Ψ hΨ]; ring⟩

/-- The energy `½ ∑_± ℓ^± ϱ^± ∫ (Φ^±)²`. -/
def energy (ϱm ϱp : ℝ) (Φ : Pair Cm Cp I) : ℝ :=
  1 / 2 * (ϱm * T.neg.innerM Φ.m.M Φ.m.M + 1 / T.lam * (ϱp * T.pos.innerM Φ.p.M Φ.p.M))

/-- Eq. (27): with `r^± = 0`, along a solution of the semi-discrete scheme,
`d/dt ½ ∑_± ℓ^± ϱ^± ∫ (Φ^±)² = −a(Φ,Φ) ≤ 0`. -/
theorem energy_rate (ϱm ϱp : ℝ) (Φ : ℝ → Pair Cm Cp I) (dm : Cm → ℝ) (dp : Cp → ℝ)
    (t : ℝ) (hdm : ∀ K, HasDerivAt (fun s => (Φ s).m.M K) (dm K) t)
    (hdp : ∀ K, HasDerivAt (fun s => (Φ s).p.M K) (dp K) t)
    (hS : T.SemiScheme ϱm ϱp 0 0 (Φ t) dm dp) :
    HasDerivAt (fun s => T.energy ϱm ϱp (Φ s)) (-T.a (Φ t) (Φ t)) t
      ∧ -T.a (Φ t) (Φ t) ≤ 0 := by
  refine ⟨?_, neg_nonpos.mpr (T.a_self_nonneg _)⟩
  have h1 := T.neg.hasDerivAt_innerM_self (fun s => (Φ s).m.M) dm t hdm
  have h2 := T.pos.hasDerivAt_innerM_self (fun s => (Φ s).p.M) dp t hdp
  have h := ((h1.const_mul ϱm).add ((h2.const_mul ϱp).const_mul (1 / T.lam))).const_mul (1 / 2)
  refine h.congr_deriv ?_
  obtain ⟨hX, hw⟩ := (T.weak_unsteady ϱm ϱp 0 0 (Φ t) dm dp).mp hS
  have := hw (Φ t) hX
  rw [T.rhs_zero] at this
  linarith

/-- The `θ`-scheme remark of Section 5.4: if `Φ^n, Φ^{n+1} ∈ X_λ` satisfy the weak form with
`∂_tΦ^± ≈ (Φ^{±,n+1} − Φ^{±,n})/Δt` and `a(θΦ^{n+1} + (1−θ)Φ^n, ·)`, then the energy does not
increase for `θ ≥ ½`. -/
theorem theta_energy (ϱm ϱp : ℝ) (hϱm : 0 ≤ ϱm) (hϱp : 0 ≤ ϱp) {θ Δt : ℝ} (hθ : 1 / 2 ≤ θ)
    (hΔt : 0 < Δt) (Φ0 Φ1 : Pair Cm Cp I) (h0 : T.InX Φ0) (h1 : T.InX Φ1)
    (hw : ∀ Ψ, T.InX Ψ →
      ϱm * T.neg.innerM ((1 / Δt) • (Φ1.m.M - Φ0.m.M)) Ψ.m.M
        + 1 / T.lam * (ϱp * T.pos.innerM ((1 / Δt) • (Φ1.p.M - Φ0.p.M)) Ψ.p.M)
        + T.a (θ • Φ1 + (1 - θ) • Φ0) Ψ = 0) :
    T.energy ϱm ϱp Φ1 ≤ T.energy ϱm ϱp Φ0 := by
  set Ψ := θ • Φ1 + (1 - θ) • Φ0 with hΨdef
  have hX : T.InX Ψ := T.InX_add (T.InX_smul θ h1) (T.InX_smul (1 - θ) h0)
  have hw' := hw Ψ hX
  rw [T.neg.innerM_smul_left, T.pos.innerM_smul_left] at hw'
  have hm := T.neg.innerM_theta Φ0.m.M Φ1.m.M θ
  have hp := T.pos.innerM_theta Φ0.p.M Φ1.p.M θ
  have eΨm : Ψ.m.M = θ • Φ1.m.M + (1 - θ) • Φ0.m.M := rfl
  have eΨp : Ψ.p.M = θ • Φ1.p.M + (1 - θ) • Φ0.p.M := rfl
  rw [← eΨm] at hm; rw [← eΨp] at hp
  have ha := T.a_self_nonneg Ψ
  have dm := T.neg.innerM_self_nonneg (Φ1.m.M - Φ0.m.M)
  have dp := T.pos.innerM_self_nonneg (Φ1.p.M - Φ0.p.M)
  have hl : 0 < 1 / T.lam := by have := T.lam_pos; positivity
  -- `ϱ^- I^- + (1/λ) ϱ^+ I^+ = −Δt a(Ψ,Ψ) ≤ 0`
  have hI : ϱm * T.neg.innerM (Φ1.m.M - Φ0.m.M) Ψ.m.M
      + 1 / T.lam * (ϱp * T.pos.innerM (Φ1.p.M - Φ0.p.M) Ψ.p.M) ≤ 0 := by
    have e : ϱm * T.neg.innerM (Φ1.m.M - Φ0.m.M) Ψ.m.M
        + 1 / T.lam * (ϱp * T.pos.innerM (Φ1.p.M - Φ0.p.M) Ψ.p.M) = -Δt * T.a Ψ Ψ := by
      field_simp at hw'
      field_simp
      linarith
    rw [e]; nlinarith
  have q1 : 0 ≤ ϱm * ((θ - 1 / 2) * T.neg.innerM (Φ1.m.M - Φ0.m.M) (Φ1.m.M - Φ0.m.M)) := by
    have : 0 ≤ θ - 1 / 2 := by linarith
    positivity
  have q2 : 0 ≤ 1 / T.lam * (ϱp * ((θ - 1 / 2) * T.pos.innerM (Φ1.p.M - Φ0.p.M)
      (Φ1.p.M - Φ0.p.M))) := by
    have : 0 ≤ θ - 1 / 2 := by linarith
    positivity
  unfold energy
  rw [hm, hp] at hI
  nlinarith

end TwoPhase

end CutCell

end
