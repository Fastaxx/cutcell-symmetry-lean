/-
Interface Schur complement (Section 5.3 of the article) and the matrix S_Gamma.
-/
import LeanVerif.Matrices

open Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

namespace TwoPhase

open Phase

variable {Cm Fm Cp Fp I : Type*} [Fintype Cm] [Fintype Fm] [Fintype Cp] [Fintype Fp] [Fintype I]
  [DecidableEq Cm] [DecidableEq Fm] [DecidableEq Cp] [DecidableEq Fp] [DecidableEq I]
variable (T : TwoPhase Cm Fm Cp Fp I)

lemma zero_trace_definite (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (Ψ : Pair Cm Cp I) (hΨ : T.InX Ψ) (h0 : Ψ.m.Γ = 0) (ha : T.a Ψ Ψ = 0) : Ψ = 0 := by
  obtain ⟨c, rfl⟩ := T.eq_constMode_of_a_self_eq_zero hm hp Ψ hΨ ha
  have hc : c = 0 := by
    have := congr_fun h0 (Classical.arbitrary I); simpa [constMode] using this
  subst hc
  ext <;> simp [constMode]

/-- Blocks of A_red. -/
def Abulk : Matrix (Cm ⊕ Cp) (Cm ⊕ Cp) ℝ := T.Ared.toBlocks₁₁
def Bc : Matrix (Cm ⊕ Cp) I ℝ := T.Ared.toBlocks₁₂
def DΓ : Matrix I I ℝ := T.Ared.toBlocks₂₂

lemma Ared_eq_fromBlocks : T.Ared = fromBlocks T.Abulk T.Bc T.Bcᵀ T.DΓ := by
  have h21 : T.Ared.toBlocks₂₁ = T.Bcᵀ := by
    ext i j
    simp only [toBlocks₂₁, Bc, toBlocks₁₂, transpose_apply, of_apply]
    exact T.Ared_isSymm.apply _ _
  rw [← h21]; unfold Abulk Bc DΓ; rw [fromBlocks_toBlocks]

lemma sum_elim_dotProduct {m n : Type*} [Fintype m] [Fintype n] (a c : m → ℝ) (b d : n → ℝ) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

lemma dotProduct_Ared_blocks (w v : Cm ⊕ Cp → ℝ) (ζ η : I → ℝ) :
    Sum.elim w ζ ⬝ᵥ (T.Ared *ᵥ Sum.elim v η)
      = w ⬝ᵥ (T.Abulk *ᵥ v + T.Bc *ᵥ η) + ζ ⬝ᵥ (T.Bcᵀ *ᵥ v + T.DΓ *ᵥ η) := by
  rw [T.Ared_eq_fromBlocks, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sum_elim_dotProduct]

theorem Abulk_posDef (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I] :
    T.Abulk.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun v hv => ?_⟩
  · refine Matrix.IsSymm.isHermitian_real ?_
    have h := T.Ared_isSymm
    rw [T.Ared_eq_fromBlocks, isSymm_fromBlocks_iff] at h
    exact h.1
  · rw [star_trivial]
    have e : v ⬝ᵥ (T.Abulk *ᵥ v) = Sum.elim v 0 ⬝ᵥ (T.Ared *ᵥ Sum.elim v 0) := by
      rw [T.dotProduct_Ared_blocks]; simp
    rw [e, T.dotProduct_Ared]
    refine lt_of_le_of_ne (T.a_self_nonneg _) fun h => hv ?_
    have h0 := T.zero_trace_definite hm hp _ (T.InX_stateOf _) (by funext i; rfl) h.symm
    rw [T.stateOf_eq_zero_iff] at h0
    funext k; exact congr_fun h0 (Sum.inl k)

/-! ### Harmonic extension, eq. (26) -/

def vStar (η : I → ℝ) : Cm ⊕ Cp → ℝ := -((T.Abulk⁻¹ * T.Bc) *ᵥ η)

/-- Discrete harmonic extension. -/
def H (η : I → ℝ) : Pair Cm Cp I := T.stateOf (Sum.elim (T.vStar η) η)

lemma InX_H (η : I → ℝ) : T.InX (T.H η) := T.InX_stateOf _

lemma H_trace (η : I → ℝ) : (T.H η).m.Γ = η := rfl

lemma Abulk_vStar (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I] (η : I → ℝ) :
    T.Abulk *ᵥ T.vStar η + T.Bc *ᵥ η = 0 := by
  have hdet : IsUnit T.Abulk.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (T.Abulk_posDef hm hp).isUnit
  unfold vStar
  rw [mulVec_neg, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.one_mul,
    neg_add_cancel]

lemma coeffs_of_zero_trace (Ψ : Pair Cm Cp I) (h0 : Ψ.m.Γ = 0) :
    coeffs Ψ = Sum.elim (Sum.elim Ψ.m.M Ψ.p.M) 0 := by
  unfold coeffs; rw [h0]

/-- Eq. (26). -/
theorem H_harmonic (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I] (η : I → ℝ)
    (Ψ : Pair Cm Cp I) (hΨ : T.InX Ψ) (h0 : Ψ.m.Γ = 0) : T.a (T.H η) Ψ = 0 := by
  rw [← T.stateOf_coeffs Ψ hΨ, H, ← T.dotProduct_Ared, coeffs_of_zero_trace Ψ h0,
    T.dotProduct_Ared_blocks, T.Abulk_vStar hm hp]
  simp

theorem H_existsUnique (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (η : I → ℝ) :
    ∃! Φ : Pair Cm Cp I, T.InX Φ ∧ Φ.m.Γ = η
      ∧ ∀ Ψ, T.InX Ψ → Ψ.m.Γ = 0 → T.a Φ Ψ = 0 := by
  refine ⟨T.H η, ⟨T.InX_H η, T.H_trace η, T.H_harmonic hm hp η⟩, ?_⟩
  rintro Φ ⟨hX, htr, hharm⟩
  have hD := T.InX_sub hX (T.InX_H η)
  have hD0 : (Φ - T.H η).m.Γ = 0 := by simp [htr, H_trace]
  have ha : T.a (Φ - T.H η) (Φ - T.H η) = 0 := by
    rw [T.a_sub_left, hharm _ hD hD0, T.H_harmonic hm hp η _ hD hD0, sub_self]
  have := T.zero_trace_definite hm hp _ hD hD0 ha
  ext K
  · exact sub_eq_zero.mp (congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.m.M) this) K)
  · exact sub_eq_zero.mp (congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.m.Γ) this) K)
  · exact sub_eq_zero.mp (congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.p.M) this) K)
  · exact sub_eq_zero.mp (congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.p.Γ) this) K)

theorem harmonic_iff_div (Φ : Pair Cm Cp I) :
    (∀ Ψ, T.InX Ψ → Ψ.m.Γ = 0 → T.a Φ Ψ = 0)
      ↔ T.neg.divM (T.Qm Φ) = 0 ∧ T.pos.divM (T.Qp Φ) = 0 := by
  constructor
  · intro h
    have hres : ∀ Ψ, T.InX Ψ → Ψ.m.Γ = 0 →
        T.neg.innerM (T.neg.divM (T.Qm Φ)) Ψ.m.M
          + 1 / T.lam * T.pos.innerM (T.pos.divM (T.Qp Φ)) Ψ.p.M = 0 := by
      intro Ψ hΨ h0
      have := T.residuals 0 0 Φ Ψ hΨ
      rw [h Ψ hΨ h0, T.rhs_zero, h0, Phase.innerΓ_zero_right, sub_zero, sub_zero, sub_zero,
        sub_zero] at this
      exact this
    refine ⟨?_, ?_⟩
    · funext K
      have := hres ⟨⟨Pi.single K 1, 0⟩, 0⟩ (by simp [InX]) rfl
      simp only [zero_M, Phase.innerM_single, Phase.innerM_zero_right, mul_zero,
        add_zero] at this
      exact (mul_eq_zero.mp this).resolve_left (T.neg.V_pos K).ne'
    · funext K
      have := hres ⟨0, ⟨Pi.single K 1, 0⟩⟩ (by simp [InX]) rfl
      simp only [zero_M, Phase.innerM_single, Phase.innerM_zero_right,
        zero_add] at this
      have hl : (1 / T.lam) ≠ 0 := by have := T.lam_pos; positivity
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hl)).resolve_left
        (T.pos.V_pos K).ne'
  · rintro ⟨h1, h2⟩ Ψ hΨ h0
    have := T.residuals 0 0 Φ Ψ hΨ
    rw [h1, h2, T.rhs_zero, h0, Phase.innerΓ_zero_right, sub_zero, sub_zero, sub_zero,
      sub_zero] at this
    simp only [Phase.innerM, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
      add_zero] at this
    exact this.symm

/-- Eq. (26) is one bulk problem per phase. -/
theorem harmonic_iff_div_grad (Φ : Pair Cm Cp I) :
    (∀ Ψ, T.InX Ψ → Ψ.m.Γ = 0 → T.a Φ Ψ = 0)
      ↔ T.neg.divM (fun σ => T.km * T.neg.grad Φ.m σ) = 0
        ∧ T.pos.divM (fun σ => T.kp * T.pos.grad Φ.p σ) = 0 := by
  have e1 : T.Qm Φ = fun σ => (-1 : ℝ) * (T.km * T.neg.grad Φ.m σ) := by
    funext σ; simp [Qm]
  have e2 : T.Qp Φ = fun σ => (-1 : ℝ) * (T.kp * T.pos.grad Φ.p σ) := by
    funext σ; simp [Qp]
  rw [T.harmonic_iff_div, e1, e2, T.neg.divM_mul (-1), T.pos.divM_mul (-1)]
  simp

/-! ### Proposition 6 -/

def s (η ζ : I → ℝ) : ℝ := T.a (T.H η) (T.H ζ)

theorem s_comm (η ζ : I → ℝ) : T.s η ζ = T.s ζ η := T.a_comm _ _

theorem s_nonneg (η : I → ℝ) : 0 ≤ T.s η η := T.a_self_nonneg _

theorem s_min (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I] (η : I → ℝ)
    (Ψ : Pair Cm Cp I) (hΨ : T.InX Ψ) (htr : Ψ.m.Γ = η) : T.s η η ≤ T.a Ψ Ψ := by
  have hX0 := T.InX_sub hΨ (T.InX_H η)
  have h0 : (Ψ - T.H η).m.Γ = 0 := by simp [htr, H_trace]
  have hdec : Ψ = T.H η + (Ψ - T.H η) := by ext <;> simp
  have hc : T.a (T.H η) (Ψ - T.H η) = 0 := T.H_harmonic hm hp η _ hX0 h0
  rw [hdec, T.a_add_left, T.a_add_right, T.a_add_right, hc, T.a_comm (Ψ - T.H η), hc]
  have := T.a_self_nonneg (Ψ - T.H η)
  unfold s; linarith

/-- First formula of (27). -/
theorem s_isLeast (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I] (η : I → ℝ) :
    IsLeast {x | ∃ Ψ : Pair Cm Cp I, T.InX Ψ ∧ Ψ.m.Γ = η ∧ x = T.a Ψ Ψ} (T.s η η) := by
  refine ⟨⟨T.H η, T.InX_H η, T.H_trace η, rfl⟩, ?_⟩
  rintro _ ⟨Ψ, hΨ, htr, rfl⟩
  exact T.s_min hm hp η Ψ hΨ htr

theorem s_flux (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I] (η ζ : I → ℝ) :
    T.s η ζ = -T.neg.innerΓ (T.neg.divΓ (T.Qm (T.H η)) + T.pos.divΓ (T.Qp (T.H η))) ζ := by
  obtain ⟨d1, d2⟩ := (T.harmonic_iff_div (T.H η)).mp (T.H_harmonic hm hp η)
  have := T.residuals 0 0 (T.H η) (T.H ζ) (T.InX_H ζ)
  rw [d1, d2, T.rhs_zero, T.H_trace, sub_zero, sub_zero, sub_zero] at this
  simp only [Phase.innerM, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_sub] at this
  unfold s; linarith

/-- Second formula of (27). -/
theorem s_DtN (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I] (η ζ : I → ℝ) :
    T.s η ζ = T.neg.innerΓ (T.km • T.neg.divΓ (T.neg.grad (T.H η).m)
      + T.kp • T.pos.divΓ (T.pos.grad (T.H η).p)) ζ := by
  rw [T.s_flux hm hp η ζ]
  have e1 : T.neg.divΓ (T.Qm (T.H η)) = (-T.km) • T.neg.divΓ (T.neg.grad (T.H η).m) :=
    T.neg.divΓ_mul (-T.km) (T.neg.grad (T.H η).m)
  have e2 : T.pos.divΓ (T.Qp (T.H η)) = (-T.kp) • T.pos.divΓ (T.pos.grad (T.H η).p) :=
    T.pos.divΓ_mul (-T.kp) (T.pos.grad (T.H η).p)
  rw [e1, e2]
  unfold Phase.innerΓ
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Proposition 6, anchored case. -/
theorem s_definite (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hanch : T.neg.Anchored ∨ T.pos.Anchored) (η : I → ℝ) (h : T.s η η = 0) : η = 0 := by
  have := T.a_definite hm hp hanch _ (T.InX_H η) h
  rw [← T.H_trace η, this]; rfl

/-- Proposition 6, kernel without anchoring. -/
theorem s_kernel (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hnm : ¬ T.neg.Anchored) (hnp : ¬ T.pos.Anchored) (η : I → ℝ) :
    T.s η η = 0 ↔ ∃ c, η = fun _ => c := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := (T.a_kernel hm hp hnm hnp _ (T.InX_H η)).mp h
    refine ⟨c, ?_⟩
    rw [← T.H_trace η, hc]; rfl
  · rintro ⟨c, rfl⟩
    have h1 := T.s_min hm hp _ (T.constMode c) (T.InX_constMode c) rfl
    rw [(T.a_kernel hm hp hnm hnp _ (T.InX_constMode c)).mpr ⟨c, rfl⟩] at h1
    exact le_antisymm h1 (T.s_nonneg _)

/-- Proposition 6, reduction to the interface, eq. (28). -/
theorem scheme_iff_interface (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ : Pair Cm Cp I) (hΦ : T.InX Φ) :
    T.Scheme rm rp Φ ↔
      (∀ Ψ, T.InX Ψ → Ψ.m.Γ = 0 → T.a (Φ - T.H Φ.m.Γ) Ψ = T.rhs rm rp Ψ)
        ∧ ∀ ζ, T.s Φ.m.Γ ζ = T.rhs rm rp (T.H ζ) := by
  set η := Φ.m.Γ
  have hX0 := T.InX_sub hΦ (T.InX_H η)
  have h00 : (Φ - T.H η).m.Γ = 0 := by simp [η, H_trace]
  have k2 : ∀ Ψ, T.InX Ψ → Ψ.m.Γ = 0 → T.a (Φ - T.H η) Ψ = T.a Φ Ψ := by
    intro Ψ hΨ h0; rw [T.a_sub_left, T.H_harmonic hm hp η Ψ hΨ h0, sub_zero]
  have k3 : ∀ ζ, T.a Φ (T.H ζ) = T.s η ζ := by
    intro ζ
    have : T.a (Φ - T.H η) (T.H ζ) = 0 := by
      rw [T.a_comm]; exact T.H_harmonic hm hp ζ _ hX0 h00
    rw [T.a_sub_left] at this; unfold s; linarith
  rw [T.weak_form]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨fun Ψ hΨ h0 => by rw [k2 Ψ hΨ h0, h Ψ hΨ],
      fun ζ => by rw [← k3 ζ, h _ (T.InX_H ζ)]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hΦ, fun Ψ hΨ => ?_⟩
    have hΨ0 := T.InX_sub hΨ (T.InX_H Ψ.m.Γ)
    have hΨ00 : (Ψ - T.H Ψ.m.Γ).m.Γ = 0 := by simp [H_trace]
    have e1 : T.a Φ Ψ = T.a Φ (Ψ - T.H Ψ.m.Γ) + T.a Φ (T.H Ψ.m.Γ) := by
      rw [T.a_sub_right]; ring
    rw [e1, ← k2 _ hΨ0 hΨ00, h1 _ hΨ0 hΨ00, k3, h2, T.rhs_sub]
    ring

/-! ### Matrix S_Gamma -/

def SΓ : Matrix I I ℝ := T.DΓ - T.Bcᵀ * T.Abulk⁻¹ * T.Bc

/-- S_Gamma is the matrix of s. -/
theorem dotProduct_SΓ (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (η ζ : I → ℝ) : ζ ⬝ᵥ (T.SΓ *ᵥ η) = T.s η ζ := by
  unfold s H
  rw [← T.dotProduct_Ared, T.dotProduct_Ared_blocks, T.Abulk_vStar hm hp, dotProduct_zero,
    zero_add]
  unfold SΓ vStar
  rw [sub_mulVec, mulVec_neg, mulVec_mulVec, ← Matrix.mul_assoc, sub_eq_neg_add, add_comm]

/-- S_Gamma is positive definite if one phase is anchored. -/
theorem SΓ_posDef (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hanch : T.neg.Anchored ∨ T.pos.Anchored) : T.SΓ.PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.IsSymm.isHermitian_real ?_, fun η hη => ?_⟩
  · refine Matrix.IsSymm.ext fun i j => ?_
    have h1 := T.dotProduct_SΓ hm hp (Pi.single i 1) (Pi.single j 1)
    have h2 := T.dotProduct_SΓ hm hp (Pi.single j 1) (Pi.single i 1)
    have e : ∀ (M : Matrix I I ℝ) (a b : I), Pi.single a (1 : ℝ) ⬝ᵥ (M *ᵥ Pi.single b 1) = M a b :=
      fun M a b => by simp [single_dotProduct, mulVec_single]
    rw [e] at h1 h2
    rw [h1, h2, T.s_comm]
  · rw [star_trivial, T.dotProduct_SΓ hm hp]
    exact lt_of_le_of_ne (T.s_nonneg η) fun h => hη (T.s_definite hm hp hanch η h.symm)

end TwoPhase

end CutCell

end
