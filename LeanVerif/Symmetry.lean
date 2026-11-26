/-
Proposition 5 (Section 5.2 of the article).
-/
import LeanVerif.Scheme

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

namespace TwoPhase

open Phase

variable {Cm Fm Cp Fp I : Type*} [Fintype Cm] [Fintype Fm] [Fintype Cp] [Fintype Fp] [Fintype I]
  [DecidableEq Cm] [DecidableEq Fm] [DecidableEq Cp] [DecidableEq Fp] [DecidableEq I]
variable (T : TwoPhase Cm Fm Cp Fp I)

/-- The state c (1, lambda). -/
def constMode (c : ℝ) : Pair Cm Cp I := ⟨const c, const (T.lam * c)⟩

lemma InX_constMode (c : ℝ) : T.InX (T.constMode c) := by
  unfold InX constMode; funext i; simp

/-- Eq. (25). -/
theorem a_self_nonneg (Ψ : Pair Cm Cp I) : 0 ≤ T.a Ψ Ψ := by
  unfold a
  have h1 := T.neg.innerE_self_nonneg (T.neg.grad Ψ.m)
  have h2 := T.pos.innerE_self_nonneg (T.pos.grad Ψ.p)
  have := T.km_pos; have := T.kp_pos; have := T.lam_pos
  positivity

theorem a_self_eq_zero_iff (Ψ : Pair Cm Cp I) :
    T.a Ψ Ψ = 0 ↔ (∀ σ, T.neg.grad Ψ.m σ = 0) ∧ (∀ σ, T.pos.grad Ψ.p σ = 0) := by
  rw [← T.neg.innerE_self_eq_zero_iff, ← T.pos.innerE_self_eq_zero_iff]
  unfold a
  have h1 := T.neg.innerE_self_nonneg (T.neg.grad Ψ.m)
  have h2 := T.pos.innerE_self_nonneg (T.pos.grad Ψ.p)
  have hk := T.km_pos; have hk' := T.kp_pos; have hl := T.lam_pos
  constructor
  · intro h
    have e2 : 0 ≤ 1 / T.lam * (T.kp * T.pos.innerE (T.pos.grad Ψ.p) (T.pos.grad Ψ.p)) := by
      positivity
    have e1 : 0 ≤ T.km * T.neg.innerE (T.neg.grad Ψ.m) (T.neg.grad Ψ.m) := by positivity
    have z1 : T.km * T.neg.innerE (T.neg.grad Ψ.m) (T.neg.grad Ψ.m) = 0 := by linarith
    have z2 : 1 / T.lam * (T.kp * T.pos.innerE (T.pos.grad Ψ.p) (T.pos.grad Ψ.p)) = 0 := by
      linarith
    refine ⟨(mul_eq_zero.mp z1).resolve_left hk.ne', ?_⟩
    have z3 := (mul_eq_zero.mp z2).resolve_left (by positivity)
    exact (mul_eq_zero.mp z3).resolve_left hk'.ne'
  · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

lemma eq_constMode_of_a_self_eq_zero (hm : T.neg.Connected) (hp : T.pos.Connected)
    [Nonempty I] (Ψ : Pair Cm Cp I) (hΨ : T.InX Ψ) (h0 : T.a Ψ Ψ = 0) :
    ∃ c, Ψ = T.constMode c := by
  obtain ⟨g1, g2⟩ := (T.a_self_eq_zero_iff Ψ).mp h0
  obtain ⟨cm, hcm⟩ := hm _ g1
  obtain ⟨cp, hcp⟩ := hp _ g2
  have hc : cp = T.lam * cm := by
    have := congr_fun hΨ (Classical.arbitrary I)
    rw [hcm, hcp] at this; simpa using this
  refine ⟨cm, ?_⟩
  ext1
  · exact hcm
  · rw [hcp, hc]; rfl

/-- Proposition 5, anchored case. -/
theorem a_definite (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hanch : T.neg.Anchored ∨ T.pos.Anchored) (Ψ : Pair Cm Cp I) (hΨ : T.InX Ψ)
    (h0 : T.a Ψ Ψ = 0) : Ψ = 0 := by
  obtain ⟨c, rfl⟩ := T.eq_constMode_of_a_self_eq_zero hm hp Ψ hΨ h0
  obtain ⟨g1, g2⟩ := (T.a_self_eq_zero_iff _).mp h0
  have hc : c = 0 := by
    rcases hanch with ha | ha
    · exact T.neg.const_eq_zero_of_anchored ha c g1
    · have := T.pos.const_eq_zero_of_anchored ha (T.lam * c) g2
      exact (mul_eq_zero.mp this).resolve_left T.lam_pos.ne'
  subst hc
  ext <;> simp [constMode]

/-- Proposition 5, kernel without anchoring. -/
theorem a_kernel (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hnm : ¬ T.neg.Anchored) (hnp : ¬ T.pos.Anchored) (Ψ : Pair Cm Cp I) (hΨ : T.InX Ψ) :
    T.a Ψ Ψ = 0 ↔ ∃ c, Ψ = T.constMode c := by
  constructor
  · exact T.eq_constMode_of_a_self_eq_zero hm hp Ψ hΨ
  · rintro ⟨c, rfl⟩
    rw [T.a_self_eq_zero_iff]
    exact ⟨T.neg.grad_const_of_not_anchored hnm c, T.pos.grad_const_of_not_anchored hnp _⟩

lemma a_eq_zero_of_a_self_eq_zero (Φ Ψ : Pair Cm Cp I) (h : T.a Φ Φ = 0) : T.a Φ Ψ = 0 := by
  have key : ∀ t : ℝ, 0 ≤ T.a Ψ Ψ + 2 * t * T.a Φ Ψ := by
    intro t
    have := T.a_self_nonneg (Ψ + t • Φ)
    rw [T.a_add_left, T.a_add_right, T.a_add_right, T.a_smul_left, T.a_smul_left,
      T.a_smul_right, T.a_smul_right, h, T.a_comm Ψ Φ] at this
    linarith
  by_contra hne
  have h1 := key (-(T.a Ψ Ψ + 1) / (2 * T.a Φ Ψ))
  have : 2 * (-(T.a Ψ Ψ + 1) / (2 * T.a Φ Ψ)) * T.a Φ Ψ = -(T.a Ψ Ψ + 1) := by
    field_simp
  linarith

/-- Uniqueness of the solution of the scheme. -/
theorem scheme_unique (hm : T.neg.Connected) (hp : T.pos.Connected) [Nonempty I]
    (hanch : T.neg.Anchored ∨ T.pos.Anchored) (rm : Cm → ℝ) (rp : Cp → ℝ)
    (Φ Φ' : Pair Cm Cp I) (h : T.Scheme rm rp Φ) (h' : T.Scheme rm rp Φ') : Φ = Φ' := by
  rw [T.weak_form] at h h'
  have hX := T.InX_sub h.1 h'.1
  have h0 : T.a (Φ - Φ') (Φ - Φ') = 0 := by
    rw [T.a_sub_left, h.2 _ hX, h'.2 _ hX, sub_self]
  have := T.a_definite hm hp hanch _ hX h0
  ext K
  · exact sub_eq_zero.mp (congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.m.M) this) K)
  · exact sub_eq_zero.mp (congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.m.Γ) this) K)
  · exact sub_eq_zero.mp (congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.p.M) this) K)
  · exact sub_eq_zero.mp (congr_fun (congr_arg (fun Ψ : Pair Cm Cp I => Ψ.p.Γ) this) K)

end TwoPhase

end CutCell

end
