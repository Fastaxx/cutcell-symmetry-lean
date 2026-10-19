/-
# The scheme and its weak form (Sections 5.1–5.2 of the article)

The two phases share the interface cells `𝓜^Γ` (type `I`) and the areas `|Γ_K|`.
The source enters only through its cell means `Π^±_𝓜 r^±` (`rm`, `rp`), since
`∫ r^± Ψ^{ω±} = ∫ Π^±_𝓜 r^± Ψ^{ω±}` for `Ψ^{ω±} ∈ X^±_𝓜`.
-/
import LeanVerif.Operators

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

namespace Phase

variable {C F I : Type*} [Fintype C] [Fintype F] [Fintype I]
  [DecidableEq C] [DecidableEq F] [DecidableEq I]
variable (P : Phase C F I)

lemma innerM_sub_left (f g h : C → ℝ) : P.innerM (f - g) h = P.innerM f h - P.innerM g h := by
  unfold innerM; rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.sub_apply]; ring

lemma innerM_add_left (f g h : C → ℝ) : P.innerM (f + g) h = P.innerM f h + P.innerM g h := by
  unfold innerM; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.add_apply]; ring

lemma innerM_smul_left (c : ℝ) (f h : C → ℝ) : P.innerM (c • f) h = c * P.innerM f h := by
  unfold innerM; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma innerM_zero_right (f : C → ℝ) : P.innerM f 0 = 0 := by simp [innerM]

lemma innerΓ_comm (f g : I → ℝ) : P.innerΓ f g = P.innerΓ g f := by
  unfold innerΓ; exact Finset.sum_congr rfl fun _ _ => by ring

lemma innerΓ_add_left (f g h : I → ℝ) : P.innerΓ (f + g) h = P.innerΓ f h + P.innerΓ g h := by
  unfold innerΓ; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.add_apply]; ring

lemma innerΓ_smul_left (c : ℝ) (f h : I → ℝ) : P.innerΓ (c • f) h = c * P.innerΓ f h := by
  unfold innerΓ; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma innerΓ_zero_right (f : I → ℝ) : P.innerΓ f 0 = 0 := by simp [innerΓ]

/-- The energy `∫ |∇_𝒟 Φ|² = ∑_σ W_σ (∇_σ Φ)²`. -/
lemma innerE_self_nonneg (Q : F → ℝ) : 0 ≤ P.innerE Q Q := by
  unfold innerE
  refine Finset.sum_nonneg fun σ _ => ?_
  have := P.W_pos σ
  rw [mul_assoc, ← sq]; positivity

lemma innerE_self_eq_zero_iff (Q : F → ℝ) : P.innerE Q Q = 0 ↔ ∀ σ, Q σ = 0 := by
  unfold innerE
  have hnn : ∀ σ ∈ (Finset.univ : Finset F), 0 ≤ P.W σ * Q σ * Q σ := by
    intro σ _; have := P.W_pos σ; rw [mul_assoc, ← sq]; positivity
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h σ
    have h1 := h σ (Finset.mem_univ σ)
    rw [mul_assoc, ← sq] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 (P.W_pos σ).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  · intro h σ _; rw [h σ]; ring

lemma innerE_neg_smul_right (k : ℝ) (Q R : F → ℝ) :
    P.innerE R (fun σ => -k * Q σ) = -k * P.innerE Q R := by
  unfold innerE; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Theorem 2 with `Q = −k ∇_𝒟 Φ`:
`∫ Ψ^ω div_𝓜 Q = k ∫ ∇_𝒟Φ·∇_𝒟Ψ + ∫_Γ Ψ^γ div_Γ Q`. -/
theorem green_flux (k : ℝ) (Φ Ψ : Field C I) :
    P.innerM Ψ.ω (P.divM fun σ => -k * P.grad Φ σ)
      = k * P.innerE (P.grad Φ) (P.grad Ψ)
        + P.innerΓ Ψ.γ (P.divΓ fun σ => -k * P.grad Φ σ) := by
  have h := P.green Ψ (fun σ => -k * P.grad Φ σ)
  rw [P.innerE_neg_smul_right] at h
  linarith

end Phase

open Phase

/-- The two-phase data: two phases sharing `𝓜^Γ` and `|Γ_K|`, the conductivities
`k^± > 0` and the Henry coefficient `λ > 0`. -/
structure TwoPhase (Cm Fm Cp Fp I : Type*) [Fintype Cm] [Fintype Cp] where
  neg : Phase Cm Fm I
  pos : Phase Cp Fp I
  km : ℝ
  kp : ℝ
  lam : ℝ
  km_pos : 0 < km
  kp_pos : 0 < kp
  lam_pos : 0 < lam
  /-- both phases see the same interface pieces `Γ_K` -/
  G_eq : pos.G = neg.G

/-- A two-phase state `Φ = (Φ^-, Φ^+)`, `Φ^± = (Φ^{ω±}, Φ^{γ±})`. -/
@[ext]
structure Pair (Cm Cp I : Type*) where
  m : Field Cm I
  p : Field Cp I

namespace Pair

variable {Cm Cp I : Type*}

instance : Add (Pair Cm Cp I) := ⟨fun Φ Ψ => ⟨Φ.m + Ψ.m, Φ.p + Ψ.p⟩⟩
instance : Sub (Pair Cm Cp I) := ⟨fun Φ Ψ => ⟨Φ.m - Ψ.m, Φ.p - Ψ.p⟩⟩
instance : SMul ℝ (Pair Cm Cp I) := ⟨fun c Φ => ⟨c • Φ.m, c • Φ.p⟩⟩
instance : Zero (Pair Cm Cp I) := ⟨⟨0, 0⟩⟩

@[simp] lemma add_m (Φ Ψ : Pair Cm Cp I) : (Φ + Ψ).m = Φ.m + Ψ.m := rfl
@[simp] lemma add_p (Φ Ψ : Pair Cm Cp I) : (Φ + Ψ).p = Φ.p + Ψ.p := rfl
@[simp] lemma sub_m (Φ Ψ : Pair Cm Cp I) : (Φ - Ψ).m = Φ.m - Ψ.m := rfl
@[simp] lemma sub_p (Φ Ψ : Pair Cm Cp I) : (Φ - Ψ).p = Φ.p - Ψ.p := rfl
@[simp] lemma smul_m (c : ℝ) (Φ : Pair Cm Cp I) : (c • Φ).m = c • Φ.m := rfl
@[simp] lemma smul_p (c : ℝ) (Φ : Pair Cm Cp I) : (c • Φ).p = c • Φ.p := rfl
@[simp] lemma zero_m : (0 : Pair Cm Cp I).m = 0 := rfl
@[simp] lemma zero_p : (0 : Pair Cm Cp I).p = 0 := rfl

end Pair

namespace TwoPhase

variable {Cm Fm Cp Fp I : Type*} [Fintype Cm] [Fintype Fm] [Fintype Cp] [Fintype Fp] [Fintype I]
  [DecidableEq Cm] [DecidableEq Fm] [DecidableEq Cp] [DecidableEq Fp] [DecidableEq I]
variable (T : TwoPhase Cm Fm Cp Fp I)

/-- `X_λ` (eq. `X-lambda`): the trace law `Ψ^{γ+} = λ Ψ^{γ−}`. -/
def InX (Ψ : Pair Cm Cp I) : Prop := Ψ.p.γ = T.lam • Ψ.m.γ

lemma InX_zero : T.InX 0 := by simp [InX]

lemma InX_add {Φ Ψ : Pair Cm Cp I} (hΦ : T.InX Φ) (hΨ : T.InX Ψ) : T.InX (Φ + Ψ) := by
  unfold InX at *; simp [hΦ, hΨ, smul_add]

lemma InX_sub {Φ Ψ : Pair Cm Cp I} (hΦ : T.InX Φ) (hΨ : T.InX Ψ) : T.InX (Φ - Ψ) := by
  unfold InX at *; simp [hΦ, hΨ, smul_sub]

lemma InX_smul (c : ℝ) {Φ : Pair Cm Cp I} (hΦ : T.InX Φ) : T.InX (c • Φ) := by
  unfold InX at *; simp [hΦ, smul_comm c T.lam]

/-- The bilinear form (eq. `X-lambda`), with `ℓ^- = 1`, `ℓ^+ = 1/λ`:
`a(Φ,Ψ) = ∑_± ℓ^± ∫ k^± ∇_𝒟Φ^±·∇_𝒟Ψ^±`. -/
def a (Φ Ψ : Pair Cm Cp I) : ℝ :=
  T.km * T.neg.innerE (T.neg.grad Φ.m) (T.neg.grad Ψ.m)
    + 1 / T.lam * (T.kp * T.pos.innerE (T.pos.grad Φ.p) (T.pos.grad Ψ.p))

lemma a_comm (Φ Ψ : Pair Cm Cp I) : T.a Φ Ψ = T.a Ψ Φ := by
  unfold a; rw [T.neg.innerE_comm, T.pos.innerE_comm]

lemma a_add_left (Φ Ψ Ξ : Pair Cm Cp I) : T.a (Φ + Ψ) Ξ = T.a Φ Ξ + T.a Ψ Ξ := by
  unfold a innerE
  simp only [Pair.add_m, Pair.add_p, T.neg.grad_add, T.pos.grad_add]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]; ring

lemma a_sub_left (Φ Ψ Ξ : Pair Cm Cp I) : T.a (Φ - Ψ) Ξ = T.a Φ Ξ - T.a Ψ Ξ := by
  unfold a innerE
  simp only [Pair.sub_m, Pair.sub_p, T.neg.grad_sub, T.pos.grad_sub]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]; ring

lemma a_smul_left (c : ℝ) (Φ Ξ : Pair Cm Cp I) : T.a (c • Φ) Ξ = c * T.a Φ Ξ := by
  unfold a innerE
  simp only [Pair.smul_m, Pair.smul_p, T.neg.grad_smul, T.pos.grad_smul]
  have h1 : ∑ σ, T.neg.W σ * (c * T.neg.grad Φ.m σ) * T.neg.grad Ξ.m σ
      = c * ∑ σ, T.neg.W σ * T.neg.grad Φ.m σ * T.neg.grad Ξ.m σ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have h2 : ∑ σ, T.pos.W σ * (c * T.pos.grad Φ.p σ) * T.pos.grad Ξ.p σ
      = c * ∑ σ, T.pos.W σ * T.pos.grad Φ.p σ * T.pos.grad Ξ.p σ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h1, h2]; ring

lemma a_add_right (Φ Ψ Ξ : Pair Cm Cp I) : T.a Ξ (Φ + Ψ) = T.a Ξ Φ + T.a Ξ Ψ := by
  rw [T.a_comm, T.a_add_left, T.a_comm Φ, T.a_comm Ψ]

lemma a_sub_right (Φ Ψ Ξ : Pair Cm Cp I) : T.a Ξ (Φ - Ψ) = T.a Ξ Φ - T.a Ξ Ψ := by
  rw [T.a_comm, T.a_sub_left, T.a_comm Φ, T.a_comm Ψ]

lemma a_smul_right (c : ℝ) (Φ Ξ : Pair Cm Cp I) : T.a Ξ (c • Φ) = c * T.a Ξ Φ := by
  rw [T.a_comm, T.a_smul_left, T.a_comm Φ]

/-- The fluxes `Q^± = −k^± ∇_𝒟 Φ^±`. -/
def Qm (Φ : Pair Cm Cp I) : Fm → ℝ := fun σ => -T.km * T.neg.grad Φ.m σ
def Qp (Φ : Pair Cm Cp I) : Fp → ℝ := fun σ => -T.kp * T.pos.grad Φ.p σ

/-- The scheme (eq. `scheme`) with `g_D = 0`, `g_Γ = 0`:
`div_𝓜 Q^± = Π^±_𝓜 r^±`, `div_Γ Q^- + div_Γ Q^+ = 0`, `Φ^{γ+} = λ Φ^{γ−}`. -/
def Scheme (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ : Pair Cm Cp I) : Prop :=
  T.neg.divM (T.Qm Φ) = rm ∧ T.pos.divM (T.Qp Φ) = rp
    ∧ T.neg.divΓ (T.Qm Φ) + T.pos.divΓ (T.Qp Φ) = 0 ∧ T.InX Φ

/-- The right-hand side `∑_± ℓ^± ∫ r^± Ψ^{ω±}`. -/
def rhs (rm : Cm → ℝ) (rp : Cp → ℝ) (Ψ : Pair Cm Cp I) : ℝ :=
  T.neg.innerM rm Ψ.m.ω + 1 / T.lam * T.pos.innerM rp Ψ.p.ω

lemma rhs_add (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ Ψ : Pair Cm Cp I) :
    T.rhs rm rp (Φ + Ψ) = T.rhs rm rp Φ + T.rhs rm rp Ψ := by
  unfold rhs
  rw [T.neg.innerM_comm, T.pos.innerM_comm]
  simp only [Pair.add_m, Pair.add_p, add_ω, T.neg.innerM_add_left, T.pos.innerM_add_left]
  rw [T.neg.innerM_comm _ rm, T.neg.innerM_comm _ rm, T.pos.innerM_comm _ rp,
    T.pos.innerM_comm _ rp]
  ring

lemma rhs_sub (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ Ψ : Pair Cm Cp I) :
    T.rhs rm rp (Φ - Ψ) = T.rhs rm rp Φ - T.rhs rm rp Ψ := by
  unfold rhs
  rw [T.neg.innerM_comm, T.pos.innerM_comm]
  simp only [Pair.sub_m, Pair.sub_p, sub_ω, T.neg.innerM_sub_left, T.pos.innerM_sub_left]
  rw [T.neg.innerM_comm _ rm, T.neg.innerM_comm _ rm, T.pos.innerM_comm _ rp,
    T.pos.innerM_comm _ rp]
  ring

lemma rhs_zero (Ψ : Pair Cm Cp I) : T.rhs 0 0 Ψ = 0 := by
  simp [rhs, Phase.innerM]

/-- `∫_Γ` does not depend on the phase. -/
lemma innerΓ_pos (f g : I → ℝ) : T.pos.innerΓ f g = T.neg.innerΓ f g := by
  unfold Phase.innerΓ; rw [T.G_eq]

/-- Eq. (`residuals`): for `Ψ ∈ X_λ`,
`∑_± ℓ^± ∫ (div_𝓜 Q^± − Π r^±) Ψ^{ω±} − ∫_Γ (div_Γ Q^- + div_Γ Q^+) Ψ^{γ−}
  = a(Φ,Ψ) − ∑_± ℓ^± ∫ r^± Ψ^{ω±}`. -/
theorem residuals (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ Ψ : Pair Cm Cp I) (hΨ : T.InX Ψ) :
    T.neg.innerM (T.neg.divM (T.Qm Φ) - rm) Ψ.m.ω
      + 1 / T.lam * T.pos.innerM (T.pos.divM (T.Qp Φ) - rp) Ψ.p.ω
      - T.neg.innerΓ (T.neg.divΓ (T.Qm Φ) + T.pos.divΓ (T.Qp Φ)) Ψ.m.γ
      = T.a Φ Ψ - T.rhs rm rp Ψ := by
  have hm : T.neg.innerM Ψ.m.ω (T.neg.divM (T.Qm Φ))
      = T.km * T.neg.innerE (T.neg.grad Φ.m) (T.neg.grad Ψ.m)
        + T.neg.innerΓ Ψ.m.γ (T.neg.divΓ (T.Qm Φ)) := T.neg.green_flux T.km Φ.m Ψ.m
  have hp : T.pos.innerM Ψ.p.ω (T.pos.divM (T.Qp Φ))
      = T.kp * T.pos.innerE (T.pos.grad Φ.p) (T.pos.grad Ψ.p)
        + T.pos.innerΓ Ψ.p.γ (T.pos.divΓ (T.Qp Φ)) := T.pos.green_flux T.kp Φ.p Ψ.p
  rw [hΨ, T.innerΓ_pos, Phase.innerΓ_smul_left, Phase.innerΓ_comm] at hp
  rw [Phase.innerΓ_comm] at hm
  unfold a rhs
  rw [T.neg.innerM_sub_left, T.pos.innerM_sub_left, T.neg.innerΓ_add_left,
    T.neg.innerM_comm (T.neg.divM _), T.pos.innerM_comm (T.pos.divM _), hm, hp]
  have hl : 1 / T.lam * T.lam = 1 := by field_simp [T.lam_pos.ne']
  linear_combination (T.neg.innerΓ (T.pos.divΓ (T.Qp Φ)) Ψ.m.γ) * hl

/-- **Proposition 3** (weak form): `Φ` solves the scheme iff `Φ ∈ X_λ` and
`a(Φ,Ψ) = ∑_± ℓ^± ∫ r^± Ψ^{ω±}` for all `Ψ ∈ X_λ`. -/
theorem weak_form (rm : Cm → ℝ) (rp : Cp → ℝ) (Φ : Pair Cm Cp I) :
    T.Scheme rm rp Φ ↔ T.InX Φ ∧ ∀ Ψ, T.InX Ψ → T.a Φ Ψ = T.rhs rm rp Ψ := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h4, fun Ψ hΨ => ?_⟩
    have := T.residuals rm rp Φ Ψ hΨ
    rw [h1, h2, h3, sub_self, sub_self] at this
    simp only [Phase.innerM, Phase.innerΓ, Pi.zero_apply, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, sub_zero] at this
    linarith
  · rintro ⟨hX, h⟩
    have hres : ∀ Ψ, T.InX Ψ →
        T.neg.innerM (T.neg.divM (T.Qm Φ) - rm) Ψ.m.ω
          + 1 / T.lam * T.pos.innerM (T.pos.divM (T.Qp Φ) - rp) Ψ.p.ω
          - T.neg.innerΓ (T.neg.divΓ (T.Qm Φ) + T.pos.divΓ (T.Qp Φ)) Ψ.m.γ = 0 := by
      intro Ψ hΨ; rw [T.residuals rm rp Φ Ψ hΨ, h Ψ hΨ, sub_self]
    refine ⟨?_, ?_, ?_, hX⟩
    · funext K
      have := hres ⟨⟨Pi.single K 1, 0⟩, 0⟩ (by simp [InX])
      simp only [zero_ω, Phase.innerM_single, Phase.innerM_zero_right,
        Phase.innerΓ_zero_right, mul_zero, add_zero, sub_zero, Pi.sub_apply] at this
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (T.neg.V_pos K).ne'
      · exact sub_eq_zero.mp h0
    · funext K
      have := hres ⟨0, ⟨Pi.single K 1, 0⟩⟩ (by simp [InX])
      simp only [zero_ω, zero_γ, Phase.innerM_single, Phase.innerM_zero_right,
        Phase.innerΓ_zero_right, zero_add, sub_zero, Pi.sub_apply] at this
      have hl : (1 / T.lam) ≠ 0 := by have := T.lam_pos; positivity
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hl
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact absurd h0 (T.pos.V_pos K).ne'
      · exact sub_eq_zero.mp h0
    · funext i
      have := hres ⟨⟨0, Pi.single i 1⟩, ⟨0, T.lam • Pi.single i 1⟩⟩ (by simp [InX])
      simp only [Phase.innerM_zero_right, Phase.innerΓ_single, mul_zero, add_zero,
        zero_sub, neg_eq_zero, Pi.add_apply] at this
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (T.neg.G_pos i).ne'
      · simpa using h0

end TwoPhase

end CutCell

end
