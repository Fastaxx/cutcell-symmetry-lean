/-
Operators of one phase (Section 4 of the article).

A piecewise constant function is stored as its coefficients. The moments are
V = |K|, A = |sigma|, B = |S_K|, W = |D_sigma| and G = |Gamma_K|. Lemma 1 is not
proved here: it enters as the hypotheses of the structure `Phase`.
-/
import Mathlib

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

/-- Geometric data of one phase. `ne K s` is n_{K,s}.e_alpha, and 0 if s is not a face of K. -/
structure Phase (C F I : Type*) [Fintype C] where
  ι : I → C
  ι_inj : Function.Injective ι
  ne : C → F → ℝ
  Dir : F → Prop
  V : C → ℝ
  A : F → ℝ
  B : C → F → ℝ
  W : F → ℝ
  G : I → ℝ
  V_pos : ∀ K, 0 < V K
  W_pos : ∀ σ, 0 < W σ
  G_pos : ∀ i, 0 < G i
  A_nonneg : ∀ σ, 0 ≤ A σ
  /-- Lemma 1(c). -/
  uncut : ∀ K σ, K ∉ Set.range ι → ne K σ ≠ 0 → B K σ = A σ
  /-- A non-Dirichlet face with A > 0 has one cell on each side. -/
  interior : ∀ σ, ¬ Dir σ → A σ ≠ 0 → ∑ K, ne K σ = 0
  dirichlet : ∀ σ, Dir σ → ∑ K, ne K σ ≠ 0

namespace Phase

variable {C F I : Type*} [Fintype C] [Fintype F] [Fintype I]
  [DecidableEq C] [DecidableEq F] [DecidableEq I]
variable (P : Phase C F I)

/-- A pair (Phi, Phi_Gamma). -/
@[ext]
structure Field (C I : Type*) where
  M : C → ℝ
  Γ : I → ℝ

instance : Add (Field C I) := ⟨fun Φ Ψ => ⟨Φ.M + Ψ.M, Φ.Γ + Ψ.Γ⟩⟩
instance : Sub (Field C I) := ⟨fun Φ Ψ => ⟨Φ.M - Ψ.M, Φ.Γ - Ψ.Γ⟩⟩
instance : SMul ℝ (Field C I) := ⟨fun c Φ => ⟨c • Φ.M, c • Φ.Γ⟩⟩
instance : Zero (Field C I) := ⟨⟨0, 0⟩⟩

@[simp] lemma add_M (Φ Ψ : Field C I) : (Φ + Ψ).M = Φ.M + Ψ.M := rfl
@[simp] lemma add_Γ (Φ Ψ : Field C I) : (Φ + Ψ).Γ = Φ.Γ + Ψ.Γ := rfl
@[simp] lemma sub_M (Φ Ψ : Field C I) : (Φ - Ψ).M = Φ.M - Ψ.M := rfl
@[simp] lemma sub_Γ (Φ Ψ : Field C I) : (Φ - Ψ).Γ = Φ.Γ - Ψ.Γ := rfl
@[simp] lemma smul_M (c : ℝ) (Φ : Field C I) : (c • Φ).M = c • Φ.M := rfl
@[simp] lemma smul_Γ (c : ℝ) (Φ : Field C I) : (c • Φ).Γ = c • Φ.Γ := rfl
@[simp] lemma zero_M : (0 : Field C I).M = 0 := rfl
@[simp] lemma zero_Γ : (0 : Field C I).Γ = 0 := rfl

def const (c : ℝ) : Field C I := ⟨fun _ => c, fun _ => c⟩

@[simp] lemma const_M (c : ℝ) (K : C) : (const c : Field C I).M K = c := rfl
@[simp] lemma const_Γ (c : ℝ) (i : I) : (const c : Field C I).Γ i = c := rfl

/-! ### L2 products, eq. (14) -/

def innerM (Φ Ψ : C → ℝ) : ℝ := ∑ K, P.V K * Φ K * Ψ K

def innerΓ (Φ Ψ : I → ℝ) : ℝ := ∑ i, P.G i * Φ i * Ψ i

def innerE (Q R : F → ℝ) : ℝ := ∑ σ, P.W σ * Q σ * R σ

lemma innerM_comm (Φ Ψ : C → ℝ) : P.innerM Φ Ψ = P.innerM Ψ Φ := by
  unfold innerM; exact Finset.sum_congr rfl fun _ _ => by ring

lemma innerE_comm (Q R : F → ℝ) : P.innerE Q R = P.innerE R Q := by
  unfold innerE; exact Finset.sum_congr rfl fun _ _ => by ring

lemma innerM_single (Φ : C → ℝ) (K : C) : P.innerM Φ (Pi.single K 1) = P.V K * Φ K := by
  simp [innerM, Pi.single_apply]

lemma innerΓ_single (Φ : I → ℝ) (i : I) : P.innerΓ Φ (Pi.single i 1) = P.G i * Φ i := by
  simp [innerΓ, Pi.single_apply]

/-! ### Divergence, eq. (15) -/

def divWet (Q : F → ℝ) (K : C) : ℝ := ∑ σ, P.ne K σ * P.A σ * Q σ

def divΓK (Q : F → ℝ) (K : C) : ℝ := ∑ σ, P.ne K σ * (P.B K σ - P.A σ) * Q σ

def divK (Q : F → ℝ) (K : C) : ℝ := ∑ σ, P.ne K σ * P.B K σ * Q σ

lemma divK_eq_add (Q : F → ℝ) (K : C) : P.divK Q K = P.divWet Q K + P.divΓK Q K := by
  unfold divK divWet divΓK
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

def divM (Q : F → ℝ) : C → ℝ := fun K => P.divK Q K / P.V K

def divΓ (Q : F → ℝ) : I → ℝ := fun i => P.divΓK Q (P.ι i) / P.G i

/-- Bulk divergence in the form printed in eq. (15). -/
theorem divK_eq_sections {D : Type*} [Fintype D] (Q : F → ℝ) (K : C) (lo hi : D → F)
    (hne : ∀ σ, P.ne K σ = ∑ α, ((if σ = hi α then 1 else 0) - (if σ = lo α then 1 else 0)))
    (hB : ∀ α, P.B K (lo α) = P.B K (hi α)) :
    P.divK Q K = ∑ α, P.B K (hi α) * (Q (hi α) - Q (lo α)) := by
  unfold divK
  simp_rw [hne, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, hB]
  ring

/-- Interface divergence in the form printed in eq. (15). -/
theorem divΓK_eq_sections {D : Type*} [Fintype D] (Q : F → ℝ) (K : C) (lo hi : D → F)
    (hne : ∀ σ, P.ne K σ = ∑ α, ((if σ = hi α then 1 else 0) - (if σ = lo α then 1 else 0)))
    (hB : ∀ α, P.B K (lo α) = P.B K (hi α)) :
    P.divΓK Q K = ∑ α, ((P.B K (hi α) - P.A (hi α)) * Q (hi α)
      - (P.B K (hi α) - P.A (lo α)) * Q (lo α)) := by
  unfold divΓK
  simp_rw [hne, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, hB]

/-! ### Gradient, eqs. (17)-(18) -/

/-- Trace extended by zero to the cells without interface. -/
def Γext (ΦΓ : I → ℝ) (K : C) : ℝ :=
  if h : K ∈ Set.range P.ι then ΦΓ h.choose else 0

lemma Γext_ι (ΦΓ : I → ℝ) (i : I) : P.Γext ΦΓ (P.ι i) = ΦΓ i := by
  unfold Γext
  have h : P.ι i ∈ Set.range P.ι := ⟨i, rfl⟩
  simp only [h, ↓reduceDIte]
  exact congrArg ΦΓ (P.ι_inj h.choose_spec)

lemma Γext_of_not_mem (ΦΓ : I → ℝ) (K : C) (hK : K ∉ Set.range P.ι) : P.Γext ΦΓ K = 0 := by
  unfold Γext; simp only [hK, ↓reduceDIte]

lemma Γext_add (a b : I → ℝ) (K : C) : P.Γext (a + b) K = P.Γext a K + P.Γext b K := by
  unfold Γext; split_ifs <;> simp

lemma Γext_sub (a b : I → ℝ) (K : C) : P.Γext (a - b) K = P.Γext a K - P.Γext b K := by
  unfold Γext; split_ifs <;> simp

lemma Γext_smul (c : ℝ) (a : I → ℝ) (K : C) : P.Γext (c • a) K = c * P.Γext a K := by
  unfold Γext; split_ifs <;> simp

lemma sum_Γext_mul (ΦΓ : I → ℝ) (g : C → ℝ) :
    ∑ K, P.Γext ΦΓ K * g K = ∑ i, ΦΓ i * g (P.ι i) := by
  classical
  have hsub : ∀ K ∈ (Finset.univ : Finset C), K ∉ Finset.univ.image P.ι →
      P.Γext ΦΓ K * g K = 0 := by
    intro K _ hK
    rw [P.Γext_of_not_mem ΦΓ K (by simpa using hK), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image P.ι)) hsub,
    Finset.sum_image (fun i _ j _ h => P.ι_inj h)]
  exact Finset.sum_congr rfl fun i _ => by rw [P.Γext_ι]

/-- Gradient on the face s. -/
def grad (Φ : Field C I) (σ : F) : ℝ :=
  -(∑ K, P.ne K σ * (P.B K σ * Φ.M K + (P.A σ - P.B K σ) * P.Γext Φ.Γ K)) / P.W σ

lemma W_mul_grad (Φ : Field C I) (σ : F) :
    P.W σ * P.grad Φ σ
      = -∑ K, P.ne K σ * (P.B K σ * Φ.M K + (P.A σ - P.B K σ) * P.Γext Φ.Γ K) := by
  unfold grad
  rw [mul_div_cancel₀ _ (P.W_pos σ).ne']

lemma grad_add (Φ Ψ : Field C I) (σ : F) : P.grad (Φ + Ψ) σ = P.grad Φ σ + P.grad Ψ σ := by
  have hW := (P.W_pos σ).ne'
  apply mul_left_cancel₀ hW
  rw [mul_add, P.W_mul_grad, P.W_mul_grad, P.W_mul_grad, ← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [add_M, add_Γ, Pi.add_apply, P.Γext_add]; ring

lemma grad_sub (Φ Ψ : Field C I) (σ : F) : P.grad (Φ - Ψ) σ = P.grad Φ σ - P.grad Ψ σ := by
  have hW := (P.W_pos σ).ne'
  apply mul_left_cancel₀ hW
  rw [mul_sub, P.W_mul_grad, P.W_mul_grad, P.W_mul_grad, neg_sub_neg, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [sub_M, sub_Γ, Pi.sub_apply, P.Γext_sub]; ring

lemma grad_smul (c : ℝ) (Φ : Field C I) (σ : F) : P.grad (c • Φ) σ = c * P.grad Φ σ := by
  have hW := (P.W_pos σ).ne'
  apply mul_left_cancel₀ hW
  rw [mul_left_comm, P.W_mul_grad, P.W_mul_grad, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [smul_M, smul_Γ, Pi.smul_apply, smul_eq_mul, P.Γext_smul]; ring

/-- s = K|L. -/
def TwoCells (σ : F) (K L : C) : Prop :=
  K ≠ L ∧ ∀ M, P.ne M σ = if M = K then 1 else if M = L then -1 else 0

lemma sum_two {α : Type*} [Fintype α] [DecidableEq α] (g : α → ℝ) (a b : α) (hab : a ≠ b)
    (x y : ℝ) :
    ∑ i, (if i = a then x else if i = b then y else 0) * g i = x * g a + y * g b := by
  have h : ∀ i, (if i = a then x else if i = b then y else 0) * g i
      = (if i = a then x * g i else 0) + (if i = b then y * g i else 0) := by
    intro i
    by_cases ha : i = a
    · subst ha; simp [hab]
    · by_cases hb : i = b
      · subst hb; simp [ha]
      · simp [ha, hb]
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- Eq. (17) as printed, for s = K|L. -/
theorem W_mul_grad_of_twoCells (Φ : Field C I) {σ : F} {K L : C} (h : P.TwoCells σ K L) :
    P.W σ * P.grad Φ σ
      = P.B L σ * Φ.M L - P.B K σ * Φ.M K
        + (P.A σ - P.B L σ) * P.Γext Φ.Γ L - (P.A σ - P.B K σ) * P.Γext Φ.Γ K := by
  obtain ⟨hKL, hne⟩ := h
  rw [P.W_mul_grad]
  simp_rw [hne]
  rw [sum_two (fun M => P.B M σ * Φ.M M + (P.A σ - P.B M σ) * P.Γext Φ.Γ M) K L hKL]
  ring

/-! ### Theorem 2, eq. (19) -/

lemma innerM_divM (f : C → ℝ) (Q : F → ℝ) :
    P.innerM f (P.divM Q) = ∑ K, f K * P.divK Q K := by
  unfold innerM divM
  refine Finset.sum_congr rfl fun K _ => ?_
  have hV := (P.V_pos K).ne'
  field_simp

lemma innerΓ_divΓ (f : I → ℝ) (Q : F → ℝ) :
    P.innerΓ f (P.divΓ Q) = ∑ K, P.Γext f K * P.divΓK Q K := by
  rw [P.sum_Γext_mul f (P.divΓK Q)]
  unfold innerΓ divΓ
  refine Finset.sum_congr rfl fun i _ => ?_
  have hG := (P.G_pos i).ne'
  field_simp

/-- Theorem 2 (discrete Green identity). -/
theorem green (Φ : Field C I) (Q : F → ℝ) :
    P.innerE (P.grad Φ) Q = -P.innerM Φ.M (P.divM Q) + P.innerΓ Φ.Γ (P.divΓ Q) := by
  rw [P.innerM_divM, P.innerΓ_divΓ]
  unfold innerE divK divΓK
  have hL : ∀ σ, P.W σ * P.grad Φ σ * Q σ
      = ∑ K, (-(Φ.M K * (P.ne K σ * P.B K σ * Q σ))
          + P.Γext Φ.Γ K * (P.ne K σ * (P.B K σ - P.A σ) * Q σ)) := by
    intro σ
    rw [P.W_mul_grad, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hL, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-! ### Lemma 4 -/

lemma W_mul_grad_const (c : ℝ) (σ : F) :
    P.W σ * P.grad (const c) σ = -(∑ K, P.ne K σ) * P.A σ * c := by
  rw [P.W_mul_grad, neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases hK0 : P.ne K σ = 0
  · simp [hK0]
  · by_cases hK : K ∈ Set.range P.ι
    · obtain ⟨i, rfl⟩ := hK
      rw [P.Γext_ι]; simp; ring
    · rw [P.Γext_of_not_mem _ _ hK, P.uncut K σ hK hK0]; simp; ring

/-- Lemma 4, interior faces. -/
theorem grad_const_interior (c : ℝ) {σ : F} (hσ : ¬ P.Dir σ) : P.grad (const c) σ = 0 := by
  have hW := (P.W_pos σ).ne'
  apply mul_left_cancel₀ hW
  rw [P.W_mul_grad_const, mul_zero]
  by_cases hA : P.A σ = 0
  · simp [hA]
  · simp [P.interior σ hσ hA]

/-- Lemma 4, Dirichlet faces. -/
theorem grad_const_dirichlet (c : ℝ) {σ : F} {K : C} (hK : ∀ M, M ≠ K → P.ne M σ = 0) :
    P.W σ * P.grad (const c) σ = -P.ne K σ * P.A σ * c := by
  rw [P.W_mul_grad_const, Finset.sum_eq_single K (fun M _ hM => hK M hM) (by simp)]

/-- Assumption 2. -/
def Connected : Prop :=
  ∀ Φ : Field C I, (∀ σ, P.grad Φ σ = 0) → ∃ c, Φ = const c

/-- The phase is anchored. -/
def Anchored : Prop := ∃ σ, P.Dir σ ∧ 0 < P.A σ

theorem grad_const_of_not_anchored (h : ¬ P.Anchored) (c : ℝ) (σ : F) :
    P.grad (const c) σ = 0 := by
  by_cases hσ : P.Dir σ
  · have hA : P.A σ = 0 := by
      by_contra hA
      exact h ⟨σ, hσ, lt_of_le_of_ne (P.A_nonneg σ) (Ne.symm hA)⟩
    have hW := (P.W_pos σ).ne'
    apply mul_left_cancel₀ hW
    rw [P.W_mul_grad_const, hA]; ring
  · exact P.grad_const_interior c hσ

theorem const_eq_zero_of_anchored (h : P.Anchored) (c : ℝ)
    (hg : ∀ σ, P.grad (const c) σ = 0) : c = 0 := by
  obtain ⟨σ, hσ, hA⟩ := h
  have := P.W_mul_grad_const c σ
  rw [hg σ, mul_zero] at this
  have hs := P.dirichlet σ hσ
  rcases mul_eq_zero.mp this.symm with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (neg_eq_zero.mp h2) hs
    · exact absurd h2 hA.ne'
  · exact h1

end Phase

end CutCell

end
