/-
# Discrete spaces and operators of one phase (Section 4 of the article)

A phase is fixed and the sign `±` is dropped, as in Sections 3–4 of the article.

## The model

A piecewise constant function is identified with its coefficients, and the `L²` products
of the article (eq. `products`) are the corresponding weighted sums:

| article | Lean |
|---|---|
| active cells `𝓜^±` | type `C` |
| active faces `𝓔^±` (all directions) | type `F` |
| interface cells `𝓜^Γ ⊂ 𝓜^±` | type `I`, injected in `C` by `ι` |
| `n_{K,σ}·e_α ∈ {−1,0,1}` | `ne K σ` (`0` when `σ ∉ 𝓔(K)`) |
| `V_K, A_σ, B_K^α, W_σ, |Γ_K|` | `V K, A σ, B K σ, W σ, G i` |
| Dirichlet faces `𝓔_D` | predicate `Dir` |
| `Φ^ω ∈ X_𝓜`, `Φ^γ ∈ X_Γ`, `Q ∈ H_𝓔` | `C → ℝ`, `I → ℝ`, `F → ℝ` |

The moment formulas of the divergences (eqs. `div-omega`, `div-gamma`, `div`) and of the
gradient (eqs. `grad-omega`, `grad-gamma`) are the definitions.  Their derivation from the
divergence theorem uses Lemma 1 (moments), which is geometric and enters the model as
hypotheses: `uncut` is Lemma 1(c), `interior`/`dirichlet` describe the neighbours of a face
(a face whose missing neighbour is outside the phase has `A_σ = 0`, Lemma 1(b)), and the
positivity fields are Lemma 1(e) and the definition of the active sets.
-/
import Mathlib

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

/-- The geometric data of one phase (Sections 3.1–3.3 of the article). -/
structure Phase (C F I : Type*) [Fintype C] where
  /-- the injection `𝓜^Γ ↪ 𝓜^±` -/
  ι : I → C
  ι_inj : Function.Injective ι
  /-- `n_{K,σ}·e_α` for `σ ∈ 𝓔(K) ∩ 𝓔^{(α)}`, `0` if `σ ∉ 𝓔(K)` -/
  ne : C → F → ℝ
  /-- Dirichlet faces `𝓔_D` -/
  Dir : F → Prop
  /-- volume `V_K = |K^±|` -/
  V : C → ℝ
  /-- aperture `A_σ = |σ^±|` -/
  A : F → ℝ
  /-- centroidal section `B_K^α = |S_K^α|` (`α` = direction of `σ`) -/
  B : C → F → ℝ
  /-- dual volume `W_σ = |D_σ|` -/
  W : F → ℝ
  /-- interface area `|Γ_K|` -/
  G : I → ℝ
  V_pos : ∀ K, 0 < V K
  W_pos : ∀ σ, 0 < W σ
  G_pos : ∀ i, 0 < G i
  A_nonneg : ∀ σ, 0 ≤ A σ
  /-- Lemma 1(c): on a cell without interface, `A_σ = B_K^α` -/
  uncut : ∀ K σ, K ∉ Set.range ι → ne K σ ≠ 0 → B K σ = A σ
  /-- a non-Dirichlet face with `A_σ ≠ 0` is `K|L`: one cell on each side -/
  interior : ∀ σ, ¬ Dir σ → A σ ≠ 0 → ∑ K, ne K σ = 0
  /-- a Dirichlet face has a single neighbour -/
  dirichlet : ∀ σ, Dir σ → ∑ K, ne K σ ≠ 0

namespace Phase

variable {C F I : Type*} [Fintype C] [Fintype F] [Fintype I]
  [DecidableEq C] [DecidableEq F] [DecidableEq I]
variable (P : Phase C F I)

/-- A pair `Φ = (Φ^ω, Φ^γ) ∈ X_𝓜 × X_Γ`. -/
@[ext]
structure Field (C I : Type*) where
  ω : C → ℝ
  γ : I → ℝ

instance : Add (Field C I) := ⟨fun Φ Ψ => ⟨Φ.ω + Ψ.ω, Φ.γ + Ψ.γ⟩⟩
instance : Sub (Field C I) := ⟨fun Φ Ψ => ⟨Φ.ω - Ψ.ω, Φ.γ - Ψ.γ⟩⟩
instance : SMul ℝ (Field C I) := ⟨fun c Φ => ⟨c • Φ.ω, c • Φ.γ⟩⟩
instance : Zero (Field C I) := ⟨⟨0, 0⟩⟩

@[simp] lemma add_ω (Φ Ψ : Field C I) : (Φ + Ψ).ω = Φ.ω + Ψ.ω := rfl
@[simp] lemma add_γ (Φ Ψ : Field C I) : (Φ + Ψ).γ = Φ.γ + Ψ.γ := rfl
@[simp] lemma sub_ω (Φ Ψ : Field C I) : (Φ - Ψ).ω = Φ.ω - Ψ.ω := rfl
@[simp] lemma sub_γ (Φ Ψ : Field C I) : (Φ - Ψ).γ = Φ.γ - Ψ.γ := rfl
@[simp] lemma smul_ω (c : ℝ) (Φ : Field C I) : (c • Φ).ω = c • Φ.ω := rfl
@[simp] lemma smul_γ (c : ℝ) (Φ : Field C I) : (c • Φ).γ = c • Φ.γ := rfl
@[simp] lemma zero_ω : (0 : Field C I).ω = 0 := rfl
@[simp] lemma zero_γ : (0 : Field C I).γ = 0 := rfl

/-- The constant `c` on every `K^±` and on `Γ`. -/
def const (c : ℝ) : Field C I := ⟨fun _ => c, fun _ => c⟩

@[simp] lemma const_ω (c : ℝ) (K : C) : (const c : Field C I).ω K = c := rfl
@[simp] lemma const_γ (c : ℝ) (i : I) : (const c : Field C I).γ i = c := rfl

/-! ### `L²` products (eq. `products`) -/

/-- `∫_{Ω^±} Φ^ω Ψ^ω = ∑_K V_K Φ^ω_K Ψ^ω_K`. -/
def innerM (Φ Ψ : C → ℝ) : ℝ := ∑ K, P.V K * Φ K * Ψ K

/-- `∫_Γ Φ^γ Ψ^γ = ∑_K |Γ_K| Φ^γ_K Ψ^γ_K`. -/
def innerΓ (Φ Ψ : I → ℝ) : ℝ := ∑ i, P.G i * Φ i * Ψ i

/-- `∫_{Ω^±} Q·P = ∑_σ W_σ Q_σ P_σ`. -/
def innerE (Q R : F → ℝ) : ℝ := ∑ σ, P.W σ * Q σ * R σ

lemma innerM_comm (Φ Ψ : C → ℝ) : P.innerM Φ Ψ = P.innerM Ψ Φ := by
  unfold innerM; exact Finset.sum_congr rfl fun _ _ => by ring

lemma innerE_comm (Q R : F → ℝ) : P.innerE Q R = P.innerE R Q := by
  unfold innerE; exact Finset.sum_congr rfl fun _ _ => by ring

lemma innerM_single (Φ : C → ℝ) (K : C) : P.innerM Φ (Pi.single K 1) = P.V K * Φ K := by
  simp [innerM, Pi.single_apply]

lemma innerΓ_single (Φ : I → ℝ) (i : I) : P.innerΓ Φ (Pi.single i 1) = P.G i * Φ i := by
  simp [innerΓ, Pi.single_apply]

/-! ### Divergence (eqs. `div-omega`, `div-gamma`, `div`, `div-functions`) -/

/-- Flux of `Q` through the faces of `K`: `div^ω_K Q = ∑_σ A_σ Q_{K,σ}`,
with `Q_{K,σ} = Q_σ n_{K,σ}·e_α`. -/
def divω (Q : F → ℝ) (K : C) : ℝ := ∑ σ, P.ne K σ * P.A σ * Q σ

/-- Flux of `Q` through `Γ_K`: `div^Γ_K Q = ∑_σ (B_K^α − A_σ) Q_{K,σ}`. -/
def divΓK (Q : F → ℝ) (K : C) : ℝ := ∑ σ, P.ne K σ * (P.B K σ - P.A σ) * Q σ

/-- Flux of `Q` through `∂K^±`: `div_K Q = ∑_σ B_K^α Q_{K,σ}`. -/
def divK (Q : F → ℝ) (K : C) : ℝ := ∑ σ, P.ne K σ * P.B K σ * Q σ

/-- Eq. (`div`): `div_K = div^ω_K + div^Γ_K`. -/
lemma divK_eq_add (Q : F → ℝ) (K : C) : P.divK Q K = P.divω Q K + P.divΓK Q K := by
  unfold divK divω divΓK
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The function `div_𝓜 Q ∈ X_𝓜` (value `div_K Q / V_K` on `K^±`). -/
def divM (Q : F → ℝ) : C → ℝ := fun K => P.divK Q K / P.V K

/-- The function `div_Γ Q ∈ X_Γ` (value `div^Γ_K Q / |Γ_K|` on `Γ_K`). -/
def divΓ (Q : F → ℝ) : I → ℝ := fun i => P.divΓK Q (P.ι i) / P.G i

/-! ### Gradient (eqs. `grad-omega`, `grad-gamma`, `grad`, `grad-functions`) -/

/-- The convention `Φ^γ_K := 0` for `K ∉ 𝓜^Γ`. -/
def γext (Φγ : I → ℝ) (K : C) : ℝ :=
  if h : K ∈ Set.range P.ι then Φγ h.choose else 0

lemma γext_ι (Φγ : I → ℝ) (i : I) : P.γext Φγ (P.ι i) = Φγ i := by
  unfold γext
  have h : P.ι i ∈ Set.range P.ι := ⟨i, rfl⟩
  simp only [h, ↓reduceDIte]
  exact congrArg Φγ (P.ι_inj h.choose_spec)

lemma γext_of_not_mem (Φγ : I → ℝ) (K : C) (hK : K ∉ Set.range P.ι) : P.γext Φγ K = 0 := by
  unfold γext; simp only [hK, ↓reduceDIte]

lemma γext_add (a b : I → ℝ) (K : C) : P.γext (a + b) K = P.γext a K + P.γext b K := by
  unfold γext; split_ifs <;> simp

lemma γext_sub (a b : I → ℝ) (K : C) : P.γext (a - b) K = P.γext a K - P.γext b K := by
  unfold γext; split_ifs <;> simp

lemma γext_smul (c : ℝ) (a : I → ℝ) (K : C) : P.γext (c • a) K = c * P.γext a K := by
  unfold γext; split_ifs <;> simp

/-- Sums against the extended trace are sums over `𝓜^Γ`. -/
lemma sum_γext_mul (Φγ : I → ℝ) (g : C → ℝ) :
    ∑ K, P.γext Φγ K * g K = ∑ i, Φγ i * g (P.ι i) := by
  classical
  have hsub : ∀ K ∈ (Finset.univ : Finset C), K ∉ Finset.univ.image P.ι →
      P.γext Φγ K * g K = 0 := by
    intro K _ hK
    rw [P.γext_of_not_mem Φγ K (by simpa using hK), zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image P.ι)) hsub,
    Finset.sum_image (fun i _ j _ h => P.ι_inj h)]
  exact Finset.sum_congr rfl fun i _ => by rw [P.γext_ι]

/-- `∇^ω_σ(Φ^ω)`: `W_σ ∇^ω_σ = B_L Φ^ω_L − B_K Φ^ω_K` for `σ = K|L`. -/
def gradω (Φω : C → ℝ) (σ : F) : ℝ := -(∑ K, P.ne K σ * P.B K σ * Φω K) / P.W σ

/-- `∇^Γ_σ(Φ^γ)`: `W_σ ∇^Γ_σ = (A_σ − B_L) Φ^γ_L − (A_σ − B_K) Φ^γ_K` for `σ = K|L`. -/
def gradΓ (Φγ : I → ℝ) (σ : F) : ℝ :=
  -(∑ K, P.ne K σ * (P.A σ - P.B K σ) * P.γext Φγ K) / P.W σ

/-- `∇_σ(Φ^ω,Φ^γ) = ∇^ω_σ(Φ^ω) + ∇^Γ_σ(Φ^γ)`; the function `∇_𝒟 Φ ∈ H_𝓔`. -/
def grad (Φ : Field C I) (σ : F) : ℝ := P.gradω Φ.ω σ + P.gradΓ Φ.γ σ

lemma W_mul_grad (Φ : Field C I) (σ : F) :
    P.W σ * P.grad Φ σ
      = -∑ K, P.ne K σ * (P.B K σ * Φ.ω K + (P.A σ - P.B K σ) * P.γext Φ.γ K) := by
  unfold grad gradω gradΓ
  have hW := (P.W_pos σ).ne'
  rw [mul_add, mul_div_cancel₀ _ hW, mul_div_cancel₀ _ hW, ← neg_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma grad_add (Φ Ψ : Field C I) (σ : F) : P.grad (Φ + Ψ) σ = P.grad Φ σ + P.grad Ψ σ := by
  have hW := (P.W_pos σ).ne'
  apply mul_left_cancel₀ hW
  rw [mul_add, P.W_mul_grad, P.W_mul_grad, P.W_mul_grad, ← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [add_ω, add_γ, Pi.add_apply, P.γext_add]; ring

lemma grad_sub (Φ Ψ : Field C I) (σ : F) : P.grad (Φ - Ψ) σ = P.grad Φ σ - P.grad Ψ σ := by
  have hW := (P.W_pos σ).ne'
  apply mul_left_cancel₀ hW
  rw [mul_sub, P.W_mul_grad, P.W_mul_grad, P.W_mul_grad, neg_sub_neg, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [sub_ω, sub_γ, Pi.sub_apply, P.γext_sub]; ring

lemma grad_smul (c : ℝ) (Φ : Field C I) (σ : F) : P.grad (c • Φ) σ = c * P.grad Φ σ := by
  have hW := (P.W_pos σ).ne'
  apply mul_left_cancel₀ hW
  rw [mul_left_comm, P.W_mul_grad, P.W_mul_grad, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [smul_ω, smul_γ, Pi.smul_apply, smul_eq_mul, P.γext_smul]; ring

lemma grad_zero (σ : F) : P.grad 0 σ = 0 := by
  simp [grad, gradω, gradΓ, γext]

/-! ### Theorem 2: discrete Green identity (eqs. `adjoint`, `green`) -/

/-- First identity of (`adjoint`): `∫ ∇^ω_𝒟 Φ^ω · Q = −∫ Φ^ω div_𝓜 Q`,
i.e. `∇^ω_𝒟 = −div_𝓜^*`. -/
theorem green_ω (Φω : C → ℝ) (Q : F → ℝ) :
    P.innerE (P.gradω Φω) Q = -P.innerM Φω (P.divM Q) := by
  unfold innerE innerM gradω divM divK
  have hL : ∀ σ, P.W σ * (-(∑ K, P.ne K σ * P.B K σ * Φω K) / P.W σ) * Q σ
      = -∑ K, P.ne K σ * P.B K σ * Φω K * Q σ := by
    intro σ
    rw [mul_div_cancel₀ _ (P.W_pos σ).ne', neg_mul, Finset.sum_mul]
  have hR : ∀ K, P.V K * Φω K * ((∑ σ, P.ne K σ * P.B K σ * Q σ) / P.V K)
      = ∑ σ, P.ne K σ * P.B K σ * Φω K * Q σ := by
    intro K
    have hV := (P.V_pos K).ne'
    rw [show P.V K * Φω K * ((∑ σ, P.ne K σ * P.B K σ * Q σ) / P.V K)
        = Φω K * ∑ σ, P.ne K σ * P.B K σ * Q σ by field_simp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hL, hR]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]

/-- Second identity of (`adjoint`): `∫ ∇^Γ_𝒟 Φ^γ · Q = ∫_Γ Φ^γ div_Γ Q`,
i.e. `∇^Γ_𝒟 = div_Γ^*`. -/
theorem green_Γ (Φγ : I → ℝ) (Q : F → ℝ) :
    P.innerE (P.gradΓ Φγ) Q = P.innerΓ Φγ (P.divΓ Q) := by
  unfold innerE innerΓ gradΓ divΓ
  have hR : ∀ i, P.G i * Φγ i * (P.divΓK Q (P.ι i) / P.G i) = Φγ i * P.divΓK Q (P.ι i) := by
    intro i; field_simp [(P.G_pos i).ne']
  simp_rw [hR]
  rw [← P.sum_γext_mul Φγ (P.divΓK Q)]
  unfold divΓK
  have hL : ∀ σ, P.W σ * (-(∑ K, P.ne K σ * (P.A σ - P.B K σ) * P.γext Φγ K) / P.W σ) * Q σ
      = ∑ K, P.γext Φγ K * (P.ne K σ * (P.B K σ - P.A σ) * Q σ) := by
    intro σ
    rw [mul_div_cancel₀ _ (P.W_pos σ).ne', neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hL, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **Theorem 2** (eq. `green`):
`∫ ∇_𝒟(Φ^ω,Φ^γ)·Q = −∫ Φ^ω div_𝓜 Q + ∫_Γ Φ^γ div_Γ Q`. -/
theorem green (Φ : Field C I) (Q : F → ℝ) :
    P.innerE (P.grad Φ) Q = -P.innerM Φ.ω (P.divM Q) + P.innerΓ Φ.γ (P.divΓ Q) := by
  rw [← P.green_ω, ← P.green_Γ]
  unfold innerE grad
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### Jumps (eq. `jumps`) -/

/-- `σ = K|L`: `σ` is the upper face of `K` and the lower face of `L`. -/
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

/-- First identity of (`jumps`): `W_σ ∇_σ` is the mass of the jumps of `Φ` in `D_σ`,
on the face (`A_σ(Φ^ω_L − Φ^ω_K)`) and on `Γ` (`(Φ^γ_M − Φ^ω_M) ∫_{Γ_{M,σ}} n·e_α`, where
`∫_{Γ_{M,σ}} n·e_α = (n_{M,σ}·e_α)(B_M^α − A_σ)` by Lemma 1(d)). -/
theorem jumps_grad (Φ : Field C I) {σ : F} {K L : C} (h : P.TwoCells σ K L) :
    P.W σ * P.grad Φ σ
      = P.A σ * (Φ.ω L - Φ.ω K)
        + ((P.γext Φ.γ K - Φ.ω K) * (P.ne K σ * (P.B K σ - P.A σ))
          + (P.γext Φ.γ L - Φ.ω L) * (P.ne L σ * (P.B L σ - P.A σ))) := by
  obtain ⟨hKL, hne⟩ := h
  rw [P.W_mul_grad]
  simp_rw [hne]
  rw [sum_two (fun M => P.B M σ * Φ.ω M + (P.A σ - P.B M σ) * P.γext Φ.γ M) K L hKL]
  simp [hKL.symm]
  ring

/-- Second identity of (`jumps`): if the faces of `K` normal to `e_α` are `lo α`
(lower) and `hi α` (upper), and `B` depends only on the direction, then
`div_K Q = ∑_α B_K^α (Q_{σ'} − Q_σ)`, the mass of the jumps of `Q` across the sections. -/
theorem jumps_div {D : Type*} [Fintype D] (Q : F → ℝ) (K : C) (lo hi : D → F)
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

/-! ### Lemma 4 (constants) -/

/-- On every face, `B_K^α c + (A_σ − B_K^α) c = A_σ c` for each neighbour (Lemma 1(c)). -/
lemma W_mul_grad_const (c : ℝ) (σ : F) :
    P.W σ * P.grad (const c) σ = -(∑ K, P.ne K σ) * P.A σ * c := by
  rw [P.W_mul_grad, neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun K _ => ?_
  by_cases hK0 : P.ne K σ = 0
  · simp [hK0]
  · by_cases hK : K ∈ Set.range P.ι
    · obtain ⟨i, rfl⟩ := hK
      rw [P.γext_ι]; simp; ring
    · rw [P.γext_of_not_mem _ _ hK, P.uncut K σ hK hK0]; simp; ring

/-- **Lemma 4**, interior faces: the gradient of a constant vanishes. -/
theorem grad_const_interior (c : ℝ) {σ : F} (hσ : ¬ P.Dir σ) : P.grad (const c) σ = 0 := by
  have hW := (P.W_pos σ).ne'
  apply mul_left_cancel₀ hW
  rw [P.W_mul_grad_const, mul_zero]
  by_cases hA : P.A σ = 0
  · simp [hA]
  · simp [P.interior σ hσ hA]

/-- **Lemma 4**, Dirichlet faces: `W_σ ∇_σ = −(n_{K,σ}·e_α) A_σ c` (`K` the neighbour). -/
theorem grad_const_dirichlet (c : ℝ) (σ : F) :
    P.W σ * P.grad (const c) σ = -(∑ K, P.ne K σ) * P.A σ * c :=
  P.W_mul_grad_const c σ

/-- Assumption 2 (discrete connectedness). -/
def Connected : Prop :=
  ∀ Φ : Field C I, (∀ σ, P.grad Φ σ = 0) → ∃ c, Φ = const c

/-- A phase is anchored if `A_σ > 0` on some Dirichlet face. -/
def Anchored : Prop := ∃ σ, P.Dir σ ∧ 0 < P.A σ

/-- Without anchoring, constants have zero gradient on every face. -/
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

/-- On an anchoring face, a constant with zero gradient vanishes. -/
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
