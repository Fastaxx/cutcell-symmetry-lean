/-
# One phase of the two-fluid cut-cell discretization

Formalization of Section 2 (operators) and Section 3 (discrete Green identity)
of the article *"A two-fluid cut-cell discretization as a non-overlapping
domain decomposition"* (`main.tex`).

## The model

We fix one phase `Ω^±` (the sign is dropped throughout).  All Cartesian
directions `α` are gathered in one face type:

* `C` : the active bulk cells `𝓘_ω^±`  (each carries a phase average `Φ^ω_K`);
* `F` : the active faces `⋃_α 𝓕^{α±}` (each carries a flux `Q_f`);
* `I` : the mixed cells `𝓘_γ`, injected into `C` by `ι` (each carries a
  one-sided trace `Φ^γ_K`);
* `inc K f ∈ {−1, 0, +1}` : the incidence of cell `K` and face `f`, equal to
  `+1` if `f = f^{α+}(K)`, `−1` if `f = f^{α−}(K)` and `0` otherwise.  We do not
  need to record that faces have at most one cell on each side; the two-cell
  situation of the article is recovered in `Phase.grad_two_cells`.

The moments are `V_K`, `A_f`, `B_K^α` (written `B K f` with `α` the direction
of `f`), `W_f`, and the face diffusion coefficient `K_f`.

Exterior boundary faces: homogeneous Neumann faces carry no flux unknown and
are simply absent from `F`; a homogeneous Dirichlet face is a face with a
single adjacent cell (the "missing" amplified trace is zero).  In both cases
the exterior residual `𝓡_{∂Ω}` of the article vanishes, which is why the Green
identity below has no boundary term.
-/
import Mathlib

open Finset Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace CutCell

variable {C F I : Type*} [Fintype C] [Fintype F] [Fintype I]
  [DecidableEq C] [DecidableEq F] [DecidableEq I]

/-- The geometric data of one phase (Section 2.1 of the article). -/
structure Phase (C F I : Type*) where
  /-- the injection `𝓘_γ ↪ 𝓘_ω` of the mixed cells into the cells -/
  ι : I → C
  ι_inj : Function.Injective ι
  /-- cell/face incidence (`+1` on the `+` face of `K`, `−1` on its `−` face) -/
  inc : C → F → ℝ
  /-- phase volumes `V_K^±` -/
  V : C → ℝ
  /-- face apertures `A_f^{α±}` -/
  A : F → ℝ
  /-- centroidal face moments `B_K^{α±}` (`α` = direction of `f`) -/
  B : C → F → ℝ
  /-- staggered volumes `W_f^{α±}` -/
  W : F → ℝ
  /-- face diffusion coefficients `K_f^{α±}` -/
  Kf : F → ℝ
  V_pos : ∀ K, 0 < V K
  W_pos : ∀ f, 0 < W f
  Kf_pos : ∀ f, 0 < Kf f
  /-- an uncut cell has `B_K = A_f` on its faces (the centroidal slice is the full face) -/
  uncut_B : ∀ K f, K ∉ Set.range ι → inc K f ≠ 0 → B K f = A f

namespace Phase

variable (P : Phase C F I)

/-- A phase field `Φ^± = (Φ^{ω±}, Φ^{γ±})`: bulk averages and one-sided traces. -/
@[ext]
structure Field (C I : Type*) where
  ω : C → ℝ
  γ : I → ℝ

instance : Add (Field C I) := ⟨fun Φ Ψ => ⟨Φ.ω + Ψ.ω, Φ.γ + Ψ.γ⟩⟩
instance : SMul ℝ (Field C I) := ⟨fun c Φ => ⟨c • Φ.ω, c • Φ.γ⟩⟩
instance : Zero (Field C I) := ⟨⟨0, 0⟩⟩

@[simp] lemma add_ω (Φ Ψ : Field C I) : (Φ + Ψ).ω = Φ.ω + Ψ.ω := rfl
@[simp] lemma add_γ (Φ Ψ : Field C I) : (Φ + Ψ).γ = Φ.γ + Ψ.γ := rfl
@[simp] lemma smul_ω (c : ℝ) (Φ : Field C I) : (c • Φ).ω = c • Φ.ω := rfl
@[simp] lemma smul_γ (c : ℝ) (Φ : Field C I) : (c • Φ).γ = c • Φ.γ := rfl
@[simp] lemma zero_ω : (0 : Field C I).ω = 0 := rfl
@[simp] lemma zero_γ : (0 : Field C I).γ = 0 := rfl

/-- The constant field `c 𝟙^± = (c 𝟙_ω, c 𝟙_γ)`. -/
def const (c : ℝ) : Field C I := ⟨fun _ => c, fun _ => c⟩

@[simp] lemma const_ω (c : ℝ) (K : C) : (const c : Field C I).ω K = c := rfl
@[simp] lemma const_γ (c : ℝ) (i : I) : (const c : Field C I).γ i = c := rfl

/-! ### Divergences (eq. dd-div-bulk, dd-div-gamma, dd-div-full)

All divergences below are multiplied by `V_K`, as in the article's displays. -/

/-- `V_K div^{αω}_K(A,Q) = A_{f⁺} Q_{f⁺} − A_{f⁻} Q_{f⁻}` (Cartesian-face part). -/
def divBulk (Q : F → ℝ) (K : C) : ℝ := ∑ f, P.inc K f * P.A f * Q f

/-- `V_K div^{αγ}_K(A,B,Q) = (B_K − A_{f⁺}) Q_{f⁺} + (A_{f⁻} − B_K) Q_{f⁻}`
(embedded-interface part). -/
def divIface (Q : F → ℝ) (K : C) : ℝ := ∑ f, P.inc K f * (P.B K f - P.A f) * Q f

/-- `V_K div^α_K(B,Q) = B_K (Q_{f⁺} − Q_{f⁻})` (full directional divergence). -/
def divFull (Q : F → ℝ) (K : C) : ℝ := ∑ f, P.inc K f * P.B K f * Q f

/-- Eq. (dd-div-full): the apertures cancel when the two parts are summed. -/
lemma divFull_eq_add (Q : F → ℝ) (K : C) :
    P.divFull Q K = P.divBulk Q K + P.divIface Q K := by
  unfold divFull divBulk divIface
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun f _ => by ring

/-! ### The face-amplified trace and the gradient (eq. green-amplified ... green-gradient-telescopic) -/

/-- The one-sided trace of cell `K`, extended by zero to uncut cells. -/
def γext (Φγ : I → ℝ) (K : C) : ℝ :=
  if h : K ∈ Set.range P.ι then Φγ h.choose else 0

lemma γext_ι (Φγ : I → ℝ) (i : I) : P.γext Φγ (P.ι i) = Φγ i := by
  unfold γext
  have h : P.ι i ∈ Set.range P.ι := ⟨i, rfl⟩
  simp only [h, ↓reduceDIte]
  congr 1
  exact P.ι_inj h.choose_spec

lemma γext_of_not_mem (Φγ : I → ℝ) (K : C) (hK : K ∉ Set.range P.ι) :
    P.γext Φγ K = 0 := by
  unfold γext; simp only [hK, ↓reduceDIte]

/-- Sums weighted by the extended trace reduce to sums over the mixed cells `𝓘_γ`. -/
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

/-- Summing a function against a two-point incidence pattern. -/
lemma sum_ite_two {α : Type*} [Fintype α] [DecidableEq α] (g : α → ℝ) (a b : α)
    (hab : a ≠ b) (x y : ℝ) :
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

/-- The face-amplified value `Φ̂_K|_f := B_K Φ^ω_K + (A_f − B_K) Φ^γ_K` (eq. green-amplified). -/
def amp (Φ : Field C I) (K : C) (f : F) : ℝ :=
  P.B K f * Φ.ω K + (P.A f - P.B K f) * P.γext Φ.γ K

/-- The bulk part of the staggered gradient, `grad^{αω}_f(B,W,Φ)` (eq. dd-grad-bulk). -/
def gradBulk (Φω : C → ℝ) (f : F) : ℝ :=
  -(∑ K, P.inc K f * (P.B K f * Φω K)) / P.W f

/-- The interfacial part of the staggered gradient, `grad^{αγ}_f(A,B,W,Φ)` (eq. dd-grad-gamma). -/
def gradIface (Φγ : I → ℝ) (f : F) : ℝ :=
  -(∑ K, P.inc K f * ((P.A f - P.B K f) * P.γext Φγ K)) / P.W f

/-- The full directional gradient `G_f[Φ^ω, Φ^γ]`, written through the face-amplified
values: `W_f G_f = −∑_K inc(K,f) Φ̂_K|_f`. -/
def grad (Φ : Field C I) (f : F) : ℝ :=
  -(∑ K, P.inc K f * P.amp Φ K f) / P.W f

/-- Eq. (dd-gradient-split): `G = grad^{αω} + grad^{αγ}`. -/
lemma grad_eq_add (Φ : Field C I) (f : F) :
    P.grad Φ f = P.gradBulk Φ.ω f + P.gradIface Φ.γ f := by
  unfold grad gradBulk gradIface amp
  rw [← add_div, ← neg_add, ← Finset.sum_add_distrib]
  congr 2
  exact Finset.sum_congr rfl fun K _ => by ring

lemma W_mul_grad (Φ : Field C I) (f : F) :
    P.W f * P.grad Φ f = -(∑ K, P.inc K f * P.amp Φ K f) := by
  unfold grad; field_simp [(P.W_pos f).ne']

/-- A face `f` separating exactly two cells `K` and `K'`, with `f = f^{α−}(K) = f^{α+}(K')`. -/
def TwoCells (f : F) (K K' : C) : Prop :=
  K ≠ K' ∧ ∀ L, P.inc L f = if L = K then -1 else if L = K' then 1 else 0

/-- The telescopic identity (eq. green-gradient-telescopic):
`W_f G_f[Φ] = Φ̂_K|_f − Φ̂_{K'}|_f`. -/
theorem grad_two_cells (Φ : Field C I) {f : F} {K K' : C} (h : P.TwoCells f K K') :
    P.W f * P.grad Φ f = P.amp Φ K f - P.amp Φ K' f := by
  rw [P.W_mul_grad]
  obtain ⟨hne, hinc⟩ := h
  simp_rw [hinc]
  rw [sum_ite_two _ K K' hne]
  ring

/-- Eq. (green-gradient-expanded): the explicit two-cell form of the gradient. -/
theorem grad_two_cells_expanded (Φ : Field C I) {f : F} {K K' : C}
    (h : P.TwoCells f K K') :
    P.W f * P.grad Φ f =
      P.B K f * Φ.ω K - P.B K' f * Φ.ω K'
      + ((P.A f - P.B K f) * P.γext Φ.γ K - (P.A f - P.B K' f) * P.γext Φ.γ K') := by
  rw [P.grad_two_cells Φ h]; unfold amp; ring

/-- A cell `K` whose two faces in some direction are `fp = f^{α+}(K)` and `fm = f^{α−}(K)`,
and with no other face in that direction. This is the situation of eq. (dd-div-full). -/
def TwoFaces (K : C) (fp fm : F) : Prop :=
  fp ≠ fm ∧ ∀ f, P.inc K f = if f = fp then 1 else if f = fm then -1 else 0

/-- Eq. (dd-div-full) in its explicit form: `V_K div_K = B_K Q_{f⁺} − B_K Q_{f⁻}`
(here `B` may depend on the face, so we write `B_K^{f⁺}`, `B_K^{f⁻}`). -/
theorem divFull_two_faces (Q : F → ℝ) {K : C} {fp fm : F} (h : P.TwoFaces K fp fm) :
    P.divFull Q K = P.B K fp * Q fp - P.B K fm * Q fm := by
  obtain ⟨hne, hinc⟩ := h
  unfold divFull
  simp_rw [hinc, mul_assoc]
  rw [sum_ite_two (fun f => P.B K f * Q f) fp fm hne]
  ring

/-- Eq. (dd-div-gamma) in its explicit form. -/
theorem divIface_two_faces (Q : F → ℝ) {K : C} {fp fm : F} (h : P.TwoFaces K fp fm) :
    P.divIface Q K = (P.B K fp - P.A fp) * Q fp + (P.A fm - P.B K fm) * Q fm := by
  obtain ⟨hne, hinc⟩ := h
  unfold divIface
  simp_rw [hinc, mul_assoc]
  rw [sum_ite_two (fun f => (P.B K f - P.A f) * Q f) fp fm hne]
  ring

/-! ### Constants (consistency check of Section 3.2) -/

/-- All active faces are interior: each face has one cell on each side.
This is the pure exterior-Neumann situation (no Dirichlet anchoring). -/
def AllInterior : Prop := ∀ f, ∑ K, P.inc K f = 0

/-- For a constant field, `Φ̂_K|_f = A_f c` on every face of `K`. -/
lemma amp_const (c : ℝ) (K : C) (f : F) (hKf : P.inc K f ≠ 0) :
    P.amp (const c) K f = P.A f * c := by
  unfold amp
  by_cases hK : K ∈ Set.range P.ι
  · obtain ⟨i, rfl⟩ := hK
    rw [P.γext_ι]; simp; ring
  · rw [P.γext_of_not_mem _ _ hK, P.uncut_B K f hK hKf]; simp

/-- The full discrete gradient preserves constants exactly, whatever the truncation error. -/
theorem grad_const (hP : P.AllInterior) (c : ℝ) (f : F) : P.grad (const c) f = 0 := by
  unfold grad
  have : ∑ K, P.inc K f * P.amp (const c) K f = ∑ K, P.inc K f * (P.A f * c) := by
    refine Finset.sum_congr rfl fun K _ => ?_
    by_cases h : P.inc K f = 0
    · simp [h]
    · rw [P.amp_const c K f h]
  rw [this, ← Finset.sum_mul, hP f]; simp

/-! ### The discrete Green identity (eq. green-sbp) -/

/-- The weighted face inner product `(Q, G)_W = ∑_f W_f Q_f G_f` (eq. dd-inner-products). -/
def innerW (Q G : F → ℝ) : ℝ := ∑ f, P.W f * Q f * G f

/-- **Discrete Green identity** (eq. green-sbp, Section 3.4), with no exterior residual:

`∑_K Φ^ω_K V_K div_K(B,Q) − ∑_{K∈𝓘_γ} Φ^γ_K V_K div^γ_K(A,B,Q) = −(Q, G[Φ^ω,Φ^γ])_W`.

The proof is the one of the article: collect, for each face `f`, the coefficient of
`Q_f` on the left; it is `−∑_K inc(K,f) Φ̂_K|_f = −W_f G_f` by the telescopic identity. -/
theorem green (Φ : Field C I) (Q : F → ℝ) :
    ∑ K, Φ.ω K * P.divFull Q K - ∑ i, Φ.γ i * P.divIface Q (P.ι i)
      = -P.innerW Q (P.grad Φ) := by
  -- put the interface sum back on all cells (it vanishes on uncut cells)
  rw [← P.sum_γext_mul Φ.γ (P.divIface Q)]
  unfold divFull divIface innerW
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  -- now compare face by face
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [show P.W f * Q f * P.grad Φ f = Q f * (P.W f * P.grad Φ f) by ring,
    P.W_mul_grad, mul_neg, neg_neg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  unfold amp; ring

end Phase

end CutCell

end
