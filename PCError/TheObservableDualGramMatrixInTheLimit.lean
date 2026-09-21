/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import PCError.Attr
public import PCError.Defs.TheFactorModelAndItsDerivedMatrices
public import PCError.MatrixPreliminaries
public import PCError.SLLN.Basic
public import PCError.Weyl.Basic

/-!
# The observable dual Gram matrix in the limit

The asymptotics of the observable dual Gram matrix `W⁽ᵖ⁾ = (np)⁻¹(Y⁽ᵖ⁾)ᵀY⁽ᵖ⁾`: its almost-sure
limit `W = W₀ + (δ²/n)Iₙ`, the spectrum of that limit, and the consequences for the ordered
eigenvalues `θ⁽ᵖ⁾₁ ≥ ⋯ ≥ θ⁽ᵖ⁾ₙ` of `W⁽ᵖ⁾`, for the average bulk eigenvalue `ℓ⁽ᵖ⁾`, and for the
eigenvectors at the `k` systematic eigenvalues.

## Main statements

* `PCError.ae_tendsto_weighted_sum_div_sqrt`: *specific-return concentration* — for independent
  mean-zero variables with a uniform fourth-moment bound and deterministic weight vectors of
  Euclidean norm at most one, `p^(-1/2) ∑_{i<p} a⁽ᵖ⁾ᵢXᵢ → 0` almost surely.
* `PCError.FactorModelSeq.ae_tendsto_transpose_b_mul_noiseMatrix`,
  `PCError.FactorModelSeq.ae_tendsto_frobenius_norm_proj_noiseMatrix`: *projected-noise
  decoherence* — almost surely `p^(-1/2)(b⁽ᵖ⁾)ᵀZ⁽ᵖ⁾ → 0` in the fixed space `ℝ^{k×n}`, and
  consequently `‖Π Z⁽ᵖ⁾‖_F = o(√p)` for the systematic projector `Π = b⁽ᵖ⁾(b⁽ᵖ⁾)ᵀ`.
* `PCError.FactorModelSeq.ae_tendsto_gram_noiseMatrix`: *the noise Gram in the limit* — almost
  surely `(np)⁻¹(Z⁽ᵖ⁾)ᵀZ⁽ᵖ⁾ → (δ²/n)Iₙ`.
* `PCError.FactorModelSeq.eigenvalues₀_dualGramLim₀`,
  `PCError.FactorModelSeq.eigenvalues₀_dualGramLim`,
  `PCError.FactorModelSeq.mulVec_dualGramLim_eq_smul_iff`: *the spectrum of `W`* — the ordered
  eigenvalues of `W₀` are `λ₁ > ⋯ > λₖ > 0` followed by `n - k` zeros, those of `W` are the same
  shifted by `δ²/n`, and `W` and `W₀` have the same eigenvectors.
* `PCError.FactorModelSeq.ae_tendsto_dualGram`: *convergence of the dual Gram* — almost surely
  `W⁽ᵖ⁾ → W`.
* `PCError.FactorModelSeq.ae_tendsto_dualEigenvalues`,
  `PCError.FactorModelSeq.lam_add_div_pos`: almost surely `θ⁽ᵖ⁾ⱼ → λⱼ + δ²/n > 0` for `j ≤ k`.
* `PCError.FactorModelSeq.ae_tendsto_avgBulkEigenvalue`: almost surely `ℓ⁽ᵖ⁾ → δ²/n`.
* `PCError.FactorModelSeq.ae_tendsto_abs_inner_dualEigenvector`: almost surely the unit
  eigenvectors of `W⁽ᵖ⁾` at `θ⁽ᵖ⁾ⱼ` have `|⟪w⁽ᵖ⁾ⱼ, wⱼ⟫| → 1`.

## Implementation notes

The weight family `p^(-1/2)a⁽ᵖ⁾` of `PCError.ae_tendsto_weighted_sum_div_sqrt` is indexed as
`a : ℕ → ℕ → ℝ`, the vector `a⁽ᵖ⁾ ∈ ℝ^p` being `fun i => a p i` on `Finset.range p`; the hypothesis
is `∑_{i<p}(a⁽ᵖ⁾ᵢ)² ≤ 1` rather than `= 1`, which is what the proof uses and what lets the lemma be
applied to a family of frames constrained only for `p ≥ k`, as in
`PCError.FactorModelSeq.frameWeight`.

Sizes that grow with `p` cannot converge entrywise, so the projected noise appears twice: once in
the fixed space `ℝ^{k×n}`, where convergence is the entrywise one, and once through its Frobenius
norm, for which `Matrix.frobeniusNormedAddCommGroup` is installed as a local instance exactly as
`Matrix.instL2OpNormedAddCommGroup` is in `PCError.External`.

The ordered eigenvalues of a limit are read off through `Matrix.IsHermitian.eigenvalues₀`, indexed
by `Fin (Fintype.card (Fin n))`; `PCError.FactorModelSeq.dualEigenvalues` is that listing
reindexed by `Fin n`, so the statements below about `θ⁽ᵖ⁾` carry the same `Fin.cast` as the
definition does.  The two consequences of Weyl's inequality
`PCError.WeylPerturbation` that the limit theorems consume are isolated as
`PCError.tendsto_eigenvalues₀` and `PCError.eventually_eq_eigenvalues₀`: each ordered eigenvalue is
continuous along a convergent sequence of real symmetric matrices, and an eigenvalue sequence
converging to a *simple* eigenvalue of the limit is eventually the ordered eigenvalue sitting at
that place.
-/

@[expose] public section

namespace PCError

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace

universe u

/-! ### Entrywise convergence and the matrix operations -/

/-- Entrywise convergence of matrices is compatible with matrix multiplication: for a fixed inner
index type, multiplication is a continuous bilinear map. -/
theorem tendsto_matrix_mul {m n r ι R : Type*} [Fintype n] [Mul R] [AddCommMonoid R]
    [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R] {l : Filter ι}
    {A : ι → Matrix m n R} {B : ι → Matrix n r R} {A₀ : Matrix m n R} {B₀ : Matrix n r R}
    (hA : Tendsto A l (𝓝 A₀)) (hB : Tendsto B l (𝓝 B₀)) :
    Tendsto (fun i => A i * B i) l (𝓝 (A₀ * B₀)) :=
  ((continuous_fst.matrix_mul continuous_snd).tendsto (A₀, B₀)).comp (hA.prodMk_nhds hB)

/-- Entrywise convergence of matrices is compatible with transposition. -/
theorem tendsto_matrix_transpose {m n ι R : Type*} [TopologicalSpace R] {l : Filter ι}
    {A : ι → Matrix m n R} {A₀ : Matrix m n R} (hA : Tendsto A l (𝓝 A₀)) :
    Tendsto (fun i => (A i)ᵀ) l (𝓝 A₀ᵀ) :=
  (continuous_id.matrix_transpose.tendsto A₀).comp hA

/-! ### Perturbation of the ordered eigenvalues -/

section Weyl

attribute [local instance] Matrix.instL2OpNormedAddCommGroup

variable {m : Type u} [Fintype m] [DecidableEq m] {A : ℕ → Matrix m m ℝ} {A₀ : Matrix m m ℝ}

/-- Each ordered eigenvalue is continuous along a convergent sequence of real symmetric
matrices: an immediate consequence of Weyl's inequality. -/
theorem tendsto_eigenvalues₀ (hA : ∀ p, (A p).IsHermitian) (hA₀ : A₀.IsHermitian)
    (hconv : Tendsto A atTop (𝓝 A₀)) (i : Fin (Fintype.card m)) :
    Tendsto (fun p => (hA p).eigenvalues₀ i) atTop (𝓝 (hA₀.eigenvalues₀ i)) := by
  refine tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero (fun p => dist_nonneg) (fun p => ?_) (tendsto_l2_opNorm_sub_zero hconv))
  rw [Real.dist_eq]
  exact weylPerturbation.{u} hA₀ (hA p) i

/-- An eigenvalue of `A p` converging to a *simple* eigenvalue `ζ` of the limit `A₀` is eventually
the eigenvalue Weyl's inequality keeps at the same place in the ordered listing.  Simplicity is
spelled out as `ζ` occurring exactly once, at `i₀`, in the ordered listing of `A₀`. -/
theorem eventually_eq_eigenvalues₀ (hA : ∀ p, (A p).IsHermitian) (hA₀ : A₀.IsHermitian)
    (hconv : Tendsto A atTop (𝓝 A₀)) {ζ : ℝ} {i₀ : Fin (Fintype.card m)}
    (huniq : ∀ i, hA₀.eigenvalues₀ i = ζ → i = i₀)
    {x : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 ζ))
    (hxspec : ∀ᶠ p in atTop, ∃ v : EuclideanSpace ℝ m, v ≠ 0 ∧ A p *ᵥ v = x p • v) :
    ∀ᶠ p in atTop, x p = (hA p).eigenvalues₀ i₀ := by
  obtain ⟨γ, hγpos, hgap⟩ := exists_pos_two_mul_le_abs_sub (c := hA₀.eigenvalues₀) huniq
  have hweyl' : ∀ p j, |(hA p).eigenvalues₀ j - hA₀.eigenvalues₀ j| ≤ ‖A p - A₀‖ :=
    fun p => weylPerturbation.{u} hA₀ (hA p)
  have hev : ∀ᶠ p in atTop, ‖A p - A₀‖ < γ :=
    (tendsto_l2_opNorm_sub_zero hconv).eventually_lt_const hγpos
  have hxnear : ∀ᶠ p in atTop, |x p - ζ| < γ := by
    simpa using hx.eventually (eventually_abs_sub_lt ζ hγpos)
  filter_upwards [hev, hxnear, hxspec] with p h1 h2 h3
  obtain ⟨v, hv0, hv⟩ := h3
  refine eq_eigenvalues₀_of_abs_sub_lt (hA p) (fun j hj => ?_) h2 hv0 hv
  have t := abs_sub_le (hA₀.eigenvalues₀ j) ((hA p).eigenvalues₀ j) ζ
  rw [abs_sub_comm (hA₀.eigenvalues₀ j) ((hA p).eigenvalues₀ j)] at t
  linarith [hgap j hj, hweyl' p j]

end Weyl

/-! ### Specific-return concentration -/

section Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A mixed monomial of total degree at most four is dominated by the fourth powers of its two
factors: `|x|ᵃ|y|ᵇ ≤ max (1, |x|, |y|)⁴ ≤ 1 + |x|⁴ + |y|⁴` when `a + b ≤ 4`. -/
private theorem norm_pow_mul_pow_le {x y : ℝ} {a b : ℕ} (hab : a + b ≤ 4) :
    ‖x ^ a * y ^ b‖ ≤ 1 + ‖x‖ ^ 4 + ‖y‖ ^ 4 := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow]
  set m := max 1 (max |x| |y|) with hm
  have hx : |x| ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hy : |y| ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hax : (0 : ℝ) ≤ |x| ^ 4 := by positivity
  have hay : (0 : ℝ) ≤ |y| ^ 4 := by positivity
  calc |x| ^ a * |y| ^ b ≤ m ^ a * m ^ b := by gcongr
    _ ≤ m ^ 4 := by
        rw [← pow_add]
        exact pow_le_pow_right₀ (le_max_left _ _) hab
    _ ≤ 1 + |x| ^ 4 + |y| ^ 4 := by
        rcases max_choice (1 : ℝ) (max |x| |y|) with h | h
        · rw [hm, h]
          linarith
        · rcases max_choice |x| |y| with h' | h' <;> rw [hm, h, h'] <;> linarith

/-- Hölder for the mixed monomials of total degree at most four: on a probability space, two
functions in `L⁴` have `fᵃgᵇ` integrable whenever `a + b ≤ 4`. -/
private theorem integrable_pow_mul_pow {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ)
    {a b : ℕ} (hab : a + b ≤ 4) : Integrable (fun ω => f ω ^ a * g ω ^ b) μ := by
  refine Integrable.mono' (g := fun ω => 1 + ‖f ω‖ ^ 4 + ‖g ω‖ ^ 4)
    (((integrable_const (1 : ℝ)).add (hf.integrable_norm_pow' (p := 4))).add
      (hg.integrable_norm_pow' (p := 4)))
    ((hf.aestronglyMeasurable.pow a).mul (hg.aestronglyMeasurable.pow b)) ?_
  filter_upwards with ω
  exact norm_pow_mul_pow_le hab

/-- Hölder's exponent triple `4⁻¹ + 4⁻¹ = 2⁻¹`, which makes a product of two `L⁴` functions
`L²`. -/
private instance : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [← two_mul, show (4 : ENNReal) = 2 * 2 from by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩

/-- The variance of a product of two `L⁴` variables is at most any common bound on their fourth
moments, by the pointwise `(xy)² ≤ (x⁴ + y⁴)/2`. -/
private theorem variance_mul_le {X Y : Ω → ℝ} (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hXY : MemLp (fun ω => X ω * Y ω) 2 μ) {C : ℝ} (hCX : μ[fun ω => X ω ^ 4] ≤ C)
    (hCY : μ[fun ω => Y ω ^ 4] ≤ C) : Var[fun ω => X ω * Y ω; μ] ≤ C := by
  have hX4 : Integrable (fun ω => X ω ^ 4) μ := by
    simpa using integrable_pow_mul_pow hX hX (a := 4) (b := 0) (by norm_num)
  have hY4 : Integrable (fun ω => Y ω ^ 4) μ := by
    simpa using integrable_pow_mul_pow hY hY (a := 4) (b := 0) (by norm_num)
  have h1 := variance_le_expectation_sq (μ := μ) hXY.aestronglyMeasurable
  have h2 : ∫ ω, ((fun ω => X ω * Y ω) ^ 2) ω ∂μ ≤ ∫ ω, (X ω ^ 4 + Y ω ^ 4) / 2 ∂μ := by
    refine integral_mono (hXY.integrable_sq.congr (Filter.Eventually.of_forall fun ω => by simp))
      ((hX4.add hY4).div_const 2) fun ω => ?_
    simp only [Pi.pow_apply]
    nlinarith [sq_nonneg (X ω ^ 2 - Y ω ^ 2), sq_nonneg (X ω * Y ω)]
  have h3 : ∫ ω, (X ω ^ 4 + Y ω ^ 4) / 2 ∂μ ≤ C := by
    rw [integral_div, integral_add hX4 hY4]
    have e1 : ∫ ω, X ω ^ 4 ∂μ ≤ C := hCX
    have e2 : ∫ ω, Y ω ^ 4 ∂μ ≤ C := hCY
    linarith
  linarith

/-- The second moment of a sum of two *independent* centred variables: independence and
`E[S] = E[W] = 0` kill the cross term, leaving `E[(S + W)²] = E[S²] + E[W²]`. -/
private theorem integral_sq_add {S W : Ω → ℝ} (hSW : IndepFun S W μ)
    (hS : MemLp S 4 μ) (hW : MemLp W 4 μ) (hS0 : μ[S] = 0) (hW0 : μ[W] = 0) :
    μ[fun ω => (S ω + W ω) ^ 2] = μ[fun ω => S ω ^ 2] + μ[fun ω => W ω ^ 2] := by
  have iS2 : Integrable (fun ω => S ω ^ 2) μ := by
    simpa using integrable_pow_mul_pow hS hW (a := 2) (b := 0) (by norm_num)
  have iW2 : Integrable (fun ω => W ω ^ 2) μ := by
    simpa using integrable_pow_mul_pow hS hW (a := 0) (b := 2) (by norm_num)
  have i11 : Integrable (fun ω => S ω * W ω) μ := by
    simpa using integrable_pow_mul_pow hS hW (a := 1) (b := 1) (by norm_num)
  have p11 : μ[fun ω => S ω * W ω] = μ[S] * μ[W] :=
    hSW.integral_fun_mul_eq_mul_integral hS.aestronglyMeasurable hW.aestronglyMeasurable
  have he : (fun ω => (S ω + W ω) ^ 2)
      = fun ω => S ω ^ 2 + (2 * (S ω * W ω) + W ω ^ 2) := by funext ω; ring
  have iA : Integrable (fun ω => 2 * (S ω * W ω) + W ω ^ 2) μ := (i11.const_mul 2).add iW2
  rw [he, integral_add iS2 iA, integral_add (i11.const_mul 2) iW2, integral_const_mul, p11,
    hS0, hW0]
  ring

/-- The fourth moment of a sum of two *independent* centred variables: independence and
`E[S] = E[W] = 0` kill every odd-power cross term, leaving
`E[(S + W)⁴] = E[S⁴] + 6E[S²]E[W²] + E[W⁴]`. -/
private theorem integral_fourth_add {S W : Ω → ℝ} (hSW : IndepFun S W μ)
    (hS : MemLp S 4 μ) (hW : MemLp W 4 μ) (hS0 : μ[S] = 0) (hW0 : μ[W] = 0) :
    μ[fun ω => (S ω + W ω) ^ 4] = μ[fun ω => S ω ^ 4]
      + 6 * (μ[fun ω => S ω ^ 2] * μ[fun ω => W ω ^ 2]) + μ[fun ω => W ω ^ 4] := by
  have iS4 : Integrable (fun ω => S ω ^ 4) μ := by
    simpa using integrable_pow_mul_pow hS hW (a := 4) (b := 0) (by norm_num)
  have iW4 : Integrable (fun ω => W ω ^ 4) μ := by
    simpa using integrable_pow_mul_pow hS hW (a := 0) (b := 4) (by norm_num)
  have i31 : Integrable (fun ω => S ω ^ 3 * W ω) μ := by
    simpa using integrable_pow_mul_pow hS hW (a := 3) (b := 1) (by norm_num)
  have i22 : Integrable (fun ω => S ω ^ 2 * W ω ^ 2) μ :=
    integrable_pow_mul_pow hS hW (a := 2) (b := 2) (by norm_num)
  have i13 : Integrable (fun ω => S ω * W ω ^ 3) μ := by
    simpa using integrable_pow_mul_pow hS hW (a := 1) (b := 3) (by norm_num)
  have p31 : μ[fun ω => S ω ^ 3 * W ω] = μ[fun ω => S ω ^ 3] * μ[W] :=
    (hSW.comp (φ := fun x : ℝ => x ^ 3) (ψ := fun x : ℝ => x)
      (measurable_id.pow_const 3) measurable_id).integral_fun_mul_eq_mul_integral
      (hS.aestronglyMeasurable.pow 3) hW.aestronglyMeasurable
  have p22 : μ[fun ω => S ω ^ 2 * W ω ^ 2] = μ[fun ω => S ω ^ 2] * μ[fun ω => W ω ^ 2] :=
    (hSW.comp (φ := fun x : ℝ => x ^ 2) (ψ := fun x : ℝ => x ^ 2)
      (measurable_id.pow_const 2) (measurable_id.pow_const 2)).integral_fun_mul_eq_mul_integral
      (hS.aestronglyMeasurable.pow 2) (hW.aestronglyMeasurable.pow 2)
  have p13 : μ[fun ω => S ω * W ω ^ 3] = μ[S] * μ[fun ω => W ω ^ 3] :=
    (hSW.comp (φ := fun x : ℝ => x) (ψ := fun x : ℝ => x ^ 3)
      measurable_id (measurable_id.pow_const 3)).integral_fun_mul_eq_mul_integral
      hS.aestronglyMeasurable (hW.aestronglyMeasurable.pow 3)
  have he : (fun ω => (S ω + W ω) ^ 4)
      = fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * W ω)
        + (6 * (S ω ^ 2 * W ω ^ 2) + (4 * (S ω * W ω ^ 3) + W ω ^ 4))) := by funext ω; ring
  have iD : Integrable (fun ω => 4 * (S ω * W ω ^ 3) + W ω ^ 4) μ := (i13.const_mul 4).add iW4
  have iC : Integrable (fun ω => 6 * (S ω ^ 2 * W ω ^ 2)
      + (4 * (S ω * W ω ^ 3) + W ω ^ 4)) μ := (i22.const_mul 6).add iD
  have iB : Integrable (fun ω => 4 * (S ω ^ 3 * W ω) + (6 * (S ω ^ 2 * W ω ^ 2)
      + (4 * (S ω * W ω ^ 3) + W ω ^ 4))) μ := (i31.const_mul 4).add iC
  rw [he, integral_add iS4 iB, integral_add (i31.const_mul 4) iC,
    integral_add (i22.const_mul 6) iD, integral_add (i13.const_mul 4) iW4,
    integral_const_mul, integral_const_mul, integral_const_mul, p31, p22, p13, hS0, hW0]
  ring

/-- The two moment bounds for a finite sum of independent centred variables, proved together by
induction on the index set: if `E[Yᵢ²] ≤ vᵢ` and `E[Yᵢ⁴] ≤ K vᵢ²` then
`E[(∑ Yᵢ)²] ≤ ∑ vᵢ` and `E[(∑ Yᵢ)⁴] ≤ (K + 3)(∑ vᵢ)²`.

The fourth-moment step is the paper's computation: adding one summand contributes
`6E[S²]E[W²] + E[W⁴] ≤ 6(∑ v)vⱼ + K vⱼ²`, which the slack in `(K + 3)(∑ v + vⱼ)²` absorbs. -/
private theorem integral_sq_and_fourth_sum_le {Y : ℕ → Ω → ℝ} (hL4 : ∀ i, MemLp (Y i) 4 μ)
    (hmean : ∀ i, μ[Y i] = 0)
    (hstep : ∀ (s : Finset ℕ) (j : ℕ), j ∉ s → IndepFun (fun ω => ∑ i ∈ s, Y i ω) (Y j) μ)
    (hSmemLp : ∀ s : Finset ℕ, MemLp (fun ω => ∑ i ∈ s, Y i ω) 4 μ)
    (hSmean : ∀ s : Finset ℕ, μ[fun ω => ∑ i ∈ s, Y i ω] = 0)
    {v : ℕ → ℝ} (hv0 : ∀ i, 0 ≤ v i) (hsq : ∀ i, μ[fun ω => Y i ω ^ 2] ≤ v i)
    {K : ℝ} (hK0 : 0 ≤ K) (hfour : ∀ i, μ[fun ω => Y i ω ^ 4] ≤ K * v i ^ 2) (s : Finset ℕ) :
    μ[fun ω => (∑ i ∈ s, Y i ω) ^ 2] ≤ ∑ i ∈ s, v i ∧
      μ[fun ω => (∑ i ∈ s, Y i ω) ^ 4] ≤ (K + 3) * (∑ i ∈ s, v i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    obtain ⟨ih2, ih4⟩ := ih
    have hsum : ∀ ω, ∑ i ∈ insert j s, Y i ω = (∑ i ∈ s, Y i ω) + Y j ω := by
      intro ω; rw [Finset.sum_insert hj]; ring
    have hks2 := integral_sq_add (hstep s j hj) (hSmemLp s) (hL4 j) (hSmean s) (hmean j)
    have hks4 := integral_fourth_add (hstep s j hj) (hSmemLp s) (hL4 j) (hSmean s) (hmean j)
    have e2 : μ[fun ω => (∑ i ∈ insert j s, Y i ω) ^ 2]
        = μ[fun ω => (∑ i ∈ s, Y i ω) ^ 2] + μ[fun ω => Y j ω ^ 2] := by
      rw [← hks2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hsum])
    have e4 : μ[fun ω => (∑ i ∈ insert j s, Y i ω) ^ 4]
        = μ[fun ω => (∑ i ∈ s, Y i ω) ^ 4]
          + 6 * (μ[fun ω => (∑ i ∈ s, Y i ω) ^ 2] * μ[fun ω => Y j ω ^ 2])
          + μ[fun ω => Y j ω ^ 4] := by
      rw [← hks4]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hsum])
    have hT0 : (0 : ℝ) ≤ ∑ i ∈ s, v i := Finset.sum_nonneg fun i _ => hv0 i
    have hm2W : (0 : ℝ) ≤ μ[fun ω => Y j ω ^ 2] := integral_nonneg fun ω => by positivity
    have hprod : μ[fun ω => (∑ i ∈ s, Y i ω) ^ 2] * μ[fun ω => Y j ω ^ 2]
        ≤ (∑ i ∈ s, v i) * v j := mul_le_mul ih2 (hsq j) hm2W hT0
    rw [Finset.sum_insert hj]
    refine ⟨by rw [e2]; linarith [hsq j], ?_⟩
    rw [e4]
    nlinarith [hfour j, hv0 j, mul_nonneg hK0 (mul_nonneg hT0 (hv0 j)),
      mul_nonneg hK0 (mul_nonneg (hv0 j) (hv0 j)), mul_nonneg hT0 (hv0 j)]

/-- The uniform fourth-moment bound of the paper: along a weight vector with `∑ cᵢ² ≤ 1`,
`E[(∑ cᵢXᵢ)⁴] ≤ κ₄ + 3d̄⁴`, where `κ₄` bounds the fourth moments and `d̄²` the second ones.

Applying `PCError.integral_sq_and_fourth_sum_le` to `Yᵢ = cᵢXᵢ` with `vᵢ = cᵢ²d` and
`K = κ/d²` turns its conclusion into `(κ/d² + 3)(d ∑ cᵢ²)² ≤ κ + 3d²`. -/
private theorem integral_fourth_weighted_sum_le {X : ℕ → Ω → ℝ} (hmeasX : ∀ i, Measurable (X i))
    (hX : ∀ i, MemLp (X i) 4 μ) (hindep : iIndepFun X μ) (hmean : ∀ i, μ[X i] = 0)
    {κ d : ℝ} (hκ0 : 0 ≤ κ) (hd0 : 0 < d) (hκ : ∀ i, μ[fun ω => X i ω ^ 4] ≤ κ)
    (hd : ∀ i, μ[fun ω => X i ω ^ 2] ≤ d) (c : ℕ → ℝ) (s : Finset ℕ)
    (hc : ∑ i ∈ s, c i ^ 2 ≤ 1) :
    μ[fun ω => (∑ i ∈ s, c i * X i ω) ^ 4] ≤ κ + 3 * d ^ 2 := by
  have hY : ∀ i, MemLp (fun ω => c i * X i ω) 4 μ := fun i => (hX i).const_mul (c i)
  have hYmeas : ∀ i, Measurable (fun ω => c i * X i ω) := fun i => (hmeasX i).const_mul (c i)
  have hYindep : iIndepFun (fun i ω => c i * X i ω) μ :=
    hindep.comp (fun i x => c i * x) (fun i => measurable_id.const_mul (c i))
  have hSmemLp : ∀ t : Finset ℕ, MemLp (fun ω => ∑ i ∈ t, c i * X i ω) 4 μ :=
    fun t => memLp_finsetSum t (fun i _ => hY i)
  have hYmean : ∀ i, μ[fun ω => c i * X i ω] = 0 := by
    intro i; rw [integral_const_mul, hmean i, mul_zero]
  have hSmean : ∀ t : Finset ℕ, μ[fun ω => ∑ i ∈ t, c i * X i ω] = 0 := by
    intro t
    rw [integral_finsetSum t (fun i _ => ((hX i).integrable (by norm_num)).const_mul (c i))]
    simp [integral_const_mul, hmean]
  have hstep : ∀ (t : Finset ℕ) (j : ℕ), j ∉ t →
      IndepFun (fun ω => ∑ i ∈ t, c i * X i ω) (fun ω => c j * X j ω) μ := by
    intro t j hj
    refine (hYindep.indepFun_finsetSum_of_notMem hYmeas hj).congr
      (Filter.Eventually.of_forall fun ω => ?_) (Filter.Eventually.of_forall fun ω => rfl)
    simp
  have hsq : ∀ i, μ[fun ω => (c i * X i ω) ^ 2] ≤ c i ^ 2 * d := by
    intro i
    have e : μ[fun ω => (c i * X i ω) ^ 2] = c i ^ 2 * μ[fun ω => X i ω ^ 2] := by
      simp only [mul_pow]; rw [integral_const_mul]
    rw [e]
    exact mul_le_mul_of_nonneg_left (hd i) (sq_nonneg _)
  have hfour : ∀ i, μ[fun ω => (c i * X i ω) ^ 4] ≤ (κ / d ^ 2) * (c i ^ 2 * d) ^ 2 := by
    intro i
    have e : μ[fun ω => (c i * X i ω) ^ 4] = c i ^ 4 * μ[fun ω => X i ω ^ 4] := by
      simp only [mul_pow]; rw [integral_const_mul]
    have e2 : (κ / d ^ 2) * (c i ^ 2 * d) ^ 2 = c i ^ 4 * κ := by field_simp
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left (hκ i) (by positivity)
  have hmb := (integral_sq_and_fourth_sum_le hY hYmean hstep hSmemLp hSmean
    (v := fun i => c i ^ 2 * d) (fun i => by positivity) hsq
    (K := κ / d ^ 2) (by positivity) hfour s).2
  have hsum : ∑ i ∈ s, c i ^ 2 * d = (∑ i ∈ s, c i ^ 2) * d := by rw [← Finset.sum_mul]
  rw [hsum] at hmb
  have hT0 : (0 : ℝ) ≤ ∑ i ∈ s, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfinal : (κ / d ^ 2 + 3) * ((∑ i ∈ s, c i ^ 2) * d) ^ 2 ≤ κ + 3 * d ^ 2 := by
    have hsq1 : (∑ i ∈ s, c i ^ 2) ^ 2 ≤ 1 := by nlinarith
    have e : (κ / d ^ 2 + 3) * ((∑ i ∈ s, c i ^ 2) * d) ^ 2
        = ((κ / d ^ 2 + 3) * d ^ 2) * (∑ i ∈ s, c i ^ 2) ^ 2 := by ring
    have e2 : (κ / d ^ 2 + 3) * d ^ 2 = κ + 3 * d ^ 2 := by field_simp
    rw [e, e2]
    nlinarith [hκ0, sq_nonneg d]
  linarith

/-- **Markov's inequality at the fourth power**: a variable whose fourth moment is at most `C`
has `μ{|g| > t} ≤ C/t⁴` for every `t > 0`. -/
private theorem measure_lt_abs_le_of_integral_fourth_le {g : Ω → ℝ} {C t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun ω => g ω ^ 4) μ) (hC : μ[fun ω => g ω ^ 4] ≤ C) :
    μ {ω | t < |g ω|} ≤ ENNReal.ofReal (C / t ^ 4) := by
  calc μ {ω | t < |g ω|} ≤ μ {ω | t ^ 4 ≤ g ω ^ 4} := measure_mono fun ω hω => by
        have h := pow_le_pow_left₀ ht.le hω.le 4
        rwa [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ g ω ^ 4)] at h
    _ = ENNReal.ofReal (μ.real {ω | t ^ 4 ≤ g ω ^ 4}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    _ ≤ ENNReal.ofReal (C / t ^ 4) := ENNReal.ofReal_le_ofReal <| by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < t ^ 4), mul_comm]
        exact (mul_meas_ge_le_integral_of_nonneg (f := fun ω => g ω ^ 4)
          (ae_of_all μ fun ω => by positivity) hint (t ^ 4)).trans hC

/-- A sequence eventually bounded by `ε√p` for every `ε` of the form `1/(m+1)` satisfies
`p^(-1/2)gₚ → 0`. -/
private theorem tendsto_div_sqrt_of_eventually_abs_le {g : ℕ → ℝ}
    (h : ∀ m : ℕ, ∀ᶠ p in atTop, |g p| ≤ 1 / ((m : ℝ) + 1) * Real.sqrt p) :
    Tendsto (fun p : ℕ => (Real.sqrt p)⁻¹ * g p) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h m)
  refine ⟨max N 1, fun p hp => ?_⟩
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast (le_max_right N 1).trans hp)
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg (inv_nonneg.2 hs.le), inv_mul_eq_div,
    div_lt_iff₀ hs]
  exact (hN p ((le_max_left _ _).trans hp)).trans_lt (mul_lt_mul_of_pos_right hm hs)

/-- Markov and Borel–Cantelli: a sequence of variables whose fourth moments are bounded by a
single constant `C`, and which vanishes at `p = 0`, satisfies `p^(-1/2)fₚ → 0` almost surely.

For `ε = 1/(m+1)`, Markov applied to `fₚ⁴` gives `μ{|fₚ| > ε√p} ≤ C/(ε⁴p²)`, summable in `p`, so
by Borel–Cantelli almost surely `|fₚ| ≤ ε√p` eventually; intersecting the countably many
almost-sure events over `m` gives the limit. -/
private theorem ae_tendsto_div_sqrt_of_integral_fourth_le {f : ℕ → Ω → ℝ} (hf0 : ∀ ω, f 0 ω = 0)
    {C : ℝ} (hint : ∀ p, Integrable (fun ω => f p ω ^ 4) μ)
    (hC : ∀ p, μ[fun ω => f p ω ^ 4] ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (Real.sqrt p)⁻¹ * f p ω) atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := le_trans (integral_nonneg fun ω => by positivity) (hC 0)
  have key : ∀ m : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ p in atTop,
      |f p ω| ≤ 1 / ((m : ℝ) + 1) * Real.sqrt p := by
    intro m
    set ε : ℝ := 1 / ((m : ℝ) + 1) with hεdef
    have hε : 0 < ε := by positivity
    have hbound : ∀ p : ℕ, μ {ω | ε * Real.sqrt p < |f p ω|}
        ≤ ENNReal.ofReal (C / ε ^ 4 * (1 / (p : ℝ) ^ 2)) := by
      intro p
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp [hf0]
      · have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
        have hsq : Real.sqrt p ^ 4 = (p : ℝ) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hpR.le]
        have he : C / (ε * Real.sqrt p) ^ 4 = C / ε ^ 4 * (1 / (p : ℝ) ^ 2) := by
          rw [mul_pow, hsq, mul_one_div, div_div]
        exact (measure_lt_abs_le_of_integral_fourth_le
          (mul_pos hε (Real.sqrt_pos.2 hpR)) (hint p) (hC p)).trans
          (le_of_eq (congrArg ENNReal.ofReal he))
    have hsum : ∑' p : ℕ, μ {ω | ε * Real.sqrt p < |f p ω|} ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top
        (r := ∑' p : ℕ, C / ε ^ 4 * (1 / (p : ℝ) ^ 2))) ?_
      rw [ENNReal.ofReal_tsum_of_nonneg (fun p => by positivity)
        ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left _)]
      exact ENNReal.tsum_le_tsum hbound
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    filter_upwards [hω] with p hp
    exact le_of_not_gt hp
  filter_upwards [ae_all_iff.2 key] with ω hω
  exact tendsto_div_sqrt_of_eventually_abs_le hω

/-- **Specific-return concentration** for a family of *measurable* variables.

`κ₄` is the supremum of the fourth moments, finite by hypothesis, and `d̄² = 1 + κ₄` bounds the
second moments through the pointwise `x² ≤ 1 + x⁴` — a cruder constant than the paper's Jensen
bound `d̄² ≤ κ₄^(1/2)`, and all the argument needs. -/
private theorem ae_tendsto_weighted_sum_div_sqrt_of_measurable {X : ℕ → Ω → ℝ} {a : ℕ → ℕ → ℝ}
    (hmeasX : ∀ i, Measurable (X i)) (hX : ∀ i, MemLp (X i) 4 μ) (hindep : iIndepFun X μ)
    (hmean : ∀ i, μ[X i] = 0) (hbdd : BddAbove (Set.range fun i => μ[fun ω => X i ω ^ 4]))
    (ha : ∀ p, ∑ i ∈ Finset.range p, a p i ^ 2 ≤ 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (Real.sqrt p)⁻¹ * ∑ i ∈ Finset.range p, a p i * X i ω)
      atTop (𝓝 0) := by
  set κ := sSup (Set.range fun i => μ[fun ω => X i ω ^ 4]) with hκdef
  have hκ : ∀ i, μ[fun ω => X i ω ^ 4] ≤ κ := fun i => le_csSup hbdd ⟨i, rfl⟩
  have hκ0 : 0 ≤ κ := le_trans (integral_nonneg fun ω => by positivity) (hκ 0)
  have iX4 : ∀ i, Integrable (fun ω => X i ω ^ 4) μ := fun i => by
    simpa using integrable_pow_mul_pow (hX i) (hX i) (a := 4) (b := 0) (by norm_num)
  have iX2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ := fun i => by
    simpa using integrable_pow_mul_pow (hX i) (hX i) (a := 2) (b := 0) (by norm_num)
  have hd : ∀ i, μ[fun ω => X i ω ^ 2] ≤ 1 + κ := by
    intro i
    have h1 : μ[fun ω => X i ω ^ 2] ≤ μ[fun ω => 1 + X i ω ^ 4] := by
      refine integral_mono (iX2 i) ((integrable_const (1 : ℝ)).add (iX4 i)) fun ω => ?_
      nlinarith [sq_nonneg (X i ω ^ 2 - 1), sq_nonneg (X i ω)]
    have h2 : μ[fun ω => 1 + X i ω ^ 4] = 1 + μ[fun ω => X i ω ^ 4] := by
      rw [integral_add (integrable_const (1 : ℝ)) (iX4 i), integral_const]; simp
    rw [h2] at h1
    linarith [hκ i]
  have hd0 : (0 : ℝ) < 1 + κ := by linarith
  have hS : ∀ p : ℕ, MemLp (fun ω => ∑ i ∈ Finset.range p, a p i * X i ω) 4 μ :=
    fun p => memLp_finsetSum _ (fun i _ => (hX i).const_mul (a p i))
  refine ae_tendsto_div_sqrt_of_integral_fourth_le
    (f := fun p ω => ∑ i ∈ Finset.range p, a p i * X i ω) (fun ω => by simp)
    (C := κ + 3 * (1 + κ) ^ 2) (fun p => ?_) (fun p => ?_)
  · simpa using integrable_pow_mul_pow (hS p) (hS p) (a := 4) (b := 0) (by norm_num)
  · exact integral_fourth_weighted_sum_le hmeasX hX hindep hmean hκ0 hd0 hκ hd (a p) _ (ha p)

end Concentration

/-- **Specific-return concentration**. -/
@[pcerror "lem_noise_conc"]
theorem ae_tendsto_weighted_sum_div_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ} {a : ℕ → ℕ → ℝ} (hX : ∀ i, MemLp (X i) 4 μ)
    (hindep : iIndepFun X μ) (hmean : ∀ i, μ[X i] = 0)
    (hbdd : BddAbove (Set.range fun i => μ[fun ω => X i ω ^ 4]))
    (ha : ∀ p, ∑ i ∈ Finset.range p, a p i ^ 2 ≤ 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (Real.sqrt p)⁻¹ * ∑ i ∈ Finset.range p, a p i * X i ω)
      atTop (𝓝 0) := by
  -- pass to the measurable representatives supplied by `MemLp`, which the independence of the
  -- partial sums is stated for, then transfer the conclusion back along the countably many
  -- almost-everywhere equalities
  set X' : ℕ → Ω → ℝ := fun i => (hX i).aestronglyMeasurable.mk (X i) with hX'def
  have hae : ∀ i, X i =ᵐ[μ] X' i := fun i => (hX i).aestronglyMeasurable.ae_eq_mk
  have hmeasX' : ∀ i, Measurable (X' i) := fun i =>
    (hX i).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hX' : ∀ i, MemLp (X' i) 4 μ := fun i => (memLp_congr_ae (hae i)).1 (hX i)
  have hindep' : iIndepFun X' μ := (iIndepFun_congr hae).1 hindep
  have hmean' : ∀ i, μ[X' i] = 0 := fun i => by
    rw [← integral_congr_ae (hae i)]; exact hmean i
  have hbdd' : BddAbove (Set.range fun i => μ[fun ω => X' i ω ^ 4]) := by
    have he : (fun i => μ[fun ω => X' i ω ^ 4]) = fun i => μ[fun ω => X i ω ^ 4] := by
      funext i
      exact (integral_congr_ae (by filter_upwards [hae i] with ω h; rw [h])).symm
    rw [he]; exact hbdd
  have hall : ∀ᵐ ω ∂μ, ∀ i, X i ω = X' i ω := by rw [ae_all_iff]; exact hae
  filter_upwards [hall,
    ae_tendsto_weighted_sum_div_sqrt_of_measurable hmeasX' hX' hindep' hmean' hbdd' ha] with ω h2 h1
  exact h1.congr fun p => congrArg _ (Finset.sum_congr rfl fun i _ => by rw [h2 i])

namespace FactorModelSeq

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} (M : FactorModelSeq Ω)
  {G : Matrix (Fin M.k) (Fin M.k) ℝ} {lam : Fin M.k → ℝ}

/-! ### Projected-noise decoherence -/

section ProjNoise

/-- The `j`-th column of the principal frame, extended by zero outside the frame's range and
switched off for the degenerate sizes `p < k`: the weight family that
`PCError.ae_tendsto_weighted_sum_div_sqrt` is applied to. -/
private def frameWeight (j : Fin M.k) (p i : ℕ) : ℝ :=
  if M.k ≤ p then (if hi : i < p then M.b p ⟨i, hi⟩ j else 0) else 0

omit [MeasurableSpace Ω] in
private theorem sum_frameWeight_sq_le (j : Fin M.k) (p : ℕ) :
    ∑ i ∈ Finset.range p, M.frameWeight j p i ^ 2 ≤ 1 := by
  by_cases hp : M.k ≤ p
  · have h1 : ∑ i ∈ Finset.range p, M.frameWeight j p i ^ 2
        = ∑ i : Fin p, M.b p i j * M.b p i j := by
      rw [← Fin.sum_univ_eq_sum_range fun i => M.frameWeight j p i ^ 2]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [frameWeight, ite_eq_left hp, dite_eq_left i.isLt]
      rw [sq]
    have h2 : ((M.b p)ᵀ * M.b p) j j = 1 := by
      rw [M.transpose_b_mul_b p hp]
      simp
    rw [h1]
    rw [Matrix.mul_apply] at h2
    simp only [Matrix.transpose_apply] at h2
    rw [h2]
  · simp [frameWeight, ite_eq_right hp]

/-- **Projected-noise decoherence**: under the asymptotic hypotheses, almost surely
`p^(-1/2) (b⁽ᵖ⁾)ᵀZ⁽ᵖ⁾ → 0` in `ℝ^{k×n}`.

Each of the `kn` entries is a weighted sum `∑_{i<p} b_{ij}Z_{iℓ}` along a deterministic unit
vector, so `PCError.ae_tendsto_weighted_sum_div_sqrt` applies; the index set being finite, the
intersection of the `kn` almost-sure events is almost sure. -/
@[pcerror "lem_proj_noise"]
theorem ae_tendsto_transpose_b_mul_noiseMatrix (hyp : AsymptoticHypotheses μ M G lam) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (Real.sqrt p)⁻¹ • ((M.b p)ᵀ * M.noiseMatrix p ω))
      atTop (𝓝 0) := by
  have := hyp.iIndepFun_Z.isProbabilityMeasure
  have key : ∀ (j : Fin M.k) (ℓ : Fin M.n), ∀ᵐ ω ∂μ, Tendsto
      (fun p : ℕ => (Real.sqrt p)⁻¹ * ((M.b p)ᵀ * M.noiseMatrix p ω) j ℓ) atTop (𝓝 0) := by
    intro j ℓ
    have hindep : iIndepFun (fun i : ℕ => M.Z i ℓ) μ :=
      hyp.iIndepFun_Z.precomp (g := fun i : ℕ => (i, ℓ))
        fun i₁ i₂ h => by simpa using congrArg Prod.fst h
    have hbdd : BddAbove (Set.range fun i => μ[fun ω => M.Z i ℓ ω ^ 4]) := by
      refine hyp.bddAbove_fourthMoment_Z.mono ?_
      rintro x ⟨i, rfl⟩
      exact ⟨(i, ℓ), rfl⟩
    filter_upwards [ae_tendsto_weighted_sum_div_sqrt (X := fun i => M.Z i ℓ)
      (a := M.frameWeight j) (fun i => hyp.memLp_Z i ℓ) hindep (fun i => hyp.integral_Z i ℓ)
      hbdd (M.sum_frameWeight_sq_le j)] with ω hω
    refine hω.congr' ?_
    filter_upwards [eventually_ge_atTop M.k] with p hp
    rw [Matrix.mul_apply, ← Fin.sum_univ_eq_sum_range fun i => M.frameWeight j p i * M.Z i ℓ ω]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    simp only [frameWeight, ite_eq_left hp, dite_eq_left i.isLt, Matrix.transpose_apply,
      noiseMatrix_apply]
  have hall : ∀ᵐ ω ∂μ, ∀ (j : Fin M.k) (ℓ : Fin M.n), Tendsto
      (fun p : ℕ => (Real.sqrt p)⁻¹ * ((M.b p)ᵀ * M.noiseMatrix p ω) j ℓ) atTop (𝓝 0) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    exact key j
  filter_upwards [hall] with ω hω
  exact tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun ℓ => hω j ℓ

end ProjNoise

/-! ### The Frobenius norm of the projected noise -/

section Frobenius

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The `ℝ`-valued squares in a Frobenius norm, with the real exponent turned into a natural
one. -/
private theorem sum_rpow_two_norm {s : Type*} [Fintype s] (f : s → ℝ) :
    ∑ i, ‖f i‖ ^ (2 : ℝ) = ∑ i, f i ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, ← abs_pow,
    abs_of_nonneg (sq_nonneg _)]

omit [MeasurableSpace Ω] in
/-- A matrix with orthonormal columns is an isometry for the Euclidean norm. -/
private theorem sum_sq_b_mulVec (p : ℕ) (hp : M.k ≤ p) (y : Fin M.k → ℝ) :
    ∑ i : Fin p, (M.b p *ᵥ y) i ^ 2 = ∑ j : Fin M.k, y j ^ 2 := by
  have h : (M.b p *ᵥ y) ⬝ᵥ (M.b p *ᵥ y) = y ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.transpose_transpose (M.b p),
      Matrix.vecMul_transpose, Matrix.transpose_transpose, Matrix.mulVec_mulVec,
      M.transpose_b_mul_b p hp, Matrix.one_mulVec]
  simp only [pow_two]
  simpa [dotProduct] using h

omit [MeasurableSpace Ω] in
/-- **Frobenius invariance of the projector**: `‖Π A‖ = ‖bᵀ A‖` for `Π = b bᵀ` with `b` having
orthonormal columns, since `b` is an isometry on each column. -/
private theorem frobenius_norm_b_mul (p : ℕ) (hp : M.k ≤ p) {r : Type*} [Fintype r]
    (A : Matrix (Fin p) r ℝ) : ‖M.b p * ((M.b p)ᵀ * A)‖ = ‖(M.b p)ᵀ * A‖ := by
  have key : ∀ ℓ : r, ∑ i : Fin p, ‖(M.b p * ((M.b p)ᵀ * A)) i ℓ‖ ^ (2 : ℝ)
      = ∑ j : Fin M.k, ‖((M.b p)ᵀ * A) j ℓ‖ ^ (2 : ℝ) := by
    intro ℓ
    rw [sum_rpow_two_norm, sum_rpow_two_norm]
    have h := M.sum_sq_b_mulVec p hp fun j => ((M.b p)ᵀ * A) j ℓ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
    rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have e1 : ∑ i : Fin p, ∑ ℓ : r, ‖(M.b p * ((M.b p)ᵀ * A)) i ℓ‖ ^ (2 : ℝ)
      = ∑ ℓ : r, ∑ i : Fin p, ‖(M.b p * ((M.b p)ᵀ * A)) i ℓ‖ ^ (2 : ℝ) := Finset.sum_comm
  have e2 : ∑ j : Fin M.k, ∑ ℓ : r, ‖((M.b p)ᵀ * A) j ℓ‖ ^ (2 : ℝ)
      = ∑ ℓ : r, ∑ j : Fin M.k, ‖((M.b p)ᵀ * A) j ℓ‖ ^ (2 : ℝ) := Finset.sum_comm
  rw [Matrix.frobenius_norm_def, Matrix.frobenius_norm_def, e1, e2]
  exact congrArg (· ^ (1 / 2 : ℝ)) (Finset.sum_congr rfl fun ℓ _ => key ℓ)

/-- **Projected-noise decoherence**, the consequence: almost surely
`‖Π Z⁽ᵖ⁾‖_F = o(√p)`, where `Π = b⁽ᵖ⁾(b⁽ᵖ⁾)ᵀ` is the orthogonal projector onto the systematic
subspace. -/
@[pcerror "lem_proj_noise"]
theorem ae_tendsto_frobenius_norm_proj_noiseMatrix (hyp : AsymptoticHypotheses μ M G lam) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun p : ℕ => (Real.sqrt p)⁻¹ * ‖M.b p * ((M.b p)ᵀ * M.noiseMatrix p ω)‖) atTop (𝓝 0) := by
  filter_upwards [M.ae_tendsto_transpose_b_mul_noiseMatrix hyp] with ω hω
  have h1 : Tendsto (fun p : ℕ => ‖(Real.sqrt p)⁻¹ • ((M.b p)ᵀ * M.noiseMatrix p ω)‖)
      atTop (𝓝 0) := by simpa using hω.norm
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop M.k] with p hp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt p)⁻¹),
    M.frobenius_norm_b_mul p hp]

end Frobenius

/-! ### The noise Gram in the limit -/

section NoiseGram

/-- **Grouping an independent family into rows**: a family of real random variables indexed by
pairs `(i, j)` with `j` ranging over a finite type is, read as the family of `κ`-tuples
`i ↦ (X_{i,j})ⱼ`, again independent.

Mathlib has the converse direction (`ProbabilityTheory.iIndepFun_uncurry`) but not this one; the
proof compares the two laws through `MeasureTheory.Measure.infinitePi_map_curry`, which says
exactly that an infinite product over `ι × κ` is the iterated product read through the currying
equivalence. -/
private theorem iIndepFun_row {ι κ : Type*} [IsProbabilityMeasure μ] [Countable ι] [Finite κ]
    {X : ι → κ → Ω → ℝ} (hmeas : ∀ i j, AEMeasurable (X i j) μ)
    (h : iIndepFun (fun q : ι × κ => X q.1 q.2) μ) :
    iIndepFun (fun (i : ι) (ω : Ω) => fun j => X i j ω) μ := by
  have _ : Fintype κ := Fintype.ofFinite κ
  have hrow : ∀ i, iIndepFun (X i) μ := fun i =>
    h.precomp (g := fun j : κ => (i, j)) fun _ _ hj => by simpa using congrArg Prod.snd hj
  have hae : ∀ i, AEMeasurable (fun ω => fun j => X i j ω) μ :=
    fun i => AEMeasurable.of_eval fun j => hmeas i j
  have hpair : Measure.map (fun (ω : Ω) (q : ι × κ) => X q.1 q.2 ω) μ
      = Measure.infinitePi fun q : ι × κ => Measure.map (X q.1 q.2) μ :=
    h.map_fun_eq_infinitePi_map₀' fun q => hmeas q.1 q.2
  have : ∀ (i : ι) (j : κ), IsProbabilityMeasure (Measure.map (X i j) μ) :=
    fun i j => (Measure.isProbabilityMeasure_map_iff (hmeas i j)).mpr ‹_›
  have hstep := Measure.infinitePi_map_curry fun (i : ι) (j : κ) => Measure.map (X i j) μ
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' hae]
  have hcurry : (fun (ω : Ω) (i : ι) (j : κ) => X i j ω)
      = (MeasurableEquiv.curry ι κ ℝ) ∘ fun ω (q : ι × κ) => X q.1 q.2 ω := rfl
  rw [hcurry, ← AEMeasurable.map_map_of_aemeasurable
      (MeasurableEquiv.curry ι κ ℝ).measurable.aemeasurable
      (AEMeasurable.of_eval fun q => hmeas q.1 q.2), hpair, hstep]
  refine congrArg _ (funext fun i => ?_)
  rw [Measure.infinitePi_eq_pi, ← (iIndepFun_iff_map_fun_eq_pi_map fun j => hmeas i j).1 (hrow i)]

/-- A nonnegative family bounded by `C` is summable against `(i + 1)⁻²`, which is the variance
hypothesis Kolmogorov's strong law is applied with. -/
private theorem summable_div_add_one_sq {v : ℕ → ℝ} {C : ℝ} (hv : ∀ i, 0 ≤ v i)
    (hC : ∀ i, v i ≤ C) : Summable fun i : ℕ => v i / ((i : ℝ) + 1) ^ 2 := by
  have h : Summable fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1) ^ 2 := by
    refine ((summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 one_lt_two)).congr fun i => ?_
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun i => div_nonneg (hv i) (by positivity)) (fun i => ?_)
    ((h.mul_left C).congr fun i => mul_one_div C _)
  gcongr
  exact hC i

/-- **The noise Gram in the limit**, one entry: almost surely
`p⁻¹ ∑_{i<p} Z_{i,ℓ}Z_{i,m} → δ²` for `ℓ = m` and `→ 0` otherwise.

The summands `Z_{i,ℓ}Z_{i,m}` are independent — this is `PCError.FactorModelSeq.iIndepFun_row`
followed by the measurable map `v ↦ v_ℓ v_m` — lie in `L²` by Hölder, and have variance at most
the fourth-moment bound `κ₄`, since `(xy)² ≤ (x⁴ + y⁴)/2` pointwise.  So
`∑ᵢ Var(Z_{i,ℓ}Z_{i,m})/(i+1)² ≤ κ₄ ∑ᵢ (i+1)^{-2} < ∞` and the strong law applies.  The mean of
the summand is `δ²_{i,ℓ}` on
the diagonal, because `Z_{i,ℓ}` has mean zero, and `0` off it, because `Z_{i,ℓ}` and `Z_{i,m}` are
independent; the diagonal Cesàro limit is then the asymptotic hypothesis
`PCError.AsymptoticHypotheses.tendsto_variance_Z`. -/
private theorem ae_tendsto_gram_entry (hyp : AsymptoticHypotheses μ M G lam) (ℓ m : Fin M.n) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, M.Z i ℓ ω * M.Z i m ω)
      atTop (𝓝 (if ℓ = m then M.δsq else 0)) := by
  classical
  have := hyp.iIndepFun_Z.isProbabilityMeasure
  obtain ⟨C, hC⟩ := hyp.bddAbove_fourthMoment_Z
  have hCle : ∀ i j, μ[fun ω => M.Z i j ω ^ 4] ≤ C := fun i j => hC ⟨(i, j), rfl⟩
  have hmeas : ∀ i j, AEMeasurable (M.Z i j) μ :=
    fun i j => (hyp.memLp_Z i j).aestronglyMeasurable.aemeasurable
  have hL2 : ∀ i, MemLp (fun ω => M.Z i ℓ ω * M.Z i m ω) 2 μ :=
    fun i => (hyp.memLp_Z i ℓ).fun_mul (hyp.memLp_Z i m)
  have hindX : iIndepFun (fun (i : ℕ) (ω : Ω) => M.Z i ℓ ω * M.Z i m ω) μ :=
    (iIndepFun_row hmeas hyp.iIndepFun_Z).comp
      (g := fun _ : ℕ => fun v : Fin M.n → ℝ => v ℓ * v m) fun _ => by fun_prop
  have hmeanX : ∀ i,
      μ[fun ω => M.Z i ℓ ω * M.Z i m ω] = if ℓ = m then Var[M.Z i ℓ; μ] else 0 := by
    intro i
    split_ifs with hlm
    · subst hlm
      rw [variance_of_integral_eq_zero (hmeas i ℓ) (hyp.integral_Z i ℓ)]
      simp [sq]
    · have hi : IndepFun (M.Z i ℓ) (M.Z i m) μ :=
        hyp.iIndepFun_Z.indepFun (show ((i, ℓ) : ℕ × Fin M.n) ≠ (i, m) by simp [hlm])
      have h := hi.integral_mul_eq_mul_integral (hyp.memLp_Z i ℓ).aestronglyMeasurable
        (hyp.memLp_Z i m).aestronglyMeasurable
      simp only [Pi.mul_apply] at h
      rw [h, hyp.integral_Z i ℓ, zero_mul]
  have hsummable :
      Summable fun i : ℕ => Var[fun ω => M.Z i ℓ ω * M.Z i m ω; μ] / ((i : ℝ) + 1) ^ 2 :=
    summable_div_add_one_sq (fun i => variance_nonneg _ _)
      fun i => variance_mul_le (hyp.memLp_Z i ℓ) (hyp.memLp_Z i m) (hL2 i) (hCle i ℓ) (hCle i m)
  have h2 : Tendsto
      (fun p : ℕ => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, μ[fun ω => M.Z i ℓ ω * M.Z i m ω])
      atTop (𝓝 (if ℓ = m then M.δsq else 0)) := by
    simp only [hmeanX]
    split_ifs with hlm
    · exact hyp.tendsto_variance_Z ℓ
    · simp
  filter_upwards [kolmogorovSLLN.{u}
    (fun i ω => M.Z i ℓ ω * M.Z i m ω) hL2 hindX hsummable] with ω hω
  have h3 := hω.add h2
  rw [zero_add] at h3
  refine h3.congr fun p => ?_
  rw [Finset.sum_sub_distrib]
  ring

/-- **The noise Gram in the limit**: almost surely `(np)⁻¹(Z⁽ᵖ⁾)ᵀZ⁽ᵖ⁾ → (δ²/n)Iₙ`.

The sample size `n` is fixed, so the `n²` entries can be treated one at a time: entrywise
almost-sure convergence of matrices of fixed size is convergence of the matrices, and the
intersection of finitely many almost-sure events is almost sure.  Each entry is
`PCError.FactorModelSeq.ae_tendsto_gram_entry`, divided by `n`. -/
@[pcerror "lem_noise_gram"]
theorem ae_tendsto_gram_noiseMatrix (hyp : AsymptoticHypotheses μ M G lam) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ =>
        ((M.n : ℝ) * p)⁻¹ • ((M.noiseMatrix p ω)ᵀ * M.noiseMatrix p ω))
      atTop (𝓝 ((M.δsq / M.n) • (1 : Matrix (Fin M.n) (Fin M.n) ℝ))) := by
  classical
  have hall : ∀ᵐ ω ∂μ, ∀ ℓ m : Fin M.n, Tendsto
      (fun p : ℕ => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, M.Z i ℓ ω * M.Z i m ω) atTop
      (𝓝 (if ℓ = m then M.δsq else 0)) := by
    rw [ae_all_iff]
    intro ℓ
    rw [ae_all_iff]
    exact M.ae_tendsto_gram_entry hyp ℓ
  filter_upwards [hall] with ω hω
  refine tendsto_pi_nhds.2 fun ℓ => tendsto_pi_nhds.2 fun m => ?_
  have h := (hω ℓ m).const_mul ((M.n : ℝ)⁻¹)
  have htarget : (M.n : ℝ)⁻¹ * (if ℓ = m then M.δsq else 0)
      = ((M.δsq / M.n) • (1 : Matrix (Fin M.n) (Fin M.n) ℝ)) ℓ m := by
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [htarget] at h
  refine h.congr fun p => ?_
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, mul_inv, mul_assoc,
    ← Fin.sum_univ_eq_sum_range fun i => M.Z i ℓ ω * M.Z i m ω]
  simp

end NoiseGram

/-! ### The spectrum of the limiting dual Gram matrix -/

omit [MeasurableSpace Ω] in
/-- `W₀ = n⁻¹ Fᵀ G F` is positive semidefinite when the limiting loadings Gram `G` is. -/
theorem dualGramLim₀_posSemidef (hG : G.PosSemidef) : (M.dualGramLim₀ G).PosSemidef := by
  rw [FactorModelSeq.dualGramLim₀]
  refine Matrix.PosSemidef.smul ?_ (by positivity)
  have h := hG.conjTranspose_mul_mul_same (B := M.F)
  simpa using h

/-- A nonnegative antitone listing `e` of length `N` whose positive part has at most `k` entries
and which attains every value of a strictly decreasing positive family `lam : Fin k → ℝ` is
exactly `lam` on the first `k` places and `0` afterwards.

The positive entries of `e` form a lower set of `Fin N`, hence an initial segment, and it has
exactly `k` entries: at most `k` by hypothesis, at least `k` because the `k` distinct values of
`lam` are attained.  Reading off for each `j` the place `f j` at which `lam j` sits therefore
gives a map `Fin k → Fin k`, strictly monotone because `lam` is strictly decreasing and `e` is
antitone, hence the identity. -/
private theorem eq_dite_of_antitone {N k : ℕ} {e : Fin N → ℝ} {lam : Fin k → ℝ}
    (hanti : Antitone e) (hnn : ∀ i, 0 ≤ e i) (hlam : StrictAnti lam) (hpos : ∀ j, 0 < lam j)
    (hsup : ∀ j, ∃ i, e i = lam j)
    (hcard : (Finset.univ.filter fun i => 0 < e i).card ≤ k) (i : Fin N) :
    e i = if h : (i : ℕ) < k then lam ⟨i, h⟩ else 0 := by
  set P : Finset (Fin N) := Finset.univ.filter (fun i => 0 < e i) with hPdef
  have hmemP : ∀ a : Fin N, a ∈ P ↔ 0 < e a := by intro a; simp [hPdef]
  choose f hf using hsup
  have hfP : ∀ j, f j ∈ P := fun j => (hmemP (f j)).2 (by rw [hf j]; exact hpos j)
  have hkle : k ≤ P.card := by
    have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin k))) (t := P) f
      (fun j _ => hfP j) (fun j _ j' _ h => hlam.injective (by rw [← hf j, ← hf j', h]))
    simpa using h
  have hPcard : P.card = k := le_antisymm hcard hkle
  have hdown : ∀ a b : Fin N, a ≤ b → b ∈ P → a ∈ P := fun a b hab hb =>
    (hmemP a).2 (lt_of_lt_of_le ((hmemP b).1 hb) (hanti hab))
  have hPiff : ∀ a : Fin N, a ∈ P ↔ (a : ℕ) < k := by
    intro a
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · have hsub : Finset.Iic a ⊆ P := fun b hb => hdown b a (Finset.mem_Iic.1 hb) ha
      have h2 := Finset.card_le_card hsub
      rw [Fin.card_Iic, hPcard] at h2
      omega
    · by_contra hna
      have hsub : P ⊆ Finset.Iio a := by
        intro b hb
        rw [Finset.mem_Iio]
        by_contra hba
        exact hna (hdown a b (not_lt.1 hba) hb)
      have h2 := Finset.card_le_card hsub
      rw [Fin.card_Iio, hPcard] at h2
      omega
  have hfk : ∀ j : Fin k, ((f j : Fin N) : ℕ) < k := fun j => (hPiff (f j)).1 (hfP j)
  set g : Fin k → Fin k := fun j => ⟨(f j : ℕ), hfk j⟩ with hg
  have hgmono : StrictMono g := by
    intro j j' hjj
    have h2 : e (f j') < e (f j) := by rw [hf j, hf j']; exact hlam hjj
    have h3 : f j < f j' := by
      by_contra hcon
      exact absurd (hanti (not_lt.1 hcon)) (not_le.2 h2)
    exact h3
  have hgid : ∀ j, g j = j := fun j => hgmono.apply_eq
  by_cases hi : (i : ℕ) < k
  · have hfi : f ⟨i, hi⟩ = i := by
      refine Fin.ext ?_
      simpa [hg] using congrArg Fin.val (hgid ⟨i, hi⟩)
    rw [dite_eq_left hi, ← hf ⟨i, hi⟩, hfi]
  · rw [dite_eq_right hi]
    have hnP : i ∉ P := fun h => hi ((hPiff i).1 h)
    exact le_antisymm (not_lt.1 fun h => hnP ((hmemP i).2 h)) (hnn i)

/-- The rank of a real symmetric matrix is the number of nonzero entries of its *ordered*
eigenvalue listing: the two listings `Matrix.IsHermitian.eigenvalues` and
`Matrix.IsHermitian.eigenvalues₀` form the same multiset, so they contain the value `0` — and
hence every other value — equally often. -/
private theorem card_filter_eigenvalues₀_ne_zero {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℝ} (hA : A.IsHermitian) :
    (Finset.univ.filter fun i => hA.eigenvalues₀ i ≠ 0).card = A.rank := by
  have h := congrArg (Multiset.countP fun x : ℝ => x ≠ 0)
    (map_eigenvalues_eq_map_eigenvalues₀ hA)
  rw [Multiset.countP_map, Multiset.countP_map] at h
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype, Finset.card_def, Finset.card_def,
    Finset.filter_val, Finset.filter_val]
  exact h.symm

/-- The ordered spectrum of a positive semidefinite matrix of rank at most `k` whose positive
part is exactly a strictly decreasing positive family `lam : Fin k → ℝ`: the values of `lam`
in order, followed by zeros.

The rank bound caps the number of nonzero — hence, by positive semidefiniteness, positive —
ordered eigenvalues at `k`, and `PCError.FactorModelSeq.eq_dite_of_antitone` does the rest. -/
private theorem eigenvalues₀_eq_dite {N : Type*} [Fintype N] [DecidableEq N]
    {A : Matrix N N ℝ} (hA : A.PosSemidef) {k : ℕ} (hrank : A.rank ≤ k) {c : Fin k → ℝ}
    (hc : HasPosEigenvalues A c) (i : Fin (Fintype.card N)) :
    hA.isHermitian.eigenvalues₀ i = if h : (i : ℕ) < k then c ⟨i, h⟩ else 0 := by
  have hH := hA.isHermitian
  have hnn : ∀ i, 0 ≤ hH.eigenvalues₀ i := by
    intro i
    obtain ⟨j, hj⟩ := exists_eq_of_map_univ_val_eq
      (map_eigenvalues_eq_map_eigenvalues₀ hH).symm (rfl : hH.eigenvalues₀ i = hH.eigenvalues₀ i)
    rw [← hj]
    exact hH.posSemidef_iff_eigenvalues_nonneg.1 hA j
  have hsup : ∀ j : Fin k, ∃ i, hH.eigenvalues₀ i = c j := by
    intro j
    have h := hc.mem_spectrum j
    rw [hH.spectrum_real_eq_range_eigenvalues] at h
    obtain ⟨b, hb⟩ := h
    exact exists_eq_of_map_univ_val_eq (map_eigenvalues_eq_map_eigenvalues₀ hH) hb
  have hcard : (Finset.univ.filter fun i => 0 < hH.eigenvalues₀ i).card ≤ k := by
    have heq : (Finset.univ.filter fun i => 0 < hH.eigenvalues₀ i)
        = Finset.univ.filter fun i => hH.eigenvalues₀ i ≠ 0 :=
      Finset.filter_congr fun i _ =>
        ⟨fun h => ne_of_gt h, fun h => lt_of_le_of_ne (hnn i) (Ne.symm h)⟩
    rw [heq, card_filter_eigenvalues₀_ne_zero hH]
    exact hrank
  exact eq_dite_of_antitone hH.eigenvalues₀_antitone hnn hc.strictAnti hc.pos hsup hcard i

omit [MeasurableSpace Ω] in
/-- `W₀ = n⁻¹ Fᵀ G F` factors through the `k`-dimensional factor space, so its rank is at most
`k`. -/
private theorem rank_dualGramLim₀_le : (M.dualGramLim₀ G).rank ≤ M.k := by
  have h : M.dualGramLim₀ G = ((M.n : ℝ)⁻¹ • M.Fᵀ) * (G * M.F) := by
    rw [FactorModelSeq.dualGramLim₀, Matrix.smul_mul, Matrix.mul_assoc]
  rw [h]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin M.k))

omit [MeasurableSpace Ω] in
/-- **The spectrum of `W`**, the eigenvalues of `W₀`: the `k` systematic eigenvalues
`λ₁ > ⋯ > λₖ > 0` followed by `n - k` zeros. -/
@[pcerror "lem_W_spectrum"]
theorem eigenvalues₀_dualGramLim₀ (hG : G.PosSemidef)
    (hlam : HasPosEigenvalues (M.dualGramLim₀ G) lam) (i : Fin M.n) :
    (M.dualGramLim₀_isHermitian hG.isHermitian).eigenvalues₀
        (Fin.cast (Fintype.card_fin M.n).symm i)
      = if h : (i : ℕ) < M.k then lam ⟨i, h⟩ else 0 :=
  eigenvalues₀_eq_dite (M.dualGramLim₀_posSemidef hG) M.rank_dualGramLim₀_le hlam _

/-- An antitone listing is determined by the multiset it lists: two antitone families on
`Fin N` taking the same values with the same multiplicities are equal. -/
private theorem eq_of_antitone_of_map_univ_val_eq {N : ℕ} {f g : Fin N → ℝ} (hf : Antitone f)
    (hg : Antitone g)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) : f = g := by
  have hcoe : ∀ h : Fin N → ℝ, Multiset.map h Finset.univ.val = ↑(List.ofFn h) := fun h => by
    rw [List.ofFn_eq_map]; rfl
  rw [hcoe f, hcoe g, Multiset.coe_eq_coe] at h
  exact List.ofFn_injective (List.Perm.eq_of_sortedGE (List.sortedGE_ofFn_iff.mpr hf)
    (List.sortedGE_ofFn_iff.mpr hg) h)

/-- Unitary conjugation leaves the characteristic polynomial unchanged. -/
private theorem charpoly_conjStarAlgAut {N : Type*} [Fintype N] [DecidableEq N]
    (U : unitary (Matrix N N ℝ)) (A : Matrix N N ℝ) :
    ((Unitary.conjStarAlgAut ℝ (Matrix N N ℝ)) U A).charpoly = A.charpoly := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    UnitaryGroup.star_mul_self, Matrix.one_mul]

/-- The roots of a split monic polynomial written as a product of linear factors are the
multiset of its prescribed roots. -/
private theorem roots_prod_X_sub_C {N : Type*} [Fintype N] (d : N → ℝ) :
    (∏ i, (Polynomial.X - Polynomial.C (d i))).roots = Multiset.map d Finset.univ.val := by
  rw [Finset.prod_eq_multiset_prod,
    show Multiset.map (fun i => Polynomial.X - Polynomial.C (d i)) (Finset.univ : Finset N).val
        = Multiset.map (fun a : ℝ => Polynomial.X - Polynomial.C a)
          (Multiset.map d Finset.univ.val) by rw [Multiset.map_map]; rfl,
    Polynomial.roots_multiset_prod_X_sub_C]

/-- **The eigenvalue shift**: adding the scalar matrix `c Iₙ` to a real symmetric matrix shifts
every ordered eigenvalue by `c`.

The spectral theorem writes `A` as a unitary conjugate of `diagonal (eigenvalues A)`, so `A + cI`
is the same conjugate of `diagonal (eigenvalues A + c)`; conjugation does not change the
characteristic polynomial, whose roots are therefore the eigenvalues of `A` each shifted by `c`.
Both `eigenvalues₀ (A + cI)` and `eigenvalues₀ A + c` are antitone listings of that multiset,
hence equal. -/
private theorem eigenvalues₀_add_smul_one {N : Type*} [Fintype N] [DecidableEq N]
    {A W : Matrix N N ℝ} (hA : A.IsHermitian) {c : ℝ} (hW : W.IsHermitian)
    (hWA : W = A + c • (1 : Matrix N N ℝ)) (i : Fin (Fintype.card N)) :
    hW.eigenvalues₀ i = hA.eigenvalues₀ i + c := by
  subst hWA
  have hchar : (A + c • (1 : Matrix N N ℝ)).charpoly
      = ∏ j, (Polynomial.X - Polynomial.C (hA.eigenvalues j + c)) := by
    set φ := (Unitary.conjStarAlgAut ℝ (Matrix N N ℝ)) hA.eigenvectorUnitary with hφ
    have hA' : A = φ (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem
    have e1 : (diagonal (fun j => hA.eigenvalues j + c) : Matrix N N ℝ)
        = diagonal (RCLike.ofReal ∘ hA.eigenvalues) + c • (1 : Matrix N N ℝ) := by
      ext j l
      by_cases h : j = l <;> simp [h]
    have key : A + c • (1 : Matrix N N ℝ) = φ (diagonal (fun j => hA.eigenvalues j + c)) := by
      rw [e1, map_add, map_smul, map_one, ← hA']
    rw [key, charpoly_conjStarAlgAut, Matrix.charpoly_diagonal]
  have hmul : Multiset.map hW.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card N))).val
      = Multiset.map (fun j => hA.eigenvalues₀ j + c) Finset.univ.val := by
    have h1 := hW.roots_charpoly_eq_eigenvalues₀
    rw [hchar, roots_prod_X_sub_C] at h1
    have h2 : Multiset.map (fun j => hA.eigenvalues j + c) (Finset.univ : Finset N).val
        = Multiset.map (fun j => hA.eigenvalues₀ j + c) Finset.univ.val := by
      rw [show Multiset.map (fun j => hA.eigenvalues j + c) (Finset.univ : Finset N).val
            = Multiset.map (fun a : ℝ => a + c) (Multiset.map hA.eigenvalues Finset.univ.val) by
          rw [Multiset.map_map]; rfl,
        map_eigenvalues_eq_map_eigenvalues₀ hA, Multiset.map_map]
      rfl
    rw [h2] at h1
    have h3 : Multiset.map (RCLike.ofReal ∘ hW.eigenvalues₀)
          (Finset.univ : Finset (Fin (Fintype.card N))).val
        = Multiset.map hW.eigenvalues₀ Finset.univ.val := by simp
    rw [← h3, ← h1]
  exact congrFun (eq_of_antitone_of_map_univ_val_eq hW.eigenvalues₀_antitone
    (fun a b hab => by simpa using hA.eigenvalues₀_antitone hab) hmul) i

omit [MeasurableSpace Ω] in
/-- **The spectrum of `W`**, the eigenvalues of `W = W₀ + (δ²/n)Iₙ`: every eigenvalue of `W₀`
shifted by `δ²/n`.  In particular `λⱼ + δ²/n` is simple for `j ≤ k`, and `δ²/n` occurs with
multiplicity `n - k`. -/
@[pcerror "lem_W_spectrum"]
theorem eigenvalues₀_dualGramLim (hG : G.PosSemidef)
    (hlam : HasPosEigenvalues (M.dualGramLim₀ G) lam) (i : Fin M.n) :
    (M.dualGramLim_isHermitian hG.isHermitian).eigenvalues₀
        (Fin.cast (Fintype.card_fin M.n).symm i)
      = (if h : (i : ℕ) < M.k then lam ⟨i, h⟩ else 0) + M.δsq / M.n := by
  rw [eigenvalues₀_add_smul_one (M.dualGramLim₀_isHermitian hG.isHermitian)
      (M.dualGramLim_isHermitian hG.isHermitian) rfl, M.eigenvalues₀_dualGramLim₀ hG hlam]

omit [MeasurableSpace Ω] in
/-- **The spectrum of `W`**, the eigenvectors: adding the scalar matrix `(δ²/n)Iₙ` shifts every
eigenvalue by `δ²/n` and leaves every eigenvector unchanged. -/
@[pcerror "lem_W_spectrum"]
theorem mulVec_dualGramLim_eq_smul_iff {ζ : ℝ} {v : Fin M.n → ℝ} :
    M.dualGramLim G *ᵥ v = (ζ + M.δsq / M.n) • v ↔ M.dualGramLim₀ G *ᵥ v = ζ • v := by
  rw [FactorModelSeq.dualGramLim, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    add_smul]
  exact add_left_inj _

/-! ### Convergence of the observable dual Gram matrix -/

omit [MeasurableSpace Ω] in
/-- The observable dual Gram matrix expanded along `Y⁽ᵖ⁾ = b⁽ᵖ⁾Φ⁽ᵖ⁾ + Z⁽ᵖ⁾`, the systematic block
simplified by `(b⁽ᵖ⁾)ᵀb⁽ᵖ⁾ = Iₖ`. -/
private theorem dualGram_eq_of_le (p : ℕ) (hp : M.k ≤ p) (ω : Ω) :
    M.dualGram p ω = ((M.n : ℝ) * p)⁻¹ • ((M.Φ p)ᵀ * M.Φ p
      + (M.Φ p)ᵀ * ((M.b p)ᵀ * M.noiseMatrix p ω)
      + ((M.b p)ᵀ * M.noiseMatrix p ω)ᵀ * M.Φ p
      + (M.noiseMatrix p ω)ᵀ * M.noiseMatrix p ω) := by
  have hb := M.transpose_b_mul_b p hp
  rw [dualGram, dataMatrix]
  congr 1
  rw [transpose_add, transpose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    transpose_mul, transpose_transpose]
  have h1 : (M.Φ p)ᵀ * (M.b p)ᵀ * (M.b p * M.Φ p) = (M.Φ p)ᵀ * M.Φ p := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M.b p)ᵀ, hb, Matrix.one_mul]
  rw [h1, Matrix.mul_assoc (M.Φ p)ᵀ, ← Matrix.mul_assoc (M.noiseMatrix p ω)ᵀ, ← add_assoc]

omit [MeasurableSpace Ω] in
/-- The same expansion written in the two convergent blocks: the scaled scores `Φ̄⁽ᵖ⁾` and the
scaled projected noise `p^(-1/2)(b⁽ᵖ⁾)ᵀZ⁽ᵖ⁾`, plus the noise Gram. -/
private theorem dualGram_eq_scaled (p : ℕ) (hp : M.k ≤ p) (ω : Ω) :
    M.dualGram p ω = (M.n : ℝ)⁻¹ • ((M.scaledScores p)ᵀ * M.scaledScores p
        + (M.scaledScores p)ᵀ * ((Real.sqrt p)⁻¹ • ((M.b p)ᵀ * M.noiseMatrix p ω))
        + ((Real.sqrt p)⁻¹ • ((M.b p)ᵀ * M.noiseMatrix p ω))ᵀ * M.scaledScores p)
      + ((M.n : ℝ) * p)⁻¹ • ((M.noiseMatrix p ω)ᵀ * M.noiseMatrix p ω) := by
  have hs : (Real.sqrt p)⁻¹ * (Real.sqrt p)⁻¹ = (p : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  rw [M.dualGram_eq_of_le p hp ω, scaledScores]
  simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
  module

/-- **Convergence of the observable dual Gram matrix**: almost surely `W⁽ᵖ⁾ → W`.

The systematic block is `n⁻¹(Φ̄⁽ᵖ⁾)ᵀΦ̄⁽ᵖ⁾ → n⁻¹(Φ̄^∞)ᵀΦ̄^∞ = W₀`, the cross block is a product of
a convergent factor with `p^(-1/2)(b⁽ᵖ⁾)ᵀZ⁽ᵖ⁾ → 0` and hence vanishes, and the noise block tends to
`(δ²/n)Iₙ`. -/
@[pcerror "prop_dual_conv"]
theorem ae_tendsto_dualGram (hyp : StandingHypotheses μ M G lam) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => M.dualGram p ω) atTop (𝓝 (M.dualGramLim G)) := by
  filter_upwards [M.ae_tendsto_transpose_b_mul_noiseMatrix hyp.toAsymptoticHypotheses,
    M.ae_tendsto_gram_noiseMatrix hyp.toAsymptoticHypotheses] with ω hC hZ
  have hS := hyp.tendsto_scaledScores
  have key := ((((tendsto_matrix_mul (tendsto_matrix_transpose hS) hS).add
    (tendsto_matrix_mul (tendsto_matrix_transpose hS) hC)).add
      (tendsto_matrix_mul (tendsto_matrix_transpose hC) hS)).const_smul
        ((M.n : ℝ)⁻¹)).add hZ
  rw [Matrix.mul_zero, Matrix.transpose_zero, Matrix.zero_mul, add_zero, add_zero,
    hyp.gram_scaledScoresLim] at key
  refine (key.congr' ?_).congr fun p => rfl
  filter_upwards [eventually_ge_atTop M.k] with p hp
  exact (M.dualGram_eq_scaled p hp ω).symm

/-! ### The systematic eigenvalues in the limit -/

/-- **The systematic eigenvalues in the limit**: almost surely `θ⁽ᵖ⁾ⱼ → λⱼ + δ²/n` for each
`j ≤ k`.

Weyl's inequality makes each ordered eigenvalue continuous along `W⁽ᵖ⁾ → W`, and the `j`-th
ordered eigenvalue of `W` is `λⱼ + δ²/n`. -/
@[pcerror "prop_theta_limit"]
theorem ae_tendsto_dualEigenvalues (hyp : StandingHypotheses μ M G lam) (j : Fin M.k) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j)) atTop
      (𝓝 (lam j + M.δsq / M.n)) := by
  filter_upwards [M.ae_tendsto_dualGram hyp] with ω hω
  have h := tendsto_eigenvalues₀ (fun p => M.dualGram_isHermitian p ω)
    (M.dualGramLim_isHermitian hyp.G_posDef.isHermitian) hω
    (Fin.cast (Fintype.card_fin M.n).symm (Fin.castLE M.k_lt_n.le j))
  rw [M.eigenvalues₀_dualGramLim hyp.G_posDef.posSemidef hyp.hasPosEigenvalues_dualGramLim₀] at h
  simpa [dualEigenvalues] using h

/-- **The systematic eigenvalues in the limit**, positivity of the limit: `λⱼ + δ²/n > 0`, because
`λⱼ > 0` and `δ² > 0`. -/
@[pcerror "prop_theta_limit"]
theorem lam_add_div_pos (hyp : AsymptoticHypotheses μ M G lam) (j : Fin M.k) :
    0 < lam j + M.δsq / M.n := by
  have h1 := hyp.hasPosEigenvalues_dualGramLim₀.pos j
  have h2 : (0 : ℝ) < M.n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le M.k) M.k_lt_n
  have := M.δsq_pos
  positivity

/-! ### The average bulk eigenvalue in the limit -/

/-- **The average bulk eigenvalue in the limit**: almost surely `ℓ⁽ᵖ⁾ → δ²/n`.

Each of the `n - k` bulk eigenvalues `θ⁽ᵖ⁾ᵢ`, `i > k`, tends to the `i`-th ordered eigenvalue
`δ²/n` of `W`, and an average of finitely many convergent sequences converges to the average of
the limits. -/
@[pcerror "prop_bulk_limit"]
theorem ae_tendsto_avgBulkEigenvalue (hyp : StandingHypotheses μ M G lam) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => M.avgBulkEigenvalue p ω) atTop (𝓝 (M.δsq / M.n)) := by
  classical
  filter_upwards [M.ae_tendsto_dualGram hyp] with ω hω
  set s := Finset.univ.filter fun i : Fin M.n => M.k ≤ (i : ℕ) with hs
  have hcard : s.card = M.n - M.k := by
    have hIci : s = Finset.Ici (⟨M.k, M.k_lt_n⟩ : Fin M.n) := by
      ext i; simp [hs, Fin.le_def]
    rw [hIci, Fin.card_Ici]
  have hterm : ∀ i ∈ s,
      Tendsto (fun p : ℕ => M.dualEigenvalues p ω i) atTop (𝓝 (M.δsq / M.n)) := by
    intro i hi
    have hik : ¬ ((i : ℕ) < M.k) := by simp only [hs, Finset.mem_filter] at hi; omega
    have h := tendsto_eigenvalues₀ (fun p => M.dualGram_isHermitian p ω)
      (M.dualGramLim_isHermitian hyp.G_posDef.isHermitian) hω
      (Fin.cast (Fintype.card_fin M.n).symm i)
    rw [M.eigenvalues₀_dualGramLim hyp.G_posDef.posSemidef hyp.hasPosEigenvalues_dualGramLim₀,
      dite_eq_right hik, zero_add] at h
    simpa [dualEigenvalues] using h
  have hsum := tendsto_finsetSum s hterm
  rw [Finset.sum_const, hcard, nsmul_eq_mul,
    show ((M.n - M.k : ℕ) : ℝ) = (M.n : ℝ) - M.k from by
      exact_mod_cast Nat.cast_sub M.k_lt_n.le] at hsum
  have hlt : (M.k : ℝ) < M.n := by exact_mod_cast M.k_lt_n
  have hne : ((M.n : ℝ) - M.k) ≠ 0 := sub_ne_zero.2 hlt.ne'
  have hfin := hsum.const_mul ((M.n : ℝ) - M.k)⁻¹
  rw [inv_mul_cancel_left₀ hne] at hfin
  simpa [avgBulkEigenvalue, hs] using hfin

/-! ### The systematic eigenvectors in the limit -/

/-- **The systematic eigenvectors in the limit**: almost surely, for each `j ≤ k` and any choice
of unit eigenvectors `w⁽ᵖ⁾ⱼ` of `W⁽ᵖ⁾` at `θ⁽ᵖ⁾ⱼ`, one has `|⟪w⁽ᵖ⁾ⱼ, wⱼ⟫| → 1`, where `wⱼ` is a
unit eigenvector of `W₀` at `λⱼ`.

The eigenvalue `λⱼ + δ²/n` of `W` is simple with eigenvector `wⱼ`, so eigenpair convergence at a
simple eigenvalue applies along `W⁽ᵖ⁾ → W`; the simple eigenvalue it produces is eventually
`θ⁽ᵖ⁾ⱼ` itself, because the eigenvalues of `W` are separated. -/
@[pcerror "prop_w_limit"]
theorem ae_tendsto_abs_inner_dualEigenvector (hyp : StandingHypotheses μ M G lam) (j : Fin M.k)
    {w : EuclideanSpace ℝ (Fin M.n)} (hw1 : ‖w‖ = 1)
    (hw : M.dualGramLim₀ G *ᵥ w = lam j • w) :
    ∀ᵐ ω ∂μ, ∀ u : ℕ → EuclideanSpace ℝ (Fin M.n),
      (∀ᶠ p in atTop, ‖u p‖ = 1 ∧
        M.dualGram p ω *ᵥ u p = M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j) • u p) →
      Tendsto (fun p => |⟪u p, w⟫|) atTop (𝓝 1) := by
  classical
  set ζ := lam j + M.δsq / M.n with hζ
  have hWH := M.dualGramLim_isHermitian hyp.G_posDef.isHermitian
  have hWw : M.dualGramLim G *ᵥ w = ζ • w := (M.mulVec_dualGramLim_eq_smul_iff).2 hw
  set i₀ : Fin (Fintype.card (Fin M.n)) :=
    Fin.cast (Fintype.card_fin M.n).symm (Fin.castLE M.k_lt_n.le j) with hi₀def
  have hev := M.eigenvalues₀_dualGramLim hyp.G_posDef.posSemidef hyp.hasPosEigenvalues_dualGramLim₀
  have hi₀ : hWH.eigenvalues₀ i₀ = ζ := by rw [hi₀def, hev]; simp [hζ]
  have huniq : ∀ i, hWH.eigenvalues₀ i = ζ → i = i₀ := by
    intro i hi
    have hc : i = Fin.cast (Fintype.card_fin M.n).symm (Fin.cast (Fintype.card_fin M.n) i) := rfl
    rw [hc, hev] at hi
    have hi' : (if h : ((Fin.cast (Fintype.card_fin M.n) i : Fin M.n) : ℕ) < M.k
        then lam ⟨_, h⟩ else 0) = lam j := by rw [hζ] at hi; linarith
    split_ifs at hi' with h
    · have hji := hyp.hasPosEigenvalues_dualGramLim₀.injective hi'
      rw [hi₀def]
      exact Fin.ext (by simpa using congrArg Fin.val hji)
    · exact absurd hi'.symm (ne_of_gt (hyp.hasPosEigenvalues_dualGramLim₀.pos j))
  have hsimple : ∀ v : EuclideanSpace ℝ (Fin M.n), ‖v‖ = 1 →
      M.dualGramLim G *ᵥ v = ζ • v → v = w ∨ v = -w := by
    obtain ⟨i₁, hi₁, hi₁uniq⟩ := exists_unique_eq_of_map_univ_val_eq
      (map_eigenvalues_eq_map_eigenvalues₀ hWH).symm hi₀ huniq
    intro v hv1 hv
    have e1 := eq_or_eq_neg_eigenvectorBasis hWH hi₁uniq hv1 hv
    have e2 := eq_or_eq_neg_eigenvectorBasis hWH hi₁uniq hw1 hWw
    rcases e1 with h1 | h1 <;> rcases e2 with h2 | h2 <;> rw [h1, h2] <;> simp
  filter_upwards [M.ae_tendsto_dualGram hyp] with ω hω
  obtain ⟨zeta, hzeta, hspec, hconc⟩ := exists_tendsto_simple_eigenvalue
    (fun p => M.dualGram_isHermitian p ω) hWH hω hw1 hWw hsimple
  have hxspec : ∀ᶠ p in atTop, ∃ v : EuclideanSpace ℝ (Fin M.n), v ≠ 0 ∧
      M.dualGram p ω *ᵥ v = zeta p • v := by
    filter_upwards [hspec] with p hp
    obtain ⟨v, hv1, hv, -⟩ := hp
    exact ⟨v, fun h => by simp [h] at hv1, hv⟩
  have heq := eventually_eq_eigenvalues₀ (fun p => M.dualGram_isHermitian p ω) hWH hω
    huniq hzeta hxspec
  intro u hu
  refine hconc u ?_
  filter_upwards [hu, heq] with p h1 h2
  have hth : M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j) = zeta p := by rw [h2]; rfl
  exact ⟨h1.1, by rw [h1.2, hth]⟩

end FactorModelSeq

end PCError

end
