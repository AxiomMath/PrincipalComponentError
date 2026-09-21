/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import PCError.Attr
public import PCError.Angles
public import PCError.Defs.TheOutOfSubspaceErrorIsEstimable
public import PCError.TheObservableDualGramMatrixInTheLimit
public import PCError.TheSystematicDualGramsInTheLimit

/-!
# Error in the estimated principal directions

The asymptotics of the sample principal directions `h_j`, the unit eigenvectors of the scaled
sample covariance `S⁽ᵖ⁾` at its top eigenvalues.  Gram duality reconstructs `h_j` from the
fixed-size dual eigenvector `w⁽ᵖ⁾ⱼ`, and everything about `h_j` is then read off from the
limits of `w⁽ᵖ⁾ⱼ` and `θ⁽ᵖ⁾ⱼ` established in
`PCError.TheObservableDualGramMatrixInTheLimit`.  The error splits exactly into an
out-of-subspace part, which the noise level `δ²` controls, and an in-subspace rotation, which
it does not.

## Main statements

* `PCError.FactorModelSeq.norm_eq_one_of_sqrt_smul_eq_dataMatrix_mulVec`,
  `PCError.FactorModelSeq.sampleCov_mulVec_eq_smul_of_sqrt_smul_eq_dataMatrix_mulVec`:
  *reconstruction of the sample eigenvector* — a vector `h_j` with
  `√(npθ⁽ᵖ⁾ⱼ) h_j = Y⁽ᵖ⁾w⁽ᵖ⁾ⱼ` is a unit eigenvector of `S⁽ᵖ⁾` at `θ⁽ᵖ⁾ⱼ`.
* `PCError.FactorModelSeq.transpose_b_mulVec_eq_smul`: *the principal coordinate of the sample
  eigenvector* — `(b⁽ᵖ⁾)ᵀh_j = (nθ⁽ᵖ⁾ⱼ)^{-1/2}(Φ̄⁽ᵖ⁾ + p^{-1/2}(b⁽ᵖ⁾)ᵀZ⁽ᵖ⁾)w⁽ᵖ⁾ⱼ`.
* `PCError.FactorModelSeq.ae_exists_sign_tendsto_transpose_b_mulVec`: *the limit of the
  principal coordinate* — up to signs, `(b⁽ᵖ⁾)ᵀh_j → √(nλⱼ/(nλⱼ+δ²)) νⱼ`.
* `PCError.FactorModelSeq.ae_tendsto_one_sub_sinSqAngleSubspace`,
  `PCError.FactorModelSeq.ae_tendsto_sinSqAngleSubspace`: *in-subspace mass* and
  *out-of-subspace error* — `cos²∠(h_j, 𝓑) → nλⱼ/(nλⱼ+δ²)` and
  `sin²∠(h_j, 𝓑) → δ²/(nλⱼ+δ²)`.
* `PCError.FactorModelSeq.ae_eventually_starProjection_ne_zero`: the projection of `h_j` onto
  the systematic subspace is eventually nonzero.
* `PCError.FactorModelSeq.ae_tendsto_sinSqAngle_starProjection`: *in-subspace rotation error* —
  `sin²∠(Π h_j, b⁽ᵖ⁾ⱼ) → sin²∠(νⱼ, eⱼ)`.
* `PCError.FactorModelSeq.ae_tendsto_sinSqAngle_principalDirection`: *error decomposition* —
  `sin²∠(h_j, b⁽ᵖ⁾ⱼ) → δ²/(nλⱼ+δ²) + nλⱼ/(nλⱼ+δ²) sin²∠(νⱼ, eⱼ)`.

## Implementation notes

Angles need norms and inner products, so the vectors of this file live in `EuclideanSpace`, and
a matrix acts on them through `Matrix.toEuclideanLin`.  The first section collects what a matrix
`b` with orthonormal columns, `bᵀb = 1`, does to that structure: it is an isometry, so it
preserves inner products, norms and the squared sines of angles, and `bbᵀ` is the orthogonal
projector onto the span of its columns (`PCError.starProjection_range_toEuclideanLin`).  This is
the only place where the orthonormality hypothesis of `PCError.FactorModelSeq` is used, and it
is what makes `sin²∠(Π h_j, b⁽ᵖ⁾ⱼ) = sin²∠((b⁽ᵖ⁾)ᵀh_j, eⱼ)`, an identity between an angle in
the growing space `ℝ^p` and one in the fixed space `ℝ^k`.

The sample eigenvector `h_j` lives in `ℝ^p` and so has a `p`-dependent type; a *choice* of it
for every `p`, together with the dual eigenvectors it is reconstructed from, is bundled as
`PCError.FactorModelSeq.PrincipalDirectionSeq`.  Its three conditions hold only eventually in
`p`, which is all the asymptotics use and all that can be asked: a `p × k` frame has
orthonormal columns only once `p ≥ k`, and `θ⁽ᵖ⁾ⱼ` is positive only for large `p`.

There is no `cos²` definition: `cos²∠(h_j, 𝓑)` is spelled `1 - sinSqAngleSubspace h_j 𝓑`, which
is what `PCError.sinSqAngleSubspace` makes it.  The error decomposition needs no nonvanishing
hypothesis, because the exact angular split
`PCError.sinSqAngle_eq_sinSqAngleSubspace_add_mul_sinSqAngle_starProjection` was proved without
one.
-/

@[expose] public section

namespace PCError

universe u

open Filter Matrix MeasureTheory
open scoped Topology RealInnerProductSpace

/-! ### Convergence in a Euclidean space -/

section Convergence

variable {ι : Type*} {l : Filter ι}

/-- Convergence in `EuclideanSpace ℝ n` is entrywise convergence. -/
theorem tendsto_euclideanSpace_iff {n : Type*} [Finite n] {v : ι → EuclideanSpace ℝ n}
    {v₀ : EuclideanSpace ℝ n} :
    Tendsto v l (𝓝 v₀) ↔ ∀ i, Tendsto (fun a => (v a).ofLp i) l (𝓝 (v₀.ofLp i)) := by
  have := Fintype.ofFinite n
  rw [(EuclideanSpace.equiv n ℝ).toHomeomorph.isEmbedding.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- Matrix–vector multiplication is jointly continuous in the matrix and the vector, for
matrices of a fixed size acting on a Euclidean space. -/
theorem tendsto_toEuclideanLin {m n : Type*} [Fintype n] [DecidableEq n] [Finite m]
    {A : ι → Matrix m n ℝ} {A₀ : Matrix m n ℝ} {v : ι → EuclideanSpace ℝ n}
    {v₀ : EuclideanSpace ℝ n} (hA : Tendsto A l (𝓝 A₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun a => Matrix.toEuclideanLin (A a) (v a)) l (𝓝 (Matrix.toEuclideanLin A₀ v₀)) := by
  rw [tendsto_euclideanSpace_iff]
  rw [tendsto_euclideanSpace_iff] at hv
  intro i
  change Tendsto (fun a => ∑ j, A a i j * (v a).ofLp j) l (𝓝 (∑ j, A₀ i j * v₀.ofLp j))
  refine tendsto_finsetSum _ fun j _ => Tendsto.mul ?_ (hv j)
  exact (((continuous_apply j).comp (continuous_apply i)).tendsto A₀).comp hA

/-- The squared sine of the angle to a fixed nonzero vector is continuous away from `0`. -/
theorem tendsto_sinSqAngle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u : ι → E} {u₀ v : E} (hu₀ : u₀ ≠ 0) (hvne : v ≠ 0) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun a => sinSqAngle (u a) v) l (𝓝 (sinSqAngle u₀ v)) := by
  have hne : ‖u₀‖ ^ 2 * ‖v‖ ^ 2 ≠ 0 := mul_ne_zero
    (pow_ne_zero 2 (norm_ne_zero_iff.2 hu₀)) (pow_ne_zero 2 (norm_ne_zero_iff.2 hvne))
  simp only [sinSqAngle]
  exact tendsto_const_nhds.sub
    ((((Tendsto.inner (𝕜 := ℝ) hu tendsto_const_nhds).pow 2)).div
      ((hu.norm.pow 2).mul tendsto_const_nhds) hne)

end Convergence

/-! ### Frames with orthonormal columns as isometries -/

section OrthonormalColumns

variable {m r : Type*} [Fintype r] [DecidableEq r] {b : Matrix m r ℝ}

/-- The vector underlying `Matrix.toEuclideanLin A x` is the matrix–vector product
`A *ᵥ x.ofLp`. -/
@[simp] theorem ofLp_toEuclideanLin (A : Matrix m r ℝ) (x : EuclideanSpace ℝ r) :
    (Matrix.toEuclideanLin A x).ofLp = A *ᵥ x.ofLp :=
  rfl

/-- The composite of the maps of two matrices on Euclidean spaces is the map of their product. -/
theorem toEuclideanLin_toEuclideanLin {s : Type*} [Fintype s] [DecidableEq s]
    (A : Matrix m r ℝ) (B : Matrix r s ℝ) (x : EuclideanSpace ℝ s) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) = Matrix.toEuclideanLin (A * B) x := by
  ext i
  simp [Matrix.mulVec_mulVec]

/-- The identity matrix acts as the identity map of `EuclideanSpace ℝ r`. -/
@[simp] theorem toEuclideanLin_one (x : EuclideanSpace ℝ r) :
    Matrix.toEuclideanLin (1 : Matrix r r ℝ) x = x := by
  ext i
  simp

variable [Fintype m]

/-- A matrix with orthonormal columns preserves inner products. -/
theorem inner_toEuclideanLin_toEuclideanLin (hb : bᵀ * b = 1) (x y : EuclideanSpace ℝ r) :
    ⟪Matrix.toEuclideanLin b x, Matrix.toEuclideanLin b y⟫ = ⟪x, y⟫ := by
  simp only [inner_eq_dotProduct, ofLp_toEuclideanLin]
  rw [Matrix.dotProduct_mulVec, ← Matrix.transpose_transpose b, Matrix.vecMul_transpose,
    Matrix.transpose_transpose, Matrix.mulVec_mulVec, hb, Matrix.one_mulVec]

/-- A matrix with orthonormal columns is an isometry. -/
theorem norm_toEuclideanLin (hb : bᵀ * b = 1) (x : EuclideanSpace ℝ r) :
    ‖Matrix.toEuclideanLin b x‖ = ‖x‖ := by
  have h := inner_toEuclideanLin_toEuclideanLin hb x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (Matrix.toEuclideanLin b x), norm_nonneg x]

/-- A matrix with orthonormal columns preserves the angle between two lines. -/
theorem sinSqAngle_toEuclideanLin (hb : bᵀ * b = 1) (x y : EuclideanSpace ℝ r) :
    sinSqAngle (Matrix.toEuclideanLin b x) (Matrix.toEuclideanLin b y) = sinSqAngle x y := by
  rw [sinSqAngle, sinSqAngle, inner_toEuclideanLin_toEuclideanLin hb,
    norm_toEuclideanLin hb, norm_toEuclideanLin hb]

variable [DecidableEq m]

/-- The adjoint of a real matrix, read as a map of Euclidean spaces, is its transpose. -/
theorem inner_toEuclideanLin_left (A : Matrix m r ℝ) (x : EuclideanSpace ℝ r)
    (u : EuclideanSpace ℝ m) :
    ⟪Matrix.toEuclideanLin A x, u⟫ = ⟪x, Matrix.toEuclideanLin Aᵀ u⟫ := by
  rw [show Aᵀ = Aᴴ from (Matrix.conjTranspose_eq_transpose_of_trivial A).symm,
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

/-- For a matrix `b` with orthonormal columns, `bbᵀ` is the orthogonal projector onto the span
of the columns of `b`.  This is the matrix `Π`; see
`PCError.FactorModelSeq.starProjection_principalSubspace_eq_frameProj`. -/
theorem starProjection_range_toEuclideanLin (hb : bᵀ * b = 1) (u : EuclideanSpace ℝ m) :
    (LinearMap.range (Matrix.toEuclideanLin b)).starProjection u
      = Matrix.toEuclideanLin b (Matrix.toEuclideanLin bᵀ u) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ⟨_, rfl⟩ ?_
  rw [Submodule.mem_orthogonal]
  rintro v ⟨x, rfl⟩
  rw [inner_sub_right, inner_toEuclideanLin_left, inner_toEuclideanLin_left,
    toEuclideanLin_toEuclideanLin, hb, toEuclideanLin_one, sub_self]

end OrthonormalColumns

namespace FactorModelSeq

variable {Ω : Type u} (M : FactorModelSeq Ω)

/-! ### The systematic subspace and the principal directions -/

/-- The *systematic subspace* `𝓑⁽ᵖ⁾ ⊆ ℝ^p`: the span of the columns of the principal frame
`b⁽ᵖ⁾`, read as a subspace of the Euclidean space `ℝ^p`. -/
noncomputable def principalSubspace (p : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin p)) :=
  LinearMap.range (Matrix.toEuclideanLin (M.b p))

/-- The systematic subspace is the range of the principal frame. -/
theorem principalSubspace_def (p : ℕ) :
    M.principalSubspace p = LinearMap.range (Matrix.toEuclideanLin (M.b p)) :=
  rfl

/-- Membership in the systematic subspace: `u ∈ 𝓑⁽ᵖ⁾` exactly when `u = b⁽ᵖ⁾x` for some `x`. -/
theorem mem_principalSubspace_iff {p : ℕ} {u : EuclideanSpace ℝ (Fin p)} :
    u ∈ M.principalSubspace p ↔ ∃ x, Matrix.toEuclideanLin (M.b p) x = u :=
  LinearMap.mem_range

/-- The vector underlying the `j`-th principal direction is the `j`-th column of `b⁽ᵖ⁾`. -/
@[simp] theorem ofLp_principalDirection (p : ℕ) (j : Fin M.k) :
    (M.principalDirection p j).ofLp = (M.b p)ᵀ j :=
  rfl

/-- The principal frame `b⁽ᵖ⁾` carries the `j`-th standard basis vector `eⱼ` of `ℝ^k` to the
`j`-th principal direction `b⁽ᵖ⁾ⱼ`. -/
@[simp] theorem toEuclideanLin_b_single (p : ℕ) (j : Fin M.k) :
    Matrix.toEuclideanLin (M.b p) (EuclideanSpace.single j (1 : ℝ))
      = M.principalDirection p j := by
  ext i
  simp [Matrix.mulVec_single]

/-- Each principal direction lies in the systematic subspace. -/
theorem principalDirection_mem_principalSubspace (p : ℕ) (j : Fin M.k) :
    M.principalDirection p j ∈ M.principalSubspace p :=
  M.mem_principalSubspace_iff.2 ⟨EuclideanSpace.single j (1 : ℝ), M.toEuclideanLin_b_single p j⟩

variable {p : ℕ}

/-- The orthogonal projector onto the systematic subspace acts as `u ↦ b⁽ᵖ⁾((b⁽ᵖ⁾)ᵀu)`. -/
theorem starProjection_principalSubspace (hp : M.k ≤ p) (u : EuclideanSpace ℝ (Fin p)) :
    (M.principalSubspace p).starProjection u
      = Matrix.toEuclideanLin (M.b p) (Matrix.toEuclideanLin (M.b p)ᵀ u) := by
  rw [M.principalSubspace_def]
  exact starProjection_range_toEuclideanLin (M.transpose_b_mul_b p hp) u

/-- The orthogonal projector onto the systematic subspace is the matrix
`Π = b⁽ᵖ⁾(b⁽ᵖ⁾)ᵀ`. -/
theorem starProjection_principalSubspace_eq_frameProj (hp : M.k ≤ p)
    (u : EuclideanSpace ℝ (Fin p)) :
    (M.principalSubspace p).starProjection u = Matrix.toEuclideanLin (frameProj (M.b p)) u := by
  rw [M.starProjection_principalSubspace hp, toEuclideanLin_toEuclideanLin,
    frameProj_eq_mul_transpose]

/-- The projection onto the systematic subspace has the norm of the principal coordinate
vector: `‖Π u‖ = ‖(b⁽ᵖ⁾)ᵀu‖`. -/
theorem norm_starProjection_principalSubspace (hp : M.k ≤ p) (u : EuclideanSpace ℝ (Fin p)) :
    ‖(M.principalSubspace p).starProjection u‖ = ‖Matrix.toEuclideanLin (M.b p)ᵀ u‖ := by
  rw [M.starProjection_principalSubspace hp, norm_toEuclideanLin (M.transpose_b_mul_b p hp)]

/-- For a unit vector `u`, the squared cosine of the angle to the systematic subspace is the
squared norm of the principal coordinate vector `(b⁽ᵖ⁾)ᵀu`. -/
theorem one_sub_sinSqAngleSubspace_principalSubspace (hp : M.k ≤ p)
    {u : EuclideanSpace ℝ (Fin p)} (hu : ‖u‖ = 1) :
    1 - sinSqAngleSubspace u (M.principalSubspace p)
      = ‖Matrix.toEuclideanLin (M.b p)ᵀ u‖ ^ 2 := by
  rw [sinSqAngleSubspace, hu, one_pow, div_one, sub_sub_cancel,
    M.norm_starProjection_principalSubspace hp]

/-- The rotation inside the systematic subspace is an angle in the *fixed* space `ℝ^k`:
`sin²∠(Π u, b⁽ᵖ⁾ⱼ) = sin²∠((b⁽ᵖ⁾)ᵀu, eⱼ)`. -/
theorem sinSqAngle_starProjection_principalSubspace (hp : M.k ≤ p)
    (u : EuclideanSpace ℝ (Fin p)) (j : Fin M.k) :
    sinSqAngle ((M.principalSubspace p).starProjection u) (M.principalDirection p j)
      = sinSqAngle (Matrix.toEuclideanLin (M.b p)ᵀ u) (EuclideanSpace.single j (1 : ℝ)) := by
  rw [M.starProjection_principalSubspace hp, ← M.toEuclideanLin_b_single p j,
    sinSqAngle_toEuclideanLin (M.transpose_b_mul_b p hp)]

/-! ### Reconstruction of the sample eigenvector -/

/-- `S⁽ᵖ⁾` is the Gram product `AAᵀ` of the scaled data matrix `A = (np)^{-1/2}Y⁽ᵖ⁾`. -/
theorem sampleCov_eq_mul_transpose (p : ℕ) (ω : Ω) :
    M.sampleCov p ω = ((Real.sqrt ((M.n : ℝ) * p))⁻¹ • M.dataMatrix p ω) *
      ((Real.sqrt ((M.n : ℝ) * p))⁻¹ • M.dataMatrix p ω)ᵀ := by
  rw [sampleCov, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_inv,
    Real.mul_self_sqrt (by positivity)]

/-- `W⁽ᵖ⁾` is the Gram product `AᵀA` of the scaled data matrix `A = (np)^{-1/2}Y⁽ᵖ⁾`. -/
theorem dualGram_eq_transpose_mul (p : ℕ) (ω : Ω) :
    M.dualGram p ω = ((Real.sqrt ((M.n : ℝ) * p))⁻¹ • M.dataMatrix p ω)ᵀ *
      ((Real.sqrt ((M.n : ℝ) * p))⁻¹ • M.dataMatrix p ω) := by
  rw [dualGram, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_inv,
    Real.mul_self_sqrt (by positivity)]

section Reconstruct

variable {ω : Ω} {θ : ℝ} {w : EuclideanSpace ℝ (Fin M.n)} {h : EuclideanSpace ℝ (Fin p)}

/-- The dual eigenvector equation of `W⁽ᵖ⁾` as an eigenvector equation for the Gram product `AAᵀ`,
where `A := ((np)^{-1/2}Y⁽ᵖ⁾)ᵀ`. -/
private theorem mulVec_mul_transpose_eq_smul (hw : M.dualGram p ω *ᵥ w = θ • w) :
    ((((Real.sqrt ((M.n : ℝ) * p))⁻¹ • M.dataMatrix p ω)ᵀ) *
        (((Real.sqrt ((M.n : ℝ) * p))⁻¹ • M.dataMatrix p ω)ᵀ)ᵀ) *ᵥ w = θ • w := by
  rw [transpose_transpose, ← M.dualGram_eq_transpose_mul]
  exact hw

/-- The reconstruction equation `√(npθ) h = Y⁽ᵖ⁾w` in the form `√θ h = Aᵀw`, where
`A := ((np)^{-1/2}Y⁽ᵖ⁾)ᵀ`. -/
private theorem sqrt_smul_eq_transpose_mulVec (hp : p ≠ 0)
    (hh : Real.sqrt ((M.n : ℝ) * p * θ) • h = M.dataMatrix p ω *ᵥ w) :
    Real.sqrt θ • h = ((((Real.sqrt ((M.n : ℝ) * p))⁻¹ • M.dataMatrix p ω)ᵀ)ᵀ) *ᵥ w := by
  have hnp : (0 : ℝ) < (M.n : ℝ) * p :=
    mul_pos (by exact_mod_cast M.n_pos) (by exact_mod_cast Nat.pos_of_ne_zero hp)
  rw [transpose_transpose, Matrix.smul_mulVec, ← hh, smul_smul, Real.sqrt_mul hnp.le,
    inv_mul_cancel_left₀ (Real.sqrt_ne_zero'.2 hnp)]

/-- **Reconstruction of the sample eigenvector**, the unit-norm part: a vector `h` with
`√(npθ) h = Y⁽ᵖ⁾w`, built from a unit eigenvector `w` of the observable dual Gram matrix
`W⁽ᵖ⁾` at a nonzero `θ`, is a unit vector. -/
@[pcerror "lem_reconstruct"]
theorem norm_eq_one_of_sqrt_smul_eq_dataMatrix_mulVec (hp : p ≠ 0) (hθ : θ ≠ 0) (hw1 : ‖w‖ = 1)
    (hw : M.dualGram p ω *ᵥ w = θ • w)
    (hh : Real.sqrt ((M.n : ℝ) * p * θ) • h = M.dataMatrix p ω *ᵥ w) : ‖h‖ = 1 :=
  norm_eq_one_of_sqrt_smul_eq_transpose_mulVec _ hθ hw1
    (M.mulVec_mul_transpose_eq_smul hw) (M.sqrt_smul_eq_transpose_mulVec hp hh)

/-- **Reconstruction of the sample eigenvector**, the eigenvector part: a vector `h` with
`√(npθ) h = Y⁽ᵖ⁾w`, built from a unit eigenvector `w` of the observable dual Gram matrix
`W⁽ᵖ⁾` at a nonzero `θ`, is an eigenvector of the scaled sample covariance `S⁽ᵖ⁾` at `θ`. -/
@[pcerror "lem_reconstruct"]
theorem sampleCov_mulVec_eq_smul_of_sqrt_smul_eq_dataMatrix_mulVec (hp : p ≠ 0) (hθ : θ ≠ 0)
    (hw1 : ‖w‖ = 1) (hw : M.dualGram p ω *ᵥ w = θ • w)
    (hh : Real.sqrt ((M.n : ℝ) * p * θ) • h = M.dataMatrix p ω *ᵥ w) :
    M.sampleCov p ω *ᵥ h = θ • h := by
  have hAw := M.mulVec_mul_transpose_eq_smul hw
  have hres := transpose_mul_mulVec_eq_smul_of_sqrt_smul_eq_transpose_mulVec _
    (pos_of_mulVec_mul_transpose_eq_smul _ hθ hw1 hAw) hAw
    (M.sqrt_smul_eq_transpose_mulVec hp hh)
  rwa [transpose_transpose, ← M.sampleCov_eq_mul_transpose] at hres

/-! ### The principal coordinate of the sample eigenvector -/

/-- **The principal coordinate of the sample eigenvector**:
`(b⁽ᵖ⁾)ᵀh = (nθ)^{-1/2}(Φ̄⁽ᵖ⁾ + p^{-1/2}(b⁽ᵖ⁾)ᵀZ⁽ᵖ⁾)w` for the vector `h` reconstructed from `w`
as in `PCError.FactorModelSeq.norm_eq_one_of_sqrt_smul_eq_dataMatrix_mulVec`. -/
@[pcerror "lem_coord_formula"]
theorem transpose_b_mulVec_eq_smul (hp : M.k ≤ p) (hθ : 0 < θ)
    (hh : Real.sqrt ((M.n : ℝ) * p * θ) • h = M.dataMatrix p ω *ᵥ w) :
    (M.b p)ᵀ *ᵥ h = (Real.sqrt ((M.n : ℝ) * θ))⁻¹ •
      ((M.scaledScores p + (Real.sqrt p)⁻¹ • ((M.b p)ᵀ * M.noiseMatrix p ω)) *ᵥ w) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le M.one_le_k hp
  have hsp : Real.sqrt p ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hppos)
  have hsnθ : Real.sqrt ((M.n : ℝ) * θ) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (mul_pos (by exact_mod_cast M.n_pos) hθ)
  have hsqrt : Real.sqrt p * Real.sqrt ((M.n : ℝ) * θ) = Real.sqrt ((M.n : ℝ) * p * θ) := by
    rw [← Real.sqrt_mul p.cast_nonneg, mul_left_comm, ← mul_assoc]
  set C := M.scaledScores p + (Real.sqrt p)⁻¹ • ((M.b p)ᵀ * M.noiseMatrix p ω) with hC
  have hbY : (M.b p)ᵀ * M.dataMatrix p ω = Real.sqrt p • C := by
    rw [hC, smul_add, M.sqrt_smul_scaledScores p hppos.ne', smul_smul, mul_inv_cancel₀ hsp,
      one_smul, dataMatrix, Matrix.mul_add, ← Matrix.mul_assoc, M.transpose_b_mul_b p hp,
      Matrix.one_mul]
  have hstep : Real.sqrt ((M.n : ℝ) * θ) • ((M.b p)ᵀ *ᵥ h) = C *ᵥ w :=
    (smul_right_inj hsp).1 <| by
      rw [smul_smul, hsqrt, ← Matrix.mulVec_smul, hh, Matrix.mulVec_mulVec, hbY,
        Matrix.smul_mulVec]
  rw [← hstep, inv_smul_smul₀ hsnθ]

end Reconstruct

/-! ### Choices of the sample principal direction -/

/-- A choice, for every `p`, of a unit eigenvector `w⁽ᵖ⁾ⱼ` of the observable dual Gram matrix
`W⁽ᵖ⁾` at its `j`-th eigenvalue `θ⁽ᵖ⁾ⱼ`, together with the sample principal direction
`h_j ∈ ℝ^p` that Gram duality reconstructs from it.  Each of the three conditions is imposed
only for large `p`. -/
structure PrincipalDirectionSeq (j : Fin M.k) (ω : Ω) where
  /-- The chosen unit eigenvectors `w⁽ᵖ⁾ⱼ` of the observable dual Gram matrix. -/
  dual : ℕ → EuclideanSpace ℝ (Fin M.n)
  /-- The reconstructed sample principal directions `h_j ∈ ℝ^p`. -/
  sample : (p : ℕ) → EuclideanSpace ℝ (Fin p)
  /-- The dual eigenvectors are unit vectors. -/
  norm_dual : ∀ᶠ p in atTop, ‖dual p‖ = 1
  /-- The dual eigenvectors sit at the `j`-th eigenvalue `θ⁽ᵖ⁾ⱼ` of `W⁽ᵖ⁾`. -/
  dualGram_mulVec_dual : ∀ᶠ p in atTop, M.dualGram p ω *ᵥ dual p
    = M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j) • dual p
  /-- `h_j` is the vector Gram duality reconstructs from `w⁽ᵖ⁾ⱼ`. -/
  sqrt_smul_sample : ∀ᶠ p in atTop,
    Real.sqrt ((M.n : ℝ) * p * M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j)) • sample p
      = M.dataMatrix p ω *ᵥ dual p

/-! ### The limit of the principal coordinate -/

/-- The limiting systematic scale `nx + δ²` of a positive `x` is positive. -/
theorem n_mul_add_δsq_pos {x : ℝ} (hx : 0 < x) : 0 < (M.n : ℝ) * x + M.δsq :=
  add_pos (mul_pos (by exact_mod_cast M.n_pos) hx) M.δsq_pos

variable [MeasurableSpace Ω] {μ : Measure Ω} {G : Matrix (Fin M.k) (Fin M.k) ℝ}
  {lam : Fin M.k → ℝ}

/-- The observed principal-coordinate scores `Φ̄⁽ᵖ⁾ + p^{-1/2}(b⁽ᵖ⁾)ᵀZ⁽ᵖ⁾` of
`PCError.FactorModelSeq.transpose_b_mulVec_eq_smul` converge almost surely to `Φ̄^∞`. -/
theorem ae_tendsto_scaledScores_add_transpose_b_mul_noiseMatrix
    (hyp : StandingHypotheses μ M G lam) :
    ∀ᵐ ω ∂μ, Tendsto (fun p : ℕ => M.scaledScores p
        + (Real.sqrt p)⁻¹ • ((M.b p)ᵀ * M.noiseMatrix p ω)) atTop (𝓝 M.scaledScoresLim) := by
  filter_upwards [M.ae_tendsto_transpose_b_mul_noiseMatrix hyp.toAsymptoticHypotheses] with ω hω
  simpa using hyp.tendsto_scaledScores.add hω

/-- The reconstructed sample principal directions are eventually unit vectors. -/
theorem ae_eventually_norm_sample_eq_one (hslln : KolmogorovSLLN.{u})
    (hweyl : WeylPerturbation.{0}) (hyp : StandingHypotheses μ M G lam) (j : Fin M.k) :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω, ∀ᶠ p in atTop, ‖s.sample p‖ = 1 := by
  filter_upwards [M.ae_tendsto_dualEigenvalues hslln hweyl hyp j] with ω hθ s
  filter_upwards [hθ.eventually_const_lt (M.lam_add_div_pos hyp.toAsymptoticHypotheses j),
    s.norm_dual, s.dualGram_mulVec_dual, s.sqrt_smul_sample, eventually_gt_atTop 0]
    with p h1 h2 h3 h4 h5
  exact M.norm_eq_one_of_sqrt_smul_eq_dataMatrix_mulVec h5.ne' h1.ne' h2 h3 h4

/-- **The limit of the principal coordinate**: almost surely there are signs `ς⁽ᵖ⁾ ∈ {±1}` with
`ς⁽ᵖ⁾(b⁽ᵖ⁾)ᵀh_j → √(nλⱼ/(nλⱼ+δ²)) νⱼ`, where `νⱼ` is the unit eigenvector of `N` at `λⱼ` that
Gram duality attaches to the eigenvector `wⱼ` of `W₀`. -/
@[pcerror "prop_coord_limit"]
theorem ae_exists_sign_tendsto_transpose_b_mulVec (hslln : KolmogorovSLLN.{u})
    (hweyl : WeylPerturbation.{0}) (hyp : StandingHypotheses μ M G lam) (j : Fin M.k)
    {w : EuclideanSpace ℝ (Fin M.n)} (hw1 : ‖w‖ = 1)
    (hw : M.dualGramLim₀ G *ᵥ w = lam j • w) {ν : EuclideanSpace ℝ (Fin M.k)}
    (hν : M.scaledScoresLim *ᵥ w = Real.sqrt ((M.n : ℝ) * lam j) • ν) :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω, ∃ ς : ℕ → ℝ, (∀ p, ς p = 1 ∨ ς p = -1) ∧
      Tendsto (fun p => ς p • Matrix.toEuclideanLin (M.b p)ᵀ (s.sample p)) atTop
        (𝓝 (Real.sqrt ((M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)) • ν)) := by
  classical
  have hlam : 0 < lam j := hyp.hasPosEigenvalues_dualGramLim₀.pos j
  have hsL : Real.sqrt ((M.n : ℝ) * lam j + M.δsq) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (M.n_mul_add_δsq_pos hlam)
  have hfin : (Real.sqrt ((M.n : ℝ) * lam j + M.δsq))⁻¹ • (Real.sqrt ((M.n : ℝ) * lam j) • ν)
      = Real.sqrt ((M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)) • ν := by
    rw [smul_smul, Real.sqrt_div (by positivity), div_eq_inv_mul]
  filter_upwards [M.ae_tendsto_dualEigenvalues hslln hweyl hyp j,
    M.ae_tendsto_scaledScores_add_transpose_b_mul_noiseMatrix hyp,
    M.ae_tendsto_abs_inner_dualEigenvector hslln hweyl hyp j hw1 hw] with ω hθ hC habs s
  have habs' : Tendsto (fun p => |⟪s.dual p, w⟫|) atTop (𝓝 1) :=
    habs s.dual (s.norm_dual.and s.dualGram_mulVec_dual)
  have hpin : Tendsto (fun p => Real.sign ⟪s.dual p, w⟫ • s.dual p) atTop (𝓝 w) :=
    tendsto_real_sign_inner_smul s.norm_dual hw1 habs'
  have hlim : Matrix.toEuclideanLin M.scaledScoresLim w
      = Real.sqrt ((M.n : ℝ) * lam j) • ν := congrArg (WithLp.toLp 2) hν
  have hmv := tendsto_toEuclideanLin hC hpin
  rw [hlim] at hmv
  have hscal : Tendsto (fun p : ℕ =>
      (Real.sqrt ((M.n : ℝ) * M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j)))⁻¹) atTop
      (𝓝 (Real.sqrt ((M.n : ℝ) * lam j + M.δsq))⁻¹) := by
    have hn : (M.n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.n_pos.ne'
    have h1 := hθ.const_mul ((M.n : ℝ))
    rw [show (M.n : ℝ) * (lam j + M.δsq / M.n) = (M.n : ℝ) * lam j + M.δsq by field_simp] at h1
    exact h1.sqrt.inv₀ hsL
  have hmain : Tendsto (fun p => Real.sign ⟪s.dual p, w⟫ •
      Matrix.toEuclideanLin (M.b p)ᵀ (s.sample p)) atTop
      (𝓝 (Real.sqrt ((M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)) • ν)) := by
    rw [← hfin]
    refine (hscal.smul hmv).congr' ?_
    filter_upwards [eventually_ge_atTop M.k,
      hθ.eventually_const_lt (M.lam_add_div_pos hyp.toAsymptoticHypotheses j),
      s.sqrt_smul_sample] with p hp hθp hs
    have hE : Matrix.toEuclideanLin (M.b p)ᵀ (s.sample p)
        = (Real.sqrt ((M.n : ℝ) *
            M.dualEigenvalues p ω (Fin.castLE M.k_lt_n.le j)))⁻¹ •
          Matrix.toEuclideanLin (M.scaledScores p
            + (Real.sqrt p)⁻¹ • ((M.b p)ᵀ * M.noiseMatrix p ω)) (s.dual p) :=
      congrArg (WithLp.toLp 2) (M.transpose_b_mulVec_eq_smul hp hθp hs)
    rw [hE, map_smul, smul_comm]
  refine ⟨fun p => if ⟪s.dual p, w⟫ < 0 then -1 else 1, fun p => ?_, hmain.congr' ?_⟩
  · by_cases hp : ⟪s.dual p, w⟫ < 0 <;> simp [hp]
  · filter_upwards [eventually_inner_ne_zero habs'] with p hp
    rcases lt_trichotomy ⟪s.dual p, w⟫ 0 with hlt | he | hgt
    · rw [Real.sign_of_neg hlt, ite_eq_left hlt]
    · exact absurd he hp
    · rw [Real.sign_of_pos hgt, ite_eq_right (not_lt.2 hgt.le)]

/-! ### The in-subspace mass and the out-of-subspace error -/

section Limits

variable (hslln : KolmogorovSLLN.{u}) (hweyl : WeylPerturbation.{0})
  (hyp : StandingHypotheses μ M G lam) (j : Fin M.k) {w : EuclideanSpace ℝ (Fin M.n)}
  (hw1 : ‖w‖ = 1) (hw : M.dualGramLim₀ G *ᵥ w = lam j • w) {ν : EuclideanSpace ℝ (Fin M.k)}
  (hν : M.scaledScoresLim *ᵥ w = Real.sqrt ((M.n : ℝ) * lam j) • ν)

include hslln hweyl hyp hw1 hw hν

/-- **In-subspace mass**: almost surely `cos²∠(h_j, 𝓑) → nλⱼ/(nλⱼ+δ²)`. -/
@[pcerror "thm_insub_mass"]
theorem ae_tendsto_one_sub_sinSqAngleSubspace :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
      Tendsto (fun p => 1 - sinSqAngleSubspace (s.sample p) (M.principalSubspace p)) atTop
        (𝓝 ((M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq))) := by
  have hlam : 0 < lam j := hyp.hasPosEigenvalues_dualGramLim₀.pos j
  have hδ := M.δsq_pos
  have hν1 : ‖ν‖ = 1 :=
    M.norm_eq_one_of_sqrt_smul_eq_scaledScoresLim_mulVec hyp.gram_scaledScoresLim hlam.ne'
      hw1 hw hν.symm
  have hval : ‖Real.sqrt ((M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)) • ν‖ ^ 2
      = (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq) := by
    rw [norm_smul, Real.norm_eq_abs, hν1, mul_one, sq_abs,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq))]
  filter_upwards [M.ae_exists_sign_tendsto_transpose_b_mulVec hslln hweyl hyp j hw1 hw hν,
    M.ae_eventually_norm_sample_eq_one hslln hweyl hyp j] with ω hex hnorm s
  obtain ⟨ς, hς, hlimit⟩ := hex s
  have h1 := hlimit.norm.pow 2
  rw [hval] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop M.k, hnorm s] with p hp hn
  have habs1 : |ς p| = 1 := by rcases hς p with h | h <;> simp [h]
  rw [M.one_sub_sinSqAngleSubspace_principalSubspace hp hn, norm_smul, Real.norm_eq_abs, habs1,
    one_mul]

/-- **Out-of-subspace error**: almost surely `sin²∠(h_j, 𝓑) → δ²/(nλⱼ+δ²)`, the complement of
the in-subspace mass. -/
@[pcerror "thm_oos_limit"]
theorem ae_tendsto_sinSqAngleSubspace :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
      Tendsto (fun p => sinSqAngleSubspace (s.sample p) (M.principalSubspace p)) atTop
        (𝓝 (M.δsq / ((M.n : ℝ) * lam j + M.δsq))) := by
  have hLne : ((M.n : ℝ) * lam j + M.δsq) ≠ 0 :=
    (M.n_mul_add_δsq_pos (hyp.hasPosEigenvalues_dualGramLim₀.pos j)).ne'
  have he : (1 : ℝ) - (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)
      = M.δsq / ((M.n : ℝ) * lam j + M.δsq) := by
    field_simp
    ring
  filter_upwards [M.ae_tendsto_one_sub_sinSqAngleSubspace hslln hweyl hyp j hw1 hw hν]
    with ω hcos s
  simpa [he] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub (hcos s)

/-- **The projection is eventually nonzero**: almost surely `Π h_j ≠ 0` for all large `p`. -/
@[pcerror "lem_proj_nonzero"]
theorem ae_eventually_starProjection_ne_zero :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
      ∀ᶠ p in atTop, (M.principalSubspace p).starProjection (s.sample p) ≠ 0 := by
  have hlam : 0 < lam j := hyp.hasPosEigenvalues_dualGramLim₀.pos j
  have hpos : 0 < (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq) :=
    div_pos (mul_pos (by exact_mod_cast M.n_pos) hlam) (M.n_mul_add_δsq_pos hlam)
  filter_upwards [M.ae_tendsto_one_sub_sinSqAngleSubspace hslln hweyl hyp j hw1 hw hν]
    with ω hcos s
  filter_upwards [(hcos s).eventually_const_lt hpos] with p hp h0
  simp [sinSqAngleSubspace, h0] at hp

/-- **In-subspace rotation error**: almost surely `sin²∠(Π h_j, b⁽ᵖ⁾ⱼ) → sin²∠(νⱼ, eⱼ)`. -/
@[pcerror "thm_rotation_limit"]
theorem ae_tendsto_sinSqAngle_starProjection :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
      Tendsto (fun p => sinSqAngle ((M.principalSubspace p).starProjection (s.sample p))
        (M.principalDirection p j)) atTop
        (𝓝 (sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)))) := by
  have hlam : 0 < lam j := hyp.hasPosEigenvalues_dualGramLim₀.pos j
  have hκ : 0 < Real.sqrt ((M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)) :=
    Real.sqrt_pos.2
      (div_pos (mul_pos (by exact_mod_cast M.n_pos) hlam) (M.n_mul_add_δsq_pos hlam))
  have hν1 : ‖ν‖ = 1 :=
    M.norm_eq_one_of_sqrt_smul_eq_scaledScoresLim_mulVec hyp.gram_scaledScoresLim hlam.ne'
      hw1 hw hν.symm
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.1 (by simp [hν1])
  have hej : (EuclideanSpace.single j (1 : ℝ)) ≠ 0 := norm_ne_zero_iff.1 (by simp)
  filter_upwards [M.ae_exists_sign_tendsto_transpose_b_mulVec hslln hweyl hyp j hw1 hw hν]
    with ω hex s
  obtain ⟨ς, hς, hlimit⟩ := hex s
  have hcont := tendsto_sinSqAngle (smul_ne_zero hκ.ne' hν0) hej hlimit
  rw [sinSqAngle_smul_left hκ.ne'] at hcont
  refine hcont.congr' ?_
  filter_upwards [eventually_ge_atTop M.k] with p hp
  have hςne : ς p ≠ 0 := by rcases hς p with h | h <;> simp [h]
  rw [sinSqAngle_smul_left hςne, M.sinSqAngle_starProjection_principalSubspace hp]

/-- **Error decomposition**: almost surely
`sin²∠(h_j, b⁽ᵖ⁾ⱼ) → δ²/(nλⱼ+δ²) + nλⱼ/(nλⱼ+δ²) sin²∠(νⱼ, eⱼ)`. -/
@[pcerror "thm_error_decomp"]
theorem ae_tendsto_sinSqAngle_principalDirection :
    ∀ᵐ ω ∂μ, ∀ s : M.PrincipalDirectionSeq j ω,
      Tendsto (fun p => sinSqAngle (s.sample p) (M.principalDirection p j)) atTop
        (𝓝 (M.δsq / ((M.n : ℝ) * lam j + M.δsq)
          + (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq)
            * sinSqAngle ν (EuclideanSpace.single j (1 : ℝ)))) := by
  have hLne : ((M.n : ℝ) * lam j + M.δsq) ≠ 0 :=
    (M.n_mul_add_δsq_pos (hyp.hasPosEigenvalues_dualGramLim₀.pos j)).ne'
  have he : (1 : ℝ) - M.δsq / ((M.n : ℝ) * lam j + M.δsq)
      = (M.n : ℝ) * lam j / ((M.n : ℝ) * lam j + M.δsq) := by
    field_simp
    ring
  filter_upwards [M.ae_tendsto_sinSqAngleSubspace hslln hweyl hyp j hw1 hw hν,
    M.ae_tendsto_sinSqAngle_starProjection hslln hweyl hyp j hw1 hw hν] with ω hoos hrot s
  have hsum := (hoos s).add
    (((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub (hoos s)).mul (hrot s))
  rw [he] at hsum
  exact hsum.congr' (Eventually.of_forall fun p =>
    (sinSqAngle_eq_sinSqAngleSubspace_add_mul_sinSqAngle_starProjection (s.sample p)
      (M.principalSubspace p) (M.principalDirection_mem_principalSubspace p j)).symm)

end Limits

end FactorModelSeq

end PCError

end
