/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import PCError.Attr

/-!
# The sample subspace projector

A *frame* is a matrix `H : Matrix m n R`, read as the list `h₁, …, hₙ` of its columns
in `Rᵐ`. It carries a square matrix `H Hᴴ`, and as soon as the columns are
orthonormal — the single equation `Hᴴ * H = 1` — that square matrix is the
orthogonal projector onto their span. This file defines it, together with the frame
of eigenvectors of a Hermitian matrix cut out by a choice of eigenvalue indices.

In the notation of the paper, `H⁽ᵖ⁾ = [h₁ ⋯ h_k]` collects `k` orthonormal
eigenvectors of the sample covariance `S⁽ᵖ⁾` and `Π_H = H⁽ᵖ⁾ (H⁽ᵖ⁾)ᵀ`; that is
`frameProj (eigenvectorFrame hS f)` for `f : Fin k → Fin p` the choice of the `k`
largest eigenvalues.

## Main definitions

* `PCError.frameProj H`: the matrix `H Hᴴ`, written `Π_H` in the paper.
* `PCError.eigenvectorFrame hA f`: the frame whose columns are the eigenvectors of a
  Hermitian matrix `A` indexed by `f`.

## Main statements

* `PCError.isStarProjection_frameProj`: for a frame with orthonormal columns,
  `Π_H` is a self-adjoint idempotent, i.e. an orthogonal projector.
* `PCError.range_mulVecLin_frameProj`: it projects onto the column span of `H`.
* `PCError.trace_frameProj_eq_card`: its trace is the number of columns.
* `PCError.conjTranspose_eigenvectorFrame_mul_self` and `PCError.mul_eigenvectorFrame`:
  the columns of `eigenvectorFrame hA f` are orthonormal, and are eigenvectors of `A`.
* `PCError.isStarProjection_frameProj_eigenvectorFrame`: the projector cut out by an
  injective selection of eigenvectors of a Hermitian matrix is an orthogonal projector.

## Implementation notes

`PCError.frameProj` is defined for an arbitrary frame rather than for a frame of
eigenvectors: self-adjointness, idempotence, the identification of its range with the
span of the columns of `H`, and the value of its trace all follow from the single
equation `Hᴴ * H = 1`, so the eigenvector input enters only through that equation.
-/

@[expose] public section

open Matrix

namespace PCError

variable {m n R : Type*}

/-! ### The projector attached to a frame -/

section Frame

variable [Fintype n]

section

variable [NonUnitalNonAssocSemiring R] [Star R] (H : Matrix m n R)

/-- `PCError.frameProj H` is the matrix `H Hᴴ` attached to a frame `H`, i.e. to a
finite list of vectors presented as the columns of `H`. When those columns are
orthonormal, `Hᴴ * H = 1`, it is the orthogonal projector onto their span
(`PCError.isStarProjection_frameProj`, `PCError.range_mulVecLin_frameProj`); this is
the matrix `Π_H`. -/
@[pcerror "def_PiH"]
def frameProj : Matrix m m R := H * Hᴴ

/-- The defining formula for `frameProj`, so that it can be used without unfolding the
definition. -/
theorem frameProj_def : frameProj H = H * Hᴴ := rfl

/-- Over a trivial star operation — in particular over `ℝ`, the setting of the paper —
the projector attached to a frame is `H Hᵀ`. -/
theorem frameProj_eq_mul_transpose [TrivialStar R] : frameProj H = H * Hᵀ := by
  rw [frameProj_def, conjTranspose_eq_transpose_of_trivial]

end

variable [NonUnitalSemiring R] [StarRing R] (H : Matrix m n R)

/-- The projector attached to a frame is Hermitian. -/
theorem isHermitian_frameProj : (frameProj H).IsHermitian :=
  isHermitian_mul_conjTranspose_self H

/-- The projector attached to a frame is its own conjugate transpose. -/
@[simp]
theorem conjTranspose_frameProj : (frameProj H)ᴴ = frameProj H :=
  isHermitian_frameProj H

/-- Over a trivial star operation — in particular over `ℝ`, the setting of the paper —
the projector attached to a frame is its own transpose. -/
@[simp]
theorem transpose_frameProj [TrivialStar R] : (frameProj H)ᵀ = frameProj H := by
  rw [← conjTranspose_eq_transpose_of_trivial, conjTranspose_frameProj]

/-- The projector attached to a frame is a self-adjoint element of the matrix ring. -/
theorem isSelfAdjoint_frameProj : IsSelfAdjoint (frameProj H) :=
  isHermitian_frameProj H

end Frame

section Trace

variable [Fintype m] [Fintype n] [NonUnitalCommSemiring R] [StarRing R]

/-- The projector `H Hᴴ` attached to a frame and the Gram matrix `Hᴴ H` of its columns
have the same trace. -/
theorem trace_frameProj (H : Matrix m n R) : (frameProj H).trace = (Hᴴ * H).trace :=
  trace_mul_comm H Hᴴ

end Trace

section PosSemidef

variable [Fintype n] [Finite m] [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

/-- The projector attached to a frame is positive semidefinite. -/
theorem posSemidef_frameProj (H : Matrix m n R) : (frameProj H).PosSemidef := by
  simpa [frameProj_def] using posSemidef_conjTranspose_mul_self Hᴴ

end PosSemidef

/-! ### The projector attached to a frame with orthonormal columns -/

section Orthonormal

variable [Fintype m] [Fintype n] [DecidableEq n] [CommSemiring R] [StarRing R]
  {H : Matrix m n R}

/-- A frame with orthonormal columns is fixed by its own projector: `Π_H H = H`. -/
theorem frameProj_mul_self_frame (h : Hᴴ * H = 1) : frameProj H * H = H := by
  rw [frameProj_def, Matrix.mul_assoc, h, Matrix.mul_one]

/-- The projector of a frame with orthonormal columns is idempotent: `Π_H Π_H = Π_H`. -/
theorem isIdempotentElem_frameProj (h : Hᴴ * H = 1) : IsIdempotentElem (frameProj H) := by
  change frameProj H * frameProj H = frameProj H
  rw [frameProj_def, Matrix.mul_assoc, ← Matrix.mul_assoc Hᴴ H Hᴴ, h, Matrix.one_mul]

/-- For a frame with orthonormal columns, `Π_H = H Hᴴ` is an orthogonal projector: a
self-adjoint idempotent. -/
theorem isStarProjection_frameProj (h : Hᴴ * H = 1) : IsStarProjection (frameProj H) :=
  ⟨isIdempotentElem_frameProj h, isSelfAdjoint_frameProj H⟩

/-- The projector of a frame with orthonormal columns fixes every vector in the column
span of `H`. -/
theorem frameProj_mulVec_mulVec (h : Hᴴ * H = 1) (x : n → R) :
    frameProj H *ᵥ (H *ᵥ x) = H *ᵥ x := by
  rw [Matrix.mulVec_mulVec, frameProj_mul_self_frame h]

/-- A frame with orthonormal columns and its projector have the same range: `Π_H` is
the projection *onto the span of the columns of `H`*. -/
theorem range_mulVecLin_frameProj (h : Hᴴ * H = 1) :
    LinearMap.range (frameProj H).mulVecLin = LinearMap.range H.mulVecLin := by
  refine le_antisymm ?_ ?_
  · rw [frameProj_def, mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · conv_lhs => rw [← frameProj_mul_self_frame h]
    rw [mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _

/-- The projector of a frame with `n` orthonormal columns has trace `n`. -/
theorem trace_frameProj_eq_card (h : Hᴴ * H = 1) :
    (frameProj H).trace = (Fintype.card n : R) := by
  rw [trace_frameProj, h, trace_one]

end Orthonormal

section Submatrix

variable [Fintype m] [DecidableEq m] [DecidableEq n] [Semiring R] [StarRing R]

/-- Selecting the columns of a matrix with orthonormal columns along an injective map
again gives a frame with orthonormal columns. -/
theorem conjTranspose_submatrix_mul_self {U : Matrix m m R} (hU : Uᴴ * U = 1) {f : n → m}
    (hf : Function.Injective f) : (U.submatrix id f)ᴴ * U.submatrix id f = 1 := by
  ext i j
  have hij := congrFun (congrFun hU (f i)) (f j)
  simp only [mul_apply, conjTranspose_apply, submatrix_apply, id_eq, one_apply] at hij ⊢
  rw [hij]
  simp [hf.eq_iff]

end Submatrix

/-! ### The frame of a selection of eigenvectors of a Hermitian matrix -/

section EigenvectorFrame

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype m] [DecidableEq m] {A : Matrix m m 𝕜}

/-- `PCError.eigenvectorFrame hA f` is the frame whose `j`-th column is the
eigenvector `hA.eigenvectorBasis (f j)` of the Hermitian matrix `A`: the eigenvectors
of `A` selected, with multiplicity, by `f`. Its columns are orthonormal whenever `f`
is injective (`PCError.conjTranspose_eigenvectorFrame_mul_self`), and they are
eigenvectors of `A` (`PCError.mul_eigenvectorFrame`). For `A = S⁽ᵖ⁾` the sample
covariance and `f` the choice of the `k` largest eigenvalues this is the matrix
`H⁽ᵖ⁾ = [h₁ ⋯ h_k]`. -/
@[pcerror "def_PiH"]
noncomputable def eigenvectorFrame (hA : A.IsHermitian) (f : n → m) : Matrix m n 𝕜 :=
  (hA.eigenvectorUnitary : Matrix m m 𝕜).submatrix id f

/-- The defining formula for `eigenvectorFrame`, so that it can be used without
unfolding the definition. -/
theorem eigenvectorFrame_def (hA : A.IsHermitian) (f : n → m) :
    eigenvectorFrame hA f = (hA.eigenvectorUnitary : Matrix m m 𝕜).submatrix id f := rfl

/-- The `(i, j)` entry of `PCError.eigenvectorFrame hA f` is the `i`-th coordinate of the
eigenvector `hA.eigenvectorBasis (f j)`. -/
@[simp]
theorem eigenvectorFrame_apply (hA : A.IsHermitian) (f : n → m) (i : m) (j : n) :
    eigenvectorFrame hA f i j = (hA.eigenvectorBasis (f j)).ofLp i :=
  hA.eigenvectorUnitary_apply i (f j)

/-- The columns of `PCError.eigenvectorFrame hA f` are orthonormal: they are distinct
members of an orthonormal eigenbasis. -/
theorem conjTranspose_eigenvectorFrame_mul_self [DecidableEq n] (hA : A.IsHermitian)
    {f : n → m} (hf : Function.Injective f) :
    (eigenvectorFrame hA f)ᴴ * eigenvectorFrame hA f = 1 :=
  conjTranspose_submatrix_mul_self
    (by simpa [star_eq_conjTranspose] using UnitaryGroup.star_mul_self hA.eigenvectorUnitary) hf

/-- The columns of `PCError.eigenvectorFrame hA f` are eigenvectors of `A`, with
eigenvalues `hA.eigenvalues ∘ f`. -/
theorem mul_eigenvectorFrame [Fintype n] [DecidableEq n] (hA : A.IsHermitian) (f : n → m) :
    A * eigenvectorFrame hA f
      = eigenvectorFrame hA f * diagonal (fun j => (hA.eigenvalues (f j) : 𝕜)) := by
  ext i j
  have h := congrFun (hA.mulVec_eigenvectorBasis (f j)) i
  rw [mul_diagonal, mul_apply]
  simpa [mulVec, dotProduct, RCLike.real_smul_eq_coe_mul, mul_comm] using h

/-- The projector cut out by a selection of eigenvectors of a Hermitian matrix — the
matrix `Π_H` — is an orthogonal projector. -/
theorem isStarProjection_frameProj_eigenvectorFrame [Fintype n] (hA : A.IsHermitian)
    {f : n → m} (hf : Function.Injective f) :
    IsStarProjection (frameProj (eigenvectorFrame hA f)) := by
  classical
  exact isStarProjection_frameProj (conjTranspose_eigenvectorFrame_mul_self hA hf)

end EigenvectorFrame

end PCError
