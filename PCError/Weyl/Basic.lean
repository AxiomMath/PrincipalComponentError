/-
Copyright (c) 2026 Marcel Morgenstern, Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern, Ken Ono
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import PCError.Attr
public import PCError.External
public import PCError.Weyl.CourantFischer

/-!
# Weyl's eigenvalue perturbation inequality

`PCError.WeylPerturbation` is stated in `PCError.External` as one of the results the source
cites rather than proves.  It is proved here, so a theorem that took it as a hypothesis can be
discharged: the sorted eigenvalues `Matrix.IsHermitian.eigenvalues₀` of real symmetric matrices
are `1`-Lipschitz in the ℓ²-operator norm.

The mathematical content is the Courant–Fischer variational bound of
`PCError.Weyl.CourantFischer`, applied to the symmetric operators
`Matrix.toEuclideanLin A` and `Matrix.toEuclideanLin A'` on `EuclideanSpace ℝ n`; what is left is
the estimate `|⟪A v, v⟫| ≤ ‖A‖ * ‖v‖ ^ 2`, read at `A - A'`, which is Cauchy–Schwarz followed by
the defining bound `Matrix.l2_opNorm_mulVec` of the operator norm.

## Main statements

* `PCError.abs_inner_toEuclideanLin_le`: the quadratic form of a matrix is bounded by the operator
  norm, `|⟪A v, v⟫| ≤ ‖A‖ * ‖v‖ ^ 2`.
* `PCError.abs_eigenvalues₀_sub_le`: **Weyl's eigenvalue perturbation inequality**,
  `|λᵢ(A) - λᵢ(A')| ≤ ‖A - A'‖`, as a standalone theorem.
* `PCError.weylPerturbation`: the same statement in the packaged form
  `PCError.WeylPerturbation`, so that it can be fed to the theorems that assume it.

## Implementation notes

This development is adapted from the Apache-2.0 licensed file
`ErgodicTheory/Lyapunov/ExteriorNorm/Weyl.lean` of the repository
<https://github.com/marcmorningstar/lean4-ergodic-theory>, at revision
`162efaa9bc24abb10f07eb8710d2e93a6c2cabed`, by Marcel Morgenstern.
That file states its matrix corollary for `Matrix (Fin d) (Fin d) ℝ`; here the index type is an
arbitrary `Fintype`, which costs nothing because `Matrix.toEuclideanLin` and
`finrank_euclideanSpace` are already stated at that generality.

`Matrix.instL2OpNormedAddCommGroup` is installed as a `local instance`, exactly as in
`PCError.External`: it is not a global instance in Mathlib, and it is the norm
`PCError.WeylPerturbation` speaks of.

`Matrix.IsHermitian.eigenvalues₀` is *by definition* the sorted `eigenvalues` of
`Matrix.toEuclideanLin A` read at `finrank_euclideanSpace`, so the two indexings agree by `rfl`.
-/

@[expose] public section

namespace PCError

open Matrix
open scoped RealInnerProductSpace

attribute [local instance] Matrix.instL2OpNormedAddCommGroup

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Cauchy–Schwarz against the ℓ²-operator norm: the quadratic form of a matrix, read on
`EuclideanSpace ℝ n`, is bounded by `‖A‖ * ‖v‖ ^ 2`. -/
theorem abs_inner_toEuclideanLin_le (A : Matrix n n ℝ) (v : EuclideanSpace ℝ n) :
    |⟪toEuclideanLin A v, v⟫| ≤ ‖A‖ * ‖v‖ ^ 2 := by
  calc |⟪toEuclideanLin A v, v⟫|
      ≤ ‖toEuclideanLin A v‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖A‖ * ‖v‖ * ‖v‖ := by gcongr; exact Matrix.l2_opNorm_mulVec A v
    _ = ‖A‖ * ‖v‖ ^ 2 := by ring

/-- **Weyl's eigenvalue perturbation inequality.**  The eigenvalues of real symmetric matrices,
listed in weakly decreasing order by `Matrix.IsHermitian.eigenvalues₀`, are `1`-Lipschitz in the
ℓ²-operator norm: the `i`-th eigenvalues of `A` and `A'` differ by at most `‖A - A'‖`. -/
@[pcerror "lem_weyl"]
theorem abs_eigenvalues₀_sub_le {A A' : Matrix n n ℝ} (hA : A.IsHermitian) (hA' : A'.IsHermitian)
    (i : Fin (Fintype.card n)) : |hA.eigenvalues₀ i - hA'.eigenvalues₀ i| ≤ ‖A - A'‖ := by
  have hTA : (toEuclideanLin A).IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  have hTA' : (toEuclideanLin A').IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA'
  refine LinearMap.IsSymmetric.abs_eigenvalues_sub_le hTA finrank_euclideanSpace hTA'
    (fun v => ?_) i
  have hlin : (toEuclideanLin A - toEuclideanLin A') v = toEuclideanLin (A - A') v := by
    simp only [LinearMap.sub_apply, map_sub]
  rw [hlin]
  exact abs_inner_toEuclideanLin_le (A - A') v

/-- Weyl's eigenvalue perturbation inequality, in the packaged form `PCError.WeylPerturbation`
in which `PCError.External` states it. -/
theorem weylPerturbation : WeylPerturbation.{u} :=
  fun hA hA' i => abs_eigenvalues₀_sub_le hA' hA i

end PCError

end
