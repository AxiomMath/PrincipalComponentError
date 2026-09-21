/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Probability.Moments.Variance
public import PCError.Attr
public import PCError.Defs.TheFactorModelAndItsDerivedMatrices

/-!
# The principal directions, and two classical results the source cites

Besides `PCError.FactorModelSeq.principalDirection`, this module states the two
classical results the source cites rather than proves, and which Mathlib does not
have at the pinned revision.

Both are proved here, so neither is an assumption: `PCError.KolmogorovSLLN` by
`PCError.kolmogorovSLLN` in `PCError.SLLN.Basic`, and `PCError.WeylPerturbation`
by `PCError.weylPerturbation` in `PCError.Weyl.Basic`.  Nothing takes either as a
hypothesis; each is packaged as a `Prop`-valued *definition*, which is the form
its theorem is stated in and the form a consumer applies.

Eigenvector continuity at a simple eigenvalue, which the source proves as its
Lemma 2, is proved here too, in
`PCError.tendsto_abs_inner_of_tendsto_eigenvalue`.

## Main definitions

* `PCError.FactorModelSeq.principalDirection`: the `j`-th principal direction
  `b⁽ᵖ⁾ⱼ`, the `j`-th column of the principal frame read in `ℝ^p`.
* `PCError.KolmogorovSLLN`: Kolmogorov's strong law of large numbers for
  independent, not necessarily identically distributed summands with
  `∑ᵢ Var(Xᵢ)/i² < ∞`.
* `PCError.WeylPerturbation`: Weyl's eigenvalue perturbation inequality — the
  `i`-th largest eigenvalue of a real symmetric matrix is `1`-Lipschitz in the
  ℓ²-operator norm.

## Implementation notes

`Matrix.instL2OpNormedAddCommGroup` — the ℓ²-operator (spectral) norm on
matrices, obtained by identifying a matrix with a continuous linear map between
Euclidean spaces — is not a global instance in Mathlib, so it is installed here
as a `local instance`.  It is the norm `‖A' - A‖` in `PCError.WeylPerturbation`
refers to.  A downstream file that wants to *rewrite* that norm should install
the same local instance and use `Matrix.l2_opNorm_def` or
`Matrix.l2_opNorm_toEuclideanCLM`; merely *applying* the hypothesis needs
nothing, since the instance is already fixed in its statement.

Eigenvalues of a symmetric matrix are read off through
`Matrix.IsHermitian.eigenvalues₀ : Fin (Fintype.card n) → ℝ`, which lists them in
weakly decreasing order (`Matrix.IsHermitian.eigenvalues₀_antitone`); this is the
listing `λ₁ ≥ ⋯ ≥ λₘ` of the source, and the one `dualEigenvalues` is built from.
-/

@[expose] public section

namespace PCError

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace

universe u

namespace FactorModelSeq

variable {Ω : Type u} (M : FactorModelSeq Ω)

/-- The `j`-th *principal direction* `b⁽ᵖ⁾ⱼ ∈ ℝ^p`: the `j`-th column of the principal
frame. -/
def principalDirection (p : ℕ) (j : Fin M.k) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 ((M.b p)ᵀ j)

end FactorModelSeq

attribute [local instance] Matrix.instL2OpNormedAddCommGroup

/-! ### Kolmogorov's strong law of large numbers -/

/-- **Kolmogorov's strong law of large numbers** for independent, not necessarily
identically distributed summands: if the real random variables `X i` on a
probability space are independent with finite variances satisfying
`∑ᵢ Var(Xᵢ)/i² < ∞`, then `p⁻¹ ∑_{i < p} (Xᵢ - 𝔼[Xᵢ]) → 0` almost surely.

This is a result the source cites rather than proves, and it is not in Mathlib:
`ProbabilityTheory.strong_law_ae` is the i.i.d. strong law, which assumes
identical distributions and concludes convergence to a common mean, and neither
its hypotheses nor its conclusion cover the variance criterion below.

Reference: A. N. Kolmogorov, *Sur la loi forte des grands nombres*, C. R. Acad.
Sci. Paris **191** (1930), 910–912; in the form stated here, S. I. Resnick,
*A Probability Path*, Birkhäuser, 1999, Corollary 7.4.1 (see also W. Feller,
*An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.,
Wiley, 1968, Ch. X.7, where the hypothesis is called Kolmogorov's criterion).

`MemLp (X i) 2 μ` is the finite-variance hypothesis, and it also supplies the
measurability of `X i` and the integrability making `μ[X i]` meaningful.  The
source indexes the summands from `1`; here they are indexed from `0`, so its
`∑ᵢ Var(Xᵢ)/i²` is the sum below over `((i : ℝ) + 1) ^ 2`.

Proved in this development, as `PCError.kolmogorovSLLN` in
`PCError.SLLN.Basic`, which is where the `lem_slln` tag sits. -/
def KolmogorovSLLN : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ), (∀ i, MemLp (X i) 2 μ) → iIndepFun X μ →
    (Summable fun i : ℕ => Var[X i; μ] / ((i : ℝ) + 1) ^ 2) →
    ∀ᵐ ω ∂μ, Tendsto
      (fun p : ℕ => (p : ℝ)⁻¹ * ∑ i ∈ Finset.range p, (X i ω - μ[X i])) atTop (𝓝 0)

/-! ### Weyl's eigenvalue perturbation inequality -/

/-- **Weyl's eigenvalue perturbation inequality**: for real symmetric matrices
`A` and `A'` with eigenvalues listed in weakly decreasing order, the `i`-th
eigenvalues differ by at most the ℓ²-operator norm of `A' - A`.  Equivalently,
each `λᵢ` is a `1`-Lipschitz function on the symmetric matrices.

This is a result the source cites rather than proves, and it is not in Mathlib
at the pinned revision: the ordered eigenvalues `Matrix.IsHermitian.eigenvalues₀`
are available, but no perturbation bound on them is.

Reference: H. Weyl, *Das asymptotische Verteilungsgesetz der Eigenwerte linearer
partieller Differentialgleichungen*, Math. Ann. **71** (1912), 441–479; in the
form stated here, R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed.,
Cambridge University Press, 2013, Corollary 4.3.15 (a corollary of Weyl's
inequalities, Theorem 4.3.1).

The norm is the one described in the module docstring; symmetry of *both*
matrices is essential, the bound failing badly for non-normal perturbations.

Proved in this development, as `PCError.abs_eigenvalues₀_sub_le` in
`PCError.Weyl.Basic`, which is where the `lem_weyl` tag sits;
`PCError.weylPerturbation` there is the same result in this packaged form. -/
def WeylPerturbation : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n] {A A' : Matrix n n ℝ}
    (hA : A.IsHermitian) (hA' : A'.IsHermitian) (i : Fin (Fintype.card n)),
    |hA'.eigenvalues₀ i - hA.eigenvalues₀ i| ≤ ‖A' - A‖

end PCError

end
