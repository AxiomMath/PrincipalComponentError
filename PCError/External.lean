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
# The principal directions, and classical results assumed as black boxes

Besides `PCError.FactorModelSeq.principalDirection`, this module collects the
three statements the development assumes.  It proves none of those three, and
none of the three is available in Mathlib at the pinned revision.  Two of them are
standard classical theorems that the source cites; the third the source proves
itself, and only this formalization leaves it unproved.

Each is packaged as a `Prop`-valued *definition*, not as an `axiom`.  A theorem
that needs one takes it as an explicit hypothesis, so the assumption is part of
the statement a reader sees rather than something only `#print axioms` reveals,
and every theorem of the development is unconditionally true.

A theorem receives only those of the three it actually uses, so its signature
records exactly which classical inputs it rests on.

## Main definitions

* `PCError.FactorModelSeq.principalDirection`: the `j`-th principal direction
  `b⁽ᵖ⁾ⱼ`, the `j`-th column of the principal frame read in `ℝ^p`.
* `PCError.KolmogorovSLLN`: Kolmogorov's strong law of large numbers for
  independent, not necessarily identically distributed summands with
  `∑ᵢ Var(Xᵢ)/i² < ∞`.
* `PCError.WeylPerturbation`: Weyl's eigenvalue perturbation inequality — the
  `i`-th largest eigenvalue of a real symmetric matrix is `1`-Lipschitz in the
  ℓ²-operator norm.
* `PCError.EigenpairContinuity`: continuity of the eigenvector at a simple
  eigenvalue, in the sequential form the source uses.

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

This development does not prove this statement; a theorem that uses it takes it
as an explicit hypothesis. -/
@[pcerror "lem_slln"]
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

This development does not prove this statement; a theorem that uses it takes it
as an explicit hypothesis. -/
@[pcerror "lem_weyl"]
def WeylPerturbation : Prop :=
  ∀ {n : Type*} [Fintype n] [DecidableEq n] {A A' : Matrix n n ℝ}
    (hA : A.IsHermitian) (hA' : A'.IsHermitian) (i : Fin (Fintype.card n)),
    |hA'.eigenvalues₀ i - hA.eigenvalues₀ i| ≤ ‖A' - A‖

/-! ### Eigenvector continuity at a simple eigenvalue -/

/-- **Continuity of the eigenvector at a simple eigenvalue**, in the sequential
form the source uses: if real symmetric matrices `A p` converge to a real
symmetric `A₀`, and `μ` is an eigenvalue of `A₀` whose unit eigenvectors are
exactly `±v`, then one can choose real numbers `lam p` and unit vectors `u p`
that are eigenpairs of `A p` for all large `p`, sign-normalised by
`0 ≤ ⟪u p, v⟫`, with `lam p → μ` and `u p → v`.

The source **proves** this rather than citing it: it is Lemma 2, stated on p. 23
and proved on pp. 23–24, from Weyl's inequality together with compactness of the
unit sphere and simplicity of the eigenvalue.  This development nevertheless
assumes it instead of proving it, which is why it is collected here beside the
two results the source really does cite.  The Kato reference below is for the
general fact, not for the source's treatment of it.

The simplicity hypothesis is what makes the statement true: eigenvectors of a
convergent family of symmetric matrices need not converge at a repeated
eigenvalue, only the eigenprojections do.

Reference: T. Kato, *Perturbation Theory for Linear Operators*, 2nd ed.,
Springer, 1976, Ch. II, §5.1 (continuity of the eigenvalues and eigenprojections
of a symmetric matrix under a convergent perturbation; §5.3 records the failure
without simplicity); see also G. W. Stewart and J.-G. Sun, *Matrix Perturbation
Theory*, Academic Press, 1990, §V.2.

Vectors are taken in `EuclideanSpace ℝ n` so that `‖·‖` and `⟪·, ·⟫` are the
Euclidean norm and inner product, while `Matrix.mulVec` still applies, exactly as
in `Matrix.IsHermitian.mulVec_eigenvectorBasis`.  Convergence of the matrices is
in the entrywise topology, which for a fixed finite index type is the topology of
every norm. -/
@[pcerror "lem_eigcont"]
def EigenpairContinuity : Prop :=
  ∀ {n : Type*} [Fintype n] {A : ℕ → Matrix n n ℝ} {A₀ : Matrix n n ℝ},
    (∀ p, (A p).IsHermitian) → A₀.IsHermitian → Tendsto A atTop (𝓝 A₀) →
    ∀ {μ : ℝ} {v : EuclideanSpace ℝ n}, ‖v‖ = 1 → A₀ *ᵥ v = μ • v →
    (∀ w : EuclideanSpace ℝ n, ‖w‖ = 1 → A₀ *ᵥ w = μ • w → w = v ∨ w = -v) →
    ∃ lam : ℕ → ℝ, ∃ u : ℕ → EuclideanSpace ℝ n,
      Tendsto lam atTop (𝓝 μ) ∧ Tendsto u atTop (𝓝 v) ∧
        ∀ᶠ p in atTop, A p *ᵥ u p = lam p • u p ∧ ‖u p‖ = 1 ∧ 0 ≤ ⟪u p, v⟫

end PCError

end
