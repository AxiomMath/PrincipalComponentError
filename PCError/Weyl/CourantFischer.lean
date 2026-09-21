/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The Courant–Fischer variational bound for a symmetric operator

Mathlib's `Mathlib/Analysis/InnerProductSpace/Rayleigh.lean` characterises only the *extreme*
eigenvalues of a self-adjoint operator, as a Rayleigh `iSup`/`iInf`.  What the Weyl perturbation
inequality needs is the per-index bound: the `i`-th sorted eigenvalue is bounded below on the span
of the top `i + 1` eigenvectors and above on the span of the bottom `n - i` ones, and those two
spans have dimensions summing to `n + 1`, so they meet in a nonzero vector.  That dimension count
is `PCError.LinearMap.IsSymmetric.eigenvalues_sub_le` below.

## Main definitions

* `PCError.LinearMap.IsSymmetric.eigenspan`: the span of those eigenvectors whose sorted index
  satisfies a given predicate, with `PCError.LinearMap.IsSymmetric.mem_eigenspan` and
  `PCError.LinearMap.IsSymmetric.finrank_eigenspan` describing its members and its dimension.

## Main statements

* `PCError.LinearMap.IsSymmetric.apply_inner_self_eq_sum`: the quadratic form `⟪T v, v⟫` expanded
  in the orthonormal eigenbasis.
* `PCError.LinearMap.IsSymmetric.le_apply_inner_self_of_mem_eigenspan_Iic`,
  `PCError.LinearMap.IsSymmetric.apply_inner_self_le_of_mem_eigenspan_Ici`: the two one-sided
  Rayleigh bounds on `PCError.LinearMap.IsSymmetric.eigenspan`.
* `PCError.LinearMap.IsSymmetric.eigenvalues_sub_le`: the Courant–Fischer dimension count — if
  `⟪(T - S) v, v⟫ ≤ C * ‖v‖ ^ 2` for every `v`, then `μᵢ(T) - μᵢ(S) ≤ C`.
* `PCError.LinearMap.IsSymmetric.abs_eigenvalues_sub_le`: **Weyl's inequality at the operator
  level** — if `|⟪(T - S) v, v⟫| ≤ C * ‖v‖ ^ 2` for every `v`, then `|μᵢ(T) - μᵢ(S)| ≤ C`.

## Implementation notes

This development is adapted from the Apache-2.0 licensed file
`ErgodicTheory/Lyapunov/ExteriorNorm/Weyl.lean` of the repository
<https://github.com/marcmorningstar/lean4-ergodic-theory>, at revision
`162efaa9bc24abb10f07eb8710d2e93a6c2cabed`, by Marcel Morgenstern.

Everything here is stated for a real inner product space, which is the only case the matrix
corollary in `PCError.Weyl.Basic` needs, and is where `⟪T v, v⟫` is a real number so that
`|·| ≤ C * ‖v‖ ^ 2` says what it should.  Eigenvalues are indexed by `Fin n` through
`LinearMap.IsSymmetric.eigenvalues`, which lists them in *weakly decreasing* order
(`LinearMap.IsSymmetric.eigenvalues_antitone`); `i ≤ j` therefore means `μⱼ ≤ μᵢ`.

`PCError.LinearMap.IsSymmetric.eigenvalues_sub_le` is proved by the Courant–Fischer dimension
count: the span of the top `i + 1` eigenvectors of `T` has dimension `i + 1` and the span of the
bottom `n - i` eigenvectors of `S` has dimension `n - i`, so their dimensions sum to `n + 1`;
since their join sits inside an `n`-dimensional space, they meet in a nonzero vector, on which the
two Rayleigh bounds collide.
-/

@[expose] public section

namespace PCError

open Module
open scoped RealInnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {T : E →ₗ[ℝ] E}

/-- Expansion of the quadratic form of a symmetric operator in its orthonormal eigenbasis:
`⟪T v, v⟫ = ∑ᵢ μᵢ * ⟪bᵢ, v⟫ ^ 2`, with `μ` the sorted eigenvalues and `b` the eigenvector
basis. -/
theorem apply_inner_self_eq_sum (hT : T.IsSymmetric) (hn : finrank ℝ E = n) (v : E) :
    ⟪T v, v⟫ = ∑ i, hT.eigenvalues hn i * ⟪hT.eigenvectorBasis hn i, v⟫ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).sum_inner_mul_inner (T v) v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT v (hT.eigenvectorBasis hn i), hT.apply_eigenvectorBasis hn i, inner_smul_right,
    real_inner_comm v (hT.eigenvectorBasis hn i)]
  simp only [RCLike.ofReal_real_eq_id, id]
  ring

variable (hT : T.IsSymmetric) (hn : finrank ℝ E = n)

/-- The span of those eigenvectors of `T` whose sorted index satisfies the predicate `p`. -/
def eigenspan (p : Fin n → Prop) : Submodule ℝ E :=
  Submodule.span ℝ ((hT.eigenvectorBasis hn).toBasis '' {j | p j})

/-- A vector lies in `eigenspan hT hn p` exactly when its inner products against the
eigenvectors *outside* `p` all vanish. -/
theorem mem_eigenspan {p : Fin n → Prop} {v : E} :
    v ∈ eigenspan hT hn p ↔ ∀ j, ¬ p j → ⟪hT.eigenvectorBasis hn j, v⟫ = 0 := by
  simp only [eigenspan, Basis.mem_span_image, Set.subset_def, Finset.mem_coe,
    Finsupp.mem_support_iff, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, Set.mem_ofPred_eq]
  exact forall_congr' fun _ => not_imp_comm

/-- The dimension of `eigenspan hT hn p` is the number of sorted indices satisfying `p`. -/
theorem finrank_eigenspan (p : Fin n → Prop) [DecidablePred p] :
    finrank ℝ (eigenspan hT hn p) = (Finset.univ.filter p).card := by
  classical
  rw [eigenspan,
    finrank_span_set_eq_card ((hT.eigenvectorBasis hn).toBasis.linearIndepOn _ |>.id_image),
    Set.toFinset_card, Set.card_image_of_injective _ (hT.eigenvectorBasis hn).toBasis.injective,
    ← Set.toFinset_card, Set.toFinset_ofPred]

/-- On the span of the top `i + 1` eigenvectors the quadratic form is at least `μᵢ * ‖v‖ ^ 2`:
`μᵢ` is the smallest of those `i + 1` eigenvalues. -/
theorem le_apply_inner_self_of_mem_eigenspan_Iic (i : Fin n) {v : E}
    (hv : v ∈ eigenspan hT hn (· ≤ i)) : hT.eigenvalues hn i * ‖v‖ ^ 2 ≤ ⟪T v, v⟫ := by
  rw [apply_inner_self_eq_sum hT hn, ← (hT.eigenvectorBasis hn).sum_sq_inner_right v,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt j i with hji | hji
  · have : hT.eigenvalues hn i ≤ hT.eigenvalues hn j := hT.eigenvalues_antitone hn hji
    nlinarith [sq_nonneg ⟪hT.eigenvectorBasis hn j, v⟫]
  · simp [(mem_eigenspan hT hn).mp hv j (not_le.mpr hji)]

/-- On the span of the bottom `n - i` eigenvectors the quadratic form is at most `μᵢ * ‖v‖ ^ 2`:
`μᵢ` is the largest of those `n - i` eigenvalues. -/
theorem apply_inner_self_le_of_mem_eigenspan_Ici (i : Fin n) {v : E}
    (hv : v ∈ eigenspan hT hn (i ≤ ·)) : ⟪T v, v⟫ ≤ hT.eigenvalues hn i * ‖v‖ ^ 2 := by
  rw [apply_inner_self_eq_sum hT hn, ← (hT.eigenvectorBasis hn).sum_sq_inner_right v,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases le_or_gt i j with hij | hij
  · have : hT.eigenvalues hn j ≤ hT.eigenvalues hn i := hT.eigenvalues_antitone hn hij
    nlinarith [sq_nonneg ⟪hT.eigenvectorBasis hn j, v⟫]
  · simp [(mem_eigenspan hT hn).mp hv j (not_le.mpr hij)]

/-- **Weyl's inequality, one-sided.** If `⟪(T - S) v, v⟫ ≤ C * ‖v‖ ^ 2` for every `v`, then the
`i`-th sorted eigenvalue of `T` exceeds that of `S` by at most `C`. -/
theorem eigenvalues_sub_le {S : E →ₗ[ℝ] E} (hS : S.IsSymmetric) {C : ℝ}
    (hC : ∀ v : E, ⟪(T - S) v, v⟫ ≤ C * ‖v‖ ^ 2) (i : Fin n) :
    hT.eigenvalues hn i - hS.eigenvalues hn i ≤ C := by
  set V := eigenspan hT hn (· ≤ i) with hV
  set W := eigenspan hS hn (i ≤ ·) with hW
  have hdimV : finrank ℝ V = i + 1 := by
    rw [hV, finrank_eigenspan, Finset.filter_ge_eq_Iic, Fin.card_Iic]
  have hdimW : finrank ℝ W = n - i := by
    rw [hW, finrank_eigenspan, Finset.filter_le_eq_Ici, Fin.card_Ici]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V W
  have hle : finrank ℝ (V ⊔ W : Submodule ℝ E) ≤ n := by rw [← hn]; exact Submodule.finrank_le _
  have hi : (i : ℕ) < n := i.isLt
  have hne : (V ⊓ W : Submodule ℝ E) ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨v, ⟨hvV, hvW⟩, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnorm : 0 < ‖v‖ ^ 2 := by positivity
  have hTS : ⟪T v, v⟫ - ⟪S v, v⟫ ≤ C * ‖v‖ ^ 2 := by
    simpa only [LinearMap.sub_apply, inner_sub_left] using hC v
  nlinarith [le_apply_inner_self_of_mem_eigenspan_Iic hT hn i hvV,
    apply_inner_self_le_of_mem_eigenspan_Ici hS hn i hvW]

/-- **Weyl's inequality, two-sided.** If `|⟪(T - S) v, v⟫| ≤ C * ‖v‖ ^ 2` for every `v`, then the
`i`-th sorted eigenvalues of `T` and of `S` differ by at most `C`. -/
theorem abs_eigenvalues_sub_le {S : E →ₗ[ℝ] E} (hS : S.IsSymmetric) {C : ℝ}
    (hC : ∀ v : E, |⟪(T - S) v, v⟫| ≤ C * ‖v‖ ^ 2) (i : Fin n) :
    |hT.eigenvalues hn i - hS.eigenvalues hn i| ≤ C := by
  have hC' : ∀ v : E, ⟪(S - T) v, v⟫ ≤ C * ‖v‖ ^ 2 := fun v => by
    have h := neg_le_of_abs_le (hC v)
    simp only [LinearMap.sub_apply, inner_sub_left] at h ⊢
    linarith
  exact abs_sub_le_iff.mpr ⟨eigenvalues_sub_le hT hn hS (fun v => le_of_abs_le (hC v)) i,
    eigenvalues_sub_le hS hn hT hC' i⟩

end LinearMap.IsSymmetric

end PCError

end
