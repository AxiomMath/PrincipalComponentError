/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Basic.Real.Sign
public import PCError.Attr
public import PCError.External

/-!
# Matrix preliminaries

Four elementary facts about real matrices and their eigenpairs, used throughout the
asymptotic analysis.

## Main statements

* `PCError.pos_of_mulVec_mul_transpose_eq_smul`,
  `PCError.norm_eq_one_of_sqrt_smul_eq_transpose_mulVec`,
  `PCError.transpose_mul_mulVec_eq_smul_of_sqrt_smul_eq_transpose_mulVec`: *Gram duality* — a
  nonzero eigenvalue `λ` of `AAᵀ` with unit eigenvector `v` is positive, and `λ^(-1/2) Aᵀ v`
  is a unit eigenvector of `AᵀA` at `λ`.
* `PCError.mem_spectrum_mul_transpose_iff`: the two Gram products `AAᵀ` and `AᵀA` share their
  nonzero spectrum.
* `PCError.exists_tendsto_simple_eigenvalue`: eigenpair convergence at a simple eigenvalue.
* `PCError.eventually_inner_ne_zero`, `PCError.tendsto_real_sign_inner_smul`: *sign pinning* — unit
  vectors whose inner products with a fixed unit vector tend to `1` in absolute value converge
  after their signs are pinned.

## Implementation notes

Vectors are taken in `EuclideanSpace ℝ m`, so that `‖·‖` and `⟪·, ·⟫` are the Euclidean norm
and inner product while `Matrix.mulVec` still applies, exactly as in
`Matrix.IsHermitian.mulVec_eigenvectorBasis` and in the cited inputs
`PCError.WeylPerturbation` and `PCError.EigenpairContinuity`.  The
elaborator inserts the coercion `WithLp.ofLp` in `A *ᵥ v`, so an equation such as
`A *ᵥ v = lam • v` is an equation of plain vectors; only norms and inner products see the
`EuclideanSpace` structure.  `PCError.inner_eq_dotProduct` is the bridge used to compute them.

Simplicity of an eigenvalue is spelled out as in `PCError.EigenpairContinuity`: the unit
eigenvectors at that eigenvalue are exactly `±v`.  This is what a one-dimensional eigenspace
amounts to, and it is the form the eigenvector arguments consume.
-/

@[expose] public section

namespace PCError

open Filter Matrix
open scoped Topology RealInnerProductSpace

/-! ### Euclidean inner products as dot products -/

variable {m r : Type*} [Fintype m] [Fintype r]

/-- The inner product of `EuclideanSpace ℝ m` is the dot product of the underlying vectors. -/
theorem inner_eq_dotProduct (x y : EuclideanSpace ℝ m) : ⟪x, y⟫ = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- The squared Euclidean norm of a vector is the dot product of the underlying vector with
itself. -/
theorem dotProduct_self_eq_norm_sq (x : EuclideanSpace ℝ m) : x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
  rw [← inner_eq_dotProduct, real_inner_self_eq_norm_sq]

/-- A symmetric matrix is self-adjoint for the dot product. -/
theorem dotProduct_mulVec_eq_mulVec_dotProduct {R n : Type*} [NonUnitalCommSemiring R]
    [Fintype n] {M : Matrix n n R} (hM : M.IsSymm) (x y : n → R) :
    x ⬝ᵥ (M *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [hM.dotProduct_mulVec_comm, dotProduct_comm]

/-! ### Gram duality -/

/-- If `v` is an eigenvector of `AAᵀ` at `λ`, then `Aᵀ v` is an eigenvector of `AᵀA` at `λ`
(possibly the zero one, if `λ = 0`). -/
theorem mulVec_transpose_mulVec_eq_smul {R : Type*} [CommSemiring R] (A : Matrix m r R)
    {lam : R} {v : m → R} (hAv : (A * Aᵀ) *ᵥ v = lam • v) :
    (Aᵀ * A) *ᵥ (Aᵀ *ᵥ v) = lam • (Aᵀ *ᵥ v) := by
  rw [mulVec_mulVec, Matrix.mul_assoc, ← mulVec_mulVec, hAv, mulVec_smul]

/-- If `v` is an eigenvector of `AAᵀ` at `λ`, then `(Aᵀ v) ⬝ᵥ (Aᵀ v) = λ * (v ⬝ᵥ v)`, which
over `ℝ` reads `‖Aᵀ v‖² = λ ‖v‖²`. -/
theorem transpose_mulVec_dotProduct_self {R : Type*} [CommSemiring R] (A : Matrix m r R)
    {lam : R} {v : m → R} (hAv : (A * Aᵀ) *ᵥ v = lam • v) :
    (Aᵀ *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ v) = lam * (v ⬝ᵥ v) := by
  rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, hAv, smul_dotProduct, smul_eq_mul]

/-- If `v` is a unit eigenvector of `AAᵀ` at `λ`, then `‖Aᵀ v‖² = λ`. -/
theorem transpose_mulVec_dotProduct_self_of_norm_eq_one (A : Matrix m r ℝ) {lam : ℝ}
    {v : EuclideanSpace ℝ m} (hv : ‖v‖ = 1) (hAv : (A * Aᵀ) *ᵥ v = lam • v) :
    (Aᵀ *ᵥ v.ofLp) ⬝ᵥ (Aᵀ *ᵥ v.ofLp) = lam := by
  rw [transpose_mulVec_dotProduct_self A hAv, dotProduct_self_eq_norm_sq, hv]
  ring

/-- **Gram duality**, first part: a nonzero eigenvalue of a Gram matrix `AAᵀ` with a unit
eigenvector is positive. -/
@[pcerror "lem_gram_duality"]
theorem pos_of_mulVec_mul_transpose_eq_smul (A : Matrix m r ℝ) {lam : ℝ} (hlam : lam ≠ 0)
    {v : EuclideanSpace ℝ m} (hv : ‖v‖ = 1) (hAv : (A * Aᵀ) *ᵥ v = lam • v) : 0 < lam := by
  refine lt_of_le_of_ne ?_ (Ne.symm hlam)
  rw [← transpose_mulVec_dotProduct_self_of_norm_eq_one A hv hAv]
  simpa using dotProduct_self_star_nonneg (Aᵀ *ᵥ v.ofLp)

/-- **Gram duality**, second part: the vector `u = λ^(-1/2) Aᵀ v` built from a unit eigenvector
`v` of `AAᵀ` at a nonzero `λ` is again a unit vector. -/
@[pcerror "lem_gram_duality"]
theorem norm_eq_one_of_sqrt_smul_eq_transpose_mulVec (A : Matrix m r ℝ) {lam : ℝ}
    (hlam : lam ≠ 0) {v : EuclideanSpace ℝ m} (hv : ‖v‖ = 1) (hAv : (A * Aᵀ) *ᵥ v = lam • v)
    {u : EuclideanSpace ℝ r} (hu : √lam • u = Aᵀ *ᵥ v) : ‖u‖ = 1 := by
  have hpos : 0 < lam := pos_of_mulVec_mul_transpose_eq_smul A hlam hv hAv
  have h := transpose_mulVec_dotProduct_self_of_norm_eq_one A hv hAv
  rw [← hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    dotProduct_self_eq_norm_sq] at h
  have hnorm : ‖u‖ ^ 2 = 1 := by
    have hs : √lam * √lam = lam := Real.mul_self_sqrt hpos.le
    field_simp at h
    nlinarith [h, hs, sq_nonneg ‖u‖]
  nlinarith [hnorm, norm_nonneg u]

/-- **Gram duality**, third part: the vector `u = λ^(-1/2) Aᵀ v` built from an eigenvector `v`
of `AAᵀ` at a positive `λ` is an eigenvector of `AᵀA` at the same `λ`. -/
@[pcerror "lem_gram_duality"]
theorem transpose_mul_mulVec_eq_smul_of_sqrt_smul_eq_transpose_mulVec (A : Matrix m r ℝ)
    {lam : ℝ} (hlam : 0 < lam) {v : EuclideanSpace ℝ m} (hAv : (A * Aᵀ) *ᵥ v = lam • v)
    {u : EuclideanSpace ℝ r} (hu : √lam • u = Aᵀ *ᵥ v) :
    (Aᵀ * A) *ᵥ u = lam • u := by
  have h := mulVec_transpose_mulVec_eq_smul A hAv
  rw [← hu, mulVec_smul, smul_comm] at h
  exact smul_right_injective _ (ne_of_gt (Real.sqrt_pos.2 hlam)) h

/-- A scalar is an eigenvalue of a square matrix over a field exactly when the matrix has a
nonzero eigenvector at it. -/
theorem mem_spectrum_iff_exists_mulVec_eq_smul {K n : Type*} [Field K] [Fintype n]
    [DecidableEq n] {M : Matrix n n K} {lam : K} :
    lam ∈ spectrum K M ↔ ∃ v : n → K, v ≠ 0 ∧ M *ᵥ v = lam • v := by
  rw [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' (R := K) (n := n)) M,
    ← Module.End.hasEigenvalue_iff_mem_spectrum]
  refine ⟨fun h => ?_, fun ⟨v, hv0, hv⟩ => ?_⟩
  · obtain ⟨v, hv, hv0⟩ := h.exists_hasEigenvector
    exact ⟨v, hv0, by simpa [Matrix.toLinAlgEquiv'_apply] using Module.End.mem_eigenspace_iff.1 hv⟩
  · refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [Matrix.toLinAlgEquiv'_apply] using hv

/-- Half of `PCError.mem_spectrum_mul_transpose_iff`: a nonzero eigenvalue of `AAᵀ` is an
eigenvalue of `AᵀA`. -/
theorem mem_spectrum_transpose_mul_of_mem_spectrum_mul_transpose [DecidableEq m] [DecidableEq r]
    (A : Matrix m r ℝ) {lam : ℝ} (hlam : lam ≠ 0) (h : lam ∈ spectrum ℝ (A * Aᵀ)) :
    lam ∈ spectrum ℝ (Aᵀ * A) := by
  obtain ⟨v, hv0, hv⟩ := mem_spectrum_iff_exists_mulVec_eq_smul.1 h
  refine mem_spectrum_iff_exists_mulVec_eq_smul.2
    ⟨Aᵀ *ᵥ v, fun h0 => ?_, mulVec_transpose_mulVec_eq_smul A hv⟩
  have hd := transpose_mulVec_dotProduct_self A hv
  rw [h0, dotProduct_zero] at hd
  exact (mul_eq_zero.1 hd.symm).elim hlam fun h1 => hv0 (dotProduct_self_eq_zero.1 h1)

/-- **The two Gram products share their nonzero spectrum**: a nonzero real `λ` is an eigenvalue
of `AAᵀ` if and only if it is an eigenvalue of `AᵀA`. -/
@[pcerror "lem_gram_spectrum"]
theorem mem_spectrum_mul_transpose_iff [DecidableEq m] [DecidableEq r] (A : Matrix m r ℝ)
    {lam : ℝ} (hlam : lam ≠ 0) :
    lam ∈ spectrum ℝ (A * Aᵀ) ↔ lam ∈ spectrum ℝ (Aᵀ * A) :=
  ⟨mem_spectrum_transpose_mul_of_mem_spectrum_mul_transpose A hlam, fun h => by
    simpa using
      mem_spectrum_transpose_mul_of_mem_spectrum_mul_transpose Aᵀ hlam (by simpa using h)⟩

/-! ### Eigenvectors of a Hermitian matrix at a fixed eigenvalue -/

section Hermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}

/-- An eigenvector of a real symmetric matrix `M` at `λ` is orthogonal to every vector of the
eigenvector basis whose eigenvalue is not `λ`. -/
theorem inner_eigenvectorBasis_eq_zero (hM : M.IsHermitian) {lam : ℝ} {w : EuclideanSpace ℝ n}
    (hw : M *ᵥ w = lam • w) {i : n} (hi : hM.eigenvalues i ≠ lam) :
    ⟪hM.eigenvectorBasis i, w⟫ = 0 := by
  have key := dotProduct_mulVec_eq_mulVec_dotProduct hM.isSymm (hM.eigenvectorBasis i).ofLp w.ofLp
  rw [hw, hM.mulVec_eigenvectorBasis i, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul] at key
  rw [inner_eq_dotProduct]
  by_contra hne
  exact hi (mul_right_cancel₀ hne key.symm)

/-- An eigenvalue of a real symmetric matrix appears in its list of eigenvalues. -/
theorem exists_eigenvalues_eq (hM : M.IsHermitian) {lam : ℝ} {w : EuclideanSpace ℝ n}
    (hw0 : w ≠ 0) (hw : M *ᵥ w = lam • w) : ∃ i, hM.eigenvalues i = lam := by
  by_contra hcon
  push Not at hcon
  refine hw0 ?_
  have h0 : ∀ i, (hM.eigenvectorBasis.repr w).ofLp i = 0 := fun i => by
    rw [OrthonormalBasis.repr_apply_apply]
    exact inner_eigenvectorBasis_eq_zero hM hw (hcon i)
  rw [← hM.eigenvectorBasis.sum_repr w]
  simp [h0]

/-- If the unit eigenvectors of a real symmetric matrix at `λ` are exactly `±v`, then `λ` occurs
exactly once in its list of eigenvalues. -/
theorem exists_unique_eigenvalues_eq (hM : M.IsHermitian) {lam : ℝ} {v : EuclideanSpace ℝ n}
    (hv : ‖v‖ = 1) (hMv : M *ᵥ v = lam • v)
    (hsimple : ∀ w : EuclideanSpace ℝ n, ‖w‖ = 1 → M *ᵥ w = lam • w → w = v ∨ w = -v) :
    ∃ i₀, hM.eigenvalues i₀ = lam ∧ ∀ i, hM.eigenvalues i = lam → i = i₀ := by
  obtain ⟨i₀, hi₀⟩ := exists_eigenvalues_eq hM (fun h => by simp [h] at hv) hMv
  refine ⟨i₀, hi₀, fun i hi => ?_⟩
  by_contra hne
  have hb : ∀ j, hM.eigenvalues j = lam →
      M *ᵥ (hM.eigenvectorBasis j).ofLp = lam • (hM.eigenvectorBasis j).ofLp := by
    intro j hj
    rw [hM.mulVec_eigenvectorBasis j, hj]
  have horth : ⟪hM.eigenvectorBasis i, hM.eigenvectorBasis i₀⟫ = 0 :=
    hM.eigenvectorBasis.orthonormal.2 hne
  rcases hsimple _ (hM.eigenvectorBasis.orthonormal.1 i) (hb i hi) with h1 | h1 <;>
    rcases hsimple _ (hM.eigenvectorBasis.orthonormal.1 i₀) (hb i₀ hi₀) with h2 | h2 <;>
      rw [h1, h2] at horth <;> simp [hv] at horth

/-- If `λ` occurs exactly once in the list of eigenvalues of a real symmetric matrix `M`, at the
index `i₀`, then the unit eigenvectors of `M` at `λ` are exactly `±` the `i₀`-th vector of the
eigenvector basis: `λ` is a simple eigenvalue. -/
theorem eq_or_eq_neg_eigenvectorBasis (hM : M.IsHermitian) {lam : ℝ} {i₀ : n}
    (huniq : ∀ i, hM.eigenvalues i = lam → i = i₀) {w : EuclideanSpace ℝ n} (hw1 : ‖w‖ = 1)
    (hw : M *ᵥ w = lam • w) :
    w = hM.eigenvectorBasis i₀ ∨ w = -hM.eigenvectorBasis i₀ := by
  set b := hM.eigenvectorBasis with hb
  have hrepr : ∀ i, i ≠ i₀ → (b.repr w).ofLp i = 0 := by
    intro i hi
    rw [hb, OrthonormalBasis.repr_apply_apply]
    exact inner_eigenvectorBasis_eq_zero hM hw fun h => hi (huniq i h)
  have hs : ∑ i, (b.repr w).ofLp i • b i = (b.repr w).ofLp i₀ • b i₀ :=
    Finset.sum_eq_single i₀ (fun i _ hi => by rw [hrepr i hi, zero_smul])
      fun h => absurd (Finset.mem_univ i₀) h
  have hw' : w = (b.repr w).ofLp i₀ • b i₀ := by rw [← hs]; exact (b.sum_repr w).symm
  have habs : |(b.repr w).ofLp i₀| = 1 := by
    rwa [hw', norm_smul, b.orthonormal.1 i₀, mul_one, Real.norm_eq_abs] at hw1
  rcases (abs_eq zero_le_one).1 habs with h | h
  · exact Or.inl (by rw [hw', h, one_smul])
  · exact Or.inr (by rw [hw', h, neg_one_smul])

/-- The eigenvalues of a real symmetric matrix, listed over the index type of the matrix and
listed in decreasing order over `Fin (Fintype.card n)`, form the same multiset: both list the
roots of the characteristic polynomial. -/
theorem map_eigenvalues_eq_map_eigenvalues₀ (hM : M.IsHermitian) :
    Multiset.map hM.eigenvalues Finset.univ.val
      = Multiset.map hM.eigenvalues₀ Finset.univ.val := by
  have h2 := hM.roots_charpoly_eq_eigenvalues₀
  rw [hM.roots_charpoly_eq_eigenvalues, ← Multiset.map_map, ← Multiset.map_map] at h2
  exact Multiset.map_injective RCLike.ofReal_injective h2

end Hermitian

/-! ### Transferring values and multiplicities between two listings -/

section Listings

variable {α β γ : Type*} [Fintype α] [Fintype β] {f : α → γ} {g : β → γ} {c : γ}

/-- A value taken by `f` is taken by `g`, when the two families list the same multiset. -/
theorem exists_eq_of_map_univ_val_eq
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) {a : α} (ha : f a = c) :
    ∃ b : β, g b = c := by
  have hmem : c ∈ Multiset.map g Finset.univ.val :=
    h ▸ Multiset.mem_map.2 ⟨a, Finset.mem_univ_val a, ha⟩
  obtain ⟨b, -, hb⟩ := Multiset.mem_map.1 hmem
  exact ⟨b, hb⟩

/-- A value taken exactly once by `f` is taken exactly once by `g`, when the two families list
the same multiset. -/
theorem exists_unique_eq_of_map_univ_val_eq
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) {a₀ : α} (h₀ : f a₀ = c)
    (huniq : ∀ a, f a = c → a = a₀) : ∃ b₀ : β, g b₀ = c ∧ ∀ b, g b = c → b = b₀ := by
  classical
  have hcard : (Finset.univ.filter fun a : α => c = f a).card
      = (Finset.univ.filter fun b : β => c = g b).card := by
    have hc := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at hc
    exact hc
  have hone : (Finset.univ.filter fun a : α => c = f a) = {a₀} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ha => huniq a ha.symm, fun ha => by rw [ha, h₀]⟩
  rw [hone, Finset.card_singleton] at hcard
  obtain ⟨b₀, hb₀⟩ := Finset.card_eq_one.1 hcard.symm
  have hmem : ∀ b : β, c = g b ↔ b = b₀ := fun b => by simpa using Finset.ext_iff.1 hb₀ b
  exact ⟨b₀, ((hmem b₀).2 rfl).symm, fun b hb => (hmem b).1 hb.symm⟩

end Listings

/-! ### Simple eigenvalues of a real symmetric matrix -/

section Simple

/-- A real family on a finite type is separated from a value it takes only at `j₀`: some `γ > 0`
has `2 * γ ≤ |c j - lam|` for every other index. -/
theorem exists_pos_two_mul_le_abs_sub {ι : Type*} [Finite ι] {c : ι → ℝ} {lam : ℝ} {j₀ : ι}
    (huniq : ∀ j, c j = lam → j = j₀) : ∃ γ > 0, ∀ j, j ≠ j₀ → 2 * γ ≤ |c j - lam| := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set d : ι → ℝ := fun j => if j = j₀ then 1 else |c j - lam| with hd
  have hdpos : ∀ j, 0 < d j := by
    intro j
    by_cases hj : j = j₀
    · simp [hd, hj]
    · rw [hd]
      simp only [ite_eq_right hj]
      exact abs_pos.2 (sub_ne_zero.2 fun h => hj (huniq j h))
  have hnonempty : (Finset.univ : Finset ι).Nonempty := ⟨j₀, Finset.mem_univ _⟩
  set γ := (Finset.univ.inf' hnonempty d) / 2 with hγ
  have hγpos : 0 < γ := by
    have h : 0 < Finset.univ.inf' hnonempty d := (Finset.lt_inf'_iff hnonempty).2 fun j _ => hdpos j
    rw [hγ]
    linarith
  refine ⟨γ, hγpos, fun j hj => ?_⟩
  have h := Finset.inf'_le d (Finset.mem_univ j)
  rw [hd] at h
  simp only [ite_eq_right hj] at h
  rw [hγ]
  linarith

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ}

/-- An eigenvalue closer than `γ` to `ζ` is the `j₀`-th one of the decreasing listing, when every
other index of that listing keeps its eigenvalue at distance `≥ γ` from `ζ`. -/
theorem eq_eigenvalues₀_of_abs_sub_lt (hM : M.IsHermitian) {lam ζ γ : ℝ}
    {j₀ : Fin (Fintype.card n)} (hfar : ∀ j, j ≠ j₀ → γ ≤ |hM.eigenvalues₀ j - ζ|)
    (hlam : |lam - ζ| < γ) {w : EuclideanSpace ℝ n} (hw0 : w ≠ 0) (hw : M *ᵥ w = lam • w) :
    lam = hM.eigenvalues₀ j₀ := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq hM hw0 hw
  obtain ⟨j, hj⟩ := exists_eq_of_map_univ_val_eq (map_eigenvalues_eq_map_eigenvalues₀ hM) hi
  by_cases hjj : j = j₀
  · rw [← hj, hjj]
  · have h := hfar j hjj
    rw [hj] at h
    exact absurd h (not_le.2 hlam)

/-- At an eigenvalue occurring exactly once in the decreasing listing of a real symmetric matrix
there is a unit eigenvector, and every unit eigenvector there is `±` it. -/
theorem exists_unit_eigenvector_eq_or_neg (hM : M.IsHermitian) {lam : ℝ}
    {j₀ : Fin (Fintype.card n)} (hj₀ : hM.eigenvalues₀ j₀ = lam)
    (huniq : ∀ j, hM.eigenvalues₀ j = lam → j = j₀) :
    ∃ w : EuclideanSpace ℝ n, ‖w‖ = 1 ∧ M *ᵥ w = lam • w ∧
      ∀ w' : EuclideanSpace ℝ n, ‖w'‖ = 1 → M *ᵥ w' = lam • w' → w' = w ∨ w' = -w := by
  obtain ⟨i, hi, hiuniq⟩ :=
    exists_unique_eq_of_map_univ_val_eq (map_eigenvalues_eq_map_eigenvalues₀ hM).symm hj₀ huniq
  exact ⟨hM.eigenvectorBasis i, hM.eigenvectorBasis.orthonormal.1 i,
    by rw [hM.mulVec_eigenvectorBasis i, hi],
    fun w' hw'1 hw' => eq_or_eq_neg_eigenvectorBasis hM hiuniq hw'1 hw'⟩

end Simple

/-! ### Eigenpair convergence at a simple eigenvalue -/

section EigenpairConvergence

attribute [local instance] Matrix.instL2OpNormedAddCommGroup

/-- Entrywise convergence of matrices of fixed size implies convergence in the ℓ²-operator
norm: the ℓ²-operator norm is the norm of the image of a linear map out of a
finite-dimensional space, hence continuous for the entrywise topology. -/
theorem tendsto_l2_opNorm_sub_zero {m n ι : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {l : Filter ι} {A : ι → Matrix m n ℝ} {A₀ : Matrix m n ℝ} (h : Tendsto A l (𝓝 A₀)) :
    Tendsto (fun p => ‖A p - A₀‖) l (𝓝 0) := by
  set L : Matrix m n ℝ →ₗ[ℝ] (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m) :=
    (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap).toLinearMap
  have hcont : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have h0 : Tendsto (fun p => A p - A₀) l (𝓝 0) := by
    simpa using h.sub (tendsto_const_nhds (x := A₀))
  have h1 := (continuous_norm.tendsto (L 0)).comp ((hcont.tendsto 0).comp h0)
  simp only [Function.comp_def, map_zero, norm_zero] at h1
  exact h1.congr fun p => by rw [Matrix.l2_opNorm_def]; rfl

universe u

variable {m : Type u} [Fintype m] {A : ℕ → Matrix m m ℝ} {A₀ : Matrix m m ℝ}

/-- **Eigenpair convergence at a simple eigenvalue**: if real symmetric matrices `A p` converge
to a real symmetric `A₀`, and `ζ` is a simple eigenvalue of `A₀` with unit eigenvector `v` — its
unit eigenvectors being exactly `±v` — then for all large `p` the matrix `A p` has a simple
eigenvalue `zeta p`, these converge to `ζ`, and *every* choice of unit eigenvectors of `A p` at
`zeta p` has `|⟪·, v⟫| → 1`.

The eigenvalue `zeta p` is the one Weyl's inequality (`hweyl`) keeps close to `ζ`, and the
eigenvector statement comes from eigenpair continuity (`heigcont`) together with simplicity,
which pins any other choice of unit eigenvector up to sign. -/
@[pcerror "lem_eigpair_conv"]
theorem exists_tendsto_simple_eigenvalue (hweyl : WeylPerturbation.{u})
    (heigcont : EigenpairContinuity.{u}) (hA : ∀ p, (A p).IsHermitian) (hA₀ : A₀.IsHermitian)
    (hconv : Tendsto A atTop (𝓝 A₀)) {ζ : ℝ} {v : EuclideanSpace ℝ m} (hv : ‖v‖ = 1)
    (hAv : A₀ *ᵥ v = ζ • v)
    (hsimple : ∀ w : EuclideanSpace ℝ m, ‖w‖ = 1 → A₀ *ᵥ w = ζ • w → w = v ∨ w = -v) :
    ∃ zeta : ℕ → ℝ, Tendsto zeta atTop (𝓝 ζ) ∧
      (∀ᶠ p in atTop, ∃ w : EuclideanSpace ℝ m, ‖w‖ = 1 ∧ A p *ᵥ w = zeta p • w ∧
        ∀ w' : EuclideanSpace ℝ m, ‖w'‖ = 1 → A p *ᵥ w' = zeta p • w' → w' = w ∨ w' = -w) ∧
      ∀ u : ℕ → EuclideanSpace ℝ m,
        (∀ᶠ p in atTop, ‖u p‖ = 1 ∧ A p *ᵥ u p = zeta p • u p) →
        Tendsto (fun p => |⟪u p, v⟫|) atTop (𝓝 1) := by
  classical
  -- `ζ` occurs exactly once in the eigenvalue list of `A₀`, hence also in the decreasing
  -- listing, which is where Weyl's inequality lives, and there it is separated by `2γ`
  obtain ⟨i₀, hi₀, huniq₀⟩ := exists_unique_eigenvalues_eq hA₀ hv hAv hsimple
  obtain ⟨j₀, hj₀, hjuniq⟩ :=
    exists_unique_eq_of_map_univ_val_eq (map_eigenvalues_eq_map_eigenvalues₀ hA₀) hi₀ huniq₀
  obtain ⟨γ, hγpos, hgap⟩ := exists_pos_two_mul_le_abs_sub hjuniq
  obtain ⟨zeta, hzetadef⟩ : ∃ zeta : ℕ → ℝ, ∀ p, zeta p = (hA p).eigenvalues₀ j₀ :=
    ⟨_, fun _ => rfl⟩
  have hweyl' : ∀ p j, |(hA p).eigenvalues₀ j - hA₀.eigenvalues₀ j| ≤ ‖A p - A₀‖ :=
    fun p => hweyl hA₀ (hA p)
  have hnorm : Tendsto (fun p => ‖A p - A₀‖) atTop (𝓝 0) := tendsto_l2_opNorm_sub_zero hconv
  have hnear : ∀ p, |zeta p - ζ| ≤ ‖A p - A₀‖ := fun p => by
    rw [hzetadef p, ← hj₀]; exact hweyl' p j₀
  have hzeta : Tendsto zeta atTop (𝓝 ζ) := tendsto_iff_dist_tendsto_zero.2 <| by
    simpa only [Real.dist_eq] using squeeze_zero (fun p => abs_nonneg _) hnear hnorm
  have hev : ∀ᶠ p in atTop, ‖A p - A₀‖ < γ := hnorm.eventually_lt_const hγpos
  -- for large `p`, every other eigenvalue of `A p` stays at distance `≥ γ` from `ζ`
  have hfar : ∀ᶠ p in atTop, ∀ j, j ≠ j₀ → γ ≤ |(hA p).eigenvalues₀ j - ζ| := by
    filter_upwards [hev] with p hp j hj
    have t := abs_sub_le (hA₀.eigenvalues₀ j) ((hA p).eigenvalues₀ j) ζ
    rw [abs_sub_comm (hA₀.eigenvalues₀ j) ((hA p).eigenvalues₀ j)] at t
    linarith [hgap j hj, hweyl' p j]
  -- hence `zeta p` occurs exactly once in the decreasing listing of the eigenvalues of `A p`
  have hsimplep : ∀ᶠ p in atTop, ∀ j, (hA p).eigenvalues₀ j = zeta p → j = j₀ := by
    filter_upwards [hfar, hev] with p h1 h2 j hj
    by_contra hjne
    have h3 := h1 j hjne
    rw [hj] at h3
    linarith [hnear p]
  refine ⟨zeta, hzeta, ?_, ?_⟩
  · filter_upwards [hsimplep] with p hp
    exact exists_unit_eigenvector_eq_or_neg (hA p) (hzetadef p).symm hp
  · -- the eigenvector statement: eigenpair continuity supplies one choice, simplicity pins
    -- every other choice to it up to sign
    obtain ⟨lam, u, hlam, hu, huev⟩ := heigcont hA hA₀ hconv hv hAv hsimple
    have hlamzeta : ∀ᶠ p in atTop, lam p = zeta p := by
      have hlamnear : ∀ᶠ p in atTop, |lam p - ζ| < γ := by
        simpa using hlam.eventually (eventually_abs_sub_lt ζ hγpos)
      filter_upwards [huev, hfar, hlamnear] with p h1 h2 h3
      rw [hzetadef p]
      exact eq_eigenvalues₀_of_abs_sub_lt (hA p) h2 h3 (fun h => by simp [h] at h1) h1.1
    have habsu : Tendsto (fun p => |⟪u p, v⟫|) atTop (𝓝 1) := by
      have h := (Filter.Tendsto.inner (𝕜 := ℝ) hu (tendsto_const_nhds (x := v) (f := atTop))).abs
      rw [real_inner_self_eq_norm_sq, hv] at h
      simpa using h
    intro u' hu'
    refine habsu.congr' ?_
    filter_upwards [hu', huev, hlamzeta, hsimplep] with p h1 h2 h3 h4
    obtain ⟨w₀, -, -, huniq₀⟩ := exists_unit_eigenvector_eq_or_neg (hA p) (hzetadef p).symm h4
    rcases huniq₀ _ h2.2.1 (by rw [← h3]; exact h2.1) with h5 | h5 <;>
      rcases huniq₀ _ h1.1 h1.2 with h6 | h6 <;>
      simp [h5, h6, inner_neg_left, abs_neg]

end EigenpairConvergence

/-! ### Sign pinning -/

section SignPinning

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} {l : Filter ι}
  {u : ι → E} {u₀ : E}

/-- **Sign pinning**, first part: if the inner products `⟪uᵢ, u₀⟫` tend to `1` in absolute
value, then they are eventually nonzero, so that their signs are well defined. -/
@[pcerror "lem_sign_pin"]
theorem eventually_inner_ne_zero (h : Tendsto (fun i => |⟪u i, u₀⟫|) l (𝓝 1)) :
    ∀ᶠ i in l, ⟪u i, u₀⟫ ≠ 0 := by
  filter_upwards [h.eventually (eventually_gt_nhds (zero_lt_one' ℝ))] with i hi h0
  simp [h0] at hi

/-- **Sign pinning**, second part: unit vectors `uᵢ` whose inner products with a unit vector
`u₀` tend to `1` in absolute value converge to `u₀` once their signs are pinned by
`uᵢ ↦ sign ⟪uᵢ, u₀⟫ • uᵢ`. -/
@[pcerror "lem_sign_pin"]
theorem tendsto_real_sign_inner_smul (hu : ∀ᶠ i in l, ‖u i‖ = 1) (hu₀ : ‖u₀‖ = 1)
    (h : Tendsto (fun i => |⟪u i, u₀⟫|) l (𝓝 1)) :
    Tendsto (fun i => Real.sign ⟪u i, u₀⟫ • u i) l (𝓝 u₀) := by
  -- For a unit `uᵢ` with `⟪uᵢ, u₀⟫ ≠ 0` the pinned vector is again a unit vector, and
  -- `‖sign ⟪uᵢ, u₀⟫ • uᵢ - u₀‖ ^ 2 = 2 (1 - |⟪uᵢ, u₀⟫|)`.
  have key : ∀ᶠ i in l, ‖Real.sign ⟪u i, u₀⟫ • u i - u₀‖ = √(2 - 2 * |⟪u i, u₀⟫|) := by
    filter_upwards [hu, eventually_inner_ne_zero h] with i hi hne
    have hsq : ‖Real.sign ⟪u i, u₀⟫ • u i - u₀‖ ^ 2 = 2 - 2 * |⟪u i, u₀⟫| := by
      rcases lt_or_gt_of_ne hne with hc | hc
      · rw [Real.sign_of_neg hc, abs_of_neg hc, norm_sub_sq_real, real_inner_smul_left,
          norm_smul, hi, hu₀]
        norm_num
        ring
      · rw [Real.sign_of_pos hc, abs_of_pos hc, norm_sub_sq_real, real_inner_smul_left,
          norm_smul, hi, hu₀]
        norm_num
        ring
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  have hg : Tendsto (fun i => √(2 - 2 * |⟪u i, u₀⟫|)) l (𝓝 0) := by
    have h2 : Tendsto (fun i => 2 - 2 * |⟪u i, u₀⟫|) l (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ)) (f := l)).sub (h.const_mul 2)
    simpa using h2.sqrt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact hg.congr' (key.mono fun i hi => hi.symm)

end SignPinning

end PCError

end
