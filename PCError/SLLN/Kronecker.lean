/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import PCError.Attr

/-!
# Kronecker's lemma

Kronecker's lemma: if `b` is positive, monotone and diverges to `∞`, and the series
`∑ a k / b k` converges, then the Cesàro-type averages `(b n)⁻¹ ∑_{k < n} a k` tend to `0`.

The proof is Abel summation against the tails of the convergent series.  Writing
`R n := S - ∑_{k < n} a k / b k` for the tail, so that `R n → 0` and
`a n = b n * (R n - R (n + 1))`, summation by parts gives

`∑_{k < n} a k = b 0 * R 0 - b n * R n + ∑_{k < n} (b (k + 1) - b k) * R (k + 1)`,

and after dividing by `b n` each of the three terms tends to `0`.  The last one is a
weighted average of the null sequence `R (· + 1)` against the nonnegative weights
`b (k + 1) - b k`, whose total mass over `k < n` is exactly `b n - b 0`; that is
`PCError.tendsto_inv_mul_sum_range_diff_mul_of_tendsto_zero`, isolated because it is the
only analytic content.

Nothing here is probabilistic; the lemma is used to pass from almost sure convergence of
`∑ (X i - 𝔼[X i]) / (i + 1)` to the strong law of large numbers.

## Main statements

* `PCError.tendsto_inv_mul_sum_range_diff_mul_of_tendsto_zero`: a `b`-weighted average of a
  null sequence is null.
* `PCError.tendsto_inv_mul_sum_range_of_tendsto`: **Kronecker's lemma**, in the form that only
  asks for convergence of the partial sums of `∑ a k / b k` (rather than `Summable`, which for
  real series is strictly stronger).
* `PCError.tendsto_inv_mul_sum_range_of_summable`: Kronecker's lemma from `Summable`.
* `PCError.tendsto_inv_natCast_mul_sum_range_of_tendsto`: the case `b k = k + 1`, restated with
  the plain normalisation `(n : ℝ)⁻¹`, which is the form the strong law needs.
-/

@[expose] public section

namespace PCError

open Filter Finset
open scoped Topology

/-- A `b`-weighted average of a null sequence is null: if `b` is positive, monotone and
diverges, and `r n → 0`, then `(b n)⁻¹ ∑_{k < n} (b (k + 1) - b k) * r k → 0`.

The weights `b (k + 1) - b k` are nonnegative with total mass `b n - b 0 ≤ b n` over `k < n`,
so splitting the sum at an index beyond which `|r|` is small bounds the average by
`C / b n + ε`. -/
theorem tendsto_inv_mul_sum_range_diff_mul_of_tendsto_zero {b : ℕ → ℝ} (hb_pos : ∀ n, 0 < b n)
    (hb_mono : Monotone b) (hb_top : Tendsto b atTop atTop) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => (b n)⁻¹ * ∑ k ∈ range n, (b (k + 1) - b k) * r k) atTop (𝓝 0) := by
  have hw : ∀ k, 0 ≤ b (k + 1) - b k := fun k => sub_nonneg.2 (hb_mono (Nat.le_succ k))
  have habs : ∀ s : Finset ℕ, |∑ k ∈ s, (b (k + 1) - b k) * r k| ≤
      ∑ k ∈ s, (b (k + 1) - b k) * |r k| := fun s =>
    (abs_sum_le_sum_abs _ _).trans_eq
      (sum_congr rfl fun k _ => by rw [abs_mul, abs_of_nonneg (hw k)])
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hr (ε / 2) (half_pos hε)
  set C := ∑ k ∈ range N, (b (k + 1) - b k) * |r k|
  have hCb : Tendsto (fun n => C * (b n)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hb_top).const_mul C
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hCb (ε / 2) (half_pos hε)
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hbn : 0 < b n := hb_pos n
  have hearly : |∑ k ∈ range N, (b (k + 1) - b k) * r k| ≤ C := habs _
  have hmass : ∑ k ∈ Ico N n, (b (k + 1) - b k) ≤ b n := by
    calc ∑ k ∈ Ico N n, (b (k + 1) - b k) ≤ ∑ k ∈ range n, (b (k + 1) - b k) :=
          sum_le_sum_of_subset_of_nonneg
            (fun k hk => mem_range.2 (mem_Ico.1 hk).2) fun k _ _ => hw k
      _ = b n - b 0 := sum_range_sub (f := b) n
      _ ≤ b n := by linarith [(hb_pos 0).le]
  have hlate : |∑ k ∈ Ico N n, (b (k + 1) - b k) * r k| ≤ ε / 2 * b n := by
    calc |∑ k ∈ Ico N n, (b (k + 1) - b k) * r k|
        ≤ ∑ k ∈ Ico N n, (b (k + 1) - b k) * |r k| := habs _
      _ ≤ ∑ k ∈ Ico N n, (b (k + 1) - b k) * (ε / 2) := by
          refine sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hw k)
          simpa [dist_zero_right, Real.norm_eq_abs] using (hN k (mem_Ico.1 hk).1).le
      _ = ε / 2 * ∑ k ∈ Ico N n, (b (k + 1) - b k) := by rw [← sum_mul, mul_comm]
      _ ≤ ε / 2 * b n := mul_le_mul_of_nonneg_left hmass (half_pos hε).le
  have hMn := hM n ((le_max_right _ _).trans hn)
  rw [dist_zero_right, Real.norm_eq_abs] at hMn ⊢
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hbn.le), ← sum_range_add_sum_Ico _ hnN]
  calc (b n)⁻¹ * |∑ k ∈ range N, (b (k + 1) - b k) * r k +
          ∑ k ∈ Ico N n, (b (k + 1) - b k) * r k|
      ≤ (b n)⁻¹ * (C + ε / 2 * b n) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hearly hlate))
          (inv_nonneg.2 hbn.le)
    _ = C * (b n)⁻¹ + ε / 2 := by field_simp
    _ < ε / 2 + ε / 2 := by linarith [le_abs_self (C * (b n)⁻¹)]
    _ = ε := by ring

/-- **Kronecker's lemma**.  Let `b : ℕ → ℝ` be positive, monotone and divergent.  If the partial
sums of `∑ a k / b k` converge, then `(b n)⁻¹ ∑_{k < n} a k → 0`.

The hypothesis is convergence of the partial sums, not `Summable`; for real series the latter
means unconditional convergence and is strictly stronger, and the martingale convergence
theorem supplies only the former. -/
theorem tendsto_inv_mul_sum_range_of_tendsto {a b : ℕ → ℝ} (hb_pos : ∀ n, 0 < b n)
    (hb_mono : Monotone b) (hb_top : Tendsto b atTop atTop) {S : ℝ}
    (hS : Tendsto (fun n => ∑ k ∈ range n, a k / b k) atTop (𝓝 S)) :
    Tendsto (fun n => (b n)⁻¹ * ∑ k ∈ range n, a k) atTop (𝓝 0) := by
  set R : ℕ → ℝ := fun n => S - ∑ k ∈ range n, a k / b k with hR
  have hR_tendsto : Tendsto R atTop (𝓝 0) := by
    simpa [hR] using hS.const_sub S
  have hR_succ : ∀ n, a n = b n * (R n - R (n + 1)) := by
    intro n
    have hbn : b n ≠ 0 := (hb_pos n).ne'
    have h : R (n + 1) = R n - a n / b n := by
      simp only [hR, sum_range_succ]
      ring
    rw [h]
    field_simp
    ring
  -- Abel summation against the tails `R`
  have habel : ∀ n, ∑ k ∈ range n, a k =
      b 0 * R 0 - b n * R n + ∑ k ∈ range n, (b (k + 1) - b k) * R (k + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, sum_range_succ (f := fun k => (b (k + 1) - b k) * R (k + 1)),
        hR_succ n]
      ring
  have hfirst : Tendsto (fun n => b 0 * R 0 * (b n)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hb_top).const_mul (b 0 * R 0)
  have hthird := tendsto_inv_mul_sum_range_diff_mul_of_tendsto_zero hb_pos hb_mono hb_top
    (r := fun k => R (k + 1)) (hR_tendsto.comp (tendsto_add_atTop_nat 1))
  have hsum : Tendsto (fun n => b 0 * R 0 * (b n)⁻¹ - R n +
      (b n)⁻¹ * ∑ k ∈ range n, (b (k + 1) - b k) * R (k + 1)) atTop (𝓝 0) := by
    simpa using (hfirst.sub hR_tendsto).add hthird
  refine hsum.congr fun n => ?_
  have hbn : b n ≠ 0 := (hb_pos n).ne'
  rw [habel n]
  field_simp

/-- **Kronecker's lemma** from summability: if `b` is positive, monotone and divergent and
`∑ a k / b k` is summable, then `(b n)⁻¹ ∑_{k < n} a k → 0`. -/
theorem tendsto_inv_mul_sum_range_of_summable {a b : ℕ → ℝ} (hb_pos : ∀ n, 0 < b n)
    (hb_mono : Monotone b) (hb_top : Tendsto b atTop atTop)
    (hsum : Summable fun k => a k / b k) :
    Tendsto (fun n => (b n)⁻¹ * ∑ k ∈ range n, a k) atTop (𝓝 0) :=
  tendsto_inv_mul_sum_range_of_tendsto hb_pos hb_mono hb_top hsum.hasSum.tendsto_sum_nat

/-- Kronecker's lemma at `b k = k + 1`, restated with the plain normalisation `(n : ℝ)⁻¹`: if the
partial sums of `∑ a k / (k + 1)` converge, then `n⁻¹ ∑_{k < n} a k → 0`.

This is the form the strong law of large numbers uses.  The value at `n = 0` is irrelevant, the
limit being along `atTop`; `(0 : ℝ)⁻¹ = 0` there. -/
theorem tendsto_inv_natCast_mul_sum_range_of_tendsto {a : ℕ → ℝ} {S : ℝ}
    (hS : Tendsto (fun n : ℕ => ∑ k ∈ range n, a k / ((k : ℝ) + 1)) atTop (𝓝 S)) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ range n, a k) atTop (𝓝 0) := by
  have hmain : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ∑ k ∈ range n, a k) atTop (𝓝 0) :=
    tendsto_inv_mul_sum_range_of_tendsto (b := fun n : ℕ => (n : ℝ) + 1)
      (fun n => by positivity) (Nat.mono_cast.add_const 1)
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) hS
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 + ((n : ℝ))⁻¹) atTop (𝓝 1) := by
      simpa using
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_add (1 : ℝ)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    field_simp
  have := hratio.mul hmain
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  field_simp

end PCError

end
