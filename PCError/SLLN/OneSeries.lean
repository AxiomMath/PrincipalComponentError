/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Moments.Variance
public import PCError.Attr

/-!
# The Khinchine–Kolmogorov one-series theorem

If `Y i` are independent, centred and square-integrable with `∑ᵢ Var(Yᵢ) < ∞`, then the series
`∑ᵢ Yᵢ` converges almost surely.  This is
`PCError.ae_exists_tendsto_sum_range_of_summable_variance`.

The proof runs the partial sums through the almost-everywhere martingale convergence theorem.
Writing `Sₙ := ∑_{i ≤ n} Yᵢ` — indexed so that `Sₙ` is measurable with respect to
`MeasureTheory.Filtration.natural Y`, whose `n`-th σ-algebra already sees `Yₙ` — the increment
`S_{n+1} - Sₙ = Y_{n+1}` is independent of that σ-algebra and centred, so `S` is a martingale;
and `‖Sₙ‖₁ ≤ ‖Sₙ‖₂ = √(Var Sₙ) = √(∑_{i ≤ n} Var Yᵢ) ≤ √(∑ᵢ Var Yᵢ)` bounds it in `L¹`.
`MeasureTheory.Submartingale.ae_tendsto_limitProcess` — Doob's theorem, the analytic core —
then supplies almost sure convergence, and a shift of index turns `∑_{i ≤ n}` into `∑_{i < n}`.

## Main statements

* `PCError.eLpNorm_two_eq_ofReal_sqrt_variance`: on a probability space the `L²` seminorm of a
  centred `L²` random variable is the square root of its variance.
* `PCError.eLpNorm_one_le_ofReal_sqrt_variance`: the resulting `L¹` bound.
* `PCError.martingale_sum_range_succ`: the partial sums `∑_{i ≤ n} Yᵢ` of an independent centred
  integrable family form a martingale for the natural filtration.
* `PCError.ae_exists_tendsto_sum_range_of_summable_variance_of_stronglyMeasurable`,
  `PCError.ae_exists_tendsto_sum_range_of_summable_variance`: the **one-series theorem**, the
  second without a measurability hypothesis beyond `MemLp`.

## Implementation notes

`MeasureTheory.Filtration.natural` and hence the martingale argument need honest
`StronglyMeasurable` summands, whereas `MemLp` supplies only `AEStronglyMeasurable`.  The
`…_of_stronglyMeasurable` statement carries the stronger hypothesis and
`ae_exists_tendsto_sum_range_of_summable_variance` removes it by replacing each `Yᵢ`
with `AEStronglyMeasurable.mk`, transporting independence along
`ProbabilityTheory.iIndepFun.congr` and the moments along `integral_congr_ae` and
`ProbabilityTheory.variance_congr`.
-/

@[expose] public section

namespace PCError

open Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- On a probability space, the `L²` seminorm of a centred square-integrable real random variable
is the square root of its variance. -/
theorem eLpNorm_two_eq_ofReal_sqrt_variance [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (hmean : μ[f] = 0) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (Var[f; μ])) := by
  have he : evariance f μ = ENNReal.ofReal (Var[f; μ]) := hf.ofReal_variance_eq.symm
  have hpow : eLpNorm f 2 μ ^ (2 : ℝ) = ENNReal.ofReal (Var[f; μ]) := by
    rw [← he, evariance]
    simp only [hmean, sub_zero]
    have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2)
      (by norm_num) hf.aestronglyMeasurable
    push_cast at h
    rw [h]
    exact lintegral_congr fun ω => by rw [← ENNReal.rpow_natCast]; norm_num
  have key : eLpNorm f 2 μ ^ (2 : ℝ) = ENNReal.ofReal (Real.sqrt (Var[f; μ])) ^ (2 : ℝ) := by
    rw [hpow, ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (variance_nonneg f μ)]
  exact ENNReal.rpow_left_injective (x := 2) (by norm_num) key

/-- On a probability space, the `L¹` seminorm of a centred square-integrable real random variable
is at most the square root of its variance. -/
theorem eLpNorm_one_le_ofReal_sqrt_variance [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) (hmean : μ[f] = 0) :
    eLpNorm f 1 μ ≤ ENNReal.ofReal (Real.sqrt (Var[f; μ])) :=
  (eLpNorm_le_eLpNorm_of_exponent_le one_le_two).trans_eq
    (eLpNorm_two_eq_ofReal_sqrt_variance hf hmean)

/-- The partial sums `∑_{i ≤ n} Yᵢ` of an independent, centred, integrable family of random
variables valued in a separable Banach space form a martingale for the natural filtration of `Y`.

The sum runs over `i ≤ n` rather than `i < n` because the `n`-th σ-algebra of
`MeasureTheory.Filtration.natural Y` already sees `Yₙ`; with that indexing the increment
`S_{n+1} - Sₙ = Y_{n+1}` is independent of the past, which is what makes `S` a martingale. -/
theorem martingale_sum_range_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Y : ℕ → Ω → E) (hmeas : ∀ i, StronglyMeasurable (Y i)) (hint : ∀ i, Integrable (Y i) μ)
    (hindep : iIndepFun Y μ) (hmean : ∀ i, μ[Y i] = 0) :
    Martingale (fun n => ∑ i ∈ range (n + 1), Y i) (Filtration.natural Y hmeas) μ := by
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  refine martingale_of_condExp_sub_eq_zero_nat (fun n => ?_) (fun n => ?_) (fun n => ?_)
  · exact Finset.stronglyMeasurable_sum _ fun i hi =>
      (Filtration.stronglyAdapted_natural hmeas i).mono
        ((Filtration.natural Y hmeas).mono (Nat.lt_succ_iff.mp (mem_range.mp hi)))
  · exact integrable_finsetSum' _ fun i _ => hint i
  · have hdiff : (∑ i ∈ range (n + 1 + 1), Y i) - (∑ i ∈ range (n + 1), Y i) = Y (n + 1) := by
      funext ω; simp [Finset.sum_range_succ]
    rw [hdiff]
    filter_upwards [hindep.condExp_natural_ae_eq_of_lt hmeas (show n < n + 1 by omega)]
      with ω hω
    rw [hω, hmean]
    rfl

/-- **Khinchine–Kolmogorov one-series theorem**, for strongly measurable summands: if the real
random variables `Y i` on a probability space are independent, centred, square-integrable and
have summable variances, then almost surely the series `∑ᵢ Yᵢ` converges.

See `PCError.ae_exists_tendsto_sum_range_of_summable_variance` for the version without the
measurability hypothesis. -/
theorem ae_exists_tendsto_sum_range_of_summable_variance_of_stronglyMeasurable (Y : ℕ → Ω → ℝ)
    (hmeas : ∀ i, StronglyMeasurable (Y i)) (hY : ∀ i, MemLp (Y i) 2 μ)
    (hindep : iIndepFun Y μ) (hmean : ∀ i, μ[Y i] = 0)
    (hvar : Summable fun i => Var[Y i; μ]) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => ∑ i ∈ range n, Y i ω) atTop (𝓝 c) := by
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  have hint : ∀ i, Integrable (Y i) μ := fun i => (hY i).integrable one_le_two
  have hmart := martingale_sum_range_succ Y hmeas hint hindep hmean
  have hbdd : ∀ n, eLpNorm (∑ i ∈ range (n + 1), Y i) 1 μ ≤
      ENNReal.ofReal (Real.sqrt (∑' i, Var[Y i; μ])) := by
    intro n
    have hLp : MemLp (∑ i ∈ range (n + 1), Y i) 2 μ := memLp_finsetSum' _ fun i _ => hY i
    have hm0 : μ[∑ i ∈ range (n + 1), Y i] = 0 := by
      simp only [Finset.sum_apply]
      rw [integral_finsetSum _ fun i _ => hint i]
      exact Finset.sum_eq_zero fun i _ => hmean i
    have hvarsum : Var[∑ i ∈ range (n + 1), Y i; μ] = ∑ i ∈ range (n + 1), Var[Y i; μ] :=
      IndepFun.variance_sum (fun i _ => hY i) fun i _ j _ hij => hindep.indepFun hij
    refine (eLpNorm_one_le_ofReal_sqrt_variance hLp hm0).trans ?_
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    rw [hvarsum]
    exact hvar.sum_le_tsum _ fun i _ => variance_nonneg _ _
  filter_upwards [hmart.submartingale.ae_tendsto_limitProcess hbdd] with ω hω
  simp only [Finset.sum_apply] at hω
  exact ⟨_, (tendsto_add_atTop_iff_nat 1).mp hω⟩

/-- **Khinchine–Kolmogorov one-series theorem**: if the real random variables `Y i` on a
probability space are independent, centred and square-integrable with summable variances, then
almost surely the series `∑ᵢ Yᵢ` converges.

Only `MemLp (Y i) 2 μ` is assumed, not strong measurability; the martingale argument, which needs
the latter, is run on the modifications `AEStronglyMeasurable.mk`. -/
theorem ae_exists_tendsto_sum_range_of_summable_variance (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, MemLp (Y i) 2 μ) (hindep : iIndepFun Y μ) (hmean : ∀ i, μ[Y i] = 0)
    (hvar : Summable fun i => Var[Y i; μ]) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => ∑ i ∈ range n, Y i ω) atTop (𝓝 c) := by
  have : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  set Z : ℕ → Ω → ℝ := fun i => (hY i).aestronglyMeasurable.mk (Y i)
  have hae : ∀ i, Y i =ᵐ[μ] Z i := fun i => (hY i).aestronglyMeasurable.ae_eq_mk
  have hZmeas : ∀ i, StronglyMeasurable (Z i) := fun i =>
    (hY i).aestronglyMeasurable.stronglyMeasurable_mk
  have hZLp : ∀ i, MemLp (Z i) 2 μ := fun i => (hY i).ae_eq (hae i)
  have hZmean : ∀ i, μ[Z i] = 0 := fun i => (integral_congr_ae (hae i)).symm.trans (hmean i)
  have hZvar : ∀ i, Var[Z i; μ] = Var[Y i; μ] := fun i => (variance_congr (hae i)).symm
  have hZsum : Summable fun i => Var[Z i; μ] := by
    simpa only [hZvar] using hvar
  have key := ae_exists_tendsto_sum_range_of_summable_variance_of_stronglyMeasurable Z hZmeas
    hZLp (iIndepFun.congr hae hindep) hZmean hZsum
  filter_upwards [key, ae_all_iff.mpr hae] with ω hω hall
  obtain ⟨c, hc⟩ := hω
  exact ⟨c, hc.congr fun n => Finset.sum_congr rfl fun i _ => (hall i).symm⟩

end PCError

end
