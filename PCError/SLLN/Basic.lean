/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import PCError.Attr
public import PCError.External
public import PCError.SLLN.Kronecker
public import PCError.SLLN.OneSeries

/-!
# Kolmogorov's strong law of large numbers

`PCError.kolmogorovSLLN` proves `PCError.KolmogorovSLLN`, the statement the development used to
assume: for independent, not necessarily identically distributed real random variables `X i` with
`MemLp (X i) 2 μ` and `∑ᵢ Var(Xᵢ)/(i+1)² < ∞`, almost surely

`p⁻¹ ∑_{i < p} (Xᵢ - 𝔼[Xᵢ]) → 0`.

Two inputs do the work, each proved here and each a Mathlib gap in its own right:

* `PCError.ae_exists_tendsto_sum_range_of_summable_variance` — the Khinchine–Kolmogorov one-series
  theorem, applied to the normalised summands `Yᵢ := (i + 1)⁻¹ (Xᵢ - 𝔼[Xᵢ])`, whose variances are
  `Var(Xᵢ)/(i+1)²` and hence summable by hypothesis.  It gives almost sure convergence of
  `∑ᵢ (Xᵢ - 𝔼[Xᵢ])/(i + 1)`.
* `PCError.tendsto_inv_natCast_mul_sum_range_of_tendsto` — Kronecker's lemma, applied pointwise at
  each `ω` where that series converges, which converts convergence of `∑ᵢ aᵢ/(i + 1)` into
  `p⁻¹ ∑_{i < p} aᵢ → 0`.

Independence of the `Yᵢ` comes from independence of the `Xᵢ` through
`ProbabilityTheory.iIndepFun.comp`; no measurability beyond `MemLp` is needed, since the
one-series theorem takes care of that itself.

## Main statements

* `PCError.kolmogorovSLLN`: **Kolmogorov's strong law of large numbers** under Kolmogorov's
  variance criterion, i.e. a proof of `PCError.KolmogorovSLLN`.
-/

@[expose] public section

namespace PCError

open Filter Finset MeasureTheory ProbabilityTheory
open scoped Topology

universe u

/-- **Kolmogorov's strong law of large numbers** for independent, not necessarily identically
distributed summands under Kolmogorov's variance criterion, in the packaged form
`PCError.KolmogorovSLLN` in which `PCError.External` states it. -/
@[pcerror "lem_slln"]
theorem kolmogorovSLLN : KolmogorovSLLN.{u} := by
  intro Ω _ μ _ X hX hindep hsum
  have hint : ∀ i, Integrable (X i) μ := fun i => (hX i).integrable one_le_two
  set Y : ℕ → Ω → ℝ := fun i ω => ((i : ℝ) + 1)⁻¹ * (X i ω - μ[X i]) with hYdef
  have hYLp : ∀ i, MemLp (Y i) 2 μ := fun i =>
    ((hX i).sub (memLp_const _)).const_mul _
  have hYmean : ∀ i, μ[Y i] = 0 := by
    intro i
    simp only [hYdef, integral_const_mul, integral_sub (hint i) (integrable_const _),
      integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, mul_zero]
  have hYvar : ∀ i, Var[Y i; μ] = Var[X i; μ] / ((i : ℝ) + 1) ^ 2 := by
    intro i
    rw [hYdef, variance_const_mul, variance_sub_const (hX i).aestronglyMeasurable, inv_pow,
      inv_mul_eq_div]
  have hYindep : iIndepFun Y μ := by
    have h : iIndepFun (fun i : ℕ => (fun x : ℝ => ((i : ℝ) + 1)⁻¹ * (x - μ[X i])) ∘ X i) μ :=
      hindep.comp _ fun i => (measurable_id.sub_const _).const_mul _
    exact h
  have hYsum : Summable fun i => Var[Y i; μ] := by
    simpa only [hYvar] using hsum
  filter_upwards [ae_exists_tendsto_sum_range_of_summable_variance Y hYLp hYindep hYmean hYsum]
    with ω hω
  obtain ⟨c, hc⟩ := hω
  refine tendsto_inv_natCast_mul_sum_range_of_tendsto (S := c) (hc.congr fun n => ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hYdef, div_eq_inv_mul]

end PCError

end
