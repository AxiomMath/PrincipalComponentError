[![](logo.svg)](https://axiommath.ai/)

# Principal Component Error in High-Dimensional Factor Models

This is a Lean formalization of the asymptotic error of the sample principal directions in a latent factor model, in the regime where the cross-section grows and the sample size stays fixed. The results are unconditional: the classical inputs the source cites are proved here rather than assumed.

## Main Results

* The error decomposition: the squared sine of the angle between the `j`-th sample principal direction and its target converges almost surely to an out-of-subspace error plus an in-subspace rotation error.
* The out-of-subspace error is estimable: the observable ratio of the average bulk eigenvalue to the `j`-th dual Gram eigenvalue converges to it almost surely.
* The rotation error is not estimable: with at least two factors, every value between the out-of-subspace floor and `1` is the limiting error of some admissible factor covariance.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on Mathlib. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
