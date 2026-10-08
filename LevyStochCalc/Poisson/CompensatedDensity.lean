/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedDensityTruncation
import LevyStochCalc.Poisson.CompensatedDensityDyadic
import LevyStochCalc.Poisson.CompensatedDensityShifted
import LevyStochCalc.Poisson.CompensatedDensityRectSimple
import LevyStochCalc.Poisson.CompensatedDensityMarkApprox
import LevyStochCalc.Poisson.CompensatedDensityStepIntegral
import LevyStochCalc.Poisson.CompensatedDensityBoxIsometry
import LevyStochCalc.Poisson.CompensatedDensityMarkSum
import LevyStochCalc.Poisson.CompensatedDensityRefinement
import LevyStochCalc.Poisson.CompensatedDensityLimit

/-!
# Density of adapted simple predictable integrands (compensated Poisson)

Toward the L²-completion of the compensated-Poisson simple integral: adapted
`SimplePredictable` integrands are dense in `L²(P ⊗ ds ⊗ ν)`. The construction
reduces a general predictable square-integrable integrand `φ : Ω → ℝ → E → ℝ` to a
bounded one by truncation, then discretizes time and the mark space, and passes to
the limit in `L²(P)`. Compensated mirror of `Brownian/ItoDensity.lean`.

This module collects the development, which is spread over the following parts.

* `CompensatedDensityTruncation`: value and mark truncation of a square-integrable integrand.
* `CompensatedDensityDyadic`: dyadic time-discretisation with the mark carried as a parameter.
* `CompensatedDensityShifted`: the adapted (left-shifted) dyadic eval.
* `CompensatedDensityRectSimple`: rectangle-simple functions and their `L²` density.
* `CompensatedDensityMarkApprox`: mark discretisation of the shifted dyadic eval.
* `CompensatedDensityStepIntegral`: step (finite-sum) predictable integrands.
* `CompensatedDensityBoxIsometry`: weighted covariances of compensated boxes.
* `CompensatedDensityMarkSum`: the mark-sum process and its `L²` isometry.
* `CompensatedDensityRefinement`: Doob `L²` bricks and dyadic cross-resolution refinement.
* `CompensatedDensityLimit`: the cross-resolution Cauchy estimate and the `L²` limit.
-/
