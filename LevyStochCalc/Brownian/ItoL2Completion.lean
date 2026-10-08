/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoL2CompletionLp
import LevyStochCalc.Brownian.ItoL2CompletionExistence
import LevyStochCalc.Brownian.ItoL2CompletionIncrement
import LevyStochCalc.Brownian.ItoL2CompletionConvergence
import LevyStochCalc.Brownian.ItoL2CompletionCompensator
import LevyStochCalc.Brownian.ItoL2CompletionMaster
import LevyStochCalc.Brownian.ItoL2CompletionQuadVar
import LevyStochCalc.Brownian.ItoL2CompletionApi

/-!
# Brownian Itô integral via L²-completion

Lifts the simple-integrand Brownian integral to `Lp ℝ 2 P`, takes the L²-limit
along a dense approximating sequence, and proves the L²-isometry of the limit,
giving the L² Brownian Itô integral of a progressively measurable integrand with
respect to any filtration `ℱ` for which `W` is a Brownian motion
(`IsBrownianFiltration W ℱ`). The result is packaged as the theorem
`itoIsometry_brownian_unified_existence` (cited result #5) and the
`stochasticIntegral` API (`itoIsometry`, `quadVar_stochasticIntegral`,
`martingale_stochasticIntegral`). Builds on the refinement machinery in
`Brownian/SimplePredictableRefine.lean`.

This module is the aggregator of the development, which is split into the parts

* `Brownian/ItoL2CompletionLp.lean` — the `L²` lift of the simple-integrand integral;
* `Brownian/ItoL2CompletionExistence.lean` — existence of the `L²` integral;
* `Brownian/ItoL2CompletionIncrement.lean` — increment expansions and the
  intermediate-time isometry;
* `Brownian/ItoL2CompletionConvergence.lean` — `L¹`/`L²` convergence and adapted
  approximation;
* `Brownian/ItoL2CompletionCompensator.lean` — the compensated square of a simple
  integral;
* `Brownian/ItoL2CompletionMaster.lean` — the master approximating sequence and
  `stochasticIntegralBrownian`;
* `Brownian/ItoL2CompletionQuadVar.lean` — isometry, right continuity and quadratic
  variation;
* `Brownian/ItoL2CompletionApi.lean` — the `stochasticIntegral` API.
-/
