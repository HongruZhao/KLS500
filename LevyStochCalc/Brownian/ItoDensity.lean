/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoDensityDyadicAverages
import LevyStochCalc.Brownian.ItoDensityShiftedAverages
import LevyStochCalc.Brownian.ItoDensityPointwise
import LevyStochCalc.Brownian.ItoDensityPredictableL2
import LevyStochCalc.Brownian.ItoDensityUnbounded

/-!
# Density of simple predictable processes in L²

Dyadic approximation of `L²(Ω × [0,T])` integrands by simple predictable
processes, giving the density results `simplePredictable_dense_L2` and
`adaptedSimple_dense_L2_brownian` that extend the Itô integral off the simple
class. Builds on `Brownian/ItoSimple.lean`.

The development is split into
`Brownian/ItoDensityDyadicAverages.lean` (truncation and the dyadic cell averages),
`Brownian/ItoDensityShiftedAverages.lean` (left-shifted averages and cell-average identities),
`Brownian/ItoDensityPointwise.lean` (almost-everywhere convergence of the averages),
`Brownian/ItoDensityPredictableL2.lean` (`L²` convergence in the bounded case) and
`Brownian/ItoDensityUnbounded.lean` (the density results in general).
-/
