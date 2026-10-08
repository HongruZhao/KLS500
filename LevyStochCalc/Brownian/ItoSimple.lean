/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoSimpleIntegrand
import LevyStochCalc.Brownian.ItoSimpleMoments
import LevyStochCalc.Brownian.ItoSimpleIsometry

/-!
# Brownian Itô integral on simple predictable integrands

The simple predictable integrands `∑_i ξ_i · 1_{(t_i, t_{i+1}]}` for a scalar
Brownian motion `W`, their integral `simpleIntegral`, and the L²-isometry on
this class (`simpleIntegral_isometry`, `simpleIntegral_L2_isometry_brownian`).
L²-density of simple predictables is in `Brownian/ItoDensity.lean`; the
martingale property in `Brownian/ItoMartingale.lean`.

The material is divided into `Brownian/ItoSimpleIntegrand.lean` (the integrand class, the
elementary integral and the energy of the integrand), `Brownian/ItoSimpleMoments.lean` (the
second moments of the terms of that integral) and `Brownian/ItoSimpleIsometry.lean` (the
isometry itself).
-/
