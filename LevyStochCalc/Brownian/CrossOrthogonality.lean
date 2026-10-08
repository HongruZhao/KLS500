/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.CrossOrthogonalityDirectCross
import LevyStochCalc.Brownian.CrossOrthogonalityLimit

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

For a `d`-dimensional Brownian motion `W` whose coordinates are all Brownian motions for one
filtration `ℱ`, and distinct coordinates `i ≠ j`, integrals against `Wⁱ` and against `Wʲ` are
orthogonal in `L²`. The development is split into two parts:

* `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross`: the identity
  `E[Z (Wⁱ_b - Wⁱ_a)(Wʲ_b - Wʲ_a)] = 0` for a bounded `ℱ_a`-measurable weight `Z`, obtained from a
  uniform grid of `[a, b]` along which the product of the two increments telescopes.
* `LevyStochCalc.Brownian.CrossOrthogonalityLimit`: cross terms over intervals in any relative
  position, orthogonality on elementary integrands, and its passage to the Itô integrals by
  continuity of the `L²` pairing.
-/
