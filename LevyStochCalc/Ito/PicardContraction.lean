/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardContractionEstimate
import LevyStochCalc.Ito.PicardContractionFixedPoint

/-!
# The Picard self-map is a Bielecki contraction

The contraction estimate for the Picard step transfers to the self-map and to the step taken
against a raw state process, the iterates converge in Bielecki norm, and their limit is a fixed
point of the step. The development is split over the following files.

* `LevyStochCalc.Ito.PicardContractionEstimate` — the contraction estimate for the step, for the
  self-map and against a raw state process, and the geometric convergence of the iterates.
* `LevyStochCalc.Ito.PicardContractionFixedPoint` — the limit of the iterates, its Bielecki
  bounds, and the Picard equation it solves along its own path.
-/
