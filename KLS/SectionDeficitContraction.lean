import KLS.MomentSectionEngulfing

/-! The quantitative contraction underlying a gradient modulus. Comparable
opposite support deficits force a dyadic contraction strictly better than
one half. Neither a Hölder exponent nor Hessian regularity is assumed. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def supportDeficit (u : Space n → ℝ) (x p y : Space n) : ℝ :=
  u y - u x - inner ℝ p (y - x)

theorem supportDeficit_nonneg {u : Space n → ℝ} {x p : Space n}
    (hp : p ∈ convexSubgradient u x) (y : Space n) : 0 ≤ supportDeficit u x p y := by
  have hh := hp y
  dsimp [supportDeficit]
  linarith

theorem supportDeficit_self (u : Space n → ℝ) (x p : Space n) : supportDeficit u x p x = 0 := by
  simp [supportDeficit]

def sectionDeficitContractionFactor (C : ℝ) : ℝ := C / (2 * C + 1)

theorem sectionDeficitContractionFactor_pos_lt_half {C : ℝ} (hC : 0 < C) :
    0 < sectionDeficitContractionFactor C ∧ sectionDeficitContractionFactor C < 1 / 2 := by
  unfold sectionDeficitContractionFactor
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0 < 2 * C + 1)).mpr
    linarith

/-- Opposite support-deficit comparison at the midpoint yields a contraction
strictly stronger than the ordinary convexity factor one half. -/
theorem supportDeficit_midpoint_contraction
    {u : Space n → ℝ} {x y z p q : Space n}
    (hq : q ∈ convexSubgradient u y) (hmid : z - y = y - x)
    {C : ℝ} (hC : 0 < C)
    (hcompare : supportDeficit u x p y ≤ C * supportDeficit u y q x) :
    supportDeficit u x p y ≤ sectionDeficitContractionFactor C * supportDeficit u x p z := by
  have hqz := hq z
  have hzx : z - x = (y - x) + (y - x) := by
    calc
      _ = (z - y) + (y - x) := by abel
      _ = (y - x) + (y - x) := by rw [hmid]
  have hxy : x - y = -(y - x) := by abel
  have hgap : 2 * supportDeficit u x p y + supportDeficit u y q x ≤
      supportDeficit u x p z := by
    dsimp [supportDeficit]
    rw [hmid] at hqz
    rw [hzx, inner_add_right, hxy, inner_neg_right]
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hgap hC.le
  unfold sectionDeficitContractionFactor
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * C + 1)).mpr
  nlinarith

def dyadicSectionPoint (x v : Space n) (k : ℕ) : Space n :=
  x + ((1 / 2 : ℝ) ^ k) • v

theorem dyadicSectionPoint_step (x v : Space n) (k : ℕ) :
    dyadicSectionPoint x v k - dyadicSectionPoint x v (k + 1) =
      dyadicSectionPoint x v (k + 1) - x := by
  dsimp [dyadicSectionPoint]
  rw [pow_succ]
  module

/-- The actual midpoint estimate is iterated at every dyadic scale. The
comparison premise may be supplied by two-center section engulfing; it is
not a Hölder or differentiability premise. -/
theorem supportDeficit_dyadic_le
    {u : Space n → ℝ} {x p v : Space n} {C : ℝ} (hC : 0 < C)
    (hcompare : ∀ k : ℕ, ∃ q ∈ convexSubgradient u (dyadicSectionPoint x v (k + 1)),
      supportDeficit u x p (dyadicSectionPoint x v (k + 1)) ≤
        C * supportDeficit u (dyadicSectionPoint x v (k + 1)) q x) :
    ∀ k : ℕ, supportDeficit u x p (dyadicSectionPoint x v k) ≤
      (sectionDeficitContractionFactor C) ^ k * supportDeficit u x p (x + v) := by
  intro k
  induction k with
  | zero => simp [dyadicSectionPoint]
  | succ k ih =>
      obtain ⟨q, hq, hcomp⟩ := hcompare k
      have hstep := supportDeficit_midpoint_contraction hq (dyadicSectionPoint_step x v k) hC hcomp
      have hκ := (sectionDeficitContractionFactor_pos_lt_half hC).1
      calc
        _ ≤ sectionDeficitContractionFactor C * supportDeficit u x p (dyadicSectionPoint x v k) := hstep
        _ ≤ sectionDeficitContractionFactor C *
            (sectionDeficitContractionFactor C ^ k * supportDeficit u x p (x + v)) :=
          mul_le_mul_of_nonneg_left ih hκ.le
        _ = sectionDeficitContractionFactor C ^ (k + 1) * supportDeficit u x p (x + v) := by
          rw [pow_succ]
          ring

end KLS
end

#print axioms KLS.sectionDeficitContractionFactor_pos_lt_half
#print axioms KLS.supportDeficit_midpoint_contraction
#print axioms KLS.supportDeficit_dyadic_le
