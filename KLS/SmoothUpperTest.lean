import KLS.HessianMetricComposition
import KLS.WeightedOptimalPoincare
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology ContDiff ENNReal RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The derivative of the actual smooth monotone transition has compact support. -/
theorem hasCompactSupport_deriv_smoothTransition : HasCompactSupport (deriv Real.smoothTransition) := by
  apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (s := Icc (0 : ℝ) 1)
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  simp only [mem_Icc, not_and_or, not_le] at hn
  apply hx
  rcases hn with hx0 | hx1
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hx0] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.deriv_eq]
    simp
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_nhds hx1] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.deriv_eq]
    simp

/-- Its derivative is nonnegative and uniformly bounded by a finite constant. -/
theorem exists_deriv_smoothTransition_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, 0 ≤ deriv Real.smoothTransition x ∧
      ‖deriv Real.smoothTransition x‖ ≤ B := by
  have hcont : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hasCompactSupport_deriv_smoothTransition
  exact ⟨max B 0, le_max_right _ _, fun x =>
    ⟨Real.smoothTransition.monotone.deriv_nonneg, (hB x).trans (le_max_left _ _)⟩⟩

/-- A bounded monotone smooth test detecting the strict upper level set. -/
def smoothUpperTest (f : Space n → ℝ) (M : ℝ) (x : Space n) : ℝ :=
  Real.smoothTransition (f x - M)

theorem smoothUpperTest_contDiff {f : Space n → ℝ} {k : ℕ∞}
    (hf : ContDiff ℝ k f) (M : ℝ) : ContDiff ℝ k (smoothUpperTest f M) :=
  Real.smoothTransition.contDiff.comp (hf.sub contDiff_const)

theorem smoothUpperTest_nonneg (f : Space n → ℝ) (M : ℝ) (x : Space n) :
    0 ≤ smoothUpperTest f M x := Real.smoothTransition.nonneg _

theorem smoothUpperTest_pos {f : Space n → ℝ} {M : ℝ} {x : Space n}
    (hx : M < f x) : 0 < smoothUpperTest f M x :=
  Real.smoothTransition.pos_of_pos (sub_pos.mpr hx)

theorem smoothUpperTest_eq_zero {f : Space n → ℝ} {M : ℝ} {x : Space n}
    (hx : f x ≤ M) : smoothUpperTest f M x = 0 :=
  Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx)

theorem coordinateDerivative_smoothUpperTest {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (M : ℝ) (i : Fin n) (x : Space n) :
    coordinateDerivative (smoothUpperTest f M) i x =
      deriv Real.smoothTransition (f x - M) * coordinateDerivative f i x := by
  change coordinateDerivative (fun y => Real.smoothTransition (f y - M)) i x = _
  rw [coordinateDerivative_scalar_comp
    ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _)
    ((hf.sub contDiff_const).differentiable one_ne_zero _)]
  simp only [coordinateDerivative, fderiv_sub_const]

/-- Boundedness and the actual scalar chain rule place this test in the
original faithful finite-energy class. -/
theorem smoothUpperTest_faithful {φ f : Space n → ℝ}
    [IsProbabilityMeasure (potentialMeasure φ)] (hf : ContDiff ℝ 1 f)
    (hd : ∀ i : Fin n, MemLp (coordinateDerivative f i) 2 (potentialMeasure φ)) (M : ℝ) :
    LocallyLipschitzTests (potentialMeasure φ) (smoothUpperTest f M) ∧
      energy (potentialMeasure φ) (smoothUpperTest f M) < ⊤ := by
  have hs := smoothUpperTest_contDiff hf M
  have hs2 : MemLp (smoothUpperTest f M) 2 (potentialMeasure φ) := by
    apply MemLp.of_bound hs.continuous.aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (smoothUpperTest_nonneg f M x)]
      exact Real.smoothTransition.le_one _
  obtain ⟨B, _, hB⟩ := exists_deriv_smoothTransition_bound
  have hds (i : Fin n) : MemLp (coordinateDerivative (smoothUpperTest f M) i) 2
      (potentialMeasure φ) := by
    apply ((hd i).norm.const_mul B).mono'
      (contDiff_coordinateDerivative hs (m := 0) (by norm_num) i).continuous.aestronglyMeasurable
    refine Eventually.of_forall fun x => ?_
    rw [coordinateDerivative_smoothUpperTest hf, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB _).2 (norm_nonneg _)
  exact ⟨⟨hs.locallyLipschitz, hs2⟩, energy_lt_top_of_memLp_coordinateDerivative hds⟩

/-- The genuine gradient pairing with this upper-level test is nonnegative. -/
theorem smoothUpperTest_gradient_pairing_nonneg {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (M : ℝ) (i : Fin n) (x : Space n) :
    0 ≤ coordinateDerivative f i x * coordinateDerivative (smoothUpperTest f M) i x := by
  rw [coordinateDerivative_smoothUpperTest hf]
  nlinarith [Real.smoothTransition.monotone.deriv_nonneg (x := f x - M),
    sq_nonneg (coordinateDerivative f i x)]

end KLS
end
