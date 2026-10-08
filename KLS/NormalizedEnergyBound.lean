import KLS.NormalizedSubharmonicDistribution
import KLS.SubharmonicEnergy

open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma contDiff_normalizedQuadraticError {u : Space n → ℝ} (hu : ContDiff ℝ 1 u)
    (x₀ p : Space n) (c ε : ℝ) : ContDiff ℝ 1 (normalizedQuadraticError u x₀ p c ε) :=
  (hu.sub ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp))).div_const ε

lemma contDiff_subharmonicNormalizedError {u : Space n → ℝ} (hu : ContDiff ℝ 1 u)
    (x₀ p : Space n) (c ε : ℝ) : ContDiff ℝ 1 (subharmonicNormalizedError u x₀ p c ε) :=
  (contDiff_normalizedQuadraticError hu _ _ _ _).add
    (contDiff_const.mul ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp)))

lemma subharmonicNormalizedError_apply (u : Space n → ℝ) (x₀ p : Space n) (c ε : ℝ) (x : Space n) :
    subharmonicNormalizedError u x₀ p c ε x =
      normalizedQuadraticError u x₀ p c ε x + ε * ‖x-x₀‖ ^ 2 := by
  simp only [subharmonicNormalizedError, centeredQuadratic, inner_zero_left, zero_add,
    matrixAction_one_apply, real_inner_self_eq_norm_sq]
  ring

lemma coordinateDerivative_subharmonicNormalizedError {u : Space n → ℝ}
    (hu : ContDiff ℝ 1 u) (x₀ p : Space n) (c ε : ℝ) (i : Fin n) (x : Space n) :
    coordinateDerivative (subharmonicNormalizedError u x₀ p c ε) i x =
      coordinateDerivative (normalizedQuadraticError u x₀ p c ε) i x + 2 * ε * (x-x₀) i := by
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x₀ 0 0
  have hq : ContDiff ℝ 1 q := (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  have hqd (x : Space n) : coordinateDerivative q i x = (x-x₀) i := by
    rw [coordinateDerivative_eq_gradient, gradient_centeredQuadratic Matrix.PosSemidef.one]
    simp only [matrixAction_one_apply, zero_add]
  change coordinateDerivative (fun y => normalizedQuadraticError u x₀ p c ε y +
    (2 * ε) * q y) i x = _
  change coordinateDerivative (normalizedQuadraticError u x₀ p c ε +
    (fun y => (2 * ε) * q y)) i x = _
  rw [coordinateDerivative_add (f := normalizedQuadraticError u x₀ p c ε)
    (g := fun y => (2 * ε) * q y)
    ((contDiff_normalizedQuadraticError hu _ _ _ _).differentiable (by norm_num) x)
    ((contDiff_const.mul hq).differentiable (by norm_num) x)]
  have hs := coordinateDerivative_smul (hq.differentiable (by norm_num) x) (2 * ε) i
  rw [show coordinateDerivative (fun y => (2 * ε) * q y) i x =
    (2 * ε) * coordinateDerivative q i x from hs, hqd]

/-- Uniform local energy for the corrected normalized function follows from
its actual Monge--Ampere equation and a bound on the original normalized error. -/
theorem subharmonicNormalizedError_caccioppoli (hn : 0 < n)
    {u f χ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (x₀ p : Space n) (c : ℝ) {ε r R S M : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R) (hrR : r < R) (hRS : R < S)
    (hχs : tsupport χ ⊆ closedBall x₀ r)
    (hdensity : ∀ x ∈ closedBall x₀ S, |f x - 1| ≤ ε ^ 2)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ tsupport χ, |normalizedQuadraticError u x₀ p c ε x| ≤ M) :
    (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative (subharmonicNormalizedError u x₀ p c ε) i x ^ 2) ≤
      16 * (M + r ^ 2) ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) := by
  apply bounded_subharmonic_caccioppoli hχ (contDiff_subharmonicNormalizedError hu _ _ _ _)
    hχc hrR hχs
    (fun ψ hψ hψc hψs hψ0 => integral_subharmonicNormalizedError_mul_laplacian_nonneg hn
      hu.continuous huc hf hMA x₀ p c hε hεhalf hR hRS hdensity hψ hψc hψs hψ0)
    (by positivity)
  intro x hx
  rw [subharmonicNormalizedError_apply]
  have hxnorm : ‖x-x₀‖ ≤ r := hχs hx
  have hxr : ‖x-x₀‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (x-x₀)]
  calc
    _ ≤ |normalizedQuadraticError u x₀ p c ε x| + |ε * ‖x-x₀‖ ^ 2| := abs_add_le _ _
    _ = |normalizedQuadraticError u x₀ p c ε x| + ε * ‖x-x₀‖ ^ 2 := by
      rw [abs_of_nonneg (show 0 ≤ ε * ‖x-x₀‖ ^ 2 by positivity)]
    _ ≤ M + r ^ 2 := by
      have hb := hbound x hx
      nlinarith [sq_nonneg r]


/-- The actual normalized error itself has a uniform local gradient energy
bound; the vanishing quadratic used to prove subharmonicity is removed. -/
theorem normalizedQuadraticError_caccioppoli (hn : 0 < n)
    {u f χ : Space n → ℝ} (hu : ContDiff ℝ 1 u) (huc : ConvexOn ℝ univ u)
    (hf : Continuous f)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (x₀ p : Space n) (c : ℝ) {ε r R S M : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R) (hrR : r < R) (hRS : R < S)
    (hχs : tsupport χ ⊆ closedBall x₀ r)
    (hdensity : ∀ x ∈ closedBall x₀ S, |f x - 1| ≤ ε ^ 2)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ tsupport χ, |normalizedQuadraticError u x₀ p c ε x| ≤ M) :
    (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative (normalizedQuadraticError u x₀ p c ε) i x ^ 2) ≤
      32 * (M + r ^ 2) ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) +
        2 * n * r ^ 2 * (∫ x, χ x ^ 2) := by
  let w := normalizedQuadraticError u x₀ p c ε
  let z := subharmonicNormalizedError u x₀ p c ε
  have hw : ContDiff ℝ 1 w := contDiff_normalizedQuadraticError hu _ _ _ _
  have hz : ContDiff ℝ 1 z := contDiff_subharmonicNormalizedError hu _ _ _ _
  have hb := subharmonicNormalizedError_caccioppoli hn hu huc hf hMA hχ hχc x₀ p c
    hε hεhalf hR hrR hRS hχs hdensity hM hbound
  have hint {g : Space n → ℝ} (hg : ContDiff ℝ 1 g) :
      Integrable (fun x => ∑ i, χ x ^ 2 * coordinateDerivative g i x ^ 2) := by
    apply integrable_finsetSum
    intro i _
    exact ((hχ.continuous.pow 2).mul
      ((contDiff_coordinateDerivative hg (m := 0) (by norm_num) i).continuous.pow 2)).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using hχc.mul_right.mul_right)
  have hχ2 : Integrable (fun x => χ x ^ 2) :=
    (hχ.continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using hχc.mul_right)
  have hpoint (x : Space n) : (∑ i, χ x ^ 2 * coordinateDerivative w i x ^ 2) ≤
      2 * (∑ i, χ x ^ 2 * coordinateDerivative z i x ^ 2) + 2 * n * r ^ 2 * χ x ^ 2 := by
    by_cases hx : x ∈ tsupport χ
    · have hxnorm : ‖x-x₀‖ ≤ r := hχs hx
      have hr : 0 ≤ r := (norm_nonneg _).trans hxnorm
      have hi (i : Fin n) : χ x ^ 2 * coordinateDerivative w i x ^ 2 ≤
          2 * (χ x ^ 2 * coordinateDerivative z i x ^ 2) + 2 * r ^ 2 * χ x ^ 2 := by
        have hcoord : |(x-x₀) i| ≤ r := (PiLp.norm_apply_le (x-x₀) i).trans hxnorm
        have hcorr : |2 * ε * (x-x₀) i| ≤ r := by
          rw [abs_mul, abs_of_nonneg (show 0 ≤ 2 * ε by positivity)]
          have hmul := mul_le_mul_of_nonneg_left hcoord (show 0 ≤ 2 * ε by positivity)
          nlinarith
        have hcorr2 : (2 * ε * (x-x₀) i) ^ 2 ≤ r ^ 2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hr).mpr hcorr
        have hd := coordinateDerivative_subharmonicNormalizedError hu x₀ p c ε i x
        change coordinateDerivative z i x = coordinateDerivative w i x + 2 * ε * (x-x₀) i at hd
        have he : coordinateDerivative w i x ^ 2 ≤ 2 * coordinateDerivative z i x ^ 2 + 2 * r ^ 2 := by
          rw [hd]
          nlinarith [sq_nonneg (coordinateDerivative w i x + 4 * ε * (x-x₀) i)]
        have hm := mul_le_mul_of_nonneg_left he (sq_nonneg (χ x))
        nlinarith
      calc
        _ ≤ ∑ i, (2 * (χ x ^ 2 * coordinateDerivative z i x ^ 2) + 2 * r ^ 2 * χ x ^ 2) :=
          Finset.sum_le_sum (fun i _ => hi i)
        _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
    · simp only [image_eq_zero_of_notMem_tsupport hx, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, le_refl]
  have hI := integral_mono (hint hw) ((hint hz).const_mul 2 |>.add (hχ2.const_mul (2 * n * r ^ 2))) hpoint
  simp only [Pi.add_apply] at hI
  rw [integral_add ((hint hz).const_mul 2) (hχ2.const_mul (2 * n * r ^ 2)),
    integral_const_mul, integral_const_mul] at hI
  dsimp only [z, w] at hI
  nlinarith

/-- Original weak moment transport supplies the C1 premise of the genuine
uniform energy estimate, rather than requiring regularity of the unknown. -/
theorem moment_normalizedQuadraticError_caccioppoli (hn : 0 < n)
    {u V χ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V) [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (x₀ p : Space n) (c : ℝ) {ε r R S M : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hR : 0 < R) (hrR : r < R) (hRS : R < S)
    (hχs : tsupport χ ⊆ closedBall x₀ r)
    (hdensity : ∀ x ∈ closedBall x₀ S, |Real.exp (-u x + V (gradient u x)) - 1| ≤ ε ^ 2)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ tsupport χ, |normalizedQuadraticError u x₀ p c ε x| ≤ M) :
    (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative (normalizedQuadraticError u x₀ p c ε) i x ^ 2) ≤
      32 * (M + r ^ 2) ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) +
        2 * n * r ^ 2 * (∫ x, χ x ^ 2) :=
  normalizedQuadraticError_caccioppoli hn
    (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush) hc
    (continuous_real_moment_density_closedTarget hLip hc hV hK hKc hpush)
    (fun _S hS => subgradient_volume_eq_lintegral_real_moment_density hLip hc hV.measurable
      hK.measurableSet hKc hpush hS) hχ hχc x₀ p c hε hεhalf hR hrR hRS hχs hdensity hM hbound

end KLS
end
