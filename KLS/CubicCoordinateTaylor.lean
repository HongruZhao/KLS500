import KLS.CoordinateMeanValue

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

/-- Three ordinary mean-value estimates give a cubic remainder from bounds
on literal third coordinate derivatives. -/
theorem abs_le_cube_of_zero_second_coordinate_jet {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {c x : Space n} {r M : ℝ}
    (hM : 0 ≤ M) (hx : x ∈ closedBall c r) (hzero : f c = 0)
    (hfirst : ∀ i, coordinateDerivative f i c = 0)
    (hsecond : ∀ i j, coordinateHessian f c i j = 0)
    (hthird : ∀ y ∈ closedBall c r, ∀ i j k,
      |harmonicCoordinateWord [i,j,k] f y| ≤ M) :
    |f x| ≤ (n : ℝ) ^ 3 * M * ‖x - c‖ ^ 3 := by
  let d := ‖x - c‖
  have hd : 0 ≤ d := norm_nonneg _
  have hdr : d ≤ r := hx
  have hsub : closedBall c d ⊆ closedBall c r := closedBall_subset_closedBall hdr
  have hc : c ∈ closedBall c d := mem_closedBall_self hd
  have hx' : x ∈ closedBall c d := by simp [d, mem_closedBall, dist_eq_norm]
  have hHb : ∀ y ∈ closedBall c d, ∀ i j, |coordinateHessian f y i j| ≤ n * M * d := by
    intro y hy i j
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z => coordinateHessian f z i j) :=
      contDiff_harmonicCoordinateWord hf [i,j]
    have hm := abs_sub_le_of_coordinateDerivative_le (convex_closedBall c d)
      (fun z _ => hs.differentiable (by simp) z) hM
      (fun z hz k => hthird z (hsub hz) k i j) hc hy
    change |coordinateHessian f y i j - coordinateHessian f c i j| ≤ _ at hm
    rw [hsecond, sub_zero] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (show ‖y-c‖ ≤ d from hy) (by positivity))
  have hDb : ∀ y ∈ closedBall c d, ∀ i,
      |coordinateDerivative f i y| ≤ (n : ℝ) ^ 2 * M * d ^ 2 := by
    intro y hy i
    have hs := contDiff_harmonicCoordinateWord hf [i]
    have hm := abs_sub_le_of_coordinateDerivative_le (convex_closedBall c d)
      (fun z _ => hs.differentiable (by simp) z) (by positivity : 0 ≤ (n : ℝ) * M * d)
      (fun z hz j => hHb z hz j i) hc hy
    change |coordinateDerivative f i y - coordinateDerivative f i c| ≤ _ at hm
    rw [hfirst, sub_zero] at hm
    calc
      |coordinateDerivative f i y| ≤ n * (n * M * d) * ‖y-c‖ := hm
      _ ≤ n * (n * M * d) * d :=
        mul_le_mul_of_nonneg_left (show ‖y-c‖ ≤ d from hy) (by positivity)
      _ = (n : ℝ) ^ 2 * M * d ^ 2 := by ring
  have hm := abs_sub_le_of_coordinateDerivative_le (convex_closedBall c d)
    (fun z _ => hf.differentiable (by simp) z)
    (by positivity : 0 ≤ (n : ℝ) ^ 2 * M * d ^ 2) hDb hc hx'
  rw [hzero, sub_zero] at hm
  convert hm using 1
  dsimp [d]
  ring


/-- The polynomial is the genuine second-order Taylor polynomial. -/
theorem abs_sub_quadratic_taylor_le_cube {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {c x : Space n} {r M : ℝ}
    (hM : 0 ≤ M) (hx : x ∈ closedBall c r)
    (hthird : ∀ y ∈ closedBall c r, ∀ i j k,
      |harmonicCoordinateWord [i,j,k] f y| ≤ M) :
    |f x - centeredQuadratic (coordinateHessian f c) c (gradient f c) (f c) x| ≤
      (n : ℝ) ^ 3 * M * ‖x - c‖ ^ 3 := by
  let A := coordinateHessian f c
  have hA : A.IsSymm := coordinateHessian_symmetric (hf.of_le (by simp)) c
  let q := centeredQuadratic A c (gradient f c) (f c)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q :=
    (contDiff_centeredQuadratic _ _ _ _).of_le (by simp)
  have hqH (y : Space n) : coordinateHessian q y = A :=
    coordinateHessian_centeredQuadratic_of_isSymm hA _ _ _ _
  apply abs_le_cube_of_zero_second_coordinate_jet (hf.sub hq) hM hx
  · simp [q]
  · intro i
    rw [coordinateDerivative_sub (hf.differentiable (by simp) c)
      (hq.differentiable (by simp) c)]
    simp only [coordinateDerivative_eq_gradient, q, gradient_centeredQuadratic_of_isSymm hA,
      sub_self, map_zero, add_zero]
  · intro i j
    rw [coordinateHessian_sub (hf.of_le (by simp)) (hq.of_le (by simp)), hqH]
    exact sub_self _
  · intro y hy i j k
    have he : (fun z => coordinateHessian (fun z => f z - q z) z j k) =
        (fun z => coordinateHessian f z j k - A j k) := by
      funext z
      rw [coordinateHessian_sub (hf.of_le (by simp)) (hq.of_le (by simp)), hqH]
    change |coordinateDerivative (fun z => coordinateHessian (fun z => f z - q z) z j k) i y| ≤ M
    rw [he, coordinateDerivative, fderiv_sub_const]
    exact hthird y hy i j k


/-- The quantitative estimate applies to a function smooth only on its open
domain. The extension agrees with the original function and its actual jets. -/
theorem abs_sub_quadratic_taylor_le_cube_of_contDiffOn {f : Space n → ℝ}
    {U : Set (Space n)} (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    {c x : Space n} {r M : ℝ} (hr : 0 ≤ r) (hball : closedBall c r ⊆ U)
    (hM : 0 ≤ M) (hx : x ∈ closedBall c r)
    (hthird : ∀ y ∈ closedBall c r, ∀ i j k,
      |harmonicCoordinateWord [i,j,k] f y| ≤ M) :
    |f x - centeredQuadratic (coordinateHessian f c) c (gradient f c) (f c) x| ≤
      (n : ℝ) ^ 3 * M * ‖x - c‖ ^ 3 := by
  obtain ⟨g, hg, he⟩ := exists_global_smooth_eq_near_compact hU hf
    (isCompact_closedBall c r) hball
  have hec : g =ᶠ[𝓝 c] f := he.filter_mono (nhds_le_nhdsSet (mem_closedBall_self hr))
  have heH : coordinateHessian g c = coordinateHessian f c := by
    ext i j
    exact (harmonicCoordinateWord_eventuallyEq hec [i,j]).self_of_nhds
  have h := abs_sub_quadratic_taylor_le_cube hg hM hx (fun y hy i j k => by
    rw [(harmonicCoordinateWord_eventuallyEq
      (he.filter_mono (nhds_le_nhdsSet hy)) [i,j,k]).self_of_nhds]
    exact hthird y hy i j k)
  rwa [he.self_of_nhdsSet hx, heH, hec.gradient_eq, hec.self_of_nhds] at h

end KLS
end
