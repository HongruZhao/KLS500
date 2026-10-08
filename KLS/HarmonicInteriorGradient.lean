import KLS.HarmonicBernsteinBound

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped ContDiff Topology BigOperators
noncomputable section
namespace KLS
open EllipticPdes.Sobolev EllipticPdes.Regularity
variable {n : ℕ}

lemma exists_global_smooth_eq_near_compact {f : Space n → ℝ} {U K : Set (Space n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : Space n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ g =ᶠ[𝓝ˢ K] f := by
  obtain ⟨ζ, hζ, hζ1, -⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hK hU hKU
  refine ⟨fun x => ζ x * f x, contDiff_mul_of_contDiffOn hU hζ hf, ?_⟩
  filter_upwards [hζ1] with x hx
  simp only [hx, one_mul]

lemma coordinateDerivative_eq_of_eventuallyEq {f g : Space n → ℝ} {x : Space n}
    (h : f =ᶠ[𝓝 x] g) (i : Fin n) : coordinateDerivative f i x = coordinateDerivative g i x :=
  congrArg (fun L : Space n →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) h.fderiv_eq

/-- The explicit Bernstein bound is local; global smoothness is obtained by
a proved cutoff extension and is not required of the original function. -/
theorem coordinateDerivative_sq_le_of_harmonicOn {f : Space n → ℝ} {U : Set (Space n)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hharm : ∀ x ∈ U, coordinateLaplacian f x = 0)
    {c : Space n} {R B : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ U)
    (hbound : ∀ x ∈ closedBall c R, f x ^ 2 ≤ B)
    (i : Fin n) {x : Space n} (hx : x ∈ closedBall c (R / 2)) :
    coordinateDerivative f i x ^ 2 ≤ (120 + 8 * n) * B / R ^ 2 := by
  obtain ⟨g, hg, he⟩ := exists_global_smooth_eq_near_compact hU hf (isCompact_closedBall c R) hball
  have hglap : ∀ y ∈ ball c R, coordinateLaplacian g y = 0 := by
    intro y hy
    rw [coordinateLaplacian_eq_of_eventuallyEq (he.filter_mono
      (nhds_le_nhdsSet (ball_subset_closedBall hy)))]
    exact hharm y (hball (ball_subset_closedBall hy))
  have hgbound : ∀ y ∈ closedBall c R, g y ^ 2 ≤ B := by
    intro y hy
    rw [he.self_of_nhdsSet hy]
    exact hbound y hy
  have hb := coordinateDerivative_sq_le_of_harmonic_on_ball (hg.of_le (by simp)) hR hglap hgbound i hx
  have hxR : x ∈ closedBall c R := closedBall_subset_closedBall (by linarith) hx
  rwa [coordinateDerivative_eq_of_eventuallyEq (he.filter_mono (nhds_le_nhdsSet hxR)) i] at hb

/-- A bounded continuous viscosity-harmonic function has an explicit interior
derivative bound, with all differentiability supplied by the Weyl theorem. -/
theorem IsViscosityHarmonicOn.coordinateDerivative_sq_le
    {U : Set (Space n)} {w : Space n → ℝ} (hw : IsViscosityHarmonicOn U w)
    (hU : IsOpen U) {c : Space n} {R B : ℝ} (hR : 0 < R)
    (hball : closedBall c R ⊆ U) (hbound : ∀ x ∈ closedBall c R, w x ^ 2 ≤ B)
    (i : Fin n) {x : Space n} (hx : x ∈ closedBall c (R / 2)) :
    coordinateDerivative w i x ^ 2 ≤ (120 + 8 * n) * B / R ^ 2 :=
  coordinateDerivative_sq_le_of_harmonicOn hU (hw.contDiffOn hU)
    (fun _ hy => hw.coordinateLaplacian_eq_zero hU hy) hR hball hbound i hx

end KLS
end
