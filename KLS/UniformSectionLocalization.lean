import KLS.MomentGradientHomeomorph

/-! Uniform small support sections at nearby centers, from actual strict
convexity, interior conjugate slopes and continuity of the chosen slope. -/
open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal
noncomputable section
namespace KLS
variable {n : ℕ}

theorem exists_uniform_small_support_sections
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {p : Space n → Space n} {x₀ : Space n} (hpc : ContinuousAt p x₀)
    (hp₀ : p x₀ ∈ convexSubgradient u x₀)
    (hpD : p x₀ ∈ interior (momentLegendreDomain u))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r t : ℝ, 0 < r ∧ 0 < t ∧
      ∀ x ∈ closedBall x₀ r, ∀ h : ℝ, h ≤ t →
        {z | u z ≤ u x + inner ℝ (p x) (z - x) + h} ⊆ ball x₀ ε := by
  let g : Space n → ℝ := fun z => u z - u x₀ - inner ℝ (p x₀) (z - x₀)
  have hg : Continuous g := (hu.sub continuous_const).sub
    (continuous_const.inner (continuous_id.sub continuous_const))
  have hgzero : g x₀ = 0 := by simp [g]
  have hgnon (z : Space n) : 0 ≤ g z := by
    have h := hp₀ z
    dsimp [g]
    linarith
  obtain ⟨a, M, ha, hbound⟩ := exists_linear_lower_bound_tiltedPotential u hpD
  let A : ℝ := max 0 (M + u x₀ - inner ℝ (p x₀) x₀)
  have hA : 0 ≤ A := le_max_left _ _
  have hlower (z : Space n) : a * ‖z‖ - A ≤ g z := by
    have hh := hbound z
    have hAM : M + u x₀ - inner ℝ (p x₀) x₀ ≤ A := le_max_right _ _
    dsimp [g, tiltedPotential] at *
    rw [inner_sub_right]
    linarith
  have hzeros : {z | g z = 0} ⊆ ball x₀ ε := by
    intro z hz
    by_cases hzx : z = x₀
    · simpa [hzx] using hε
    · have hstrict := strict_support_inequality_of_strictConvexOn hc hp₀ (Ne.symm hzx)
      dsimp [g] at hz
      linarith
  obtain ⟨R, hR, _, hRU⟩ := exists_pos_compact_sublevel_subset hg hgnon ha hlower
    isOpen_ball hzeros
  let B : ℝ := ‖x₀‖ + 1
  let c : ℝ := A / a + B
  have hB : 0 < B := by dsimp [B]; positivity
  have hcpos : 0 < c := by dsimp [c]; exact add_pos_of_nonneg_of_pos (div_nonneg hA ha.le) hB
  let δ : ℝ := min (a / 2) (R / (8 * c))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδa : δ / a ≤ 1 / 2 := by
    apply (div_le_iff₀ ha).mpr
    have hh : δ ≤ a / 2 := min_le_left _ _
    linarith
  have hδc : δ * c ≤ R / 8 := by
    have hh : δ ≤ R / (8 * c) := min_le_right _ _
    have hh' := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 8) hcpos)).mp hh
    nlinarith
  have heg : ∀ᶠ x in 𝓝 x₀, g x < R / 8 :=
    hg.continuousAt.eventually_lt continuousAt_const (by rw [hgzero]; positivity)
  have heB : ∀ᶠ x in 𝓝 x₀, ‖x‖ < B :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by dsimp [B]; linarith)
  have heδ : ∀ᶠ x in 𝓝 x₀, ‖p x - p x₀‖ < δ :=
    (hpc.sub continuousAt_const).norm.eventually_lt continuousAt_const
      (by change ‖p x₀ - p x₀‖ < δ; simpa using hδ)
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp (heg.and (heB.and heδ))
  refine ⟨r / 2, R / 8, by positivity, by positivity, ?_⟩
  intro x hx h hh z hz
  have hxr : dist x x₀ < r := lt_of_le_of_lt hx (by linarith)
  obtain ⟨hgx, hnx, hpx⟩ := hnear hxr
  have herr : g z ≤ g x + ‖p x - p x₀‖ * ‖z - x‖ + h := by
    have hip := real_inner_le_norm (p x - p x₀) (z - x)
    change u z ≤ u x + inner ℝ (p x) (z - x) + h at hz
    dsimp [g]
    simp only [inner_sub_left, inner_sub_right] at hip hz ⊢
    linarith
  have hdz : ‖z - x‖ ≤ ‖z‖ + B := (norm_sub_le z x).trans (by linarith)
  have herr' : g z ≤ g x + δ * (‖z‖ + B) + h := by
    have hm := mul_le_mul hpx.le hdz (norm_nonneg _) hδ.le
    linarith
  have hnorm : ‖z‖ ≤ (g z + A) / a := (le_div_iff₀ ha).mpr (by linarith [hlower z])
  have habsorb : δ * ‖z‖ ≤ g z / 2 + δ * (A / a) := by
    calc
      _ ≤ δ * ((g z + A) / a) := mul_le_mul_of_nonneg_left hnorm hδ.le
      _ = (δ / a) * g z + δ * (A / a) := by ring
      _ ≤ (1 / 2) * g z + δ * (A / a) :=
        by linarith [mul_le_mul_of_nonneg_right hδa (hgnon z)]
      _ = _ := by ring
  have hdc : δ * (A / a) + δ * B = δ * c := by dsimp [c]; ring
  have hsmall : g z ≤ R := by
    nlinarith
  exact hRU hsmall

/-- The uniform localization conditions are discharged by the actual weak
moment equation, rather than assumed as a regularity modulus. -/
theorem exists_uniform_small_moment_sections
    {u V : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L u)
    (hc : ConvexOn ℝ univ u) (hV : Continuous V)
    [IsFiniteMeasure (potentialMeasure u)]
    {K : Set (Space n)} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hpush : MomentMap.gradientPushforward u = (potentialMeasure V).restrict K)
    (x₀ : Space n) {ε : ℝ} (hε : 0 < ε) :
    ∃ r t : ℝ, 0 < r ∧ 0 < t ∧
      ∀ x ∈ closedBall x₀ r, ∀ h : ℝ, h ≤ t →
        {z | u z ≤ u x + inner ℝ (gradient u x) (z - x) + h} ⊆ ball x₀ ε := by
  have hd := (moment_contDiff_one_closedTarget hLip hc hV hK hKc hpush).differentiable (by norm_num)
  apply exists_uniform_small_support_sections hLip.continuous
    (moment_strictConvexOn hLip hc hV hK.measurableSet hKc hpush)
    (continuous_gradient_of_subsingleton_convexSubgradient hLip hc
      (moment_convexSubgradient_subsingleton_closedTarget hLip hc hV hK hKc hpush)).continuousAt
    (gradient_mem_convexSubgradient hc (hd x₀))
    (moment_gradient_mem_interior_domain hLip hc hV hK hKc hpush x₀) hε

end KLS
end
#print axioms KLS.exists_uniform_small_support_sections
#print axioms KLS.exists_uniform_small_moment_sections
