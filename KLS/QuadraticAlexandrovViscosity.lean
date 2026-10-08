import KLS.StrictAlexandrovTouch
import KLS.QuadraticSubgradientVolume

/-! Alexandrov-to-viscosity inequalities for positive quadratic tests.
Only the weak subgradient-image volume identity and continuity of its density
are used; the solution is not assumed differentiable. -/

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

lemma matrixAction_smul_scalar (t : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Space n) :
    matrixAction (t • A) x = t • matrixAction A x := by
  ext i
  simp only [matrixAction_apply, Matrix.smul_apply, smul_eq_mul, PiLp.smul_apply]
  simp only [← Finset.mul_sum, mul_assoc]

lemma centeredQuadratic_smul_difference (t : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (x₀ p : Space n) (c : ℝ) (x : Space n) :
    centeredQuadratic (t • A) x₀ p c x - centeredQuadratic A x₀ p c x =
      ((t - 1) / 2) * inner ℝ (x - x₀) (matrixAction A (x - x₀)) := by
  simp only [centeredQuadratic, matrixAction_smul_scalar, inner_smul_right]
  ring

lemma exists_scaling_above_det_lt {A : Matrix (Fin n) (Fin n) ℝ} {b : ℝ}
    (h : A.det < b) : ∃ t : ℝ, 1 < t ∧ (t • A).det < b := by
  have hd : Continuous (fun t : ℝ => (t • A).det) :=
    (continuous_id.smul continuous_const).matrix_det
  have he : ∀ᶠ t in 𝓝 (1 : ℝ), (t • A).det < b :=
    hd.continuousAt.eventually (Iio_mem_nhds (by simpa using h))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1 + ε / 2, by linarith, hball ?_⟩
  simp only [mem_ball, Real.dist_eq]
  rw [show 1 + ε / 2 - 1 = ε / 2 by ring, abs_of_pos (by positivity)]
  linarith

lemma exists_scaling_below_det_gt {A : Matrix (Fin n) (Fin n) ℝ} {b : ℝ}
    (h : b < A.det) : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ b < (t • A).det := by
  have hd : Continuous (fun t : ℝ => (t • A).det) :=
    (continuous_id.smul continuous_const).matrix_det
  have he : ∀ᶠ t in 𝓝 (1 : ℝ), b < (t • A).det :=
    hd.continuousAt.eventually (Ioi_mem_nhds (by simpa using h))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  let δ := min ε 1 / 2
  have hδ : 0 < δ := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hδε : δ < ε := by dsimp [δ]; have := min_le_left ε 1; linarith
  have hδ1 : δ < 1 := by dsimp [δ]; have := min_le_right ε 1; linarith
  refine ⟨1 - δ, by linarith, by linarith, hball ?_⟩
  simp only [mem_ball, Real.dist_eq]
  rw [show 1 - δ - 1 = -δ by ring, abs_neg, abs_of_pos hδ]
  exact hδε

/-- A positive quadratic touching from above has determinant at least the
continuous Alexandrov density at the contact point. -/
theorem det_ge_density_of_positive_quadratic_upper_touch
    {u f : Space n → ℝ} (hu : Continuous u) {x₀ p : Space n} {c : ℝ}
    (hf : ContinuousAt f x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hcontact : u x₀ = c)
    (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ centeredQuadratic A x₀ p c x) :
    f x₀ ≤ A.det := by
  by_contra hnot
  obtain ⟨t, ht, htdet⟩ := exists_scaling_above_det_lt (lt_of_not_ge hnot)
  have htpos : 0 < t := by linarith
  have hAt : (t • A).PosDef := hA.smul htpos
  let b := ((t • A).det + f x₀) / 2
  have hdb : (t • A).det < b := by dsimp [b]; linarith
  have hbf : b < f x₀ := by dsimp [b]; linarith
  have hbpos : 0 < b := hAt.det_pos.trans hdb
  have hdensity : ∀ᶠ x in 𝓝 x₀, b < f x := hf.eventually (Ioi_mem_nhds hbf)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (htouch.and hdensity)
  let q := centeredQuadratic (t • A) x₀ p c
  have hbound : ∀ x ∈ frontier (closedBall x₀ r), u x < q x := by
    intro x hx
    have hxs := frontier_closedBall_subset_sphere hx
    have hxK : x ∈ closedBall x₀ r := sphere_subset_closedBall hxs
    have hne : x ≠ x₀ := by
      intro heq
      subst x
      have hh : (0 : ℝ) = r := by simpa only [mem_sphere, dist_self] using hxs
      linarith
    have hpos := inner_matrixAction_pos hA (sub_ne_zero.mpr hne)
    have hdiff := centeredQuadratic_smul_difference t A x₀ p c x
    have hmul : 0 < ((t - 1) / 2) * inner ℝ (x - x₀) (matrixAction A (x - x₀)) :=
      mul_pos (by linarith) hpos
    have hle := (hball hxK).1
    change u x < centeredQuadratic (t • A) x₀ p c x
    linarith
  have hlt := lt_of_strict_subgradient_volume_comparison
    (u := q) (v := u) (isCompact_closedBall x₀ r)
    (continuous_centeredQuadratic _ _ _ _) hu (convex_centeredQuadratic hAt.posSemidef _ _ _)
    hbound (a := ENNReal.ofReal (t • A).det) (b := ENNReal.ofReal b)
    (by exact (ENNReal.ofReal_lt_ofReal_iff hbpos).mpr hdb)
    (fun S hS hSK => by
      rw [volume_convexSubgradientImage_centeredQuadratic hAt.posSemidef, hMA S hS]
      refine ⟨le_rfl, ?_⟩
      calc
        _ = ∫⁻ _x in S, ENNReal.ofReal b ∂volume := by simp
        _ ≤ _ := setLIntegral_mono' hS.measurableSet
          (fun x hx => ENNReal.ofReal_le_ofReal (hball (hSK hx)).2.le))
  have hc := hlt x₀ (mem_closedBall_self hr.le)
  simp only [q, centeredQuadratic_center, hcontact, lt_self_iff_false] at hc

/-- A positive quadratic touching from below has determinant at most the
continuous nonnegative Alexandrov density at the contact point. -/
theorem det_le_density_of_positive_quadratic_lower_touch
    {u f : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    {x₀ p : Space n} {c : ℝ} (hf : ContinuousAt f x₀) (hfpos : 0 ≤ f x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (hcontact : u x₀ = c)
    (htouch : ∀ᶠ x in 𝓝 x₀, centeredQuadratic A x₀ p c x ≤ u x) :
    A.det ≤ f x₀ := by
  by_contra hnot
  obtain ⟨t, htpos, ht, htdet⟩ := exists_scaling_below_det_gt (lt_of_not_ge hnot)
  have hAt : (t • A).PosDef := hA.smul htpos
  let b := ((t • A).det + f x₀) / 2
  have hbd : b < (t • A).det := by dsimp [b]; linarith
  have hfb : f x₀ < b := by dsimp [b]; linarith
  have hbpos : 0 < b := hfpos.trans_lt hfb
  have hdensity : ∀ᶠ x in 𝓝 x₀, f x < b := hf.eventually (Iio_mem_nhds hfb)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (htouch.and hdensity)
  let q := centeredQuadratic (t • A) x₀ p c
  have hbound : ∀ x ∈ frontier (closedBall x₀ r), q x < u x := by
    intro x hx
    have hxs := frontier_closedBall_subset_sphere hx
    have hxK : x ∈ closedBall x₀ r := sphere_subset_closedBall hxs
    have hne : x ≠ x₀ := by
      intro heq
      subst x
      have hh : (0 : ℝ) = r := by simpa only [mem_sphere, dist_self] using hxs
      linarith
    have hpos := inner_matrixAction_pos hA (sub_ne_zero.mpr hne)
    have hdiff := centeredQuadratic_smul_difference t A x₀ p c x
    have hmul : ((t - 1) / 2) * inner ℝ (x - x₀) (matrixAction A (x - x₀)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hpos
    have hle := (hball hxK).1
    change centeredQuadratic (t • A) x₀ p c x < u x
    linarith
  have hlt := lt_of_strict_subgradient_volume_comparison
    (u := u) (v := q) (isCompact_closedBall x₀ r) hu
    (continuous_centeredQuadratic _ _ _ _) huc hbound
    (a := ENNReal.ofReal b) (b := ENNReal.ofReal (t • A).det)
    (by exact (ENNReal.ofReal_lt_ofReal_iff hAt.det_pos).mpr hbd)
    (fun S hS hSK => by
      rw [volume_convexSubgradientImage_centeredQuadratic hAt.posSemidef, hMA S hS]
      refine ⟨?_, le_rfl⟩
      calc
        _ ≤ ∫⁻ _x in S, ENNReal.ofReal b ∂volume := setLIntegral_mono' hS.measurableSet
          (fun x hx => ENNReal.ofReal_le_ofReal (hball (hSK hx)).2.le)
        _ = _ := by simp)
  have hc := hlt x₀ (mem_closedBall_self hr.le)
  simp only [q, centeredQuadratic_center, hcontact, lt_self_iff_false] at hc

end KLS
end

#print axioms KLS.det_ge_density_of_positive_quadratic_upper_touch
#print axioms KLS.det_le_density_of_positive_quadratic_lower_touch
