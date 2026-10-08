import KLS.ConvexUpperTestHessian

open MeasureTheory InnerProductSpace Matrix Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace KLS
variable {n : ℕ}

/-- A positive quadratic touching from above has determinant at least the
continuous Alexandrov density at the contact point. -/
theorem det_ge_density_of_positive_quadratic_upper_touch_local
    {u f : Space n → ℝ} (hu : Continuous u) {x₀ p : Space n} {c : ℝ}
    (hf : ContinuousAt f x₀) {U : Set (Space n)} (hU : U ∈ 𝓝 x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S → S ⊆ U →
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
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp ((htouch.and hdensity).and hU)
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
    have hle := (hball hxK).1.1
    change u x < centeredQuadratic (t • A) x₀ p c x
    linarith
  have hlt := lt_of_strict_subgradient_volume_comparison
    (u := q) (v := u) (isCompact_closedBall x₀ r)
    (continuous_centeredQuadratic _ _ _ _) hu (convex_centeredQuadratic hAt.posSemidef _ _ _)
    hbound (a := ENNReal.ofReal (t • A).det) (b := ENNReal.ofReal b)
    (by exact (ENNReal.ofReal_lt_ofReal_iff hbpos).mpr hdb)
    (fun S hS hSK => by
      rw [volume_convexSubgradientImage_centeredQuadratic hAt.posSemidef, hMA S hS (fun x hx => (hball (hSK hx)).2)]
      refine ⟨le_rfl, ?_⟩
      calc
        _ = ∫⁻ _x in S, ENNReal.ofReal b ∂volume := by simp
        _ ≤ _ := setLIntegral_mono' hS.measurableSet
          (fun x hx => ENNReal.ofReal_le_ofReal (hball (hSK hx)).1.2.le))
  have hc := hlt x₀ (mem_closedBall_self hr.le)
  simp only [q, centeredQuadratic_center, hcontact, lt_self_iff_false] at hc

theorem det_ge_density_of_c2_semidefinite_upper_touch_local
    {u f ψ : Space n → ℝ} (hu : Continuous u) {x₀ : Space n}
    (hf : ContinuousAt f x₀) {U : Set (Space n)} (hU : U ∈ 𝓝 x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S → S ⊆ U →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiffAt ℝ 2 ψ x₀) (hH : (coordinateHessian ψ x₀).PosSemidef)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (coordinateHessian ψ x₀).det := by
  by_contra hnot
  let A := coordinateHessian ψ x₀
  have hgap : A.det < f x₀ := lt_of_not_ge hnot
  have hd : Continuous (fun ε : ℝ => (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have he : ∀ᶠ ε in 𝓝 (0 : ℝ), (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ)).det < f x₀ :=
    hd.continuousAt.eventually (Iio_mem_nhds (by simpa using hgap))
  obtain ⟨ε, hε, _, hdet⟩ := exists_pos_lt_of_eventually_zero zero_lt_one he
  have hAplus := posDef_add_scalar_one_of_posSemidef hH hε
  have htaylor := eventually_abs_sub_centeredQuadratic_le_sq hψ hH
    (div_pos hε (by norm_num : (0 : ℝ) < 2))
  have hquad : ∀ᶠ x in 𝓝 x₀,
      u x ≤ centeredQuadratic (A + ε • (1 : Matrix (Fin n) (Fin n) ℝ))
        x₀ (gradient ψ x₀) (ψ x₀) x := by
    filter_upwards [htouch, htaylor] with x hx ht
    have hdifference := centeredQuadratic_add_scalar_one_difference A ε x₀ (gradient ψ x₀) (ψ x₀) x
    have hupper := (abs_le.mp ht).2
    change ψ x - centeredQuadratic A x₀ (gradient ψ x₀) (ψ x₀) x ≤ _ at hupper
    linarith
  have hineq := det_ge_density_of_positive_quadratic_upper_touch_local hu hf hU hMA hAplus hcontact hquad
  exact (not_le_of_gt hdet) hineq

/-- The unrestricted upper C2-test inequality for a convex Alexandrov solution. -/
theorem det_ge_density_of_convex_c2_upper_touch_local
    {u f ψ : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u) {x₀ : Space n}
    (hf : ContinuousAt f x₀) {U : Set (Space n)} (hU : U ∈ 𝓝 x₀)
    (hMA : ∀ S : Set (Space n), IsOpen S → S ⊆ U →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume)
    (hψ : ContDiffAt ℝ 2 ψ x₀)
    (hcontact : u x₀ = ψ x₀) (htouch : ∀ᶠ x in 𝓝 x₀, u x ≤ ψ x) :
    f x₀ ≤ (coordinateHessian ψ x₀).det :=
  det_ge_density_of_c2_semidefinite_upper_touch_local hu hf hU hMA hψ
    (coordinateHessian_posSemidef_of_convex_upper_touch huc hψ hcontact htouch) hcontact htouch


end KLS
end
