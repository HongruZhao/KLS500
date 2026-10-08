import KLS.ViscosityLaplacianCalculus

/-! Local uniform limits of actual approximate Laplacian test inequalities.
The proof transfers a strict touching test through a compact maximum; it does
not assume differentiability of the limiting or approximating functions. -/
open MeasureTheory InnerProductSpace Set Filter Matrix Metric
open scoped Topology ContDiff RealInnerProductSpace NNReal Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {n : ℕ}

/-- The upper-test half of harmonic viscosity at a local uniform limit. -/
theorem upper_laplacian_nonneg_of_local_uniform_limit
    {U : Set (Space n)} (hU : IsOpen U)
    {v : ℕ → Space n → ℝ} (hv : ∀ m, Continuous (v m))
    {ε : ℕ → ℝ} (hεlim : Tendsto ε atTop (𝓝 0))
    {w : Space n → ℝ}
    (hlim : ∀ K : Set (Space n), IsCompact K → K ⊆ U → TendstoUniformlyOn v w atTop K)
    (htest : ∀ m (ψ : Space n → ℝ), ContDiff ℝ 2 ψ → ∀ (B : ℝ), 0 < B →
      |ε m * B| ≤ 1 / 2 → ∀ x ∈ U, ‖matrixAction (coordinateHessian ψ x)‖ ≤ B →
      v m x = ψ x → (∀ᶠ y in 𝓝 x, v m y ≤ ψ y) →
      -(1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε m ≤ coordinateLaplacian ψ x)
    {x : Space n} (hx : x ∈ U) {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hcontact : w x = ψ x) (htouch : ∀ᶠ y in 𝓝 x, w y ≤ ψ y) :
    0 ≤ coordinateLaplacian ψ x := by
  by_contra hn
  have hlap : coordinateLaplacian ψ x < 0 := lt_of_not_ge hn
  let a : ℝ := -coordinateLaplacian ψ x / (2 * ((n : ℝ) + 1))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have ha : 0 < a := by
    exact div_pos (neg_pos.mpr hlap) (by positivity)
  have haeq : a * (2 * ((n : ℝ) + 1)) = -coordinateLaplacian ψ x := by
    dsimp [a]
    exact div_mul_cancel₀ _ (by positivity)
  let q := centeredQuadratic (1 : Matrix (Fin n) (Fin n) ℝ) x 0 0
  let Φ : Space n → ℝ := fun y => ψ y + a * q y
  have hΦ : ContDiff ℝ 2 Φ :=
    hψ.add (contDiff_const.mul ((contDiff_centeredQuadratic _ _ _ _).of_le (by simp)))
  have hlapΦ : coordinateLaplacian Φ x = coordinateLaplacian ψ x + a * n := by
    simpa only [add_zero] using coordinateLaplacian_add_scalar_quadratic_const hψ x a 0 x
  have hlapΦneg : coordinateLaplacian Φ x < 0 := by rw [hlapΦ]; nlinarith
  let b : ℝ := -coordinateLaplacian Φ x / 2
  have hb : 0 < b := by dsimp [b]; linarith
  let B : ℝ := ‖matrixAction (coordinateHessian Φ x)‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hgood : {y : Space n | y ∈ U ∧ w y ≤ ψ y ∧
      coordinateLaplacian Φ y < -b ∧ ‖matrixAction (coordinateHessian Φ y)‖ < B} ∈ 𝓝 x := by
    have hLe := (continuous_coordinateLaplacian hΦ).continuousAt.eventually_lt_const
      (by dsimp [b]; linarith : coordinateLaplacian Φ x < -b)
    have hHe := (continuous_coordinateHessian_operator_norm hΦ).continuousAt.eventually_lt_const
      (by dsimp [B]; linarith : ‖matrixAction (coordinateHessian Φ x)‖ < B)
    filter_upwards [hU.mem_nhds hx, htouch, hLe, hHe] with y hy ht hl hh
    exact ⟨hy, ht, hl, hh⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hgood
  have hballU : closedBall x r ⊆ U := fun y hy => (hball hy).1
  let δ : ℝ := a * r ^ 2 / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgap : ∀ y ∈ frontier (closedBall x r),
      w y - Φ y ≤ w x - Φ x - δ := by
    intro y hy
    have hdist : ‖y - x‖ = r := frontier_closedBall_subset_sphere hy
    have hyball : y ∈ closedBall x r := by simpa only [mem_closedBall, dist_eq_norm] using hdist.le
    have hwy := (hball hyball).2.1
    have hqy : q y = r ^ 2 / 2 := by
      dsimp only [q]
      rw [centeredQuadratic_one_eq_half_norm_sq x y, hdist]
    have hqx : q x = 0 := by simp [q]
    dsimp [Φ, δ]
    rw [hqy, hqx, hcontact]
    nlinarith
  have hclose := Metric.tendstoUniformlyOn_iff.mp
    (hlim (closedBall x r) (isCompact_closedBall _ _) hballU) (δ / 3) (by positivity)
  have hsmall : ∀ᶠ m in atTop, |ε m * B| ≤ 1 / 2 := by
    have hh : Tendsto (fun m => |ε m * B|) atTop (𝓝 0) := by
      simpa only [zero_mul, abs_zero] using (hεlim.mul_const B).abs
    exact (hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ hm => hm.le
  have herr : ∀ᶠ m in atTop,
      (1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε m < b := by
    have hh : Tendsto (fun m => (1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε m)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using (hεlim.const_mul (1 + (nonlinearComparisonConstant n - 2) * B ^ 2))
    exact hh.eventually (gt_mem_nhds hb)
  obtain ⟨m, hmclose, hmsmall, hmerr⟩ := (hclose.and (hsmall.and herr)).exists
  obtain ⟨z, hz, d, hc, ht⟩ := exists_interior_upper_contact_of_uniform_bound
    (hv m) hΦ.continuous (isCompact_closedBall x r) (mem_closedBall_self hr.le) hδ hgap
    (fun y hy => by simpa only [Real.dist_eq, abs_sub_comm] using (hmclose y hy).le)
  have hzball : z ∈ closedBall x r := interior_subset hz
  have hzt := hball hzball
  have hbound : ‖matrixAction (coordinateHessian (fun y => Φ y + d) z)‖ ≤ B := by
    rw [coordinateHessian_add_const]
    exact hzt.2.2.2.le
  have hineq := htest m (fun y => Φ y + d) (hΦ.add contDiff_const) B hB hmsmall
    z hzt.1 hbound hc ht
  rw [coordinateLaplacian_add_const] at hineq
  have hl := hzt.2.2.1
  linarith

/-- The lower-test half, proved by applying the genuine upper contact
transfer to negated functions and tests. -/
theorem lower_laplacian_nonpos_of_local_uniform_limit
    {U : Set (Space n)} (hU : IsOpen U)
    {v : ℕ → Space n → ℝ} (hv : ∀ m, Continuous (v m))
    {ε : ℕ → ℝ} (hεlim : Tendsto ε atTop (𝓝 0))
    {w : Space n → ℝ}
    (hlim : ∀ K : Set (Space n), IsCompact K → K ⊆ U → TendstoUniformlyOn v w atTop K)
    (htest : ∀ m (ψ : Space n → ℝ), ContDiff ℝ 2 ψ → ∀ (B : ℝ), 0 < B →
      |ε m * B| ≤ 1 / 2 → ∀ x ∈ U, ‖matrixAction (coordinateHessian ψ x)‖ ≤ B →
      v m x = ψ x → (∀ᶠ y in 𝓝 x, ψ y ≤ v m y) →
      coordinateLaplacian ψ x ≤ (1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε m)
    {x : Space n} (hx : x ∈ U) {ψ : Space n → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hcontact : w x = ψ x) (htouch : ∀ᶠ y in 𝓝 x, ψ y ≤ w y) :
    coordinateLaplacian ψ x ≤ 0 := by
  have hnegLim : ∀ K : Set (Space n), IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun m => -(v m)) (-w) atTop K := by
    intro K hK hKU
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    exact (Metric.tendstoUniformlyOn_iff.mp (hlim K hK hKU) δ hδ).mono fun m hm y hy => by
      simpa only [Pi.neg_apply, dist_neg_neg] using hm y hy
  have hnegTest : ∀ m (φ : Space n → ℝ), ContDiff ℝ 2 φ → ∀ B : ℝ, 0 < B →
      |ε m * B| ≤ 1 / 2 → ∀ y ∈ U, ‖matrixAction (coordinateHessian φ y)‖ ≤ B →
      (-v m) y = φ y → (∀ᶠ z in 𝓝 y, (-v m) z ≤ φ z) →
      -(1 + (nonlinearComparisonConstant n - 2) * B ^ 2) * ε m ≤ coordinateLaplacian φ y := by
    intro m φ hφ B hB hsmall y hy hH hc ht
    have hHneg : ‖matrixAction (coordinateHessian (-φ) y)‖ ≤ B := by
      rwa [coordinateHessian_neg_operator_norm hφ]
    have hcneg : v m y = (-φ) y := by change -v m y = φ y at hc; simp only [Pi.neg_apply]; linarith
    have htneg : ∀ᶠ z in 𝓝 y, (-φ) z ≤ v m z := by
      filter_upwards [ht] with z hz
      change -v m z ≤ φ z at hz
      change -φ z ≤ v m z
      linarith
    have hi := htest m (-φ) hφ.neg B hB hsmall y hy hHneg hcneg htneg
    rw [coordinateLaplacian_neg hφ] at hi
    linarith
  have hct : (-w) x = (-ψ) x := by simp only [Pi.neg_apply, hcontact]
  have htt : ∀ᶠ y in 𝓝 x, (-w) y ≤ (-ψ) y := by
    filter_upwards [htouch] with y hy
    exact neg_le_neg hy
  have hi := upper_laplacian_nonneg_of_local_uniform_limit hU (fun m => (hv m).neg)
    hεlim hnegLim hnegTest hx hψ.neg hct htt
  change 0 ≤ coordinateLaplacian (-ψ) x at hi
  rw [coordinateLaplacian_neg hψ] at hi
  linarith

/-- Continuous viscosity harmonicity stated through actual global C2 tests.
This definition does not assert a classical Hessian or a weak PDE identity. -/
def IsViscosityHarmonicOn (U : Set (Space n)) (w : Space n → ℝ) : Prop :=
  ContinuousOn w U ∧ ∀ x ∈ U, ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → w x = ψ x →
    ((∀ᶠ y in 𝓝 x, w y ≤ ψ y) → 0 ≤ coordinateLaplacian ψ x) ∧
    ((∀ᶠ y in 𝓝 x, ψ y ≤ w y) → coordinateLaplacian ψ x ≤ 0)

end KLS
end
