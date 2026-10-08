import KLS.MollifiedCompactTests

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace KLS
variable {n : ℕ}

lemma gradient_pairing_nonpos_of_distribution_subharmonic {h φ : Space n → ℝ}
    (hh : ContDiff ℝ 1 h) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hdist : 0 ≤ ∫ x, h x * coordinateLaplacian φ x) :
    (∫ x, ∑ i, coordinateDerivative φ i x * coordinateDerivative h i x) ≤ 0 := by
  have hleft (i : Fin n) : Integrable (fun x => coordinateDerivative φ i x * coordinateDerivative h i x) :=
    ((contDiff_coordinateDerivative hφ (m := 0) (by norm_num) i).continuous.mul
      (contDiff_coordinateDerivative hh (m := 0) (by norm_num) i).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative hc i).mul_right
  have hright (i : Fin n) : Integrable (fun x => coordinateHessian φ x i i * h x) :=
    ((contDiff_coordinateHessian hφ (m := 0) (by norm_num) i i).continuous.mul hh.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateHessian hc i i).mul_right
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => integral_mul_coordinateDerivative_of_hasCompactSupport_left
      (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i) hh
      (hasCompactSupport_coordinateDerivative hc i) i)
  change (∑ i, ∫ x, coordinateDerivative φ i x * coordinateDerivative h i x) =
    ∑ i, -(∫ x, coordinateHessian φ x i i * h x) at hsum
  rw [← integral_finsetSum _ (fun i _ => hleft i), Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun i _ => hright i)] at hsum
  have he : (fun x => ∑ i, coordinateHessian φ x i i * h x) =
      (fun x => h x * coordinateLaplacian φ x) := by
    funext x
    simp only [coordinateLaplacian, Finset.mul_sum, mul_comm]
  rw [he] at hsum
  linarith

/-- The distribution inequality extends to nonnegative compact C1 tests by
actual positive mollification and strong convergence of their derivatives. -/
theorem gradient_pairing_nonpos_of_distribution_subharmonic_C1
    {h φ : Space n → ℝ} (hh : ContDiff ℝ 1 h)
    {c : Space n} {r R : ℝ} (hrR : r < R)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, h x * coordinateLaplacian ψ x)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ closedBall c r) (hφ0 : ∀ x, 0 ≤ φ x) :
    (∫ x, ∑ i, coordinateDerivative φ i x * coordinateDerivative h i x) ≤ 0 := by
  have hder (i : Fin n) : Continuous (coordinateDerivative h i) :=
    (contDiff_coordinateDerivative hh (m := 0) (by norm_num) i).continuous
  have hi {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
      (∫ x, ∑ i, coordinateDerivative ψ i x * coordinateDerivative h i x) =
        ∑ i, ∫ x, coordinateDerivative h i x * coordinateDerivative ψ i x := by
    rw [integral_finsetSum (f := fun i x => coordinateDerivative ψ i x * coordinateDerivative h i x) _ (fun i _ =>
      ((contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.mul
        (hder i)).integrable_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hψc i).mul_right)]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext x
    exact mul_comm _ _
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_integral_mul_coordinateDerivative_mollify hφ hc (hder i) i)
  have he : ∀ᶠ k : ℕ in atTop,
      (∑ i, ∫ x, coordinateDerivative h i x * coordinateDerivative (mollify k φ) i x) ≤ 0 := by
    filter_upwards [eventually_tsupport_mollify_subset_ball hs hrR] with k hk
    have hψ : ContDiff ℝ 2 (mollify k φ) :=
      (mollify_contDiff hφ.continuous.locallyIntegrable k).of_le (by simp)
    rw [← hi (hψ.of_le (by norm_num)) (hasCompactSupport_mollify hc k)]
    exact gradient_pairing_nonpos_of_distribution_subharmonic hh hψ (hasCompactSupport_mollify hc k)
      (hdist _ hψ (hasCompactSupport_mollify hc k) hk (mollify_nonneg hφ0 k))
  rw [hi hφ hc]
  exact le_of_tendsto ht he

/-- A genuine local Caccioppoli estimate for nonnegative C1 distribution subharmonic functions. -/
theorem subharmonic_caccioppoli_coordinate_on_tsupport {χ h : Space n → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport χ)
    {c : Space n} {r R : ℝ} (hrR : r < R) (hs : tsupport χ ⊆ closedBall c r)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, h x * coordinateLaplacian ψ x)
    (h0 : ∀ x ∈ tsupport χ, 0 ≤ h x) :
    (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) ≤
      4 * (∫ x, ∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) := by
  let f : Space n → ℝ := fun x => χ x * χ x * h x
  have hf : ContDiff ℝ 1 f := (hχ.mul hχ).mul hh
  have hfc : HasCompactSupport f := hc.mul_right.mul_right
  have hfs : tsupport f ⊆ tsupport χ := tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hf0 : ∀ x, 0 ≤ f x := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact mul_nonneg (mul_self_nonneg _) (h0 x hx)
    · simp only [f, image_eq_zero_of_notMem_tsupport hx, zero_mul, le_refl]
  have hnonpos := gradient_pairing_nonpos_of_distribution_subharmonic_C1 hh hrR hdist
    hf hfc (hfs.trans hs) hf0
  have hdf (i : Fin n) (x : Space n) : coordinateDerivative f i x =
      2 * χ x * h x * coordinateDerivative χ i x + χ x ^ 2 * coordinateDerivative h i x := by
    dsimp only [f]
    rw [coordinateDerivative_mul ((hχ.mul hχ).differentiable (by norm_num) x)
      (hh.differentiable (by norm_num) x),
      coordinateDerivative_mul (hχ.differentiable (by norm_num) x) (hχ.differentiable (by norm_num) x)]
    ring
  have hdcχ (i : Fin n) := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
  have hdch (i : Fin n) := (contDiff_coordinateDerivative hh (m := 0) (by norm_num) i).continuous
  have hE : Integrable (fun x => ∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) :=
    integrable_finsetSum _ (fun i _ =>
      ((hχ.continuous.pow 2).mul ((hdch i).pow 2)).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right))
  have hA : Integrable (fun x => ∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) :=
    integrable_finsetSum _ (fun i _ =>
      ((hh.continuous.pow 2).mul ((hdcχ i).pow 2)).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using
          (hasCompactSupport_coordinateDerivative hc i).mul_right.mul_left))
  have hD : Integrable (fun x => ∑ i, coordinateDerivative f i x * coordinateDerivative h i x) :=
    integrable_finsetSum _ (fun i _ =>
      ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.mul (hdch i)).integrable_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hfc i).mul_right)
  have hp (x : Space n) : (∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) ≤
      4 * (∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) +
        2 * (∑ i, coordinateDerivative f i x * coordinateDerivative h i x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [hdf]
    nlinarith [sq_nonneg (χ x * coordinateDerivative h i x + 2 * h x * coordinateDerivative χ i x)]
  have hm := integral_mono hE ((hA.const_mul 4).add (hD.const_mul 2)) hp
  have hsplit := integral_add (hA.const_mul 4) (hD.const_mul 2)
  simp only [Pi.add_apply] at hm hsplit
  rw [hsplit, integral_const_mul, integral_const_mul] at hm
  linarith



lemma integral_coordinateLaplacian_eq_zero {φ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, coordinateLaplacian φ x) = 0 := by
  have hi (i : Fin n) : (∫ x, coordinateHessian φ x i i) = 0 := by
    have h := integral_mul_coordinateDerivative_of_hasCompactSupport_left
      (contDiff_coordinateDerivative hφ (m := 1) (by norm_num) i)
      (f := coordinateDerivative φ i) (g := fun _ => (1 : ℝ)) contDiff_const
      (hasCompactSupport_coordinateDerivative hc i) i
    have hconst (x : Space n) : coordinateDerivative (fun _ => (1 : ℝ)) i x = 0 := by
      simp [coordinateDerivative]
    simp only [hconst, mul_zero, integral_zero, mul_one] at h
    exact neg_eq_zero.mp h.symm
  unfold coordinateLaplacian
  rw [integral_finsetSum _ (fun i _ =>
    (contDiff_coordinateHessian hφ (m := 0) (by norm_num) i i).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_coordinateHessian hc i i))]
  simp only [hi, Finset.sum_const_zero]

lemma integral_add_const_mul_laplacian {h φ : Space n → ℝ}
    (hh : Continuous h) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (a : ℝ) :
    (∫ x, (h x + a) * coordinateLaplacian φ x) =
      ∫ x, h x * coordinateLaplacian φ x := by
  have hlc : HasCompactSupport (coordinateLaplacian φ) := hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_coordinateLaplacian_subset φ)
  have hl : Integrable (coordinateLaplacian φ) :=
    (continuous_coordinateLaplacian hφ).integrable_of_hasCompactSupport hlc
  have hp : Integrable (fun x => h x * coordinateLaplacian φ x) :=
    (hh.mul (continuous_coordinateLaplacian hφ)).integrable_of_hasCompactSupport hlc.mul_left
  simp only [add_mul]
  rw [integral_add hp (hl.const_mul a), integral_const_mul,
    integral_coordinateLaplacian_eq_zero hφ hc, mul_zero, add_zero]

/-- Local energy of a bounded C1 distribution-subharmonic function is
controlled by its size and the chosen cutoff, with no Hessian assumption. -/
theorem bounded_subharmonic_caccioppoli {χ h : Space n → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport χ)
    {c : Space n} {r R M : ℝ} (hrR : r < R) (hs : tsupport χ ⊆ closedBall c r)
    (hdist : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, h x * coordinateLaplacian ψ x)
    (hM : 0 ≤ M) (hbound : ∀ x ∈ tsupport χ, |h x| ≤ M) :
    (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) ≤
      16 * M ^ 2 * (∫ x, ∑ i, coordinateDerivative χ i x ^ 2) := by
  have hshift : ∀ ψ : Space n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball c R → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, (h x + M) * coordinateLaplacian ψ x := by
    intro ψ hψ hψc hψs hψ0
    rw [integral_add_const_mul_laplacian hh.continuous hψ hψc M]
    exact hdist ψ hψ hψc hψs hψ0
  have h0 (x : Space n) (hx : x ∈ tsupport χ) : 0 ≤ h x + M := by
    have h := (abs_le.mp (hbound x hx)).1
    linarith
  have hsq (x : Space n) (hx : x ∈ tsupport χ) : (h x + M) ^ 2 ≤ 4 * M ^ 2 := by
    have h := abs_le.mp (hbound x hx)
    nlinarith [h0 x hx]
  have hb := subharmonic_caccioppoli_coordinate_on_tsupport hχ (hh.add contDiff_const) hc
    hrR hs hshift h0
  have hder (i : Fin n) (x : Space n) :
      coordinateDerivative (fun y => h y + M) i x = coordinateDerivative h i x := by
    simp only [coordinateDerivative, fderiv_add_const]
  simp only [hder] at hb
  have hdχ (i : Fin n) := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
  have hAi (i : Fin n) : Integrable (fun x => (h x + M) ^ 2 * coordinateDerivative χ i x ^ 2) :=
    (((hh.continuous.add continuous_const).pow 2).mul ((hdχ i).pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using (hasCompactSupport_coordinateDerivative hc i).mul_right.mul_left)
  have hBi (i : Fin n) : Integrable (fun x => coordinateDerivative χ i x ^ 2) :=
    ((hdχ i).pow 2).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using (hasCompactSupport_coordinateDerivative hc i).mul_right)
  have hpoint (x : Space n) : (∑ i, (h x + M) ^ 2 * coordinateDerivative χ i x ^ 2) ≤
      4 * M ^ 2 * (∑ i, coordinateDerivative χ i x ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hx : x ∈ tsupport χ
    · exact mul_le_mul_of_nonneg_right (hsq x hx) (sq_nonneg _)
    · have hz : coordinateDerivative χ i x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hx (tsupport_coordinateDerivative_subset χ i ht))
      simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, le_refl]
  have hI := integral_mono (integrable_finsetSum _ (fun i _ => hAi i))
    ((integrable_finsetSum _ (fun i _ => hBi i)).const_mul (4 * M ^ 2)) hpoint
  rw [integral_const_mul] at hI
  nlinarith

end KLS
end
