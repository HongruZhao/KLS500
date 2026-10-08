import KLS.TiltCumulantHierarchy
import KLS.LogTiltCumulants

/-!
# Low-order identification of the actual cumulant tensors

The all-order Fréchet definition is connected to actual means, covariances,
and third centered moments by uniqueness of the proved directional derivatives.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff

noncomputable section
namespace KLS

@[simp] theorem exponentialTilt_zero {n : ℕ} (μ : Measure (Space n))
    [IsProbabilityMeasure μ] : exponentialTilt μ 0 = μ := by
  simp only [exponentialTilt, inner_zero_left, tilted_const]

theorem isCompact_support_exponentialTilt {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (z : Space n) :
    IsCompact (exponentialTilt μ z).support := by
  change IsCompact (μ.tilted (fun x => inner ℝ z x)).support
  rwa [tilted_support_eq hμ (by fun_prop)]

theorem cumulantTensor_one_apply {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (h : Fin 1 → Space n) :
    cumulantTensor μ 1 h = ∫ x, inner ℝ (h 0) x ∂μ := by
  rw [cumulantTensor, iteratedFDeriv_one_apply]
  have hd := hasDerivAt_log_tiltPartition hμ (q := fun _ => 0)
    (s := fun x => inner ℝ (h 0) x) continuous_const (by fun_prop) 0
  have he : (fun t : ℝ => tiltLogLaplace μ (t • h 0)) =
      (fun t => Real.log (tiltPartition μ (fun x => 0 + t * inner ℝ (h 0) x))) := by
    funext t
    simp only [tiltLogLaplace, inner_smul_left, RCLike.conj_to_real, zero_add]
  have hh := ((contDiff_tiltLogLaplace hμ).differentiable (by simp)
    (0 + (0 : ℝ) • h 0)).deriv_comp_add_smul
  simp only [zero_smul, add_zero, zero_add] at hh
  rw [← hh, he, hd.deriv]
  simp only [tiltAverage, zero_mul, add_zero, tilted_const]

theorem cumulantTensor_two_apply {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (h : Fin 2 → Space n) :
    cumulantTensor μ 2 h = covariance (fun x => inner ℝ (h 0) x)
      (fun x => inner ℝ (h 1) x) μ := by
  have ht := hasDerivAt_cumulantTensor_exponentialTilt_eval hμ (m := 1) (by omega)
    0 (h 0) (Fin.tail h) 0
  simp only [zero_add, zero_smul, exponentialTilt_zero, Fin.cons_self_tail] at ht
  have he (u : ℝ) : cumulantTensor (exponentialTilt μ (u • h 0)) 1 (Fin.tail h) =
      ∫ x, inner ℝ (h 1) x ∂exponentialTilt μ (u • h 0) := by
    have := exponentialTilt_isProbability hμ (u • h 0)
    exact cumulantTensor_one_apply (isCompact_support_exponentialTilt hμ (u • h 0)) (Fin.tail h)
  simp_rw [he] at ht
  have hd := hasDerivAt_exponentialTilt_average hμ
    (f := fun x => inner ℝ (h 1) x)
    (integrable_of_continuous_compact_support_measure hμ (by fun_prop)) 0 (h 0) 0
  simp only [zero_add, zero_smul, exponentialTilt_zero] at hd
  have h2 (v : Space n) : MemLp (fun x => inner ℝ v x) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    exact integrable_of_continuous_compact_support_measure hμ (by fun_prop)
  rw [covariance_comm, covariance_eq_sub (h2 (h 1)) (h2 (h 0))]
  exact ht.unique hd

theorem cumulantTensor_three_apply {n : ℕ} {μ : Measure (Space n)}
    [IsProbabilityMeasure μ] (hμ : IsCompact μ.support) (h : Fin 3 → Space n) :
    cumulantTensor μ 3 h = tiltThirdCumulant μ (fun _ => 0)
      (fun x => inner ℝ (h 0) x) (fun x => inner ℝ (h 1) x)
      (fun x => inner ℝ (h 2) x) := by
  have ht := hasDerivAt_cumulantTensor_exponentialTilt_eval hμ (m := 2) (by omega)
    0 (h 0) (Fin.tail h) 0
  simp only [zero_add, zero_smul, exponentialTilt_zero, Fin.cons_self_tail] at ht
  have he (u : ℝ) : cumulantTensor (exponentialTilt μ (u • h 0)) 2 (Fin.tail h) =
      covariance (fun x => inner ℝ (h 1) x) (fun x => inner ℝ (h 2) x)
        (exponentialTilt μ (u • h 0)) := by
    have := exponentialTilt_isProbability hμ (u • h 0)
    exact cumulantTensor_two_apply (isCompact_support_exponentialTilt hμ (u • h 0)) (Fin.tail h)
  simp_rw [he] at ht
  have hd := hasDerivAt_exponentialTilt_covariance hμ
    (f := fun x => inner ℝ (h 1) x) (g := fun x => inner ℝ (h 2) x)
    (by fun_prop) (by fun_prop) 0 (h 0) 0
  simp only [zero_add, zero_smul, inner_zero_left] at hd
  rw [ht.unique hd]
  unfold tiltThirdCumulant tiltAverage
  congr 1
  funext x
  ring

/-- The all-order Fréchet definition agrees entrywise with the existing BKL
third-cumulant matrix. This is a value identity and makes no identification of
the multilinear operator norm with the matrix Frobenius norm. -/
theorem IsIsotropic.cumulantTensor_three_coordinate {n : ℕ}
    {μ : Measure (Space n)} [IsProbabilityMeasure μ] (hμ : IsCompact μ.support)
    (hiso : IsIsotropic μ) (u : Space n) (i j : Fin n) :
    cumulantTensor μ 3 ![u, PiLp.single 2 i 1, PiLp.single 2 j 1] =
      thirdCumulantMatrix μ u i j := by
  rw [cumulantTensor_three_apply hμ, ← hiso.tiltThirdCumulant_zero u i j]
  unfold tiltThirdCumulant tiltAverage
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    EuclideanSpace.inner_single_left, map_one, one_mul]
  congr 1
  funext x
  ring

end KLS
end

#print axioms KLS.cumulantTensor_one_apply
#print axioms KLS.cumulantTensor_two_apply
#print axioms KLS.cumulantTensor_three_apply
#print axioms KLS.IsIsotropic.cumulantTensor_three_coordinate
