import KLS.DefinitionBridges

/-!
# Standard Gaussian in the original density-based KLS class

This module verifies that the standard Gaussian belongs to the original
density-based `IsKLSMeasure` class in every finite dimension. It supplies an
explicit finite quadratic potential and proves the probability and moment
conditions independently. Membership in the compact-set `admissibleMeasure`
class still needs the measure/density log-concavity bridge and is not asserted.
-/

open scoped ENNReal NNReal BigOperators ProbabilityTheory
open MeasureTheory ProbabilityTheory Set

noncomputable section
namespace KLS

/-- A concrete probability measure available in every finite dimension. -/
def gaussianExample (n : ℕ) : Measure (Space n) := stdGaussian (Space n)

instance gaussianExample_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (gaussianExample n) := by
  unfold gaussianExample
  infer_instance

instance gaussianExample_isGaussian (n : ℕ) : IsGaussian (gaussianExample n) := by
  unfold gaussianExample
  infer_instance

theorem gaussianExample_memLp_coordinate (n : ℕ) (i : Fin n) :
    MemLp (fun x : Space n => x i) 2 (gaussianExample n) := by
  exact IsGaussian.memLp_dual (gaussianExample n) (EuclideanSpace.proj (𝕜 := ℝ) i) 2
    (by simp)

theorem gaussianExample_integral_coordinate (n : ℕ) (i : Fin n) :
    (∫ x : Space n, x i ∂(gaussianExample n)) = 0 := by
  exact integral_strongDual_stdGaussian (EuclideanSpace.proj (𝕜 := ℝ) i)

theorem gaussianExample_secondMomentMatrix (n : ℕ) :
    secondMomentMatrix (gaussianExample n) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  have hc := covariance_eval_multivariateGaussian (μ := (0 : Space n))
    (S := (1 : Matrix (Fin n) (Fin n) ℝ)) Matrix.PosSemidef.one i j
  rw [multivariateGaussian_zero_one] at hc
  change ProbabilityTheory.covariance (fun x : Space n => x i)
    (fun x : Space n => x j) (gaussianExample n) = _ at hc
  rw [covariance_eq_sub (gaussianExample_memLp_coordinate n i)
    (gaussianExample_memLp_coordinate n j)] at hc
  simpa [secondMomentMatrix, gaussianExample_integral_coordinate] using hc

/-- Gaussian isotropy includes all moment integrability; the proof does not
infer moment identities from Lean's default value of an undefined integral. -/
theorem gaussianExample_isIsotropic (n : ℕ) : IsIsotropic (gaussianExample n) := by
  refine ⟨?_, ?_, ?_, gaussianExample_secondMomentMatrix n⟩
  · exact IsGaussian.integrable_fun_id
  · exact integral_id_stdGaussian
  · intro i j
    exact (gaussianExample_memLp_coordinate n i).integrable_mul
      (gaussianExample_memLp_coordinate n j)

theorem gaussianExample_integral_norm_sq (n : ℕ) :
    (∫ x : Space n, ‖x‖ ^ 2 ∂(gaussianExample n)) = (n : ℝ) :=
  (gaussianExample_isIsotropic n).integral_norm_sq

/-- Only the probability/isotropy portion of nonvacuity is certified here. -/
theorem exists_probability_isotropic (n : ℕ) :
    ∃ μ : Measure (Space n), IsProbabilityMeasure μ ∧ IsIsotropic μ :=
  ⟨gaussianExample n, inferInstance, gaussianExample_isIsotropic n⟩


lemma map_withDensity_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (e : α ≃ᵐ β) (μ : Measure α)
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.measurable,
    lintegral_withDensity_eq_lintegral_mul (g := fun x => g (e x)) μ hf (hg.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul (μ.map e) (hf.comp e.symm.measurable) hg,
    lintegral_map ((hf.comp e.symm.measurable).mul hg) e.measurable]
  simp

lemma pi_withDensity_ofReal {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i)) (hnn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ENNReal.ofReal (∏ i, f i (x i))
    ∂((Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (univ.pi s))) = _
  rw [Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun i => (hf i).restrict))
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg (fun i _ => hnn i (x i)))]
  rw [integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict
    (Filter.Eventually.of_forall (hnn i))

lemma gaussianExample_eq_withDensity_prod (n : ℕ) :
    gaussianExample n = (volume : Measure (Space n)).withDensity
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  rw [gaussianExample, ← map_pi_eq_stdGaussian]
  simp_rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0), gaussianPDF_def]
  rw [pi_withDensity_ofReal (fun _ : Fin n => gaussianPDFReal 0 1)
    (fun _ => integrable_gaussianPDFReal 0 1) (fun _ => gaussianPDFReal_nonneg 0 1)]
  change ((volume : Measure (Fin n → ℝ)).withDensity
    (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i)))).map
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)) = _
  rw [map_withDensity_measurableEquiv _ _ _ (by fun_prop)]
  rw [show (volume : Measure (Fin n → ℝ)).map (MeasurableEquiv.toLp 2 (Fin n → ℝ)) =
    (volume : Measure (Space n)) from (PiLp.volume_preserving_toLp (Fin n)).map_eq]
  rfl

def gaussianCoordinatePotential (x : ℝ) : ℝ :=
  x ^ 2 / 2 + Real.log (Real.sqrt (2 * Real.pi))

lemma gaussianPDFReal_eq_exp_potential (x : ℝ) :
    gaussianPDFReal 0 1 x = Real.exp (-gaussianCoordinatePotential x) := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  rw [gaussianCoordinatePotential, neg_add, Real.exp_add,
    Real.exp_neg (Real.log (Real.sqrt (2 * Real.pi))), Real.exp_log hs]
  simp [gaussianPDFReal, neg_div, mul_comm]

lemma gaussianCoordinatePotential_convex :
    ConvexOn ℝ univ gaussianCoordinatePotential := by
  have hsq : ConvexOn ℝ univ (fun x : ℝ => x ^ 2) :=
    (show Even (2 : ℕ) by decide).convexOn_pow
  convert (hsq.smul (c := (2 : ℝ)⁻¹) (by positivity)).add_const
      (Real.log (Real.sqrt (2 * Real.pi))) using 1
  ext x
  simp [gaussianCoordinatePotential, smul_eq_mul, div_eq_mul_inv, mul_comm]

def gaussianPotential (n : ℕ) (x : Space n) : ℝ :=
  ∑ i, gaussianCoordinatePotential (x i)

lemma gaussianPotential_convex (n : ℕ) : ConvexOn ℝ univ (gaussianPotential n) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change (∑ i, gaussianCoordinatePotential (a * x i + b * y i)) ≤
    a * (∑ i, gaussianCoordinatePotential (x i)) +
      b * (∑ i, gaussianCoordinatePotential (y i))
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact gaussianCoordinatePotential_convex.2 (mem_univ _) (mem_univ _) ha hb hab

lemma gaussianPotential_extendedConvex (n : ℕ) :
    ExtendedConvex (fun x : Space n => (gaussianPotential n x : WithTop ℝ)) := by
  simpa [ExtendedConvex] using (gaussianPotential_convex n).convex_epigraph

lemma gaussianPotential_exp_density (n : ℕ) :
    (fun x : Space n => expNegPotential (gaussianPotential n x : WithTop ℝ)) =
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  funext x
  simp only [expNegPotential, gaussianPotential]
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [← gaussianPDFReal_eq_exp_potential]

/-- The standard Gaussian has the explicitly constructed convex quadratic potential. -/
lemma gaussianExample_hasLogConcaveDensity (n : ℕ) :
    HasLogConcaveDensity (gaussianExample n) := by
  refine ⟨(fun x => (gaussianPotential n x : WithTop ℝ)),
    gaussianPotential_extendedConvex n, ?_, ?_⟩
  · rw [gaussianPotential_exp_density]
    fun_prop
  · rw [gaussianPotential_exp_density]
    exact gaussianExample_eq_withDensity_prod n

/-- Full nonvacuity of the original Job 45 density-based class. This does not
claim membership in the separate compact-set class without its bridge. -/
lemma gaussianExample_isKLSMeasure (n : ℕ) : IsKLSMeasure (gaussianExample n) where
  isProb := inferInstance
  absCont := (gaussianExample_hasLogConcaveDensity n).absolutelyContinuousLebesgue
  logConcave := gaussianExample_hasLogConcaveDensity n
  isotropic := gaussianExample_isIsotropic n

lemma exists_isKLSMeasure (n : ℕ) : ∃ μ : Measure (Space n), IsKLSMeasure μ :=
  ⟨gaussianExample n, gaussianExample_isKLSMeasure n⟩


end KLS
end

#print axioms KLS.gaussianExample_isIsotropic
#print axioms KLS.exists_probability_isotropic

#print axioms KLS.gaussianExample_isKLSMeasure
#print axioms KLS.exists_isKLSMeasure
