import KLS.WeakHessianVarianceMean
import KLS.RawWeakBrascampLieb
import KLS.RawHessianTraceTerms

open Matrix InnerProductSpace MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ContDiff ENNReal NNReal Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

theorem measurable_actual_inverse_hessian_entry (φ : Space n → ℝ) (i j : Fin n) :
    Measurable (fun x => (coordinateHessian φ x)⁻¹ i j) := by
  have hH : Measurable (coordinateHessian φ) :=
    Measurable.of_eval (fun a => Measurable.of_eval
      (fun b => measurable_coordinateDerivative (coordinateDerivative φ b) a))
  have hd : Measurable (fun x => (coordinateHessian φ x).det) :=
    (continuous_id.matrix_det.measurable).comp hH
  have ha : Measurable (fun x => (coordinateHessian φ x).adjugate i j) :=
    ((continuous_id.matrix_adjugate.matrix_elem i j).measurable).comp hH
  have ht : Measurable (fun x => (coordinateHessian φ x).det⁻¹ *
      (coordinateHessian φ x).adjugate i j) := hd.inv.mul ha
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul] using ht

theorem aestronglyMeasurable_rawInverseHessianGradientForm
    {φ : Space n → ℝ} {F : Fin n → Space n → ℝ} {μ : Measure (Space n)}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ) :
    AEStronglyMeasurable (rawInverseHessianGradientForm φ F) μ := by
  unfold rawInverseHessianGradientForm
  exact Finset.univ.aestronglyMeasurable_fun_sum fun i _ =>
    Finset.univ.aestronglyMeasurable_fun_sum fun j _ =>
      ((measurable_actual_inverse_hessian_entry φ i j).aestronglyMeasurable.mul (hF i)).mul (hF j)

theorem rawInverseHessianGradientForm_nonneg
    {φ : Space n → ℝ} {x : Space n} (hpos : (coordinateHessian φ x).PosDef)
    (F : Fin n → Space n → ℝ) : 0 ≤ rawInverseHessianGradientForm φ F x := by
  rw [rawInverseHessianGradientForm, matrix_quadratic_sum_eq_dotProduct]
  simpa only [star_trivial] using hpos.inv.posSemidef.dotProduct_mulVec_nonneg (fun i => F i x)

/-- The actual scalar energies sum to the noncommuting raw trace energy. -/
theorem sum_raw_energy_hessianCongruence
    (φ : Space n → ℝ) (T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) (x : Space n) (hT : ∀ i, (T x i).IsSymm) :
    (∑ a, ∑ b, rawInverseHessianGradientForm φ
      (fun i y => (R * T y i * R.transpose) a b) x) =
      rawHessianTraceGradientTerm (coordinateHessian φ x) (R.transpose * R) (T x) := by
  unfold rawInverseHessianGradientForm
  have hswap : (∑ a, ∑ b, ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
      (R * T x i * R.transpose) a b * (R * T x j * R.transpose) a b) =
      ∑ i, ∑ j, (coordinateHessian φ x)⁻¹ i j *
        (∑ a, ∑ b, (R * T x i * R.transpose) a b * (R * T x j * R.transpose) a b) := by
    simp_rw [Finset.mul_sum, mul_assoc]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [matrix_congruence_entrywise_inner _ _ _ (hT _)]
  rfl

/-- Finite total trace energy gives finite energy of each entry, using
nonnegativity and the proved raw energy identity. -/
theorem integrable_raw_hessianCongruence_energy
    {φ : Space n → ℝ} {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hpos : ∀ᵐ x, (coordinateHessian φ x).PosDef)
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTs : ∀ᵐ x, ∀ k, (T x k).IsSymm) (R : Matrix (Fin n) (Fin n) ℝ)
    (hA : Integrable (fun x => rawHessianTraceGradientTerm (coordinateHessian φ x)
      (R.transpose * R) (T x)) (potentialMeasure φ)) (a b : Fin n) :
    Integrable (rawInverseHessianGradientForm φ (fun i y => (R * T y i * R.transpose) a b))
      (potentialMeasure φ) := by
  have hF (i : Fin n) : LocallyIntegrable (fun y => (R * T y i * R.transpose) a b) volume :=
    locallyIntegrable_of_memLp_two_on_compacts (fun S hS =>
      memLp_two_matrixCongruence_raw (fun c d => hTl i c d S hS) R a b)
  have hac := withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (Real.exp (-φ x)))
  have hm := aestronglyMeasurable_rawInverseHessianGradientForm (φ := φ)
    (fun i => (hF i).aestronglyMeasurable.mono_ac hac)
  apply hA.mono' hm
  have hposμ : ∀ᵐ x ∂potentialMeasure φ, (coordinateHessian φ x).PosDef := hac.ae_le hpos
  have hTsμ : ∀ᵐ x ∂potentialMeasure φ, ∀ k, (T x k).IsSymm := hac.ae_le hTs
  filter_upwards [hposμ, hTsμ] with x hx ht
  rw [Real.norm_of_nonneg (rawInverseHessianGradientForm_nonneg hx _),
    ← sum_raw_energy_hessianCongruence φ T R x ht]
  have h1 : rawInverseHessianGradientForm φ (fun i y => (R * T y i * R.transpose) a b) x ≤
      ∑ j, rawInverseHessianGradientForm φ (fun i y => (R * T y i * R.transpose) a j) x :=
    Finset.single_le_sum (fun j _ => rawInverseHessianGradientForm_nonneg hx
      (fun i y => (R * T y i * R.transpose) a j)) (Finset.mem_univ b)
  exact h1.trans (Finset.single_le_sum (fun i _ => Finset.sum_nonneg
    (fun j _ => rawInverseHessianGradientForm_nonneg hx
      (fun k y => (R * T y k * R.transpose) i j))) (Finset.mem_univ a))

theorem sum_integral_raw_energy_hessianCongruence
    {φ : Space n → ℝ} {T : Space n → Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hpos : ∀ᵐ x, (coordinateHessian φ x).PosDef)
    (hTl : ∀ k i j S, IsCompact S → MemLp (fun x => T x k i j) 2 (volume.restrict S))
    (hTs : ∀ᵐ x, ∀ k, (T x k).IsSymm) (R : Matrix (Fin n) (Fin n) ℝ)
    (hA : Integrable (fun x => rawHessianTraceGradientTerm (coordinateHessian φ x)
      (R.transpose * R) (T x)) (potentialMeasure φ)) :
    (∑ a, ∑ b, ∫ x, rawInverseHessianGradientForm φ
      (fun i y => (R * T y i * R.transpose) a b) x ∂potentialMeasure φ) =
      ∫ x, rawHessianTraceGradientTerm (coordinateHessian φ x) (R.transpose * R) (T x)
        ∂potentialMeasure φ := by
  have he (a b : Fin n) := integrable_raw_hessianCongruence_energy hpos hTl hTs R hA a b
  calc
    _ = ∑ a, ∫ x, ∑ b, rawInverseHessianGradientForm φ
        (fun i y => (R * T y i * R.transpose) a b) x ∂potentialMeasure φ := by
      apply Finset.sum_congr rfl
      intro a _
      exact (integral_finsetSum Finset.univ (fun b _ => he a b)).symm
    _ = ∫ x, ∑ a, ∑ b, rawInverseHessianGradientForm φ
        (fun i y => (R * T y i * R.transpose) a b) x ∂potentialMeasure φ :=
      (integral_finsetSum Finset.univ
        (fun a _ => integrable_finsetSum Finset.univ (fun b _ => he a b))).symm
    _ = _ := by
      apply integral_congr_ae
      have hTsμ : ∀ᵐ x ∂potentialMeasure φ, ∀ k, (T x k).IsSymm :=
        (withDensity_absolutelyContinuous volume (fun x => ENNReal.ofReal (Real.exp (-φ x)))).ae_le hTs
      filter_upwards [hTsμ] with x hx
      exact sum_raw_energy_hessianCongruence φ T R x hx

end KLS
end
