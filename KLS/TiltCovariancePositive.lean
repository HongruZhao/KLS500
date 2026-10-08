import KLS.CovarianceMatrix
import KLS.IsotropicSupport
import KLS.TiltCumulants

/-! Strict positive covariance from actual full affine support, preserved by
positive exponential tilting. No positive-definiteness assumption on the tilt. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped Topology
noncomputable section
namespace KLS

variable {n : ℕ} {μ : Measure (Space n)}

theorem eq_zero_of_affineSpan_support_eq_top_ae_inner_eq_const
    (hfull : affineSpan ℝ μ.support = ⊤) {u : Space n} {c : ℝ}
    (h : (fun x : Space n => inner ℝ u x) =ᵐ[μ] fun _ => c) : u = 0 := by
  have hs : μ.support ⊆ {x : Space n | inner ℝ u x = c} :=
    μ.support_subset_of_isClosed (isClosed_eq (by fun_prop) continuous_const) h
  let L : Space n →ₗ[ℝ] ℝ := (innerSL ℝ u).toLinearMap
  have he : L.toAffineMap = AffineMap.const ℝ (Space n) c :=
    AffineMap.ext_on hfull hs
  have hc : 0 = c := by
    have ht := congrArg (fun f : Space n →ᵃ[ℝ] ℝ => f 0) he
    simpa [L] using ht
  have hu : inner ℝ u u = 0 := by
    have ht := congrArg (fun f : Space n →ᵃ[ℝ] ℝ => f u) he
    simpa [L, ← hc] using ht
  exact inner_self_eq_zero.mp hu

/-- Full affine support forces the genuine covariance form to be strictly positive. -/
theorem covarianceMatrix_posDef_of_affineSpan_support_eq_top [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤) :
    (covarianceMatrix μ).PosDef := by
  have hmem (f : Space n → ℝ) (hf : Continuous f) : MemLp f 2 μ := by
    apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    exact integrable_of_continuous_compact_support_measure hμ (by fun_prop)
  have hid : MemLp (id : Space n → Space n) 2 μ := by
    apply MemLp.of_eval_piLp
    intro i
    exact hmem (fun x => x i) (by fun_prop)
  have hs : (covarianceBilin μ).toBilinForm.IsSymm := ⟨covarianceBilin_comm⟩
  change ((covarianceBilin μ).toBilinForm.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).PosDef
  apply (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis _ hs).mp
  intro u hu
  change 0 < covarianceBilin μ u u
  rw [covarianceBilin_self hid]
  apply lt_of_le_of_ne' (variance_nonneg _ _)
  intro hz
  have hae := ae_eq_integral_of_variance_eq_zero (hmem (fun x => inner ℝ u x) (by fun_prop)) hz
  exact hu (eq_zero_of_affineSpan_support_eq_top_ae_inner_eq_const hfull hae)

/-- Every positive continuous tilt preserves full affine dimension and strict
positive definiteness of the actual covariance, at every finite parameter. -/
theorem covarianceMatrix_tilted_posDef [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (hfull : affineSpan ℝ μ.support = ⊤)
    {q : Space n → ℝ} (hq : Continuous q) : (covarianceMatrix (μ.tilted q)).PosDef := by
  letI := tilted_isProbability_of_compact_support hμ hq
  have hs : (μ.tilted q).support = μ.support := tilted_support_eq hμ hq
  apply covarianceMatrix_posDef_of_affineSpan_support_eq_top
  · rwa [hs]
  · rwa [hs]

theorem IsIsotropic.covarianceMatrix_tilted_posDef [IsProbabilityMeasure μ]
    (hiso : IsIsotropic μ) (hμ : IsCompact μ.support)
    {q : Space n → ℝ} (hq : Continuous q) : (covarianceMatrix (μ.tilted q)).PosDef :=
  KLS.covarianceMatrix_tilted_posDef hμ hiso.affineSpan_support_eq_top hq

end KLS
end
#print axioms KLS.covarianceMatrix_tilted_posDef
#print axioms KLS.IsIsotropic.covarianceMatrix_tilted_posDef
