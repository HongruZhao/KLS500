import Entropy197500FullVerification
import KLS.GaussianExample
import KLS.CheegerNonvacuity

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal
noncomputable section

namespace FinalDustDefinitionAudit

theorem upstream_poincare_literal {n : ℕ} (μ : Measure (KLS.Space n)) (C : ℝ) :
    OAI.LeanBlast.KLS.PoincareBound μ C ↔
      ∀ f : KLS.Space n → ℝ, (ContDiff ℝ ∞ f ∧ HasCompactSupport f) →
        (∫ x, (f x-(∫ y, f y ∂μ))^2 ∂μ) ≤ C*(∫ x, ‖gradient f x‖^2 ∂μ) := Iff.rfl

theorem upstream_statement_literal : OAI.LeanBlast.KLS.KLSStatement ↔
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ρ : KLS.Space n → ℝ,
      OAI.LeanBlast.KLS.IsLogConcaveDensity ρ →
      OAI.LeanBlast.KLS.IsIsotropic (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) →
      ∀ f : KLS.Space n → ℝ, (ContDiff ℝ ∞ f ∧ HasCompactSupport f) →
        (∫ x, (f x-(∫ y, f y ∂volume.withDensity (fun x => ENNReal.ofReal (ρ x))))^2
          ∂volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ≤
        C*(∫ x, ‖gradient f x‖^2 ∂volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := Iff.rfl

theorem fixed500_literal : ∀ n : ℕ, 1 ≤ n → ∀ ρ : KLS.Space n → ℝ,
    OAI.LeanBlast.KLS.IsLogConcaveDensity ρ →
    OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ) →
    ∀ f : KLS.Space n → ℝ, (ContDiff ℝ ∞ f ∧ HasCompactSupport f) →
      (∫ x, (f x-(∫ y, f y ∂OAI.LeanBlast.KLS.densityMeasure ρ))^2
        ∂OAI.LeanBlast.KLS.densityMeasure ρ) ≤
      500*(∫ x, ‖gradient f x‖^2 ∂OAI.LeanBlast.KLS.densityMeasure ρ) :=
  OAI.LeanBlast.KLS.poincareBound500

def gaussianDensity (n : ℕ) (x : KLS.Space n) : ℝ := Real.exp (-KLS.gaussianPotential n x)

theorem gaussianDensity_measure (n : ℕ) :
    OAI.LeanBlast.KLS.densityMeasure (gaussianDensity n) = KLS.gaussianExample n := by
  rw [KLS.gaussianExample_eq_withDensity_prod]
  exact congrArg (fun d => (volume : Measure (KLS.Space n)).withDensity d)
    (KLS.gaussianPotential_exp_density n)

theorem gaussianDensity_logConcave (n : ℕ) :
    OAI.LeanBlast.KLS.IsLogConcaveDensity (gaussianDensity n) where
  nonnegative := fun x => (Real.exp_pos _).le
  measurable := by unfold gaussianDensity KLS.gaussianPotential KLS.gaussianCoordinatePotential;fun_prop
  probability := by rw [gaussianDensity_measure];infer_instance
  log_concave := by
    have hsupport : {x : KLS.Space n | 0 < gaussianDensity n x} = univ :=
      eq_univ_of_forall fun x => Real.exp_pos _
    rw [hsupport]
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    have hh := (KLS.gaussianPotential_convex n).2 (mem_univ x) (mem_univ y) ha hb hab
    change a*Real.log (gaussianDensity n x)+b*Real.log (gaussianDensity n y) ≤
      Real.log (gaussianDensity n (a • x+b • y))
    simp only [gaussianDensity,Real.log_exp]
    change KLS.gaussianPotential n (a • x+b • y) ≤
      a*KLS.gaussianPotential n x+b*KLS.gaussianPotential n y at hh
    linarith only [hh]

theorem gaussianDensity_isotropic (n : ℕ) :
    OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure (gaussianDensity n)) := by
  rw [gaussianDensity_measure]
  refine ⟨?_,?_,KLS.gaussianExample_integral_coordinate n,?_⟩
  · intro i
    exact (KLS.gaussianExample_memLp_coordinate n i).integrable (by norm_num)
  · intro i j
    exact (KLS.gaussianExample_memLp_coordinate n i).integrable_mul
      (KLS.gaussianExample_memLp_coordinate n j)
  · intro i j
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
      (KLS.gaussianExample_secondMomentMatrix n)
    simpa only [KLS.secondMomentMatrix,Matrix.one_apply] using h

theorem upstream_density_class_nonempty (n : ℕ) :
    ∃ ρ : KLS.Space n → ℝ, OAI.LeanBlast.KLS.IsLogConcaveDensity ρ ∧
      OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ) :=
  ⟨gaussianDensity n,gaussianDensity_logConcave n,gaussianDensity_isotropic n⟩

theorem original_admissible_class_nonempty (n : ℕ) :
    ∃ μ : Measure (KLS.Space n), KLS.admissibleMeasure μ :=
  ⟨KLS.gaussianExample n,(KLS.gaussianExample_isKLSMeasure n).admissibleMeasure⟩

theorem upstream_test_class_nonzero (n : ℕ) :
    ∃ f : KLS.Space n → ℝ, OAI.LeanBlast.KLS.IsTestFunction f ∧ f 0 = 1 := by
  let χ : ContDiffBump (0 : KLS.Space n) := ⟨1,2,by norm_num,by norm_num⟩
  exact ⟨χ,⟨χ.contDiff,χ.hasCompactSupport⟩,χ.one_of_mem_closedBall (by simp [χ])⟩

end FinalDustDefinitionAudit

#print axioms FinalDustDefinitionAudit.upstream_poincare_literal
#print axioms FinalDustDefinitionAudit.upstream_statement_literal
#print axioms FinalDustDefinitionAudit.fixed500_literal
#print axioms FinalDustDefinitionAudit.upstream_density_class_nonempty
#print axioms FinalDustDefinitionAudit.original_admissible_class_nonempty
#print axioms FinalDustDefinitionAudit.upstream_test_class_nonzero
#print axioms KLS.admissibleMeasure_iff_isKLSMeasure
#print axioms KLS.IsIsotropic.exists_cheeger_test
#print axioms OAI.LeanBlast.KLS.klsStatement500
#print axioms OAI.LeanBlast.KLS.fullStatement500
#print axioms KLS.admissibleMeasure.cheeger_lower_entropy197_500
#print axioms KLS.exactOpenAIKLSStatement_entropy197_500
