import OAI.Analysis.KLS.Model
import KLS.DensityToClass
import KLS.RealEndpoint
import KLS.WeightedFaithfulCutoff
import KLS.WeightedOptimalPoincare
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Explicit semantic bridges from the unchanged OpenAI model at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a to the original full KLS classes.
The upstream module is preserved byte for byte. -/

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff Topology
noncomputable section
namespace KLS.OpenAIBridge

theorem density_pointwise_logConcave {n : ℕ} {ρ : Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (x y : Space n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ENNReal.ofReal (ρ x)^t * ENNReal.ofReal (ρ y)^(1-t) ≤
      ENNReal.ofReal (ρ (t • x+(1-t) • y)) := by
  by_cases hx : ρ x = 0
  · simp only [hx, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact zero_le
  by_cases hy : ρ y = 0
  · simp only [hy, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1), mul_zero]
    exact zero_le
  have hx' : 0 < ρ x := (hρ.nonnegative x).lt_of_ne (Ne.symm hx)
  have hy' : 0 < ρ y := (hρ.nonnegative y).lt_of_ne (Ne.symm hy)
  have hz : 0 < ρ (t • x+(1-t) • y) :=
    hρ.log_concave.1 hx' hy' ht0.le (sub_nonneg.mpr ht1.le) (by ring)
  have hh := hρ.log_concave.2 hx' hy' ht0.le (sub_nonneg.mpr ht1.le)
    (by ring : t+(1-t)=1)
  change t*Real.log (ρ x)+(1-t)*Real.log (ρ y) ≤
    Real.log (ρ (t • x+(1-t) • y)) at hh
  rw [ENNReal.ofReal_rpow_of_pos hx', ENNReal.ofReal_rpow_of_pos hy',
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hρ.nonnegative x) t)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_def_of_pos hx', Real.rpow_def_of_pos hy', ← Real.exp_add]
  calc
    _ = Real.exp (t*Real.log (ρ x)+(1-t)*Real.log (ρ y)) := by congr 1; ring
    _ ≤ Real.exp (Real.log (ρ (t • x+(1-t) • y))) := Real.exp_le_exp.mpr hh
    _ = _ := Real.exp_log hz

theorem density_measureLogConcave {n : ℕ} {ρ : Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ) :
    measureLogConcave (OAI.LeanBlast.KLS.densityMeasure ρ) := by
  apply measureLogConcave_withDensity_of_pointwise hρ.measurable.ennreal_ofReal
  exact fun x y _ ht0 ht1 => density_pointwise_logConcave hρ x y ht0 ht1

theorem isotropic {n : ℕ} {μ : Measure (Space n)}
    (hμ : OAI.LeanBlast.KLS.IsIsotropic μ) : IsIsotropic μ := by
  refine ⟨Integrable.of_eval_piLp hμ.integrable_coordinate, ?_, hμ.integrable_product, ?_⟩
  · ext i
    rw [eval_integral_piLp hμ.integrable_coordinate i, hμ.mean_zero]
    rfl
  · ext i j
    simpa only [secondMomentMatrix, Matrix.one_apply] using hμ.second_moment i j

theorem admissible {n : ℕ} {ρ : Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    (hiso : OAI.LeanBlast.KLS.IsIsotropic (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    admissibleMeasure (OAI.LeanBlast.KLS.densityMeasure ρ) :=
  ⟨hρ.probability, density_measureLogConcave hρ, isotropic hiso⟩

theorem poincareBound_of_mem {n : ℕ} {ρ : Space n → ℝ}
    (hρ : OAI.LeanBlast.KLS.IsLogConcaveDensity ρ)
    {C : ℝ≥0} (hC : C ∈ poincareConstants (OAI.LeanBlast.KLS.densityMeasure ρ)) :
    OAI.LeanBlast.KLS.PoincareBound (OAI.LeanBlast.KLS.densityMeasure ρ) C := by
  let : IsProbabilityMeasure (OAI.LeanBlast.KLS.densityMeasure ρ) := hρ.probability
  intro f hf
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le (by simp)
  have he : energy (OAI.LeanBlast.KLS.densityMeasure ρ) f < ⊤ := by
    apply energy_lt_top_of_memLp_coordinateDerivative
    intro i
    exact (contDiff_coordinateDerivative hf.1 (m := 0) (by simp) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hf.2 i)
  obtain ⟨hf2, _hgrad, hh⟩ := finiteEnergy_real_poincare_of_mem_constants
    (μ := OAI.LeanBlast.KLS.densityMeasure ρ)
    (withDensity_absolutelyContinuous _ _) hC hf1.locallyLipschitz he
  have hv : OAI.LeanBlast.KLS.variance (OAI.LeanBlast.KLS.densityMeasure ρ) f =
      ProbabilityTheory.variance f (OAI.LeanBlast.KLS.densityMeasure ρ) := by
    exact (ProbabilityTheory.variance_eq_integral hf2.aemeasurable).symm
  rw [hv, ProbabilityTheory.variance_eq_sub hf2]
  exact hh

theorem statement_of_uniform_poincare {C : ℝ≥0} (hC : 0 < (C:ℝ))
    (hfull : ∀ (n : ℕ), 1 ≤ n → ∀ μ : Measure (Space n),
      admissibleMeasure μ → C ∈ poincareConstants μ) :
    OAI.LeanBlast.KLS.KLSStatement := by
  refine ⟨C, hC, ?_⟩
  intro n hn ρ hρ hiso
  exact poincareBound_of_mem hρ (hfull n hn _ (admissible hρ hiso))

end KLS.OpenAIBridge
end
