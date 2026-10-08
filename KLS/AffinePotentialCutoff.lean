import KLS.MatrixActionMeasure
import KLS.GaussianExample
import KLS.WeightedIntegrationByParts
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

/-! Exact affine change of variables for finite smooth potentials and
conditional laws on balls. The normalization and Jacobian are explicit. -/

open MeasureTheory ProbabilityTheory Set Filter Metric Matrix
open scoped ENNReal ContDiff Topology

noncomputable section
namespace KLS

def affineMatrixEquiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Space n) (hA : A.det ≠ 0) : Space n ≃ᴬ[ℝ] Space n :=
  (((matrixAction A).toLinearMap.equivOfDetNeZero (by change (matrixAction A).det ≠ 0; rwa [det_matrixAction])).toContinuousLinearEquiv.toContinuousAffineEquiv).trans
      (ContinuousAffineEquiv.vaddConst ℝ b)

@[simp] lemma affineMatrixEquiv_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Space n) (hA : A.det ≠ 0) (x : Space n) :
    affineMatrixEquiv A b hA x = affineMatrixMap A b x := rfl

lemma map_volume_affineMatrixEquiv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b : Space n) (hA : A.det ≠ 0) :
    (volume : Measure (Space n)).map (affineMatrixEquiv A b hA) =
      ENNReal.ofReal |A.det⁻¹| • volume := by
  have he : (affineMatrixEquiv A b hA : Space n → Space n) =
      (fun y => y + b) ∘ (matrixAction A) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have hl : (volume : Measure (Space n)).map (matrixAction A) =
      ENNReal.ofReal |A.det⁻¹| • volume := by
    have hh := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
        (f := (matrixAction A).toLinearMap) (by change (matrixAction A).det ≠ 0; rwa [det_matrixAction])
    change volume.map (matrixAction A) = ENNReal.ofReal |(matrixAction A).det⁻¹| • volume at hh
    rwa [det_matrixAction] at hh
  rw [hl, Measure.map_smul _ (by fun_prop), Measure.IsAddRightInvariant.map_add_right_eq_self]

def affineTransformedPotential {n : ℕ} (V : Space n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0)
    (x : Space n) : ℝ :=
  V ((affineMatrixEquiv A b hA).symm x) - Real.log |A.det⁻¹|

lemma affineTransformedPotential_contDiff {n : ℕ} {V : Space n → ℝ}
    {m : ℕ∞} (hV : ContDiff ℝ m V)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    ContDiff ℝ m (affineTransformedPotential V A b hA) :=
  (hV.comp (affineMatrixEquiv A b hA).symm.toContinuousAffineMap.contDiff).sub contDiff_const

lemma affineTransformedPotential_convex {n : ℕ} {V : Space n → ℝ}
    (hV : ConvexOn ℝ univ V)
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0) :
    ConvexOn ℝ univ (affineTransformedPotential V A b hA) := by
  have hh : ConvexOn ℝ univ (fun x => V ((affineMatrixEquiv A b hA).symm x)) := by
    convert hV.comp_affineMap (affineMatrixEquiv A b hA).symm.toAffineEquiv.toAffineMap using 1 <;> simp [Function.comp_def]
  convert hh.add_const (-Real.log |A.det⁻¹|) using 1
  ext x
  simp [affineTransformedPotential, sub_eq_add_neg]

lemma map_potentialMeasure_affineMatrixEquiv {n : ℕ} {V : Space n → ℝ}
    (hV : Measurable V) (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n)
    (hA : A.det ≠ 0) :
    (potentialMeasure V).map (affineMatrixEquiv A b hA) =
      potentialMeasure (affineTransformedPotential V A b hA) := by
  let e := (affineMatrixEquiv A b hA).toHomeomorph.toMeasurableEquiv
  change ((volume : Measure (Space n)).withDensity
    (fun x => ENNReal.ofReal (Real.exp (-V x)))).map e = _
  rw [map_withDensity_measurableEquiv e _ _ (by fun_prop)]
  change ((volume.map (affineMatrixEquiv A b hA)).withDensity _) = _
  rw [map_volume_affineMatrixEquiv, withDensity_smul_measure,
    ← withDensity_smul _ (by fun_prop : Measurable
      ((fun x => ENNReal.ofReal (Real.exp (-V x))) ∘ e.symm))]
  congr 1
  funext x
  change ENNReal.ofReal |A.det⁻¹| * ENNReal.ofReal (Real.exp (-V (e.symm x))) = _
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  change |A.det⁻¹| * Real.exp (-V (e.symm x)) =
    Real.exp (-(V (e.symm x) - Real.log |A.det⁻¹|))
  rw [neg_sub, Real.exp_sub, Real.exp_log (abs_pos.mpr (inv_ne_zero hA)),
    Real.exp_neg, div_eq_mul_inv]

lemma potentialMeasure_add_const {n : ℕ} {V : Space n → ℝ}
    (hV : Measurable V) (c : ℝ) :
    potentialMeasure (fun x => V x + c) =
      ENNReal.ofReal (Real.exp (-c)) • potentialMeasure V := by
  unfold potentialMeasure
  rw [← withDensity_smul _ (by fun_prop : Measurable
    (fun x => ENNReal.ofReal (Real.exp (-V x))))]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, neg_add, Real.exp_add]
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

lemma restrict_closedBall_eq_restrict_ball_of_absolutelyContinuous {n : ℕ}
    {μ : Measure (Space n)} (hμ : μ ≪ volume) {r : ℝ} (hr : r ≠ 0) :
    μ.restrict (closedBall (0 : Space n) r) = μ.restrict (ball 0 r) := by
  apply Measure.restrict_congr_set
  have hs : μ (sphere (0 : Space n) r) = 0 :=
    hμ (Measure.addHaar_sphere_of_ne_zero volume 0 hr)
  filter_upwards [compl_mem_ae_iff.mpr hs] with x hx
  simp only [mem_compl_iff, mem_sphere] at hx
  simp only [mem_closedBall, mem_ball]
  exact propext (le_iff_lt_or_eq.trans (or_iff_left hx))

lemma cond_closedBall_potentialMeasure {n : ℕ} {μ : Measure (Space n)}
    [IsFiniteMeasure μ] {V : Space n → ℝ} (hV : Measurable V)
    (heq : μ = potentialMeasure V) {r : ℝ} (hr : r ≠ 0)
    (hm : μ (closedBall (0 : Space n) r) ≠ 0) :
    cond μ (closedBall (0 : Space n) r) =
      (potentialMeasure (fun x => V x + Real.log (μ.real (closedBall 0 r)))).restrict
        (ball 0 r) := by
  have hfin : μ (closedBall (0 : Space n) r) ≠ (∞ : ℝ≥0∞) := measure_ne_top μ _
  have hpos : 0 < μ.real (closedBall (0 : Space n) r) :=
    ENNReal.toReal_pos hm hfin
  have hc : ENNReal.ofReal (Real.exp (-Real.log (μ.real (closedBall 0 r)))) =
      (μ (closedBall (0 : Space n) r))⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hpos, ENNReal.ofReal_inv_of_pos hpos]
    exact congrArg Inv.inv (ENNReal.ofReal_toReal hfin)
  rw [potentialMeasure_add_const hV, hc, ← heq, Measure.restrict_smul, ProbabilityTheory.cond,
    restrict_closedBall_eq_restrict_ball_of_absolutelyContinuous _ hr]
  rw [heq]
  exact withDensity_absolutelyContinuous _ _

lemma map_restrict_affineMatrixEquiv {n : ℕ} (μ : Measure (Space n))
    (A : Matrix (Fin n) (Fin n) ℝ) (b : Space n) (hA : A.det ≠ 0)
    (s : Set (Space n)) :
    (μ.restrict s).map (affineMatrixEquiv A b hA) =
      (μ.map (affineMatrixEquiv A b hA)).restrict ((affineMatrixEquiv A b hA) '' s) := by
  let e := (affineMatrixEquiv A b hA).toHomeomorph.toMeasurableEquiv
  have hh := e.restrict_map μ (e '' s)
  rw [e.preimage_image] at hh
  exact hh.symm

end KLS
end

#print axioms KLS.map_potentialMeasure_affineMatrixEquiv
#print axioms KLS.cond_closedBall_potentialMeasure
#print axioms KLS.map_restrict_affineMatrixEquiv
