import KLS.SuspensionMixedCumulants
import KLS.LinearCumulantTaylor

/-! A literal suspension direction combines the noise coordinate and an
identically replicated affine direction; their squared norms add exactly. -/
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators
noncomputable section
namespace KLS

def suspensionPureProjection (n N : ℕ) :
    Space (suspensionDimension n N) →L[ℝ] Space (suspensionDimension n N) :=
  ContinuousLinearMap.id ℝ _ -
    (suspensionNoiseProjection n N).smulRight (suspensionNoiseDirection n N)

lemma suspensionPureProjection_apply (n N : ℕ) (z : Space (suspensionDimension n N)) :
    suspensionPureProjection n N z =
      z - (suspensionNoiseProjection n N z) • suspensionNoiseDirection n N := rfl

lemma suspensionNoiseProjection_pureProjection (n N : ℕ)
    (z : Space (suspensionDimension n N)) :
    suspensionNoiseProjection n N (suspensionPureProjection n N z) = 0 := by
  simp [suspensionPureProjection_apply, map_sub, map_smul,
    suspensionNoiseProjection_noiseDirection]

lemma suspensionCopyProjection_pureProjection (n N : ℕ) (i : Fin N)
    (z : Space (suspensionDimension n N)) :
    suspensionCopyProjection n N i (suspensionPureProjection n N z) =
      suspensionCopyProjection n N i z := by
  simp [suspensionPureProjection_apply, map_sub, map_smul,
    suspensionCopyProjection_noiseDirection]

lemma suspensionPureProjection_eq_self {n N : ℕ} (z : Space (suspensionDimension n N))
    (hz : suspensionNoiseProjection n N z = 0) : suspensionPureProjection n N z = z := by
  simp [suspensionPureProjection_apply, hz]

def suspensionCombinedDirection (n N : ℕ) (a : ℝ) (u : Space n) :
    Space (suspensionDimension n N) :=
  WithLp.toLp 2 (fun k => Option.elim
    ((Fintype.equivFin (SuspensionIndex n N)).symm k) a
    (fun ij => (Real.sqrt N)⁻¹ * u ij.2))

lemma suspensionCombinedDirection_apply (n N : ℕ) (a : ℝ) (u : Space n)
    (j : SuspensionIndex n N) :
    suspensionCombinedDirection n N a u (Fintype.equivFin _ j) =
      Option.elim j a (fun ij => (Real.sqrt N)⁻¹ * u ij.2) := by
  simp [suspensionCombinedDirection]

lemma suspensionNoiseProjection_combinedDirection (n N : ℕ) (a : ℝ) (u : Space n) :
    suspensionNoiseProjection n N (suspensionCombinedDirection n N a u) = a := by
  simp [suspensionNoiseProjection, suspensionCombinedDirection]

lemma suspensionCopyProjection_combinedDirection (n N : ℕ) (a : ℝ) (u : Space n) (i : Fin N) :
    suspensionCopyProjection n N i (suspensionCombinedDirection n N a u) = (Real.sqrt N)⁻¹ • u := by
  ext j
  simp [suspensionCopyProjection, suspensionCombinedDirection]

lemma suspensionCombinedDirection_decomposition (n N : ℕ) (a : ℝ) (u : Space n) :
    suspensionCombinedDirection n N a u =
      a • suspensionNoiseDirection n N + suspensionCombinedDirection n N 0 u := by
  ext k
  obtain ⟨j, rfl⟩ := (Fintype.equivFin (SuspensionIndex n N)).surjective k
  cases j <;> simp [suspensionCombinedDirection_apply, suspensionNoiseDirection]

lemma suspensionCombinedDirection_norm_sq {n N : ℕ} (hN : 0 < N) (a : ℝ) (u : Space n) :
    ‖suspensionCombinedDirection n N a u‖^2 = a^2 + ‖u‖^2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN').ne'
  have hsq : (Real.sqrt N)^2 = (N : ℝ) := Real.sq_sqrt hN'.le
  rw [EuclideanSpace.real_norm_sq_eq, ← (Fintype.equivFin (SuspensionIndex n N)).sum_comp]
  simp_rw [suspensionCombinedDirection_apply]
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [Option.elim_none, Option.elim_some, mul_pow, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  have hc : ((Real.sqrt N)⁻¹)^2 * (N : ℝ) = 1 := by
    field_simp
    exact hsq.symm
  rw [← mul_assoc, hc, one_mul]

end KLS
end
