import KLS.AdaptiveCumulantNoiseWords
import KLS.TiltCumulantLowOrders
import KLS.MaskedDirections

/-! Exact covariance contraction in the singleton terms of the cumulant drift. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS
variable {n : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

theorem listCumulant_eq_word (hμ : IsCompact μ.support) (vs : List (Space n)) :
    listCumulant μ vs = directionalWordDerivative (tiltLogLaplace μ) vs 0 := by
  have he := directionalWordDerivative_ofFn (contDiff_tiltLogLaplace hμ) vs.get (0 : Space n)
  simpa only [List.ofFn_get, listCumulant, cumulantTensor] using he.symm

theorem listCumulant_perm (hμ : IsCompact μ.support) {vs ws : List (Space n)}
    (hp : vs.Perm ws) : listCumulant μ vs = listCumulant μ ws := by
  rw [listCumulant_eq_word hμ, listCumulant_eq_word hμ]
  exact congrFun (directionalWordDerivative_perm (contDiff_tiltLogLaplace hμ) hp) 0

/-- The first slot of the literal cumulant tensor, with all later slots fixed. -/
def listCumulantHead (μ : Measure (Space n)) (vs : List (Space n)) : Space n →L[ℝ] ℝ :=
  (cumulantTensor μ (vs.length+1)).curryLeft.flipMultilinear vs.get

omit [IsProbabilityMeasure μ] in
theorem listCumulant_cons (v : Space n) (vs : List (Space n)) :
    listCumulant μ (v :: vs) = listCumulantHead μ vs v := by
  change cumulantTensor μ (vs.length+1) (v :: vs).get =
    cumulantTensor μ (vs.length+1) (Fin.cons v vs.get)
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

namespace AdaptiveLocalization
open KLS.StandardLocalization

theorem listCumulant_two_inverseSqrt (hμ : IsCompact μ.support)
    (z : Fin (n+n*n) → ℝ) (k : Fin n) (v : Space n) :
    listCumulant (law μ (decodeState z).1 (decodeState z).2)
      [inverseSqrtDirection μ z k, v] =
      ∑ i : Fin n, v i * (covariance μ (decodeState z).1 (decodeState z).2 *
        inverseSqrtCovariance μ (decodeState z)) i k := by
  let p := decodeState z
  letI := law_isProbability hμ p.1 p.2
  have hν : IsCompact (law μ p.1 p.2).support := by rwa [support_law hμ]
  change cumulantTensor (law μ p.1 p.2) 2 ([inverseSqrtDirection μ z k, v] : List (Space n)).get = _
  rw [cumulantTensor_two_apply hν]
  change ProbabilityTheory.covariance (fun x => inner ℝ (inverseSqrtDirection μ z k) x)
    (fun x => inner ℝ v x) (law μ p.1 p.2) = _
  rw [ProbabilityTheory.covariance_comm]
  have he : (fun x => inner ℝ v x) = fun x => ∑ i : Fin n, v i * x i := by
    funext x
    rw [inner_eq_coordinate_sum]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hp : (fun x => inner ℝ (inverseSqrtDirection μ z k) x) = projection μ p k :=
    funext (inner_inverseSqrtDirection z k)
  rw [he, hp]
  have hm (f : Space n → ℝ) (hf : Continuous f) : MemLp f 2 (law μ p.1 p.2) :=
    memLp_two_continuous_tilted hμ (continuous_exponent p.1 p.2) hf
  rw [ProbabilityTheory.covariance_fun_sum_left (fun i => hm _ (by fun_prop))
    (hm _ (continuous_projection p k))]
  simp only [ProbabilityTheory.covariance_const_mul_left, covariance_projection hμ]
  rfl

/-- Summing the whitened directions against the actual covariance recovers the vector. -/
theorem cumulant_two_inverseSqrt_reconstruction (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ) (v : Space n) :
    (∑ k : Fin n, listCumulant (law μ (decodeState z).1 (decodeState z).2)
      [inverseSqrtDirection μ z k, v] • inverseSqrtDirection μ z k) = v := by
  let p := decodeState z
  let A := covariance μ p.1 p.2
  let S := inverseSqrtCovariance μ p
  have hsym : A.transpose = A := (covariance_posDef hμ hfull p).isHermitian.isSymm.eq
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (covariance_posDef hμ hfull p).det_pos.ne'
  have hmat : S * (A*S).transpose = 1 := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hsym]
    rw [show S*S.transpose = inverseCovariance μ p from inverseSqrtCovariance_mul_transpose hμ hfull p]
    exact Matrix.nonsing_inv_mul _ hunit
  have hvec := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M *ᵥ (fun i => v i)) hmat
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at hvec
  apply PiLp.ext
  intro j
  change (EuclideanSpace.proj j) (∑ k : Fin n,
    listCumulant (law μ (decodeState z).1 (decodeState z).2)
      [inverseSqrtDirection μ z k, v] • inverseSqrtDirection μ z k) = v j
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hj := congrFun hvec j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at hj
  simp only [listCumulant_two_inverseSqrt hμ]
  change (∑ k : Fin n, (∑ i : Fin n, v i * (A*S) i k) * S j k) = v j
  convert hj using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Each singleton subset in the quadratic drift contracts to the original cumulant. -/
theorem cumulant_singleton_contraction (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (z : Fin (n+n*n) → ℝ)
    (v : Space n) (vs : List (Space n)) :
    (∑ k : Fin n, listCumulant (law μ (decodeState z).1 (decodeState z).2)
      [inverseSqrtDirection μ z k, v] *
      listCumulant (law μ (decodeState z).1 (decodeState z).2)
        (inverseSqrtDirection μ z k :: vs)) =
      listCumulant (law μ (decodeState z).1 (decodeState z).2) (v :: vs) := by
  simp only [listCumulant_cons]
  have he := congrArg (listCumulantHead (law μ (decodeState z).1 (decodeState z).2) vs)
    (cumulant_two_inverseSqrt_reconstruction hμ hfull z v)
  simpa only [map_sum, map_smul, smul_eq_mul, listCumulant_cons] using he

end AdaptiveLocalization
end KLS
end
#print axioms KLS.AdaptiveLocalization.cumulant_singleton_contraction
