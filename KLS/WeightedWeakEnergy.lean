import KLS.WeightedWeakEquation

/-!
# The weak energy test and its Caccioppoli bound

The energy test χ²f is justified by actual smooth compact mollifications of
an L² function and its actual weak derivatives. The passage to the limit
uses strong L² pairings with compact continuous coefficients.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ}

lemma coordinateDerivative_cutoff_sq_mul {χ q : Space n → ℝ}
    (hχ : Differentiable ℝ χ) (hq : Differentiable ℝ q) (i : Fin n) (x : Space n) :
    coordinateDerivative (fun y => χ y ^ 2 * q y) i x =
      χ x ^ 2 * coordinateDerivative q i x +
        2 * χ x * coordinateDerivative χ i x * q x := by
  simp only [pow_two]
  have hχsq : DifferentiableAt ℝ (fun y => χ y * χ y) x := (hχ x).mul (hχ x)
  rw [coordinateDerivative_mul hχsq (hq x),
    coordinateDerivative_mul (hχ x) (hχ x)]
  ring

/-- The χ²f test is valid for actual L² weak derivatives. -/
theorem weak_energy_identity {ρ f χ : Space n → ℝ}
    (hρ : Continuous ρ) (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (G : Fin n → Lp ℝ 2 (volume : Measure (Space n)))
    (hG : ∀ i, HasWeakCoordinateDerivative f i (G i))
    (hχ : ContDiff ℝ 3 χ) (hc : HasCompactSupport χ)
    (hweak : ∀ q : Space n → ℝ, ContDiff ℝ 3 q → HasCompactSupport q →
      (∑ i, ∫ x, G i x * (ρ x *
        coordinateDerivative (fun y => χ y ^ 2 * q y) i x)) = 0) :
    (∑ i, ((∫ x, (ρ x * χ x ^ 2 * G i x) * G i x) +
      (∫ x, (2 * ρ x * χ x * coordinateDerivative χ i x * G i x) * f x))) = 0 := by
  let A : Fin n → Space n → ℝ := fun i x => ρ x * χ x ^ 2 * G i x
  let B : Fin n → Space n → ℝ :=
    fun i x => 2 * ρ x * χ x * coordinateDerivative χ i x * G i x
  have hac : HasCompactSupport (fun x => ρ x * χ x ^ 2) := by
    convert! (hc.mul_right (f' := χ)).mul_left (f := ρ) using 1
    funext x
    simp only [pow_two, Pi.mul_apply]
  have hA (i : Fin n) : MemLp (A i) 2 volume :=
    ((hρ.mul (hχ.continuous.pow 2)).memLp_top_of_hasCompactSupport hac volume).mul (Lp.memLp (G i))
  have hB (i : Fin n) : MemLp (B i) 2 volume := by
    have hbcont : Continuous (fun x => 2 * ρ x * χ x * coordinateDerivative χ i x) :=
      ((continuous_const.mul hρ).mul hχ.continuous).mul
        (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
    have hbcomp : HasCompactSupport (fun x => 2 * ρ x * χ x * coordinateDerivative χ i x) :=
      (hc.mul_left (f := fun x => 2 * ρ x)).mul_right
    exact (hbcont.memLp_top_of_hasCompactSupport hbcomp volume).mul (Lp.memLp (G i))
  have hm (k : ℕ) : MemLp (mollify k f) 2 volume := memLp_mollify hf k
  have hdm (k : ℕ) (i : Fin n) : MemLp (coordinateDerivative (mollify k f) i) 2 volume := by
    rw [(hG i).mollify_eq hf]
    exact memLp_mollify (Lp.memLp (G i)) k
  have hlim (i : Fin n) : Tendsto
      (fun k => (∫ x, A i x * coordinateDerivative (mollify k f) i x) +
        ∫ x, B i x * mollify k f x) atTop
      (𝓝 ((∫ x, A i x * G i x) + ∫ x, B i x * f x)) :=
    (tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero (fun k => hdm k i)
      (Lp.memLp (G i)) (hA i) ((hG i).eLpNorm_mollify_derivative_sub_tendsto_zero hf)).add
      (tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hm hf (hB i)
        (eLpNorm_mollify_sub_tendsto_zero hf))
  have hz (k : ℕ) : (∑ i, ((∫ x, A i x * coordinateDerivative (mollify k f) i x) +
      (∫ x, B i x * mollify k f x))) = 0 := by
    have hs := hweak (mollify k f)
      ((mollify_contDiff (hf.locallyIntegrable (by norm_num)) k).of_le (by simp))
      (hasCompactSupport_mollify hfc k)
    convert hs using 1
    apply Finset.sum_congr rfl
    intro i _
    have hadd := integral_add ((hA i).integrable_mul (hdm k i)) ((hB i).integrable_mul (hm k))
    simp only [Pi.add_apply, Pi.mul_apply] at hadd
    rw [← hadd]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [A, B]
      rw [coordinateDerivative_cutoff_sq_mul (hχ.differentiable (by norm_num))
        ((mollify_contDiff (hf.locallyIntegrable (by norm_num)) k).differentiable (by simp))]
      ring
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  have he := tendsto_nhds_unique hs (show Tendsto
      (fun k => ∑ i, ((∫ x, A i x * coordinateDerivative (mollify k f) i x) +
        (∫ x, B i x * mollify k f x))) atTop (𝓝 0) from by simpa only [hz] using tendsto_const_nhds)
  exact he

/-- The completed weak energy test gives the usual Caccioppoli constant four. -/
theorem weak_caccioppoli {ρ f χ : Space n → ℝ}
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (G : Fin n → Lp ℝ 2 (volume : Measure (Space n)))
    (hG : ∀ i, HasWeakCoordinateDerivative f i (G i))
    (hχ : ContDiff ℝ 3 χ) (hc : HasCompactSupport χ)
    (hweak : ∀ q : Space n → ℝ, ContDiff ℝ 3 q → HasCompactSupport q →
      (∑ i, ∫ x, G i x * (ρ x *
        coordinateDerivative (fun y => χ y ^ 2 * q y) i x)) = 0) :
    (∑ i, ∫ x, ρ x * χ x ^ 2 * (G i x) ^ 2) ≤
      4 * ∑ i, ∫ x, ρ x * f x ^ 2 * (coordinateDerivative χ i x) ^ 2 := by
  let E : Fin n → Space n → ℝ := fun i x => (ρ x * χ x ^ 2 * G i x) * G i x
  let C : Fin n → Space n → ℝ :=
    fun i x => (2 * ρ x * χ x * coordinateDerivative χ i x * G i x) * f x
  let B : Fin n → Space n → ℝ :=
    fun i x => (ρ x * (coordinateDerivative χ i x) ^ 2 * f x) * f x
  have pair {a v w : Space n → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
      (hv : MemLp v 2 volume) (hw : MemLp w 2 volume) :
      Integrable (fun x => (a x * v x) * w x) volume := by
    have hav : MemLp (fun x => a x * v x) 2 volume :=
      (ha.memLp_top_of_hasCompactSupport hac volume).mul hv
    exact hav.integrable_mul hw
  have hE (i : Fin n) : Integrable (E i) volume := by
    apply pair (hρ.mul (hχ.continuous.pow 2)) _ (Lp.memLp (G i)) (Lp.memLp (G i))
    convert! (hc.mul_right (f' := χ)).mul_left (f := ρ) using 1
    funext x
    simp only [pow_two, Pi.mul_apply]
  have hC (i : Fin n) : Integrable (C i) volume := by
    apply pair (((continuous_const.mul hρ).mul hχ.continuous).mul
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous) _ (Lp.memLp (G i)) hf
    exact (hc.mul_left (f := fun x => 2 * ρ x)).mul_right
  have hB (i : Fin n) : Integrable (B i) volume := by
    apply pair (hρ.mul ((contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous.pow 2)) _ hf hf
    convert!
      ((hasCompactSupport_coordinateDerivative hc i).mul_right
        (f' := coordinateDerivative χ i)).mul_left (f := ρ) using 1
    funext x
    simp only [pow_two, Pi.mul_apply]
  have hi (i : Fin n) : 0 ≤ (∫ x, E i x) + 2 * (∫ x, C i x) + 4 * (∫ x, B i x) := by
    have h1 := integral_add (hE i) ((hC i).const_mul 2)
    have h2 := integral_add ((hE i).add ((hC i).const_mul 2)) ((hB i).const_mul 4)
    simp only [Pi.add_apply] at h1 h2
    rw [← integral_const_mul, ← h1, ← integral_const_mul, ← h2]
    apply integral_nonneg
    intro x
    dsimp only [E, C, B]
    convert mul_nonneg (hρ0 x)
      (sq_nonneg (χ x * G i x + 2 * f x * coordinateDerivative χ i x)) using 1 <;> ring
  have hs : 0 ≤ (∑ i, ∫ x, E i x) + 2 * (∑ i, ∫ x, C i x) +
      4 * (∑ i, ∫ x, B i x) := by
    simpa only [Finset.sum_add_distrib, Finset.mul_sum] using Finset.sum_nonneg (fun i _ => hi i)
  have hz := weak_energy_identity hρ hf hfc G hG hχ hc hweak
  change (∑ i, ((∫ x, E i x) + (∫ x, C i x))) = 0 at hz
  rw [Finset.sum_add_distrib] at hz
  have hbound : (∑ i, ∫ x, E i x) ≤ 4 * ∑ i, ∫ x, B i x := by linarith
  convert hbound using 1
  · apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [E]; ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [B]; ring

end KLS
end

#print axioms KLS.weak_energy_identity
#print axioms KLS.weak_caccioppoli
