import KLS.LocalHarmonicMollification
import KLS.WeakGradientExtraction

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal Topology
noncomputable section
namespace KLS
variable {n : ℕ}

lemma integral_gradient_mul_eq_zero_of_divergence_zero_on_tsupport
    {f : Space n → ℝ} {G : Fin n → Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hdiv : ∀ x ∈ tsupport f, ∑ i, coordinateDerivative (G i) i x = 0) :
    (∫ x, ∑ i, coordinateDerivative f i x * G i x) = 0 := by
  have hleft (i : Fin n) : Integrable (fun x => f x * coordinateDerivative (G i) i x) :=
    (hf.continuous.mul (contDiff_coordinateDerivative (hG i) (m := 0) (by norm_num) i).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hright (i : Fin n) : Integrable (fun x => coordinateDerivative f i x * G i x) :=
    ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.mul (hG i).continuous).integrable_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc i).mul_right
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => integral_mul_coordinateDerivative_of_hasCompactSupport_left hf (hG i) hc i)
  rw [← integral_finsetSum _ (fun i _ => hleft i), Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun i _ => hright i)] at hsum
  have hz : (∫ x, ∑ i, f x * coordinateDerivative (G i) i x) = 0 := by
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun x => by
      dsimp only [Pi.zero_apply]
      rw [← Finset.mul_sum]
      by_cases hx : x ∈ tsupport f
      · rw [hdiv x hx, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [hz] at hsum
  exact neg_eq_zero.mp hsum.symm

/-- Local harmonicity only on the cutoff support suffices for the actual
Caccioppoli estimate. -/
theorem harmonic_caccioppoli_coordinate_on_tsupport {χ h : Space n → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hh : ContDiff ℝ 2 h) (hc : HasCompactSupport χ)
    (heq : ∀ x ∈ tsupport χ, coordinateLaplacian h x = 0) :
    (∫ x, ∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) ≤
      4 * (∫ x, ∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) := by
  let f : Space n → ℝ := fun x => χ x * χ x * h x
  have hf : ContDiff ℝ 1 f := (hχ.mul hχ).mul (hh.of_le (by norm_num))
  have hfc : HasCompactSupport f := hc.mul_right.mul_right
  have hfs : tsupport f ⊆ tsupport χ := tsupport_mul_subset_left.trans tsupport_mul_subset_left
  have hG (i : Fin n) : ContDiff ℝ 1 (coordinateDerivative h i) :=
    contDiff_coordinateDerivative hh (m := 1) (by norm_num) i
  have hzero := integral_gradient_mul_eq_zero_of_divergence_zero_on_tsupport hf hfc hG
    (fun x hx => heq x (hfs hx))
  have hdf (i : Fin n) (x : Space n) : coordinateDerivative f i x =
      2 * χ x * h x * coordinateDerivative χ i x + χ x ^ 2 * coordinateDerivative h i x := by
    dsimp only [f]
    rw [coordinateDerivative_mul ((hχ.mul hχ).differentiable (by norm_num) x)
      (hh.differentiable (by norm_num) x),
      coordinateDerivative_mul (hχ.differentiable (by norm_num) x) (hχ.differentiable (by norm_num) x)]
    ring
  have hdcχ (i : Fin n) := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
  have hdch (i : Fin n) := (contDiff_coordinateDerivative hh (m := 0) (by norm_num) i).continuous
  have hE : Integrable (fun x => ∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) :=
    integrable_finsetSum _ (fun i _ =>
      ((hχ.continuous.pow 2).mul ((hdch i).pow 2)).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right))
  have hA : Integrable (fun x => ∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) :=
    integrable_finsetSum _ (fun i _ =>
      ((hh.continuous.pow 2).mul ((hdcχ i).pow 2)).integrable_of_hasCompactSupport
        (by simpa [pow_two, Pi.mul_def] using
          (hasCompactSupport_coordinateDerivative hc i).mul_right.mul_left))
  have hD : Integrable (fun x => ∑ i, coordinateDerivative f i x * coordinateDerivative h i x) :=
    integrable_finsetSum _ (fun i _ =>
      ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) i).continuous.mul (hG i).continuous).integrable_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hfc i).mul_right)
  have hp (x : Space n) : (∑ i, χ x ^ 2 * coordinateDerivative h i x ^ 2) ≤
      4 * (∑ i, h x ^ 2 * coordinateDerivative χ i x ^ 2) +
        2 * (∑ i, coordinateDerivative f i x * coordinateDerivative h i x) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [hdf]
    nlinarith [sq_nonneg (χ x * coordinateDerivative h i x + 2 * h x * coordinateDerivative χ i x)]
  have hm := integral_mono hE ((hA.const_mul 4).add (hD.const_mul 2)) hp
  have hsplit := integral_add (hA.const_mul 4) (hD.const_mul 2)
  simp only [Pi.add_apply] at hm hsplit
  rwa [hsplit, integral_const_mul, integral_const_mul, hzero, mul_zero, add_zero] at hm

/-- Shifted mollifications which are harmonic on a compact cutoff support have
uniform global L2 bounds for the actual derivatives of their cutoff products. -/
theorem exists_uniform_derivative_sq_compact_mul_shifted_harmonic_mollify
    {χ v : Space n → ℝ} (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hv : MemLp v 2 volume) (N : ℕ)
    (heq : ∀ k x, x ∈ tsupport χ → coordinateLaplacian (mollify (k + N) v) x = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℕ, ∀ i : Fin n,
      (∫ x, coordinateDerivative (fun y => χ y * mollify (k + N) v y) i x ^ 2) ≤ M := by
  have hvloc := hv.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hAex (i : Fin n) : ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
      (∫ x, coordinateDerivative χ i x ^ 2 * mollify k v x ^ 2) ≤ A :=
    exists_uniform_integral_sq_compact_mul_mollify
      (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
      (hasCompactSupport_coordinateDerivative hc i) (fun K _ => hv.restrict K)
  choose A hA0 hAb using hAex
  refine ⟨10 * (∑ i, A i), mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hA0 i)), ?_⟩
  intro k i
  have hhk : ContDiff ℝ 2 (mollify (k + N) v) := (mollify_contDiff hvloc _).of_le (by simp)
  let f : Space n → ℝ := fun x => χ x * mollify (k + N) v x
  have hf : ContDiff ℝ 1 f := hχ.mul (hhk.of_le (by norm_num))
  have hfc : HasCompactSupport f := hc.mul_right
  have hdcχ (j : Fin n) := (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) j).continuous
  have hdch (j : Fin n) := (contDiff_coordinateDerivative hhk (m := 0) (by norm_num) j).continuous
  have hEi (j : Fin n) : Integrable (fun x => χ x ^ 2 * coordinateDerivative (mollify (k + N) v) j x ^ 2) :=
    ((hχ.continuous.pow 2).mul ((hdch j).pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using hc.mul_right.mul_right)
  have hAi (j : Fin n) : Integrable (fun x => mollify (k + N) v x ^ 2 * coordinateDerivative χ j x ^ 2) :=
    ((hhk.continuous.pow 2).mul ((hdcχ j).pow 2)).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using
        (hasCompactSupport_coordinateDerivative hc j).mul_right.mul_left)
  have hPi (j : Fin n) : Integrable (fun x => coordinateDerivative f j x ^ 2) :=
    ((contDiff_coordinateDerivative hf (m := 0) (by norm_num) j).continuous.pow 2).integrable_of_hasCompactSupport
      (by simpa [pow_two, Pi.mul_def] using (hasCompactSupport_coordinateDerivative hfc j).mul_right)
  have hE := integrable_finsetSum Finset.univ (fun j _ => hEi j)
  have hA := integrable_finsetSum Finset.univ (fun j _ => hAi j)
  have hP := integrable_finsetSum Finset.univ (fun j _ => hPi j)
  have hAbound : (∫ x, ∑ j, mollify (k + N) v x ^ 2 * coordinateDerivative χ j x ^ 2) ≤ ∑ j, A j := by
    rw [integral_finsetSum _ (fun j _ => hAi j)]
    exact Finset.sum_le_sum (fun j _ => by simpa only [mul_comm] using hAb j (k + N))
  have henergy := harmonic_caccioppoli_coordinate_on_tsupport hχ hhk hc (heq k)
  have hpoint (x : Space n) : (∑ j, coordinateDerivative f j x ^ 2) ≤
      2 * (∑ j, χ x ^ 2 * coordinateDerivative (mollify (k + N) v) j x ^ 2) +
        2 * (∑ j, mollify (k + N) v x ^ 2 * coordinateDerivative χ j x ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [f]
    rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x) (hhk.differentiable (by norm_num) x)]
    nlinarith [sq_nonneg (χ x * coordinateDerivative (mollify (k + N) v) j x -
      mollify (k + N) v x * coordinateDerivative χ j x)]
  have hpbound := integral_mono hP ((hE.const_mul 2).add (hA.const_mul 2)) hpoint
  have hsplit := integral_add (hE.const_mul 2) (hA.const_mul 2)
  simp only [Pi.add_apply] at hpbound hsplit
  rw [hsplit, integral_const_mul, integral_const_mul] at hpbound
  have hsumBound : (∫ x, ∑ j, coordinateDerivative f j x ^ 2) ≤ 10 * (∑ j, A j) := by linarith
  apply le_trans (integral_mono (hPi i) hP ?_) hsumBound
  intro x
  exact Finset.single_le_sum (fun j _ => sq_nonneg (coordinateDerivative f j x)) (Finset.mem_univ i)

end KLS
end
