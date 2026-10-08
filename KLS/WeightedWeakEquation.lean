import KLS.WeakDerivativeMollification

/-!
# The actual first-order weak equation on compact localizations

Weak derivatives obtained from weighted annihilation obey the weighted
gradient equation on every compact region on which the localization agrees
with the original function. All test pairings below are ordinary integrals
of actual representatives; compact support supplies their integrability.
-/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ}

lemma tsupport_coordinateDerivative_subset (f : Space n → ℝ) (i : Fin n) :
    tsupport (coordinateDerivative f i) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)

lemma weightedDiffusion_eq_zero_of_notMem_tsupport {φ f : Space n → ℝ} {x : Space n}
    (hx : x ∉ tsupport f) : weightedDiffusion φ f x = 0 := by
  have hd (i : Fin n) : coordinateDerivative f i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hi => hx (tsupport_coordinateDerivative_subset f i hi))
  have hh (i : Fin n) : coordinateHessian f x i i = 0 := by
    change coordinateDerivative (coordinateDerivative f i) i x = 0
    exact image_eq_zero_of_notMem_tsupport (fun hi => hx
      ((tsupport_coordinateDerivative_subset _ i).trans
        (tsupport_coordinateDerivative_subset f i) hi))
  simp [weightedDiffusion_eq_sum, hd, hh]

/-- The actual weak gradient pairing equals minus the actual diffusion pairing. -/
theorem weak_gradient_pairing_eq_neg_diffusion {φ f ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hf : MemLp f 2 volume)
    (G : Fin n → Lp ℝ 2 (volume : Measure (Space n)))
    (hG : ∀ i, HasWeakCoordinateDerivative f i (G i))
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ) :
    (∑ i, ∫ x, G i x * (Real.exp (-φ x) * coordinateDerivative ψ i x)) =
      -(∫ x, f x * (Real.exp (-φ x) * weightedDiffusion φ ψ x)) := by
  let w : Fin n → Space n → ℝ := fun i x => Real.exp (-φ x) * coordinateDerivative ψ i x
  have hw (i : Fin n) : ContDiff ℝ 1 (w i) :=
    ((hφ.of_le (by norm_num)).neg.exp).mul
      (contDiff_coordinateDerivative hψ (m := 1) (by norm_num) i)
  have hwc (i : Fin n) : HasCompactSupport (w i) :=
    (hasCompactSupport_coordinateDerivative hc i).mul_left
  have hi (i : Fin n) : Integrable (fun x => f x * coordinateDerivative (w i) i x) volume := by
    have hd : MemLp (coordinateDerivative (w i) i) 2 volume :=
      (contDiff_coordinateDerivative (hw i) (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_coordinateDerivative (hwc i) i)
    exact hf.integrable_mul hd
  have he (i : Fin n) : (∫ x, G i x * w i x) =
      -(∫ x, f x * coordinateDerivative (w i) i x) := by
    have ht := hG i (w i) (hw i) (hwc i)
    linarith
  calc
    _ = ∑ i, -(∫ x, f x * coordinateDerivative (w i) i x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact he i
    _ = -(∫ x, ∑ i, f x * coordinateDerivative (w i) i x) := by
      rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun i _ => hi i)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.mul_sum, ← exp_neg_mul_weightedDiffusion_eq_sum_derivative
          (hφ.of_le (by norm_num)) (hψ.of_le (by norm_num)) x]

/-- If a compact localization agrees with an annihilator on the test support,
its actual weak gradient satisfies the weighted homogeneous equation there. -/
theorem weighted_annihilator_weak_gradient_test {φ f ψ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hf : MemLp f 2 volume) (G : Fin n → Lp ℝ 2 (volume : Measure (Space n)))
    (hG : ∀ i, HasWeakCoordinateDerivative f i (G i))
    (hψ : ContDiff ℝ 3 ψ) (hc : HasCompactSupport ψ)
    (heq : ∀ x ∈ tsupport ψ, f x = u x) :
    (∑ i, ∫ x, G i x * (Real.exp (-φ x) * coordinateDerivative ψ i x)) = 0 := by
  rw [weak_gradient_pairing_eq_neg_diffusion hφ hf G hG hψ hc]
  have hpair : (∫ x, f x * (Real.exp (-φ x) * weightedDiffusion φ ψ x)) =
      ∫ x, u x * weightedDiffusion φ ψ x ∂potentialMeasure φ := by
    rw [integral_potentialMeasure hφ.continuous.measurable]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport ψ
      · rw [heq x hx]
        ring
      · simp [weightedDiffusion_eq_zero_of_notMem_tsupport hx]
  rw [hpair, hu ψ hψ hc, neg_zero]

/-- All compact C³ tests multiplied by χ² stay in the region of agreement. -/
theorem weighted_annihilator_localized_weak_equation {φ f χ : Space n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (u : Lp ℝ 2 (potentialMeasure φ))
    (hu : ∀ g : Space n → ℝ, ContDiff ℝ 3 g → HasCompactSupport g →
      (∫ x, u x * weightedDiffusion φ g x ∂potentialMeasure φ) = 0)
    (hf : MemLp f 2 volume) (G : Fin n → Lp ℝ 2 (volume : Measure (Space n)))
    (hG : ∀ i, HasWeakCoordinateDerivative f i (G i))
    (hχ : ContDiff ℝ 3 χ) (hc : HasCompactSupport χ)
    (heq : ∀ x ∈ tsupport χ, f x = u x) :
    ∀ q : Space n → ℝ, ContDiff ℝ 3 q → HasCompactSupport q →
      (∑ i, ∫ x, G i x * (Real.exp (-φ x) *
        coordinateDerivative (fun y => χ y ^ 2 * q y) i x)) = 0 := by
  intro q hq _
  have hcc : HasCompactSupport (fun y => χ y ^ 2 * q y) := by
    convert! (hc.mul_right (f' := χ)).mul_right (f' := q) using 1
    funext x
    simp only [pow_two, Pi.mul_apply]
  apply weighted_annihilator_weak_gradient_test hφ u hu hf G hG
    ((hχ.pow 2).mul hq) hcc
  intro x hx
  apply heq x
  apply tsupport_mul_subset_left (f := χ) (g := fun y => χ y * q y)
  simpa only [pow_two, mul_assoc] using hx

end KLS
end

#print axioms KLS.weak_gradient_pairing_eq_neg_diffusion
#print axioms KLS.weighted_annihilator_weak_gradient_test
#print axioms KLS.weighted_annihilator_localized_weak_equation
