import KLS.LocalWeakProduct

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma integrable_mul_compact_of_locallyIntegrable
    {f ψ : Space n → ℝ} (hf : LocallyIntegrable f volume)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun x => f x * ψ x) volume := by
  simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport hψ hc

theorem hasLocalWeakCoordinateDerivative_of_contDiff
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    HasLocalWeakCoordinateDerivative f (coordinateDerivative f i) i := by
  intro ψ hψ hc
  have he := integral_mul_coordinateDerivative_of_hasCompactSupport_left hψ hf hc i
  have hl : (∫ x, ψ x * coordinateDerivative f i x) = ∫ x, coordinateDerivative f i x * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  have hr : (∫ x, coordinateDerivative ψ i x * f x) = ∫ x, f x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  rw [hl, hr] at he
  linarith

theorem hasLocalWeakCoordinateDerivative_const (c : ℝ) (i : Fin n) :
    HasLocalWeakCoordinateDerivative (fun _ : Space n => c) (fun _ => 0) i := by
  have h := hasLocalWeakCoordinateDerivative_of_contDiff (contDiff_const (c := c)) i
  have he : coordinateDerivative (fun _ : Space n => c) i = fun _ => 0 := by
    funext x
    simp only [coordinateDerivative, fderiv_const_apply, zero_apply]
  rwa [he] at h

theorem HasLocalWeakCoordinateDerivative.add
    {f g F G : Space n → ℝ} {i : Fin n}
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hG : HasLocalWeakCoordinateDerivative g G i)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hFloc : LocallyIntegrable F volume) (hGloc : LocallyIntegrable G volume) :
    HasLocalWeakCoordinateDerivative (fun x => f x + g x) (fun x => F x + G x) i := by
  intro ψ hψ hc
  have hdψ := (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
  have hdψc := hasCompactSupport_coordinateDerivative hc i
  have ha := integrable_mul_compact_of_locallyIntegrable hf hdψ hdψc
  have hb := integrable_mul_compact_of_locallyIntegrable hg hdψ hdψc
  have hA := integrable_mul_compact_of_locallyIntegrable hFloc hψ.continuous hc
  have hB := integrable_mul_compact_of_locallyIntegrable hGloc hψ.continuous hc
  change (∫ x, (f x + g x) * coordinateDerivative ψ i x) = -(∫ x, (F x + G x) * ψ x)
  simp only [add_mul]
  rw [integral_add ha hb, integral_add hA hB, hF ψ hψ hc, hG ψ hψ hc]
  ring

theorem HasLocalWeakCoordinateDerivative.const_mul
    {f F : Space n → ℝ} {i : Fin n}
    (hF : HasLocalWeakCoordinateDerivative f F i) (c : ℝ) :
    HasLocalWeakCoordinateDerivative (fun x => c * f x) (fun x => c * F x) i := by
  intro ψ hψ hc
  change (∫ x, c * f x * coordinateDerivative ψ i x) = -(∫ x, c * F x * ψ x)
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hF ψ hψ hc]
  ring

theorem hasLocalWeakCoordinateDerivative_finset_sum
    {ι : Type*} (s : Finset ι) {f F : ι → Space n → ℝ} {i : Fin n}
    (hF : ∀ a ∈ s, HasLocalWeakCoordinateDerivative (f a) (F a) i)
    (hf : ∀ a ∈ s, LocallyIntegrable (f a) volume)
    (hFloc : ∀ a ∈ s, LocallyIntegrable (F a) volume) :
    HasLocalWeakCoordinateDerivative (fun x => ∑ a ∈ s, f a x)
      (fun x => ∑ a ∈ s, F a x) i := by
  intro ψ hψ hc
  have hdψ := (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
  have hdψc := hasCompactSupport_coordinateDerivative hc i
  change (∫ x, (∑ a ∈ s, f a x) * coordinateDerivative ψ i x) =
    -(∫ x, (∑ a ∈ s, F a x) * ψ x)
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ (fun a ha => integrable_mul_compact_of_locallyIntegrable (hf a ha) hdψ hdψc),
    integral_finsetSum _ (fun a ha => integrable_mul_compact_of_locallyIntegrable (hFloc a ha) hψ.continuous hc)]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a ha => hF a ha ψ hψ hc

end KLS
end
