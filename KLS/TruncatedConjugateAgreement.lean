import KLS.TruncatedConjugateCoercivity
import KLS.ReciprocalConjugateTransport
import KLS.SubgradientAffineCovariance

/-! The globally finite truncation agrees on an actual open region with the
finite conjugate. On this region its global subgradient image has exactly the
same volume as the relative conjugate image, even after affine centering. -/

open MeasureTheory InnerProductSpace Set Filter Metric
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

def truncatedConjugateAgreementRegion (u : Space n → ℝ) (M : ℝ) : Set (Space n) :=
  interior (momentLegendreDomain u) ∩
    {p | ‖gradient (finiteLegendrePotential u) p‖ < M}

theorem isOpen_truncatedConjugateAgreementRegion
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u) (M : ℝ) :
    IsOpen (truncatedConjugateAgreementRegion u M) := by
  exact (continuousOn_gradient_finiteLegendrePotential_of_strictConvexOn hu hc).norm
    |>.isOpen_inter_preimage isOpen_interior isOpen_Iio

theorem convexSubgradient_subset_truncatedConjugateAgreementRegion
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {x : Space n} {M : ℝ} (hx : ‖x‖ < M)
    (hD : convexSubgradient u x ⊆ interior (momentLegendreDomain u)) :
    convexSubgradient u x ⊆ truncatedConjugateAgreementRegion u M := by
  intro p hp
  refine ⟨hD hp, ?_⟩
  change ‖gradient (finiteLegendrePotential u) p‖ < M
  rw [gradient_finiteLegendrePotential_eq_of_mem_convexSubgradient hu hc (hD hp) hp]
  exact hx

theorem truncatedLegendrePotential_eq_on_agreementRegion
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {M : ℝ} {p : Space n} (hp : p ∈ truncatedConjugateAgreementRegion u M) :
    truncatedLegendrePotential u M p = finiteLegendrePotential u p := by
  exact truncatedLegendrePotential_eq_finiteLegendrePotential_of_contact hu
    ((norm_nonneg _).trans hp.2.le)
    (mem_convexSubgradient_gradient_finiteLegendrePotential hu hc hp.1) hp.2.le

theorem truncatedLegendrePotential_eventuallyEq_on_agreementRegion
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {M : ℝ} {p : Space n} (hp : p ∈ truncatedConjugateAgreementRegion u M) :
    truncatedLegendrePotential u M =ᶠ[𝓝 p] finiteLegendrePotential u := by
  filter_upwards [(isOpen_truncatedConjugateAgreementRegion hu hc M).mem_nhds hp] with q hq
  exact truncatedLegendrePotential_eq_on_agreementRegion hu hc hq

theorem convexSubgradient_truncatedLegendrePotential_eq_relative
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {M : ℝ} {p : Space n} (hp : p ∈ truncatedConjugateAgreementRegion u M) :
    convexSubgradient (truncatedLegendrePotential u M) p =
      convexSubgradientOn (finiteLegendrePotential u) (momentLegendreDomain u) p := by
  have heq := truncatedLegendrePotential_eventuallyEq_on_agreementRegion hu hc hp
  have hd := (differentiableAt_finiteLegendrePotential_of_strictConvexOn hu hc hp.1).congr_of_eventuallyEq heq
  rw [convexSubgradient_eq_singleton_of_differentiableAt
    (convexOn_truncatedLegendrePotential hu ((norm_nonneg _).trans hp.2.le)) hd,
    convexSubgradientOn_finiteLegendrePotential_eq_singleton hu hc hp.1,
    heq.gradient_eq]

theorem convexSubgradientImage_truncatedLegendrePotential_eq_relative
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    {M : ℝ} {S : Set (Space n)} (hS : S ⊆ truncatedConjugateAgreementRegion u M) :
    convexSubgradientImage (truncatedLegendrePotential u M) S =
      convexSubgradientImageOn (finiteLegendrePotential u) (momentLegendreDomain u) S := by
  ext p
  constructor
  · rintro ⟨q, hq, hp⟩
    exact ⟨q, hq, (convexSubgradient_truncatedLegendrePotential_eq_relative hu hc (hS hq)) ▸ hp⟩
  · rintro ⟨q, hq, hp⟩
    exact ⟨q, hq, (convexSubgradient_truncatedLegendrePotential_eq_relative hu hc (hS hq)).symm ▸ hp⟩

theorem volume_convexSubgradientImage_centeredTruncatedConjugate
    {u : Space n → ℝ} (hu : Continuous u) (hc : StrictConvexOn ℝ univ u)
    (x : Space n) {M : ℝ} {S : Set (Space n)}
    (hS : S ⊆ truncatedConjugateAgreementRegion u M) :
    volume (convexSubgradientImage (centeredTruncatedConjugate u x M) S) =
      volume (convexSubgradientImageOn (finiteLegendrePotential u) (momentLegendreDomain u) S) := by
  have heq : centeredTruncatedConjugate u x M =
      fun p => truncatedLegendrePotential u M p + inner ℝ (-x) p + u x := by
    funext p
    simp only [centeredTruncatedConjugate, inner_neg_left, sub_eq_add_neg]
  rw [heq, volume_convexSubgradientImage_add_affine,
    convexSubgradientImage_truncatedLegendrePotential_eq_relative hu hc hS]

end KLS
end

#print axioms KLS.isOpen_truncatedConjugateAgreementRegion
#print axioms KLS.convexSubgradient_truncatedLegendrePotential_eq_relative
#print axioms KLS.volume_convexSubgradientImage_centeredTruncatedConjugate
