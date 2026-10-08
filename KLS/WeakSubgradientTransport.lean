import KLS.MomentLegendreRegularity
import KLS.RademacherOnOpen
import KLS.SubgradientTransport

/-! Exact compact subgradient-image mass from genuine weak gradient transport.
Absolute continuity of the target gives differentiability of the finite
Legendre conjugate almost everywhere, hence uniqueness of inverse support
points. Source strict convexity and smoothness are not assumed. -/

open MeasureTheory InnerProductSpace Set Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

theorem eq_gradient_of_support_on_interior {F : Space n → ℝ} {D : Set (Space n)}
    {p x : Space n} (hp : p ∈ interior D) (hF : DifferentiableAt ℝ F p)
    (hs : ∀ q ∈ D, F p + inner ℝ x (q - p) ≤ F q) : x = gradient F p := by
  have hm : IsLocalMin (fun q => F q - inner ℝ x q) p := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hp] with q hq
    have hh := hs q hq
    simp only [inner_sub_right] at hh
    linarith
  have hd : HasFDerivAt (fun q => F q - inner ℝ x q)
      (fderiv ℝ F p - innerSL ℝ x) p :=
    hF.hasFDerivAt.sub (innerSL ℝ x).hasFDerivAt
  have hz := hm.hasFDerivAt_eq_zero hd
  apply ext_inner_right ℝ
  intro q
  have hh := congrArg (fun T : Space n →L[ℝ] ℝ => T q) hz
  change fderiv ℝ F p q - inner ℝ x q = 0 at hh
  rw [inner_gradient_left]
  linarith

theorem ae_mem_momentLegendreDomain_map_gradient
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hzero : φ 0 = 0)
    {ρ : Measure (Space n)} (hρ : ρ ≪ volume) :
    ∀ᵐ p ∂ρ.map (gradient φ), p ∈ momentLegendreDomain φ := by
  have hDm : MeasurableSet (momentLegendreDomain φ) := by
    exact (measurable_normalizedLegendreTransform φ) (measurableSet_singleton ∞).compl
  apply (ae_map_iff (measurable_gradient φ).aemeasurable hDm).mpr
  filter_upwards [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hρ
    hLip.locallyLipschitz] with x hx
  exact mem_momentLegendreDomain_of_mem_convexSubgradient hzero
    (gradient_mem_convexSubgradient hc hx)

theorem ae_unique_inverse_convexSubgradient_of_zero
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) (hzero : φ 0 = 0)
    {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    (htarget : ρ.map (gradient φ) ≪ volume) :
    ∀ᵐ p ∂ρ.map (gradient φ), ∀ x y,
      p ∈ convexSubgradient φ x → p ∈ convexSubgradient φ y → x = y := by
  have hdual := convexOn_ae_mem_interior_and_differentiableAt htarget
    (convexOn_normalizedLegendreTransform_toReal φ)
    (ae_mem_momentLegendreDomain_map_gradient hLip hc hzero hρ)
  filter_upwards [hdual] with p hp
  intro x y hx hy
  have hxg := eq_gradient_of_support_on_interior hp.1 hp.2
    (fun q hq => finiteLegendre_support_of_mem_convexSubgradient hzero hx hq)
  have hyg := eq_gradient_of_support_on_interior hp.1 hp.2
    (fun q hq => finiteLegendre_support_of_mem_convexSubgradient hzero hy hq)
  exact hxg.trans hyg.symm

lemma convexSubgradient_sub_const (φ : Space n → ℝ) (c : ℝ) (x : Space n) :
    convexSubgradient (fun y => φ y - c) x = convexSubgradient φ x := by
  ext p
  constructor <;> intro hp y
  · have hh := hp y
    dsimp at hh
    linarith
  · have hh := hp y
    dsimp
    linarith

lemma gradient_sub_const (φ : Space n → ℝ) (c : ℝ) :
    gradient (fun y => φ y - c) = gradient φ := by
  funext x
  simp only [gradient, fderiv_sub_const]

theorem ae_unique_inverse_convexSubgradient
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    (htarget : ρ.map (gradient φ) ≪ volume) :
    ∀ᵐ p ∂ρ.map (gradient φ), ∀ x y,
      p ∈ convexSubgradient φ x → p ∈ convexSubgradient φ y → x = y := by
  have hLip' : LipschitzWith L (fun y => φ y - φ 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show (φ x - φ 0) - (φ y - φ 0) = φ x - φ y by ring,
      ← Real.dist_eq]
    exact hLip.dist_le_mul x y
  have hc' : ConvexOn ℝ univ (fun y => φ y - φ 0) := by
    convert! hc.add_const (-φ 0) using 1
  have hh := ae_unique_inverse_convexSubgradient_of_zero hLip'
    hc' (by simp) hρ
    (by simpa only [gradient_sub_const] using htarget)
  simpa only [gradient_sub_const, convexSubgradient_sub_const] using hh

/-- Equality is obtained from the actual weak gradient pushforward when both
source and target are absolutely continuous. No strict convexity is assumed. -/
theorem measure_eq_map_gradient_convexSubgradientImage
    {φ : Space n → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L φ)
    (hc : ConvexOn ℝ univ φ) {ρ : Measure (Space n)} (hρ : ρ ≪ volume)
    (htarget : ρ.map (gradient φ) ≪ volume)
    {S : Set (Space n)} (hS : IsCompact S) :
    ρ S = (ρ.map (gradient φ)) (convexSubgradientImage φ S) := by
  rw [Measure.map_apply (measurable_gradient φ)
    (isCompact_convexSubgradientImage hLip hS).measurableSet]
  have hunique := ae_of_ae_map (measurable_gradient φ).aemeasurable
    (ae_unique_inverse_convexSubgradient hLip hc hρ htarget)
  apply measure_congr
  filter_upwards [locallyLipschitz_ae_differentiableAt_of_absolutelyContinuous hρ
    hLip.locallyLipschitz, hunique] with x hx hu
  apply propext
  constructor
  · intro hxS
    exact ⟨x, hxS, gradient_mem_convexSubgradient hc hx⟩
  · rintro ⟨y, hyS, hxy⟩
    have heq := hu x y (gradient_mem_convexSubgradient hc hx) hxy
    simpa only [heq] using hyS

end KLS
end

#print axioms KLS.ae_unique_inverse_convexSubgradient
#print axioms KLS.measure_eq_map_gradient_convexSubgradientImage
