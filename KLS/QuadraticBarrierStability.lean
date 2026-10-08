import KLS.QuadraticAlexandrovViscosity

/-! Quantitative stability against a positive quadratic reference. Explicit
scaled quadratic barriers convert a density gap and a boundary error into an
interior sup-norm bound. This is a comparison estimate, not C2 regularity. -/

open MeasureTheory InnerProductSpace Matrix Set Filter
open scoped Topology ENNReal

noncomputable section
namespace KLS

variable {n : ℕ}

/-- Exact support-image bounds and boundary closeness imply explicit interior
closeness to a positive quadratic. The bound on its quadratic part is supplied
as ordinary geometric data on the compact comparison set. -/
theorem abs_sub_quadratic_le_of_subgradient_volume_bounds
    {u : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    {K : Set (Space n)} (hK : IsCompact K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ p : Space n) (c η B : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hquad : ∀ x ∈ K, (1 / 2 : ℝ) * inner ℝ (x - x₀) (matrixAction A (x - x₀)) ≤ B)
    (hboundary : ∀ x ∈ frontier K, |u x - centeredQuadratic A x₀ p c x| ≤ η)
    {a b : ℝ≥0∞}
    (halow : ENNReal.ofReal ((1 - δ) • A).det < a)
    (hbup : b < ENNReal.ofReal ((1 + δ) • A).det)
    (hmass : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      a * volume S ≤ volume (convexSubgradientImage u S) ∧
      volume (convexSubgradientImage u S) ≤ b * volume S) :
    ∀ x ∈ K, |u x - centeredQuadratic A x₀ p c x| ≤ η + δ * B := by
  let C := η + δ * B
  let qlo := centeredQuadratic ((1 + δ) • A) x₀ p (c - C)
  let qhi := centeredQuadratic ((1 - δ) • A) x₀ p (c + C)
  have hminus : ((1 - δ) • A).PosSemidef := (hA.smul (by linarith)).posSemidef
  have hplus : ((1 + δ) • A).PosSemidef := (hA.smul (by linarith)).posSemidef
  have heqlo (x : Space n) : qlo x - centeredQuadratic A x₀ p c x =
      δ * ((1 / 2 : ℝ) * inner ℝ (x - x₀) (matrixAction A (x - x₀))) - C := by
    simp only [qlo, centeredQuadratic, matrixAction_smul_scalar, inner_smul_right]
    ring
  have heqhi (x : Space n) : qhi x - centeredQuadratic A x₀ p c x =
      C - δ * ((1 / 2 : ℝ) * inner ℝ (x - x₀) (matrixAction A (x - x₀))) := by
    simp only [qhi, centeredQuadratic, matrixAction_smul_scalar, inner_smul_right]
    ring
  have hfront (x : Space n) (hx : x ∈ frontier K) : x ∈ K :=
    hK.isClosed.closure_eq ▸ frontier_subset_closure hx
  have hlo : ∀ x ∈ K, qlo x ≤ u x := by
    apply le_of_strict_subgradient_volume_comparison hK hu
      (continuous_centeredQuadratic _ _ _ _) huc
      (fun x hx => ?_) hbup
      (fun S hS hSK => by
        rw [volume_convexSubgradientImage_centeredQuadratic hplus]
        exact ⟨(hmass S hS hSK).2, le_rfl⟩)
    have hbd := (abs_le.mp (hboundary x hx)).1
    have hB := mul_le_mul_of_nonneg_left (hquad x (hfront x hx)) hδ.le
    have he := heqlo x
    dsimp [C] at he
    linarith
  have hhi : ∀ x ∈ K, u x ≤ qhi x := by
    apply le_of_strict_subgradient_volume_comparison hK
      (continuous_centeredQuadratic _ _ _ _) hu (convex_centeredQuadratic hminus _ _ _)
      (fun x hx => ?_) halow
      (fun S hS hSK => by
        rw [volume_convexSubgradientImage_centeredQuadratic hminus]
        exact ⟨le_rfl, (hmass S hS hSK).1⟩)
    have hbd := (abs_le.mp (hboundary x hx)).2
    have hB := mul_le_mul_of_nonneg_left (hquad x (hfront x hx)) hδ.le
    have he := heqhi x
    dsimp [C] at he
    linarith
  intro x hx
  have hnonneg : 0 ≤ δ * ((1 / 2 : ℝ) * inner ℝ (x - x₀) (matrixAction A (x - x₀))) :=
    mul_nonneg hδ.le (mul_nonneg (by norm_num) (inner_matrixAction_nonneg hA.posSemidef _))
  have hbelow := hlo x hx
  have habove := hhi x hx
  have hel := heqlo x
  have heh := heqhi x
  dsimp [C] at hel heh
  apply abs_le.mpr
  constructor <;> linarith

/-- The same explicit stability bound with a literal Alexandrov density.
The lower and upper density bounds are scalar data, not regularity premises. -/
theorem abs_sub_quadratic_le_of_alexandrov_density_bounds
    {u f : Space n → ℝ} (hu : Continuous u) (huc : ConvexOn ℝ univ u)
    {K : Set (Space n)} (hK : IsCompact K)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ p : Space n) (c η B : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hquad : ∀ x ∈ K, (1 / 2 : ℝ) * inner ℝ (x - x₀) (matrixAction A (x - x₀)) ≤ B)
    (hboundary : ∀ x ∈ frontier K, |u x - centeredQuadratic A x₀ p c x| ≤ η)
    {a b : ℝ} (halow : ((1 - δ) • A).det < a) (hbup : b < ((1 + δ) • A).det)
    (hf : ∀ x ∈ K, a ≤ f x ∧ f x ≤ b)
    (hMA : ∀ S : Set (Space n), IsOpen S → S ⊆ K →
      volume (convexSubgradientImage u S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂volume) :
    ∀ x ∈ K, |u x - centeredQuadratic A x₀ p c x| ≤ η + δ * B := by
  have haminus : 0 < ((1 - δ) • A).det := (hA.smul (by linarith)).det_pos
  have haplus : 0 < ((1 + δ) • A).det := (hA.smul (by linarith)).det_pos
  apply abs_sub_quadratic_le_of_subgradient_volume_bounds hu huc hK hA x₀ p c η B hδ hδ1
    hquad hboundary
    ((ENNReal.ofReal_lt_ofReal_iff (haminus.trans halow)).mpr halow)
    ((ENNReal.ofReal_lt_ofReal_iff haplus).mpr hbup)
  intro S hS hSK
  rw [hMA S hS hSK]
  constructor
  · calc
      _ = ∫⁻ _x in S, ENNReal.ofReal a ∂volume := by simp
      _ ≤ _ := setLIntegral_mono' hS.measurableSet
        (fun x hx => ENNReal.ofReal_le_ofReal (hf x (hSK hx)).1)
  · calc
      _ ≤ ∫⁻ _x in S, ENNReal.ofReal b ∂volume := setLIntegral_mono' hS.measurableSet
        (fun x hx => ENNReal.ofReal_le_ofReal (hf x (hSK hx)).2)
      _ = _ := by simp

end KLS
end

#print axioms KLS.abs_sub_quadratic_le_of_subgradient_volume_bounds
#print axioms KLS.abs_sub_quadratic_le_of_alexandrov_density_bounds
