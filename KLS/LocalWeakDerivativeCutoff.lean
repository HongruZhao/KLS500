import KLS.LocalWeakDerivativeUniqueness

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A compact smooth multiplier turns a genuine local L2 weak derivative
into a global L2 derivative, with the exact product formula retained. -/
theorem HasLocalWeakCoordinateDerivative.compact_mul
    {f F χ : Space n → ℝ} {i : Fin n}
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K))
    (hFloc : ∀ K : Set (Space n), IsCompact K → MemLp F 2 (volume.restrict K))
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ) :
    ∃ W : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => χ x * f x) i W ∧
      ∀ᵐ x, W x = χ x * F x + coordinateDerivative χ i x * f x := by
  have hcf := memLp_compact_mul_of_local hχ.continuous hc hf
  have hcF := memLp_compact_mul_of_local hχ.continuous hc hFloc
  have hdf := memLp_compact_mul_of_local
    (contDiff_coordinateDerivative hχ (m := 0) (by norm_num) i).continuous
    (hasCompactSupport_coordinateDerivative hc i) hf
  have hW : MemLp (fun x => χ x * F x + coordinateDerivative χ i x * f x) 2 volume :=
    hcF.add hdf
  let W := hW.toLp (fun x => χ x * F x + coordinateDerivative χ i x * f x)
  have hWe : ∀ᵐ x, W x = χ x * F x + coordinateDerivative χ i x * f x := hW.coeFn_toLp
  refine ⟨W, ?_, hWe⟩
  intro ψ hψ hψc
  have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hdψLp : MemLp (coordinateDerivative ψ i) 2 volume :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hψc i)
  have ha : Integrable (fun x => (χ x * F x) * ψ x) volume := hcF.integrable_mul hψLp
  have hb : Integrable (fun x => (coordinateDerivative χ i x * f x) * ψ x) volume :=
    hdf.integrable_mul hψLp
  have hd : Integrable (fun x => (χ x * f x) * coordinateDerivative ψ i x) volume :=
    hcf.integrable_mul hdψLp
  have hw := hF (fun x => χ x * ψ x) (hχ.mul hψ) hc.mul_right
  have hl : (∫ x, f x * coordinateDerivative (fun y => χ y * ψ y) i x) =
      (∫ x, (coordinateDerivative χ i x * f x) * ψ x) +
      ∫ x, (χ x * f x) * coordinateDerivative ψ i x := by
    rw [← integral_add hb hd]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [coordinateDerivative_mul (hχ.differentiable (by norm_num) x)
        (hψ.differentiable (by norm_num) x)]
      ring
  have hr : (∫ x, F x * (χ x * ψ x)) = ∫ x, (χ x * F x) * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  have hwi : (∫ x, W x * ψ x) = (∫ x, (χ x * F x) * ψ x) +
      ∫ x, (coordinateDerivative χ i x * f x) * ψ x := by
    rw [← integral_add ha hb]
    apply integral_congr_ae
    filter_upwards [hWe] with x hx
    rw [hx]
    ring
  rw [hl, hr] at hw
  rw [hwi]
  linarith

end KLS
end
