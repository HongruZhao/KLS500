import KLS.TiltNumeratorDerivativeBounds
import KLS.WeightedL2TaylorTensor

/-! Continuity of each actual Taylor coefficient on the whole weighted L2
space. Its auxiliary bounds depend on the fixed law and order and do not use
the universal Taylor estimate that the suspension argument aims to prove. -/

open MeasureTheory Matrix
open scoped ENNReal ContDiff BigOperators
noncomputable section
namespace KLS

variable {n : ℕ} {V : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure V)]
  (hV : ContDiff ℝ 2 V) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a))

include hV hκ hlower

theorem exists_tiltAverage_derivative_L2_bound (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℝ 2 (potentialMeasure V),
      ‖iteratedFDeriv ℝ d (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure V) z) 0‖ ≤
        C * ‖f‖ := by
  classical
  choose C hC0 hC using fun i : ℕ => exists_tiltNumerator_derivative_L2_bound hV hκ hlower i
  let Z := tiltNumerator (potentialMeasure V) (fun _ => 0) (fun _ => 1)
  have hZ : ContDiff ℝ (⊤ : ℕ∞) Z := contDiff_tiltNumerator_of_normExponentialDomain
    (normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower (memLp_const (1 : ℝ)))
  have hZpos (z : Space n) : 0 < Z z := by
    simpa only [Z, tiltNumerator, zero_add, one_mul] using
      integral_exp_pos (integrable_exp_inner_potentialMeasure hV hκ hlower z)
  let H : Space n → ℝ := fun z => (Z z)⁻¹
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hZ.inv (fun z => (hZpos z).ne')
  let K := ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * C i *
    ‖iteratedFDeriv ℝ (d - i) H 0‖
  refine ⟨K, Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC0 i)) (norm_nonneg _)), ?_⟩
  intro f
  have hN := contDiff_tiltNumerator_of_normExponentialDomain
    (normExponentialDomain_of_memLp_potentialMeasure hV hκ hlower (Lp.memLp f))
  have he : (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure V) z) =
      (fun z => tiltNumerator (potentialMeasure V) (fun _ => 0) f z * H z) := by
    funext z
    change tiltAverage (potentialMeasure V) (fun x => inner ℝ z x) f = _
    rw [tiltAverage_eq_ratio]
    simp only [H, Z, tiltNumerator, tiltPartition, zero_add, one_mul, div_eq_mul_inv]
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (tiltNumerator (potentialMeasure V) (fun _ => 0) f) 0‖ *
        ‖iteratedFDeriv ℝ (d - i) H 0‖ := norm_iteratedFDeriv_mul_le hN hH 0 (by simp)
    _ ≤ ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (C i * ‖f‖) *
        ‖iteratedFDeriv ℝ (d - i) H 0‖ := by
      apply Finset.sum_le_sum
      intro i _
      gcongr
      exact hC i f
    _ = K * ‖f‖ := by
      dsimp [K]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem continuous_exponentialTiltCoordinateTaylor_L2 (d : ℕ) (a : Fin d → Fin n) :
    Continuous (fun f : Lp ℝ 2 (potentialMeasure V) => exponentialTiltCoordinateTaylor V f d a) := by
  have hsub (f g : Lp ℝ 2 (potentialMeasure V)) :
      exponentialTiltCoordinateTaylor V (f - g : Lp ℝ 2 (potentialMeasure V)) d a =
        exponentialTiltCoordinateTaylor V f d a - exponentialTiltCoordinateTaylor V g d a := by
    rw [exponentialTiltCoordinateTaylor_congr_ae (Lp.coeFn_sub _ _) d a]
    exact exponentialTiltCoordinateTaylor_sub hV hκ hlower (Lp.memLp f) (Lp.memLp g) d a
  let L : Lp ℝ 2 (potentialMeasure V) →ₗ[ℝ] ℝ :=
    { toFun := fun f => exponentialTiltCoordinateTaylor V f d a
      map_add' := fun f g => by
        have hs := hsub (f + g) g
        rw [add_sub_cancel_right] at hs
        linarith
      map_smul' := fun c f => by
        rw [exponentialTiltCoordinateTaylor_congr_ae (Lp.coeFn_smul c f) d a]
        exact exponentialTiltCoordinateTaylor_const_mul hV hκ hlower (Lp.memLp f) c d a }
  obtain ⟨C, _, hC⟩ := exists_tiltAverage_derivative_L2_bound hV hκ hlower d
  have hb (f : Lp ℝ 2 (potentialMeasure V)) : ‖L f‖ ≤ (C / d.factorial) * ‖f‖ := by
    let D := iteratedFDeriv ℝ d (fun z => ∫ x, f x ∂exponentialTilt (potentialMeasure V) z) 0
    have hd : ‖D (fun j => EuclideanSpace.single (a j) 1)‖ ≤ ‖D‖ := by
      simpa using D.le_opNorm (fun j => EuclideanSpace.single (a j) 1)
    change ‖D (fun j => EuclideanSpace.single (a j) 1) / (d.factorial : ℝ)‖ ≤ _
    rw [norm_div, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    calc
      _ ≤ (C * ‖f‖) / (d.factorial : ℝ) :=
        div_le_div_of_nonneg_right (hd.trans (hC f)) (Nat.cast_nonneg _)
      _ = _ := by ring
  exact (L.mkContinuous (C / d.factorial) hb).continuous

theorem continuous_exponentialTiltTaylor_square_sum_L2 (d : ℕ) :
    Continuous (fun f : Lp ℝ 2 (potentialMeasure V) =>
      ∑ a : Fin d → Fin n, exponentialTiltCoordinateTaylor V f d a ^ 2) :=
  continuous_finsetSum _ (fun a _ => (continuous_exponentialTiltCoordinateTaylor_L2 hV hκ hlower d a).pow 2)

end KLS
end
#print axioms KLS.continuous_exponentialTiltCoordinateTaylor_L2
#print axioms KLS.continuous_exponentialTiltTaylor_square_sum_L2
