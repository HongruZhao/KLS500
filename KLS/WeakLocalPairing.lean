import KLS.WeightedAnnihilatorEnergy

/-! # Actual L² Cauchy--Schwarz bounds for localized distributional derivatives -/

open MeasureTheory InnerProductSpace Set Filter
open scoped ContDiff ENNReal Topology

noncomputable section
namespace KLS
variable {n : ℕ}

theorem integral_mul_sq_le_L2 {f g : Space n → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ x, f x * g x) ^ 2 ≤ (∫ x, f x ^ 2) * (∫ x, g x ^ 2) := by
  have hp {a b : Space n → ℝ} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  have he := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  simpa only [hp, ← pow_two] using he

theorem weak_cutoff_test_pairing_sq_le {φ f χ ψ : Space n → ℝ}
    (hφ : Continuous φ) {i : Fin n} (G : Lp ℝ 2 (volume : Measure (Space n)))
    (hG : HasWeakCoordinateDerivative f i G)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hχ1 : ∀ x ∈ tsupport ψ, χ x = 1) :
    (∫ x, f x * coordinateDerivative ψ i x) ^ 2 ≤
      (∫ x, Real.exp (-φ x) * χ x ^ 2 * G x ^ 2) *
        (∫ x, Real.exp (φ x) * ψ x ^ 2) := by
  let A : Space n → ℝ := fun x => (Real.exp (-φ x / 2) * χ x) * G x
  let B : Space n → ℝ := fun x => Real.exp (φ x / 2) * ψ x
  have hA : MemLp A 2 volume :=
    (((Real.continuous_exp.comp (hφ.neg.div_const 2)).mul hχ).memLp_top_of_hasCompactSupport
      hχc.mul_left volume).mul (Lp.memLp G)
  have hB : MemLp B 2 volume :=
    ((Real.continuous_exp.comp (hφ.div_const 2)).mul hψ.continuous).memLp_of_hasCompactSupport hψc.mul_left
  have hAB : (∫ x, A x * B x) = ∫ x, G x * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [A, B]
      have he : Real.exp (-φ x / 2) * Real.exp (φ x / 2) = 1 := by
        rw [← Real.exp_add, show -φ x / 2 + φ x / 2 = 0 by ring, Real.exp_zero]
      by_cases hx : x ∈ tsupport ψ
      · rw [hχ1 x hx]
        calc
          Real.exp (-φ x / 2) * 1 * G x * (Real.exp (φ x / 2) * ψ x) =
              (Real.exp (-φ x / 2) * Real.exp (φ x / 2)) * (G x * ψ x) := by ring
          _ = _ := by rw [he, one_mul]
      · simp [image_eq_zero_of_notMem_tsupport hx]
  have hAsq : (∫ x, A x ^ 2) = ∫ x, Real.exp (-φ x) * χ x ^ 2 * G x ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [A]
      have he : Real.exp (-φ x / 2) * Real.exp (-φ x / 2) = Real.exp (-φ x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (Real.exp (-φ x / 2) * χ x * G x) ^ 2 =
            (Real.exp (-φ x / 2) * Real.exp (-φ x / 2)) * χ x ^ 2 * G x ^ 2 := by ring
        _ = _ := by rw [he]
  have hBsq : (∫ x, B x ^ 2) = ∫ x, Real.exp (φ x) * ψ x ^ 2 := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [B]
      have he : Real.exp (φ x / 2) * Real.exp (φ x / 2) = Real.exp (φ x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (Real.exp (φ x / 2) * ψ x) ^ 2 =
            (Real.exp (φ x / 2) * Real.exp (φ x / 2)) * ψ x ^ 2 := by ring
        _ = _ := by rw [he]
  rw [hG ψ hψ hψc, neg_sq]
  have he := integral_mul_sq_le_L2 hA hB
  rwa [hAB, hAsq, hBsq] at he

end KLS
end

#print axioms KLS.integral_mul_sq_le_L2
#print axioms KLS.weak_cutoff_test_pairing_sq_le
