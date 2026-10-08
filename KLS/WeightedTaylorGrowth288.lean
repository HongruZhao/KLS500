import KLS.UniversalCumulantGrowth
import KLS.FullL2CumulantTaylor

/-! The actual full-L2 suspension transfer with the explicit sufficient
Taylor radius sqrt(288), conditional on the displayed localization inputs. -/
open MeasureTheory Set Matrix
open scoped BigOperators
noncomputable section
namespace KLS
open AdaptiveLocalization

theorem one_le_sqrt288 : (1 : ℝ) ≤ Real.sqrt 288 := by
  exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)

theorem cumulantEnergyMajorant_Taylor_size {d : ℕ} (hd : 1 ≤ d) :
    2 * cumulantEnergyMajorant 144 d / (d.factorial : ℝ)^2 ≤
      (Real.sqrt 288) ^ (2*d) := by
  have hfac : (d.factorial : ℝ)^2 ≠ 0 := by positivity
  have hs : (Real.sqrt 288)^2 = (288 : ℝ) := Real.sq_sqrt (by norm_num)
  have hpow : (2 : ℝ) ≤ 2^d := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    have hj : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
    rw [pow_succ]
    linarith
  rw [cumulantEnergyMajorant]
  have hc : 2 * (144^d * (d.factorial : ℝ)^2) / (d.factorial : ℝ)^2 = 2 * 144^d := by
    field_simp
  rw [hc, pow_mul, hs]
  calc
    (2 : ℝ) * 144^d ≤ 2^d * 144^d := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 288^d := by rw [← mul_pow]; norm_num

theorem weightedCoordinateTaylorBound_sqrt288_of_seed_and_base
    (hseed : ∀ n, UniformCompactMatrixSeed n)
    (hbase : ∀ n, CompactProcessEnergyBound n 1 (cumulantEnergyMajorant 144 1))
    {n : ℕ} {V : Space n → ℝ} [IsProbabilityMeasure (potentialMeasure V)]
    (hV : ContDiff ℝ 2 V) (hμ : IsIsotropic (potentialMeasure V)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian V x *ᵥ a)) :
    WeightedCoordinateTaylorBound V (Real.sqrt 288) := by
  exact weightedCoordinateTaylorBound_of_universalCumulant hV hμ hκ hlower
    (cumulantEnergyMajorant 144)
    (fun d _ => (cumulantEnergyMajorant_pos (by norm_num : (0 : ℝ) < 144) d).le)
    (fun _ hd => cumulantEnergyMajorant_Taylor_size hd)
    (fun _ hd => universalDirectionalCumulantBound_of_seed_and_base hseed hbase hd)

end KLS
end
