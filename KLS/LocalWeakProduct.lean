import KLS.WeakSobolevProduct
import KLS.LocalWeakDerivativeCutoff
import KLS.LocalWeakDerivativeGluing

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma coordinateDerivative_smoothCutoff_eq_zero_of_norm_lt
    (k : ℕ) (i : Fin n) {x : Space n} (hx : ‖x‖ < (k : ℝ) + 1) :
    coordinateDerivative (smoothCutoff n k) i x = 0 := by
  have he : smoothCutoff n k =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact smoothCutoff_eq_one_of_norm_le k hy.le
  simp only [coordinateDerivative, he.fderiv_eq, fderiv_const_apply, zero_apply]

/-- The actual product rule for raw local L2 weak derivatives. All four
functions are square integrable on every compact set; no classical
differentiability of either factor is assumed. -/
theorem HasLocalWeakCoordinateDerivative.mul
    {f g F G : Space n → ℝ} {i : Fin n}
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hG : HasLocalWeakCoordinateDerivative g G i)
    (hf : ∀ K : Set (Space n), IsCompact K → MemLp f 2 (volume.restrict K))
    (hg : ∀ K : Set (Space n), IsCompact K → MemLp g 2 (volume.restrict K))
    (hFloc : ∀ K : Set (Space n), IsCompact K → MemLp F 2 (volume.restrict K))
    (hGloc : ∀ K : Set (Space n), IsCompact K → MemLp G 2 (volume.restrict K)) :
    HasLocalWeakCoordinateDerivative (fun x => f x * g x)
      (fun x => F x * g x + f x * G x) i := by
  intro ψ hψ hc
  obtain ⟨N, hN⟩ := compact_subset_nat_ball hc
  let χ := smoothCutoff n N
  have hχ : ContDiff ℝ 1 χ := smoothCutoff_contDiff N
  have hχc : HasCompactSupport χ := smoothCutoff_hasCompactSupport N
  have hone (x : Space n) (hx : x ∈ tsupport ψ) : χ x = 1 :=
    smoothCutoff_eq_one_of_norm_le N (show ‖x‖ ≤ (N : ℝ) + 1 from
      (show ‖x‖ < (N : ℝ) + 1 by simpa using hN hx).le)
  have hzero (x : Space n) (hx : x ∈ tsupport ψ) : coordinateDerivative χ i x = 0 :=
    coordinateDerivative_smoothCutoff_eq_zero_of_norm_lt N i
      (show ‖x‖ < (N : ℝ) + 1 by simpa using hN hx)
  obtain ⟨Fχ, hFχ, hFχe⟩ := hF.compact_mul hf hFloc hχ hχc
  obtain ⟨Gχ, hGχ, hGχe⟩ := hG.compact_mul hg hGloc hχ hχc
  have hcf := memLp_compact_mul_of_local hχ.continuous hχc hf
  have hcg := memLp_compact_mul_of_local hχ.continuous hχc hg
  have hw := integral_product_coordinateDerivative_of_weak hcf hcg hFχ hGχ hψ hc
  have hl : (∫ x, (χ x * f x) * (χ x * g x) * coordinateDerivative ψ i x) =
      ∫ x, f x * g x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hs : x ∈ tsupport ψ
      · rw [hone x hs]
        ring
      · have hd : coordinateDerivative ψ i x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun ht => hs (tsupport_coordinateDerivative_subset ψ i ht))
        rw [hd, mul_zero, mul_zero]
  have hr : (∫ x, (Fχ x * (χ x * g x) + (χ x * f x) * Gχ x) * ψ x) =
      ∫ x, (F x * g x + f x * G x) * ψ x := by
    apply integral_congr_ae
    filter_upwards [hFχe, hGχe] with x hx hy
    by_cases hs : x ∈ tsupport ψ
    · rw [hx, hy, hone x hs, hzero x hs]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, mul_zero]
  rwa [hl, hr] at hw

end KLS
end
