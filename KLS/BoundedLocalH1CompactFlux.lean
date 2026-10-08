import KLS.LocalC11FirstFactor

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- A genuine compactly supported flux equation can be tested against a
 bounded local H1 function without a compact-support premise on that function.
 A smooth localization is removed using the actual supports of the flux. -/
theorem integral_divergence_of_bounded_local_H1_test_compact_flux
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ}
    {F : Fin n → Space n → ℝ}
    (hA : ∀ i, ∀ S : Set (Space n), IsCompact S → MemLp (A i) 2 (volume.restrict S))
    (hb : LocallyIntegrable b volume)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x*coordinateDerivative ψ i x) = ∫ x, b x*ψ x)
    {K : Set (Space n)} (hK : IsCompact K)
    (hAzero : ∀ i x, x ∉ K → A i x = 0) (hbzero : ∀ x, x ∉ K → b x = 0)
    (hf : ∀ S : Set (Space n), IsCompact S → MemLp f 2 (volume.restrict S))
    {C : ℝ} (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ C)
    (hFloc : ∀ i, ∀ S : Set (Space n), IsCompact S → MemLp (F i) 2 (volume.restrict S))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x*F i x)) ∧
      Integrable (fun x => b x*f x) ∧
      (∑ i, ∫ x, A i x*F i x) = ∫ x, b x*f x := by
  obtain ⟨N,hN⟩ := compact_subset_nat_ball hK
  let χ := smoothCutoff n N
  have hχ : ContDiff ℝ 1 χ := smoothCutoff_contDiff N
  have hχc : HasCompactSupport χ := smoothCutoff_hasCompactSupport N
  have hone (x : Space n) (hx : x ∈ K) : χ x = 1 :=
    smoothCutoff_eq_one_of_norm_le N (show ‖x‖ ≤ (N : ℝ)+1 from
      (show ‖x‖ < (N : ℝ)+1 by simpa using hN hx).le)
  have hzero (i : Fin n) (x : Space n) (hx : x ∈ K) : coordinateDerivative χ i x = 0 :=
    coordinateDerivative_smoothCutoff_eq_zero_of_norm_lt N i
      (show ‖x‖ < (N : ℝ)+1 by simpa using hN hx)
  have hex (i : Fin n) := (hF i).compact_mul hf (hFloc i) hχ hχc
  choose W hW hWe using hex
  have hfχ : ∀ S : Set (Space n), IsCompact S →
      MemLp (fun x => χ x*f x) 2 (volume.restrict S) :=
    fun S hS => memLp_continuous_mul_on_compact hS (hf S hS) hχ.continuous
  have hbc : ∀ᵐ x ∂volume, ‖χ x*f x‖ ≤ C := by
    filter_upwards [hbound] with x hx
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (show ‖χ x‖ ≤ 1 by rw [Real.norm_eq_abs, abs_of_nonneg (smoothCutoff_nonneg_le_one N x).1]; exact (smoothCutoff_nonneg_le_one N x).2)).trans hx
  obtain ⟨hAi,hbi,heq⟩ := integral_divergence_of_bounded_compact_H1_test
    hA hb hdiv hfχ hχc.mul_right hbc
    (fun i _ _ => (Lp.memLp (W i)).mono_measure Measure.restrict_le_self) hW
  have heA (i : Fin n) : (fun x => A i x*W i x) =ᵐ[volume] (fun x => A i x*F i x) := by
    filter_upwards [hWe i] with x hx
    by_cases h : x ∈ K
    · rw [hx,hone x h,hzero i x h,one_mul,zero_mul,add_zero]
    · rw [hAzero i x h,zero_mul,zero_mul]
  have heb : (fun x => b x*(χ x*f x)) = fun x => b x*f x := by
    funext x
    by_cases h : x ∈ K
    · rw [hone x h,one_mul]
    · rw [hbzero x h,zero_mul,zero_mul]
  refine ⟨fun i => (hAi i).congr (heA i),by simpa only [heb] using hbi,?_⟩
  simp_rw [integral_congr_ae (heA _),heb] at heq
  exact heq

end KLS
end
