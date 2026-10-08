import KLS.LocalWeakDerivativeUniqueness
import KLS.WeightedCutoffApproximation

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma compact_subset_nat_ball {K : Set (Space n)} (hK : IsCompact K) :
    ∃ N : ℕ, K ⊆ ball 0 ((N : ℝ) + 1) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space n)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  refine ⟨N, ?_⟩
  intro x hx
  have hb := hR hx
  simp only [mem_closedBall, mem_ball, dist_zero_right] at hb ⊢
  linarith

/-- Derivatives of the actual standard cutoff sequence define one raw
derivative on the whole space. Pairwise distribution uniqueness on open
balls proves consistency; its restriction to every compact set is L2. -/
theorem exists_local_weakCoordinateDerivative_of_cutoffs
    {f : Space n → ℝ} (i : Fin n)
    (hcut : ∀ k : ℕ, ∃ G : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => smoothCutoff n k x * f x) i G) :
    ∃ g : Space n → ℝ,
      (∀ K : Set (Space n), IsCompact K → MemLp g 2 (volume.restrict K)) ∧
      HasLocalWeakCoordinateDerivative f g i := by
  choose G hG using hcut
  have hpair (k l : ℕ) : ∀ᵐ x,
      x ∈ ball (0 : Space n) (min ((k : ℝ) + 1) ((l : ℝ) + 1)) → G k x = G l x := by
    apply ae_eq_weakCoordinateDerivative_of_eqOn (hG k) (hG l) isOpen_ball
    intro x hx
    have hx' : ‖x‖ < min ((k : ℝ) + 1) ((l : ℝ) + 1) := by simpa using hx
    have hk : ‖x‖ ≤ (k : ℝ) + 1 := (lt_of_lt_of_le hx' (min_le_left _ _)).le
    have hl : ‖x‖ ≤ (l : ℝ) + 1 := (lt_of_lt_of_le hx' (min_le_right _ _)).le
    dsimp only
    rw [smoothCutoff_eq_one_of_norm_le k hk, smoothCutoff_eq_one_of_norm_le l hl]
  let g : Space n → ℝ := fun x => G (Nat.ceil ‖x‖) x
  have heq (N : ℕ) : ∀ᵐ x, x ∈ ball (0 : Space n) ((N : ℝ) + 1) → g x = G N x := by
    filter_upwards [ae_all_iff.mpr (fun k => hpair k N)] with x hx hxN
    apply hx (Nat.ceil ‖x‖)
    simp only [mem_ball, dist_zero_right] at hxN ⊢
    apply lt_min
    · have hn := Nat.le_ceil ‖x‖
      linarith
    · exact hxN
  refine ⟨g, ?_, ?_⟩
  · intro K hK
    obtain ⟨N, hN⟩ := compact_subset_nat_ball hK
    have hae : (fun x => G N x) =ᵐ[volume.restrict K] g := by
      apply (ae_restrict_iff' hK.measurableSet).mpr
      filter_upwards [heq N] with x hx hxK
      exact (hx (hN hxK)).symm
    exact (memLp_congr_ae hae).mp ((Lp.memLp (G N)).restrict K)
  · intro ψ hψ hc
    obtain ⟨N, hN⟩ := compact_subset_nat_ball hc
    have hone : ∀ x ∈ tsupport ψ, smoothCutoff n N x = 1 := by
      intro x hx
      apply smoothCutoff_eq_one_of_norm_le
      have hb := hN hx
      exact (show ‖x‖ < (N : ℝ) + 1 by simpa using hb).le
    have hw := (hG N).integral_eq_of_cutoff_one hψ hc hone
    have hr : (∫ x, G N x * ψ x) = ∫ x, g x * ψ x := by
      apply integral_congr_ae
      filter_upwards [heq N] with x hx
      by_cases hs : x ∈ tsupport ψ
      · rw [hx (hN hs)]
      · rw [image_eq_zero_of_notMem_tsupport hs, mul_zero, mul_zero]
    rwa [hr] at hw

end KLS
end
