import SpectralReductionRetainedDefect

/-! Stop when the energy minus the retained diffusion allowance is small.
This retains the actual finite defect budget as a scalar in [0,1] and
charges that budget to additional mean loss at the same stopping index. -/
open MeasureTheory InnerProductSpace Matrix Filter
open scoped ContDiff RealInnerProductSpace ENNReal Topology BigOperators
noncomputable section
namespace KLS.ConstantReduction
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {φ : Space n → ℝ} {κ : ℝ}
  [IsProbabilityMeasure (potentialMeasure φ)]
  (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hκ : 0 < κ)
  (hlower : ∀ x (a : Fin n → ℝ), κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ x *ᵥ a))

theorem weightedIteration_exists_coupled_defect_index
    {ι : Type*} [Fintype ι] (U : WeightedH1Family φ ι)
    (F : (k : ℕ) → WeightedIterationIndex n ι k → Space n → ℝ)
    (W : (k : ℕ) → WeightedH1Family φ (Fin n × WeightedIterationIndex n ι k))
    (hF : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (F k i))
    (hV : ∀ k i, F k i =ᵐ[volume] (weightedH1Value φ
      (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k i) : Space n → ℝ))
    (hL : ∀ k i, MemLp (weightedDiffusion φ (F k i)) 2 (potentialMeasure φ))
    {lam M δ : ℝ} (hlam : 0 < lam) (hM : 1 < M) (hδ : 0 < δ) (hδM : δ < 1-1/M)
    (hE0 : weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U 0 = lam)
    (hD0 : weightedIterationDiffusionEnergy φ F 0 = lam^2)
    (hB : ∀ m : ℕ, weightedIterationDiffusionEnergy φ F m +
      (∑ k ∈ Finset.range m, weightedIterationDefect hφ hκ hlower U W k) +
      κ * (∑ k ∈ Finset.range m, weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U k) ≤
        weightedIterationDiffusionEnergy φ F 0) :
    ∃ (N : ℕ) (ρ : ℝ), 0 < N ∧ 0 ≤ ρ ∧ ρ ≤ 1 ∧
      (∀ k, k+1<N → (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k))^2 ≤ M*lam) ∧
      (∑ k ∈ Finset.range (N-1), weightedIterationDefect hφ hκ hlower U W k) = ρ*lam^2 ∧
      (1-1/M-δ+ρ/M)*lam < ∑ k ∈ Finset.range N,
        weightedIterationMeanLoss (hφ.of_le (by simp)) hκ hlower U k := by
  let E := weightedIterationEnergy (hφ.of_le (by simp)) hκ hlower U
  let D := weightedIterationDiffusionEnergy φ F
  let Q : ℕ → ℝ := fun k => E k-D k/(M*lam)
  have hM0 : 0 < M := by linarith
  have hden : 0 < M*lam := mul_pos hM0 hlam
  have ht : Tendsto E atTop (𝓝 0) :=
    weightedIterationEnergy_tendsto_zero hφ hκ hlower U (F 0) (hF 0) (hV 0) (hL 0)
  have hEsmall : ∃ k, E k < δ*lam :=
    (ht.eventually (eventually_lt_nhds (mul_pos hδ hlam))).exists
  have hex : ∃ k, Q k < δ*lam := by
    obtain ⟨k,hk⟩ := hEsmall
    refine ⟨k,lt_of_le_of_lt ?_ hk⟩
    dsimp [Q]
    exact sub_le_self _ (div_nonneg (weightedIterationDiffusionEnergy_nonneg φ F k) hden.le)
  let N := Nat.find hex
  have hNQ : Q N < δ*lam := Nat.find_spec hex
  have hbefore (k : ℕ) (hk : k<N) : δ*lam ≤ Q k :=
    le_of_not_gt (Nat.find_min hex hk)
  have hQzero : Q 0 = (1-1/M)*lam := by
    dsimp [Q,E,D]
    rw [hE0,hD0]
    field_simp
  have hN : 0 < N := by
    by_contra hn
    have hz : N=0 := by omega
    rw [hz,hQzero] at hNQ
    have hh := mul_lt_mul_of_pos_right hδM hlam
    linarith
  have hscale (k : ℕ) (hk : k+1<N) :
      (weightedSuccessorScale (hφ.of_le (by simp)) hκ hlower
        (weightedSuccessorIterate (hφ.of_le (by simp)) hκ hlower U k))^2 ≤ M*lam := by
    have hbk := hbefore (k+1) hk
    have hDn : 0 ≤ D (k+1) := weightedIterationDiffusionEnergy_nonneg φ F (k+1)
    have hquot : 0 ≤ D (k+1)/(M*lam) := div_nonneg hDn hden.le
    have hEl : 0 < E (k+1) := by
      dsimp [Q] at hbk
      have hp := mul_pos hδ hlam
      linarith
    have hratio : D (k+1)/(M*lam) ≤ E (k+1) := by
      dsimp [Q] at hbk
      have hp := mul_pos hδ hlam
      linarith
    have hDe := (div_le_iff₀ hden).mp hratio
    have hEq := weightedIterationDiffusionEnergy_eq_scale_sq_mul hφ hκ hlower U F hF hV k
    change D (k+1) = _ * E (k+1) at hEq
    rw [hEq] at hDe
    exact le_of_mul_le_mul_right (by simpa only [mul_comm (E (k+1))] using hDe) hEl
  let c : ℝ := ∑ k ∈ Finset.range (N-1), weightedIterationDefect hφ hκ hlower U W k
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun k _ => weightedIterationDefect_nonneg hφ hκ hlower U W k
  have hκE : 0 ≤ κ * (∑ k ∈ Finset.range (N-1), E k) :=
    mul_nonneg hκ.le (Finset.sum_nonneg fun k _ =>
      weightedIterationEnergy_nonneg (hφ.of_le (by simp)) hκ hlower U k)
  have hbudget := hB (N-1)
  rw [hD0] at hbudget
  change D (N-1)+c+κ*(∑ k ∈ Finset.range (N-1), E k) ≤ lam^2 at hbudget
  have hDprefix : 0 ≤ D (N-1) := weightedIterationDiffusionEnergy_nonneg φ F _
  have hcupper : c ≤ lam^2 := by linarith
  have hDmono : D N ≤ D (N-1) :=
    weightedIterationDiffusionEnergy_antitone hφ hκ hlower U F hF hV hL (by omega)
  have hDc : D N+c ≤ lam^2 := by linarith
  let ρ : ℝ := c/lam^2
  have hρ0 : 0 ≤ ρ := div_nonneg hc0 (sq_nonneg _)
  have hρ1 : ρ ≤ 1 := (div_le_one (sq_pos_of_pos hlam)).mpr hcupper
  have hc : c=ρ*lam^2 := by dsimp [ρ]; field_simp
  refine ⟨N,ρ,hN,hρ0,hρ1,hscale,hc,?_⟩
  have htel := weightedIterationEnergy_telescope (hφ.of_le (by simp)) hκ hlower U N
  have he : ‖weightedFamilyGradient φ ι U‖^2=lam := hE0
  rw [he] at htel
  change lam=E N+_ at htel
  have htelmul := congrArg (fun t : ℝ => t*(M*lam)) htel
  have hQmul := mul_lt_mul_of_pos_right hNQ hden
  dsimp [Q] at hQmul
  rw [sub_mul,div_mul_cancel₀ _ (ne_of_gt hden)] at hQmul
  apply (mul_lt_mul_iff_left₀ hden).mp
  have hid : ((1-1/M-δ+ρ/M)*lam)*(M*lam)=(M-1-δ*M)*lam^2+c := by
    rw [hc]
    field_simp
  rw [hid]
  nlinarith

/-- The two endpoint checks imply every intermediate defect budget check
when the chosen finite recurrence bounds are affine in that budget. -/
theorem coupled_defect_affine_upper {M δ a b ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hzero : a ≤ 1-1/M-δ) (hone : a+b ≤ 1-δ) :
    a+b*ρ ≤ 1-1/M-δ+ρ/M := by
  have hz := mul_le_mul_of_nonneg_right hzero (show 0 ≤ 1-ρ by linarith)
  have ho := mul_le_mul_of_nonneg_right hone hρ0
  simp only [div_eq_mul_inv] at hz ho ⊢
  nlinarith

end KLS.ConstantReduction
end

#print axioms KLS.ConstantReduction.weightedIteration_exists_coupled_defect_index
#print axioms KLS.ConstantReduction.coupled_defect_affine_upper
