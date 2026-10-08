import KLS.AdaptiveGlobalEnergyNoise

/-! Actual unstopped cumulant-energy Ito equation, obtained by the genuine
locality of the Brownian integral and the proved exhaustion of state exits. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
universe v
variable {n : ℕ} {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}

private theorem martingale_sum_energy {ι : Type*} (s : Finset ι)
    (M : ι → ℝ → Ω → ℝ) (hM : ∀ i ∈ s, Martingale (M i) ℱ P) :
    Martingale (fun t ω => ∑ i ∈ s, M i t ω) ℱ P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact martingale_zero ℱ P (E := ℝ)
  | @insert i s hi ih =>
    have h1 := hM i (Finset.mem_insert_self i s)
    have h2 := ih (fun j hj => hM j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    exact h1.add h2

theorem energyNoiseCoefficient_eq_coordinate_sum (r : ℕ) (u : Space n) (k : Fin n)
    (z : Fin (n+n*n) → ℝ) :
    energyNoiseCoefficient μ r u k z = ∑ a : Fin (n+n*n),
      coordDeriv (fderiv ℝ (cumulantEnergy μ r u)) a z * coordinateDiffusion μ k z a := by
  unfold energyNoiseCoefficient
  rw [apply_eq_sum_coordDeriv]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)
variable (hμ : IsCompact μ.support) (hadm : admissibleMeasure μ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (r : ℕ) (hr : 1 ≤ r) (u : Space n)

def globalEnergyMartingale (t : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin n, D.globalEnergyNoiseIntegral hμ hadm hℱ0 hnull r hr u k t ω

theorem globalEnergyMartingale_martingale :
    Martingale (D.globalEnergyMartingale hμ hadm hℱ0 hnull r hr u) ℱ P := by
  apply martingale_sum_energy
  intro k _
  exact D.globalEnergyNoiseIntegral_martingale hμ hadm hℱ0 hnull r hr u k

theorem integral_globalEnergyMartingale_eq_zero {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, D.globalEnergyMartingale hμ hadm hℱ0 hnull r hr u T ω ∂P) = 0 := by
  unfold globalEnergyMartingale
  rw [integral_finsetSum _ (fun k _ =>
    (D.globalEnergyNoiseIntegral_martingale hμ hadm hℱ0 hnull r hr u k).integrable T)]
  simp only [D.integral_globalEnergyNoiseIntegral_eq_zero hμ hadm hℱ0 hnull r hr u _ hT,
    Finset.sum_const_zero]

omit hμ hadm hℱ0 hnull hr in
theorem sum_smoothNoise_eq_stopped_energy (j : ℕ) (k : Fin n) :
    (fun ω t => ∑ a : Fin (n+n*n), D.smoothNoise (cumulantEnergy μ r u) j a k ω t) =
      Probability.stopped (D.exit j) (D.globalEnergyNoise r u k) := by
  funext ω t
  unfold smoothNoise globalEnergyNoise Probability.stopped
  by_cases ht : (t : WithTop ℝ) ≤ D.exit j ω
  · simp only [ht, ite_true, energyNoiseCoefficient_eq_coordinate_sum]
  · simp only [ht, ite_false, Finset.sum_const_zero]

theorem sum_smoothNoiseIntegral_eq_global (j : ℕ) (k : Fin n) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit j ω →
      (∑ a : Fin (n+n*n), D.smoothNoiseIntegral (cumulantEnergy μ r u)
        (contDiff_cumulantEnergy hμ hadm.isotropic.affineSpan_support_eq_top u) j a k T ω) =
      D.globalEnergyNoiseIntegral hμ hadm hℱ0 hnull r hr u k T ω := by
  let f := cumulantEnergy μ r u
  have hf := contDiff_cumulantEnergy (r := r) hμ hadm.isotropic.affineSpan_support_eq_top u
  obtain ⟨hm', hp', hq', he⟩ := exists_stochasticIntegralBrownian_finsetSum (W.W k) ℱ (hW k)
    (fun a : Fin (n+n*n) => D.smoothNoise f j a k)
    (fun a => D.smoothNoise_measurable f hf j a k)
    (fun a => D.smoothNoise_progressive f hf j a k)
    (fun a => D.smoothNoise_energy f hf j a k) Finset.univ hT
  have hm := D.globalEnergyNoise_measurable hμ hadm.isotropic.affineSpan_support_eq_top r u k
  have hp := D.globalEnergyNoise_progressive hμ hadm.isotropic.affineSpan_support_eq_top r u k
  have hq := D.globalEnergyNoise_energy hμ hadm hℱ0 hnull r hr u k
  have hms := Probability.measurable_uncurry_stopped (D.exit_isStoppingTime j) hm
  have hps := hp.stopped (D.exit_isStoppingTime j)
  have hqs := energy_lt_top_of_abs_le
    (fun ω t => Probability.abs_stopped_le (D.exit j) (D.globalEnergyNoise r u k) ω t) hq
  have hc := stochasticIntegralBrownian_congr_fun (W.W k) ℱ (hW k)
    (D.sum_smoothNoise_eq_stopped_energy r u j k) hm' hp' hq' hms hps hqs T
  have hs := stochasticIntegralBrownian_stopped_eq_of_le (D.exit j) (W.W k) ℱ (hW k)
    (D.exit_isStoppingTime j) hm hp hq hT
  rw [hc] at he
  filter_upwards [he, hs] with ω heω hsω hle
  exact heω.symm.trans (hsω hle)

theorem energyMartingale_eq_global (j : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit j ω →
      D.energyMartingale hμ hadm.isotropic.affineSpan_support_eq_top r u j T ω =
        D.globalEnergyMartingale hμ hadm hℱ0 hnull r hr u T ω := by
  have hn := ae_all_iff.mpr fun k : Fin n =>
    D.sum_smoothNoiseIntegral_eq_global hμ hadm hℱ0 hnull r hr u j k hT
  filter_upwards [hn] with ω hω hle
  unfold energyMartingale smoothMartingale globalEnergyMartingale
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => hω k hle

theorem energy_equation_global (hr2 : 2 ≤ r) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, D.energyPath r u T ω - cumulantEnergy μ r u 0 =
      (∫ t in Icc (0 : ℝ) T, cumulantEnergyDrift μ r u (D.path t ω) ∂volume) +
        D.globalEnergyMartingale hμ hadm hℱ0 hnull r hr u T ω := by
  have he := ae_all_iff.mpr fun j : ℕ =>
    D.energy_equation hμ hadm.isotropic.affineSpan_support_eq_top hℱ0 hnull r hr2 u j hT
  have hn := ae_all_iff.mpr fun j : ℕ =>
    D.energyMartingale_eq_global hμ hadm hℱ0 hnull r hr u j hT
  filter_upwards [he, hn, D.ae_lifetime_eq_top hμ hadm hℱ0 hnull] with ω heω hnω htop
  obtain ⟨j, hj⟩ := (D.lt_lifetime_iff ω T).mp (by rw [htop]; exact WithTop.coe_lt_top T)
  exact (heω j hj.le).trans (congrArg
    ((∫ t in Icc (0 : ℝ) T, cumulantEnergyDrift μ r u (D.path t ω) ∂volume) + ·) (hnω j hj.le))

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.energy_equation_global
#print axioms KLS.AdaptiveLocalization.MaximalProcess.globalEnergyMartingale_martingale
