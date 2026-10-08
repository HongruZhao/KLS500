import KLS.AdaptiveMaximalSmoothNoise

/-! The genuine smooth-observable Itô equation on each exhausting exit of
the assembled adaptive process, with an actual square-integrable martingale. -/
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped NNReal ENNReal BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS.TensorEnergy
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito KLS.LocalDiffusion KLSLevyProbe
variable {N d : ℕ}

theorem differentialGenerator_eq_observableGenerator
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (b : (Fin N → ℝ) → Fin N → ℝ) (σ : Fin d → (Fin N → ℝ) → Fin N → ℝ)
    (x : Fin N → ℝ) :
    differentialGenerator (b x) (fun k => σ k x) f x =
      observableGenerator b σ (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f)) x := by
  unfold differentialGenerator
  have hd (k : Fin d) : fderiv ℝ (fun y => fderiv ℝ f y (σ k x)) x (σ k x) =
      fderiv ℝ (fderiv ℝ f) x (σ k x) (σ k x) := by
    rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) x)
      (differentiableAt_const (σ k x))]
    simp
  simp_rw [hd]
  rw [apply_eq_sum_coordDeriv]
  simp_rw [apply₂_eq_sum_coordDeriv₂]
  unfold observableGenerator
  simp only [smul_eq_mul]
  have hFirst : (∑ a : Fin N, b x a * coordDeriv (fderiv ℝ f) a x) =
      ∑ a : Fin N, coordDeriv (fderiv ℝ f) a x * b x a :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hFirst]
  congr 1
  congr 1
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro k _
  ring

end KLS.TensorEnergy
namespace KLS.AdaptiveLocalization
open KLS.TensorEnergy
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito LevyStochCalc.Ito.Picard KLS.LocalDiffusion KLSLevyProbe
universe u
variable {n : ℕ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Space n)} [IsProbabilityMeasure μ]
  {W : MultidimBrownianMotion P n} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, IsBrownianFiltration (W.W k) ℱ}

private theorem martingale_finsetSum {ι : Type*} (s : Finset ι)
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

namespace MaximalProcess
variable (D : MaximalProcess μ W ℱ hW)
variable (f : (Fin (n+n*n) → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)

def smoothMartingale (j : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ a : Fin (n+n*n), ∑ k : Fin n, D.smoothNoiseIntegral f hf j a k t ω

theorem smoothMartingale_martingale (j : ℕ) : Martingale (D.smoothMartingale f hf j) ℱ P := by
  apply martingale_finsetSum
  intro a _
  apply martingale_finsetSum
  intro k _
  exact D.smoothNoiseIntegral_martingale f hf j a k

theorem smoothMartingale_zero (j : ℕ) : D.smoothMartingale f hf j 0 =ᵐ[P] 0 := by
  have hz : ∀ᵐ ω ∂P, ∀ a : Fin (n+n*n), ∀ k : Fin n, D.smoothNoiseIntegral f hf j a k 0 ω = 0 :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun k =>
      stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hW k) (D.smoothNoise f j a k)
        (D.smoothNoise_measurable f hf j a k) (D.smoothNoise_progressive f hf j a k)
        (D.smoothNoise_energy f hf j a k) le_rfl
  filter_upwards [hz] with ω hω
  simp only [smoothMartingale, hω, Finset.sum_const_zero, Pi.zero_apply]

/-- Exact actual smooth-observable equation before any of the genuine exits.
The finite sum of Brownian integrals is itself a proved martingale. -/
theorem smoothObservable_equation
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ A : Set Ω, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A)
    (j : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ) ≤ D.exit j ω →
      f (D.path T ω) - f 0 =
        (∫ t in Icc (0 : ℝ) T, differentialGenerator (coordinateDrift μ (D.path t ω))
          (fun k => coordinateDiffusion μ k (D.path t ω)) f (D.path t ω) ∂volume) +
          D.smoothMartingale f hf j T ω := by
  have hn : ∀ᵐ ω ∂P, ∀ a : Fin (n+n*n), ∀ k : Fin n,
      D.smoothNoiseIntegral f hf j a k T ω = (D j).smoothObservableNoiseIntegral f hf a k T ω :=
    ae_all_iff.mpr fun a => ae_all_iff.mpr fun k => D.smoothNoiseIntegral_eq_local f hf j a k hT
  filter_upwards [D.ae_path_eq_of_le_exit, (D j).itoFormula_original_smooth f hf hℱ0 hnull hT,
    (D j).initial_Y, hn] with ω hp he h0 hnoise hle
  have he' := he hle
  rw [h0, ← hp j T hT.le hle] at he'
  have hd : (∫ t in Icc (0 : ℝ) T, observableGenerator (coordinateDrift μ) (coordinateDiffusion μ)
      (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f)) ((D j).pair.Y t ω) ∂volume) =
      ∫ t in Icc (0 : ℝ) T, differentialGenerator (coordinateDrift μ (D.path t ω))
        (fun k => coordinateDiffusion μ k (D.path t ω)) f (D.path t ω) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [differentialGenerator_eq_observableGenerator f hf]
    rw [hp j t ht.1 ((show (t : WithTop ℝ) ≤ (T : WithTop ℝ) by exact_mod_cast ht.2).trans hle)]
  rw [hd] at he'
  have hs : (∑ a : Fin (n+n*n), ∑ k : Fin n, (D j).smoothObservableNoiseIntegral f hf a k T ω) =
      D.smoothMartingale f hf j T ω := by
    unfold smoothMartingale
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_congr rfl fun k _ => (hnoise a k).symm
  rw [hs] at he'
  exact he'

end MaximalProcess
end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.MaximalProcess.smoothMartingale_martingale
#print axioms KLS.AdaptiveLocalization.MaximalProcess.smoothObservable_equation
