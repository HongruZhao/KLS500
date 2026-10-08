import KLS.DiffusionStopping
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Genuine global Lipschitz extensions of finite-dimensional local coefficients. -/
open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
namespace KLS.LocalDiffusion
open LevyStochCalc.Ito.Setting
variable {N d : ℕ}

def coefficients (b : (Fin N → ℝ) → Fin N → ℝ)
    (s : Fin d → (Fin N → ℝ) → Fin N → ℝ) : JumpDiffusionCoeffs N d Unit where
  μ := fun _ x => b x
  σ := fun _ x i k => s k x i
  γ := fun _ _ _ => 0

theorem coefficients_isRegular {b : (Fin N → ℝ) → Fin N → ℝ}
    {s : Fin d → (Fin N → ℝ) → Fin N → ℝ}
    (hb : Continuous b) (hs : ∀ k, Continuous (s k)) :
    (coefficients b s).IsRegular (0 : Measure Unit) := by
  refine ⟨hb.measurable.comp measurable_snd, ?_, measurable_const, ?_, ?_, ?_⟩
  · apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro k
    exact ((continuous_apply i).comp (hs k)).measurable.comp measurable_snd
  · intro T hT
    change (∫⁻ _t in Icc (0 : ℝ) T, (‖b 0‖₊ : ℝ≥0∞) ^ 2) < ⊤
    exact lintegral_const_lt_top (by finiteness)
  · intro T hT
    change (∫⁻ _t in Icc (0 : ℝ) T, ∑ i, ∑ k, (‖s k 0 i‖₊ : ℝ≥0∞) ^ 2) < ⊤
    apply lintegral_const_lt_top
    simp only [ENNReal.sum_ne_top, Finset.mem_univ, true_implies]
    intro i k
    finiteness
  · intro T hT
    simp [coefficients]

theorem coefficients_isLipschitz {b : (Fin N → ℝ) → Fin N → ℝ}
    {s : Fin d → (Fin N → ℝ) → Fin N → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hs : ∀ k, LipschitzWith K (s k)) :
    (coefficients b s).IsLipschitz (0 : Measure Unit)
      ((((N * d : ℕ) : ℝ) + 1) * K) := by
  have hM : (0 : ℝ) ≤ ((N * d : ℕ) : ℝ) := by positivity
  have hK : (0 : ℝ) ≤ K := K.2
  have hbase (x y : Fin N → ℝ) : ‖b x - b y‖ ≤ K * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hb.dist_le_mul x y
  have hentry (x y : Fin N → ℝ) (i : Fin N) (k : Fin d) :
      |s k x i - s k y i| ≤ K * ‖x - y‖ := by
    calc
      _ ≤ ‖s k x - s k y‖ := norm_le_pi_norm _ i
      _ ≤ _ := by simpa only [dist_eq_norm] using (hs k).dist_le_mul x y
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · intro t x y
    change ‖b x - b y‖ ≤ _
    refine (hbase x y).trans ?_
    gcongr
    nlinarith
  · intro t x y
    have hsum : (∑ i : Fin N, ∑ k : Fin d, (s k x i - s k y i) ^ 2) ≤
        ((N * d : ℕ) : ℝ) * (K * ‖x - y‖) ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin N, ∑ _k : Fin d, (K * ‖x - y‖) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro k _
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hentry x y i k)
        _ = _ := by simp [mul_assoc, Nat.cast_mul]
    change (∑ i : Fin N, ∑ k : Fin d, (s k x i - s k y i) ^ 2) ≤ _
    refine hsum.trans ?_
    have hm : ((N * d : ℕ) : ℝ) ≤ (((N * d : ℕ) : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg ((K : ℝ) * ‖x - y‖))]
  · intro t x y
    simp [coefficients]

/-- Each locally Lipschitz coefficient has an actual global Lipschitz extension
agreeing on the prescribed closed state ball. -/
theorem exists_extension_on_closedBall
    (b : (Fin N → ℝ) → Fin N → ℝ)
    (s : Fin d → (Fin N → ℝ) → Fin N → ℝ)
    (hb : LocallyLipschitz b) (hs : ∀ k, LocallyLipschitz (s k)) (R : ℝ) :
    ∃ C : JumpDiffusionCoeffs N d Unit,
      C.IsRegular (0 : Measure Unit) ∧
      (∃ L : ℝ, C.IsLipschitz (0 : Measure Unit) L) ∧
      (∀ t x, ‖x‖ ≤ R → C.μ t x = b x) ∧
      (∀ t x, ‖x‖ ≤ R → ∀ i k, C.σ t x i k = s k x i) ∧
      (∀ t x e, C.γ t x e = 0) := by
  obtain ⟨Kb, hKb⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Fin N → ℝ) R) hb.locallyLipschitzOn
  obtain ⟨B, hB, hBeq⟩ := hKb.extend_pi
  have hS (k : Fin d) : ∃ K : ℝ≥0, ∃ S : (Fin N → ℝ) → Fin N → ℝ,
      LipschitzWith K S ∧ EqOn (s k) S (closedBall 0 R) := by
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall (0 : Fin N → ℝ) R) (hs k).locallyLipschitzOn
    obtain ⟨S, hS, heq⟩ := hK.extend_pi
    exact ⟨K, S, hS, heq⟩
  choose Ks S hS hSeq using hS
  let K : ℝ≥0 := Kb + ∑ k, Ks k
  have hBK : LipschitzWith K B := hB.weaken (by simp [K])
  have hSK (k : Fin d) : LipschitzWith K (S k) := (hS k).weaken (by
    exact (Finset.single_le_sum (fun j _ => show (0 : ℝ≥0) ≤ Ks j from bot_le)
      (Finset.mem_univ k)).trans (le_add_of_nonneg_left (show (0 : ℝ≥0) ≤ Kb from bot_le)))
  refine ⟨coefficients B S, coefficients_isRegular hB.continuous (fun k => (hS k).continuous),
    ⟨_, coefficients_isLipschitz hBK hSK⟩, ?_, ?_, by simp [coefficients]⟩
  · intro t x hx
    exact (hBeq (by simpa only [mem_closedBall, dist_zero_right] using hx)).symm
  · intro t x hx i k
    exact congrFun (hSeq k (by simpa only [mem_closedBall, dist_zero_right] using hx)).symm i

end KLS.LocalDiffusion
end
#print axioms KLS.LocalDiffusion.exists_extension_on_closedBall
