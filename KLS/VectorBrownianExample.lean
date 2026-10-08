import LevyStochCalc.Brownian.MultidimFiltered
import LevyStochCalc.Brownian.VectorItoVersionExists
import LevyStochCalc.Brownian.ItoIncrement
import LevyStochCalc.Brownian.ItoZero
import Mathlib.Probability.Distributions.Gaussian.Real

set_option maxHeartbeats 2000000

/-!
Selective-import consumer for the pinned LevyStochCalc source replay.
This consumer imports only the selected dependency closure.
The final existence theorem supplies an actual two-coordinate driver with one usual
filtration, independent nondegenerate Gaussian increments, and a continuous identity-
diffusion version. The separate `identityVersion_ae_eq` lemma identifies that version
with the Brownian coordinates at every fixed nonnegative time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace KLSLevyProbe

open LevyStochCalc
open LevyStochCalc.Brownian
open LevyStochCalc.Brownian.Multidim
open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable def usualFiltration {d : ℕ} (W : MultidimBrownianMotion P d) :
    Filtration ℝ ‹MeasurableSpace Ω› :=
  augFiltration W.naturalFiltration.rightCont P

theorem usualFiltration_brownian {d : ℕ} (W : MultidimBrownianMotion P d) (k : Fin d) :
    IsBrownianFiltration (W.W k) (usualFiltration W) :=
  isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural k).rightCont

instance usualFiltration_rightContinuous {d : ℕ} (W : MultidimBrownianMotion P d) :
    (usualFiltration W).IsRightContinuous :=
  isRightContinuous_augFiltration W.naturalFiltration P

theorem usualFiltration_beforeZero {d : ℕ} (W : MultidimBrownianMotion P d)
    (t : ℝ) (ht : t ≤ 0) : usualFiltration W 0 ≤ usualFiltration W t :=
  le_of_eq (augFiltration_of_nonpos W.naturalFiltration.rightCont P ht).symm

theorem usualFiltration_null {d : ℕ} (W : MultidimBrownianMotion P d)
    (s : Set Ω) (hs : MeasurableSet s) (h0 : P s = 0) :
    MeasurableSet[usualFiltration W 0] s :=
  measurableSet_augFiltration_of_null W.naturalFiltration.rightCont P hs h0

def unitIncrement (W : MultidimBrownianMotion P 2) (i : Fin 2) : Ω → ℝ :=
  fun ω => (W.W i).W 1 ω - (W.W i).W 0 ω

theorem unitIncrement_law (W : MultidimBrownianMotion P 2) (i : Fin 2) :
    P.map (unitIncrement W i) = gaussianReal 0 1 := by
  refine ((W.W i).increment_gaussian (s := 0) (t := 1) le_rfl zero_lt_one).trans ?_
  congr 1
  exact Subtype.ext (by norm_num)

theorem unitIncrement_variance (W : MultidimBrownianMotion P 2) (i : Fin 2) :
    Var[unitIncrement W i; P] = 1 := by
  rw [← variance_id_map (X := unitIncrement W i)
    (((W.W i).measurable_eval 1).sub ((W.W i).measurable_eval 0)).aemeasurable,
    unitIncrement_law W i, variance_id_gaussianReal]
  simp

theorem unitIncrement_nonconstant (W : MultidimBrownianMotion P 2)
    (i : Fin 2) (c : ℝ) : ¬ unitIncrement W i =ᵐ[P] fun _ => c := by
  intro h
  haveI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) one_ne_zero
  have hmap : P.map (unitIncrement W i) = P.map (fun _ : Ω => c) := Measure.map_congr h
  rw [unitIncrement_law W i, Measure.map_const] at hmap
  have h0 : gaussianReal 0 1 {c} = 0 := measure_singleton c
  rw [hmap] at h0
  simp at h0

theorem unitIncrement_independent (W : MultidimBrownianMotion P 2) :
    IndepFun (unitIncrement W 1) (unitIncrement W 0) P := by
  have hset : {i : Fin 2 | i ≠ 0} = {1} := by
    ext i
    fin_cases i <;> simp
  have hind := indep_iSup_sigmaBrownian_ne W 0
  rw [hset, iSup_singleton] at hind
  exact (IndepFun_iff_Indep _ _ _).mpr
    (indep_of_indep_of_le hind
      (comap_increment_le_sigmaBrownian (W.W 1) 0 1)
      (comap_increment_le_sigmaBrownian (W.W 0) 0 1))

def identityDiffusion (p k : Fin 2) (_ω : Ω) (_s : ℝ) : ℝ :=
  if p = k then 1 else 0

theorem identityDiffusion_meas (p k : Fin 2) :
    Measurable (Function.uncurry (identityDiffusion (Ω := Ω) p k)) :=
  measurable_const

theorem identityDiffusion_prog (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (p k : Fin 2) :
    Probability.ProgressivelyMeasurable ℱ (identityDiffusion (Ω := Ω) p k) :=
  Probability.progressivelyMeasurable_const ℱ (if p = k then 1 else 0)

theorem identityDiffusion_energy (p k : Fin 2) (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖identityDiffusion p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  by_cases hpk : p = k
  · simp [identityDiffusion, hpk, Real.volume_Icc]
  · simp [identityDiffusion, hpk]

theorem identityDiffusion_bound (p k : Fin 2) (ω : Ω) (s : ℝ) :
    |identityDiffusion p k ω s| ≤ 1 := by
  by_cases hpk : p = k <;> simp [identityDiffusion, hpk]

abbrev IdentityVersion (W : MultidimBrownianMotion P 2) (X : ℝ → Ω → Fin 2 → ℝ) : Prop :=
  IsVectorItoVersion W (usualFiltration W) (usualFiltration_brownian W)
    identityDiffusion identityDiffusion_meas (identityDiffusion_prog (usualFiltration W))
    identityDiffusion_energy (fun _ _ => 0) (fun _ _ _ => 0) X

theorem exists_identityVersion (W : MultidimBrownianMotion P 2) :
    ∃ X : ℝ → Ω → Fin 2 → ℝ, IdentityVersion W X := by
  exact exists_isVectorItoVersion_aug W W.naturalFiltration.rightCont
    (fun k => (W.isBrownianFiltration_natural k).rightCont)
    identityDiffusion identityDiffusion_meas zero_le_one identityDiffusion_bound
    (identityDiffusion_prog (usualFiltration W)) identityDiffusion_energy
    (fun _ => measurable_const) (fun _ _ _ => 0)
    (fun _ => measurable_const)
    (fun _ => Probability.progressivelyMeasurable_const (usualFiltration W) 0)
    (B := 0) le_rfl (fun _ _ _ => by simp)

theorem identityEntryIntegral_ae_eq (W : MultidimBrownianMotion P 2)
    (p k : Fin 2) {t : ℝ} (ht : 0 ≤ t) :
    coordItoIntegral W (usualFiltration W) (usualFiltration_brownian W)
      identityDiffusion identityDiffusion_meas (identityDiffusion_prog (usualFiltration W))
      identityDiffusion_energy p k t =ᵐ[P]
      fun ω => if p = k then (W.W k).W t ω else 0 := by
  by_cases hpk : p = k
  · have hEq : identityDiffusion (Ω := Ω) p k = fun _ _ => (1 : ℝ) := by
      funext ω s
      simp [identityDiffusion, hpk]
    have hq : ∀ T, 0 < T → ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
        (‖(1 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      fun T _ => by simp [Real.volume_Icc]
    have hI := stochasticIntegralBrownian_congr_fun (W.W k) (usualFiltration W)
      (usualFiltration_brownian W k) hEq (identityDiffusion_meas p k)
      (identityDiffusion_prog (usualFiltration W) p k) (identityDiffusion_energy p k)
      measurable_const (Probability.progressivelyMeasurable_const (usualFiltration W) 1) hq t
    change stochasticIntegralBrownian (W.W k) (usualFiltration W)
      (usualFiltration_brownian W k) (identityDiffusion p k) (identityDiffusion_meas p k)
      (identityDiffusion_prog (usualFiltration W) p k) (identityDiffusion_energy p k) t =ᵐ[P] _
    rw [hI]
    simpa only [if_pos hpk] using stochasticIntegralBrownian_one (W.W k)
      (usualFiltration W) (usualFiltration_brownian W k) measurable_const
      (Probability.progressivelyMeasurable_const (usualFiltration W) 1) hq ht
  · have hEq : identityDiffusion (Ω := Ω) p k = fun _ _ => (0 : ℝ) := by
      funext ω s
      simp [identityDiffusion, hpk]
    have hq : ∀ T, 0 < T → ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T _ => by simp
    have hI := stochasticIntegralBrownian_congr_fun (W.W k) (usualFiltration W)
      (usualFiltration_brownian W k) hEq (identityDiffusion_meas p k)
      (identityDiffusion_prog (usualFiltration W) p k) (identityDiffusion_energy p k)
      measurable_const (Probability.progressivelyMeasurable_const (usualFiltration W) 0) hq t
    change stochasticIntegralBrownian (W.W k) (usualFiltration W)
      (usualFiltration_brownian W k) (identityDiffusion p k) (identityDiffusion_meas p k)
      (identityDiffusion_prog (usualFiltration W) p k) (identityDiffusion_energy p k) t =ᵐ[P] _
    rw [hI]
    simpa only [if_neg hpk, Pi.zero_def] using stochasticIntegralBrownian_ae_zero (W.W k)
      (usualFiltration W) (usualFiltration_brownian W k) measurable_const
      (Probability.progressivelyMeasurable_const (usualFiltration W) 0) hq t

theorem identityVersion_ae_eq (W : MultidimBrownianMotion P 2)
    {X : ℝ → Ω → Fin 2 → ℝ} (hX : IdentityVersion W X) {t : ℝ} (ht : 0 ≤ t) :
    X t =ᵐ[P] fun ω p => (W.W p).W t ω := by
  have hentries : ∀ᵐ ω ∂P, ∀ (p k : Fin 2),
      coordItoIntegral W (usualFiltration W) (usualFiltration_brownian W)
        identityDiffusion identityDiffusion_meas (identityDiffusion_prog (usualFiltration W))
        identityDiffusion_energy p k t ω = if p = k then (W.W k).W t ω else 0 :=
    ae_all_iff.mpr fun p => ae_all_iff.mpr fun k => identityEntryIntegral_ae_eq W p k ht
  filter_upwards [hX.ae_eq t ht, hentries] with ω hω hentriesω
  funext p
  rw [hω]
  simp [vectorItoProcess, vectorItoMartingale, hentriesω]

theorem identityVersion_unit_law (W : MultidimBrownianMotion P 2)
    {X : ℝ → Ω → Fin 2 → ℝ} (hX : IdentityVersion W X) (i : Fin 2) :
    P.map (fun ω => X 1 ω i) = gaussianReal 0 1 := by
  have hae : (fun ω => X 1 ω i) =ᵐ[P] unitIncrement W i := by
    filter_upwards [identityVersion_ae_eq W hX (t := 1) zero_le_one,
      (W.W i).initial_zero] with ω hω h0
    simp [hω, unitIncrement, h0]
  exact (Measure.map_congr hae).trans (unitIncrement_law W i)

/-- A nonzero genuinely two-coordinate model, with all existence premises discharged. -/
theorem exists_two_coordinate_model :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : MultidimBrownianMotion P 2) (X : ℝ → Ω → Fin 2 → ℝ),
      (∀ k, IsBrownianFiltration (W.W k) (usualFiltration W)) ∧
      (usualFiltration W).IsRightContinuous ∧
      IdentityVersion W X ∧
      IndepFun (unitIncrement W 1) (unitIncrement W 0) P ∧
      (∀ i, P.map (unitIncrement W i) = gaussianReal 0 1) ∧
      (∀ i, Var[unitIncrement W i; P] = 1) ∧
      (∀ i c, ¬ unitIncrement W i =ᵐ[P] fun _ => c) ∧
      (∀ i, P.map (fun ω => X 1 ω i) = gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, _, ⟨W⟩⟩ := MultidimBrownianMotion.exists.{0} 2
  obtain ⟨X, hX⟩ := exists_identityVersion W
  exact ⟨Ω, inferInstance, P, inferInstance, W, X, usualFiltration_brownian W,
    inferInstance, hX, unitIncrement_independent W, unitIncrement_law W,
    unitIncrement_variance W, unitIncrement_nonconstant W, identityVersion_unit_law W hX⟩

#print axioms usualFiltration_brownian
#print axioms exists_identityVersion
#print axioms identityVersion_ae_eq
#print axioms exists_two_coordinate_model

end KLSLevyProbe
