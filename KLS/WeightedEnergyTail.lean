import KLS.WeightedConfinement
import KLS.WeightedL2Indicator

/-! Actual weighted L² tail control on the completed gradient graph. -/
open MeasureTheory ProbabilityTheory InnerProductSpace Set Filter Matrix
open scoped ContDiff RealInnerProductSpace Topology

noncomputable section
namespace KLS
variable {n : ℕ}

lemma smoothCutoff_nonneg_le_one (k : ℕ) (x : Space n) :
    0 ≤ smoothCutoff n k x ∧ smoothCutoff n k x ≤ 1 :=
  ⟨(unitCutoff n).nonneg, (unitCutoff n).le_one⟩

lemma smoothCutoff_gradient_uniform_bound : ∃ K : ℝ, 0 ≤ K ∧
    ∀ k x, ‖gradient (smoothCutoff n k) x‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := smoothCutoff_gradient_bound (n := n)
  refine ⟨K, hK, fun k x => (hb k x).trans ?_⟩
  have hs : cutoffScale k ≤ 1 := by
    unfold cutoffScale
    apply inv_le_one_of_one_le₀
    linarith [Nat.cast_nonneg (α := ℝ) k]
  exact mul_le_of_le_one_left hK hs

lemma gradient_mul_sq_le {χ f : Space n → ℝ} {K : ℝ}
    (hχ : ContDiff ℝ 1 χ) (hf : ContDiff ℝ 1 f) (_hK : 0 ≤ K)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχd : ∀ x, ‖gradient χ x‖ ≤ K) (x : Space n) :
    ‖gradient (fun y => χ y * f y) x‖ ^ 2 ≤
      2 * ‖gradient f x‖ ^ 2 + 2 * K ^ 2 * f x ^ 2 := by
  rw [gradient_mul_real (hχ.differentiable (by norm_num) x)
    (hf.differentiable (by norm_num) x)]
  have hsum (a b : Space n) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    rw [norm_add_sq_real]
    have h := sq_nonneg ‖a - b‖
    rw [norm_sub_sq_real] at h
    linarith
  have hs := hsum (f x • gradient χ x) (χ x • gradient f x)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hs
  have hc2 : (χ x) ^ 2 ≤ 1 := by nlinarith [(hχb x).1, (hχb x).2]
  have hd2 : ‖gradient χ x‖ ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hχd x) 2
  have h₁ := mul_le_mul_of_nonneg_right hc2 (sq_nonneg ‖gradient f x‖)
  have h₂ := mul_le_mul_of_nonneg_left hd2 (sq_nonneg (f x))
  nlinarith

/-- A compact test's exterior mass is bounded by its actual value and gradient energies. -/
theorem weighted_tail_compact {φ f : Space n → ℝ} {κ R : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ) (hR : 0 ≤ R)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    κ ^ 2 * R ^ 2 * (∫ x in {x | R ≤ ‖x‖}, f x ^ 2 ∂potentialMeasure φ) ≤
      (2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2) * (∫ x, f x ^ 2 ∂potentialMeasure φ) +
        8 * ∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ := by
  have hfc2 : HasCompactSupport (fun x => f x ^ 2) := by
    have ht := (hc.mul_right : HasCompactSupport (f * f))
    change HasCompactSupport (fun x => f x * f x) at ht
    simpa only [pow_two] using ht
  have hi : Integrable (fun x => f x ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
    (hf.continuous.pow 2) hfc2
  have hQi : Integrable (fun x => ‖x‖ ^ 2 * f x ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
    ((continuous_norm.pow 2).mul (hf.continuous.pow 2)) hfc2.mul_left
  have hs : MeasurableSet {x : Space n | R ≤ ‖x‖} := isClosed_le continuous_const continuous_norm |>.measurableSet
  have hmono : R ^ 2 * (∫ x in {x | R ≤ ‖x‖}, f x ^ 2 ∂potentialMeasure φ) ≤
      ∫ x, ‖x‖ ^ 2 * f x ^ 2 ∂potentialMeasure φ := by
    rw [← integral_const_mul]
    apply le_trans (setIntegral_mono_on (hi.const_mul (R ^ 2)).integrableOn hQi.integrableOn hs ?_)
      (setIntegral_le_integral hQi (Eventually.of_forall fun _ => by positivity))
    intro x hx
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hx 2) (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left hmono (sq_nonneg κ)
  calc
    _ = κ ^ 2 * (R ^ 2 * (∫ x in {x | R ≤ ‖x‖}, f x ^ 2 ∂potentialMeasure φ)) := by ring
    _ ≤ _ := h
    _ ≤ _ := weighted_confinement_compact hφ hκ hlower hf hc

set_option maxHeartbeats 800000 in
/-- The cutoff extension only needs finite value and gradient energies. -/
theorem weighted_tail_smooth {φ f : Space n → ℝ} {κ K R : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ) (hR : 0 ≤ R)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hf : ContDiff ℝ 1 f) (hfi : Integrable (fun x => f x ^ 2) (potentialMeasure φ))
    (hdi : Integrable (fun x => ‖gradient f x‖ ^ 2) (potentialMeasure φ))
    (hK : 0 ≤ K) (hKb : ∀ k x, ‖gradient (smoothCutoff n k) x‖ ≤ K) :
    κ ^ 2 * R ^ 2 * (∫ x in {x | R ≤ ‖x‖}, f x ^ 2 ∂potentialMeasure φ) ≤
      (2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2 + 16 * K ^ 2) *
        (∫ x, f x ^ 2 ∂potentialMeasure φ) +
        16 * ∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ := by
  let F (k : ℕ) : Space n → ℝ := fun x => smoothCutoff n k x * f x
  have hFc (k : ℕ) : HasCompactSupport (F k) := (smoothCutoff_hasCompactSupport k).mul_right
  have hFd (k : ℕ) : ContDiff ℝ 1 (F k) := (smoothCutoff_contDiff k).mul hf
  have hF2c (k : ℕ) : HasCompactSupport (fun x => F k x ^ 2) := by
    have ht := ((hFc k).mul_right : HasCompactSupport (F k * F k))
    change HasCompactSupport (fun x => F k x * F k x) at ht
    simpa only [pow_two] using ht
  have hF2i (k : ℕ) : Integrable (fun x => F k x ^ 2) (potentialMeasure φ) :=
    integrable_potentialMeasure_of_continuous_hasCompactSupport
    hφ.continuous ((hFd k).continuous.pow 2) (hF2c k)
  have hF2b (k : ℕ) (x : Space n) : F k x ^ 2 ≤ f x ^ 2 := by
    have hχ := smoothCutoff_nonneg_le_one k x
    have hχ2 : smoothCutoff n k x ^ 2 ≤ 1 := by nlinarith [hχ.1, hχ.2]
    simpa only [F, mul_pow, one_mul] using mul_le_mul_of_nonneg_right hχ2 (sq_nonneg (f x))
  have hEi (k : ℕ) : Integrable (fun x => ‖gradient (F k) x‖ ^ 2) (potentialMeasure φ) := by
    apply integrable_potentialMeasure_of_continuous_hasCompactSupport hφ.continuous
      ((continuous_gradient_of_contDiff (hFd k)).norm.pow 2)
    change HasCompactSupport (fun x => ‖gradient (F k) x‖ ^ 2)
    have ht := ((hasCompactSupport_gradient (hFc k)).norm.mul_right :
      HasCompactSupport ((fun x => ‖gradient (F k) x‖) * (fun x => ‖gradient (F k) x‖)))
    change HasCompactSupport (fun x => ‖gradient (F k) x‖ * ‖gradient (F k) x‖) at ht
    simpa only [pow_two] using ht
  have hbound (k : ℕ) :
      κ ^ 2 * R ^ 2 * (∫ x in {x | R ≤ ‖x‖}, F k x ^ 2 ∂potentialMeasure φ) ≤
        (2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2 + 16 * K ^ 2) *
          (∫ x, f x ^ 2 ∂potentialMeasure φ) +
          16 * ∫ x, ‖gradient f x‖ ^ 2 ∂potentialMeasure φ := by
    have h := weighted_tail_compact hφ hκ hR hlower (hFd k) (hFc k)
    have hJ := integral_mono (hF2i k) hfi (hF2b k)
    have hE := integral_mono (hEi k) ((hdi.const_mul 2).add (hfi.const_mul (2 * K ^ 2)))
      (gradient_mul_sq_le (smoothCutoff_contDiff k) hf hK
        (smoothCutoff_nonneg_le_one k) (hKb k))
    have heq := integral_add (hdi.const_mul 2) (hfi.const_mul (2 * K ^ 2))
    simp only [Pi.add_apply] at heq hE
    rw [heq, integral_const_mul, integral_const_mul] at hE
    have hA : 0 ≤ 2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2 := by positivity
    have hJ' := mul_le_mul_of_nonneg_left hJ hA
    nlinarith
  have hlim : Tendsto (fun k => ∫ x in {x | R ≤ ‖x‖}, F k x ^ 2 ∂potentialMeasure φ)
      atTop (𝓝 (∫ x in {x | R ≤ ‖x‖}, f x ^ 2 ∂potentialMeasure φ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
      (fun k => (hF2i k).integrableOn.aestronglyMeasurable) hfi.integrableOn
    · intro k
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hF2b k x
    · exact Eventually.of_forall fun x => by
        simpa only [F, one_mul] using ((smoothCutoff_tendsto_one x).mul_const (f x)).pow 2
  exact le_of_tendsto' (hlim.const_mul (κ ^ 2 * R ^ 2)) hbound


/-- Exterior-tail control on each actual centered smooth-gradient pair. -/
theorem smoothCenteredGradientGraphSet_tail_norm_sq_le {φ : Space n → ℝ} {κ K R : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ) (hR : 0 ≤ R)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hK : 0 ≤ K) (hKb : ∀ k x, ‖gradient (smoothCutoff n k) x‖ ≤ K)
    {U : WeightedEnergyAmbient φ} (hU : U ∈ smoothCenteredGradientGraphSet φ) :
    κ ^ 2 * R ^ 2 * ‖weightedL2Indicator φ
        (isClosed_le continuous_const continuous_norm |>.measurableSet :
          MeasurableSet {x : Space n | R ≤ ‖x‖}) (U 0)‖ ^ 2 ≤
      (2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2 + 16 * K ^ 2) * ‖U 0‖ ^ 2 +
        16 * ∑ i : Fin n, ‖U i.succ‖ ^ 2 := by
  obtain ⟨f, hf, hc, hv, hd⟩ := hU
  let f₀ : Space n → ℝ := fun x => f x - ∫ y, f y ∂potentialMeasure φ
  have hf₀ : ContDiff ℝ 1 f₀ := (hf.of_le (by norm_num)).sub contDiff_const
  have hd₀ (i : Fin n) : coordinateDerivative f₀ i = coordinateDerivative f i := by
    funext x
    unfold coordinateDerivative
    dsimp [f₀]
    rw [fderiv_fun_sub (hf.differentiable (by norm_num) x) (differentiableAt_const _)]
    simp
  have hg₀ (x : Space n) : ‖gradient f₀ x‖ ^ 2 =
      ∑ i : Fin n, (coordinateDerivative f i x) ^ 2 := by
    simp_rw [EuclideanSpace.real_norm_sq_eq, ← coordinateDerivative_eq_gradient, hd₀]
  have hfi : MemLp f₀ 2 (potentialMeasure φ) := (memLp_congr_ae hv).mp (Lp.memLp (U 0))
  have hdi (i : Fin n) : MemLp (coordinateDerivative f i) 2 (potentialMeasure φ) :=
    (memLp_congr_ae (hd i)).mp (Lp.memLp (U i.succ))
  have hgi : Integrable (fun x => ‖gradient f₀ x‖ ^ 2) (potentialMeasure φ) := by
    simp_rw [hg₀]
    exact integrable_finsetSum Finset.univ (fun i _ => (hdi i).integrable_sq)
  have hvnorm : ‖U 0‖ ^ 2 = ∫ x, f₀ x ^ 2 ∂potentialMeasure φ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp [hx, f₀, pow_two]
  have hdnorm (i : Fin n) : ‖U i.succ‖ ^ 2 =
      ∫ x, (coordinateDerivative f i x) ^ 2 ∂potentialMeasure φ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd i] with x hx
    simp [hx, pow_two]
  have hgnorm : (∫ x, ‖gradient f₀ x‖ ^ 2 ∂potentialMeasure φ) =
      ∑ i : Fin n, ‖U i.succ‖ ^ 2 := by
    simp_rw [hg₀, hdnorm]
    exact integral_finsetSum Finset.univ (fun i _ => (hdi i).integrable_sq)
  have htail : ‖weightedL2Indicator φ
        (isClosed_le continuous_const continuous_norm |>.measurableSet :
          MeasurableSet {x : Space n | R ≤ ‖x‖}) (U 0)‖ ^ 2 =
      ∫ x in {x | R ≤ ‖x‖}, f₀ x ^ 2 ∂potentialMeasure φ := by
    rw [weightedL2Indicator_norm_sq]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hv] with x hx
    rw [hx]
  rw [htail, hvnorm, ← hgnorm]
  exact weighted_tail_smooth hφ hκ hR hlower hf₀ hfi.integrable_sq hgi hK hKb

/-- Closedness extends the genuine smooth-core tail inequality to the completed energy graph. -/
theorem weightedH1_tail_norm_sq_le {φ : Space n → ℝ} {κ K R : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ) (hR : 0 ≤ R)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a))
    (hK : 0 ≤ K) (hKb : ∀ k x, ‖gradient (smoothCutoff n k) x‖ ≤ K)
    (U : WeightedCenteredH1 φ) :
    κ ^ 2 * R ^ 2 * ‖weightedL2Indicator φ
        (isClosed_le continuous_const continuous_norm |>.measurableSet :
          MeasurableSet {x : Space n | R ≤ ‖x‖}) (weightedH1Value φ U)‖ ^ 2 ≤
      (2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2 + 16 * K ^ 2) * ‖weightedH1Value φ U‖ ^ 2 +
        16 * ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 := by
  let I := weightedL2Indicator φ
    (isClosed_le continuous_const continuous_norm |>.measurableSet :
      MeasurableSet {x : Space n | R ≤ ‖x‖})
  have hclosed : IsClosed {W : WeightedEnergyAmbient φ |
      κ ^ 2 * R ^ 2 * ‖I (W 0)‖ ^ 2 ≤
        (2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2 + 16 * K ^ 2) * ‖W 0‖ ^ 2 +
          16 * ∑ i : Fin n, ‖W i.succ‖ ^ 2} := isClosed_le (by fun_prop) (by fun_prop)
  have hcore : smoothCenteredGradientGraphSet φ ⊆ {W : WeightedEnergyAmbient φ |
      κ ^ 2 * R ^ 2 * ‖I (W 0)‖ ^ 2 ≤
        (2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2 + 16 * K ^ 2) * ‖W 0‖ ^ 2 +
          16 * ∑ i : Fin n, ‖W i.succ‖ ^ 2} :=
    fun _ hW => smoothCenteredGradientGraphSet_tail_norm_sq_le hφ hκ hR hlower hK hKb hW
  have hU : (U : WeightedEnergyAmbient φ) ∈ closure (smoothCenteredGradientGraphSet φ) := by
    rw [← weightedCenteredGradientGraph_coe_eq_closure hφ.continuous]
    exact U.property
  exact (closure_minimal hcore hclosed) hU

/-- An actual per-measure tail constant controls all completed energy-graph values uniformly.
The constant is derived from κ, dimension and the actual gradient of the potential at the origin. -/
theorem exists_weightedH1_tail_bound {φ : Space n → ℝ} {κ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hκ : 0 < κ)
    (hlower : ∀ y (a : Fin n → ℝ),
      κ * (a ⬝ᵥ a) ≤ a ⬝ᵥ (coordinateHessian φ y *ᵥ a)) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ U : WeightedCenteredH1 φ,
      (∫ x in {x | R ≤ ‖x‖}, weightedH1Value φ U x ^ 2 ∂potentialMeasure φ) ≤
        C / R ^ 2 * ‖U‖ ^ 2 := by
  obtain ⟨K, hK, hKb⟩ := smoothCutoff_gradient_uniform_bound (n := n)
  let A : ℝ := 2 * κ * n + 2 * ‖gradient φ 0‖ ^ 2 + 16 * K ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(A + 16) / κ ^ 2, by positivity, ?_⟩
  intro R hR U
  have h := weightedH1_tail_norm_sq_le hφ hκ hR.le hlower hK hKb U
  rw [weightedL2Indicator_norm_sq] at h
  have hn := weightedH1_norm_sq φ U
  have hv := sq_nonneg ‖weightedH1Value φ U‖
  have hd : 0 ≤ ∑ i : Fin n, ‖weightedH1Derivative φ i U‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : κ ^ 2 * R ^ 2 *
      (∫ x in {x | R ≤ ‖x‖}, weightedH1Value φ U x ^ 2 ∂potentialMeasure φ) ≤
        (A + 16) * ‖U‖ ^ 2 := by
    change κ ^ 2 * R ^ 2 * _ ≤ A * _ + 16 * _ at h
    have he := mul_nonneg hA hd
    nlinarith
  have hb' : (∫ x in {x | R ≤ ‖x‖}, weightedH1Value φ U x ^ 2 ∂potentialMeasure φ) ≤
      ((A + 16) * ‖U‖ ^ 2) / (κ ^ 2 * R ^ 2) :=
    (le_div_iff₀ (mul_pos (sq_pos_of_pos hκ) (sq_pos_of_pos hR))).mpr
      (by nlinarith [hb])
  convert hb' using 1
  field_simp

end KLS
end

#print axioms KLS.weighted_tail_compact
#print axioms KLS.weighted_tail_smooth

#print axioms KLS.weightedH1_tail_norm_sq_le
#print axioms KLS.exists_weightedH1_tail_bound
