import KLS.WeightedShiftedEnergyForm

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section
namespace KLS
variable {n : ℕ}

/-- The variational resolvent is constructed by Lax-Milgram on the actual
complete weighted gradient graph, using the actual value projection's adjoint. -/
def weightedResolventH1 (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] WeightedCenteredH1 φ :=
  (weightedShiftedEnergyForm_isCoercive φ ht).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (weightedH1Value φ).adjoint

/-- Its actual L2 value. The graph is centered; constants will be restored
separately when defining a mass-preserving resolvent. -/
def weightedResolvent (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (potentialMeasure φ) →L[ℝ] Lp ℝ 2 (potentialMeasure φ) :=
  (weightedH1Value φ).comp (weightedResolventH1 φ ht)

theorem weightedResolvent_variational (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) (V : WeightedCenteredH1 φ) :
    inner ℝ (weightedResolvent φ ht g) (weightedH1Value φ V) +
      t * weightedEnergyForm φ (weightedResolventH1 φ ht g) V =
        inner ℝ g (weightedH1Value φ V) := by
  let hc := weightedShiftedEnergyForm_isCoercive φ ht
  change inner ℝ (weightedH1Value φ (weightedResolventH1 φ ht g)) (weightedH1Value φ V) +
    t * weightedEnergyForm φ (weightedResolventH1 φ ht g) V = _
  rw [← weightedShiftedEnergyForm_apply]
  rw [← hc.continuousLinearEquivOfBilin_apply]
  change inner ℝ (hc.continuousLinearEquivOfBilin
    (hc.continuousLinearEquivOfBilin.symm ((weightedH1Value φ).adjoint g))) V = _
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem weightedResolvent_unique (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) {U : WeightedCenteredH1 φ}
    (hU : ∀ V, inner ℝ (weightedH1Value φ U) (weightedH1Value φ V) +
      t * weightedEnergyForm φ U V = inner ℝ g (weightedH1Value φ V)) :
    U = weightedResolventH1 φ ht g := by
  let hc := weightedShiftedEnergyForm_isCoercive φ ht
  have he : (weightedH1Value φ).adjoint g = hc.continuousLinearEquivOfBilin U := by
    apply hc.unique_continuousLinearEquivOfBilin
    intro V
    rw [ContinuousLinearMap.adjoint_inner_left, weightedShiftedEnergyForm_apply]
    exact (hU V).symm
  calc
    U = hc.continuousLinearEquivOfBilin.symm (hc.continuousLinearEquivOfBilin U) :=
      (hc.continuousLinearEquivOfBilin.symm_apply_apply U).symm
    _ = hc.continuousLinearEquivOfBilin.symm ((weightedH1Value φ).adjoint g) := by rw [he]
    _ = weightedResolventH1 φ ht g := rfl

theorem existsUnique_weightedResolventSolution (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ∃! U : WeightedCenteredH1 φ, ∀ V : WeightedCenteredH1 φ,
      inner ℝ (weightedH1Value φ U) (weightedH1Value φ V) +
        t * weightedEnergyForm φ U V = inner ℝ g (weightedH1Value φ V) :=
  ⟨weightedResolventH1 φ ht g, weightedResolvent_variational φ ht g,
    fun _ hU => weightedResolvent_unique φ ht g hU⟩

theorem weightedResolvent_energy_identity (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (g : Lp ℝ 2 (potentialMeasure φ)) :
    ‖weightedResolvent φ ht g‖ ^ 2 +
      t * weightedEnergyForm φ (weightedResolventH1 φ ht g) (weightedResolventH1 φ ht g) =
        inner ℝ g (weightedResolvent φ ht g) := by
  simpa only [weightedResolvent, ContinuousLinearMap.comp_apply, real_inner_self_eq_norm_sq] using
    weightedResolvent_variational φ ht g (weightedResolventH1 φ ht g)

theorem weightedResolvent_symmetric (φ : Space n → ℝ) {t : ℝ} (ht : 0 < t)
    (f g : Lp ℝ 2 (potentialMeasure φ)) :
    inner ℝ (weightedResolvent φ ht f) g = inner ℝ f (weightedResolvent φ ht g) := by
  have hf := weightedResolvent_variational φ ht f (weightedResolventH1 φ ht g)
  have hg := weightedResolvent_variational φ ht g (weightedResolventH1 φ ht f)
  change inner ℝ (weightedResolvent φ ht f) (weightedResolvent φ ht g) + _ =
    inner ℝ f (weightedResolvent φ ht g) at hf
  change inner ℝ (weightedResolvent φ ht g) (weightedResolvent φ ht f) + _ =
    inner ℝ g (weightedResolvent φ ht f) at hg
  rw [real_inner_comm (weightedResolvent φ ht f) (weightedResolvent φ ht g),
    weightedEnergyForm_symm φ (weightedResolventH1 φ ht g),
    real_inner_comm (weightedResolvent φ ht f) g] at hg
  exact hg.symm.trans hf

end KLS
end
