import KLS.WeakDivergenceDifferentiation

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

lemma locallyIntegrable_product_of_localL2
    {f g : Space n → ℝ}
    (hf : ∀ S, IsCompact S → MemLp f 2 (volume.restrict S))
    (hg : ∀ S, IsCompact S → MemLp g 2 (volume.restrict S)) :
    LocallyIntegrable (fun x => f x * g x) volume :=
  locallyIntegrable_iff.mpr fun S hS => (hf S hS).integrable_mul (hg S hS)

/-- A continuous local H1 multiplier obeys the genuine distributional
 divergence product rule, using bounded compact H1 test approximation. -/
theorem integral_divergence_mul_localH1
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ} {F : Fin n → Space n → ℝ}
    (hA : ∀ i S, IsCompact S → MemLp (A i) 2 (volume.restrict S))
    (hb : LocallyIntegrable b volume)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x * coordinateDerivative ψ i x) = ∫ x, b x * ψ x)
    (hfcont : Continuous f) (hf : ∀ S, IsCompact S → MemLp f 2 (volume.restrict S))
    (hFl : ∀ i S, IsCompact S → MemLp (F i) 2 (volume.restrict S))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i)
    {ψ : Space n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∑ i, ∫ x, (f x * A i x) * coordinateDerivative ψ i x) =
      ∫ x, (f x * b x - ∑ i, A i x * F i x) * ψ x := by
  have hψl : ∀ S, IsCompact S → MemLp ψ 2 (volume.restrict S) :=
    fun S _ => (hψ.continuous.memLp_of_hasCompactSupport hc).restrict S
  have hdψ (i : Fin n) := (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous
  have hdψl (i : Fin n) : ∀ S, IsCompact S →
      MemLp (coordinateDerivative ψ i) 2 (volume.restrict S) :=
    fun S _ => ((hdψ i).memLp_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc i)).restrict S
  have hψb (S : Set (Space n)) : MemLp ψ ∞ (volume.restrict S) :=
    (hψ.continuous.memLp_top_of_hasCompactSupport hc volume).restrict S
  have hdψb (i : Fin n) (S : Set (Space n)) :
      MemLp (coordinateDerivative ψ i) ∞ (volume.restrict S) :=
    ((hdψ i).memLp_top_of_hasCompactSupport (hasCompactSupport_coordinateDerivative hc i) volume).restrict S
  have htest : ∀ S, IsCompact S → MemLp (fun x => f x * ψ x) 2 (volume.restrict S) := by
    intro S hS
    have h : MemLp (fun x => ψ x * f x) 2 (volume.restrict S) := (hψb S).mul (hf S hS)
    simpa only [mul_comm] using h
  have htestF (i : Fin n) := (hF i).mul (hasLocalWeakCoordinateDerivative_of_contDiff hψ i)
    hf hψl (hFl i) (hdψl i)
  have htestFl (i : Fin n) (S : Set (Space n)) (hS : IsCompact S) :
      MemLp (fun x => F i x * ψ x + f x * coordinateDerivative ψ i x) 2 (volume.restrict S) := by
    have h₁ : MemLp (fun x => ψ x * F i x) 2 (volume.restrict S) := (hψb S).mul (hFl i S hS)
    have h₂ : MemLp (fun x => coordinateDerivative ψ i x * f x) 2 (volume.restrict S) :=
      (hdψb i S).mul (hf S hS)
    have ht : MemLp (fun x => ψ x * F i x + coordinateDerivative ψ i x * f x)
        2 (volume.restrict S) := h₁.add h₂
    convert ht using 1
    funext x
    ring
  have htc : HasCompactSupport (fun x => f x * ψ x) := hc.mul_left
  obtain ⟨C, hC⟩ := (hfcont.mul hψ.continuous).bounded_above_of_compact_support htc
  have hh := integral_divergence_of_bounded_compact_H1_test hA hb hdiv htest htc
    (Eventually.of_forall hC) htestFl htestF
  have ha (i : Fin n) : Integrable (fun x => (A i x * F i x) * ψ x) :=
    integrable_mul_compact_of_locallyIntegrable
      (locallyIntegrable_product_of_localL2 (hA i) (hFl i)) hψ.continuous hc
  have hc' (i : Fin n) : Integrable (fun x => (f x * A i x) * coordinateDerivative ψ i x) :=
    integrable_mul_compact_of_locallyIntegrable
      (locallyIntegrable_product_of_localL2 hf (hA i)) (hdψ i) (hasCompactSupport_coordinateDerivative hc i)
  have hb' : Integrable (fun x => (f x * b x) * ψ x) :=
    integrable_mul_compact_of_locallyIntegrable (hb.continuous_mul hfcont) hψ.continuous hc
  have he (i : Fin n) : (∫ x, A i x * (F i x * ψ x + f x * coordinateDerivative ψ i x)) =
      (∫ x, (A i x * F i x) * ψ x) + (∫ x, (f x * A i x) * coordinateDerivative ψ i x) := by
    rw [← integral_add (ha i) (hc' i)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; ring
  have hr : (∫ x, b x * (f x * ψ x)) = ∫ x, (f x * b x) * ψ x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hid := hh.2.2
  simp_rw [he] at hid
  rw [Finset.sum_add_distrib, hr] at hid
  have hsum : Integrable (fun x => (∑ i, A i x * F i x) * ψ x) := by
    simpa only [Finset.sum_mul] using integrable_finsetSum Finset.univ (fun i _ => ha i)
  have hrhs : (∫ x, (f x * b x - ∑ i, A i x * F i x) * ψ x) =
      (∫ x, (f x * b x) * ψ x) - ∑ i, ∫ x, (A i x * F i x) * ψ x := by
    simp only [sub_mul, Finset.sum_mul]
    rw [integral_sub hb' (by simpa only [Finset.sum_mul] using hsum),
      integral_finsetSum _ (fun i _ => ha i)]
  rw [hrhs]
  linarith

end KLS
end
