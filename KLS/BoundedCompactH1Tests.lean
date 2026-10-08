import KLS.CompactRawWeakDerivative
import KLS.BoundedCompactMollifierPairing

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
open EllipticPdes.Regularity
variable {n : ℕ}

/-- A locally L2 flux with locally L1 divergence can be tested against any
 actual bounded compact raw H1 function. Its locally constructed weak
 derivatives are used literally in the resulting integral identity. -/
theorem integral_divergence_of_bounded_compact_H1_test
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ}
    {F : Fin n → Space n → ℝ}
    (hA : ∀ i, ∀ S : Set (Space n), IsCompact S → MemLp (A i) 2 (volume.restrict S))
    (hb : LocallyIntegrable b volume)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∑ i, ∫ x, A i x*coordinateDerivative ψ i x) = ∫ x, b x*ψ x)
    (hf : ∀ S : Set (Space n), IsCompact S → MemLp f 2 (volume.restrict S))
    (hc : HasCompactSupport f) {C : ℝ}
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ C)
    (hFloc : ∀ i, ∀ S : Set (Space n), IsCompact S → MemLp (F i) 2 (volume.restrict S))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x*F i x)) ∧
      Integrable (fun x => b x*f x) ∧
      (∑ i, ∫ x, A i x*F i x) = ∫ x, b x*f x := by
  have hf2 := memLp_compact_of_localL2 hf hc
  have hfloc := hf2.locallyIntegrable (by norm_num)
  have hp (i : Fin n) := (hF i).localL2_pairing_mollify hf2 hc (hFloc i) (hA i)
  have hr := bounded_compact_mollify_localL1_pairing hfloc hc hbound hb
  refine ⟨fun i => (hp i).1,hr.1,?_⟩
  have hl := tendsto_finsetSum Finset.univ (fun i _ => (hp i).2)
  have he : (fun k => ∑ i, ∫ x, A i x*coordinateDerivative (mollify k f) i x) =
      fun k => ∫ x, b x*mollify k f x := by
    funext k
    exact hdiv _ ((mollify_contDiff hfloc k).of_le (by simp)) (hasCompactSupport_mollify hc k)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr.2

/-- The same genuine approximation extends distribution inequalities to
 nonnegative bounded compact raw H1 tests. -/
theorem integral_divergence_le_of_bounded_compact_H1_test
    {A : Fin n → Space n → ℝ} {b f : Space n → ℝ}
    {F : Fin n → Space n → ℝ}
    (hA : ∀ i, ∀ S : Set (Space n), IsCompact S → MemLp (A i) 2 (volume.restrict S))
    (hb : LocallyIntegrable b volume)
    (hdiv : ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∀ x, 0 ≤ ψ x) → (∑ i, ∫ x, A i x*coordinateDerivative ψ i x) ≤ ∫ x, b x*ψ x)
    (hf : ∀ S : Set (Space n), IsCompact S → MemLp f 2 (volume.restrict S))
    (hc : HasCompactSupport f) {C : ℝ}
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) (hnonneg : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hFloc : ∀ i, ∀ S : Set (Space n), IsCompact S → MemLp (F i) 2 (volume.restrict S))
    (hF : ∀ i, HasLocalWeakCoordinateDerivative f (F i) i) :
    (∀ i, Integrable (fun x => A i x*F i x)) ∧
      Integrable (fun x => b x*f x) ∧
      (∑ i, ∫ x, A i x*F i x) ≤ ∫ x, b x*f x := by
  have hf2 := memLp_compact_of_localL2 hf hc
  have hfloc := hf2.locallyIntegrable (by norm_num)
  have hp (i : Fin n) := (hF i).localL2_pairing_mollify hf2 hc (hFloc i) (hA i)
  have hr := bounded_compact_mollify_localL1_pairing hfloc hc hbound hb
  refine ⟨fun i => (hp i).1,hr.1,?_⟩
  have hl := tendsto_finsetSum Finset.univ (fun i _ => (hp i).2)
  apply le_of_tendsto_of_tendsto hl hr.2
  exact Eventually.of_forall fun k => hdiv _ ((mollify_contDiff hfloc k).of_le (by simp))
    (hasCompactSupport_mollify hc k) (mollify_nonneg_of_ae hnonneg k)

end KLS
end
