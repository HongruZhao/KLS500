import KLS.WeightedLocalSobolev
import KLS.ClassicalLaplacianFromDistribution

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- Raw local weak derivatives are identities against actual compact C1
tests. Integrability is supplied explicitly when a theorem needs it. -/
def HasLocalWeakCoordinateDerivative (f g : Space n → ℝ) (i : Fin n) : Prop :=
  ∀ ψ : Space n → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
    (∫ x, f x * coordinateDerivative ψ i x) = -(∫ x, g x * ψ x)

theorem HasLocalWeakCoordinateDerivative.unique
    {f F G : Space n → ℝ} {i : Fin n}
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hG : HasLocalWeakCoordinateDerivative f G i)
    (hFloc : LocallyIntegrable F volume) (hGloc : LocallyIntegrable G volume) :
    F =ᵐ[volume] G := by
  apply ae_eq_of_integral_contDiff_smul_eq hFloc hGloc
  intro ψ hψ hc
  have he := neg_injective ((hF ψ (hψ.of_le (by simp)) hc).symm.trans
    (hG ψ (hψ.of_le (by simp)) hc))
  simpa only [smul_eq_mul, mul_comm] using he

theorem HasLocalWeakCoordinateDerivative.congr_ae
    {f g F G : Space n → ℝ} {i : Fin n}
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hfg : f =ᵐ[volume] g) (hFG : F =ᵐ[volume] G) :
    HasLocalWeakCoordinateDerivative g G i := by
  intro ψ hψ hc
  have hl : (∫ x, f x * coordinateDerivative ψ i x) =
      ∫ x, g x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    rw [hx]
  have hr : (∫ x, F x * ψ x) = ∫ x, G x * ψ x := by
    apply integral_congr_ae
    filter_upwards [hFG] with x hx
    rw [hx]
  have he := hF ψ hψ hc
  rwa [hl, hr] at he

/-- Derivatives of two functions equal on an open set agree there almost
everywhere. This follows from compact-test uniqueness. -/
theorem ae_eq_weakCoordinateDerivative_of_eqOn
    {f g : Space n → ℝ} {i : Fin n}
    {F G : Lp ℝ 2 (volume : Measure (Space n))}
    (hF : HasWeakCoordinateDerivative f i F)
    (hG : HasWeakCoordinateDerivative g i G)
    {U : Set (Space n)} (hU : IsOpen U) (heq : EqOn f g U) :
    ∀ᵐ x, x ∈ U → F x = G x := by
  have hloc : LocallyIntegrable (fun x => F x - G x) volume :=
    ((Lp.memLp F).locallyIntegrable (by norm_num)).sub
      ((Lp.memLp G).locallyIntegrable (by norm_num))
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn U)
    (fun ψ hψ hc hs => by
      have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
      have hψLp : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hc
      have hleft : (∫ x, f x * coordinateDerivative ψ i x) =
          ∫ x, g x * coordinateDerivative ψ i x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only
          by_cases hx : x ∈ U
          · rw [heq hx]
          · have hd : coordinateDerivative ψ i x = 0 :=
              image_eq_zero_of_notMem_tsupport (fun ht =>
                hx (hs (tsupport_coordinateDerivative_subset ψ i ht)))
            rw [hd, mul_zero, mul_zero]
      have hright : (∫ x, F x * ψ x) = ∫ x, G x * ψ x := by
        have h₁ := hF ψ hψ1 hc
        have h₂ := hG ψ hψ1 hc
        linarith
      have hFi : Integrable (fun x => F x * ψ x) volume := (Lp.memLp F).integrable_mul hψLp
      have hGi : Integrable (fun x => G x * ψ x) volume := (Lp.memLp G).integrable_mul hψLp
      calc
        (∫ x, ψ x • (F x - G x)) = ∫ x, F x * ψ x - G x * ψ x := by
          apply integral_congr_ae
          exact Eventually.of_forall fun _ => by simp only [smul_eq_mul]; ring
        _ = 0 := by rw [integral_sub hFi hGi, hright, sub_self])
  filter_upwards [hae] with x hx hxu
  exact sub_eq_zero.mp (hx hxu)

/-- A genuine cutoff derivative is the derivative of the original function
on every compact test supported where the cutoff equals one. -/
theorem HasWeakCoordinateDerivative.integral_eq_of_cutoff_one
    {f χ ψ : Space n → ℝ} {i : Fin n}
    {F : Lp ℝ 2 (volume : Measure (Space n))}
    (hF : HasWeakCoordinateDerivative (fun x => χ x * f x) i F)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hone : ∀ x ∈ tsupport ψ, χ x = 1) :
    (∫ x, f x * coordinateDerivative ψ i x) = -(∫ x, F x * ψ x) := by
  have hw := hF ψ hψ hc
  have he : (∫ x, χ x * f x * coordinateDerivative ψ i x) =
      ∫ x, f x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport ψ
      · rw [hone x hx, one_mul]
      · have hd : coordinateDerivative ψ i x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun ht => hx (tsupport_coordinateDerivative_subset ψ i ht))
        rw [hd, mul_zero, mul_zero]
  rwa [he] at hw

end KLS
end
