import KLS.WeakDerivativeMollification

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
variable {n : ℕ}

/-- The product rule for two actual L2 weak derivatives. The product and its
derivative need only be locally integrable. Only one factor is mollified,
so every limiting term is an actual strong L2 pairing. -/
theorem integral_product_coordinateDerivative_of_weak
    {f g ψ : Space n → ℝ} {i : Fin n}
    {F G : Lp ℝ 2 (volume : Measure (Space n))}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hF : HasWeakCoordinateDerivative f i F)
    (hG : HasWeakCoordinateDerivative g i G)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x, f x * g x * coordinateDerivative ψ i x) =
      -(∫ x, (F x * g x + f x * G x) * ψ x) := by
  have hψtop := hψ.continuous.memLp_top_of_hasCompactSupport hc volume
  have hdψtop :=
    (contDiff_coordinateDerivative hψ (m := 0) (by norm_num) i).continuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_coordinateDerivative hc i) volume
  have hA : MemLp (fun x => ψ x * f x) 2 volume := hψtop.mul hf
  have hB : MemLp (fun x => coordinateDerivative ψ i x * f x) 2 volume := hdψtop.mul hf
  have hC : MemLp (fun x => ψ x * F x) 2 volume := hψtop.mul (Lp.memLp F)
  have hm (k : ℕ) : MemLp (mollify k g) 2 volume := memLp_mollify hg k
  have hdm (k : ℕ) : MemLp (coordinateDerivative (mollify k g) i) 2 volume := by
    rw [hG.mollify_eq hg]
    exact memLp_mollify (Lp.memLp G) k
  have hlim₁ := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hm hg hB
    (eLpNorm_mollify_sub_tendsto_zero hg)
  have hlim₂ := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hm hg hC
    (eLpNorm_mollify_sub_tendsto_zero hg)
  have hlim₃ := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero hdm (Lp.memLp G) hA
    (hG.eLpNorm_mollify_derivative_sub_tendsto_zero hg)
  have he (k : ℕ) :
      (∫ x, (coordinateDerivative ψ i x * f x) * mollify k g x) =
        -((∫ x, (ψ x * F x) * mollify k g x) +
          ∫ x, (ψ x * f x) * coordinateDerivative (mollify k g) i x) := by
    have hmk : ContDiff ℝ 1 (mollify k g) :=
      (mollify_contDiff (hg.locallyIntegrable (by norm_num)) k).of_le (by simp)
    have hw := hF (fun x => ψ x * mollify k g x) (hψ.mul hmk) hc.mul_right
    have ha : Integrable (fun x => ψ x * f x * coordinateDerivative (mollify k g) i x) volume :=
      hA.integrable_mul (hdm k)
    have hb : Integrable (fun x => coordinateDerivative ψ i x * f x * mollify k g x) volume :=
      hB.integrable_mul (hm k)
    have hl : (∫ x, f x * coordinateDerivative (fun y => ψ y * mollify k g y) i x) =
        (∫ x, (coordinateDerivative ψ i x * f x) * mollify k g x) +
        ∫ x, (ψ x * f x) * coordinateDerivative (mollify k g) i x := by
      rw [← integral_add hb ha]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [coordinateDerivative_mul (hψ.differentiable (by norm_num) x)
          (hmk.differentiable (by norm_num) x)]
        ring
    have hr : (∫ x, F x * (ψ x * mollify k g x)) =
        ∫ x, (ψ x * F x) * mollify k g x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun _ => by ring
    rw [hl, hr] at hw
    linarith
  have hfinal := tendsto_nhds_unique hlim₁
    (((hlim₂.add hlim₃).neg).congr (fun k => (he k).symm))
  have hl : (∫ x, (coordinateDerivative ψ i x * f x) * g x) =
      ∫ x, f x * g x * coordinateDerivative ψ i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  have hr : (∫ x, (ψ x * F x) * g x) + (∫ x, (ψ x * f x) * G x) =
      ∫ x, (F x * g x + f x * G x) * ψ x := by
    have hcg : Integrable (fun x => ψ x * F x * g x) volume := hC.integrable_mul hg
    have haG : Integrable (fun x => ψ x * f x * G x) volume := hA.integrable_mul (Lp.memLp G)
    rw [← integral_add hcg haG]
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  rwa [hl, hr] at hfinal

/-- If the actual product derivative is L2, the distributional product
identity identifies precisely that derivative, not merely some witness. -/
theorem HasWeakCoordinateDerivative.mul_of_ae_eq
    {f g : Space n → ℝ} {i : Fin n}
    {F G W : Lp ℝ 2 (volume : Measure (Space n))}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hF : HasWeakCoordinateDerivative f i F)
    (hG : HasWeakCoordinateDerivative g i G)
    (hW : ∀ᵐ x, W x = F x * g x + f x * G x) :
    HasWeakCoordinateDerivative (fun x => f x * g x) i W := by
  intro ψ hψ hc
  rw [integral_product_coordinateDerivative_of_weak hf hg hF hG hψ hc]
  congr 1
  apply integral_congr_ae
  filter_upwards [hW] with x hx
  rw [hx]

/-- Bounded Sobolev factors have an actual L2 product derivative. -/
theorem HasWeakCoordinateDerivative.mul_bounded
    {f g : Space n → ℝ} {i : Fin n}
    {F G : Lp ℝ 2 (volume : Measure (Space n))}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfb : MemLp f ∞ volume) (hgb : MemLp g ∞ volume)
    (hF : HasWeakCoordinateDerivative f i F)
    (hG : HasWeakCoordinateDerivative g i G) :
    ∃ W : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative (fun x => f x * g x) i W ∧
      ∀ᵐ x, W x = F x * g x + f x * G x := by
  have hw : MemLp (fun x => F x * g x + f x * G x) 2 volume := by
    have ha : MemLp (fun x => F x * g x) 2 volume := by
      have hb : MemLp (fun x => g x * F x) 2 volume := hgb.mul (Lp.memLp F)
      simpa only [mul_comm] using hb
    exact ha.add (hfb.mul (Lp.memLp G))
  let W := hw.toLp (fun x => F x * g x + f x * G x)
  have he : ∀ᵐ x, W x = F x * g x + f x * G x := hw.coeFn_toLp
  exact ⟨W, hF.mul_of_ae_eq hf hg hG he, he⟩

end KLS
end
