import KLS.LocalWeakDerivativeCutoff
import KLS.WeakDerivativeMollification

open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KLS
open EllipticPdes.Regularity
variable {n : ℕ}

/-- A compactly supported raw local weak derivative has a genuine global
 L2 representative, equal almost everywhere to the given derivative. -/
theorem HasLocalWeakCoordinateDerivative.global_of_compact
    {f F : Space n → ℝ} {i : Fin n}
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hf : ∀ S : Set (Space n), IsCompact S → MemLp f 2 (volume.restrict S))
    (hFloc : ∀ S : Set (Space n), IsCompact S → MemLp F 2 (volume.restrict S))
    (hc : HasCompactSupport f) :
    ∃ G : Lp ℝ 2 (volume : Measure (Space n)),
      HasWeakCoordinateDerivative f i G ∧ (fun x => G x) =ᵐ[volume] F := by
  obtain ⟨χ,hχ,hχ1,_⟩ := exists_isTestFn_one_nhdsSet_of_isCompact hc isOpen_univ
    (subset_univ (tsupport f))
  obtain ⟨G,hG,_⟩ := hF.compact_mul hf hFloc (hχ.1.of_le (by simp)) hχ.2.1
  have he : (fun x => χ x*f x) = f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · rw [hχ1.self_of_nhdsSet x hx,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero]
  rw [he] at hG
  refine ⟨G,hG,?_⟩
  exact HasLocalWeakCoordinateDerivative.unique hG hF
    ((Lp.memLp G).locallyIntegrable (by norm_num))
    (locallyIntegrable_of_memLp_two_on_compacts hFloc)

/-- The actual L2 derivative of a compactly supported function vanishes
 almost everywhere outside its actual support. -/
theorem HasWeakCoordinateDerivative.ae_zero_off_tsupport
    {f : Space n → ℝ} {i : Fin n}
    {G : Lp ℝ 2 (volume : Measure (Space n))}
    (hG : HasWeakCoordinateDerivative f i G) :
    ∀ᵐ x, x ∉ tsupport f → G x = 0 := by
  have hz : HasWeakCoordinateDerivative (fun _ : Space n => (0 : ℝ)) i 0 := by
    intro ψ _ _
    simp
  have he := ae_eq_weakCoordinateDerivative_of_eqOn hG hz
    (isClosed_tsupport f).isOpen_compl (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  filter_upwards [he] with x hx hxf
  simpa using hx hxf

/-- Actual mollified gradients converge in their pairings with locally L2
 fluxes; localization uses the common compact support enlargement. -/
theorem HasWeakCoordinateDerivative.localL2_pairing_mollify
    {f A : Space n → ℝ} {i : Fin n}
    {G : Lp ℝ 2 (volume : Measure (Space n))}
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hG : HasWeakCoordinateDerivative f i G)
    (hA : ∀ S : Set (Space n), IsCompact S → MemLp A 2 (volume.restrict S)) :
    Integrable (fun x => A x*G x) ∧
      Tendsto (fun k => ∫ x, A x*coordinateDerivative (mollify k f) i x)
        atTop (𝓝 (∫ x, A x*G x)) := by
  let S := mollifierEnlargement (tsupport f)
  have hS : IsCompact S := isCompact_mollifierEnlargement hc
  have hA2 : MemLp (S.indicator A) 2 volume :=
    (memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet).mpr (hA S hS)
  have hGe : (fun x => S.indicator A x*G x) =ᵐ[volume] (fun x => A x*G x) := by
    filter_upwards [hG.ae_zero_off_tsupport] with x hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
    · have hg0 := hx (fun h => hxS (subset_mollifierEnlargement (tsupport f) h))
      rw [hg0,mul_zero,mul_zero]
  refine ⟨(hA2.integrable_mul (Lp.memLp G)).congr hGe,?_⟩
  have ht := tendsto_integral_mul_of_eLpNorm_sub_tendsto_zero
    (fun k => by rw [hG.mollify_eq hf]; exact memLp_mollify (Lp.memLp G) k)
    (Lp.memLp G) hA2 (hG.eLpNorm_mollify_derivative_sub_tendsto_zero hf)
  have he (k : ℕ) : (∫ x, S.indicator A x*coordinateDerivative (mollify k f) i x) =
      ∫ x, A x*coordinateDerivative (mollify k f) i x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
      · have hz : coordinateDerivative (mollify k f) i x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h =>
            hx (tsupport_mollify_subset hc k (tsupport_coordinateDerivative_subset _ i h)))
        rw [hz,mul_zero,mul_zero]
  simpa only [he,integral_congr_ae hGe] using ht


/-- Compact support globalizes genuine local L2 membership. -/
theorem memLp_compact_of_localL2 {f : Space n → ℝ}
    (hf : ∀ S : Set (Space n), IsCompact S → MemLp f 2 (volume.restrict S))
    (hc : HasCompactSupport f) : MemLp f 2 volume := by
  have hi : MemLp ((tsupport f).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hc.measurableSet.nullMeasurableSet).mpr (hf _ hc)
  have he : (tsupport f).indicator f = f := by
    funext x
    by_cases hx : x ∈ tsupport f
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport hx]
  rwa [he] at hi

/-- The strong mollifier pairing limit retains the original raw local
 derivative, using its genuine global representative only in the proof. -/
theorem HasLocalWeakCoordinateDerivative.localL2_pairing_mollify
    {f F A : Space n → ℝ} {i : Fin n}
    (hF : HasLocalWeakCoordinateDerivative f F i)
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f)
    (hFloc : ∀ S : Set (Space n), IsCompact S → MemLp F 2 (volume.restrict S))
    (hA : ∀ S : Set (Space n), IsCompact S → MemLp A 2 (volume.restrict S)) :
    Integrable (fun x => A x*F x) ∧
      Tendsto (fun k => ∫ x, A x*coordinateDerivative (mollify k f) i x)
        atTop (𝓝 (∫ x, A x*F x)) := by
  obtain ⟨G,hG,hGe⟩ := hF.global_of_compact (fun S _ => hf.restrict S) hFloc hc
  have hp := hG.localL2_pairing_mollify hf hc hA
  have he : (fun x => A x*G x) =ᵐ[volume] (fun x => A x*F x) := by
    filter_upwards [hGe] with x hx
    rw [hx]
  exact ⟨hp.1.congr he, by simpa only [integral_congr_ae he] using hp.2⟩

end KLS
end
