import KLS.SuspensionProductDensity

/-! Concrete volume-preserving coordinates for the independent copies and the
extra scalar. The target is the actual Euclidean Space in its genuine dimension. -/

open MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
namespace KLS

lemma measurePreserving_uncurry_generic {I J E : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : I → J → Measure E) [∀ i j, SigmaFinite (μ i j)] :
    MeasurePreserving (MeasurableEquiv.curry I J E).symm
      (Measure.pi (fun i => Measure.pi (μ i))) (Measure.pi (fun p : I × J => μ p.1 p.2)) := by
  refine ⟨(MeasurableEquiv.curry I J E).symm.measurable, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  rw [(MeasurableEquiv.curry I J E).symm.measurableEmbedding.map_apply]
  have he : (MeasurableEquiv.curry I J E).symm ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i, j))) := by
    ext x
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left]
    exact ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  simpa only [Finset.univ_product_univ] using
    (Finset.prod_product Finset.univ Finset.univ (fun p : I × J => μ p.1 p.2 (s p))).symm

abbrev SuspensionIndex (n N : ℕ) := Option (Fin N × Fin n)
abbrev suspensionDimension (n N : ℕ) := Fintype.card (SuspensionIndex n N)

def suspensionCopiesEquiv (n N : ℕ) :
    (Fin N → Space n) ≃ᵐ (Fin N × Fin n → ℝ) :=
  (MeasurableEquiv.piCongrRight (fun _ : Fin N =>
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm)).trans
      (MeasurableEquiv.curry (Fin N) (Fin n) ℝ).symm

lemma measurePreserving_suspensionCopiesEquiv (n N : ℕ) :
    MeasurePreserving (suspensionCopiesEquiv n N) volume volume := by
  exact (measurePreserving_uncurry_generic (fun _ : Fin N => fun _ : Fin n =>
    (volume : Measure ℝ))).comp (volume_preserving_pi
      (fun _ : Fin N => PiLp.volume_preserving_ofLp (Fin n)))

def suspensionCoordinates (n N : ℕ) :
    ((Fin N → Space n) × ℝ) ≃ᵐ Space (suspensionDimension n N) :=
  ((suspensionCopiesEquiv n N).prodCongr (MeasurableEquiv.refl ℝ)).trans
    ((MeasurableEquiv.piOptionEquivProd (fun _ : SuspensionIndex n N => ℝ)).symm.trans
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin (suspensionDimension n N) => ℝ)
        (Fintype.equivFin (SuspensionIndex n N))).trans
          (MeasurableEquiv.toLp 2 (Fin (suspensionDimension n N) → ℝ))))

lemma measurePreserving_suspensionCoordinates (n N : ℕ) :
    MeasurePreserving (suspensionCoordinates n N) volume volume := by
  have hoption : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : SuspensionIndex n N => ℝ)).symm
      volume volume :=
    ⟨(MeasurableEquiv.piOptionEquivProd _).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun _ => volume)⟩
  exact (PiLp.volume_preserving_toLp (Fin (suspensionDimension n N))).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (suspensionDimension n N) => ℝ)
      (Fintype.equivFin (SuspensionIndex n N))).comp
        (hoption.comp ((measurePreserving_suspensionCopiesEquiv n N).prod
          (MeasurePreserving.id volume))))


lemma suspensionCoordinates_apply (n N : ℕ) (p : (Fin N → Space n) × ℝ)
    (a : SuspensionIndex n N) :
    suspensionCoordinates n N p (Fintype.equivFin _ a) =
      Option.elim a p.2 (fun ij => p.1 ij.1 ij.2) := by
  simp only [suspensionCoordinates, MeasurableEquiv.trans_apply]
  change ((MeasurableEquiv.piCongrLeft (fun _ : Fin (suspensionDimension n N) => ℝ)
    (Fintype.equivFin (SuspensionIndex n N))) _ (Fintype.equivFin _ a)) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  cases a <;> rfl

lemma suspensionCoordinates_symm_fst (n N : ℕ) (z : Space (suspensionDimension n N))
    (i : Fin N) (j : Fin n) :
    ((suspensionCoordinates n N).symm z).1 i j =
      z (Fintype.equivFin _ (some (i, j))) := rfl

lemma suspensionCoordinates_symm_snd (n N : ℕ) (z : Space (suspensionDimension n N)) :
    ((suspensionCoordinates n N).symm z).2 = z (Fintype.equivFin _ none) := rfl

/-- The inverse coordinate map, in the scalar-first order of the potential,
is an actual linear map. This proves that it preserves convex combinations. -/
def suspensionInverseLinear (n N : ℕ) :
    Space (suspensionDimension n N) →ₗ[ℝ] ℝ × (Fin N → Space n) where
  toFun z := (((suspensionCoordinates n N).symm z).2,
    ((suspensionCoordinates n N).symm z).1)
  map_add' x y := by
    apply Prod.ext
    · rfl
    · ext i j
      rfl
  map_smul' a x := by
    apply Prod.ext
    · rfl
    · ext i j
      rfl

def euclideanSuspensionLaw {n N : ℕ} (μ : Measure (Space n))
    (f : Space n → ℝ) (β σ c : ℝ) : Measure (Space (suspensionDimension n N)) :=
  (laplaceSuspensionLaw (Measure.pi (fun _ : Fin N => μ))
    (fun x => c * ∑ i, f (x i)) β σ).map (suspensionCoordinates n N)

lemma euclideanSuspensionLaw_eq_withDensity {n N : ℕ} {V f : Space n → ℝ}
    (hV : Measurable V) (hf : Measurable f) [IsProbabilityMeasure (potentialMeasure V)]
    {β σ c : ℝ} (hσ : 0 < σ) :
    euclideanSuspensionLaw (N := N) (potentialMeasure V) f β σ c =
      volume.withDensity (fun z => ENNReal.ofReal (σ * β / 2 * Real.exp
        (-suspensionPotential V f β σ c (suspensionInverseLinear n N z)))) := by
  rw [euclideanSuspensionLaw, laplaceSuspensionLaw_potential_density hV hf hσ,
    map_withDensity_measurableEquiv (suspensionCoordinates n N) _ _ (by
      unfold suspensionPotential
      fun_prop), (measurePreserving_suspensionCoordinates n N).map_eq]
  rfl

lemma isProbabilityMeasure_euclideanSuspensionLaw {n N : ℕ} (μ : Measure (Space n))
    [IsProbabilityMeasure μ] (f : Space n → ℝ) (hf : Measurable f) {β σ c : ℝ}
    (hβ : 0 < β) : IsProbabilityMeasure (euclideanSuspensionLaw (N := N) μ f β σ c) := by
  have : IsProbabilityMeasure (laplaceSuspensionLaw (Measure.pi (fun _ : Fin N => μ))
      (fun x => c * ∑ i, f (x i)) β σ) :=
    isProbabilityMeasure_laplaceSuspensionLaw _ _ (by fun_prop) hβ
  unfold euclideanSuspensionLaw
  exact (Measure.isProbabilityMeasure_map_iff (suspensionCoordinates n N).measurable.aemeasurable).2
    inferInstance

end KLS
end
#print axioms KLS.measurePreserving_suspensionCoordinates
#print axioms KLS.euclideanSuspensionLaw_eq_withDensity
#print axioms KLS.isProbabilityMeasure_euclideanSuspensionLaw
