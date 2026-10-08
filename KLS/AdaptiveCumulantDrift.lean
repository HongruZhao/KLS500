import KLS.AdaptiveCumulantContraction
import KLS.CumulantSubsetPairing

/-! The literal lower-cumulant drift, with one representative of each complementary pair. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace KLS.AdaptiveLocalization
open KLS.StandardLocalization
variable {n m : ℕ} {μ : Measure (Space n)} [IsProbabilityMeasure μ]

def cumulantSubsetTerm (μ : Measure (Space n)) (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ k : Fin n, cumulantNoiseWord μ z k (maskedDirections h (fun i => decide (i ∈ S))) *
    cumulantNoiseWord μ z k (maskedDirections h (fun i => decide (i ∈ Sᶜ)))

theorem cumulantSubsetTerm_complement (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) (S : Finset (Fin m)) :
    cumulantSubsetTerm μ h z Sᶜ = cumulantSubsetTerm μ h z S := by
  simp only [cumulantSubsetTerm, compl_compl]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem cumulantSubsetTerm_empty (h : Fin m → Space n) (z : Fin (n+n*n) → ℝ) :
    cumulantSubsetTerm μ h z ∅ = 0 := by
  simp [cumulantSubsetTerm, maskedDirections_none, cumulantNoiseWord]

theorem cumulantSubsetTerm_singleton (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hm : 3 ≤ m)
    (h : Fin m → Space n) (z : Fin (n+n*n) → ℝ) (i : Fin m) :
    cumulantSubsetTerm μ h z {i} = coordinateCumulant μ m h z := by
  let vs := maskedDirections h (fun j => !(decide (j = i)))
  have hne : vs ≠ [] := by
    have hl := maskedDirections_length h (fun j => !(decide (j = i)))
    have hs : maskSet (fun j => !(decide (j = i))) = ({i} : Finset (Fin m))ᶜ := by
      ext j
      simp
    rw [hs, Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at hl
    intro hh
    have hz : vs.length = 0 := by rw [hh]; rfl
    change vs.length = _ at hl
    omega
  have hp : (h i :: vs).Perm (List.ofFn h) := by
    have hp := maskedDirections_append_complement h (fun j => decide (j = i))
    simpa only [maskedDirections_singleton, List.singleton_append] using hp
  dsimp only [vs] at hne
  have he : cumulantSubsetTerm μ h z {i} =
      ∑ k : Fin n, listCumulant (law μ (decodeState z).1 (decodeState z).2)
        [inverseSqrtDirection μ z k, h i] *
        listCumulant (law μ (decodeState z).1 (decodeState z).2)
          (inverseSqrtDirection μ z k :: vs) := by
    simp only [cumulantSubsetTerm, Finset.mem_singleton, Finset.mem_compl, decide_not,
      maskedDirections_singleton, cumulantNoiseWord, hne, List.cons_ne_self, ↓reduceIte]
    rfl
  rw [he, cumulant_singleton_contraction hμ hfull]
  letI := law_isProbability hμ (decodeState z).1 (decodeState z).2
  have hν : IsCompact (law μ (decodeState z).1 (decodeState z).2).support := by rwa [support_law hμ]
  rw [listCumulant_perm hν hp, listCumulant_eq_word hν,
    directionalWordDerivative_ofFn (contDiff_tiltLogLaplace hν)]
  rfl

/-- The paper's L_m: only cumulants of orders 3 through m-1 occur.
The first argument is represented by any chosen distinguished index i₀. -/
def lowerCumulantDrift (μ : Measure (Space n)) (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) (i₀ : Fin m) : ℝ :=
  ∑ S : Finset (Fin m), if i₀ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ m-2 then
    ∑ k : Fin n,
      listCumulant (law μ (decodeState z).1 (decodeState z).2)
        (inverseSqrtDirection μ z k :: maskedDirections h (fun i => decide (i ∈ S))) *
      listCumulant (law μ (decodeState z).1 (decodeState z).2)
        (inverseSqrtDirection μ z k :: maskedDirections h (fun i => decide (i ∈ Sᶜ)))
    else 0

theorem lowerCumulantDrift_eq_middle (h : Fin m → Space n)
    (z : Fin (n+n*n) → ℝ) (i₀ : Fin m) :
    lowerCumulantDrift μ h z i₀ = ∑ S : Finset (Fin m),
      if i₀ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ m-2 then cumulantSubsetTerm μ h z S else 0 := by
  unfold lowerCumulantDrift
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : i₀ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ m-2
  · simp only [hS, ite_true]
    have hc : S.card + Sᶜ.card = m := by simp
    have ha : maskedDirections h (fun i => decide (i ∈ S)) ≠ [] := by
      rw [ne_eq, maskedDirections_eq_nil_iff]
      have hs : maskSet (fun i => decide (i ∈ S)) = S := by ext i; simp
      rw [hs]
      intro he
      have hz := congrArg Finset.card he
      simp only [Finset.card_empty] at hz
      omega
    have hb : maskedDirections h (fun i => decide (i ∈ Sᶜ)) ≠ [] := by
      rw [ne_eq, maskedDirections_eq_nil_iff]
      have hs : maskSet (fun i => decide (i ∈ Sᶜ)) = Sᶜ := by ext i; simp
      rw [hs]
      intro he
      have hz := congrArg Finset.card he
      simp only [Finset.card_empty] at hz
      omega
    simp only [cumulantSubsetTerm, cumulantNoiseWord, ha, hb, ite_false]
  · simp only [hS, ite_false]

/-- Exact deterministic drift in equation (73), obtained from the actual coefficients. -/
theorem cumulantGenerator_eq_neg_order_add_lower (hμ : IsCompact μ.support)
    (hfull : affineSpan ℝ μ.support = ⊤) (hm : 3 ≤ m)
    (h : Fin m → Space n) (z : Fin (n+n*n) → ℝ) (i₀ : Fin m) :
    cumulantGenerator μ m h z =
      -((m : ℝ) * coordinateCumulant μ m h z + lowerCumulantDrift μ h z i₀) := by
  have hg := cumulantGenerator_eq_mask_sum hμ hfull (by omega : m ≠ 0) h z
  rw [Finset.sum_comm] at hg
  have hsum : (∑ s : Fin m → Bool, ∑ k : Fin n,
      cumulantNoiseWord μ z k (maskedDirections h s) *
      cumulantNoiseWord μ z k (maskedDirections h (fun i => !(s i)))) =
      ∑ S : Finset (Fin m), cumulantSubsetTerm μ h z S := by
    have he := (maskFinsetEquiv m).symm.sum_comp (fun s : Fin m → Bool => ∑ k : Fin n,
      cumulantNoiseWord μ z k (maskedDirections h s) *
      cumulantNoiseWord μ z k (maskedDirections h (fun i => !(s i))))
    have happly (S : Finset (Fin m)) : (maskFinsetEquiv m).symm S = fun i => decide (i ∈ S) := rfl
    simp only [happly] at he
    simpa only [cumulantSubsetTerm, Finset.mem_compl, decide_not] using he.symm
  rw [hsum] at hg
  have hp := half_sum_subsets_eq_singletons_and_middle hm (cumulantSubsetTerm μ h z)
    (coordinateCumulant μ m h z) (cumulantSubsetTerm_empty h z)
    (cumulantSubsetTerm_complement h z) (cumulantSubsetTerm_singleton hμ hfull hm h z) i₀
  rw [← lowerCumulantDrift_eq_middle] at hp
  linarith

end KLS.AdaptiveLocalization
end
#print axioms KLS.AdaptiveLocalization.cumulantGenerator_eq_neg_order_add_lower
