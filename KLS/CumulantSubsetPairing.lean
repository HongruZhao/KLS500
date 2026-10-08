import KLS.MaskedDirections

/-! Complement pairing and the exact singleton multiplicity in the cumulant drift. -/
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KLS
variable {m : ℕ}

def finsetComplementEquiv (m : ℕ) : Finset (Fin m) ≃ Finset (Fin m) :=
  { toFun := fun S => Sᶜ
    invFun := fun S => Sᶜ
    left_inv := fun S => compl_compl S
    right_inv := fun S => compl_compl S }

theorem sum_subsets_complement (f : Finset (Fin m) → ℝ) :
    (∑ S : Finset (Fin m), f Sᶜ) = ∑ S : Finset (Fin m), f S :=
  (finsetComplementEquiv m).sum_comp f

theorem sum_subsets_card_one (c : ℝ) :
    (∑ S : Finset (Fin m), if S.card = 1 then c else 0) = m*c := by
  classical
  have hs : Finset.univ.filter (fun S : Finset (Fin m) => S.card = 1) =
      Finset.univ.image (fun i : Fin m => ({i} : Finset (Fin m))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hS
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS
      exact ⟨i, rfl⟩
    · rintro ⟨i, _, rfl⟩
      simp
  rw [← Finset.sum_filter, hs, Finset.sum_image]
  · simp
  · intro a _ b _ hab
    simpa using hab

theorem sum_complement_symmetric_pairing (f : Finset (Fin m) → ℝ)
    (hsym : ∀ S, f Sᶜ = f S) (i : Fin m) :
    (∑ S : Finset (Fin m), f S) =
      2 * ∑ S : Finset (Fin m), if i ∈ S then f S else 0 := by
  let g : Finset (Fin m) → ℝ := fun S => if i ∈ S then f S else 0
  have he (S : Finset (Fin m)) : f S = g S + g Sᶜ := by
    by_cases hi : i ∈ S <;> simp [g, hi, hsym]
  calc
    (∑ S, f S) = ∑ S, (g S + g Sᶜ) := Finset.sum_congr rfl fun S _ => he S
    _ = 2 * ∑ S, g S := by rw [Finset.sum_add_distrib, sum_subsets_complement]; ring

/-- There are exactly m singleton terms after complement pairing. Every remaining
proper term is represented by the subset containing the distinguished first index. -/
theorem half_sum_subsets_eq_singletons_and_middle (hm : 3 ≤ m)
    (f : Finset (Fin m) → ℝ) (c : ℝ)
    (hzero : f ∅ = 0) (hsym : ∀ S, f Sᶜ = f S)
    (hsingle : ∀ i : Fin m, f {i} = c) (i₀ : Fin m) :
    (1/2) * (∑ S : Finset (Fin m), f S) = m*c +
      ∑ S : Finset (Fin m),
        if i₀ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ m-2 then f S else 0 := by
  classical
  have hfull : f Finset.univ = 0 := by simpa using (hsym ∅).trans hzero
  have hdecomp (S : Finset (Fin m)) :
      f S = (if S.card = 1 then c else 0) +
        (if Sᶜ.card = 1 then c else 0) +
        (if 2 ≤ S.card ∧ 2 ≤ Sᶜ.card then f S else 0) := by
    have hc : S.card + Sᶜ.card = m := by simpa using Finset.card_add_card_compl S
    by_cases hA0 : S.card = 0
    · have hS : S = ∅ := Finset.card_eq_zero.mp hA0
      subst S
      have hn : m ≠ 1 := by omega
      simp [hzero, hn]
    by_cases hB0 : Sᶜ.card = 0
    · have hS : S = Finset.univ := by
        have hh := Finset.card_eq_zero.mp hB0
        simpa using congrArg (fun A : Finset (Fin m) => Aᶜ) hh
      subst S
      have hn : m ≠ 1 := by omega
      simp [hfull, hn]
    by_cases hA : S.card = 1
    · obtain ⟨i, hS⟩ := Finset.card_eq_one.mp hA
      have hf : f S = c := by rw [hS]; exact hsingle i
      have hB : Sᶜ.card ≠ 1 := by omega
      have hA2 : ¬ 2 ≤ S.card := by omega
      simp [hA, hB, hA2, hf]
    by_cases hB : Sᶜ.card = 1
    · obtain ⟨i, hS⟩ := Finset.card_eq_one.mp hB
      have hf : f S = c := by rw [← hsym S, hS]; exact hsingle i
      have hB2 : ¬ 2 ≤ Sᶜ.card := by omega
      simp [hA, hB, hB2, hf]
    have hA2 : 2 ≤ S.card := by omega
    have hB2 : 2 ≤ Sᶜ.card := by omega
    simp [hA, hB, hA2, hB2]
  let g : Finset (Fin m) → ℝ := fun S =>
    if 2 ≤ S.card ∧ 2 ≤ Sᶜ.card then f S else 0
  have hgsym (S : Finset (Fin m)) : g Sᶜ = g S := by
    simp only [g, compl_compl, hsym S, and_comm]
  have hsum : (∑ S : Finset (Fin m), f S) = 2*(m*c) + ∑ S, g S := by
    calc
      (∑ S, f S) = ∑ S, ((if S.card = 1 then c else 0) +
          (if Sᶜ.card = 1 then c else 0) + g S) :=
        Finset.sum_congr rfl fun S _ => hdecomp S
      _ = 2*(m*c) + ∑ S, g S := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          sum_subsets_card_one, sum_subsets_complement (fun S : Finset (Fin m) => if S.card = 1 then c else 0), sum_subsets_card_one]
        ring
  have hpair := sum_complement_symmetric_pairing g hgsym i₀
  have hmiddle : (∑ S : Finset (Fin m), if i₀ ∈ S then g S else 0) =
      ∑ S : Finset (Fin m),
        if i₀ ∈ S ∧ 2 ≤ S.card ∧ S.card ≤ m-2 then f S else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    have hc : S.card + Sᶜ.card = m := by simpa using Finset.card_add_card_compl S
    have he : 2 ≤ Sᶜ.card ↔ S.card ≤ m-2 := by omega
    by_cases hi : i₀ ∈ S <;> simp [g, hi, he]
  rw [hsum, hpair, hmiddle]
  ring

end KLS
end
#print axioms KLS.half_sum_subsets_eq_singletons_and_middle
