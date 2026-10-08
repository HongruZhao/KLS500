import TranspositionSeries
import KLS.FinitePermutationWords

open scoped BigOperators
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The series inequality gives the distance times the adjacent path energy. -/
theorem transpositionDefect_le_moving_particle_path {q : ℕ}
    (ρ : Equiv.Perm (Fin (q+1)) →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (i j : Fin (q+1)) (hij : i≤j) :
    ‖x-ρ (Equiv.swap i j) x‖^2 ≤
      ((((j : ℕ)-(i : ℕ)) : ℕ) : ℝ)*
        ∑ s : Fin q, if (i : ℕ)≤s ∧ (s : ℕ)<j then
          ‖x-ρ (adjacentFinSwap q s) x‖^2 else 0 := by
  have hmain : ∀ d : ℕ, ∀ i j : Fin (q+1), (j : ℕ)=(i : ℕ)+d →
      ‖x-ρ (Equiv.swap i j) x‖^2 ≤ (d : ℝ)*
        ∑ s : Fin q, if (i : ℕ)≤s ∧ (s : ℕ)<j then
          ‖x-ρ (adjacentFinSwap q s) x‖^2 else 0 := by
    intro d
    induction d with
    | zero =>
      intro i j hlen
      have he : i=j := Fin.ext (by omega)
      subst j
      have hx : ρ (Equiv.swap i i) x=x := by
        rw [Equiv.swap_self]
        change ρ 1 x=x
        simp
      rw [hx]
      simp
    | succ d ih =>
      intro i j hlen
      let k : Fin q := ⟨(j : ℕ)-1, by omega⟩
      have hk : (k : ℕ)=(j : ℕ)-1 := rfl
      have hki : (k : ℕ)=(i : ℕ)+d := by omega
      have hkj : k.succ=j := Fin.ext (by simp only [Fin.val_succ]; omega)
      by_cases hd : d=0
      · subst d
        have hki' : k.castSucc=i := Fin.ext (by simp only [Fin.val_castSucc]; omega)
        have hs : (∑ s : Fin q, if (i : ℕ)≤s ∧ (s : ℕ)<j then
            ‖x-ρ (adjacentFinSwap q s) x‖^2 else 0)=
            ‖x-ρ (adjacentFinSwap q k) x‖^2 := by
          have he (s : Fin q) : ((i : ℕ)≤s ∧ (s : ℕ)<j) ↔ s=k := by
            constructor
            · intro h
              apply Fin.ext
              omega
            · intro h
              subst s
              omega
          simp_rw [he]
          simp
        rw [hs]
        simp only [Nat.zero_add,Nat.cast_one,one_mul,adjacentFinSwap,hki',hkj]
        exact le_rfl
      · have hd0 : (0 : ℝ)<d := by exact_mod_cast (show 0<d by omega)
        have hip : i≠k.castSucc := by
          intro h
          have he := congrArg Fin.val h
          simp only [Fin.val_castSucc] at he
          omega
        have hij' : i≠j := by
          intro h
          have he := congrArg Fin.val h
          omega
        have hkj' : k.castSucc≠j := by
          intro h
          have he := congrArg Fin.val h
          simp only [Fin.val_castSucc] at he
          omega
        have hp := ih i k.castSucc (by simpa only [Fin.val_castSucc] using hki)
        have hseries := transpositionDefect_series ρ x i k.castSucc j hip hij' hkj'
          (a:=1/(d : ℝ)) (b:=1) (by positivity) (by norm_num)
        have he : ‖x-ρ (Equiv.swap k.castSucc j) x‖^2 =
            ‖x-ρ (adjacentFinSwap q k) x‖^2 := by
          rw [←hkj]
          rfl
        rw [he] at hseries
        have hm := mul_le_mul_of_nonneg_left hseries (sq_nonneg (d : ℝ))
        have hseries' : (d : ℝ)*‖x-ρ (Equiv.swap i j) x‖^2 ≤
            ((d : ℝ)+1)*(‖x-ρ (Equiv.swap i k.castSucc) x‖^2+
              (d : ℝ)*‖x-ρ (adjacentFinSwap q k) x‖^2) := by
          convert hm using 1 <;> field_simp [ne_of_gt hd0]
          ring
        have hs : (∑ s : Fin q, if (i : ℕ)≤s ∧ (s : ℕ)<j then
            ‖x-ρ (adjacentFinSwap q s) x‖^2 else 0)=
            (∑ s : Fin q, if (i : ℕ)≤s ∧ (s : ℕ)<k.castSucc then
              ‖x-ρ (adjacentFinSwap q s) x‖^2 else 0)+
            ‖x-ρ (adjacentFinSwap q k) x‖^2 := by
          have he (s : Fin q) :
              (if (i : ℕ)≤s ∧ (s : ℕ)<j then ‖x-ρ (adjacentFinSwap q s) x‖^2 else 0)=
              (if (i : ℕ)≤s ∧ (s : ℕ)<k.castSucc then ‖x-ρ (adjacentFinSwap q s) x‖^2 else 0)+
              (if s=k then ‖x-ρ (adjacentFinSwap q k) x‖^2 else 0) := by
            by_cases hsk : s=k
            · subst s
              rw [ite_eq_left (by omega),ite_eq_right (by simp),ite_eq_left rfl,zero_add]
            · have hne : (s : ℕ)≠(k : ℕ) := by
                intro h
                exact hsk (Fin.ext h)
              have hh : ((i : ℕ)≤s ∧ (s : ℕ)<j) ↔ ((i : ℕ)≤s ∧ (s : ℕ)<k.castSucc) := by
                simp only [Fin.val_castSucc]
                omega
              simp only [hh,hsk,↓reduceIte,add_zero]
          simp_rw [he]
          rw [Finset.sum_add_distrib]
          simp
        have hbound := hseries'.trans (mul_le_mul_of_nonneg_left
          (add_le_add hp (le_refl ((d : ℝ)*‖x-ρ (adjacentFinSwap q k) x‖^2))) (by positivity))
        apply le_of_mul_le_mul_left (a:=(d : ℝ)) ?_ hd0
        calc
          _ ≤ _ := hbound
          _ = _ := by rw [hs]; push_cast; ring
  exact hmain ((j : ℕ)-(i : ℕ)) i j (by omega)

end KLS.ConstantReduction
end
