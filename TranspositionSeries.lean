import TranspositionSeriesTriple

noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem transpositionDefect_series {I : Type*} [DecidableEq I]
    (ρ : Equiv.Perm I →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    (i k j : I) (hik : i≠k) (hij : i≠j) (hkj : k≠j)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    a*b*‖x-ρ (Equiv.swap i j) x‖^2 ≤
      (a+b)*(a*‖x-ρ (Equiv.swap i k) x‖^2+
        b*‖x-ρ (Equiv.swap k j) x‖^2) := by
  let ι : Fin 3 ↪ I := ⟨![i,k,j], by
    intro c d hcd
    fin_cases c <;> fin_cases d <;> simp_all⟩
  have hh := triple_transposition_series (ρ.comp (Equiv.Perm.viaEmbeddingHom ι)) x ha hb
  simp only [MonoidHom.comp_apply,viaEmbeddingHom_swap] at hh
  have h0 : ι 0=i := rfl
  have h1 : ι 1=k := rfl
  have h2 : ι 2=j := rfl
  rw [h0,h1,h2] at hh
  exact hh

end KLS.ConstantReduction
end
