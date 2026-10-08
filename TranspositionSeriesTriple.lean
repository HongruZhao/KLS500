import TranspositionLocalGap

open scoped BigOperators RealInnerProductSpace
noncomputable section
namespace KLS.ConstantReduction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem triple_transposition_series
    (ρ : Equiv.Perm (Fin 3) →* (E ≃ₗᵢ[ℝ] E)) (x : E)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    a*b*‖x-ρ (Equiv.swap 0 2) x‖^2 ≤
      (a+b)*(a*‖x-ρ (Equiv.swap 0 1) x‖^2+
        b*‖x-ρ (Equiv.swap 1 2) x‖^2) := by
  let s : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let t : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let u : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let v := x-ρ s x
  let w := ρ (t*s) x-ρ u x
  let Z := inner ℝ x (characterIsometrySum (realPermutationSign (Fin 3)) ρ x)
  have hmul (g h : Equiv.Perm (Fin 3)) : ρ g (ρ h x)=ρ (g*h) x := by
    rw [map_mul]
    rfl
  have hsu : s*u=t*s := by decide
  have hsts : s*(t*s)=u := by decide
  have htst : (t*s)*t=u := by decide
  have hw : w=ρ (t*s) (x-ρ t x) := by
    rw [map_sub,hmul,htst]
  have hwn : ‖w‖^2=‖x-ρ t x‖^2 := by rw [hw,LinearIsometryEquiv.norm_map]
  have hcycle : inner ℝ x (ρ (s*t) x)=inner ℝ x (ρ (t*s) x) := by
    rw [←hmul,←hmul]
    have hs := inner_transposition_action ρ x (ρ t x) (0 : Fin 3) 1
    have ht := inner_transposition_action ρ x (ρ s x) (1 : Fin 3) 2
    change inner ℝ (ρ s x) (ρ t x)=inner ℝ x (ρ s (ρ t x)) at hs
    change inner ℝ (ρ t x) (ρ s x)=inner ℝ x (ρ t (ρ s x)) at ht
    rw [←hs,real_inner_comm,ht]
  have hcross : inner ℝ v w=
      2*inner ℝ x (ρ (t*s) x)-2*inner ℝ x (ρ u x) := by
    have hs1 := inner_transposition_action ρ x (ρ (t*s) x) (0 : Fin 3) 1
    have hs2 := inner_transposition_action ρ x (ρ u x) (0 : Fin 3) 1
    change inner ℝ (ρ s x) (ρ (t*s) x)=inner ℝ x (ρ s (ρ (t*s) x)) at hs1
    change inner ℝ (ρ s x) (ρ u x)=inner ℝ x (ρ s (ρ u x)) at hs2
    rw [hmul,hsts] at hs1
    rw [hmul,hsu] at hs2
    dsimp only [v,w]
    rw [inner_sub_left,inner_sub_right,inner_sub_right,hs1,hs2]
    ring
  have hZ : Z=‖x‖^2-inner ℝ x (ρ s x)-inner ℝ x (ρ u x)-
      inner ℝ x (ρ t x)+2*inner ℝ x (ρ (t*s) x) := by
    dsimp only [Z]
    rw [triple_sign_sum]
    simp only [inner_add_right,inner_sub_right,real_inner_self_eq_norm_sq]
    change ‖x‖^2-inner ℝ x (ρ s x)-inner ℝ x (ρ u x)-inner ℝ x (ρ t x)+
      inner ℝ x (ρ (s*t) x)+inner ℝ x (ρ (t*s) x)=_
    rw [hcycle]
    ring
  have hv : ‖v‖^2=2*(‖x‖^2-inner ℝ x (ρ s x)) := by
    dsimp only [v]
    rw [norm_sub_sq_real,LinearIsometryEquiv.norm_map]
    ring
  have ht : ‖x-ρ t x‖^2=2*(‖x‖^2-inner ℝ x (ρ t x)) := by
    rw [norm_sub_sq_real,LinearIsometryEquiv.norm_map]
    ring
  have hu : ‖x-ρ u x‖^2=2*(‖x‖^2-inner ℝ x (ρ u x)) := by
    rw [norm_sub_sq_real,LinearIsometryEquiv.norm_map]
    ring
  have hid : inner ℝ v w=Z-(‖v‖^2+‖x-ρ t x‖^2-‖x-ρ u x‖^2)/2 := by
    rw [hcross,hZ,hv,ht,hu]
    ring
  have hnorm : ‖a • v-b • w‖^2 =
      a^2*‖v‖^2+b^2*‖x-ρ t x‖^2-2*a*b*inner ℝ v w := by
    rw [norm_sub_sq_real,norm_smul,norm_smul,inner_smul_left,inner_smul_right]
    simp only [Real.norm_eq_abs,conj_trivial,mul_pow,sq_abs]
    rw [hwn]
    ring
  have hpositive : 0≤Z := characterIsometrySum_inner_nonneg
    (realPermutationSign (Fin 3)) realPermutationSign_square ρ x
  have hz : 0≤a*b*Z := mul_nonneg (mul_nonneg ha hb) hpositive
  have hn := sq_nonneg ‖a • v-b • w‖
  rw [hnorm,hid] at hn
  change a*b*‖x-ρ u x‖^2 ≤ (a+b)*(a*‖v‖^2+b*‖x-ρ t x‖^2)
  nlinarith

end KLS.ConstantReduction
end
