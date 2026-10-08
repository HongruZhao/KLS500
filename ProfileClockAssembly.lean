import EntropyClock
import ProfileResolventNumerics

noncomputable section
namespace KLS.ConstantReduction

theorem profileClock_step_factor {t H : ℝ} (ht : 0 < t) :
    t*H/Real.sqrt (t/(101/100 : ℝ)) =
      H*Real.sqrt (101/100 : ℝ)*Real.sqrt t := by
  rw [Real.sqrt_div ht.le]
  have hr : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have hq : Real.sqrt (101/100 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt ht.le]
  ring

theorem profileClock_tail_allocation {C B t : ℝ} {N k : ℕ}
    (hC : 0 < C) (hB : 0 ≤ B) (ht : 0 < t)
    (hk : k ≤ N) (htime : t*(N : ℝ)=5*C/4) :
    2*(t*((87/100 : ℝ)*B)/Real.sqrt (t/(101/100 : ℝ)))*
        Real.sqrt (k : ℝ)/Real.sqrt (99/50 : ℝ) ≤
      (139/100 : ℝ)*B*Real.sqrt C := by
  have hn : 0 ≤ (N : ℝ) := by positivity
  have hsqrt : Real.sqrt (k : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have hmul := mul_le_mul_of_nonneg_left hsqrt
    (show 0 ≤ 2*(t*((87/100 : ℝ)*B)/Real.sqrt (t/(101/100 : ℝ)))/
        Real.sqrt (99/50 : ℝ) by positivity)
  have hbound := mul_le_mul_of_nonneg_right
    polynomial_profile_displacement_scalar_certificate
    (show 0 ≤ B*Real.sqrt C by positivity)
  have he : 2*(t*((87/100 : ℝ)*B)/Real.sqrt (t/(101/100 : ℝ)))*
      Real.sqrt (N : ℝ)/Real.sqrt (99/50 : ℝ) =
        (2*(87/100 : ℝ)*Real.sqrt ((101/100 : ℝ)*(5/4)/(99/50)))*
          (B*Real.sqrt C) := by
    rw [profileClock_step_factor ht]
    have htime' : Real.sqrt t*Real.sqrt (N : ℝ) =
        Real.sqrt (5/4 : ℝ)*Real.sqrt C := by
      rw [← Real.sqrt_mul ht.le, htime,
        show 5*C/4=(5/4 : ℝ)*C by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5/4)]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ (101/100 : ℝ)*(5/4)),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 101/100)]
    calc
      _ = (2*(87/100 : ℝ)*B*Real.sqrt (101/100 : ℝ)/
          Real.sqrt (99/50 : ℝ))*(Real.sqrt t*Real.sqrt (N : ℝ)) := by ring
      _ = _ := by rw [htime']; ring
  calc
    _ ≤ 2*(t*((87/100 : ℝ)*B)/Real.sqrt (t/(101/100 : ℝ)))*
        Real.sqrt (N : ℝ)/Real.sqrt (99/50 : ℝ) := by convert hmul using 1 <;> ring
    _ = _ := he
    _ ≤ _ := by convert hbound using 1; ring

theorem profileClock_finite_step_parameters {C B M D : ℝ}
    (hC : 0 < C) (hB : 0 < B) (_hM : 0 ≤ M) (_hD : 0 < D) :
    ∃ m : ℕ, 1 ≤ m ∧
      let N := 128*m
      let t := 5*C/(512*(m : ℝ))
      let s := t/(101/100 : ℝ)
      0 < t ∧ 0 < s ∧ 51 ≤ N ∧
      t*D ≤ B/2000 ∧ 51*t*M ≤ B*Real.sqrt C/200 ∧
      51*t*M+2*(t*((87/100 : ℝ)*B)/Real.sqrt s)*
        Real.sqrt ((N-51 : ℕ) : ℝ)/Real.sqrt (99/50 : ℝ) ≤
          (279/200 : ℝ)*B*Real.sqrt C := by
  let A := 10000*C*D/(512*B)
  let P := 51000*C*M/(512*B*Real.sqrt C)
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (max A P))
  have hmR : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hmN : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
  have hAm : A ≤ (m : ℝ) := (le_max_left A P).trans ((le_max_right 1 (max A P)).trans hm.le)
  have hPm : P ≤ (m : ℝ) := (le_max_right A P).trans ((le_max_right 1 (max A P)).trans hm.le)
  have hlag : (5*C/(512*(m : ℝ)))*D ≤ B/2000 := by
    have hmul : 10000*C*D ≤ (m : ℝ)*(512*B) :=
      (div_le_iff₀ (by positivity : 0 < 512*B)).mp hAm
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 512*(m : ℝ))).mpr
    nlinarith only [hmul]
  have hprefix : 51*(5*C/(512*(m : ℝ)))*M ≤ B*Real.sqrt C/200 := by
    have hmul : 51000*C*M ≤ (m : ℝ)*(512*B*Real.sqrt C) :=
      (div_le_iff₀ (by positivity : 0 < 512*B*Real.sqrt C)).mp hPm
    rw [show 51*(5*C/(512*(m : ℝ)))*M=(255*C*M)/(512*(m : ℝ)) by ring]
    apply (div_le_iff₀ (by positivity : 0 < 512*(m : ℝ))).mpr
    nlinarith only [hmul]
  have ht : 0 < 5*C/(512*(m : ℝ)) := by positivity
  have htime : (5*C/(512*(m : ℝ)))*((128*m : ℕ) : ℝ)=5*C/4 := by
    push_cast
    field_simp
    ring
  have htail := profileClock_tail_allocation hC hB.le ht
    (Nat.sub_le (128*m) 51) htime
  refine ⟨m,hmN,ht,by positivity,by omega,hlag,hprefix,?_⟩
  nlinarith only [hprefix,htail]

theorem profileClock_finite_time_identity {C : ℝ} {m : ℕ}
    (hm : 1 ≤ m) :
    (5*C/(512*(m : ℝ)))*((128*m : ℕ) : ℝ)=5*C/4 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  push_cast
  field_simp
  ring

theorem profileClock_finite_contraction {C : ℝ} (hC : 0 < C)
    {m : ℕ} (hm : 1 ≤ m) :
    (C/(C+5*C/(512*(m : ℝ))))^(128*m) ≤ (29/100 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have he : C/(C+5*C/(512*(m : ℝ))) =
      (512*(m : ℝ))/(512*(m : ℝ)+5) := by
    field_simp
  rw [he]
  exact profile_block128_contraction m hm

/-- A finite block can simultaneously meet the lag and prefix tolerances,
the complete clock sum estimate, and the fixed spectral contraction. -/
theorem profileClock_complete_finite_parameters {C B M D : ℝ}
    (hC : 0 < C) (hB : 0 < B) (hM : 0 ≤ M) (hD : 0 < D) :
    ∃ m : ℕ, 1 ≤ m ∧
      let N := 128*m
      let t := 5*C/(512*(m : ℝ))
      let s := t/(101/100 : ℝ)
      0 < t ∧ 0 < s ∧ 51 ≤ N ∧ t*(N : ℝ)=5*C/4 ∧
      t*D ≤ B/2000 ∧ 51*t*M ≤ B*Real.sqrt C/200 ∧
      51*t*M+2*(t*((87/100 : ℝ)*B)/Real.sqrt s)*
        Real.sqrt ((N-51 : ℕ) : ℝ)/Real.sqrt (99/50 : ℝ) ≤
          (279/200 : ℝ)*B*Real.sqrt C ∧
      51*t*M+(∑ j ∈ Finset.range (N-51),
        t*(((87/100 : ℝ)*B)/(Real.sqrt s*entropyClock (51+j)))) ≤
          (279/200 : ℝ)*B*Real.sqrt C ∧
      (C/(C+t))^N ≤ (29/100 : ℝ) := by
  obtain ⟨m,hm,ht,hs,hN,hlag,hprefix,hbound⟩ :=
    profileClock_finite_step_parameters hC hB hM hD
  refine ⟨m,hm,ht,hs,hN,profileClock_finite_time_identity hm,
    hlag,hprefix,hbound,?_,profileClock_finite_contraction hC hm⟩
  have hsum := entropyClock_displacement_tail_sum_le ht.le
    (show 0 ≤ (87/100 : ℝ)*B by positivity) hs (128*m-51)
  linarith only [hsum,hbound]

end KLS.ConstantReduction
end
