import KLS.WeightedResolventPositivity
import Mathlib.Analysis.Convex.Deriv

open Set
noncomputable section
namespace KLS.ConstantReduction

def entropyProfile (s : ℝ) : ℝ :=
    (87/100 : ℝ)*s^0 +
    (-2349/4000 : ℝ)*s^2 +
    (-21141/320000 : ℝ)*s^4 +
    (-63423/2560000 : ℝ)*s^6 +
    (-5137263/409600000 : ℝ)*s^8 +
    (-601059771/81920000000 : ℝ)*s^10 +
    (-30654048321/6553600000000 : ℝ)*s^12 +
    (-827659304667/262144000000000 : ℝ)*s^14 +
    (-7448933742003/3355443200000000 : ℝ)*s^16 +
    (-216019078518087/134217728000000000 : ℝ)*s^18 +
    (-64157666319871839/53687091200000000000 : ℝ)*s^20

def entropyProfileD1 (s : ℝ) : ℝ :=
    (-2349/2000 : ℝ)*s^1 +
    (-21141/80000 : ℝ)*s^3 +
    (-190269/1280000 : ℝ)*s^5 +
    (-5137263/51200000 : ℝ)*s^7 +
    (-601059771/8192000000 : ℝ)*s^9 +
    (-91962144963/1638400000000 : ℝ)*s^11 +
    (-5793615132669/131072000000000 : ℝ)*s^13 +
    (-7448933742003/209715200000000 : ℝ)*s^15 +
    (-1944171706662783/67108864000000000 : ℝ)*s^17 +
    (-64157666319871839/2684354560000000000 : ℝ)*s^19

def entropyProfileD2 (s : ℝ) : ℝ :=
    (-2349/2000 : ℝ)*s^0 +
    (-63423/80000 : ℝ)*s^2 +
    (-190269/256000 : ℝ)*s^4 +
    (-35960841/51200000 : ℝ)*s^6 +
    (-5409537939/8192000000 : ℝ)*s^8 +
    (-1011583594593/1638400000000 : ℝ)*s^10 +
    (-75316996724697/131072000000000 : ℝ)*s^12 +
    (-22346801226009/41943040000000 : ℝ)*s^14 +
    (-33050919013267311/67108864000000000 : ℝ)*s^16 +
    (-1218995660077564941/2684354560000000000 : ℝ)*s^18

theorem entropyProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) entropyProfile := by
  unfold entropyProfile
  fun_prop

theorem entropyProfileD1_contDiff : ContDiff ℝ (⊤ : ℕ∞) entropyProfileD1 := by
  unfold entropyProfileD1
  fun_prop

theorem entropyProfile_hasDerivAt (s : ℝ) : HasDerivAt entropyProfile (entropyProfileD1 s) s := by
  convert (((((((((((((hasDerivAt_id s).pow 0).const_mul (87/100 : ℝ)).add (((hasDerivAt_id s).pow 2).const_mul (-2349/4000 : ℝ))).add (((hasDerivAt_id s).pow 4).const_mul (-21141/320000 : ℝ))).add (((hasDerivAt_id s).pow 6).const_mul (-63423/2560000 : ℝ))).add (((hasDerivAt_id s).pow 8).const_mul (-5137263/409600000 : ℝ))).add (((hasDerivAt_id s).pow 10).const_mul (-601059771/81920000000 : ℝ))).add (((hasDerivAt_id s).pow 12).const_mul (-30654048321/6553600000000 : ℝ))).add (((hasDerivAt_id s).pow 14).const_mul (-827659304667/262144000000000 : ℝ))).add (((hasDerivAt_id s).pow 16).const_mul (-7448933742003/3355443200000000 : ℝ))).add (((hasDerivAt_id s).pow 18).const_mul (-216019078518087/134217728000000000 : ℝ))).add (((hasDerivAt_id s).pow 20).const_mul (-64157666319871839/53687091200000000000 : ℝ))) using 1
  · funext y
    dsimp only [entropyProfile,Pi.add_apply,Pi.pow_apply,id_eq]
  · dsimp only [entropyProfileD1,id_eq]
    norm_num; ring

theorem entropyProfileD1_hasDerivAt (s : ℝ) : HasDerivAt entropyProfileD1 (entropyProfileD2 s) s := by
  convert ((((((((((((hasDerivAt_id s).pow 1).const_mul (-2349/2000 : ℝ)).add (((hasDerivAt_id s).pow 3).const_mul (-21141/80000 : ℝ))).add (((hasDerivAt_id s).pow 5).const_mul (-190269/1280000 : ℝ))).add (((hasDerivAt_id s).pow 7).const_mul (-5137263/51200000 : ℝ))).add (((hasDerivAt_id s).pow 9).const_mul (-601059771/8192000000 : ℝ))).add (((hasDerivAt_id s).pow 11).const_mul (-91962144963/1638400000000 : ℝ))).add (((hasDerivAt_id s).pow 13).const_mul (-5793615132669/131072000000000 : ℝ))).add (((hasDerivAt_id s).pow 15).const_mul (-7448933742003/209715200000000 : ℝ))).add (((hasDerivAt_id s).pow 17).const_mul (-1944171706662783/67108864000000000 : ℝ))).add (((hasDerivAt_id s).pow 19).const_mul (-64157666319871839/2684354560000000000 : ℝ))) using 1
  · funext y
    dsimp only [entropyProfileD1,Pi.add_apply,Pi.pow_apply,id_eq]
  · dsimp only [entropyProfileD2,id_eq]
    norm_num; ring

theorem entropyProfile_deriv : deriv entropyProfile = entropyProfileD1 := funext fun s => (entropyProfile_hasDerivAt s).deriv

theorem entropyProfile_second_deriv : deriv (deriv entropyProfile) = entropyProfileD2 := by
  rw [entropyProfile_deriv]
  exact funext fun s => (entropyProfileD1_hasDerivAt s).deriv

theorem entropyProfile_bounds {s : ℝ} (hs : |s| ≤ 1) :
    (3/20 : ℝ) ≤ entropyProfile s ∧ entropyProfile s ≤ (87/100 : ℝ) := by
  have hy0 : 0 ≤ s^2 := sq_nonneg _
  have hy1 : s^2 ≤ 1 := by simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg s) (by norm_num : (0:ℝ)≤1)).mpr hs
  have hp1 : 0 ≤ (s^2)^1 ∧ (s^2)^1 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp2 : 0 ≤ (s^2)^2 ∧ (s^2)^2 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp3 : 0 ≤ (s^2)^3 ∧ (s^2)^3 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp4 : 0 ≤ (s^2)^4 ∧ (s^2)^4 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp5 : 0 ≤ (s^2)^5 ∧ (s^2)^5 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp6 : 0 ≤ (s^2)^6 ∧ (s^2)^6 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp7 : 0 ≤ (s^2)^7 ∧ (s^2)^7 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp8 : 0 ≤ (s^2)^8 ∧ (s^2)^8 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp9 : 0 ≤ (s^2)^9 ∧ (s^2)^9 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have hp10 : 0 ≤ (s^2)^10 ∧ (s^2)^10 ≤ 1 := ⟨pow_nonneg hy0 _,pow_le_one₀ hy0 hy1⟩
  have heq : entropyProfile s = (87/100 : ℝ)*s^0 + (-2349/4000 : ℝ)*s^2 + (-21141/320000 : ℝ)*s^4 + (-63423/2560000 : ℝ)*s^6 + (-5137263/409600000 : ℝ)*s^8 + (-601059771/81920000000 : ℝ)*s^10 + (-30654048321/6553600000000 : ℝ)*s^12 + (-827659304667/262144000000000 : ℝ)*s^14 + (-7448933742003/3355443200000000 : ℝ)*s^16 + (-216019078518087/134217728000000000 : ℝ)*s^18 + (-64157666319871839/53687091200000000000 : ℝ)*s^20 := rfl
  have hform : entropyProfile s = (87/100 : ℝ)*(s^2)^0 + (-2349/4000 : ℝ)*(s^2)^1 + (-21141/320000 : ℝ)*(s^2)^2 + (-63423/2560000 : ℝ)*(s^2)^3 + (-5137263/409600000 : ℝ)*(s^2)^4 + (-601059771/81920000000 : ℝ)*(s^2)^5 + (-30654048321/6553600000000 : ℝ)*(s^2)^6 + (-827659304667/262144000000000 : ℝ)*(s^2)^7 + (-7448933742003/3355443200000000 : ℝ)*(s^2)^8 + (-216019078518087/134217728000000000 : ℝ)*(s^2)^9 + (-64157666319871839/53687091200000000000 : ℝ)*(s^2)^10 := by
    unfold entropyProfile
    ring
  constructor <;> rw [hform] <;> norm_num only [pow_zero,mul_one] <;> linarith only [hp1.1,hp1.2,hp2.1,hp2.2,hp3.1,hp3.2,hp4.1,hp4.2,hp5.1,hp5.2,hp6.1,hp6.2,hp7.1,hp7.2,hp8.1,hp8.2,hp9.1,hp9.2,hp10.1,hp10.2]

theorem entropyProfile_curvature_identity (s : ℝ) :
    entropyProfile s*(-entropyProfileD2 s)-1 =
    (4363/200000 : ℝ)*(s^2)^0*(1-s^2)^19 +
    (82897/200000 : ℝ)*(s^2)^1*(1-s^2)^18 +
    (613411803/160000000 : ℝ)*(s^2)^2*(1-s^2)^17 +
    (36785035137/1600000000 : ℝ)*(s^2)^3*(1-s^2)^16 +
    (5129917584513/51200000000 : ℝ)*(s^2)^4*(1-s^2)^15 +
    (107659130743971/320000000000 : ℝ)*(s^2)^5*(1-s^2)^14 +
    (1473721932588591/1638400000000 : ℝ)*(s^2)^6*(1-s^2)^13 +
    (3996478908763974303/2048000000000000 : ℝ)*(s^2)^7*(1-s^2)^12 +
    (2275512343462343335689/655360000000000000 : ℝ)*(s^2)^8*(1-s^2)^11 +
    (3338698298667221348221/655360000000000000 : ℝ)*(s^2)^9*(1-s^2)^10 +
    (3314259429783827463418524803/536870912000000000000000 : ℝ)*(s^2)^10*(1-s^2)^9 +
    (26483617496335628601378277767/4294967296000000000000000 : ℝ)*(s^2)^11*(1-s^2)^8 +
    (4334844753557512713745372255101/858993459200000000000000000 : ℝ)*(s^2)^12*(1-s^2)^7 +
    (229827403657361579531818151094537/68719476736000000000000000000 : ℝ)*(s^2)^13*(1-s^2)^6 +
    (3867644076475627196322968714922009/2199023255552000000000000000000 : ℝ)*(s^2)^14*(1-s^2)^5 +
    (62415996170555800181437746310466313/87960930222080000000000000000000 : ℝ)*(s^2)^15*(1-s^2)^4 +
    (5841158032166524471071368302232529003/28147497671065600000000000000000000 : ℝ)*(s^2)^16*(1-s^2)^3 +
    (2234181586805249099806680785466679323/56294995342131200000000000000000000 : ℝ)*(s^2)^17*(1-s^2)^2 +
    (14206351212128002105925007376814642113/3602879701896396800000000000000000000 : ℝ)*(s^2)^18*(1-s^2)^1 +
    (10600866537442833543821221781643657301/144115188075855872000000000000000000000 : ℝ)*(s^2)^19*(1-s^2)^0 := by
  unfold entropyProfile entropyProfileD2
  ring

theorem entropyProfile_curvature {s : ℝ} (hs : |s| ≤ 1) :
    1 ≤ entropyProfile s*(-deriv (deriv entropyProfile) s) := by
  have hy0 : 0 ≤ s^2 := sq_nonneg _
  have hy1 : s^2 ≤ 1 := by simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg s) (by norm_num : (0:ℝ)≤1)).mpr hs
  have hm : 0 ≤ 1-s^2 := sub_nonneg.mpr hy1
  have hpos : 0 ≤
    (4363/200000 : ℝ)*(s^2)^0*(1-s^2)^19 +
    (82897/200000 : ℝ)*(s^2)^1*(1-s^2)^18 +
    (613411803/160000000 : ℝ)*(s^2)^2*(1-s^2)^17 +
    (36785035137/1600000000 : ℝ)*(s^2)^3*(1-s^2)^16 +
    (5129917584513/51200000000 : ℝ)*(s^2)^4*(1-s^2)^15 +
    (107659130743971/320000000000 : ℝ)*(s^2)^5*(1-s^2)^14 +
    (1473721932588591/1638400000000 : ℝ)*(s^2)^6*(1-s^2)^13 +
    (3996478908763974303/2048000000000000 : ℝ)*(s^2)^7*(1-s^2)^12 +
    (2275512343462343335689/655360000000000000 : ℝ)*(s^2)^8*(1-s^2)^11 +
    (3338698298667221348221/655360000000000000 : ℝ)*(s^2)^9*(1-s^2)^10 +
    (3314259429783827463418524803/536870912000000000000000 : ℝ)*(s^2)^10*(1-s^2)^9 +
    (26483617496335628601378277767/4294967296000000000000000 : ℝ)*(s^2)^11*(1-s^2)^8 +
    (4334844753557512713745372255101/858993459200000000000000000 : ℝ)*(s^2)^12*(1-s^2)^7 +
    (229827403657361579531818151094537/68719476736000000000000000000 : ℝ)*(s^2)^13*(1-s^2)^6 +
    (3867644076475627196322968714922009/2199023255552000000000000000000 : ℝ)*(s^2)^14*(1-s^2)^5 +
    (62415996170555800181437746310466313/87960930222080000000000000000000 : ℝ)*(s^2)^15*(1-s^2)^4 +
    (5841158032166524471071368302232529003/28147497671065600000000000000000000 : ℝ)*(s^2)^16*(1-s^2)^3 +
    (2234181586805249099806680785466679323/56294995342131200000000000000000000 : ℝ)*(s^2)^17*(1-s^2)^2 +
    (14206351212128002105925007376814642113/3602879701896396800000000000000000000 : ℝ)*(s^2)^18*(1-s^2)^1 +
    (10600866537442833543821221781643657301/144115188075855872000000000000000000000 : ℝ)*(s^2)^19*(1-s^2)^0 := by positivity
  rw [← entropyProfile_curvature_identity] at hpos
  rw [entropyProfile_second_deriv]
  linarith only [hpos]

end KLS.ConstantReduction
end
