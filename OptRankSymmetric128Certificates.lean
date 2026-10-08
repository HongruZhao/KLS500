import OptRankSymmetric128Certificates2To9
import OptRankSymmetric128Certificates10To17
import OptRankSymmetric128Certificates18To25
import OptRankSymmetric128Certificates26To33
import OptRankSymmetric128Certificates34To41
import OptRankSymmetric128Certificates42To49
import OptRankSymmetric128Certificates50To57
import OptRankSymmetric128Certificates58To65
import OptRankSymmetric128Certificates66To73
import OptRankSymmetric128Certificates74To81
import OptRankSymmetric128Certificates82To89
import OptRankSymmetric128Certificates90To97
import OptRankSymmetric128Certificates98To105
import OptRankSymmetric128Certificates106To113
import OptRankSymmetric128Certificates114To121
import OptRankSymmetric128Certificates122To128

set_option maxRecDepth 8192

noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric128_root_allowance_square (r : ℕ) (hr : 2 ≤ r) (hr128 : r ≤ 128) :
    rankSymmetric128IntegralWeight (r-1) * rankSymmetric128Convolution r ≤ (rankSymmetric128RootAllowance r)^2 := by
  interval_cases r
  · exact (rankSymmetric128Certificate_2).1
  · exact (rankSymmetric128Certificate_3).1
  · exact (rankSymmetric128Certificate_4).1
  · exact (rankSymmetric128Certificate_5).1
  · exact (rankSymmetric128Certificate_6).1
  · exact (rankSymmetric128Certificate_7).1
  · exact (rankSymmetric128Certificate_8).1
  · exact (rankSymmetric128Certificate_9).1
  · exact (rankSymmetric128Certificate_10).1
  · exact (rankSymmetric128Certificate_11).1
  · exact (rankSymmetric128Certificate_12).1
  · exact (rankSymmetric128Certificate_13).1
  · exact (rankSymmetric128Certificate_14).1
  · exact (rankSymmetric128Certificate_15).1
  · exact (rankSymmetric128Certificate_16).1
  · exact (rankSymmetric128Certificate_17).1
  · exact (rankSymmetric128Certificate_18).1
  · exact (rankSymmetric128Certificate_19).1
  · exact (rankSymmetric128Certificate_20).1
  · exact (rankSymmetric128Certificate_21).1
  · exact (rankSymmetric128Certificate_22).1
  · exact (rankSymmetric128Certificate_23).1
  · exact (rankSymmetric128Certificate_24).1
  · exact (rankSymmetric128Certificate_25).1
  · exact (rankSymmetric128Certificate_26).1
  · exact (rankSymmetric128Certificate_27).1
  · exact (rankSymmetric128Certificate_28).1
  · exact (rankSymmetric128Certificate_29).1
  · exact (rankSymmetric128Certificate_30).1
  · exact (rankSymmetric128Certificate_31).1
  · exact (rankSymmetric128Certificate_32).1
  · exact (rankSymmetric128Certificate_33).1
  · exact (rankSymmetric128Certificate_34).1
  · exact (rankSymmetric128Certificate_35).1
  · exact (rankSymmetric128Certificate_36).1
  · exact (rankSymmetric128Certificate_37).1
  · exact (rankSymmetric128Certificate_38).1
  · exact (rankSymmetric128Certificate_39).1
  · exact (rankSymmetric128Certificate_40).1
  · exact (rankSymmetric128Certificate_41).1
  · exact (rankSymmetric128Certificate_42).1
  · exact (rankSymmetric128Certificate_43).1
  · exact (rankSymmetric128Certificate_44).1
  · exact (rankSymmetric128Certificate_45).1
  · exact (rankSymmetric128Certificate_46).1
  · exact (rankSymmetric128Certificate_47).1
  · exact (rankSymmetric128Certificate_48).1
  · exact (rankSymmetric128Certificate_49).1
  · exact (rankSymmetric128Certificate_50).1
  · exact (rankSymmetric128Certificate_51).1
  · exact (rankSymmetric128Certificate_52).1
  · exact (rankSymmetric128Certificate_53).1
  · exact (rankSymmetric128Certificate_54).1
  · exact (rankSymmetric128Certificate_55).1
  · exact (rankSymmetric128Certificate_56).1
  · exact (rankSymmetric128Certificate_57).1
  · exact (rankSymmetric128Certificate_58).1
  · exact (rankSymmetric128Certificate_59).1
  · exact (rankSymmetric128Certificate_60).1
  · exact (rankSymmetric128Certificate_61).1
  · exact (rankSymmetric128Certificate_62).1
  · exact (rankSymmetric128Certificate_63).1
  · exact (rankSymmetric128Certificate_64).1
  · exact (rankSymmetric128Certificate_65).1
  · exact (rankSymmetric128Certificate_66).1
  · exact (rankSymmetric128Certificate_67).1
  · exact (rankSymmetric128Certificate_68).1
  · exact (rankSymmetric128Certificate_69).1
  · exact (rankSymmetric128Certificate_70).1
  · exact (rankSymmetric128Certificate_71).1
  · exact (rankSymmetric128Certificate_72).1
  · exact (rankSymmetric128Certificate_73).1
  · exact (rankSymmetric128Certificate_74).1
  · exact (rankSymmetric128Certificate_75).1
  · exact (rankSymmetric128Certificate_76).1
  · exact (rankSymmetric128Certificate_77).1
  · exact (rankSymmetric128Certificate_78).1
  · exact (rankSymmetric128Certificate_79).1
  · exact (rankSymmetric128Certificate_80).1
  · exact (rankSymmetric128Certificate_81).1
  · exact (rankSymmetric128Certificate_82).1
  · exact (rankSymmetric128Certificate_83).1
  · exact (rankSymmetric128Certificate_84).1
  · exact (rankSymmetric128Certificate_85).1
  · exact (rankSymmetric128Certificate_86).1
  · exact (rankSymmetric128Certificate_87).1
  · exact (rankSymmetric128Certificate_88).1
  · exact (rankSymmetric128Certificate_89).1
  · exact (rankSymmetric128Certificate_90).1
  · exact (rankSymmetric128Certificate_91).1
  · exact (rankSymmetric128Certificate_92).1
  · exact (rankSymmetric128Certificate_93).1
  · exact (rankSymmetric128Certificate_94).1
  · exact (rankSymmetric128Certificate_95).1
  · exact (rankSymmetric128Certificate_96).1
  · exact (rankSymmetric128Certificate_97).1
  · exact (rankSymmetric128Certificate_98).1
  · exact (rankSymmetric128Certificate_99).1
  · exact (rankSymmetric128Certificate_100).1
  · exact (rankSymmetric128Certificate_101).1
  · exact (rankSymmetric128Certificate_102).1
  · exact (rankSymmetric128Certificate_103).1
  · exact (rankSymmetric128Certificate_104).1
  · exact (rankSymmetric128Certificate_105).1
  · exact (rankSymmetric128Certificate_106).1
  · exact (rankSymmetric128Certificate_107).1
  · exact (rankSymmetric128Certificate_108).1
  · exact (rankSymmetric128Certificate_109).1
  · exact (rankSymmetric128Certificate_110).1
  · exact (rankSymmetric128Certificate_111).1
  · exact (rankSymmetric128Certificate_112).1
  · exact (rankSymmetric128Certificate_113).1
  · exact (rankSymmetric128Certificate_114).1
  · exact (rankSymmetric128Certificate_115).1
  · exact (rankSymmetric128Certificate_116).1
  · exact (rankSymmetric128Certificate_117).1
  · exact (rankSymmetric128Certificate_118).1
  · exact (rankSymmetric128Certificate_119).1
  · exact (rankSymmetric128Certificate_120).1
  · exact (rankSymmetric128Certificate_121).1
  · exact (rankSymmetric128Certificate_122).1
  · exact (rankSymmetric128Certificate_123).1
  · exact (rankSymmetric128Certificate_124).1
  · exact (rankSymmetric128Certificate_125).1
  · exact (rankSymmetric128Certificate_126).1
  · exact (rankSymmetric128Certificate_127).1
  · exact (rankSymmetric128Certificate_128).1

theorem rankSymmetric128_cumulant_coefficient (r : ℕ) (hr : 3 ≤ r) (hr128 : r ≤ 128) :
    (2*(r : ℝ)^2+3*r-2) * rankSymmetric128IntegralWeight (r-1) + 2 * rankSymmetric128RootAllowance r * (r : ℝ) ≤ (r : ℝ)^2 * rankSymmetric128CumulantWeight r := by
  interval_cases r
  · exact (rankSymmetric128Certificate_3).2.2 (by omega)
  · exact (rankSymmetric128Certificate_4).2.2 (by omega)
  · exact (rankSymmetric128Certificate_5).2.2 (by omega)
  · exact (rankSymmetric128Certificate_6).2.2 (by omega)
  · exact (rankSymmetric128Certificate_7).2.2 (by omega)
  · exact (rankSymmetric128Certificate_8).2.2 (by omega)
  · exact (rankSymmetric128Certificate_9).2.2 (by omega)
  · exact (rankSymmetric128Certificate_10).2.2 (by omega)
  · exact (rankSymmetric128Certificate_11).2.2 (by omega)
  · exact (rankSymmetric128Certificate_12).2.2 (by omega)
  · exact (rankSymmetric128Certificate_13).2.2 (by omega)
  · exact (rankSymmetric128Certificate_14).2.2 (by omega)
  · exact (rankSymmetric128Certificate_15).2.2 (by omega)
  · exact (rankSymmetric128Certificate_16).2.2 (by omega)
  · exact (rankSymmetric128Certificate_17).2.2 (by omega)
  · exact (rankSymmetric128Certificate_18).2.2 (by omega)
  · exact (rankSymmetric128Certificate_19).2.2 (by omega)
  · exact (rankSymmetric128Certificate_20).2.2 (by omega)
  · exact (rankSymmetric128Certificate_21).2.2 (by omega)
  · exact (rankSymmetric128Certificate_22).2.2 (by omega)
  · exact (rankSymmetric128Certificate_23).2.2 (by omega)
  · exact (rankSymmetric128Certificate_24).2.2 (by omega)
  · exact (rankSymmetric128Certificate_25).2.2 (by omega)
  · exact (rankSymmetric128Certificate_26).2.2 (by omega)
  · exact (rankSymmetric128Certificate_27).2.2 (by omega)
  · exact (rankSymmetric128Certificate_28).2.2 (by omega)
  · exact (rankSymmetric128Certificate_29).2.2 (by omega)
  · exact (rankSymmetric128Certificate_30).2.2 (by omega)
  · exact (rankSymmetric128Certificate_31).2.2 (by omega)
  · exact (rankSymmetric128Certificate_32).2.2 (by omega)
  · exact (rankSymmetric128Certificate_33).2.2 (by omega)
  · exact (rankSymmetric128Certificate_34).2.2 (by omega)
  · exact (rankSymmetric128Certificate_35).2.2 (by omega)
  · exact (rankSymmetric128Certificate_36).2.2 (by omega)
  · exact (rankSymmetric128Certificate_37).2.2 (by omega)
  · exact (rankSymmetric128Certificate_38).2.2 (by omega)
  · exact (rankSymmetric128Certificate_39).2.2 (by omega)
  · exact (rankSymmetric128Certificate_40).2.2 (by omega)
  · exact (rankSymmetric128Certificate_41).2.2 (by omega)
  · exact (rankSymmetric128Certificate_42).2.2 (by omega)
  · exact (rankSymmetric128Certificate_43).2.2 (by omega)
  · exact (rankSymmetric128Certificate_44).2.2 (by omega)
  · exact (rankSymmetric128Certificate_45).2.2 (by omega)
  · exact (rankSymmetric128Certificate_46).2.2 (by omega)
  · exact (rankSymmetric128Certificate_47).2.2 (by omega)
  · exact (rankSymmetric128Certificate_48).2.2 (by omega)
  · exact (rankSymmetric128Certificate_49).2.2 (by omega)
  · exact (rankSymmetric128Certificate_50).2.2 (by omega)
  · exact (rankSymmetric128Certificate_51).2.2 (by omega)
  · exact (rankSymmetric128Certificate_52).2.2 (by omega)
  · exact (rankSymmetric128Certificate_53).2.2 (by omega)
  · exact (rankSymmetric128Certificate_54).2.2 (by omega)
  · exact (rankSymmetric128Certificate_55).2.2 (by omega)
  · exact (rankSymmetric128Certificate_56).2.2 (by omega)
  · exact (rankSymmetric128Certificate_57).2.2 (by omega)
  · exact (rankSymmetric128Certificate_58).2.2 (by omega)
  · exact (rankSymmetric128Certificate_59).2.2 (by omega)
  · exact (rankSymmetric128Certificate_60).2.2 (by omega)
  · exact (rankSymmetric128Certificate_61).2.2 (by omega)
  · exact (rankSymmetric128Certificate_62).2.2 (by omega)
  · exact (rankSymmetric128Certificate_63).2.2 (by omega)
  · exact (rankSymmetric128Certificate_64).2.2 (by omega)
  · exact (rankSymmetric128Certificate_65).2.2 (by omega)
  · exact (rankSymmetric128Certificate_66).2.2 (by omega)
  · exact (rankSymmetric128Certificate_67).2.2 (by omega)
  · exact (rankSymmetric128Certificate_68).2.2 (by omega)
  · exact (rankSymmetric128Certificate_69).2.2 (by omega)
  · exact (rankSymmetric128Certificate_70).2.2 (by omega)
  · exact (rankSymmetric128Certificate_71).2.2 (by omega)
  · exact (rankSymmetric128Certificate_72).2.2 (by omega)
  · exact (rankSymmetric128Certificate_73).2.2 (by omega)
  · exact (rankSymmetric128Certificate_74).2.2 (by omega)
  · exact (rankSymmetric128Certificate_75).2.2 (by omega)
  · exact (rankSymmetric128Certificate_76).2.2 (by omega)
  · exact (rankSymmetric128Certificate_77).2.2 (by omega)
  · exact (rankSymmetric128Certificate_78).2.2 (by omega)
  · exact (rankSymmetric128Certificate_79).2.2 (by omega)
  · exact (rankSymmetric128Certificate_80).2.2 (by omega)
  · exact (rankSymmetric128Certificate_81).2.2 (by omega)
  · exact (rankSymmetric128Certificate_82).2.2 (by omega)
  · exact (rankSymmetric128Certificate_83).2.2 (by omega)
  · exact (rankSymmetric128Certificate_84).2.2 (by omega)
  · exact (rankSymmetric128Certificate_85).2.2 (by omega)
  · exact (rankSymmetric128Certificate_86).2.2 (by omega)
  · exact (rankSymmetric128Certificate_87).2.2 (by omega)
  · exact (rankSymmetric128Certificate_88).2.2 (by omega)
  · exact (rankSymmetric128Certificate_89).2.2 (by omega)
  · exact (rankSymmetric128Certificate_90).2.2 (by omega)
  · exact (rankSymmetric128Certificate_91).2.2 (by omega)
  · exact (rankSymmetric128Certificate_92).2.2 (by omega)
  · exact (rankSymmetric128Certificate_93).2.2 (by omega)
  · exact (rankSymmetric128Certificate_94).2.2 (by omega)
  · exact (rankSymmetric128Certificate_95).2.2 (by omega)
  · exact (rankSymmetric128Certificate_96).2.2 (by omega)
  · exact (rankSymmetric128Certificate_97).2.2 (by omega)
  · exact (rankSymmetric128Certificate_98).2.2 (by omega)
  · exact (rankSymmetric128Certificate_99).2.2 (by omega)
  · exact (rankSymmetric128Certificate_100).2.2 (by omega)
  · exact (rankSymmetric128Certificate_101).2.2 (by omega)
  · exact (rankSymmetric128Certificate_102).2.2 (by omega)
  · exact (rankSymmetric128Certificate_103).2.2 (by omega)
  · exact (rankSymmetric128Certificate_104).2.2 (by omega)
  · exact (rankSymmetric128Certificate_105).2.2 (by omega)
  · exact (rankSymmetric128Certificate_106).2.2 (by omega)
  · exact (rankSymmetric128Certificate_107).2.2 (by omega)
  · exact (rankSymmetric128Certificate_108).2.2 (by omega)
  · exact (rankSymmetric128Certificate_109).2.2 (by omega)
  · exact (rankSymmetric128Certificate_110).2.2 (by omega)
  · exact (rankSymmetric128Certificate_111).2.2 (by omega)
  · exact (rankSymmetric128Certificate_112).2.2 (by omega)
  · exact (rankSymmetric128Certificate_113).2.2 (by omega)
  · exact (rankSymmetric128Certificate_114).2.2 (by omega)
  · exact (rankSymmetric128Certificate_115).2.2 (by omega)
  · exact (rankSymmetric128Certificate_116).2.2 (by omega)
  · exact (rankSymmetric128Certificate_117).2.2 (by omega)
  · exact (rankSymmetric128Certificate_118).2.2 (by omega)
  · exact (rankSymmetric128Certificate_119).2.2 (by omega)
  · exact (rankSymmetric128Certificate_120).2.2 (by omega)
  · exact (rankSymmetric128Certificate_121).2.2 (by omega)
  · exact (rankSymmetric128Certificate_122).2.2 (by omega)
  · exact (rankSymmetric128Certificate_123).2.2 (by omega)
  · exact (rankSymmetric128Certificate_124).2.2 (by omega)
  · exact (rankSymmetric128Certificate_125).2.2 (by omega)
  · exact (rankSymmetric128Certificate_126).2.2 (by omega)
  · exact (rankSymmetric128Certificate_127).2.2 (by omega)
  · exact (rankSymmetric128Certificate_128).2.2 (by omega)

theorem rankSymmetric128_integral_coefficient (r : ℕ) (hr : 2 ≤ r) (hr128 : r ≤ 128) :
    ((4*rankSymmetric128Parameter r-2)*(r : ℝ)^2+(8*rankSymmetric128Parameter r-5)*r-2) * rankSymmetric128IntegralWeight (r-1) + 2 * rankSymmetric128RootAllowance r * (r : ℝ) ≤ rankSymmetric128Coercivity r * (r : ℝ)^2 * rankSymmetric128IntegralWeight r := by
  interval_cases r
  · exact (rankSymmetric128Certificate_2).2.1
  · exact (rankSymmetric128Certificate_3).2.1
  · exact (rankSymmetric128Certificate_4).2.1
  · exact (rankSymmetric128Certificate_5).2.1
  · exact (rankSymmetric128Certificate_6).2.1
  · exact (rankSymmetric128Certificate_7).2.1
  · exact (rankSymmetric128Certificate_8).2.1
  · exact (rankSymmetric128Certificate_9).2.1
  · exact (rankSymmetric128Certificate_10).2.1
  · exact (rankSymmetric128Certificate_11).2.1
  · exact (rankSymmetric128Certificate_12).2.1
  · exact (rankSymmetric128Certificate_13).2.1
  · exact (rankSymmetric128Certificate_14).2.1
  · exact (rankSymmetric128Certificate_15).2.1
  · exact (rankSymmetric128Certificate_16).2.1
  · exact (rankSymmetric128Certificate_17).2.1
  · exact (rankSymmetric128Certificate_18).2.1
  · exact (rankSymmetric128Certificate_19).2.1
  · exact (rankSymmetric128Certificate_20).2.1
  · exact (rankSymmetric128Certificate_21).2.1
  · exact (rankSymmetric128Certificate_22).2.1
  · exact (rankSymmetric128Certificate_23).2.1
  · exact (rankSymmetric128Certificate_24).2.1
  · exact (rankSymmetric128Certificate_25).2.1
  · exact (rankSymmetric128Certificate_26).2.1
  · exact (rankSymmetric128Certificate_27).2.1
  · exact (rankSymmetric128Certificate_28).2.1
  · exact (rankSymmetric128Certificate_29).2.1
  · exact (rankSymmetric128Certificate_30).2.1
  · exact (rankSymmetric128Certificate_31).2.1
  · exact (rankSymmetric128Certificate_32).2.1
  · exact (rankSymmetric128Certificate_33).2.1
  · exact (rankSymmetric128Certificate_34).2.1
  · exact (rankSymmetric128Certificate_35).2.1
  · exact (rankSymmetric128Certificate_36).2.1
  · exact (rankSymmetric128Certificate_37).2.1
  · exact (rankSymmetric128Certificate_38).2.1
  · exact (rankSymmetric128Certificate_39).2.1
  · exact (rankSymmetric128Certificate_40).2.1
  · exact (rankSymmetric128Certificate_41).2.1
  · exact (rankSymmetric128Certificate_42).2.1
  · exact (rankSymmetric128Certificate_43).2.1
  · exact (rankSymmetric128Certificate_44).2.1
  · exact (rankSymmetric128Certificate_45).2.1
  · exact (rankSymmetric128Certificate_46).2.1
  · exact (rankSymmetric128Certificate_47).2.1
  · exact (rankSymmetric128Certificate_48).2.1
  · exact (rankSymmetric128Certificate_49).2.1
  · exact (rankSymmetric128Certificate_50).2.1
  · exact (rankSymmetric128Certificate_51).2.1
  · exact (rankSymmetric128Certificate_52).2.1
  · exact (rankSymmetric128Certificate_53).2.1
  · exact (rankSymmetric128Certificate_54).2.1
  · exact (rankSymmetric128Certificate_55).2.1
  · exact (rankSymmetric128Certificate_56).2.1
  · exact (rankSymmetric128Certificate_57).2.1
  · exact (rankSymmetric128Certificate_58).2.1
  · exact (rankSymmetric128Certificate_59).2.1
  · exact (rankSymmetric128Certificate_60).2.1
  · exact (rankSymmetric128Certificate_61).2.1
  · exact (rankSymmetric128Certificate_62).2.1
  · exact (rankSymmetric128Certificate_63).2.1
  · exact (rankSymmetric128Certificate_64).2.1
  · exact (rankSymmetric128Certificate_65).2.1
  · exact (rankSymmetric128Certificate_66).2.1
  · exact (rankSymmetric128Certificate_67).2.1
  · exact (rankSymmetric128Certificate_68).2.1
  · exact (rankSymmetric128Certificate_69).2.1
  · exact (rankSymmetric128Certificate_70).2.1
  · exact (rankSymmetric128Certificate_71).2.1
  · exact (rankSymmetric128Certificate_72).2.1
  · exact (rankSymmetric128Certificate_73).2.1
  · exact (rankSymmetric128Certificate_74).2.1
  · exact (rankSymmetric128Certificate_75).2.1
  · exact (rankSymmetric128Certificate_76).2.1
  · exact (rankSymmetric128Certificate_77).2.1
  · exact (rankSymmetric128Certificate_78).2.1
  · exact (rankSymmetric128Certificate_79).2.1
  · exact (rankSymmetric128Certificate_80).2.1
  · exact (rankSymmetric128Certificate_81).2.1
  · exact (rankSymmetric128Certificate_82).2.1
  · exact (rankSymmetric128Certificate_83).2.1
  · exact (rankSymmetric128Certificate_84).2.1
  · exact (rankSymmetric128Certificate_85).2.1
  · exact (rankSymmetric128Certificate_86).2.1
  · exact (rankSymmetric128Certificate_87).2.1
  · exact (rankSymmetric128Certificate_88).2.1
  · exact (rankSymmetric128Certificate_89).2.1
  · exact (rankSymmetric128Certificate_90).2.1
  · exact (rankSymmetric128Certificate_91).2.1
  · exact (rankSymmetric128Certificate_92).2.1
  · exact (rankSymmetric128Certificate_93).2.1
  · exact (rankSymmetric128Certificate_94).2.1
  · exact (rankSymmetric128Certificate_95).2.1
  · exact (rankSymmetric128Certificate_96).2.1
  · exact (rankSymmetric128Certificate_97).2.1
  · exact (rankSymmetric128Certificate_98).2.1
  · exact (rankSymmetric128Certificate_99).2.1
  · exact (rankSymmetric128Certificate_100).2.1
  · exact (rankSymmetric128Certificate_101).2.1
  · exact (rankSymmetric128Certificate_102).2.1
  · exact (rankSymmetric128Certificate_103).2.1
  · exact (rankSymmetric128Certificate_104).2.1
  · exact (rankSymmetric128Certificate_105).2.1
  · exact (rankSymmetric128Certificate_106).2.1
  · exact (rankSymmetric128Certificate_107).2.1
  · exact (rankSymmetric128Certificate_108).2.1
  · exact (rankSymmetric128Certificate_109).2.1
  · exact (rankSymmetric128Certificate_110).2.1
  · exact (rankSymmetric128Certificate_111).2.1
  · exact (rankSymmetric128Certificate_112).2.1
  · exact (rankSymmetric128Certificate_113).2.1
  · exact (rankSymmetric128Certificate_114).2.1
  · exact (rankSymmetric128Certificate_115).2.1
  · exact (rankSymmetric128Certificate_116).2.1
  · exact (rankSymmetric128Certificate_117).2.1
  · exact (rankSymmetric128Certificate_118).2.1
  · exact (rankSymmetric128Certificate_119).2.1
  · exact (rankSymmetric128Certificate_120).2.1
  · exact (rankSymmetric128Certificate_121).2.1
  · exact (rankSymmetric128Certificate_122).2.1
  · exact (rankSymmetric128Certificate_123).2.1
  · exact (rankSymmetric128Certificate_124).2.1
  · exact (rankSymmetric128Certificate_125).2.1
  · exact (rankSymmetric128Certificate_126).2.1
  · exact (rankSymmetric128Certificate_127).2.1
  · exact (rankSymmetric128Certificate_128).2.1

end KLS.RouteArithmetic
end
