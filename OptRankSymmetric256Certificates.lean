import OptRankSymmetric128Certificates
import OptRankSymmetric256Certificates129To136
import OptRankSymmetric256Certificates137To144
import OptRankSymmetric256Certificates145To152
import OptRankSymmetric256Certificates153To160
import OptRankSymmetric256Certificates161To168
import OptRankSymmetric256Certificates169To176
import OptRankSymmetric256Certificates177To184
import OptRankSymmetric256Certificates185To192
import OptRankSymmetric256Certificates193To200
import OptRankSymmetric256Certificates201To208
import OptRankSymmetric256Certificates209To216
import OptRankSymmetric256Certificates217To224
import OptRankSymmetric256Certificates225To232
import OptRankSymmetric256Certificates233To240
import OptRankSymmetric256Certificates241To248
import OptRankSymmetric256Certificates249To256

set_option maxRecDepth 16384
noncomputable section
namespace KLS.RouteArithmetic

theorem rankSymmetric256_root_allowance_square (r : ℕ) (hr : 2 ≤ r) (hr256 : r ≤ 256) :
    rankSymmetric256IntegralWeight (r-1) * rankSymmetric256Convolution r ≤ (rankSymmetric256RootAllowance r)^2 := by
  by_cases hold : r ≤ 128
  · have hm : r-1 ≤ 128 := by omega
    simpa only [rankSymmetric256IntegralWeight_eq_previous (r-1) hm, rankSymmetric256IntegralWeight_eq_previous r hold, rankSymmetric256Convolution_eq_previous r hold, rankSymmetric256RootAllowance_eq_previous r hold, rankSymmetric256CumulantWeight_eq_previous r hold, rankSymmetric256Parameter_eq_previous r hold, rankSymmetric256Coercivity_eq_previous r hold]
      using rankSymmetric128_root_allowance_square r hr hold
  · have hlo : 129 ≤ r := by omega
    interval_cases r
    · exact (rankSymmetric256Certificate_129).1
    · exact (rankSymmetric256Certificate_130).1
    · exact (rankSymmetric256Certificate_131).1
    · exact (rankSymmetric256Certificate_132).1
    · exact (rankSymmetric256Certificate_133).1
    · exact (rankSymmetric256Certificate_134).1
    · exact (rankSymmetric256Certificate_135).1
    · exact (rankSymmetric256Certificate_136).1
    · exact (rankSymmetric256Certificate_137).1
    · exact (rankSymmetric256Certificate_138).1
    · exact (rankSymmetric256Certificate_139).1
    · exact (rankSymmetric256Certificate_140).1
    · exact (rankSymmetric256Certificate_141).1
    · exact (rankSymmetric256Certificate_142).1
    · exact (rankSymmetric256Certificate_143).1
    · exact (rankSymmetric256Certificate_144).1
    · exact (rankSymmetric256Certificate_145).1
    · exact (rankSymmetric256Certificate_146).1
    · exact (rankSymmetric256Certificate_147).1
    · exact (rankSymmetric256Certificate_148).1
    · exact (rankSymmetric256Certificate_149).1
    · exact (rankSymmetric256Certificate_150).1
    · exact (rankSymmetric256Certificate_151).1
    · exact (rankSymmetric256Certificate_152).1
    · exact (rankSymmetric256Certificate_153).1
    · exact (rankSymmetric256Certificate_154).1
    · exact (rankSymmetric256Certificate_155).1
    · exact (rankSymmetric256Certificate_156).1
    · exact (rankSymmetric256Certificate_157).1
    · exact (rankSymmetric256Certificate_158).1
    · exact (rankSymmetric256Certificate_159).1
    · exact (rankSymmetric256Certificate_160).1
    · exact (rankSymmetric256Certificate_161).1
    · exact (rankSymmetric256Certificate_162).1
    · exact (rankSymmetric256Certificate_163).1
    · exact (rankSymmetric256Certificate_164).1
    · exact (rankSymmetric256Certificate_165).1
    · exact (rankSymmetric256Certificate_166).1
    · exact (rankSymmetric256Certificate_167).1
    · exact (rankSymmetric256Certificate_168).1
    · exact (rankSymmetric256Certificate_169).1
    · exact (rankSymmetric256Certificate_170).1
    · exact (rankSymmetric256Certificate_171).1
    · exact (rankSymmetric256Certificate_172).1
    · exact (rankSymmetric256Certificate_173).1
    · exact (rankSymmetric256Certificate_174).1
    · exact (rankSymmetric256Certificate_175).1
    · exact (rankSymmetric256Certificate_176).1
    · exact (rankSymmetric256Certificate_177).1
    · exact (rankSymmetric256Certificate_178).1
    · exact (rankSymmetric256Certificate_179).1
    · exact (rankSymmetric256Certificate_180).1
    · exact (rankSymmetric256Certificate_181).1
    · exact (rankSymmetric256Certificate_182).1
    · exact (rankSymmetric256Certificate_183).1
    · exact (rankSymmetric256Certificate_184).1
    · exact (rankSymmetric256Certificate_185).1
    · exact (rankSymmetric256Certificate_186).1
    · exact (rankSymmetric256Certificate_187).1
    · exact (rankSymmetric256Certificate_188).1
    · exact (rankSymmetric256Certificate_189).1
    · exact (rankSymmetric256Certificate_190).1
    · exact (rankSymmetric256Certificate_191).1
    · exact (rankSymmetric256Certificate_192).1
    · exact (rankSymmetric256Certificate_193).1
    · exact (rankSymmetric256Certificate_194).1
    · exact (rankSymmetric256Certificate_195).1
    · exact (rankSymmetric256Certificate_196).1
    · exact (rankSymmetric256Certificate_197).1
    · exact (rankSymmetric256Certificate_198).1
    · exact (rankSymmetric256Certificate_199).1
    · exact (rankSymmetric256Certificate_200).1
    · exact (rankSymmetric256Certificate_201).1
    · exact (rankSymmetric256Certificate_202).1
    · exact (rankSymmetric256Certificate_203).1
    · exact (rankSymmetric256Certificate_204).1
    · exact (rankSymmetric256Certificate_205).1
    · exact (rankSymmetric256Certificate_206).1
    · exact (rankSymmetric256Certificate_207).1
    · exact (rankSymmetric256Certificate_208).1
    · exact (rankSymmetric256Certificate_209).1
    · exact (rankSymmetric256Certificate_210).1
    · exact (rankSymmetric256Certificate_211).1
    · exact (rankSymmetric256Certificate_212).1
    · exact (rankSymmetric256Certificate_213).1
    · exact (rankSymmetric256Certificate_214).1
    · exact (rankSymmetric256Certificate_215).1
    · exact (rankSymmetric256Certificate_216).1
    · exact (rankSymmetric256Certificate_217).1
    · exact (rankSymmetric256Certificate_218).1
    · exact (rankSymmetric256Certificate_219).1
    · exact (rankSymmetric256Certificate_220).1
    · exact (rankSymmetric256Certificate_221).1
    · exact (rankSymmetric256Certificate_222).1
    · exact (rankSymmetric256Certificate_223).1
    · exact (rankSymmetric256Certificate_224).1
    · exact (rankSymmetric256Certificate_225).1
    · exact (rankSymmetric256Certificate_226).1
    · exact (rankSymmetric256Certificate_227).1
    · exact (rankSymmetric256Certificate_228).1
    · exact (rankSymmetric256Certificate_229).1
    · exact (rankSymmetric256Certificate_230).1
    · exact (rankSymmetric256Certificate_231).1
    · exact (rankSymmetric256Certificate_232).1
    · exact (rankSymmetric256Certificate_233).1
    · exact (rankSymmetric256Certificate_234).1
    · exact (rankSymmetric256Certificate_235).1
    · exact (rankSymmetric256Certificate_236).1
    · exact (rankSymmetric256Certificate_237).1
    · exact (rankSymmetric256Certificate_238).1
    · exact (rankSymmetric256Certificate_239).1
    · exact (rankSymmetric256Certificate_240).1
    · exact (rankSymmetric256Certificate_241).1
    · exact (rankSymmetric256Certificate_242).1
    · exact (rankSymmetric256Certificate_243).1
    · exact (rankSymmetric256Certificate_244).1
    · exact (rankSymmetric256Certificate_245).1
    · exact (rankSymmetric256Certificate_246).1
    · exact (rankSymmetric256Certificate_247).1
    · exact (rankSymmetric256Certificate_248).1
    · exact (rankSymmetric256Certificate_249).1
    · exact (rankSymmetric256Certificate_250).1
    · exact (rankSymmetric256Certificate_251).1
    · exact (rankSymmetric256Certificate_252).1
    · exact (rankSymmetric256Certificate_253).1
    · exact (rankSymmetric256Certificate_254).1
    · exact (rankSymmetric256Certificate_255).1
    · exact (rankSymmetric256Certificate_256).1

theorem rankSymmetric256_cumulant_coefficient (r : ℕ) (hr : 3 ≤ r) (hr256 : r ≤ 256) :
    (2*(r : ℝ)^2+3*r-2) * rankSymmetric256IntegralWeight (r-1) + 2 * rankSymmetric256RootAllowance r * (r : ℝ) ≤ (r : ℝ)^2 * rankSymmetric256CumulantWeight r := by
  by_cases hold : r ≤ 128
  · have hm : r-1 ≤ 128 := by omega
    simpa only [rankSymmetric256IntegralWeight_eq_previous (r-1) hm, rankSymmetric256IntegralWeight_eq_previous r hold, rankSymmetric256Convolution_eq_previous r hold, rankSymmetric256RootAllowance_eq_previous r hold, rankSymmetric256CumulantWeight_eq_previous r hold, rankSymmetric256Parameter_eq_previous r hold, rankSymmetric256Coercivity_eq_previous r hold]
      using rankSymmetric128_cumulant_coefficient r hr hold
  · have hlo : 129 ≤ r := by omega
    interval_cases r
    · exact (rankSymmetric256Certificate_129).2.2
    · exact (rankSymmetric256Certificate_130).2.2
    · exact (rankSymmetric256Certificate_131).2.2
    · exact (rankSymmetric256Certificate_132).2.2
    · exact (rankSymmetric256Certificate_133).2.2
    · exact (rankSymmetric256Certificate_134).2.2
    · exact (rankSymmetric256Certificate_135).2.2
    · exact (rankSymmetric256Certificate_136).2.2
    · exact (rankSymmetric256Certificate_137).2.2
    · exact (rankSymmetric256Certificate_138).2.2
    · exact (rankSymmetric256Certificate_139).2.2
    · exact (rankSymmetric256Certificate_140).2.2
    · exact (rankSymmetric256Certificate_141).2.2
    · exact (rankSymmetric256Certificate_142).2.2
    · exact (rankSymmetric256Certificate_143).2.2
    · exact (rankSymmetric256Certificate_144).2.2
    · exact (rankSymmetric256Certificate_145).2.2
    · exact (rankSymmetric256Certificate_146).2.2
    · exact (rankSymmetric256Certificate_147).2.2
    · exact (rankSymmetric256Certificate_148).2.2
    · exact (rankSymmetric256Certificate_149).2.2
    · exact (rankSymmetric256Certificate_150).2.2
    · exact (rankSymmetric256Certificate_151).2.2
    · exact (rankSymmetric256Certificate_152).2.2
    · exact (rankSymmetric256Certificate_153).2.2
    · exact (rankSymmetric256Certificate_154).2.2
    · exact (rankSymmetric256Certificate_155).2.2
    · exact (rankSymmetric256Certificate_156).2.2
    · exact (rankSymmetric256Certificate_157).2.2
    · exact (rankSymmetric256Certificate_158).2.2
    · exact (rankSymmetric256Certificate_159).2.2
    · exact (rankSymmetric256Certificate_160).2.2
    · exact (rankSymmetric256Certificate_161).2.2
    · exact (rankSymmetric256Certificate_162).2.2
    · exact (rankSymmetric256Certificate_163).2.2
    · exact (rankSymmetric256Certificate_164).2.2
    · exact (rankSymmetric256Certificate_165).2.2
    · exact (rankSymmetric256Certificate_166).2.2
    · exact (rankSymmetric256Certificate_167).2.2
    · exact (rankSymmetric256Certificate_168).2.2
    · exact (rankSymmetric256Certificate_169).2.2
    · exact (rankSymmetric256Certificate_170).2.2
    · exact (rankSymmetric256Certificate_171).2.2
    · exact (rankSymmetric256Certificate_172).2.2
    · exact (rankSymmetric256Certificate_173).2.2
    · exact (rankSymmetric256Certificate_174).2.2
    · exact (rankSymmetric256Certificate_175).2.2
    · exact (rankSymmetric256Certificate_176).2.2
    · exact (rankSymmetric256Certificate_177).2.2
    · exact (rankSymmetric256Certificate_178).2.2
    · exact (rankSymmetric256Certificate_179).2.2
    · exact (rankSymmetric256Certificate_180).2.2
    · exact (rankSymmetric256Certificate_181).2.2
    · exact (rankSymmetric256Certificate_182).2.2
    · exact (rankSymmetric256Certificate_183).2.2
    · exact (rankSymmetric256Certificate_184).2.2
    · exact (rankSymmetric256Certificate_185).2.2
    · exact (rankSymmetric256Certificate_186).2.2
    · exact (rankSymmetric256Certificate_187).2.2
    · exact (rankSymmetric256Certificate_188).2.2
    · exact (rankSymmetric256Certificate_189).2.2
    · exact (rankSymmetric256Certificate_190).2.2
    · exact (rankSymmetric256Certificate_191).2.2
    · exact (rankSymmetric256Certificate_192).2.2
    · exact (rankSymmetric256Certificate_193).2.2
    · exact (rankSymmetric256Certificate_194).2.2
    · exact (rankSymmetric256Certificate_195).2.2
    · exact (rankSymmetric256Certificate_196).2.2
    · exact (rankSymmetric256Certificate_197).2.2
    · exact (rankSymmetric256Certificate_198).2.2
    · exact (rankSymmetric256Certificate_199).2.2
    · exact (rankSymmetric256Certificate_200).2.2
    · exact (rankSymmetric256Certificate_201).2.2
    · exact (rankSymmetric256Certificate_202).2.2
    · exact (rankSymmetric256Certificate_203).2.2
    · exact (rankSymmetric256Certificate_204).2.2
    · exact (rankSymmetric256Certificate_205).2.2
    · exact (rankSymmetric256Certificate_206).2.2
    · exact (rankSymmetric256Certificate_207).2.2
    · exact (rankSymmetric256Certificate_208).2.2
    · exact (rankSymmetric256Certificate_209).2.2
    · exact (rankSymmetric256Certificate_210).2.2
    · exact (rankSymmetric256Certificate_211).2.2
    · exact (rankSymmetric256Certificate_212).2.2
    · exact (rankSymmetric256Certificate_213).2.2
    · exact (rankSymmetric256Certificate_214).2.2
    · exact (rankSymmetric256Certificate_215).2.2
    · exact (rankSymmetric256Certificate_216).2.2
    · exact (rankSymmetric256Certificate_217).2.2
    · exact (rankSymmetric256Certificate_218).2.2
    · exact (rankSymmetric256Certificate_219).2.2
    · exact (rankSymmetric256Certificate_220).2.2
    · exact (rankSymmetric256Certificate_221).2.2
    · exact (rankSymmetric256Certificate_222).2.2
    · exact (rankSymmetric256Certificate_223).2.2
    · exact (rankSymmetric256Certificate_224).2.2
    · exact (rankSymmetric256Certificate_225).2.2
    · exact (rankSymmetric256Certificate_226).2.2
    · exact (rankSymmetric256Certificate_227).2.2
    · exact (rankSymmetric256Certificate_228).2.2
    · exact (rankSymmetric256Certificate_229).2.2
    · exact (rankSymmetric256Certificate_230).2.2
    · exact (rankSymmetric256Certificate_231).2.2
    · exact (rankSymmetric256Certificate_232).2.2
    · exact (rankSymmetric256Certificate_233).2.2
    · exact (rankSymmetric256Certificate_234).2.2
    · exact (rankSymmetric256Certificate_235).2.2
    · exact (rankSymmetric256Certificate_236).2.2
    · exact (rankSymmetric256Certificate_237).2.2
    · exact (rankSymmetric256Certificate_238).2.2
    · exact (rankSymmetric256Certificate_239).2.2
    · exact (rankSymmetric256Certificate_240).2.2
    · exact (rankSymmetric256Certificate_241).2.2
    · exact (rankSymmetric256Certificate_242).2.2
    · exact (rankSymmetric256Certificate_243).2.2
    · exact (rankSymmetric256Certificate_244).2.2
    · exact (rankSymmetric256Certificate_245).2.2
    · exact (rankSymmetric256Certificate_246).2.2
    · exact (rankSymmetric256Certificate_247).2.2
    · exact (rankSymmetric256Certificate_248).2.2
    · exact (rankSymmetric256Certificate_249).2.2
    · exact (rankSymmetric256Certificate_250).2.2
    · exact (rankSymmetric256Certificate_251).2.2
    · exact (rankSymmetric256Certificate_252).2.2
    · exact (rankSymmetric256Certificate_253).2.2
    · exact (rankSymmetric256Certificate_254).2.2
    · exact (rankSymmetric256Certificate_255).2.2
    · exact (rankSymmetric256Certificate_256).2.2

theorem rankSymmetric256_integral_coefficient (r : ℕ) (hr : 2 ≤ r) (hr256 : r ≤ 256) :
    ((4*rankSymmetric256Parameter r-2)*(r : ℝ)^2+(8*rankSymmetric256Parameter r-5)*r-2) * rankSymmetric256IntegralWeight (r-1) + 2 * rankSymmetric256RootAllowance r * (r : ℝ) ≤ rankSymmetric256Coercivity r * (r : ℝ)^2 * rankSymmetric256IntegralWeight r := by
  by_cases hold : r ≤ 128
  · have hm : r-1 ≤ 128 := by omega
    simpa only [rankSymmetric256IntegralWeight_eq_previous (r-1) hm, rankSymmetric256IntegralWeight_eq_previous r hold, rankSymmetric256Convolution_eq_previous r hold, rankSymmetric256RootAllowance_eq_previous r hold, rankSymmetric256CumulantWeight_eq_previous r hold, rankSymmetric256Parameter_eq_previous r hold, rankSymmetric256Coercivity_eq_previous r hold]
      using rankSymmetric128_integral_coefficient r hr hold
  · have hlo : 129 ≤ r := by omega
    interval_cases r
    · exact (rankSymmetric256Certificate_129).2.1
    · exact (rankSymmetric256Certificate_130).2.1
    · exact (rankSymmetric256Certificate_131).2.1
    · exact (rankSymmetric256Certificate_132).2.1
    · exact (rankSymmetric256Certificate_133).2.1
    · exact (rankSymmetric256Certificate_134).2.1
    · exact (rankSymmetric256Certificate_135).2.1
    · exact (rankSymmetric256Certificate_136).2.1
    · exact (rankSymmetric256Certificate_137).2.1
    · exact (rankSymmetric256Certificate_138).2.1
    · exact (rankSymmetric256Certificate_139).2.1
    · exact (rankSymmetric256Certificate_140).2.1
    · exact (rankSymmetric256Certificate_141).2.1
    · exact (rankSymmetric256Certificate_142).2.1
    · exact (rankSymmetric256Certificate_143).2.1
    · exact (rankSymmetric256Certificate_144).2.1
    · exact (rankSymmetric256Certificate_145).2.1
    · exact (rankSymmetric256Certificate_146).2.1
    · exact (rankSymmetric256Certificate_147).2.1
    · exact (rankSymmetric256Certificate_148).2.1
    · exact (rankSymmetric256Certificate_149).2.1
    · exact (rankSymmetric256Certificate_150).2.1
    · exact (rankSymmetric256Certificate_151).2.1
    · exact (rankSymmetric256Certificate_152).2.1
    · exact (rankSymmetric256Certificate_153).2.1
    · exact (rankSymmetric256Certificate_154).2.1
    · exact (rankSymmetric256Certificate_155).2.1
    · exact (rankSymmetric256Certificate_156).2.1
    · exact (rankSymmetric256Certificate_157).2.1
    · exact (rankSymmetric256Certificate_158).2.1
    · exact (rankSymmetric256Certificate_159).2.1
    · exact (rankSymmetric256Certificate_160).2.1
    · exact (rankSymmetric256Certificate_161).2.1
    · exact (rankSymmetric256Certificate_162).2.1
    · exact (rankSymmetric256Certificate_163).2.1
    · exact (rankSymmetric256Certificate_164).2.1
    · exact (rankSymmetric256Certificate_165).2.1
    · exact (rankSymmetric256Certificate_166).2.1
    · exact (rankSymmetric256Certificate_167).2.1
    · exact (rankSymmetric256Certificate_168).2.1
    · exact (rankSymmetric256Certificate_169).2.1
    · exact (rankSymmetric256Certificate_170).2.1
    · exact (rankSymmetric256Certificate_171).2.1
    · exact (rankSymmetric256Certificate_172).2.1
    · exact (rankSymmetric256Certificate_173).2.1
    · exact (rankSymmetric256Certificate_174).2.1
    · exact (rankSymmetric256Certificate_175).2.1
    · exact (rankSymmetric256Certificate_176).2.1
    · exact (rankSymmetric256Certificate_177).2.1
    · exact (rankSymmetric256Certificate_178).2.1
    · exact (rankSymmetric256Certificate_179).2.1
    · exact (rankSymmetric256Certificate_180).2.1
    · exact (rankSymmetric256Certificate_181).2.1
    · exact (rankSymmetric256Certificate_182).2.1
    · exact (rankSymmetric256Certificate_183).2.1
    · exact (rankSymmetric256Certificate_184).2.1
    · exact (rankSymmetric256Certificate_185).2.1
    · exact (rankSymmetric256Certificate_186).2.1
    · exact (rankSymmetric256Certificate_187).2.1
    · exact (rankSymmetric256Certificate_188).2.1
    · exact (rankSymmetric256Certificate_189).2.1
    · exact (rankSymmetric256Certificate_190).2.1
    · exact (rankSymmetric256Certificate_191).2.1
    · exact (rankSymmetric256Certificate_192).2.1
    · exact (rankSymmetric256Certificate_193).2.1
    · exact (rankSymmetric256Certificate_194).2.1
    · exact (rankSymmetric256Certificate_195).2.1
    · exact (rankSymmetric256Certificate_196).2.1
    · exact (rankSymmetric256Certificate_197).2.1
    · exact (rankSymmetric256Certificate_198).2.1
    · exact (rankSymmetric256Certificate_199).2.1
    · exact (rankSymmetric256Certificate_200).2.1
    · exact (rankSymmetric256Certificate_201).2.1
    · exact (rankSymmetric256Certificate_202).2.1
    · exact (rankSymmetric256Certificate_203).2.1
    · exact (rankSymmetric256Certificate_204).2.1
    · exact (rankSymmetric256Certificate_205).2.1
    · exact (rankSymmetric256Certificate_206).2.1
    · exact (rankSymmetric256Certificate_207).2.1
    · exact (rankSymmetric256Certificate_208).2.1
    · exact (rankSymmetric256Certificate_209).2.1
    · exact (rankSymmetric256Certificate_210).2.1
    · exact (rankSymmetric256Certificate_211).2.1
    · exact (rankSymmetric256Certificate_212).2.1
    · exact (rankSymmetric256Certificate_213).2.1
    · exact (rankSymmetric256Certificate_214).2.1
    · exact (rankSymmetric256Certificate_215).2.1
    · exact (rankSymmetric256Certificate_216).2.1
    · exact (rankSymmetric256Certificate_217).2.1
    · exact (rankSymmetric256Certificate_218).2.1
    · exact (rankSymmetric256Certificate_219).2.1
    · exact (rankSymmetric256Certificate_220).2.1
    · exact (rankSymmetric256Certificate_221).2.1
    · exact (rankSymmetric256Certificate_222).2.1
    · exact (rankSymmetric256Certificate_223).2.1
    · exact (rankSymmetric256Certificate_224).2.1
    · exact (rankSymmetric256Certificate_225).2.1
    · exact (rankSymmetric256Certificate_226).2.1
    · exact (rankSymmetric256Certificate_227).2.1
    · exact (rankSymmetric256Certificate_228).2.1
    · exact (rankSymmetric256Certificate_229).2.1
    · exact (rankSymmetric256Certificate_230).2.1
    · exact (rankSymmetric256Certificate_231).2.1
    · exact (rankSymmetric256Certificate_232).2.1
    · exact (rankSymmetric256Certificate_233).2.1
    · exact (rankSymmetric256Certificate_234).2.1
    · exact (rankSymmetric256Certificate_235).2.1
    · exact (rankSymmetric256Certificate_236).2.1
    · exact (rankSymmetric256Certificate_237).2.1
    · exact (rankSymmetric256Certificate_238).2.1
    · exact (rankSymmetric256Certificate_239).2.1
    · exact (rankSymmetric256Certificate_240).2.1
    · exact (rankSymmetric256Certificate_241).2.1
    · exact (rankSymmetric256Certificate_242).2.1
    · exact (rankSymmetric256Certificate_243).2.1
    · exact (rankSymmetric256Certificate_244).2.1
    · exact (rankSymmetric256Certificate_245).2.1
    · exact (rankSymmetric256Certificate_246).2.1
    · exact (rankSymmetric256Certificate_247).2.1
    · exact (rankSymmetric256Certificate_248).2.1
    · exact (rankSymmetric256Certificate_249).2.1
    · exact (rankSymmetric256Certificate_250).2.1
    · exact (rankSymmetric256Certificate_251).2.1
    · exact (rankSymmetric256Certificate_252).2.1
    · exact (rankSymmetric256Certificate_253).2.1
    · exact (rankSymmetric256Certificate_254).2.1
    · exact (rankSymmetric256Certificate_255).2.1
    · exact (rankSymmetric256Certificate_256).2.1

end KLS.RouteArithmetic
end
