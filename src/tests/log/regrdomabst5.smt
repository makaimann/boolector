(benchmark notroot221
:logic QF_BV
:extrafuns ((v0 BitVec[13]))
:extrafuns ((v1 BitVec[11]))
:extrafuns ((v2 BitVec[15]))
:extrafuns ((v3 BitVec[15]))
:extrafuns ((v4 BitVec[11]))
:status unknown
:formula
(let (?e6 bv1[1])
(let (?e7 bv0[1])
(let (?e8 bv479[10])
(let (?e9 bv2[4])
(let (?e10 (bvand ?e7 (bvnot ?e6)))
(let (?e11 bv0[4])
(let (?e12 (concat ?e11 v1))
(let (?e13 (ite (= v3 ?e12) bv1[1] bv0[1]))
(let (?e14 (ite (= bv1[1] (bvnot ?e13)) ?e6 ?e7))
(let (?e15 bv0[10])
(let (?e16 (concat ?e15 ?e6))
(let (?e17 (ite (bvult v4 ?e16) bv1[1] bv0[1]))
(let (?e18 (ite (= bv1[1] ?e17) ?e6 ?e7))
(let (?e19 (concat ?e15 ?e10))
(let (?e20 (extract[10:10] ?e19))
(let (?e21 (extract[10:10] v1))
(let (?e22 (extract[9:0] ?e19))
(let (?e23 (extract[9:0] v1))
(let (?e24 (ite (bvult ?e22 ?e23) bv1[1] bv0[1]))
(let (?e25 (bvand ?e20 (bvnot ?e21)))
(let (?e26 (bvand (bvnot ?e20) (bvnot ?e21)))
(let (?e27 (bvand ?e20 ?e21))
(let (?e28 (bvand ?e26 ?e24))
(let (?e29 (bvand ?e27 ?e24))
(let (?e30 (bvand (bvnot ?e28) (bvnot ?e29)))
(let (?e31 (bvand (bvnot ?e25) ?e30))
(let (?e32 (ite (= bv1[1] ?e31) ?e6 ?e7))
(let (?e33 bv0[3])
(let (?e34 (concat ?e33 ?e14))
(let (?e35 (bvand (bvnot ?e9) (bvnot ?e34)))
(let (?e36 bv7[3])
(let (?e37 (extract[0:0] ?e10))
(let (?e38 (ite (= bv1[1] ?e37) ?e36 ?e33))
(let (?e39 (concat ?e38 ?e10))
(let (?e40 (extract[3:3] ?e39))
(let (?e41 (extract[3:3] ?e9))
(let (?e42 (extract[2:0] ?e39))
(let (?e43 (extract[2:0] ?e9))
(let (?e44 (ite (bvult ?e42 ?e43) bv1[1] bv0[1]))
(let (?e45 (bvand ?e40 (bvnot ?e41)))
(let (?e46 (bvand (bvnot ?e40) (bvnot ?e41)))
(let (?e47 (bvand ?e40 ?e41))
(let (?e48 (bvand ?e46 ?e44))
(let (?e49 (bvand ?e47 ?e44))
(let (?e50 (bvand (bvnot ?e48) (bvnot ?e49)))
(let (?e51 (bvand (bvnot ?e45) ?e50))
(let (?e52 (ite (= bv1[1] (bvnot ?e51)) ?e6 ?e7))
(let (?e53 (extract[0:0] ?e14))
(let (?e54 (ite (= bv1[1] ?e53) ?e36 ?e33))
(let (?e55 (concat ?e54 ?e14))
(let (?e56 (ite (bvult ?e55 ?e35) bv1[1] bv0[1]))
(let (?e57 (ite (= bv1[1] (bvnot ?e56)) ?e6 ?e7))
(let (?e58 (bvadd ?e35 ?e35))
(let (?e59 bv1023[10])
(let (?e60 (extract[0:0] ?e52))
(let (?e61 (ite (= bv1[1] ?e60) ?e59 ?e15))
(let (?e62 (concat ?e61 ?e52))
(let (?e63 (extract[10:4] v4))
(let (?e64 (extract[3:0] v4))
(let (?e65 bv0[7])
(let (?e66 (ite (= ?e63 ?e65) bv1[1] bv0[1]))
(let (?e67 bv0[11])
(let (?e68 bv0[5])
(let (?e69 (concat ?e68 ?e62))
(let (?e70 (bvlshr ?e69  (zero_extend[12] ?e64)))
(let (?e71 (extract[10:0] ?e70))
(let (?e72 (ite (= bv1[1] (bvnot ?e66)) ?e67 ?e71))
(let (?e73 (concat ?e7 ?e14))
(let (?e74 bv0[12])
(let (?e75 (concat ?e74 ?e7))
(let (?e76 (ite (= ?e75 v0) bv1[1] bv0[1]))
(let (?e77 (ite (= bv1[1] (bvnot ?e76)) ?e6 ?e7))
(let (?e78 (ite (= ?e12 v2) bv1[1] bv0[1]))
(let (?e79 (ite (= bv1[1] ?e78) ?e6 ?e7))
(let (?e80 (extract[1:0] ?e35))
(let (?e81 (extract[3:2] ?e35))
(let (?e82 (concat ?e80 ?e81))
(let (?e83 (extract[0:0] ?e77))
(let (?e84 (ite (= bv1[1] ?e83) ?e36 ?e33))
(let (?e85 (concat ?e84 ?e77))
(let (?e86 (extract[3:3] ?e85))
(let (?e87 (extract[2:0] ?e85))
(let (?e88 (ite (bvult ?e43 ?e87) bv1[1] bv0[1]))
(let (?e89 (bvand ?e41 (bvnot ?e86)))
(let (?e90 (bvand (bvnot ?e41) (bvnot ?e86)))
(let (?e91 (bvand ?e41 ?e86))
(let (?e92 (bvand ?e90 ?e88))
(let (?e93 (bvand ?e91 ?e88))
(let (?e94 (bvand (bvnot ?e92) (bvnot ?e93)))
(let (?e95 (bvand (bvnot ?e89) ?e94))
(let (?e96 (ite (= bv1[1] (bvnot ?e95)) ?e6 ?e7))
(let (?e97 bv0[9])
(let (?e98 bv511[9])
(let (?e99 (ite (= bv1[1] ?e41) ?e98 ?e97))
(let (?e100 (concat ?e99 ?e9))
(let (?e101 (ite (bvult ?e100 v0) bv1[1] bv0[1]))
(let (?e102 (ite (= bv1[1] ?e101) ?e6 ?e7))
(let (?e103 (ite (= bv1[1] ?e37) ?e6 ?e7))
(let (?e104 (concat ?e103 ?e10))
(let (?e105 (extract[1:1] ?e73))
(let (?e106 (extract[1:1] ?e104))
(let (?e107 (extract[0:0] ?e73))
(let (?e108 (extract[0:0] ?e104))
(let (?e109 (ite (bvult ?e107 ?e108) bv1[1] bv0[1]))
(let (?e110 (bvand ?e105 (bvnot ?e106)))
(let (?e111 (bvand (bvnot ?e105) (bvnot ?e106)))
(let (?e112 (bvand ?e105 ?e106))
(let (?e113 (bvand ?e111 ?e109))
(let (?e114 (bvand ?e112 ?e109))
(let (?e115 (bvand (bvnot ?e113) (bvnot ?e114)))
(let (?e116 (bvand (bvnot ?e110) ?e115))
(let (?e117 (ite (= bv1[1] ?e116) ?e6 ?e7))
(let (?e118 (extract[3:3] ?e82))
(let (?e119 (ite (= bv1[1] ?e118) ?e98 ?e97))
(let (?e120 (concat ?e119 ?e82))
(let (?e121 (extract[12:12] v0))
(let (?e122 (extract[12:12] ?e120))
(let (?e123 (extract[11:0] v0))
(let (?e124 (extract[11:0] ?e120))
(let (?e125 (ite (bvult ?e123 ?e124) bv1[1] bv0[1]))
(let (?e126 (bvand ?e121 (bvnot ?e122)))
(let (?e127 (bvand (bvnot ?e121) (bvnot ?e122)))
(let (?e128 (bvand ?e121 ?e122))
(let (?e129 (bvand ?e127 ?e125))
(let (?e130 (bvand ?e128 ?e125))
(let (?e131 (bvand (bvnot ?e129) (bvnot ?e130)))
(let (?e132 (bvand (bvnot ?e126) ?e131))
(let (?e133 (ite (= bv1[1] (bvnot ?e132)) ?e6 ?e7))
(let (?e134 (ite (= v3 v2) bv1[1] bv0[1]))
(let (?e135 (ite (= bv1[1] ?e134) ?e6 ?e7))
(let (?e136 (extract[0:0] ?e79))
(let (?e137 (ite (= bv1[1] ?e136) ?e36 ?e33))
(let (?e138 (concat ?e137 ?e79))
(let (?e139 (extract[3:2] ?e138))
(let (?e140 (extract[1:0] ?e138))
(let (?e141 bv0[2])
(let (?e142 (ite (= ?e139 ?e141) bv1[1] bv0[1]))
(let (?e143 (extract[0:0] ?e118))
(let (?e144 (ite (= bv1[1] ?e143) ?e36 ?e33))
(let (?e145 (concat ?e144 ?e118))
(let (?e146 (bvlshr ?e82  (zero_extend[2] ?e140)))
(let (?e147 (bvlshr (bvnot ?e82)  (zero_extend[2] ?e140)))
(let (?e148 (ite (= bv1[1] ?e118) (bvnot ?e147) ?e146))
(let (?e149 (ite (= bv1[1] (bvnot ?e142)) ?e145 ?e148))
(let (?e150 (extract[2:0] ?e82))
(let (?e151 (ite (bvult ?e150 ?e150) bv1[1] bv0[1]))
(let (?e152 (bvand ?e118 (bvnot ?e118)))
(let (?e153 (bvand (bvnot ?e118) (bvnot ?e118)))
(let (?e154 (bvand ?e118 ?e118))
(let (?e155 (bvand ?e153 ?e151))
(let (?e156 (bvand ?e154 ?e151))
(let (?e157 (bvand (bvnot ?e155) (bvnot ?e156)))
(let (?e158 (bvand (bvnot ?e152) ?e157))
(let (?e159 (ite (= bv1[1] ?e158) ?e6 ?e7))
(let (?e160 (ite (= bv1[1] ?e53) ?e59 ?e15))
(let (?e161 (concat ?e160 ?e14))
(let (?e162 (ite (= ?e72 ?e161) bv1[1] bv0[1]))
(let (?e163 (ite (= bv1[1] ?e162) ?e6 ?e7))
(let (?e164 (concat ?e97 ?e79))
(let (?e165 (ite (bvult ?e164 ?e8) bv1[1] bv0[1]))
(let (?e166 (ite (= bv1[1] ?e165) ?e6 ?e7))
(let (?e167 (ite (bvult ?e18 ?e32) bv1[1] bv0[1]))
(let (?e168 (ite (= bv1[1] (bvnot ?e167)) ?e6 ?e7))
(let (?e169 (bvand ?e133 (bvnot ?e57)))
(let (?e170 (ite (= bv1[1] ?e169) ?e6 ?e7))
(let (?e171 (ite (bvult ?e102 ?e96) bv1[1] bv0[1]))
(let (?e172 (ite (= bv1[1] (bvnot ?e171)) ?e6 ?e7))
(let (?e173 (concat ?e33 ?e163))
(let (?e174 (extract[3:3] ?e149))
(let (?e175 (extract[3:3] ?e173))
(let (?e176 (extract[2:0] ?e149))
(let (?e177 (extract[2:0] ?e173))
(let (?e178 (ite (bvult ?e176 ?e177) bv1[1] bv0[1]))
(let (?e179 (bvand ?e174 (bvnot ?e175)))
(let (?e180 (bvand (bvnot ?e174) (bvnot ?e175)))
(let (?e181 (bvand ?e174 ?e175))
(let (?e182 (bvand ?e180 ?e178))
(let (?e183 (bvand ?e181 ?e178))
(let (?e184 (bvand (bvnot ?e182) (bvnot ?e183)))
(let (?e185 (bvand (bvnot ?e179) ?e184))
(let (?e186 (ite (= bv1[1] (bvnot ?e185)) ?e6 ?e7))
(let (?e187 (bvand ?e117 (bvnot ?e135)))
(let (?e188 (ite (= bv1[1] ?e187) ?e6 ?e7))
(let (?e189 (concat ?e33 ?e159))
(let (?e190 (extract[3:3] ?e58))
(let (?e191 (extract[3:3] ?e189))
(let (?e192 (extract[2:0] ?e58))
(let (?e193 (extract[2:0] ?e189))
(let (?e194 (ite (bvult ?e192 ?e193) bv1[1] bv0[1]))
(let (?e195 (bvand ?e190 (bvnot ?e191)))
(let (?e196 (bvand (bvnot ?e190) (bvnot ?e191)))
(let (?e197 (bvand ?e190 ?e191))
(let (?e198 (bvand ?e196 ?e194))
(let (?e199 (bvand ?e197 ?e194))
(let (?e200 (bvand (bvnot ?e198) (bvnot ?e199)))
(let (?e201 (bvand (bvnot ?e195) ?e200))
(let (?e202 (ite (= bv1[1] ?e201) ?e6 ?e7))
(let (?e203 (bvand ?e166 ?e14))
(let (?e204 (ite (= bv1[1] (bvnot ?e203)) ?e6 ?e7))
(let (?e205 (ite (= ?e204 ?e6) bv1[1] bv0[1]))
(let (?e206 (ite (= ?e170 ?e6) bv1[1] bv0[1]))
(let (?e207 (ite (= ?e168 ?e7) bv1[1] bv0[1]))
(let (?e208 (ite (= ?e202 ?e7) bv1[1] bv0[1]))
(let (?e209 (ite (= ?e188 ?e6) bv1[1] bv0[1]))
(let (?e210 (ite (= ?e186 ?e6) bv1[1] bv0[1]))
(let (?e211 (ite (= ?e172 ?e7) bv1[1] bv0[1]))
(let (?e212 (bvand (bvnot ?e210) (bvnot ?e211)))
(let (?e213 (bvand (bvnot ?e208) (bvnot ?e209)))
(let (?e214 (bvand ?e208 ?e209))
(let (?e215 (bvand (bvnot ?e213) (bvnot ?e214)))
(let (?e216 (bvand (bvnot ?e206) (bvnot ?e207)))
(let (?e217 (bvand (bvnot ?e215) ?e216))
(let (?e218 (bvand (bvnot ?e205) (bvnot ?e212)))
(let (?e219 (bvand (bvnot ?e218) ?e217))
(let (?e220 (bvand ?e218 (bvnot ?e217)))
(let (?e221 (bvand (bvnot ?e219) (bvnot ?e220)))
(not (= (bvnot ?e221) bv0[1]))
)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
