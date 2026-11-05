module

public import Workspace.Impl.VsQPolyC

@[expose] public section

/-!
# The whole program

All programs as one sparse program (`spProg`): block `k` starts at `10000 k`. The blocks of the hard
case and of the `Q₈` continuation are a parameter `extra`, appended after the blocks here, and
their entry points `hard` and `q8c` are parameters too. `vsQLay` checks every layout fact.
This file is generated from the layout structures.
-/

namespace GI.Impl

open GI.Lang GI.Cited

set_option maxRecDepth 100000

/-- The blocks of the program. -/
def vsQBlocks (hard q8c : ℕ) : List (List Expr) := [
    -- 0 X.top.top
    [(vsQTopE 10000 20000 40000 50000 60000 90000 110000 100000)],
    -- 1 X.top.rng
    (rangeFuns 10000),
    -- 2 X.top.fold
    (foldlFuns 20000 30000),
    -- 3 X.top.st
    [vsQFactStepE],
    -- 4 X.top.idp
    (vsWIdFuns 40000),
    -- 5 X.top.rep
    (replicateFuns 50000),
    -- 6 X.top.tbm
    (mapFuns 60000 70000),
    -- 7 X.top.it
    [(vsQTblItE 80000)],
    -- 8 X.top.tr
    (vsQTrFuns 80000),
    -- 9 X.top.red
    (reduceFuns 90000 0),
    -- 10 X.top.tl
    (linTailFuns 100000),
    -- 11 X.drv.drv
    (vsQDrvFuns 110000 120000 130000 140000 150000),
    -- 12 X.ana.ana
    [(vsQAnaE 260000 270000 300000 360000 280000 290000)],
    -- 13 X.drv.ai
    [(vsQAppE 160000 180000 (170000 + 3))],
    -- 14 X.drv.cmp
    (composeFuns 140000),
    -- 15 X.drv.paste
    [(vsQPasteE 190000 200000 210000 220000 230000 240000)],
    -- 16 X.drv.inv
    (invFuns 160000),
    -- 17 X.drv.mm
    (vsFMatMulFuns 170000),
    -- 18 X.phi.phi
    (vsQPhiFuns 180000 5 2840000 (2840000 + 2)),
    -- 19 X.drv.fd
    (findFuns 190000 (190000 + 3)) ++ [vsQPTestE],
    -- 20 X.drv.pinv
    (invFuns 200000),
    -- 21 X.drv.pmp
    (mapFuns 210000 (210000 + 3)) ++ [(vsQPMapE 250000)],
    -- 22 X.drv.app
    (appendFuns 220000),
    -- 23 X.drv.mkg
    (mkGroupFuns 230000),
    -- 24 X.drv.red
    (reduceFuns 240000 0),
    -- 25 X.drv.pcmp
    (composeFuns 250000),
    -- 26 X.ana.lcp
    (vsQLCFuns 260000 180000),
    -- 27 X.ana.orb
    (vsBOrbFuns 270000 180000 1 0),
    -- 28 X.ana.abb
    (vsQAbFuns 280000 440000),
    -- 29 X.al.al
    [(vsQALE 840000 1720000 820000 290000)],
    -- 30 X.ana.ctx
    [(vsPCtxE 310000 340000 350000)],
    -- 31 X.ana.flm
    (mapFuns 310000 320000),
    -- 32 X.ana.it
    [(vsPFlItemE 330000)],
    -- 33 X.ana.fl
    (vsWFlatFuns 330000),
    -- 34 X.ana.rws
    (vsWRowsFuns 340000),
    -- 35 X.ana.rep
    (replicateFuns 350000),
    -- 36 X.ana.abt
    [(vsPAbE 370000)],
    -- 37 X.ana.fo
    (findFuns 370000 380000),
    -- 38 X.ana.no
    [(vsPNoE 390000)],
    -- 39 X.ana.fi
    (findFuns 390000 400000),
    -- 40 X.ana.nc
    [(vsPNcE 410000 420000 430000)],
    -- 41 X.ana.comp
    (composeFuns 410000),
    -- 42 X.ana.loc
    [(vsPLocE 180000 (420000 + 1))] ++ (vsWLocFuns (420000 + 1)),
    -- 43 X.ana.eq
    (vsPEqFuns 430000),
    -- 44 X.ana.fld.f
    [(vsBFldE 450000 460000 470000)],
    -- 45 X.ana.fld.prep
    [(vsBPrepE 480000 490000 500000 510000 520000 530000 540000)],
    -- 46 X.ana.fld.c0
    [(vsB0E 590000 610000 630000)],
    -- 47 X.ana.fld.cM
    [(vsBCaseME 500000 790000 800000 490000 660000)],
    -- 48 X.ana.fld.unit
    (vsUnitFuns 480000),
    -- 49 X.ana.fld.appd
    (appendFuns 490000),
    -- 50 X.ana.fld.rng
    (rangeFuns 500000),
    -- 51 X.ana.fld.chA
    (vsBChainFuns 510000 (550000 + 22)),
    -- 52 X.ana.fld.chB
    (vsBChainFuns 520000 (560000 + 22)),
    -- 53 X.ana.fld.co
    (vsWCoFuns 530000),
    -- 54 X.ana.fld.lin
    (vsLinFuns 540000),
    -- 55 X.ana.fld.sotA
    (vsQSotFuns 550000 (570000 + 1) 1 0),
    -- 56 X.ana.fld.sotB
    (vsQSotFuns 560000 580000 1 0),
    -- 57 X.ana.fld.bA
    (vsBAFuns 570000 180000),
    -- 58 X.ana.fld.bB
    (vsBBFuns 580000 180000),
    -- 59 X.ana.fld.fd
    (findFuns 590000 600000),
    -- 60 X.ana.fld.tst
    [(vsBTestE (580000 + 3) (580000 + 4) 630000)],
    -- 61 X.ana.fld.c0b
    [(vsB0bE 620000 540000 630000 640000 500000 650000 660000 490000)],
    -- 62 X.ana.fld.m
    [(vsB0mE (570000 + 4) 670000 (580000 + 3) (580000 + 4) 680000)],
    -- 63 X.ana.fld.eqN
    (eqNatsFuns 630000),
    -- 64 X.ana.fld.tau
    [(vsB0TauE 690000 730000 710000 740000 (750000 + 3) 770000)],
    -- 65 X.ana.fld.dA
    (vsBDescFuns 650000 (570000 + 2) (550000 + 8) (570000 + 3) 780000),
    -- 66 X.ana.fld.red
    (reduceFuns 660000 0),
    -- 67 X.ana.fld.sc
    (vsWSubCFuns 670000),
    -- 68 X.ana.fld.sv
    (vsBSolveFuns 680000),
    -- 69 X.ana.fld.mI
    (mapFuns 690000 700000),
    -- 70 X.ana.fld.fI
    [(vsB0ImgE (750000 + 3))],
    -- 71 X.ana.fld.mF
    (mapFuns 710000 720000),
    -- 72 X.ana.fld.fF
    [(vsB0FlatE 760000)],
    -- 73 X.ana.fld.sv2
    (vsBSolveFuns 730000),
    -- 74 X.ana.fld.rp
    (replicateFuns 740000),
    -- 75 X.ana.fld.mm
    (vsFMatMulFuns 750000),
    -- 76 X.ana.fld.fl
    (vsWFlatFuns 760000),
    -- 77 X.ana.fld.ch
    (vsQChunkFuns 770000),
    -- 78 X.ana.fld.cmp
    (composeFuns 780000),
    -- 79 X.ana.fld.dB
    (vsBDescFuns 790000 (580000 + 1) (560000 + 8) (580000 + 2) 780000),
    -- 80 X.ana.fld.mc
    (mapFuns 800000 810000),
    -- 81 X.ana.fld.cr
    [(vsBCorrE (580000 + 3) (580000 + 4) (580000 + 32) 790000 780000)],
    -- 82 X.al.s4
    [(vsQA4E 830000 hard q8c)],
    -- 83 X.al.st4
    [(vsPStep4E 2740000 2800000 2500000 2550000 2630000 2730000)],
    -- 84 X.al.x2.f
    [(vsQA2AE 850000 910000 920000 930000 940000 950000 960000 970000)],
    -- 85 X.al.x2.bm
    [(vsQABmE 860000 890000 900000)],
    -- 86 X.al.x2.mpb
    (mapFuns 860000 870000),
    -- 87 X.al.x2.itb
    [(vsHLocItE 880000)],
    -- 88 X.al.x2.locb
    [(vsPLocE 180000 (880000 + 1))] ++ (vsWLocFuns (880000 + 1)),
    -- 89 X.al.x2.idpb
    (vsWIdFuns 890000),
    -- 90 X.al.x2.algb
    (vsFAlgSpanFuns 900000),
    -- 91 X.al.x2.bas
    (vsWBasFuns 910000),
    -- 92 X.al.x2.ann
    (vsFAnnFuns 920000),
    -- 93 X.al.x2.nil
    (vsFNilFuns 930000),
    -- 94 X.al.x2.eig
    (vsFEigFuns 940000),
    -- 95 X.al.x2.fix
    (vsFFixFuns 950000),
    -- 96 X.al.x2.spl
    (vsQSplFuns 960000),
    -- 97 X.al.x2.s.f
    [(vsQA2SE 980000 990000 1010000 1000000 1070000)],
    -- 98 X.al.x2.s.idp
    (vsWIdFuns 980000),
    -- 99 X.al.x2.s.alg
    (vsFAlgSpanFuns 990000),
    -- 100 X.al.x2.s.spl
    (vsQSplFuns 1000000),
    -- 101 X.al.x2.s.sp.f
    [(vsQASpinE 1020000 1050000 1060000)],
    -- 102 X.al.x2.s.sp.mp
    (mapFuns 1020000 1030000),
    -- 103 X.al.x2.s.sp.it
    [(vsQASpinItE 1040000)],
    -- 104 X.al.x2.s.sp.img
    (vsWImgFuns 1040000),
    -- 105 X.al.x2.s.sp.cat
    (vsWFlatFuns 1050000),
    -- 106 X.al.x2.s.sp.bas
    (vsWBasFuns 1060000),
    -- 107 X.al.x2.s.t.f
    [(vsQA2TE 1100000 2 1300000 1080000 1390000)],
    -- 108 X.al.x2.s.t.itq
    (iterFuns 1080000 1090000),
    -- 109 X.al.x2.s.t.st
    [vsHMulE],
    -- 110 X.al.x2.s.t.t.f
    [(vsQATblE 1110000 1160000)],
    -- 111 X.al.x2.s.t.t.mpk
    (mapFuns 1110000 1120000),
    -- 112 X.al.x2.s.t.t.ki
    [(vsQTKeyItemE 1130000 1140000 1150000)],
    -- 113 X.al.x2.s.t.t.key
    (vsWKeyFuns 1130000),
    -- 114 X.al.x2.s.t.t.cat
    (vsWFlatFuns 1140000),
    -- 115 X.al.x2.s.t.t.appd
    (appendFuns 1150000),
    -- 116 X.al.x2.s.t.t.mpo
    (mapFuns 1160000 1170000),
    -- 117 X.al.x2.s.t.t.fo
    [(vsQATbOutE 1180000)],
    -- 118 X.al.x2.s.t.t.mpi
    (mapFuns 1180000 1190000),
    -- 119 X.al.x2.s.t.t.fi
    [(vsQATbInE 1200000 1280000)],
    -- 120 X.al.x2.s.t.t.it
    [(vsQTItemE 1210000 1220000 1230000 1240000 1250000 1260000 1270000)],
    -- 121 X.al.x2.s.t.t.tl
    (linTailFuns 1210000),
    -- 122 X.al.x2.s.t.t.chk
    (vsQChunkFuns 1220000),
    -- 123 X.al.x2.s.t.t.ker
    (vsWKerFuns 1230000),
    -- 124 X.al.x2.s.t.t.img
    (vsWImgFuns 1240000),
    -- 125 X.al.x2.s.t.t.key'
    (vsWKeyFuns 1250000),
    -- 126 X.al.x2.s.t.t.cat'
    (vsWFlatFuns 1260000),
    -- 127 X.al.x2.s.t.t.appd'
    (appendFuns 1270000),
    -- 128 X.al.x2.s.t.t.fnd
    (findFuns 1280000 1290000),
    -- 129 X.al.x2.s.t.t.eq
    (eqNatsFuns 1290000),
    -- 130 X.al.x2.s.t.b.f
    [(vsQABlksE 1310000 1320000 1370000)],
    -- 131 X.al.x2.s.t.b.rng
    (rangeFuns 1310000),
    -- 132 X.al.x2.s.t.b.mpo
    (mapFuns 1320000 1330000),
    -- 133 X.al.x2.s.t.b.fo
    [(vsQABlkE 1310000 1340000 1360000)],
    -- 134 X.al.x2.s.t.b.mpi
    (mapFuns 1340000 1350000),
    -- 135 X.al.x2.s.t.b.fi
    [vsQABlkIE],
    -- 136 X.al.x2.s.t.b.cat
    (vsWFlatFuns 1360000),
    -- 137 X.al.x2.s.t.b.flt
    (filterFuns 1370000 1380000),
    -- 138 X.al.x2.s.t.b.fn
    [vsQANonE],
    -- 139 X.al.x2.s.t.w.f
    [(vsQTSplE 1400000 1420000 1430000 1440000 1450000 1470000 1490000 1510000)],
    -- 140 X.al.x2.s.t.w.kmp
    (mapFuns 1400000 1410000),
    -- 141 X.al.x2.s.t.w.kI
    [(vsQTKeyItemE 1520000 1530000 1540000)],
    -- 142 X.al.x2.s.t.w.cat
    (vsWFlatFuns 1420000),
    -- 143 X.al.x2.s.t.w.appd
    (appendFuns 1430000),
    -- 144 X.al.x2.s.t.w.tl
    (linTailFuns 1440000),
    -- 145 X.al.x2.s.t.w.so
    (vsQSotFuns 1450000 1460000 1 0),
    -- 146 X.al.x2.s.t.w.fa
    [(vsQTActE 1590000 1610000 1620000 1630000 1700000 1710000)],
    -- 147 X.al.x2.s.t.w.smp
    (mapFuns 1470000 1480000),
    -- 148 X.al.x2.s.t.w.sI
    [vsQTSndE],
    -- 149 X.al.x2.s.t.w.lmp
    (mapFuns 1490000 1500000),
    -- 150 X.al.x2.s.t.w.lI
    [(vsQTLowE 1550000 1560000 1570000 1580000)],
    -- 151 X.al.x2.s.t.w.rng
    (rangeFuns 1510000),
    -- 152 X.al.x2.s.t.w.key'
    (vsWKeyFuns 1520000),
    -- 153 X.al.x2.s.t.w.cat'
    (vsWFlatFuns 1530000),
    -- 154 X.al.x2.s.t.w.appd'
    (appendFuns 1540000),
    -- 155 X.al.x2.s.t.w.tk
    (linTakeFuns 1550000),
    -- 156 X.al.x2.s.t.w.cat''
    (vsWFlatFuns 1560000),
    -- 157 X.al.x2.s.t.w.lift
    (vsWLiftFuns 1570000),
    -- 158 X.al.x2.s.t.w.bas
    (vsWBasFuns 1580000),
    -- 159 X.al.x2.s.t.w.itm
    [(vsQLCItemE 180000 1600000)],
    -- 160 X.al.x2.s.t.w.loc
    (vsWLocFuns 1600000),
    -- 161 X.al.x2.s.t.w.tl₁
    (linTailFuns 1610000),
    -- 162 X.al.x2.s.t.w.chk
    (vsQChunkFuns 1620000),
    -- 163 X.al.x2.s.t.w.mp
    (mapFuns 1630000 1640000),
    -- 164 X.al.x2.s.t.w.fI
    [(vsQTItemE 1650000 1660000 1670000 1680000 1690000 1700000 1710000)],
    -- 165 X.al.x2.s.t.w.tl'
    (linTailFuns 1650000),
    -- 166 X.al.x2.s.t.w.chk'
    (vsQChunkFuns 1660000),
    -- 167 X.al.x2.s.t.w.ker
    (vsWKerFuns 1670000),
    -- 168 X.al.x2.s.t.w.img
    (vsWImgFuns 1680000),
    -- 169 X.al.x2.s.t.w.key
    (vsWKeyFuns 1690000),
    -- 170 X.al.x2.s.t.w.cat₂
    (vsWFlatFuns 1700000),
    -- 171 X.al.x2.s.t.w.appd₂
    (appendFuns 1710000),
    -- 172 X.al.x3.f
    [(vsQA3E 1990000 1730000 1790000)],
    -- 173 X.al.x3.ctx
    [(vsPCtxE 1740000 1770000 1780000)],
    -- 174 X.al.x3.flm
    (mapFuns 1740000 1750000),
    -- 175 X.al.x3.it
    [(vsPFlItemE 1760000)],
    -- 176 X.al.x3.fl
    (vsWFlatFuns 1760000),
    -- 177 X.al.x3.rws
    (vsWRowsFuns 1770000),
    -- 178 X.al.x3.rep
    (replicateFuns 1780000),
    -- 179 X.al.x3.ab
    [(vsPAbE 1800000)],
    -- 180 X.al.x3.fo
    (findFuns 1800000 1810000),
    -- 181 X.al.x3.no
    [(vsPNoE 1820000)],
    -- 182 X.al.x3.fi
    (findFuns 1820000 1830000),
    -- 183 X.al.x3.nc
    [(vsPNcE 1840000 1850000 1860000)],
    -- 184 X.al.x3.comp
    (composeFuns 1840000),
    -- 185 X.al.x3.loc
    [(vsPLocE 180000 (1850000 + 1))] ++ (vsWLocFuns (1850000 + 1)),
    -- 186 X.al.x3.eq
    (vsPEqFuns 1860000),
    -- 187 X.al.x3.c.t.c.conj
    [(vsHConjE 1880000 1890000 1900000 1910000 1920000 1930000 1940000)],
    -- 188 X.al.x3.c.t.c.tl
    (tailFuns 1880000),
    -- 189 X.al.x3.c.t.c.ch
    (vsQChunkFuns 1890000),
    -- 190 X.al.x3.c.t.c.loc
    [(vsPLocE 180000 (1900000 + 1))] ++ (vsWLocFuns (1900000 + 1)),
    -- 191 X.al.x3.c.t.c.inv
    (invFuns 1910000),
    -- 192 X.al.x3.c.t.c.mm
    (vsFMatMulFuns 1920000),
    -- 193 X.al.x3.c.t.c.fl
    (vsWFlatFuns 1930000),
    -- 194 X.al.x3.c.t.c.app
    (appendFuns 1940000),
    -- 195 X.al.x3.c.t.conjT
    [(vsHConjTE 1880000 1890000 1960000 1980000 1940000)],
    -- 196 X.al.x3.c.t.mp
    (mapFuns 1960000 1970000),
    -- 197 X.al.x3.c.t.it
    [(vsHConjItE 1870000)],
    -- 198 X.al.x3.c.t.cat
    (vsWFlatFuns 1980000),
    -- 199 X.al.x3.c.q8
    [(vsQCentE 2000000 (2030000 + 22) 2040000)],
    -- 200 X.al.x3.c.y0
    [(vsHY0E 2010000 1980000 1940000)],
    -- 201 X.al.x3.c.mpy
    (mapFuns 2010000 2020000),
    -- 202 X.al.x3.c.ity
    [(vsHPcE 1900000 1930000 1940000)],
    -- 203 X.al.x3.c.sb
    (vsQSotFuns 2030000 1950000 1 0),
    -- 204 X.al.x3.c.mp2
    (mapFuns 2040000 2050000),
    -- 205 X.al.x3.c.it2
    [vsHSndE],
    -- 206 X.al.x4.x2.x3.x4.d.o.orb
    [(vsPOrbE 2160000 2070000)],
    -- 207 X.al.x4.x2.x3.x4.d.o.itb
    (iterFuns 2070000 2080000),
    -- 208 X.al.x4.x2.x3.x4.d.o.st
    [(vsPOItE 2090000)],
    -- 209 X.al.x4.x2.x3.x4.d.o.fo
    (foldlFuns 2090000 2100000),
    -- 210 X.al.x4.x2.x3.x4.d.o.out
    [(vsPOOutE 2110000)],
    -- 211 X.al.x4.x2.x3.x4.d.o.fi
    (foldlFuns 2110000 2120000),
    -- 212 X.al.x4.x2.x3.x4.d.o.ins
    [(vsPOInsE 2130000 2160000 2210000)],
    -- 213 X.al.x4.x2.x3.x4.d.o.conj
    [(vsPConjE 2140000 2150000)],
    -- 214 X.al.x4.x2.x3.x4.d.o.comp
    (composeFuns 2140000),
    -- 215 X.al.x4.x2.x3.x4.d.o.inv
    (invFuns 2150000),
    -- 216 X.al.x4.x2.x3.x4.d.o.key
    [(vsPKeyE 2170000)],
    -- 217 X.al.x4.x2.x3.x4.d.o.mp
    (mapFuns 2170000 2180000),
    -- 218 X.al.x4.x2.x3.x4.d.o.it
    [(vsPKeyItemE 2190000 2200000 2220000)],
    -- 219 X.al.x4.x2.x3.x4.d.o.comm
    [(vsPCommE 2140000 2150000)],
    -- 220 X.al.x4.x2.x3.x4.d.o.loc
    [(vsPLocE 180000 (2200000 + 1))] ++ (vsWLocFuns (2200000 + 1)),
    -- 221 X.al.x4.x2.x3.x4.d.o.fd
    (findFuns 2210000 2230000),
    -- 222 X.al.x4.x2.x3.x4.d.o.fd'
    (findFuns 2220000 2250000),
    -- 223 X.al.x4.x2.x3.x4.d.o.pk
    [(vsPPkE 2240000)],
    -- 224 X.al.x4.x2.x3.x4.d.o.eq
    (eqNatsFuns 2240000),
    -- 225 X.al.x4.x2.x3.x4.d.o.eqb
    (vsPEqFuns 2250000),
    -- 226 X.al.x4.x2.x3.x4.d.dim
    [(vsPDimE 2060000 2270000)],
    -- 227 X.al.x4.x2.x3.x4.d.bas
    (foldlFuns 2270000 2280000),
    -- 228 X.al.x4.x2.x3.x4.d.g
    [(vsPGStepE 2290000)],
    -- 229 X.al.x4.x2.x3.x4.d.ins
    (vsInsertFuns 2290000),
    -- 230 X.al.x4.x2.x3.x4.d.nt
    [(vsPNotInE 2310000)],
    -- 231 X.al.x4.x2.x3.x4.d.inl
    (vsPInLPFuns 2310000 180000),
    -- 232 X.al.x4.x2.x3.x4.e.en
    [(vsPEnumE 2330000 2420000)],
    -- 233 X.al.x4.x2.x3.x4.e.fo
    (foldlFuns 2330000 2340000),
    -- 234 X.al.x4.x2.x3.x4.e.st
    [(vsPEStepE 2350000 2410000)],
    -- 235 X.al.x4.x2.x3.x4.e.mpM
    (mapFuns 2350000 2360000),
    -- 236 X.al.x4.x2.x3.x4.e.mid
    [(vsPEMidE 2370000)],
    -- 237 X.al.x4.x2.x3.x4.e.mpI
    (mapFuns 2370000 2380000),
    -- 238 X.al.x4.x2.x3.x4.e.it
    [(vsPEItemE 2390000 2400000)],
    -- 239 X.al.x4.x2.x3.x4.e.pow
    (vsPPowFuns 2390000),
    -- 240 X.al.x4.x2.x3.x4.e.comp
    (composeFuns 2400000),
    -- 241 X.al.x4.x2.x3.x4.e.cat
    (vsWFlatFuns 2410000),
    -- 242 X.al.x4.x2.x3.x4.e.rng
    (rangeFuns 2420000),
    -- 243 X.al.x4.x2.x3.x4.desc
    [(vsPDescE 2440000)],
    -- 244 X.al.x4.x2.x3.x4.it
    (iterFuns 2440000 2450000),
    -- 245 X.al.x4.x2.x3.x4.st
    [(vsPDsStepE 2260000 2320000 2460000)],
    -- 246 X.al.x4.x2.x3.x4.fnd
    (findFuns 2460000 2470000),
    -- 247 X.al.x4.x2.x3.x4.pr
    [(vsPDPredE 2300000 2260000)],
    -- 248 X.al.x4.x2.x3.x4.fin
    [(vsPFinE 2260000 2490000 2500000)],
    -- 249 X.al.x4.x2.x3.x4.mkg
    (mkGroupFuns 2490000),
    -- 250 X.al.x4.x2.x3.x4.ab
    [(vsPAbE 2510000)],
    -- 251 X.al.x4.x2.x3.x4.fo
    (findFuns 2510000 2520000),
    -- 252 X.al.x4.x2.x3.x4.no
    [(vsPNoE 2530000)],
    -- 253 X.al.x4.x2.x3.x4.fi
    (findFuns 2530000 2540000),
    -- 254 X.al.x4.x2.x3.x4.nc
    [(vsPNcE 2140000 2200000 2250000)],
    -- 255 X.al.x4.x2.x3.x4.grow
    [(vsPGrowE 2560000 2490000 3)],
    -- 256 X.al.x4.x2.x3.x4.ap
    (appendFuns 2560000),
    -- 257 X.al.x4.x2.x3.s4
    [(vsPS4E 2430000 2480000 2550000)],
    -- 258 X.al.x4.x2.x3.pair
    [(vsPPairE 2510000 2530000)],
    -- 259 X.al.x4.x2.x3.comm
    [(vsPCommE 2140000 2150000)],
    -- 260 X.al.x4.x2.x3.zp
    [(vsPZpE 2610000 2420000)],
    -- 261 X.al.x4.x2.x3.zmp
    (mapFuns 2610000 2620000),
    -- 262 X.al.x4.x2.x3.zit
    [(vsPZItemE 2390000 2200000)],
    -- 263 X.al.x4.x2.x3.tl
    (tailFuns 2630000),
    -- 264 X.al.x4.x2.x3.rad
    [(vsPRadE 2650000 2660000 2670000 2690000)],
    -- 265 X.al.x4.x2.x3.gmp
    (mapFuns 2650000 2160000),
    -- 266 X.al.x4.x2.x3.ker
    (vsWKerFuns 2660000),
    -- 267 X.al.x4.x2.x3.rfnd
    (findFuns 2670000 2680000),
    -- 268 X.al.x4.x2.x3.rp
    [(vsPRadPredE 2690000 2300000)],
    -- 269 X.al.x4.x2.x3.word
    (vsPWordFuns 2690000 2140000 2390000),
    -- 270 X.al.x4.x2.s3
    [(vsPS3E 2580000 2590000 2600000 2630000 2640000 2550000 2570000)],
    -- 271 X.al.x4.x2.fnd2
    (findFuns 2710000 2300000),
    -- 272 X.al.x4.x2.ord
    (vsPOrdFuns 2720000 180000),
    -- 273 X.al.x4.s2
    [(vsPS2E 2710000 2720000 2490000 2550000 2500000 2630000 2700000)],
    -- 274 X.al.x4.ctxP
    [(vsPCtxE 2750000 2780000 2790000)],
    -- 275 X.al.x4.flm
    (mapFuns 2750000 2760000),
    -- 276 X.al.x4.fit
    [(vsPFlItemE 2770000)],
    -- 277 X.al.x4.fl
    (vsWFlatFuns 2770000),
    -- 278 X.al.x4.rws
    (vsWRowsFuns 2780000),
    -- 279 X.al.x4.rep
    (replicateFuns 2790000),
    -- 280 X.al.x4.der
    (vsPDerFuns 2800000 2490000 2820000 4),
    -- 281 X.al.x4.dmkg
    [],
    -- 282 X.al.x4.bad
    [(vsPBadE 2830000)],
    -- 283 X.al.x4.fd
    (findFuns 2830000 2300000),
    -- 284 X.phi.gl
    (vsQGLFuns 2840000)
]

/-- The primitives: membership `0`, pointwise stabilizer `1`, minimal blocks `2`, normal closure `3`,
derived subgroup `4`, constructive membership `5`. -/
noncomputable def vsQPrims (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks)
    (hn : NormalClosure) (hd : DerivedSubgroup) (hcm : ConstructiveMembership) : List Prim := [
    (membershipPrim hm),
    (pointwiseStabPrim hps),
    (minimalBlocksPrim hmb),
    (normalClosurePrim hn),
    (derivedSubgroupPrim hd),
    (linMembershipPrim hcm)
]

/-- The whole program, with the extra blocks after ours. -/
noncomputable def vsQProg (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks)
    (hn : NormalClosure) (hd : DerivedSubgroup) (hcm : ConstructiveMembership) (hard q8c : ℕ)
    (extra : List (List Expr)) : Program :=
  spProg 10000 (vsQBlocks hard q8c ++ extra) (vsQPrims hps hm hmb hn hd hcm)

/-- The indices. -/
def vsQIdx (hard q8c : ℕ) : VsQAllX :=
  { top := { top := 0, rng := 10000, fold := 20000, st := 30000, idp := 40000, rep := 50000, tbm := 60000, it := 70000, tr := 80000, red := 90000, jm := 0, tl := 100000, drv := 110000 }, drv := { drv := 110000, ana := 120000, ai := 130000, cmp := 140000, paste := 150000, inv := 160000, mm := 170000, phi := 180000, fd := 190000, pinv := 200000, pmp := 210000, app := 220000, mkg := 230000, red := 240000, jm := 0, pcmp := 250000 }, ana := { ana := 120000, lcp := 260000, orb := 270000, ojp := 1, ojm := 0, abb := 280000, al := 290000, ctx := 300000, flm := 310000, it := 320000, fl := 330000, rws := 340000, rep := 350000, abt := 360000, fo := 370000, no := 380000, fi := 390000, nc := 400000, comp := 410000, loc := 420000, eq := 430000, phi := 180000, fld := { f := 440000, prep := 450000, c0 := 460000, cM := 470000, unit := 480000, appd := 490000, rng := 500000, chA := 510000, chB := 520000, co := 530000, lin := 540000, sotA := 550000, sotB := 560000, bA := 570000, bB := 580000, phi := 180000, jp := 1, jm := 0, fd := 590000, tst := 600000, c0b := 610000, m := 620000, eqN := 630000, tau := 640000, dA := 650000, red := 660000, sc := 670000, sv := 680000, mI := 690000, fI := 700000, mF := 710000, fF := 720000, sv2 := 730000, rp := 740000, mm := 750000, fl := 760000, ch := 770000, cmp := 780000, dB := 790000, mc := 800000, cr := 810000 } }, al := { al := 290000, s4 := 820000, st4 := 830000, hard := hard, q8c := q8c, x2 := { f := 840000, bm := 850000, mpb := 860000, itb := 870000, locb := 880000, phib := 180000, idpb := 890000, algb := 900000, bas := 910000, ann := 920000, nil := 930000, eig := 940000, fix := 950000, spl := 960000, s := { f := 970000, idp := 980000, alg := 990000, spl := 1000000, sp := { f := 1010000, mp := 1020000, it := 1030000, img := 1040000, cat := 1050000, bas := 1060000 }, t := { f := 1070000, jmb := 2, itq := 1080000, st := 1090000, t := { f := 1100000, mpk := 1110000, ki := 1120000, key := 1130000, cat := 1140000, appd := 1150000, mpo := 1160000, fo := 1170000, mpi := 1180000, fi := 1190000, it := 1200000, tl := 1210000, chk := 1220000, ker := 1230000, img := 1240000, key' := 1250000, cat' := 1260000, appd' := 1270000, fnd := 1280000, eq := 1290000 }, b := { f := 1300000, rng := 1310000, mpo := 1320000, fo := 1330000, mpi := 1340000, fi := 1350000, cat := 1360000, flt := 1370000, fn := 1380000 }, w := { f := 1390000, kmp := 1400000, kI := 1410000, cat := 1420000, appd := 1430000, tl := 1440000, so := 1450000, fa := 1460000, smp := 1470000, sI := 1480000, lmp := 1490000, lI := 1500000, rng := 1510000, jp := 1, jm := 0, key' := 1520000, cat' := 1530000, appd' := 1540000, tk := 1550000, cat'' := 1560000, lift := 1570000, bas := 1580000, itm := 1590000, loc := 1600000, phi := 180000, tl₁ := 1610000, chk := 1620000, mp := 1630000, fI := 1640000, tl' := 1650000, chk' := 1660000, ker := 1670000, img := 1680000, key := 1690000, cat₂ := 1700000, appd₂ := 1710000 } } } }, x3 := { f := 1720000, ctx := 1730000, flm := 1740000, it := 1750000, fl := 1760000, rws := 1770000, rep := 1780000, ab := 1790000, fo := 1800000, no := 1810000, fi := 1820000, nc := 1830000, comp := 1840000, loc := 1850000, eq := 1860000, phi := 180000, c := { t := { c := { conj := 1870000, tl := 1880000, ch := 1890000, loc := 1900000, phi := 180000, inv := 1910000, mm := 1920000, fl := 1930000, app := 1940000 }, conjT := 1950000, mp := 1960000, it := 1970000, cat := 1980000 }, q8 := 1990000, y0 := 2000000, mpy := 2010000, ity := 2020000, sb := 2030000, jp := 1, jm := 0, mp2 := 2040000, it2 := 2050000 } }, x4 := { x2 := { x3 := { x4 := { d := { o := { orb := 2060000, itb := 2070000, st := 2080000, fo := 2090000, out := 2100000, fi := 2110000, ins := 2120000, conj := 2130000, comp := 2140000, inv := 2150000, key := 2160000, mp := 2170000, it := 2180000, comm := 2190000, loc := 2200000, fd := 2210000, fd' := 2220000, pk := 2230000, eq := 2240000, eqb := 2250000, phi := 180000 }, dim := 2260000, bas := 2270000, g := 2280000, ins := 2290000, nt := 2300000, inl := 2310000 }, e := { en := 2320000, fo := 2330000, st := 2340000, mpM := 2350000, mid := 2360000, mpI := 2370000, it := 2380000, pow := 2390000, comp := 2400000, cat := 2410000, rng := 2420000 }, desc := 2430000, it := 2440000, st := 2450000, fnd := 2460000, pr := 2470000, fin := 2480000, mkg := 2490000, ab := 2500000, fo := 2510000, no := 2520000, fi := 2530000, nc := 2540000, grow := 2550000, ap := 2560000, ncp := 3 }, s4 := 2570000, pair := 2580000, comm := 2590000, zp := 2600000, zmp := 2610000, zit := 2620000, tl := 2630000, rad := 2640000, gmp := 2650000, ker := 2660000, rfnd := 2670000, rp := 2680000, word := 2690000 }, s3 := 2700000, fnd2 := 2710000, ord := 2720000 }, s2 := 2730000, ctxP := 2740000, flm := 2750000, fit := 2760000, fl := 2770000, rws := 2780000, rep := 2790000, der := 2800000, dmkg := 2810000, bad := 2820000, fd := 2830000, derp := 4 } }, phi := { phi := 180000, j := 5, gl := 2840000 } }

theorem spProg_getD_app {A E : List (List Expr)} {k : ℕ} (hk : k < A.length) :
    (A ++ E).getD k [] = A.getD k [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem spProg_app_funs {B : ℕ} {A E : List (List Expr)} {ps : List Prim} {n : ℕ} {e : Expr}
    (hB : 0 < B) (hk : n / B < A.length) (h : (A.getD (n / B) []).getD (n % B) .nil = e) :
    (spProg B (A ++ E) ps).funs[n]? = some e := by
  have := spProg_funs (B := B) (blks := A ++ E) (ps := ps) (k := n / B) (j := n % B)
    (by rw [List.length_append]; omega) (Nat.mod_lt _ hB)
  rw [Nat.div_add_mod, spProg_getD_app hk, h] at this
  exact this

theorem spProg_app_hasAt {B : ℕ} {A E : List (List Expr)} {ps : List Prim} {n : ℕ} {fs : List Expr}
    (hB : 0 < B) (hk : n / B < A.length) (h : ((A.getD (n / B) []).drop (n % B)).take fs.length = fs)
    (hl : n % B + fs.length ≤ B) : (spProg B (A ++ E) ps).HasAt n fs := by
  intro j hj
  set bl := A.getD (n / B) []
  have hlen : n % B + j < bl.length := by
    have := congrArg List.length h
    simp only [List.length_take, List.length_drop] at this
    omega
  have := spProg_funs (B := B) (blks := A ++ E) (ps := ps) (k := n / B) (j := n % B + j)
    (by rw [List.length_append]; omega) (by omega)
  rw [← Nat.add_assoc, Nat.div_add_mod, spProg_getD_app hk] at this
  rw [this, List.getD_eq_getElem _ _ hlen]
  congr 1
  have e2 : fs[j] = (List.take fs.length (List.drop (n % B) bl))[j]'(by rw [h]; exact hj) := by
    congr 1 <;> simp [h]
  rw [e2, List.getElem_take, List.getElem_drop]

theorem vsQBlocks_length (hard q8c : ℕ) : (vsQBlocks hard q8c).length = 285 := rfl

/-- Close the layout facts of the sparse program. -/
macro "sp_lay" : tactic => `(tactic| repeat' (first
  | ((try dsimp only [vsQIdx]); first
      | exact spProg_app_funs (by norm_num) (by rw [vsQBlocks_length]; norm_num) rfl
      | exact spProg_app_hasAt (by norm_num) (by rw [vsQBlocks_length]; norm_num) rfl (by decide)
      | exact spProg_prim rfl
      | (show (_ : ℕ) = _; rfl))
  | ((fail_if_success show @Eq (Option _) _ _); constructor)))

set_option maxHeartbeats 0 in
/-- **The layout of the whole program.** -/
theorem vsQLay (hps : PointwiseStab) (hm : Membership) (hmb : MinimalBlocks) (hn : NormalClosure)
    (hd : DerivedSubgroup) (hcm : ConstructiveMembership) (hard q8c : ℕ) (extra : List (List Expr)) :
    VsQAllLay (vsQProg hps hm hmb hn hd hcm hard q8c extra) (vsQIdx hard q8c) hps hm hmb hn hd hcm := by
  unfold vsQProg
  sp_lay

end GI.Impl
