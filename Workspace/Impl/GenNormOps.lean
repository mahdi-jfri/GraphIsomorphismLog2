import Workspace.Impl.GenNormAlt
import Workspace.Impl.GenNormOrbit
import Workspace.Impl.GenNormCosets
import Workspace.Impl.GenNormGlue
import Workspace.Impl.GenNormLabelBuild
import Workspace.Impl.GenNormParentList

/-!
# The installed normalization modules

The fields specify program indices and the code installed at them. They add no algorithmic
hypothesis: every stage specification is proved from these code equalities and the cited
primitive hypotheses.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Preimage PointwiseStab Membership)

/-- The installed finite-loop program for attaching point images to position generators. -/
structure normPairAt (Pg : Program) where
  map : ℕ
  parent : ℕ
  act : ℕ
  gather : ℕ
  recover : ℕ
  point : ℕ
  filter : ℕ
  cand : ℕ
  all : ℕ
  test : ℕ
  mem : ℕ
  hmap : Pg.HasAt map (mapFuns map parent)
  hparent : Pg.funs[parent]? = some (normParentF act recover)
  hact : Pg.funs[act]? = some (actF gather)
  hgather : Pg.HasAt gather (gatherFuns gather)
  hrecover : Pg.HasAt recover (mapFuns recover point)
  hpoint : Pg.funs[point]? = some (normPointF filter)
  hfilter : Pg.HasAt filter (filterFuns filter cand)
  hcand : Pg.funs[cand]? = some (normCandidateF all)
  hall : Pg.HasAt all (allFuns all test)
  htest : Pg.funs[test]? = some (normIncTestF mem)
  hmem : Pg.HasAt mem (normMemFuns mem)

/-- The complete collection of code used by normalization preparation. -/
structure normOps (Pg : Program) (hp : Preimage) (hst : PointwiseStab) (hm : Membership) where
  pairs : normPairAt Pg
  cls : ℕ
  range : ℕ
  alt : ℕ
  replicate : ℕ
  cycles : ℕ
  pre : ℕ
  jpre : ℕ
  raw : ℕ
  kr : ℕ
  jst : ℕ
  cosets : ℕ
  outsideFilter : ℕ
  outside : ℕ
  jm : ℕ
  selection : ℕ
  count : ℕ
  blockmap : ℕ
  cell : ℕ
  bits : ℕ
  bit : ℕ
  mem : ℕ
  orbit : ℕ
  lo : ℕ
  max : ℕ
  labels : ℕ
  hcls : Pg.HasAt cls (clsFuns cls)
  hrange : Pg.HasAt range (rangeFuns range)
  halt : Pg.funs[alt]? = some (normAltF replicate cycles)
  hreplicate : Pg.HasAt replicate (replicateFuns replicate)
  hcycles : Pg.HasAt cycles (cycGensFuns cycles)
  hpre : Pg.HasAt pre (graphPreFuns pre jpre)
  hjpre : Pg.prims[jpre]? = some (preimagePrim hp)
  hraw : Pg.funs[raw]? = some (normRawReduceF kr jst)
  hkr : Pg.HasAt kr (krFuns kr jst)
  hjst : Pg.prims[jst]? = some (pointwiseStabPrim hst)
  hcosets : Pg.funs[cosets]? = some (normCosetsF outsideFilter)
  houtsideFilter : Pg.HasAt outsideFilter (filterFuns outsideFilter outside)
  houtside : Pg.funs[outside]? = some (normOutsideF jm)
  hjm : Pg.prims[jm]? = some (membershipPrim hm)
  hselection : Pg.HasAt selection (hsplitFuns selection cls)
  hcount : Pg.HasAt count (countFuns count)
  hblockmap : Pg.HasAt blockmap (mapFuns blockmap cell)
  hcell : Pg.funs[cell]? = some (normBlockCellF bits)
  hbits : Pg.HasAt bits (mapFuns bits bit)
  hbit : Pg.funs[bit]? = some (normMemFlipF mem)
  hmem : Pg.HasAt mem (normMemFuns mem)
  horbit : Pg.funs[orbit]? = some (normOrbitF lo max)
  hlo : Pg.HasAt lo (loFuns lo)
  hmax : Pg.HasAt max (maxFuns max)
  hlabels : Pg.funs[labels]? = some normLabelBuildF

/-- A field of the input `[state,representatives,hierarchy,m,k,E]`. -/
def normInput (i : ℕ) : Expr := normReadE (.var 0) [i]

/-- A field of the canonical state in that input. -/
def normState (i : ℕ) : Expr := normReadE (.var 0) [0, i]

/-- A field of a stage result. -/
def normField (slot i : ℕ) : Expr := normReadE (.var slot) [i]

/-- The complement flag for the Cameron subsets. -/
def normFlip : Expr := .arith .lt (normInput 3) (.arith .mul (.nat 2) (normInput 4))

/-- The context of the parent-pair map, from the numbering and two range calls. -/
def normPairContext : Expr := Expr.mkList
  [normField 1 0, normField 1 1, normInput 5, .var 2, .var 3]

/-- The raw parent generators, including the stored identity, in a canonical group value. -/
def normParentGenerators : Expr := normReadE (.var 0) [0, 1, 1]

/-- The stored identity permutation of the position action. -/
def normPositionIds : Expr := normReadE (.var 0) [0, 1, 1, 0]

/-- Prepare the canonical normalized group, labels, mode and cosets for the child loop.
The comments give the slot of each `let` result. -/
def normPrepF {Pg : Program} {hp : Preimage} {hst : PointwiseStab} {hm : Membership}
    (o : normOps Pg hp hst hm) : Expr :=
  .letE (.call o.cls (mk2 (normInput 1) (normState 2))) -- 1: numbering
  (.letE (.call o.range (.length (normField 1 1))) -- 2: block identities
  (.letE (.call o.range (normInput 3)) -- 3: point identities
  (.letE (.call o.pairs.map (mk2 normPairContext normParentGenerators)) -- 4: parent graph
  (.letE (.call o.alt (normInput 3)) -- 5: alternating generators
  (.letE (.call o.pre (Expr.mkList [mk2 (normState 0) (normInput 3), .var 4, .var 5])) -- 6
  (.letE (.call o.raw (mk2 (normState 0) (.var 6))) -- 7: [canonical group,raw generators]
  (.letE (.call o.pairs.map (mk2 normPairContext (normField 7 1))) -- 8: reduced graph pairs
  (.letE (.call o.cosets (mk2 (mk2 (normField 7 0) normPositionIds) normParentGenerators)) -- 9
  (.letE (.call o.selection (mk2 (normState 2) (normInput 2))) -- 10: selected interval
  (.letE (.call o.count (mk2 (.nat 0) (normField 1 0))) -- 11: fiber size
  (.letE (.call o.blockmap (mk2 (Expr.mkList
    [normInput 5, normField 1 0, normState 2, .var 3, normFlip]) normPositionIds)) -- 12
  (.letE (.call o.labels (Expr.mkList
    [normInput 3, normInput 4, .var 8, .var 10, .var 11, .var 12])) -- 13
  (.letE (.call o.orbit (mk2 (normField 7 0) (normState 2))) -- 14: transitivity
  (mk2 (Expr.mkList [normInput 0, normField 7 0, normInput 2, .var 13, .var 14])
    (.var 9)))))))))))))))

end GI.Impl
