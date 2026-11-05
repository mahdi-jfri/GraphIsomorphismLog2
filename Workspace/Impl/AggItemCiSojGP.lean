module

public import Workspace.Impl.AggKerRed
public import Workspace.Impl.AggItemC1G
public import Workspace.Impl.AggItemCiSojWt
public import Workspace.Impl.GenNormPoly

@[expose] public section

/-!
# The physical group of a rectangle query

Map first projections of the recorded graph generators, then use the established
group-value constructor to add the degree and leading identity. The graph's
canonical generator-count bound makes this a canonical physical group value.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {k q : ℕ}

/-- On `[k,graph generators]`, build the physical query group value. -/
def itcsPhysF (mp mk : ℕ) : Expr :=
  .letE (.call mp (mk2 (.nat 0) (arg 1))) (.call mk (mk2 (arg 0) (.var 1)))

/-- Common budget including the group-value constructor's result. -/
def itcsPhysW (M : ℕ) : ℕ := 1000*(M^3+mkGroupK*M^6+10)

/-- Cost of projecting graph generators and building their group value. -/
def itcsPhysC (M : ℕ) : ℕ :=
  100*(itcsPhysW M+1)+M*(300*M^2)+mapK*(M+1)*(2*itcsPhysW M+1)+mkGroupK*M^6

set_option maxHeartbeats 400000 in
/-- The physical group-value program with all table and library premises proved. -/
theorem itcs_phys_prog {Pg : Program} {f mp fb mk : ℕ}
    (hf : Pg.funs[f]? = some (itcsPhysF mp mk))
    (hm : Pg.HasAt mp (mapFuns mp fb)) (hb : Pg.funs[fb]? = some krFstF)
    (hmg : Pg.HasAt mk (mkGroupFuns mk)) (ps : List (Perm (Fin k)×Perm (Fin q))) :
    FunDet Pg f (.list [.nat k,.list (ps.map pairV)]) (encGroup (ps.map Prod.fst))
      (itcsPhysC (pM k q ps)) := by
  let M:=pM k q ps
  let Bw:=itcsPhysW M
  have hM : k+q+ps.length+2=M := rfl
  have h1 : 1≤ M := by omega
  have hp13 : M≤ M^3 := Nat.le_self_pow (by omega) _
  have hp23 : M^2≤ M^3 := Nat.pow_le_pow_right h1 (by omega)
  have budget : 500*M^3+100*(mkGroupK*M^6)+1000≤ Bw := by dsimp only [Bw]; unfold itcsPhysW; omega
  have wps : (Val.list (ps.map pairV)).wt≤50*M^3 := wt_pairList_le ps
  have k2 : (k+1)^2≤ M^3 := (Nat.pow_le_pow_left (by omega : k+1≤ M) 2).trans hp23
  have wr0:=wt_list_encPerms_le (ps.map Prod.fst)
  have wr : (Val.list ((ps.map Prod.fst).map encPerm)).wt≤20*M^3 := by
    have hh:=it_perms_wt (l:=ps.map Prod.fst) (m:=M) (by simp only [List.length_map]; omega)
    have hk2:=Nat.pow_le_pow_left (by omega : k+1≤ M) 2
    calc _ ≤ M*(9*(k+1)^2)+4 := hh
      _ ≤ M*(9*M^2)+4 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 9 hk2)) 4
      _ = 9*M^3+4 := by ring
      _ ≤ 20*M^3 := by have hp:=Nat.one_le_pow 3 M h1; omega
  have kn:=wt_nat_le k
  have win : (Val.list [.nat k,.list (ps.map pairV)]).wt≤ Bw := by
    have hh:=wt_list2_le (.nat k) (.list (ps.map pairV))
    omega
  have wmap : (Val.list [.nat 0,.list (ps.map pairV)]).wt≤ Bw := by
    have hh:=wt_list2_le (.nat 0) (.list (ps.map pairV))
    have hz:=wt_nat_le 0
    omega
  have wmk : (Val.list [.nat k,.list ((ps.map Prod.fst).map encPerm)]).wt≤ Bw := by
    have hh:=wt_list2_le (.nat k) (.list ((ps.map Prod.fst).map encPerm))
    omega
  let Cmp:=M*(300*M^2)+mapK*(M+1)*(2*Bw+1)
  have mapCall : FunDet Pg mp (.list [.nat 0,.list (ps.map pairV)])
      (.list ((ps.map Prod.fst).map encPerm)) Cmp := by
    have hh:=mapList_spec hm ps pairV (fun p=>encPerm p.1) (c:=.nat 0) (B:=300*(k+q+1)^2)
      (fun a _ b _ h=>by rw [pairV_injective h]) (fun p _=>krFst_step hb p)
    have he : ps.map (fun p=>encPerm p.1)=(ps.map Prod.fst).map encPerm := by rw [List.map_map]; rfl
    rw [he] at hh
    refine hh.mono (Nat.add_le_add ?_ ?_)
    · exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left (by omega) 2))
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hmul : (ps.length+2)*(k+1)≤ M^2 := by
    calc _ ≤ M*M := Nat.mul_le_mul (by omega) (by omega)
      _ = M^2 := by ring
  have hmk : mkGroupK*((ps.map Prod.fst).length+2)*(k+1)≤ mkGroupK*M^2 := by
    simp only [List.length_map,Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hmul
  have cg : mkGroupK*(((ps.map Prod.fst).length+2)*(k+1))^3≤ mkGroupK*M^6 := by
    have hh:=Nat.mul_le_mul_left mkGroupK (Nat.pow_le_pow_left hmul 3)
    simpa only [List.length_map,←Nat.pow_mul] using hh
  have groupCall:=(mkGroup_spec hmg (ps.map Prod.fst)).mono cg
  have wg:=itcs_det_weight groupCall
  let inp : Val:=.list [.nat k,.list (ps.map pairV)]
  have get {rest : List Val} {i : ℕ} {v : Val}
      (hi:[Val.nat k,.list (ps.map pairV)][i]?=some v) (hii:i+2≤ Bw) :
      StDC Pg (inp::rest) (arg i) v 3 0 Bw :=
    StDC.arg hi win hii ((st_wt_mem (List.mem_of_getElem? hi)).trans win)
  have mc:=StDC.call (StDC.mk2 (StDC.nat 0 (by omega)) (get (rest:=[]) (i:=1) rfl (by omega)) wmap (by omega)) mapCall (wr.trans (by omega))
  have r1 : StDC Pg [inp,.list ((ps.map Prod.fst).map encPerm)] (.var 1)
      (.list ((ps.map Prod.fst).map encPerm)) 1 0 Bw := StDC.var' rfl (wr.trans (by omega))
  have gc:=StDC.call (StDC.mk2 (get (rest:=[.list ((ps.map Prod.fst).map encPerm)]) (i:=0) rfl (by omega)) r1 wmk (by omega)) groupCall (wg.trans (by omega))
  have body:=StDC.letE mc gc (wg.trans (by omega))
  clear budget wps k2 wr0 wr kn win wmap wmk mapCall hmul hmk cg groupCall wg get mc r1 gc
  exact StDC.funDet hf body (by unfold itcsPhysC; dsimp only [Bw,Cmp,M] at *; omega)

/-- Polynomial round cost under the canonical graph-generator bound. -/
theorem itcs_phys_pbu : PBU fun _ W _=>itcsPhysC (W+(2*W+3)+W^2+2) := by
  simp only [itcsPhysC,itcsPhysW,mkGroupK,mapK]
  norm_poly

end GI.Impl
