import Workspace.Impl.AggItemCiSojWt
import Workspace.Impl.AggItemC1G
import Workspace.Impl.GenNormPoly

/-!
# Constructing the full item generator list

Invert the first projected transporter, form its differences with all projected
representatives, and append the projected source generators and the even
pointwise-fixing generators. This is the explicit list in `itcsLeftGens`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- On `[representatives, source generators, pointwise-fixing generators]`, build
the full item generators. The representative list is nonempty. -/
def itcsGroupBuildF (inv mp app : ℕ) : Expr :=
  .letE (.call inv (.get (arg 0) (.nat 0)))
    (.letE (.call mp (mk2 (.var 1) (arg 0)))
      (.letE (.call app (mk2 (.var 2) (arg 1)))
        (.call app (mk2 (.var 3) (arg 2)))))

/-- A common bound for the lists of permutations in the group constructor. -/
theorem itcs_perms_poly {M : ℕ} (ls : List (Perm (Fin q))) (hq : q+1≤M)
    (hl : ls.length≤M) (h1 : 1≤M) : (.list (ls.map encPerm) : Val).wt ≤ 20*M^3 := by
  have h := it_perms_wt hl
  have hp := Nat.pow_le_pow_left hq 2
  have hM := Nat.one_le_pow 3 M h1
  calc _ ≤ M * (9*(q+1)^2)+4 := h
    _ ≤ M * (9*M^2)+4 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 9 hp)) 4
    _ = 9*M^3+4 := by ring
    _ ≤ 20*M^3 := by omega

/-- Cost of the full generator-list constructor. -/
def itcsGroupBuildC (M : ℕ) : ℕ :=
  100*(1000*M^3+1) + invK*M^4 + M*(permK*M^3) + mapK*(M+1)*(2000*M^3+1) +
    2*(loopModK*(M+1)*(2000*M^3+M+1))

set_option maxHeartbeats 500000 in
/-- All inverse, map, composition, append, and weight preconditions of the group
constructor are proved here. -/
theorem itcs_group_build_prog {Pg : Program} {f inv mp cmp app : ℕ}
    (hf : Pg.funs[f]? = some (itcsGroupBuildF inv mp app))
    (hi : Pg.HasAt inv (invFuns inv)) (hm : Pg.HasAt mp (mapFuns mp cmp))
    (hc : Pg.HasAt cmp (composeFuns cmp)) (ha : Pg.HasAt app (appendFuns app))
    (rs gs fs : List (Perm (Fin q))) (r₀ : Perm (Fin q)) (hr : rs[0]? = some r₀) :
    FunDet Pg f (.list [.list (rs.map encPerm),.list (gs.map encPerm),.list (fs.map encPerm)])
      (.list (((rs.map (r₀⁻¹ * ·) ++ gs) ++ fs).map encPerm))
      (itcsGroupBuildC (q+rs.length+gs.length+fs.length+2)) := by
  let M := q+rs.length+gs.length+fs.length+2
  let Bw := 1000*M^3
  let ds := rs.map (r₀⁻¹ * ·)
  have hM : q+rs.length+gs.length+fs.length+2 = M := rfl
  have h1 : 1≤M := by omega
  have hp1 : 1≤M^3 := Nat.one_le_pow 3 M h1
  have hq : q+1≤M := by omega
  have pw2 : (q+1)^2≤M^3 :=
    (Nat.pow_le_pow_left hq 2).trans (Nat.pow_le_pow_right h1 (by omega))
  have pw3 : (q+1)^3≤M^3 := Nat.pow_le_pow_left hq 3
  have pw4 : (q+1)^4≤M^4 := Nat.pow_le_pow_left hq 4
  have wr := itcs_perms_poly rs hq (by omega) h1
  have wg := itcs_perms_poly gs hq (by omega) h1
  have wf := itcs_perms_poly fs hq (by omega) h1
  have wd : (Val.list (ds.map encPerm)).wt≤20*M^3 := itcs_perms_poly ds hq (by simp only [ds,List.length_map]; omega) h1
  have wdg : (Val.list ((ds++gs).map encPerm)).wt≤20*M^3 :=
    itcs_perms_poly (ds++gs) hq (by simp only [ds,List.length_append,List.length_map]; omega) h1
  have wout : (Val.list (((ds++gs)++fs).map encPerm)).wt≤20*M^3 :=
    itcs_perms_poly ((ds++gs)++fs) hq (by simp only [ds,List.length_append,List.length_map]; omega) h1
  have winv := (wt_encPerm_le r₀⁻¹).trans (Nat.mul_le_mul_left 4 pw2)
  have wr₀ := (wt_encPerm_le r₀).trans (Nat.mul_le_mul_left 4 pw2)
  let rv : Val := .list (rs.map encPerm)
  let gv : Val := .list (gs.map encPerm)
  let fv : Val := .list (fs.map encPerm)
  let dv : Val := .list (ds.map encPerm)
  let av : Val := .list ((ds++gs).map encPerm)
  let out : Val := .list (((ds++gs)++fs).map encPerm)
  let inp : Val := .list [rv,gv,fv]
  have wrv : rv.wt ≤ 20*M^3 := wr
  have wgv : gv.wt ≤ 20*M^3 := wg
  have wfv : fv.wt ≤ 20*M^3 := wf
  have wdv : dv.wt ≤ 20*M^3 := wd
  have wav : av.wt ≤ 20*M^3 := wdg
  have wov : out.wt ≤ 20*M^3 := wout
  have wi : inp.wt≤Bw := by have h:=wt_list3_le rv gv fv; dsimp only [inp,rv,gv,fv] at h ⊢; dsimp only [Bw]; omega
  have wmi : (Val.list [encPerm r₀⁻¹,rv]).wt≤Bw := by have h:=wt_list2_le (encPerm r₀⁻¹) rv; dsimp only [rv] at h ⊢; dsimp only [Bw]; omega
  have wa1 : (Val.list [dv,gv]).wt≤Bw := by have h:=wt_list2_le dv gv; dsimp only [dv,gv] at h ⊢; dsimp only [Bw]; omega
  have wa2 : (Val.list [av,fv]).wt≤Bw := by have h:=wt_list2_le av fv; dsimp only [av,fv] at h ⊢; dsimp only [Bw]; omega
  let Cmp := M*(permK*M^3)+mapK*(M+1)*(2000*M^3+1)
  have hmap : FunDet Pg mp (.list [encPerm r₀⁻¹,rv]) dv Cmp := by
    have hh := mapList_spec hm rs encPerm (fun r=>encPerm (r₀⁻¹*r)) (c:=encPerm r₀⁻¹)
      (B:=permK*(q+1)^3) (fun a _ b _ h=>by rw [encPerm_injective h])
      (fun r _=>compose_spec hc r₀⁻¹ r)
    have hemap : rs.map (fun r=>encPerm (r₀⁻¹*r)) = ds.map encPerm := by
      simp only [ds,List.map_map,Function.comp_def]
    rw [hemap] at hh
    refine hh.mono (Nat.add_le_add ?_ ?_)
    · exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ pw3)
    · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by dsimp only [Bw,rv] at wmi; omega)
  let Cap := loopModK*(M+1)*(2000*M^3+M+1)
  have app1 : FunDet Pg app (.list [dv,gv]) av Cap := by
    refine FunAll.mono (append_spec ha (ds.map encPerm) (gs.map encPerm)) fun w cost ⟨hw,hcost⟩=> ?_
    have he : w=av := by simpa only [av,List.map_append] using hw
    refine ⟨he, ?_⟩
    rw [he] at hcost
    simp only [List.length_map] at hcost
    have hb := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (by omega : gs.length+1≤M+1))
      (by dsimp only [Bw] at wa1; omega : (Val.list [dv,gv]).wt+gs.length+av.wt+1≤2000*M^3+M+1)
    exact hcost.trans hb
  have app2 : FunDet Pg app (.list [av,fv]) out Cap := by
    refine FunAll.mono (append_spec ha ((ds++gs).map encPerm) (fs.map encPerm)) fun w cost ⟨hw,hcost⟩=> ?_
    have he : w=out := by simpa only [out,List.map_append] using hw
    refine ⟨he, ?_⟩
    rw [he] at hcost
    simp only [List.length_map] at hcost
    have hb := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (by omega : fs.length+1≤M+1))
      (by dsimp only [Bw] at wa2; omega : (Val.list [av,fv]).wt+fs.length+out.wt+1≤2000*M^3+M+1)
    exact hcost.trans hb
  have get {rest : List Val} {i : ℕ} {v : Val} (hh : [rv,gv,fv][i]?=some v) (hii:i+2≤Bw) :
      StDC Pg (inp::rest) (arg i) v 3 0 Bw :=
    StDC.arg hh wi hii ((st_wt_mem (List.mem_of_getElem? hh)).trans wi)
  have rhead := StDC.get (get (rest:=[]) (i:=0) rfl (by dsimp [Bw]; omega))
    (StDC.nat 0 (by dsimp [Bw]; omega)) (by simp only [rv,List.getElem?_map,hr,Option.map_some]) (wr₀.trans (by dsimp [Bw]; omega))
  have ic := StDC.call rhead (inv_spec hi r₀) (winv.trans (by dsimp [Bw]; omega))
  have i1 : StDC Pg [inp,encPerm r₀⁻¹] (.var 1) (encPerm r₀⁻¹) 1 0 Bw := StDC.var' rfl (winv.trans (by dsimp [Bw]; omega))
  have mc := StDC.call (StDC.mk2 i1 (get (rest:=[encPerm r₀⁻¹]) (i:=0) rfl (by dsimp [Bw]; omega)) wmi (by dsimp [Bw]; omega)) hmap (wd.trans (by dsimp [Bw]; omega))
  have d2 : StDC Pg [inp,encPerm r₀⁻¹,dv] (.var 2) dv 1 0 Bw := StDC.var' rfl (wd.trans (by dsimp [Bw]; omega))
  have ac1 := StDC.call (StDC.mk2 d2 (get (rest:=[encPerm r₀⁻¹,dv]) (i:=1) rfl (by dsimp [Bw]; omega)) wa1 (by dsimp [Bw]; omega)) app1 (wdg.trans (by dsimp [Bw]; omega))
  have a3 : StDC Pg [inp,encPerm r₀⁻¹,dv,av] (.var 3) av 1 0 Bw := StDC.var' rfl (wdg.trans (by dsimp [Bw]; omega))
  have ac2 := StDC.call (StDC.mk2 a3 (get (rest:=[encPerm r₀⁻¹,dv,av]) (i:=2) rfl (by dsimp [Bw]; omega)) wa2 (by dsimp [Bw]; omega)) app2 (wout.trans (by dsimp [Bw]; omega))
  have body := StDC.letE ic (StDC.letE mc (StDC.letE ac1 ac2 (wout.trans (by dsimp [Bw]; omega)))
    (wout.trans (by dsimp [Bw]; omega))) (wout.trans (by dsimp [Bw]; omega))
  have hic := Nat.mul_le_mul_left invK pw4
  clear wrv wgv wfv wdv wav wov wr wg wf wd wdg wout winv wr₀ wi wmi wa1 wa2 hmap app1 app2 get rhead ic i1 mc d2 ac1 a3 ac2
  exact StDC.funDet hf body (by unfold itcsGroupBuildC; dsimp only [Bw,Cmp,Cap,M] at *; omega)

/-- Polynomial round bound for the group constructor. -/
theorem itcs_group_build_pbu : PBU fun _ W _ => itcsGroupBuildC (3*(2*W+3)+W^2+10) := by
  simp only [itcsGroupBuildC,invK,permK,mapK,loopModK]
  norm_poly

end GI.Impl
