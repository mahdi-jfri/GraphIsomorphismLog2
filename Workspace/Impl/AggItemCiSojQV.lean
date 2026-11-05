module

public import Workspace.Impl.AggItemCiSojQuery
public import Workspace.Impl.AggItemCiSojSG

@[expose] public section

/-!
# Assembling the canonical inherited query value

The encoder keeps the parent hierarchy and phase size, clears the row record,
turns floor mode off, and writes `h = 2`, exactly as `State.queryChild` does.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

/-- A list constructor for the ten fields of a canonical state. -/
def itcsMk10 (a b c d e f g h i j : Expr) : Expr :=
  .snoc (.snoc (.snoc (.snoc (.snoc (itcsMk5 a b c d e) f) g) h) i) j

/-- Assemble the ten fields, with every prefix bounded by the final list. -/
theorem itcs_mk10 {Pg : Program} {env : List Val} {Bw : ℕ}
    {a b c d e f g h i j : Expr} {va vb vc vd ve vf vg vh vi vj : Val}
    {na nb nc nd ne nf ng nh ni nj Ea Eb Ec Ed Ee Ef Eg Eh Ei Ej : ℕ}
    (ha : StDC Pg env a va na Ea Bw) (hb : StDC Pg env b vb nb Eb Bw)
    (hc : StDC Pg env c vc nc Ec Bw) (hd : StDC Pg env d vd nd Ed Bw)
    (he : StDC Pg env e ve ne Ee Bw) (hf : StDC Pg env f vf nf Ef Bw)
    (hg : StDC Pg env g vg ng Eg Bw) (hh : StDC Pg env h vh nh Eh Bw)
    (hi : StDC Pg env i vi ni Ei Bw) (hj : StDC Pg env j vj nj Ej Bw)
    (hw : (Val.list [va, vb, vc, vd, ve, vf, vg, vh, vi, vj]).wt ≤ Bw) (h4 : 4 ≤ Bw) :
    StDC Pg env (itcsMk10 a b c d e f g h i j)
      (.list [va, vb, vc, vd, ve, vf, vg, vh, vi, vj])
      (na + nb + nc + nd + ne + nf + ng + nh + ni + nj + 11)
      (Ea + Eb + Ec + Ed + Ee + Ef + Eg + Eh + Ei + Ej) Bw := by
  have p5 : (Val.list [va, vb, vc, vd, ve]).wt ≤ Bw := (wt_list_mono (by exact ⟨[vf, vg, vh, vi, vj], rfl⟩)).trans hw
  have p6 : (Val.list [va, vb, vc, vd, ve, vf]).wt ≤ Bw := (wt_list_mono (by exact ⟨[vg, vh, vi, vj], rfl⟩)).trans hw
  have p7 : (Val.list [va, vb, vc, vd, ve, vf, vg]).wt ≤ Bw := (wt_list_mono (by exact ⟨[vh, vi, vj], rfl⟩)).trans hw
  have p8 : (Val.list [va, vb, vc, vd, ve, vf, vg, vh]).wt ≤ Bw := (wt_list_mono (by exact ⟨[vi, vj], rfl⟩)).trans hw
  have p9 : (Val.list [va, vb, vc, vd, ve, vf, vg, vh, vi]).wt ≤ Bw := (wt_list_mono (by exact ⟨[vj], rfl⟩)).trans hw
  exact (StDC.snoc (StDC.snoc (StDC.snoc (StDC.snoc (StDC.snoc
    (itcs_mk5 ha hb hc hd he p5 h4) hf p6) hg p7) hh p8) hi p9) hj hw).mono (by omega) (by omega)

/-- On `[k, group, domain, source colors, target colors, hierarchy, N]`, encode
an inherited query. -/
def itcsWinF : Expr :=
  itcsMk10 (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) (arg 5) .nil (.nat 0) (.nat 2) (arg 6)

/-- The concrete query-state constructor. -/
theorem itcs_win_spec {Pg : Program} {f k N Bw : ℕ} {gv dv xv yv hv : Val}
    (hf : Pg.funs[f]? = some itcsWinF)
    (hin : (Val.list [.nat k, gv, dv, xv, yv, hv, .nat N]).wt ≤ Bw)
    (hout : (winVal' k gv dv xv yv hv N).wt ≤ Bw) (h10 : 10 ≤ Bw) :
    FunDet Pg f (.list [.nat k, gv, dv, xv, yv, hv, .nat N])
      (winVal' k gv dv xv yv hv N) (50 * (Bw + 1)) := by
  have get {i : ℕ} {v : Val}
      (hi : [Val.nat k, gv, dv, xv, yv, hv, .nat N][i]? = some v) (hii : i + 2 ≤ Bw) :
      StDC Pg [.list [.nat k, gv, dv, xv, yv, hv, .nat N]] (arg i) v 3 0 Bw :=
    StDC.arg hi hin hii ((st_wt_mem (List.mem_of_getElem? hi)).trans hin)
  have body := itcs_mk10 (get (i := 0) rfl (by omega)) (get (i := 1) rfl (by omega))
    (get (i := 2) rfl (by omega)) (get (i := 3) rfl (by omega))
    (get (i := 4) rfl (by omega)) (get (i := 5) rfl (by omega))
    (StDC.nil (by omega)) (StDC.nat 0 (by omega)) (StDC.nat 2 (by omega))
    (get (i := 6) rfl (by omega)) hout (by omega)
  exact StDC.funDet hf body (by omega)

end GI.Impl
