import Workspace.Impl.GenNormGlue
import Workspace.Impl.LinObjectAffineEval

namespace GI.Impl
open GI.Cited GI.Lang

def linObjectEvalAtom (C : ℕ) : ℕ := 1000 * (C + 2) ^ 2
def linObjectEvalPack (C : ℕ) : ℕ := 100000 * (C + 2) ^ 2

theorem linObjectEvalRead {P : Program} {env : List Val} {C slot : ℕ} {root out : Val}
    (henv : normEnvBound C env) (hs : env[slot]? = some root)
    (path : List ℕ) (hr : normReadVal root path = some out)
    (hl : path.length ≤ 5) (hp : path.sum ≤ 50) (hC : 100 ≤ C) :
    out.wt ≤ C ∧ Det P env (normReadE (.var slot) path) out (linObjectEvalAtom C) := by
  obtain ⟨hw,hd⟩ := normRead_env henv hs path hr hl hp hC
  refine ⟨hw,hd.mono ?_⟩
  unfold linObjectEvalAtom
  nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) (C + 1)]

theorem linObjectEvalLength {P : Program} {env : List Val} {C : ℕ} {e : Expr} {vs : List Val}
    (hw : (Val.list vs).wt ≤ C) (hd : Det P env e (.list vs) (linObjectEvalAtom C)) :
    (Val.nat vs.length).wt ≤ C + 1 ∧
      Det P env (.length e) (.nat vs.length) (2 * linObjectEvalAtom C) := by
  have hl := length_lt_wt_list vs
  have hn := wt_nat_le vs.length
  refine ⟨by omega,(Det.length hd).mono ?_⟩
  unfold linObjectEvalAtom
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  omega

theorem linObjectEvalPack2 {P : Program} {env : List Val} {C : ℕ} {a b : Val} {ea eb : Expr}
    (ha : a.wt ≤ C + 1) (hb : b.wt ≤ C + 1)
    (da : Det P env ea a (2 * linObjectEvalAtom C))
    (db : Det P env eb b (2 * linObjectEvalAtom C)) :
    Det P env (mk2 ea eb) (.list [a,b]) (linObjectEvalPack C) := by
  refine (Det.mk2 da db).mono ?_
  have hw := wt_list2_le a b
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  unfold linObjectEvalPack linObjectEvalAtom
  omega

theorem linObjectEvalPack3 {P : Program} {env : List Val} {C : ℕ} {a b c : Val} {ea eb ec : Expr}
    (ha : a.wt ≤ C + 1) (hb : b.wt ≤ C + 1) (hc : c.wt ≤ C + 1)
    (da : Det P env ea a (2 * linObjectEvalAtom C))
    (db : Det P env eb b (2 * linObjectEvalAtom C))
    (dc : Det P env ec c (2 * linObjectEvalAtom C)) :
    Det P env (mk3 ea eb ec) (.list [a,b,c]) (linObjectEvalPack C) := by
  refine (Det.mk3 da db dc).mono ?_
  have hw := wt_list3_le a b c
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  unfold linObjectEvalPack linObjectEvalAtom
  omega

theorem linObjectEvalPack4 {P : Program} {env : List Val} {C : ℕ} {a b c d : Val} {ea eb ec ed : Expr}
    (ha : a.wt ≤ C + 1) (hb : b.wt ≤ C + 1) (hc : c.wt ≤ C + 1) (hd : d.wt ≤ C + 1)
    (da : Det P env ea a (2 * linObjectEvalAtom C))
    (db : Det P env eb b (2 * linObjectEvalAtom C))
    (dc : Det P env ec c (2 * linObjectEvalAtom C))
    (dd : Det P env ed d (2 * linObjectEvalAtom C)) :
    Det P env (mk4 ea eb ec ed) (.list [a,b,c,d]) (linObjectEvalPack C) := by
  refine (Det.mk4 da db dc dd).mono ?_
  have hw := wt_list4_le a b c d
  have hp : C + 2 ≤ (C + 2) ^ 2 := Nat.le_self_pow (by decide) _
  unfold linObjectEvalPack linObjectEvalAtom
  omega

end GI.Impl
