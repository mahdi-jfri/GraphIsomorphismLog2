module

public import Workspace.Impl.LinObjectEvalBound

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linObjectEvalPack5 {P : Program} {env : List Val} {C : ℕ}
    {a b c d e : Val} {ea eb ec ed ee : Expr}
    (ha : a.wt ≤ C+1) (hb : b.wt ≤ C+1) (hc : c.wt ≤ C+1) (hd : d.wt ≤ C+1) (he : e.wt ≤ C+1)
    (da : Det P env ea a (2*linObjectEvalAtom C)) (db : Det P env eb b (2*linObjectEvalAtom C))
    (dc : Det P env ec c (2*linObjectEvalAtom C)) (dd : Det P env ed d (2*linObjectEvalAtom C))
    (de : Det P env ee e (2*linObjectEvalAtom C)) :
    Det P env (.snoc (mk4 ea eb ec ed) ee) (.list [a,b,c,d,e]) (2*linObjectEvalPack C) := by
  have dp := linObjectEvalPack4 ha hb hc hd da db dc dd
  have hh := wt_list_le [a,b,c,d,e]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hh
  refine (Det.snoc dp de).mono ?_
  have hp : C+2 ≤ (C+2)^2 := Nat.le_self_pow (by decide) _
  simp only [List.cons_append,List.nil_append]
  unfold linObjectEvalPack linObjectEvalAtom
  omega

end GI.Impl
