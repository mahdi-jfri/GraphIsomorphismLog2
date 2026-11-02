import Workspace.Impl.LinAffineInput
import Workspace.Impl.LinVectorTransport

namespace GI.Impl
open GI.Cited GI.Lang

/-- Homogenization preserves a transporter equation, including unequal source
and target vectors. -/
theorem linAffineTransport_equation (I : VecStabInst)
    (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g)
    (g : gens I.gs) (v w : Fin I.d → ZMod I.p) :
    ((linAffineLayerInst I c hc).φ g).val.mulVec (linExtend v 1) = linExtend w 1 ↔
      (I.φ g).val.mulVec v + c g = w := by
  change (linAffineMatrix (I.φ g).val (c g)).mulVec (linExtend v 1) = linExtend w 1 ↔ _
  rw [linAffineMatrix_mulVec, one_smul]
  constructor
  · intro he
    funext i
    have hh := congrFun he i.castSucc
    simpa only [linExtend_castSucc] using hh
  · intro he
    rw [he]

def linAffineTargetSub (I : VecStabInst)
    (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g)
    (w : Fin I.d → ZMod I.p) : Subgroup (Equiv.Perm (Fin I.n)) :=
  vecStabSub (linVectorTarget (linAffineLayerInst I c hc) (linExtend w 1))

theorem linAffineTargetSub_mem (I : VecStabInst)
    (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g)
    (w : Fin I.d → ZMod I.p) (g : gens I.gs) :
    g.val ∈ linAffineTargetSub I c hc w ↔ (I.φ g).val.mulVec w + c g = w := by
  change g.val ∈ (vecStab (linVectorTarget (linAffineLayerInst I c hc) (linExtend w 1))).map
    (gens I.gs).subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, he⟩
    have hkg : k = g := Subtype.ext he
    subst k
    exact (linAffineTransport_equation I c hc g w w).mp hk
  · intro he
    exact ⟨g, (linAffineTransport_equation I c hc g w w).mpr he, rfl⟩

def linAffineTransportOut (I : VecStabInst)
    (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g)
    (w : Fin I.d → ZMod I.p) (out : Val) : Prop :=
  (out = .list [] ∧ ¬∃ g : gens I.gs, (I.φ g).val.mulVec I.v + c g = w) ∨
    ∃ (g : gens I.gs) (sv : Val), out = .list [encPerm g.val, sv] ∧
      (I.φ g).val.mulVec I.v + c g = w ∧ GensVal I.n sv (linAffineTargetSub I c hc w)

theorem linAffineTransportOut_of_vector (I : VecStabInst)
    (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g)
    (w : Fin I.d → ZMod I.p) {out : Val}
    (ho : linVectorTransportOut (linAffineLayerInst I c hc) (linExtend w 1) out) :
    linAffineTransportOut I c hc w out := by
  rcases ho with ⟨rfl, hno⟩ | ⟨g, sv, he, hg, hgens⟩
  · refine Or.inl ⟨rfl, ?_⟩
    rintro ⟨g, hg⟩
    exact hno ⟨g, (linAffineTransport_equation I c hc g I.v w).mpr hg⟩
  · exact Or.inr ⟨g, sv, he, (linAffineTransport_equation I c hc g I.v w).mp hg, hgens⟩

theorem linAffineVectorExtend_value {p d : ℕ} (hp : p.Prime) (v : Fin d → ZMod p) :
    encVec (linExtend v 1) = .list (((List.finRange d).map fun i => Val.nat (v i).val) ++ [.nat 1]) := by
  have hh := congrArg Val.list (linExtend_value (fun x : ZMod p => Val.nat x.val) v 1)
  simpa only [encVec, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.one_lt] using hh

end GI.Impl
