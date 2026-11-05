module

public import Workspace.Impl.AggItemCiSojAskFrame
public import Workspace.Impl.AggItemCiSojStartScalar

@[expose] public section

/-! # Frames from the actual source and aligned target tables -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Store the raw edge table, fixed alignment, and the certified graph generators
in the same semantic frame used by the two-query step proof. -/
noncomputable def itcsFrameOf (hc : RectConds P₀ S L W R) (rep : RectRep P₀ S L W R)
    (X Y : PairCfg L.q) (v : ℕ) (a : alternatingGroup (Fin L.q))
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (hlen : hs.length ≤ k^2) (hier : Val) (hhier : HierValC e hier S.hier) : itcsQFrame e S L :=
  ⟨W,R,hc,rep,itcsMatrix X v,(fun w r => decide (Y.col (a.val w.val) (a.val r.val)=v)),
    a,hs,hhs,hlen,hier,hhier⟩

open Classical in
/-- All actual pullback and state-constructor calls yield the frame's exact
query value. The hypotheses on `n` are only numeric cost substitutions. Palette
bounds, the raw edge bound, and the three parent fields are proved separately
at the caller. -/
theorem itcs_colors_frame {Pg : Program} {f cmp rng pull cb bit state B n : ℕ}
    (hf : Pg.funs[f]?=some (itcsColorsStateF cmp rng pull state))
    (hcmp : Pg.HasAt cmp (composeFuns cmp)) (hr : Pg.HasAt rng (rangeFuns rng))
    (hm : Pg.HasAt pull (mapFuns pull cb)) (hb : Pg.funs[cb]?=some (itcsPullB bit))
    (hbit : Pg.funs[bit]?=some itcsPullF) (hst : Pg.funs[state]?=some itcsStateF)
    (hc : RectConds P₀ S L W R) (rep : RectRep P₀ S L W R)
    (X Y : PairCfg L.q) (x₀ y₀ : Fin L.q)
    (hX : itCfColsLe (.pair X x₀) B) (hY : itCfColsLe (.pair Y y₀) B)
    (v : ℕ) (hv : v ≤ B) (a : alternatingGroup (Fin L.q))
    (hs : List (Perm (Fin k) × Perm (Fin L.q))) (hhs : PairGens e L rep.H hs)
    (hlen : hs.length ≤ k^2) (sv : List Val) (hier : Val) (hhier : HierValC e hier S.hier)
    (hsvk : sv[0]?=some (.nat k)) (hsvh : sv[5]?=some hier) (hsvN : sv[9]?=some (.nat S.N))
    (hcostCmp : permK*(L.q+1)^3 ≤ n) (hcostRng : 7000*(L.q+1)^3 ≤ n)
    (hcostPull : itcsPullC k L.q B ≤ n)
    (hinput : ∀ t : permitted W R,
      (Val.list [.list sv,encGroup (hs.map Prod.fst),
        encFun (fun i => if e.symm i∈rep.Δ then 1 else 0),rcColVal X,rcColVal Y,.nat v,.nat L.q,
        encFun (fun i => rcCellCode (rep.cell (e.symm i))),encPerm a.val,encPerm t.val.val]).wt ≤ n)
    (hstate : ∀ t : permitted W R,
      itcsStateC (.list sv) (encGroup (hs.map Prod.fst))
        (encFun (fun i => if e.symm i∈rep.Δ then 1 else 0))
        (encFun (fun i => itcsQCode (rep.colors (itcsMatrix X v) (e.symm i))))
        (encFun (fun i => itcsQCode (rep.colors
          (RectRep.twistMat t (fun w r => decide (Y.col (a.val w.val) (a.val r.val)=v))) (e.symm i)))) ≤ n) :
    let F := itcsFrameOf hc rep X Y v a hs hhs hlen hier hhier
    ∀ t : permitted W R,
      FunDet Pg f (.list [.list sv,encGroup (hs.map Prod.fst),
        encFun (fun i => if e.symm i∈rep.Δ then 1 else 0),rcColVal X,rcColVal Y,.nat v,.nat L.q,
        encFun (fun i => rcCellCode (rep.cell (e.symm i))),encPerm a.val,encPerm t.val.val])
        (F.query t) (10^9*(n+100)) := by
  dsimp only
  intro t
  exact (itcs_colors_state_query hf hcmp hr hm hb hbit hst e rep X Y x₀ y₀ hX hY
    v hv a.val t hs sv hier hsvk hsvh hsvN).mono
      (itcs_colors_cost_scalar (hinput t) hcostCmp hcostRng hcostPull hcostPull (hstate t))

end GI.Impl
