import Workspace.Impl.AggItemCiSojRes
import Workspace.Impl.AggItemCiSojColorsQuery
import Workspace.Impl.AggItemCiSojPhysicalExact
import Workspace.Impl.AggItemCiSojAP
import Workspace.Impl.AggItemCiSojGC
import Workspace.Impl.AggItemCiSojFP
import Workspace.Impl.AggItemCiSojSD
import Workspace.Impl.AggItemCiSojMK
import Workspace.Impl.AggItemCiSojQueue

/-! # Preparing the first rectangle and asking its inherited queries -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- The rectangle stage receives `[original item input,fiber,balanced X,cert]`.
Check target side sizes before alignment and representation construction. -/
def itcsRectPrepF (rng bal sides guard align fix markW markR rep ask : ℕ) : Expr :=
  let orig := arg 0
  let st := Expr.get (.get orig (.nat 0)) (.nat 0)
  let sv := Expr.get st (.nat 0)
  let q := Expr.get (.get st (.nat 1)) (.nat 1)
  let ps := Expr.get st (.nat 2)
  let xc := Expr.get (.get orig (.nat 2)) (.nat 1)
  let yc := Expr.get (.get orig (.nat 3)) (.nat 1)
  let cv := arg 3
  let vL := Expr.get cv (.nat 0)
  let vR := Expr.get cv (.nat 1)
  let vE := Expr.get cv (.nat 2)
  let afterRep := Expr.call ask (itcsMk10 sv q xc yc vE (.var 5) (.var 6) (.var 9) (.var 1) (.var 3))
  let pass := Expr.letE (.call align (mk2 (.var 3) (.var 4)))
    (.letE (.call fix (.var 3))
      (.letE (.call markW (mk2 (.var 3) (.var 1)))
        (.letE (.call markR (mk2 (.var 3) (.var 1)))
          (.letE (.call rep (itcsMk5 sv q ps (.var 7) (.var 8))) afterRep))))
  .letE (.call rng q)
    (.letE (.call bal (mk2 yc (.var 1)))
      (.letE (.call sides (mk2 (mk3 (arg 2) vL vR) (.var 1)))
        (.letE (.call sides (mk2 (mk3 (.var 2) vL vR) (.var 1)))
          (.ite (.call guard (mk2 (.var 3) (.var 4))) pass (itcsResE .nil)))))

/-- The exact item-level request encoding for `Continue`. -/
def itcsAskV (query payload pending : Val) : Val :=
  .list [.nat 1,.nat 1,query,.list [payload,pending,.list []]]

/-- The request expression after constructing the first and optional second
physical query states. -/
def itcsAskE (payload pending : Expr) : Expr :=
  mk4 (.nat 1) (.nat 1) (.var 2) (mk3 payload pending .nil)

/-- One physical query from the stored input and computed physical data. -/
def itcsAskQuery (colors : ℕ) (t : Expr) : Expr :=
  .call colors (itcsMk10 (arg 0) (.get (.var 1) (.nat 0)) (.get (.var 1) (.nat 1))
    (.get (arg 2) (.nat 0)) (.get (arg 3) (.nat 0)) (arg 4) (arg 1)
    (.get (arg 7) (.nat 1)) (arg 5) t)

/-- The fixed payload after physical-data construction. -/
def itcsAskPayload (ts : Expr) : Expr :=
  itcsMk5 (arg 1) (arg 5) (arg 6) (.get (.var 1) (.nat 2)) ts

/-- The optional query branch, after storing the first query in slot 2. -/
def itcsAskTail (colors : ℕ) : Expr :=
  let tws := Expr.get (arg 7) (.nat 2)
  let twist := Expr.get tws (.nat 0)
  .ite (.length tws)
    (.letE (itcsAskQuery colors twist)
      (itcsAskE (itcsAskPayload (mk2 (arg 8) twist)) (.snoc .nil (.var 3))))
    (itcsAskE (itcsAskPayload (.snoc .nil (arg 8))) .nil)

/-- Input: `[parent,q,X-input,Y-input,edge,alignment,fix,rep,identity,side X]`.
The first query is untwisted. The optional second query uses the recorded twist,
even when it is identity. Store the query occurrences in this same order. -/
def itcsAskF (data colors : ℕ) : Expr :=
  .letE (.call data (mk4 (arg 0) (arg 1) (.get (arg 7) (.nat 0)) (.get (arg 7) (.nat 1))))
    (.letE (itcsAskQuery colors (arg 8)) (itcsAskTail colors))

/-- A uniform structural cost for constructing the first request. -/
def itcsAskC (W Cd C₀ C₁ : ℕ) : ℕ := 500*(1000*(W+Cd+C₀+C₁+100)+1)+Cd+C₀+C₁

/-- The initial request stores no answers, and keeps the optional second state
as the exact queue expected by the step program. -/
theorem itcs_ask_value (Q payload : Val) (pending : List Val) :
    itcsAskV Q payload (.list pending) =
      .list [.nat 1,.nat 1,Q,.list [payload,.list pending,.list []]] := rfl

/-- The initial continuation's structural state has polynomial weight. -/
theorem itcs_ask_weight (Q payload pending : Val) :
    (itcsAskV Q payload pending).wt ≤ 10*(Q.wt+payload.wt+pending.wt+20) := by
  have hi := wt_list3_le payload pending (.list [])
  have ho := wt_list4_le (.nat 1) (.nat 1) Q (.list [payload,pending,.list []])
  have hn := wt_nat_le 1
  simp only [wt_list_nil] at hi
  unfold itcsAskV
  omega

end GI.Impl
