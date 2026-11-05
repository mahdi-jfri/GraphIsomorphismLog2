module

public import Workspace.Impl.AggItemCiSojFront
public import Workspace.Impl.AggItemCiSojIItem
public import Workspace.Impl.AggItemCiSojBP
public import Workspace.Impl.AggItemCiSojBW
public import Workspace.Impl.AggItemCiSojRes

@[expose] public section

/-! # The full first-rectangle start program's source dispatch -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.CoherentEntrance Equiv Equiv.Perm
open GI.Cited (Val)

/-- The actual start program. It follows the model's cut, balance, and rectangle
branches in that order. The rectangle callee receives the original item input,
source fiber, source balanced table, and computed source certificate. -/
def itcsStartF (front pc rng bal baltest imp part cert rect : ℕ) : Expr :=
  let xc := Expr.get (arg 2) (.nat 1)
  let yc := Expr.get (arg 3) (.nat 1)
  let fiber := Expr.get (.var 1) (.nat 0)
  let scan := Expr.get (.var 1) (.nat 1)
  let n := Expr.length fiber
  .letE (.call front xc)
    (.ite (.arith .lt scan (.arith .mul n n))
      (.letE (.call pc (mk2 (mk3 (.get xc (.nat 0)) fiber n) scan))
        (itcsResE (.call imp (mk3 xc yc (.var 2)))))
      (.letE (.call rng (.length (.get xc (.nat 0))))
        (.letE (.call bal (mk2 xc (.var 2)))
          (.ite (.call baltest (mk2 (mk2 (.var 3) n) fiber))
            (itcsResE (.call part (mk2 xc yc)))
            (.letE (.call cert xc) (.call rect (mk4 (.var 0) fiber (.var 3) (.var 4))))))))

variable {q : ℕ}

/-- The scan result is always at most its no-hit index. -/
theorem itcs_imp_scan_le (X : PairCfg q) :
    itcsImpScan X ≤ X.fiber.card*X.fiber.card := by
  have h := List.findIdx_le_length (p:=itcsImpQ X)
    (xs:=(List.range (X.fiber.card*X.fiber.card)).map Val.nat)
  simpa only [itcsImpScan,List.length_map,List.length_range] using h

/-- The start program's exact integer branch test is the negation of the model's
primitive-cut predicate. -/
theorem itcs_imp_scan_lt (X : PairCfg q) (hX : X.Good deltaB) {x₀ : Fin q}
    (hx : x₀∈X.fiber) :
    itcsImpScan X < X.fiber.card*X.fiber.card ↔ ¬ PrimitiveColorCuts X.coloring false := by
  rw [←itcs_imp_scan_primitive X hX hx]
  have h := itcs_imp_scan_le X
  omega

/-- The selected implication color is a fixed function of the source object. -/
noncomputable def itcsImpValue (X : PairCfg q) (h : ∃ a b, ImpPair X a b) : ℕ :=
  X.col (X.emb rfl (itcsImp X h).1.1) (X.emb rfl (itcsImp X h).1.2)

/-- The selected raw color meets the palette bound. -/
theorem itcs_imp_value_le (X : PairCfg q) (x₀ : Fin q) {B : ℕ}
    (hcol : itCfColsLe (.pair X x₀) B) (h : ∃ a b, ImpPair X a b) :
    itcsImpValue X h ≤ B := hcol.1 _ _

/-- The actual component item receives blocks of size at least two, as required
by its full partition-item proof. -/
theorem itcs_imp_value_components (X : PairCfg q) (h : ∃ a b, ImpPair X a b) :
    ∀ a ∈ X.fiber, 2 ≤ (X.comp (itcsImpValue X h) a).card := by
  have hh := (itcs_imp_sizes X (itcsImp X h).1.1 (itcsImp X h).1.2).1 (itcsImp X h).2
  intro a ha
  have hb := (hh.2 a ha).1
  change 2 ≤ (itpBlk (itcsLab X (itcsImpValue X h)) a).card at hb
  rwa [itcs_lab_blk] at hb

end GI.Impl
