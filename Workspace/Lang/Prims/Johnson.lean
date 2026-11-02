import Workspace.Lang.Prims.Basic
import Workspace.Lang.Prims.Repr
import Workspace.Cited.AlgoJohnson

/-!
# The Johnson identification as a primitive

The cited task `GI.Cited.JohnsonIdentificationTask` ([H, §2.8]) as a `GI.Lang` primitive,
following `Workspace/Lang/Prims/Other.lean`. The argument is `[G, m, k]`; the result is the list of
the `k`-sets of an identification `ι` carrying `G` onto `Alt(m)` on `k`-sets.
-/

namespace GI.Lang

open GI.Cited
open Equiv

/-- **Johnson identification** as a primitive. -/
noncomputable def johnsonPrim (h : JohnsonIdentification) : Prim := Prim.ofHyp _ _ h

/-- The result of the Johnson identification for `G ≤ Sym(n)` and `m, k`. -/
def JohnsonOut {n : ℕ} (G : Subgroup (Perm (Fin n))) (m k : ℕ) (w : Val) : Prop :=
  ∃ ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}, IsJohnsonId G ι ∧ w = encKSets ι

theorem johnsonPrim_spec (h : JohnsonIdentification) {n m k : ℕ} {gv : Val}
    {G : Subgroup (Perm (Fin n))} (hG : GroupVal n gv G) (h5 : 5 ≤ m) (hk1 : 1 ≤ k)
    (hb : (k + 1) ^ 2 < m + 2)
    (hJ : ∃ ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}, IsJohnsonId G ι) :
    PrimSpec (johnsonPrim h) (.list [gv, .nat m, .nat k]) (JohnsonOut G m k) := by
  obtain ⟨gs, rfl, rfl⟩ := hG
  exact Prim.ofHyp_spec h (⟨n, m, k, gs, h5, hk1, hb, hJ⟩ : JohnsonInst) (by
    rintro ⟨n', m', k', gs', _, _, _, _⟩ hy
    simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq, and_true] at hy
    obtain ⟨hg, rfl, rfl⟩ := hy
    obtain rfl := encGroup_deg hg
    obtain rfl := encGroup_injective hg
    rfl)

theorem johnson_call (h : JohnsonIdentification) {P : Program} {env : List Val}
    {j : ℕ} {a : Expr} {ca n m k : ℕ} {gv : Val} {G : Subgroup (Perm (Fin n))}
    (hj : P.prims[j]? = some (johnsonPrim h)) (ha : Det P env a (.list [gv, .nat m, .nat k]) ca)
    (hG : GroupVal n gv G) (h5 : 5 ≤ m) (hk1 : 1 ≤ k) (hb : (k + 1) ^ 2 < m + 2)
    (hJ : ∃ ι : Fin n ≃ {A : Finset (Fin m) // A.card = k}, IsJohnsonId G ι) :
    EvalAll P env (.prim j a) (fun w c => JohnsonOut G m k w ∧
      c ≤ ca + (johnsonPrim h).bound (.list [gv, .nat m, .nat k]) + w.wt + 1) :=
  EvalAll.prim_spec hj ha (johnsonPrim_spec h hG h5 hk1 hb hJ)

end GI.Lang
