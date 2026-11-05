module

public import Workspace.Lang.Prims.Blocks
public import Workspace.Lang.Prims.Reduce
public import Workspace.Impl.Canon
public import Workspace.Impl.GenCosetsMath

@[expose] public section

/-!
# The block kernel as a canonical group value

The children of the enumeration step (Algorithm 5) run under the kernel `K` of the action on the
blocks. Their state values must be canonical (`Canon`), so the group value of `K` must have at
most `k²` generators (`GroupValC`). The kernel program (`ker_spec`, with the cited `Preimage`)
gives some generators of `K`; the reduction (`reduce_spec`, with the cited `Membership`) keeps
at most `k²` of them.

`kerNF_spec` is the program; `kerNF_kernel` says that, for the block relation of a primitive
quotient, its group is the image of the block kernel on `Fin k`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens Preimage Membership)

variable {n : ℕ}

/-- The entry: reduce the generators of the kernel. -/
def kerNFEntry (b : ℕ) : Expr := .call (b + 1) (.call (b + 6) (.var 0))

/-- The kernel with at most `n²` generators, at base `b`. -/
def kerNFFuns (b jpre jmem : ℕ) : List Expr :=
  [kerNFEntry b] ++ reduceFuns (b + 1) jmem ++ kerFuns (b + 6) jpre

/-- The cost bound of the kernel with at most `n²` generators, for an argument of weight `T`. -/
noncomputable def kerNFCost (hp : Preimage) (hm : Membership) (n T : ℕ) : ℕ :=
  (preimagePrim hp).boundSize (3 * T) + kerK * T ^ 9 + reduceCost hm n (320 * (n + 1) ^ 6) +
    1000 * (n + 1) ^ 6 + 10 * T

/-- **The kernel of the action on the classes of an invariant relation, with at most `n²`
generators.** -/
theorem kerNF_spec (hp : Preimage) (hm : Membership) {P : Program} {b jpre jmem : ℕ}
    (hb : P.HasAt b (kerNFFuns b jpre jmem)) (hjp : P.prims[jpre]? = some (preimagePrim hp))
    (hjm : P.prims[jmem]? = some (membershipPrim hm)) {gv rv : Val}
    {G : Subgroup (Perm (Fin n))} {R : Fin n → Fin n → Prop} (hG : GroupVal n gv G)
    (hR : ReprVal n rv R) (hpres : ∀ g ∈ G, ∀ i j, R (g i) (g j) ↔ R i j) :
    FunAll P b (.list [gv, rv]) (fun w c =>
      (∃ K, GroupValC n w K ∧ ∀ g, g ∈ K ↔ g ∈ G ∧ ∀ i, R (g i) i) ∧
      c ≤ kerNFCost hp hm n (Val.list [gv, rv]).wt) := by
  simp only [kerNFFuns] at hb
  have he : P.funs[b]? = some (kerNFEntry b) := hb.left.left.single
  have hr : P.HasAt (b + 1) (reduceFuns (b + 1) jmem) := by simpa using hb.left.right
  have hk : P.HasAt (b + 6) (kerFuns (b + 6) jpre) := by
    simpa [reduceFuns, foldlFuns, loopFuns, Nat.add_assoc] using hb.right
  have hpos : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have inner : EvalAll P [Val.list [gv, rv]] (.call (b + 6) (.var 0)) (fun w c =>
      (∃ K, GroupVal n w K ∧ ∀ g, g ∈ K ↔ g ∈ G ∧ ∀ i, R (g i) i) ∧ w.wt ≤ 320 * (n + 1) ^ 6 ∧
      c ≤ (preimagePrim hp).boundSize (3 * (Val.list [gv, rv]).wt) +
        kerK * (Val.list [gv, rv]).wt ^ 9 + (Val.list [gv, rv]).wt + 320 * (n + 1) ^ 6 + 2) :=
    EvalAll.call_funAll (Det.var' (i := 0) rfl) fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact (ker_spec hp hk hjp hG hR hpres).mono fun w c hw =>
        ⟨hw.1, hw.2.1, by have := hw.2.1; have := hw.2.2; omega⟩
  refine FunAll.intro he (EvalAll.call_funAll inner fun v ca hv => ?_)
  obtain ⟨⟨K, ⟨gs, rfl, hgs⟩, hK⟩, hvw, hca⟩ := hv
  refine FunAll.mono (reduce_spec hm hr hjm gs) fun w c hw => ?_
  obtain ⟨rfl, hc⟩ := hw
  refine ⟨⟨K, ⟨keepList gs, rfl, by rw [gens_keepList, hgs], length_keepList_le gs⟩, hK⟩, ?_⟩
  have hlen : gs.length ≤ 320 * (n + 1) ^ 6 := by
    have h1 : gs.length < (Val.list (gs.map encPerm)).wt := by
      have := length_lt_wt_list (gs.map encPerm); simpa using this
    have h2 : (Val.list (gs.map encPerm)).wt ≤ (encGroup gs).wt := by
      have h3 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
        wt_le_wt_list (vs := [.nat n, .list ((1 :: gs).map encPerm)]) (by simp)
      have h4 : (Val.list (gs.map encPerm)).wt ≤ (Val.list ((1 :: gs).map encPerm)).wt :=
        wt_list_sublist (by simp)
      omega
    omega
  have hrc := reduceCost_mono hm n hlen
  have hw := wt_encGroup_le_sq (length_keepList_le gs)
  unfold kerNFCost
  omega

/-- **The kernel program on the block relation of a primitive quotient** gives a canonical value
of the block kernel. -/
theorem kerNF_kernel (hp : Preimage) (hm : Membership) {P : Program} {b jpre jmem : ℕ}
    (hb : P.HasAt b (kerNFFuns b jpre jmem)) (hjp : P.prims[jpre]? = some (preimagePrim hp))
    (hjm : P.prims[jmem]? = some (membershipPrim hm)) {Ω C : Type} {S : State Ω C}
    (Q : PrimitiveQuotient S) {k : ℕ} (e : Ω ≃ Fin k) {gv rv : Val}
    (hG : GroupVal k gv (groupFin e S.G))
    (hR : ReprVal k rv fun i j => Q.labFin e i = Q.labFin e j) :
    FunAll P b (.list [gv, rv]) (fun w c => GroupValC k w (groupFin e Q.kernel) ∧
      c ≤ kerNFCost hp hm k (Val.list [gv, rv]).wt) :=
  (kerNF_spec hp hm hb hjp hjm hG hR fun g hg i j => Q.labFin_pres e hg i j).mono
    fun w c hw => by
      obtain ⟨⟨K, hK, hmem⟩, hc⟩ := hw
      refine ⟨?_, hc⟩
      have : K = groupFin e Q.kernel := by
        ext g; rw [hmem, Q.mem_groupFin_kernel_iff]
      exact this ▸ hK

end GI.Impl
