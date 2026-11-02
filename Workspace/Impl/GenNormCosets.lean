import Workspace.Impl.GenNormGraph
import Workspace.Impl.GenNormReduce

/-!
# Computing normalization coset representatives by membership

Filter the parent generators for those outside the normalized group. An empty result means
normalization has one coset. Otherwise identity and the first filtered generator represent
the two cosets. The sign-kernel lemmas prove the cover, but the program computes no signs.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm Membership)
open scoped Pointwise

/-- Membership on numbered positions agrees with membership before numbering. -/
theorem normGroupFin_mem {Ω : Type} {n : ℕ} (en : Ω ≃ Fin n)
    (G : Subgroup (Perm Ω)) (a : Perm (Fin n)) :
    a ∈ groupFin en G ↔ (toFin en).symm a ∈ G := by
  constructor
  · rintro ⟨g, hg, he⟩
    rw [← he]
    change (toFin en).symm (toFin en g) ∈ G
    rw [MulEquiv.symm_apply_apply]
    exact hg
  · intro h
    exact ⟨(toFin en).symm a, h, MulEquiv.apply_symm_apply _ _⟩

/-- The computable choices remaining after fixing Cameron's identification. -/
structure normCosetData {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)
    {m k : ℕ} (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e) where
  τ : Fin ((Q.normGroup e hS).subgroupOf S.G).index → Perm Ω
  mem : ∀ j, τ j ∈ S.G
  cover : (S.G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (Q.normGroup e hS : Set (Perm Ω))

/-- Fix the exact Cameron identification while supplying the computed cosets. -/
def normCosetData.choice {Ω C : Type} {S : State Ω C} {Q : PrimitiveQuotient S}
    {m k : ℕ} {e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)} {hS : Q.ProductStructure m k 1 e}
    (D : normCosetData Q e hS) : Q.NormChoice :=
  ⟨m, k, e, hS, D.τ, D.mem, D.cover⟩

/-- On `[normalizedGroup,g]`, test whether `g` is outside the group. -/
def normOutsideF (jm : ℕ) : Expr :=
  .letE (.prim jm (.var 0)) (.ite (.var 1) (.nat 0) (.nat 1))

/-- Uniform budget for one membership test against a canonical group. -/
noncomputable def normOutsideCost (hm : Membership) (n : ℕ) : ℕ :=
  let W := 2 * (groupW n + 4 * (n + 1) ^ 2) + 6
  (membershipPrim hm).boundSize W + 100 * (W + 1)

open Classical in
/-- The outside test is the complement of the cited membership test. -/
theorem normOutside_spec (hm : Membership) {Pg : Program} {f jm n : ℕ}
    (hf : Pg.funs[f]? = some (normOutsideF jm))
    (hj : Pg.prims[jm]? = some (membershipPrim hm)) {gv : Val}
    {G : Subgroup (Perm (Fin n))} (hgv : GroupValC n gv G) (a : Perm (Fin n)) :
    FunDet Pg f (.list [gv, encPerm a]) (boolVal (decide (a ∉ G))) (normOutsideCost hm n) := by
  let inp := Val.list [gv, encPerm a]
  have wg := hgv.wt_le
  have wa := wt_encPerm_le a
  have wi := wt_list2_le gv (encPerm a)
  have hp := prim_bound_le_wt (membershipPrim hm)
    (show inp.wt ≤ 2 * (groupW n + 4 * (n + 1) ^ 2) + 6 by dsimp only [inp]; omega)
  change (membershipPrim hm).bound inp ≤
    (membershipPrim hm).boundSize (2 * (groupW n + 4 * (n + 1) ^ 2) + 6) at hp
  have hp' : (membershipPrim hm).bound (.list [gv, encPerm a]) ≤
    (membershipPrim hm).boundSize (2 * (groupW n + 4 * (n + 1) ^ 2) + 6) := hp
  have dcall := membership_call hm hj (Det.var' (P := Pg) (env := [inp]) (i := 0) rfl) hgv.groupVal
  refine FunDet.intro hf (EvalAll.letE dcall fun w c hw => ?_)
  obtain ⟨hw, hc⟩ := hw
  rcases hw with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
  · have hb : boolVal (decide (a ∉ G)) = .nat 0 := by simp [ha, boolVal]
    rw [hb]
    refine (Det.ite_pos (e := .nat 1)
      (Det.var' (P := Pg) (env := [inp, .nat 1]) (i := 1) rfl) (by decide) (Det.nat 0)).post
      fun cc hcc => ⟨rfl, ?_⟩
    have w0 := wt_nat_le 0
    have w1 := wt_nat_le 1
    unfold normOutsideCost
    dsimp only
    change _ ≤ _ at wi
    have ei : (Val.list [gv, encPerm a]).wt = inp.wt := rfl
    omega
  · have hb : boolVal (decide (a ∉ G)) = .nat 1 := by simp [ha, boolVal]
    rw [hb]
    refine (Det.ite_zero (t := .nat 0)
      (Det.var' (P := Pg) (env := [inp, .nat 0]) (i := 1) rfl) (Det.nat 1)).post
      fun cc hcc => ⟨rfl, ?_⟩
    have w0 := wt_nat_le 0
    have w1 := wt_nat_le 1
    unfold normOutsideCost
    dsimp only
    have ei : (Val.list [gv, encPerm a]).wt = inp.wt := rfl
    omega

/-- The outside predicate on a search value. It is used only on encoded permutations. -/
noncomputable def normOutsideQ {n : ℕ} (G : Subgroup (Perm (Fin n))) (v : Val) : Bool := by
  classical
  exact decide (∃ a : Perm (Fin n), v = encPerm a ∧ a ∉ G)

open Classical in
/-- The ghost predicate agrees with membership on every entry passed to the filter. -/
theorem normOutsideQ_enc {n : ℕ} (G : Subgroup (Perm (Fin n))) (a : Perm (Fin n)) :
    normOutsideQ G (encPerm a) = decide (a ∉ G) := by
  apply Bool.eq_iff_iff.mpr
  simp only [normOutsideQ, decide_eq_true_eq]
  constructor
  · rintro ⟨g, heq, hg⟩
    exact encPerm_injective heq ▸ hg
  · intro h
    exact ⟨a, rfl, h⟩

/-- On `[[normalizedGroup,identity],parentGenerators]`, return one or two representatives. -/
def normCosetsF (filter : ℕ) : Expr :=
  .letE (.call filter (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
    (.ite (.length (.var 1))
      (mk2 (.get (arg 0) (.nat 1)) (.get (.var 1) (.nat 0)))
      (mk1 (.get (arg 0) (.nat 1))))

/-- The filter and the one-or-two representative construction have polynomial own cost. -/
noncomputable def normCosetsCost (hm : Membership) (n L W : ℕ) : ℕ :=
  let U := L * (8 * (n + 1) ^ 2 + 1) + 4
  L * normOutsideCost hm n + loopModK * (L + 1) * (2 * (W + U) + 6 + L + U + 1) +
    10000 * (W + U + (n + 1) ^ 2 + 20)

/-- The returned list is exactly the chosen representatives, in its runtime order. -/
def normCosetsOut {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (w : Val) : Prop :=
  ∃ (D : normCosetData Q e hS) (ts : List (Perm (Fin n))),
    w = .list (ts.map encPerm) ∧ ts.length = ((Q.normGroup e hS).subgroupOf S.G).index ∧
      ∀ j, D.τ j = (toFin en).symm (ts.getD j 1)

/-- If all parent generators are normalized, identity is the whole transversal. -/
theorem normCosets_even {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (gs : List (Perm (Fin n)))
    (hgen : GI.Cited.gens gs = groupFin en S.G)
    (hgs : ∀ a ∈ gs, a ∈ groupFin en (Q.normGroup e hS)) :
    normCosetsOut en Q e hS (.list [encPerm (1 : Perm (Fin n))]) := by
  have heven : ∀ g : S.G, normSign Q e hS g = 1 := by
    apply normEven_of_gens Q e hS en gs hgen
    intro a ha haG
    exact (normMem_iff Q e hS ⟨_, haG⟩).mp ((normGroupFin_mem en _ a).mp (hgs a ha))
  let c := normChoiceEven Q e hS heven
  let D : normCosetData Q e hS := ⟨c.τ, c.τ_mem, c.cover⟩
  have hidx := normIndex_one Q e hS heven
  refine ⟨D, [1], rfl, by simpa using hidx.symm, ?_⟩
  intro j
  have hj : j.val = 0 := by have := j.2; omega
  change (1 : Perm Ω) = (toFin en).symm ([1].getD j.val 1)
  rw [hj]
  change (1 : Perm Ω) = (toFin en).symm 1
  exact (map_one (toFin en).symm).symm

/-- An element outside the normalized group supplies the second coset. -/
theorem normCosets_odd {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (a : Perm (Fin n))
    (ha : a ∈ groupFin en S.G) (hna : a ∉ groupFin en (Q.normGroup e hS)) :
    normCosetsOut en Q e hS (.list [encPerm (1 : Perm (Fin n)), encPerm a]) := by
  haveI : Finite Ω := Finite.of_equiv _ en.symm
  let t : S.G := ⟨(toFin en).symm a, (normGroupFin_mem en S.G a).mp ha⟩
  have ht : normSign Q e hS t ≠ 1 := by
    intro h
    apply hna
    apply (normGroupFin_mem en _ a).mpr
    exact (normMem_iff Q e hS t).mpr h
  let c := normChoiceOdd Q e hS t ht
  let D : normCosetData Q e hS := ⟨c.τ, c.τ_mem, c.cover⟩
  have hidx := normIndex_two Q e hS t ht
  refine ⟨D, [1, a], rfl, by simpa using hidx.symm, ?_⟩
  intro j
  have hj : j.val < 2 := by have := j.2; omega
  change (if j.val = 0 then 1 else (t : Perm Ω)) =
    (toFin en).symm ([1, a].getD j.val 1)
  by_cases h0 : j.val = 0
  · rw [h0]
    change (1 : Perm Ω) = (toFin en).symm 1
    exact (map_one (toFin en).symm).symm
  · have h1 : j.val = 1 := by omega
    rw [h1]
    rfl

open Classical in
/-- The program computes the one or two representatives used by `NormChoice`. -/
theorem normCosets_spec (hm : Membership) {Pg : Program} {f filter test jm : ℕ}
    (hf : Pg.funs[f]? = some (normCosetsF filter))
    (hfilter : Pg.HasAt filter (filterFuns filter test))
    (htest : Pg.funs[test]? = some (normOutsideF jm))
    (hj : Pg.prims[jm]? = some (membershipPrim hm))
    {Ω C : Type} {S : State Ω C} {n m k : ℕ} (en : Ω ≃ Fin n)
    (Q : PrimitiveQuotient S) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k))
    (hS : Q.ProductStructure m k 1 e) (gs : List (Perm (Fin n)))
    (hgen : GI.Cited.gens gs = groupFin en S.G) {gv : Val}
    (hgv : GroupValC n gv (groupFin en (Q.normGroup e hS))) :
    FunAll Pg f (.list [.list [gv, encPerm (1 : Perm (Fin n))], .list (gs.map encPerm)])
      (fun w cost => normCosetsOut en Q e hS w ∧ cost ≤ normCosetsCost hm n gs.length
        (Val.list [gv, encPerm (1 : Perm (Fin n))]).wt) := by
  let K := groupFin en (Q.normGroup e hS)
  let ctx := Val.list [gv, encPerm (1 : Perm (Fin n))]
  let inp := Val.list [ctx, .list (gs.map encPerm)]
  let outs := gs.filter (fun a => decide (a ∉ K))
  let U := gs.length * (8 * (n + 1) ^ 2 + 1) + 4
  let F := gs.length * normOutsideCost hm n + loopModK * (gs.length + 1) *
    (2 * (ctx.wt + U) + 6 + gs.length + U + 1)
  have hcb : ∀ v ∈ gs.map encPerm, FunDet Pg test (.list [gv, v])
      (boolVal (normOutsideQ K v)) (normOutsideCost hm n) := by
    intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    rw [normOutsideQ_enc]
    exact normOutside_spec hm htest hj hgv a
  have hfil := filter_spec hfilter hcb
  have heq : (gs.map encPerm).filter (normOutsideQ K) = outs.map encPerm := by
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro a _
    exact normOutsideQ_enc K a
  rw [heq] at hfil
  have hL : outs.length ≤ gs.length := List.length_filter_le _ _
  have wi := wt_list_map_le gs encPerm (fun a _ => wt_encPerm_le a)
  have wo := wt_list_map_le outs encPerm (fun a _ => wt_encPerm_le a)
  have hcoef : 2 * (4 * (n + 1) ^ 2) + 1 = 8 * (n + 1) ^ 2 + 1 := by ring
  rw [hcoef] at wi wo
  have wiU : (Val.list (gs.map encPerm)).wt ≤ U := wi
  have woU : (Val.list (outs.map encPerm)).wt ≤ U := by
    dsimp only [U]
    have h := Nat.mul_le_mul_right (8 * (n + 1) ^ 2 + 1) hL
    omega
  have hLU : gs.length ≤ U := by
    dsimp only [U]
    have h := Nat.le_mul_of_pos_right gs.length (show 0 < 8 * (n + 1) ^ 2 + 1 by omega)
    omega
  have wg : gv.wt < ctx.wt := wt_le_wt_list (by simp)
  have einp : (Val.list [ctx, .list (gs.map encPerm)]).wt = inp.wt := rfl
  have wc : ctx.wt < inp.wt := wt_le_wt_list (by simp)
  have win := wt_list2_le ctx (.list (gs.map encPerm))
  have wgarg := wt_list2_le gv (.list (gs.map encPerm))
  have wid := wt_encPerm_le (1 : Perm (Fin n))
  have hsub : FunDet Pg filter (.list [gv, .list (gs.map encPerm)])
      (.list (outs.map encPerm)) F := by
    refine hfil.mono fun w cost hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    rw [hw.1] at hc
    have hsum : ((gs.map encPerm).map (fun _ => normOutsideCost hm n)).sum =
        gs.length * normOutsideCost hm n := by
      simp only [List.map_map, Function.comp_def]
      simp [List.map_const', List.sum_replicate, smul_eq_mul]
    rw [hsum] at hc
    simp only [List.length_map] at hc
    dsimp only [F]
    refine hc.trans (Nat.add_le_add_left ?_ _)
    apply Nat.mul_le_mul_left
    omega
  have dg : Det Pg [inp] (.get (arg 0) (.nat 0)) gv (5 * inp.wt + 20) :=
    (Det.get' (Det.arg' (P := Pg) (vs := [ctx, .list (gs.map encPerm)]) (j := 0) rfl)
      (Det.nat 0) rfl).mono (by omega)
  have dgs : Det Pg [inp] (arg 1) (.list (gs.map encPerm)) (2 * inp.wt + 6) :=
    Det.arg' (j := 1) rfl
  have dc := Det.call (Det.mk2 dg dgs) hsub
  have did : ∀ rest, Det Pg (inp :: rest) (.get (arg 0) (.nat 1)) (encPerm (1 : Perm (Fin n)))
      (5 * inp.wt + 30) := by
    intro rest
    have w : (encPerm (1 : Perm (Fin n))).wt < ctx.wt := wt_le_wt_list (by simp)
    exact (Det.get' (Det.arg' (P := Pg) (vs := [ctx, .list (gs.map encPerm)]) (rest := rest)
      (j := 0) rfl) (Det.nat 1) rfl).mono (by omega)
  have dvar := Det.var' (P := Pg) (env := [inp, .list (outs.map encPerm)]) (i := 1) rfl
  have dlen := Det.length dvar
  have warg := wt_list2_le gv (.list (gs.map encPerm))
  have hcost : normCosetsCost hm n gs.length ctx.wt =
      F + 10000 * (ctx.wt + U + (n + 1) ^ 2 + 20) := rfl
  refine FunAll.intro hf ?_
  cases ho : outs with
  | nil =>
    have hgs : ∀ a ∈ gs, a ∈ K := by
      intro a ha
      by_contra h
      have hh : a ∈ outs := List.mem_filter.mpr ⟨ha, by simp [h]⟩
      rw [ho] at hh
      cases hh
    have hout := normCosets_even en Q e hS gs hgen hgs
    rw [ho] at dc dlen
    simp only [List.map_nil, List.length_nil] at dc dlen
    have db := Det.ite_zero
      (t := mk2 (.get (arg 0) (.nat 1)) (.get (.var 1) (.nat 0))) dlen (Det.mk1 (did _))
    refine (Det.letE dc db).post fun cost hc => ⟨hout, ?_⟩
    have wnil : (Val.list []).wt = 4 := rfl
    have wp := wt_list1_le (encPerm (1 : Perm (Fin n)))
    have wzero := wt_nat_le 0
    change _ ≤ normCosetsCost hm n gs.length ctx.wt
    rw [hcost]
    omega
  | cons a rest =>
    have haout : a ∈ outs := by rw [ho]; simp
    have ha := (List.mem_filter.mp haout).1
    have hna : a ∉ K := of_decide_eq_true (List.mem_filter.mp haout).2
    have haG : a ∈ groupFin en S.G := hgen ▸ Subgroup.subset_closure ha
    have hout := normCosets_odd en Q e hS a haG hna
    rw [ho] at dc dlen
    simp only [List.map_cons, List.length_cons, List.length_map] at dc dlen
    have dfirst := Det.get' (Det.var' (P := Pg)
      (env := [inp, .list (encPerm a :: rest.map encPerm)]) (i := 1) rfl) (Det.nat 0) rfl
    have db := Det.ite_pos (e := mk1 (.get (arg 0) (.nat 1))) dlen (by omega)
      (Det.mk2 (did _) dfirst)
    refine (Det.letE dc db).post fun cost hc => ⟨hout, ?_⟩
    have wa := wt_encPerm_le a
    have wp := wt_list2_le (encPerm (1 : Perm (Fin n))) (encPerm a)
    have wlen := wt_nat_le (rest.length + 1)
    have wout : (Val.list (encPerm a :: rest.map encPerm)).wt ≤ U := by
      simpa only [ho, List.map_cons] using woU
    have hrlen : rest.length + 1 ≤ gs.length := by simpa only [ho, List.length_cons] using hL
    change _ ≤ normCosetsCost hm n gs.length ctx.wt
    rw [hcost]
    omega

end GI.Impl
