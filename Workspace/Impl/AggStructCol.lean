import Workspace.Impl.AggStructMath
import Workspace.Impl.AggCacheProg
import Workspace.Lang.Prims.Other

/-!
# The tuple colorings of the two strings, as a program

The refinement task (`KaryRefinementTask`) takes the colorings of all `κ`-tuples of the two
strings, as lists in the order of `finFunctionFinEquiv` (`encKColoring`). The color of `(z, t)`
is its class number by first occurrence (`stNum`): the index of the first tuple `t₀` with
`tupleRel (x, t₀) (z, t)` (`tcol_stNum`).

The program reads the relation through a module at `brel` (the hypothesis `StRelOK`): on
`[[cv, z, tv t], tv t₀]` it decides `R z t t₀`, for a context `cv` and an injective encoding
`tv` of tuples. With the comparison table of the comparison phase, `R z t t₀` is
`tupleRel (x, t₀) (strOf z, t)`: a table entry for two injective tuples, a comparison of the
equality patterns for two noninjective ones.

`stCols_spec`: on `[cv, tsV]` (all encoded tuples, in order) the module returns
`[encKColoring c₀, encKColoring c₁]` with `c_z t = ts.findIdx (R z t ·)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encKColoring)

variable {q κ : ℕ}

/-- All `κ`-tuples, in the order of `finFunctionFinEquiv`. -/
def stTs (q κ : ℕ) : List (Fin κ → Fin q) :=
  (List.finRange (q ^ κ)).map finFunctionFinEquiv.symm

theorem stTs_length : (stTs q κ).length = q ^ κ := by simp [stTs]

theorem mem_stTs (t : Fin κ → Fin q) : t ∈ stTs q κ := by
  simp only [stTs, List.mem_map, List.mem_finRange, true_and]
  exact ⟨finFunctionFinEquiv t, by simp⟩

/-- The color of `(z, t)`: the index of the first `t₀` with `R z t t₀`. -/
def stCz (R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool) (z : ℕ) (t : Fin κ → Fin q) : ℕ :=
  (stTs q κ).findIdx (R z t)

theorem stCz_le (R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool) (z : ℕ) (t : Fin κ → Fin q) :
    stCz R z t ≤ q ^ κ := stTs_length (q := q) (κ := κ) ▸ List.findIdx_le_length

/-- The list of the colors is the encoded coloring. -/
theorem stTs_map_nat (c : (Fin κ → Fin q) → ℕ) :
    Val.list ((stTs q κ).map fun t => .nat (c t)) = encKColoring c := by
  simp [stTs, encKColoring, List.map_map, Function.comp_def]

/-- **The contract of the relation module**: on `[[cv, z, tv t], tv t₀]`, for `z < 2`, it
returns `R z t t₀` at cost at most `Bc`. -/
def StRelOK (Pg : Program) (brel : ℕ) (cv : Val) (tv : (Fin κ → Fin q) → Val)
    (R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool) (Bc : ℕ) : Prop :=
  ∀ z t t₀, z < 2 →
    FunDet Pg brel (.list [.list [cv, .nat z, tv t], tv t₀]) (boolVal (R z t t₀)) Bc

/-- On `[[cv, tsV, z], tv t]`: find the first `t₀` in `tsV` with `R z t t₀`. -/
def stColF (bf : ℕ) : Expr :=
  .call bf (mk2 (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 2)) (arg 1)) (.get (arg 0) (.nat 1)))

/-- On `[cv, tsV]`: the two colorings. -/
def stColsF (bm : ℕ) : Expr :=
  mk2 (.call bm (mk2 (mk3 (arg 0) (arg 1) (.nat 0)) (arg 1)))
    (.call bm (mk2 (mk3 (arg 0) (arg 1) (.nat 1)) (arg 1)))

/-- The module at base `b` (eight functions), with the relation module at `brel`. -/
def stColsFuns (b brel : ℕ) : List Expr :=
  [stColsF (b + 1)] ++ mapFuns (b + 1) (b + 4) ++ [stColF (b + 5)] ++ findFuns (b + 5) brel

/-- The cost of one color, for size parameter `M`. -/
def stColCost (Bc M : ℕ) : ℕ := M * Bc + loopModK * (M + 1) * (10 * M + 40) + 400 * M + 1000

open Classical in
/-- The test of `find` on values. -/
noncomputable def stQv (tv : (Fin κ → Fin q) → Val)
    (R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool) (z : ℕ) (t : Fin κ → Fin q) (v : Val) :
    Bool :=
  decide (∃ t₀, tv t₀ = v ∧ R z t t₀ = true)

theorem stQv_tv {tv : (Fin κ → Fin q) → Val} (htv : Function.Injective tv)
    (R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool) (z : ℕ) (t t₀ : Fin κ → Fin q) :
    stQv tv R z t (tv t₀) = R z t t₀ := by
  unfold stQv
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨t₁, h1, h2⟩; rwa [← htv h1]
  · intro h; exact ⟨t₀, rfl, h⟩

theorem stCol_spec {Pg : Program} {f brel : ℕ} (hf : Pg.funs[f]? = some (stColF (f + 1)))
    (hfind : Pg.HasAt (f + 1) (findFuns (f + 1) brel)) {cv : Val}
    {tv : (Fin κ → Fin q) → Val} (htv : Function.Injective tv)
    {R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool} {Bc : ℕ}
    (hrel : StRelOK Pg brel cv tv R Bc) {z : ℕ} (hz : z < 2) (t : Fin κ → Fin q) {M : ℕ}
    (hM : (Val.list [cv, .list ((stTs q κ).map tv)]).wt ≤ M) :
    FunDet Pg f (.list [.list [cv, .list ((stTs q κ).map tv), .nat z], tv t])
      (.nat (stCz R z t)) (stColCost Bc M) := by
  set tsV := (stTs q κ).map tv with htsV
  set ctx := Val.list [cv, .list tsV, .nat z] with hctx
  set vs : List Val := [ctx, tv t]
  have g0 := Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 0) (v := ctx) rfl
  have g1 := Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 1) (v := tv t) rfl
  have dcv := Det.get' g0 (Det.nat 0) (v := cv) rfl
  have dz := Det.get' g0 (Det.nat 2) (v := .nat z) rfl
  have dts := Det.get' g0 (Det.nat 1) (v := .list tsV) rfl
  have darg := Det.mk2 (Det.mk3 dcv dz g1) dts
  have hT : ∀ x ∈ tsV, FunDet Pg brel (.list [.list [cv, .nat z, tv t], x])
      (boolVal (stQv tv R z t x)) Bc := by
    intro x hx
    obtain ⟨t₀, -, rfl⟩ := List.mem_map.1 hx
    rw [stQv_tv htv]
    exact hrel z t t₀ hz
  have hfd := (find_spec hfind hT)
  have hidx : tsV.findIdx (stQv tv R z t) = stCz R z t := by
    rw [htsV, List.findIdx_map]
    unfold stCz
    congr 1
    funext t₀
    exact stQv_tv htv R z t t₀
  rw [hidx] at hfd
  refine FunDet.intro hf ((Det.call darg (hfd.mono fun w c h => ⟨h.1, h.2⟩)).mono ?_)
  -- the cost
  have hwl := sum_wt_lt_wt_list [cv, .list tsV]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hwl
  have hn : tsV.length < (Val.list tsV).wt := length_lt_wt_list tsV
  have htt : (tv t).wt < (Val.list tsV).wt := wt_le_wt_list (List.mem_map.2 ⟨t, mem_stTs t, rfl⟩)
  have hz3 : (Val.nat z).wt ≤ 3 := (wt_nat_le z).trans (by omega)
  have hc1 := wt_list3_le cv (.nat z) (tv t)
  have hc2 := wt_list2_le (Val.list [cv, .nat z, tv t]) (.list tsV)
  have hc3 := wt_list3_le cv (.list tsV) (.nat z)
  have hc4 := wt_list2_le ctx (tv t)
  have hout : (Val.nat (stCz R z t)).wt ≤ tsV.length + 2 := by
    have := wt_nat_le (stCz R z t)
    have : stCz R z t ≤ tsV.length := by
      rw [htsV, List.length_map]; exact List.findIdx_le_length
    omega
  have hsum : (tsV.map fun _ => Bc).sum ≤ M * Bc := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have hloop : loopModK * (tsV.length + 1) *
      ((Val.list [.list [cv, .nat z, tv t], .list tsV]).wt + 2 * tsV.length + 3) ≤
      loopModK * (M + 1) * (10 * M + 40) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hvs : (Val.list vs).wt ≤ 2 * (ctx.wt + (tv t).wt) + 6 := wt_list2_le _ _
  have hctxw : ctx.wt = (Val.list [cv, .list tsV, .nat z]).wt := rfl
  unfold stColCost
  omega

theorem stForall₂_eq {tv : (Fin κ → Fin q) → Val} (htv : Function.Injective tv)
    (g : (Fin κ → Fin q) → Val) :
    ∀ (ts : List (Fin κ → Fin q)) (ws : List Val),
      List.Forall₂ (fun x w => ∃ t, x = tv t ∧ w = g t) (ts.map tv) ws → ws = ts.map g
  | [], ws, h => by cases h; rfl
  | t :: ts, ws, h => by
    cases h with
    | cons h1 h2 =>
      obtain ⟨t', e1, rfl⟩ := h1
      rw [htv e1, stForall₂_eq htv g ts _ h2]
      rfl

/-- The cost of the colors of one string, for size parameter `M`. -/
def stMapCost (Bc M : ℕ) : ℕ := M * stColCost Bc (3 * M + 10) + mapK * (M + 1) * (8 * M * M + 40 * M + 60)

theorem stColCost_mono (Bc : ℕ) {M M' : ℕ} (h : M ≤ M') : stColCost Bc M ≤ stColCost Bc M' := by
  unfold stColCost
  have h1 := Nat.mul_le_mul_right Bc h
  have h2 : loopModK * (M + 1) * (10 * M + 40) ≤ loopModK * (M' + 1) * (10 * M' + 40) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  omega

/-- **The colors of one string** (`z < 2`): on `[[cv, tsV, z], tsV]` the map returns
`encKColoring (stCz R z)`. -/
theorem stMap_spec {Pg : Program} {b brel : ℕ} (hb : Pg.HasAt b (stColsFuns b brel)) {cv : Val}
    {tv : (Fin κ → Fin q) → Val} (htv : Function.Injective tv)
    {R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool} {Bc : ℕ}
    (hrel : StRelOK Pg brel cv tv R Bc) {z : ℕ} (hz : z < 2) {M : ℕ}
    (hM : (Val.list [cv, .list ((stTs q κ).map tv)]).wt ≤ M) :
    FunDet Pg (b + 1)
      (.list [.list [cv, .list ((stTs q κ).map tv), .nat z], .list ((stTs q κ).map tv)])
      (encKColoring (stCz R z)) (stMapCost Bc M) := by
  have hmap : Pg.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := hb.left.left.right
  have hf : Pg.funs[b + 4]? = some (stColF (b + 5)) := by simpa using hb.left.right.single
  have hfind : Pg.HasAt (b + 5) (findFuns (b + 5) brel) := by simpa using hb.right
  set tsV := (stTs q κ).map tv with htsV
  set c := Val.list [cv, .list tsV, .nat z] with hc
  have hwl := sum_wt_lt_wt_list [cv, .list tsV]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hwl
  have hn : tsV.length < (Val.list tsV).wt := length_lt_wt_list tsV
  have hz3 : (Val.nat z).wt ≤ 3 := (wt_nat_le z).trans (by omega)
  have hc3 := wt_list3_le cv (.list tsV) (.nat z)
  have hcw : c.wt = (Val.list [cv, .list tsV, .nat z]).wt := rfl
  have hM' : (Val.list [cv, .list tsV]).wt ≤ 3 * M + 10 := by omega
  have hcol := fun t => stCol_spec (f := b + 4) hf hfind htv hrel hz t hM'
  have hm := map_spec hmap (c := c) (xs := tsV)
    (R := fun x w => ∃ t, x = tv t ∧ w = .nat (stCz R z t))
    (B := fun _ => stColCost Bc (3 * M + 10)) (fun x hx => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
      exact FunAll.mono (hcol t) fun w cost h => ⟨⟨t, rfl, h.1⟩, h.2⟩)
  refine hm.mono fun w cost h => ?_
  obtain ⟨ws, rfl, h2, hcost⟩ := h
  have hws := stForall₂_eq htv (fun t => .nat (stCz R z t)) _ ws h2
  have hw : Val.list ws = encKColoring (stCz R z) := by
    rw [hws, ← stTs_map_nat]
  refine ⟨hw, ?_⟩
  rw [hw] at hcost
  have hwk : (encKColoring (stCz R z)).wt ≤ q ^ κ * (2 * q ^ κ + 5) + 4 := by
    have := wt_encFun_le (n := q ^ κ) (fun j => stCz R z (finFunctionFinEquiv.symm j))
      (B := q ^ κ) fun j => stCz_le R z _
    exact this
  have hlen : tsV.length = q ^ κ := by rw [htsV, List.length_map, stTs_length]
  have hnM : q ^ κ ≤ M := by omega
  have hsq : q ^ κ * (2 * q ^ κ + 5) ≤ M * (2 * M + 5) := Nat.mul_le_mul hnM (by omega)
  have hsum : (tsV.map fun _ => stColCost Bc (3 * M + 10)).sum ≤ M * stColCost Bc (3 * M + 10) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have hcx := wt_list2_le c (.list tsV)
  have hloop : mapK * (tsV.length + 1) * ((Val.list [c, .list tsV]).wt +
      (encKColoring (stCz R z)).wt + 1) ≤ mapK * (M + 1) * (8 * M * M + 40 * M + 60) := by
    refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
    have : M * (2 * M + 5) = 2 * (M * M) + 5 * M := by ring
    have : 8 * M * M = 8 * (M * M) := by ring
    omega
  unfold stMapCost
  omega

/-- The cost of the module, for size parameter `M`. -/
def stColsCost (Bc M : ℕ) : ℕ := 2 * stMapCost Bc M + 100 * (M + 1) ^ 2

/-- **The two tuple colorings.** On `[cv, tsV]` the module returns
`[encKColoring (stCz R 0), encKColoring (stCz R 1)]`. -/
theorem stCols_spec {Pg : Program} {b brel : ℕ} (hb : Pg.HasAt b (stColsFuns b brel)) {cv : Val}
    {tv : (Fin κ → Fin q) → Val} (htv : Function.Injective tv)
    {R : ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool} {Bc : ℕ}
    (hrel : StRelOK Pg brel cv tv R Bc) {M : ℕ}
    (hM : (Val.list [cv, .list ((stTs q κ).map tv)]).wt ≤ M) :
    FunDet Pg b (.list [cv, .list ((stTs q κ).map tv)])
      (.list [encKColoring (stCz R 0), encKColoring (stCz R 1)]) (stColsCost Bc M) := by
  have hf : Pg.funs[b]? = some (stColsF (b + 1)) := by
    simpa using (hb.block 0 (gs := [stColsF (b + 1)]) (by rfl)).single
  set tsV := (stTs q κ).map tv with htsV
  set vs : List Val := [cv, .list tsV]
  have g0 := Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 0) (v := cv) rfl
  have g1 := Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 1) (v := .list tsV) rfl
  have a0 := Det.mk2 (Det.mk3 g0 g1 (Det.nat 0)) g1
  have a1 := Det.mk2 (Det.mk3 g0 g1 (Det.nat 1)) g1
  have m0 := stMap_spec hb htv hrel (z := 0) (by omega) hM
  have m1 := stMap_spec hb htv hrel (z := 1) (by omega) hM
  have d := Det.mk2 (Det.call a0 m0) (Det.call a1 m1)
  refine FunDet.intro hf (d.mono ?_)
  have hwl := sum_wt_lt_wt_list [cv, .list tsV]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hwl
  have hvs : (Val.list vs).wt = (Val.list [cv, .list tsV]).wt := rfl
  have hlen : tsV.length = q ^ κ := by rw [htsV, List.length_map, stTs_length]
  have hn : tsV.length < (Val.list tsV).wt := length_lt_wt_list tsV
  have hwk : ∀ z, (encKColoring (stCz R z)).wt ≤ q ^ κ * (2 * q ^ κ + 5) + 4 := fun z =>
    wt_encFun_le (n := q ^ κ) (fun j => stCz R z (finFunctionFinEquiv.symm j))
      (B := q ^ κ) fun j => stCz_le R z _
  have hsq : q ^ κ * (2 * q ^ κ + 5) ≤ M * (2 * M + 5) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : M * (2 * M + 5) = 2 * (M * M) + 5 * M := by ring
  have e2 : (M + 1) ^ 2 = M * M + 2 * M + 1 := by ring
  have w0 := hwk 0
  have w1 := hwk 1
  have hz0 := wt_nat_le 0
  have hz1 := wt_nat_le 1
  have l1 := wt_list3_le cv (.list tsV) (.nat 0)
  have l2 := wt_list3_le cv (.list tsV) (.nat 1)
  have l3 := wt_list2_le (.list [cv, .list tsV, .nat 0]) (.list tsV)
  have l4 := wt_list2_le (.list [cv, .list tsV, .nat 1]) (.list tsV)
  have l5 := wt_list2_le (encKColoring (stCz R 0)) (encKColoring (stCz R 1))
  unfold stColsCost
  omega

/-! ### The colors are the class numbers, and the refinement call -/

open Classical in
/-- The relation the program reads: `(x, t₀)` and `(z, t)` are in one comparison class, with
`z = 0` for `x` and `z = 1` for `y`. -/
noncomputable def stRel {Ω C : Type} (S : State Ω C) [Fintype S.dom] [DecidableEq S.dom]
    (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ) (x y : S.dom → C) :
    ℕ → (Fin κ → Fin q) → (Fin κ → Fin q) → Bool :=
  fun z t t₀ => decide (GI.LocalCertificates.tupleRel S.domGroup πd κ (x, t₀)
    (if z = 0 then x else y, t))

theorem stCz_tcol {Ω C : Type} (S : State Ω C) [Fintype S.dom] [DecidableEq S.dom]
    (πd : S.domGroup →* alternatingGroup (Fin q)) (κ : ℕ) (x y : S.dom → C) :
    stCz (stRel S πd κ x y) 0 = tcol S πd κ (stNum S κ (stTs q κ) x) x ∧
      stCz (stRel S πd κ x y) 1 = tcol S πd κ (stNum S κ (stTs q κ) x) y := by
  constructor <;> funext t <;> rw [tcol_stNum] <;> unfold stCz <;> congr 1

/-- The output of the cited task meets the clauses of a joint refinement of the round. -/
theorem st_jointOK {n k : ℕ} {c c' d d' : (Fin k → Fin n) → ℕ}
    (h : GI.Cited.JointRefinement c c' d d') : JointOK c c' d d' := h

/-! ### The call of the refinement task -/

/-- On `[q, [e, e']]`: the task `KaryRefinement` on `[q zeros, e, e']`. -/
def stRefF (brep j : ℕ) : Expr :=
  .prim j (mk3 (.call brep (mk2 (arg 0) (.nat 0))) (.get (arg 1) (.nat 0)) (.get (arg 1) (.nat 1)))

/-- The cost constant of `stRefF`. -/
def stRefK : ℕ := 10 ^ 6

theorem wt_replicate_zero_le (s : ℕ) : (Val.list (List.replicate s (.nat 0))).wt ≤ 7 * (s + 1) := by
  have h := wt_list_le (List.replicate s (Val.nat 0))
  have h1 : ((List.replicate s (Val.nat 0)).map Val.wt).sum ≤ s * 2 := by
    rw [List.map_replicate, List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_left _ (wt_nat_le 0)
  simp only [List.length_replicate] at h
  omega

/-- **The joint refinement call**: on the two colorings (values at most `q^κ`) it returns a
joint coherent refinement (`KaryOut`), at cost the bound of the task plus `stRefK (M + 1)²`, for
`M` at least the weight of the input and `q`. -/
theorem stRef_spec {κ : ℕ} (h : GI.Cited.KaryRefinement κ) {Pg : Program} {f brep j : ℕ}
    (hf : Pg.funs[f]? = some (stRefF brep j)) (hrep : Pg.HasAt brep (replicateFuns brep))
    (hj : Pg.prims[j]? = some (karyRefinementPrim h)) {q : ℕ} (c c' : (Fin κ → Fin q) → ℕ)
    (hc : ∀ t, c t ≤ q ^ κ) (hc' : ∀ t, c' t ≤ q ^ κ) {M : ℕ}
    (hM : (Val.list [.nat q, .list [encKColoring c, encKColoring c']]).wt ≤ M) (hqM : q ≤ M) :
    FunAll Pg f (.list [.nat q, .list [encKColoring c, encKColoring c']]) (fun w cost =>
      KaryOut c c' w ∧ cost ≤ (karyRefinementPrim h).bound (karyEnc c c') +
        30 * (q ^ κ + 1) ^ 2 + stRefK * (M + 1) ^ 2) := by
  set vs : List Val := [.nat q, .list [encKColoring c, encKColoring c']]
  have g0 := Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 0) (v := .nat q) rfl
  have g1 := Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 1)
    (v := .list [encKColoring c, encKColoring c']) rfl
  have hr := replicate_spec hrep q (.nat 0)
  have dr := Det.call (Det.mk2 g0 (Det.nat 0)) (hr.mono fun w cost h => ⟨h.1, by
    rw [h.1] at h; exact h.2⟩)
  have d0 := Det.get' g1 (Det.nat 0) (v := encKColoring c) rfl
  have d1 := Det.get' g1 (Det.nat 1) (v := encKColoring c') rfl
  have da := Det.mk3 dr d0 d1
  refine FunAll.intro hf ((karyRefinement_call h hc hc' hj da).mono fun w cost hw => ⟨hw.1, ?_⟩)
  have hvs : (Val.list vs).wt ≤ M := hM
  have hvs' : (Val.list vs).wt = (Val.list [.nat q, .list [encKColoring c, encKColoring c']]).wt :=
    rfl
  have w1 := wt_list2_le (encKColoring c) (encKColoring c')
  have hl := sum_wt_lt_wt_list vs
  simp only [vs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hl
  have hl2 := sum_wt_lt_wt_list [encKColoring c, encKColoring c']
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hl2
  have hrw := wt_replicate_zero_le q
  have hz := wt_nat_le 0
  have hqv := wt_list2_le (.nat q) (.nat 0)
  have h3 := wt_list3_le (Val.list (List.replicate q (.nat 0))) (encKColoring c) (encKColoring c')
  have hsq : (M + 1) * (M + 1) = (M + 1) ^ 2 := by ring
  have hM1 : M + 1 ≤ (M + 1) ^ 2 := by nlinarith
  have hlq : loopModK * (q + 1) * ((Val.list [.nat q, .nat 0]).wt + q +
      (Val.list (List.replicate q (.nat 0))).wt + 1) ≤ loopModK * (M + 1) * (20 * M + 40) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hlq2 : loopModK * (M + 1) * (20 * M + 40) ≤ 40 * loopModK * (M + 1) ^ 2 := by
    rw [← hsq]; nlinarith
  unfold stRefK loopModK at *
  omega

end GI.Impl
