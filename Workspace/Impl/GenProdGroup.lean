module

public import Workspace.Impl.GenProdSq
public import Workspace.Impl.GenKernel
public import Workspace.Impl.GenEnum

@[expose] public section

/-!
# The product refinement: the coordinate group and its cosets

The coordinate group is the stabilizer in `G` of the mask labeling of the pairs of points
(`sqAct_maskF_iff`). On pairs, `G` acts through the squares `g × g`.

* `prod_cosetList`: the transversal of the orbit of the mask labeling under the squares, moved
  back by `unsq`, meets every coset of the coordinate group once.
* `prodKer_spec`: the kernel program on the squares and the relation "equal masks", followed by
  `unsq` of the generators and the reduction, gives a canonical value of the coordinate group.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Preimage Membership)

section math

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
  (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) {k : ℕ} (e : Ω ≃ Fin k)

/-- **Coset representatives of the coordinate group.** -/
theorem prod_cosetList (hS : Q.ProductStructure m l r E) (hb : 2 ≤ m.choose l)
    {gs : List (Perm (Fin k))} (hG : genGroup gs = groupFin e S.G)
    (L : List ((Fin (k * k) → ℕ) × Perm (Fin (k * k)))) (hnd : (L.map Prod.fst).Nodup)
    (horb : ∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit labAct (gs.map sqPerm) (maskF Q E e))
    (hp : ∀ p ∈ L, p.2 ∈ genGroup (gs.map sqPerm) ∧ labAct p.2 (maskF Q E e) = p.1) :
    let ts := ((L.map fun p => unsq p.2)).map (toFin e).symm
    (∀ t ∈ ts, t ∈ S.G) ∧ (∀ g ∈ S.G, ∃ t ∈ ts, t⁻¹ * g ∈ Q.coordinateGroup E hS hb) ∧
      (∀ i j (hi : i < ts.length) (hj : j < ts.length),
        ts[i]⁻¹ * ts[j] ∈ Q.coordinateGroup E hS hb → i = j) := by
  have h := cosetList_of_stab (act := sqAct) isAct_sq (x₀ := maskF Q E e) (K :=
    Q.coordinateGroup E hS hb) e hG (fun h hh => sqAct_maskF_iff Q E e hS hb hh)
    (L.map fun p => (p.1, unsq p.2)) (by simpa [List.map_map, Function.comp_def] using hnd)
    (fun y => by
      rw [← actOrbit_sq, ← horb]
      simp [List.map_map, Function.comp_def])
    (fun p hpL => by
      obtain ⟨h1, h2, -⟩ := sqPairs_good gs (maskF Q E e) L hp p hpL
      exact ⟨h1, h2⟩)
  simpa [List.map_map, Function.comp_def] using h

/-- The relation "equal masks" is kept by the squares of `G`, and its kernel there is the square
of the coordinate group. -/
theorem prodKer_eq (hS : Q.ProductStructure m l r E) (hb : 2 ≤ m.choose l)
    (K : Subgroup (Perm (Fin (k * k))))
    (hK : ∀ g, g ∈ K ↔ g ∈ (groupFin e S.G).map sqHom ∧
      ∀ i, maskF Q E e (g i) = maskF Q E e i) :
    K = (groupFin e (Q.coordinateGroup E hS hb)).map sqHom := by
  ext x
  rw [hK, maskF_kernel Q E e hS hb]

end math

/-! ### The programs -/

variable {k : ℕ}

theorem sqPerm_one : sqPerm (1 : Perm (Fin k)) = 1 := map_one (sqHom (k := k))

theorem unsq_one : unsq (1 : Perm (Fin (k * k))) = 1 := by
  rw [← sqPerm_one, unsq_sqPerm]

/-- The constant `1`, on any argument. -/
def oneF : Expr := .nat 1

theorem one_det {P : Program} {f : ℕ} (hf : P.funs[f]? = some oneF) (x : Val) :
    FunDet P f x (.nat 1) 4 := FunDet.intro hf (Det.nat 1)

/-- The labels compared with "equal": the first pair with the same label. -/
theorem reprVal_eqLab (lab : Fin k → ℕ) :
    ReprVal k (encFun (Cls.repOf (Cls.keyOf lab fun _ => 1))) (fun i j => lab i = lab j) := by
  have hk : Cls.keyOf lab (fun _ : Fin k => 1) = lab := by funext i; simp [Cls.keyOf]
  rw [hk]
  refine ⟨fun i => ⟨Cls.repOf lab i, Cls.repOf_lt _ i⟩, rfl, fun i j => ?_, fun i => ?_⟩
  · rw [Fin.mk.injEq, Cls.repOf_eq_iff]
  · exact Fin.ext (Cls.repOf_idem _ i)

/-- **The coordinate group as a program.** On `[c, gsq, mask, ones]` with `c = [k, ids]`: the
classes of equal masks (`cls`), the kernel of the squares on them (`kerNF`), the generators back
from the squares (`unsq`), the reduction. -/
def pkerE (bcls bker bmu bred : ℕ) : Expr :=
  .letE (.call bcls (mk2 (arg 2) (arg 3)))
  (.letE (.call bker (mk2 (arg 1) (.get (.var 1) (.nat 2))))
  (.letE (.call bmu (mk2 (arg 0) (.get (.var 2) (.nat 1))))
    (.call bred (mk2 (.get (arg 0) (.nat 0)) (.var 3)))))

/-- The context of the conversions back from pairs. -/
def cK (k : ℕ) : Val := .list [.nat k, encFun fun j : Fin k => (j : ℕ)]

theorem wt_cK_le (k : ℕ) : (cK k).wt ≤ 20 * (k + 1) ^ 2 := by
  have h1 := wt_list2_le (.nat k) (encFun fun j : Fin k => (j : ℕ))
  have h2 := wt_ids_le k
  have h3 := wt_nat_le k
  have : k + 1 ≤ (k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  show (Val.list [.nat k, encFun fun j : Fin k => (j : ℕ)]).wt ≤ _
  omega

/-- The bound of the conversion of the kernel generators. -/
theorem mapUnsq_cost_le (n : ℕ) (hn : n ≤ (k * k) ^ 2 + 1) (wi wo : ℕ)
    (hwi : wi ≤ 1000 * (k + 1) ^ 12) (hwo : wo ≤ ((k * k) ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) + 4) :
    n * (sqConvK * (k + 1) ^ 6) + mapK * (n + 1) * (wi + wo + 1) ≤ 10 ^ 14 * (k + 1) ^ 16 := by
  have hk1 : 1 ≤ k + 1 := by omega
  have e1 : (k * k) ^ 2 + 1 ≤ (k + 1) ^ 4 := by nlinarith [Nat.zero_le k]
  have p2 : 1 ≤ (k + 1) ^ 2 := Nat.one_le_pow _ _ hk1
  have p4 : (k + 1) ^ 2 ≤ (k + 1) ^ 4 := Nat.pow_le_pow_right hk1 (by norm_num)
  have p12 : (k + 1) ^ 6 ≤ (k + 1) ^ 12 := Nat.pow_le_pow_right hk1 (by norm_num)
  have p1 : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ hk1
  have hwo' : wo ≤ 13 * (k + 1) ^ 6 := by
    have : ((k * k) ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) ≤ (k + 1) ^ 4 * (9 * (k + 1) ^ 2) :=
      Nat.mul_le_mul e1 (by omega)
    have e : (k + 1) ^ 4 * (9 * (k + 1) ^ 2) = 9 * (k + 1) ^ 6 := by ring
    have : 1 ≤ (k + 1) ^ 6 := Nat.one_le_pow _ _ hk1
    omega
  have m1 : n * (sqConvK * (k + 1) ^ 6) ≤ (k + 1) ^ 4 * (sqConvK * (k + 1) ^ 12) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ p12)
  have m2 : mapK * (n + 1) * (wi + wo + 1) ≤ 1000 * (2 * (k + 1) ^ 4) * (1100 * (k + 1) ^ 12) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : (k + 1) ^ 4 * (sqConvK * (k + 1) ^ 12) = sqConvK * (k + 1) ^ 16 := by ring
  have e3 : 1000 * (2 * (k + 1) ^ 4) * (1100 * (k + 1) ^ 12) = 2200000 * (k + 1) ^ 16 := by ring
  simp only [sqConvK] at e2 m1 ⊢
  omega

theorem aux_wi {X a b c P : ℕ} (h1 : X ≤ 2 * (a + b) + 6) (h2 : a ≤ 20 * P) (h3 : b < c)
    (h4 : c ≤ 320 * P) : X ≤ 1000 * P := by omega

/-- The cost of `pkerE` on an input of weight `W`. -/
noncomputable def pkerCost (hp : Preimage) (hm : Membership) (k W : ℕ) : ℕ :=
  clsK * (W + 1) ^ 4 + kerNFCost hp hm (k * k) (100 * (W + 1) ^ 2) +
    reduceCost hm k ((k * k) ^ 2) + 10 ^ 15 * (k + 1) ^ 16 + 10 ^ 4 * (W + 1) ^ 2

set_option maxHeartbeats 4000000 in
/-- **The coordinate group as a program.** -/
theorem pker_spec (hp : Preimage) (hm : Membership) {P : Program}
    {f bcls bker jpre jm bmu fu bmt fe bred : ℕ}
    (hf : P.funs[f]? = some (pkerE bcls bker bmu bred))
    (hcls : P.HasAt bcls (clsFuns bcls))
    (hker : P.HasAt bker (kerNFFuns bker jpre jm)) (hjp : P.prims[jpre]? = some (preimagePrim hp))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hmu : P.HasAt bmu (mapFuns bmu fu)) (hfu : P.funs[fu]? = some (tabWrapF bmt))
    (hbmt : P.HasAt bmt (mapFuns bmt fe)) (hfe : P.funs[fe]? = some unsqEntF)
    (hred : P.HasAt bred (reduceFuns bred jm))
    {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S) {m l r : ℕ}
    (E : Fin Q.d ≃ (Fin r → Product.KSet m l)) (e : Ω ≃ Fin k)
    (hS : Q.ProductStructure m l r E) (hb : 2 ≤ m.choose l)
    (hmask : ∀ j, maskF Q E e j ≤ k * k)
    {hs : List (Perm (Fin (k * k)))} (hhs : gens hs = (groupFin e S.G).map sqHom) :
    FunAll P f (.list [cK k, encGroup hs, encFun (maskF Q E e), encFun fun _ : Fin (k * k) => 1])
      (fun w c => GroupValC k w (groupFin e (Q.coordinateGroup E hS hb)) ∧
        c ≤ pkerCost hp hm k (Val.list [cK k, encGroup hs, encFun (maskF Q E e),
          encFun fun _ : Fin (k * k) => 1]).wt) := by
  obtain ⟨W, hW⟩ : ∃ W, W = (Val.list [cK k, encGroup hs, encFun (maskF Q E e),
    encFun fun _ : Fin (k * k) => 1]).wt := ⟨_, rfl⟩
  rw [← hW]
  set vs := [cK k, encGroup hs, encFun (maskF Q E e), encFun fun _ : Fin (k * k) => 1] with hvs
  have hsum := sum_wt_lt_wt_list vs
  simp only [hvs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have hWv : (Val.list vs).wt = (Val.list [cK k, encGroup hs, encFun (maskF Q E e),
    encFun fun _ : Fin (k * k) => 1]).wt := rfl
  have hones : k * k < (encFun fun _ : Fin (k * k) => 1).wt := by
    have := length_lt_wt_list ((List.finRange (k * k)).map fun _ => Val.nat 1)
    simpa [encFun] using this
  have hkW : k * k ≤ W := by omega
  have hkW' : k ≤ W := (Nat.le_mul_self k).trans hkW
  -- the classes
  have dc := Det.call (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl)
    (Det.arg' (P := P) (vs := vs) (rest := []) (j := 3) rfl))
    (cls_spec hcls (maskF Q E e) (fun _ => 1) (X := W) (fun j => (hmask j).trans hkW)
      (fun _ => le_rfl) hkW)
  refine FunAll.intro hf (EvalAll.letE dc fun cv c1 hc1 => ?_)
  obtain ⟨rfl, hc1⟩ := hc1
  -- the kernel on the squares
  have hR := reprVal_eqLab (maskF Q E e)
  have wcls : (clsVal (maskF Q E e) fun _ => 1).wt ≤ 40 * (W + 1) ^ 2 :=
    (wt_clsVal_le _ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have dA := Det.mk2 (Det.arg' (P := P) (vs := vs)
      (rest := [clsVal (maskF Q E e) fun _ => 1]) (j := 1) rfl)
      (Det.get' (Det.var' (P := P) (env := [.list vs, clsVal (maskF Q E e) fun _ => 1]) (i := 1)
        rfl) (Det.nat 2) (v := encFun (Cls.repOf (Cls.keyOf (maskF Q E e) fun _ => 1))) rfl)
  have wrep : (encFun (Cls.repOf (Cls.keyOf (maskF Q E e) fun _ => 1))).wt <
      (clsVal (maskF Q E e) fun _ => 1).wt := wt_le_wt_list (by simp)
  have wgh : (encGroup hs).wt < W := by omega
  have wA := wt_list2_le (encGroup hs) (encFun (Cls.repOf (Cls.keyOf (maskF Q E e) fun _ => 1)))
  have wenv := wt_list2_le (Val.list vs) (clsVal (maskF Q E e) fun _ => 1)
  have hWW : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have ecl : (Val.list [encFun (Cls.numOf (fun _ => 1) (Cls.keyOf (maskF Q E e) fun _ => 1)),
      natList (Cls.repsOf (fun _ => 1) (Cls.keyOf (maskF Q E e) fun _ => 1)),
      encFun (Cls.repOf (Cls.keyOf (maskF Q E e) fun _ => 1))]).wt =
      (clsVal (maskF Q E e) fun _ => 1).wt := rfl
  have dA' := dA.mono (c' := 1000 * (W + 1) ^ 2) (by omega)
  have dK := EvalAll.call_funAll dA' (Q := fun w c => (∃ K, GroupValC (k * k) w K ∧ ∀ g, g ∈ K ↔
      g ∈ (groupFin e S.G).map sqHom ∧ ∀ i, maskF Q E e (g i) = maskF Q E e i) ∧
      c ≤ 1000 * (W + 1) ^ 2 + kerNFCost hp hm (k * k) (100 * (W + 1) ^ 2) + w.wt + 1)
    fun v ca h => by
      obtain ⟨rfl, hca⟩ := h
      refine (kerNF_spec hp hm hker hjp hjm (n := k * k) ⟨hs, rfl, hhs⟩ hR
        (fun g hg i j => maskF_pres Q E e hS hg i j)).mono fun w c hw => ⟨hw.1, ?_⟩
      have := kerNFCost_mono hp hm (k * k) (show (Val.list [encGroup hs,
        encFun (Cls.repOf (Cls.keyOf (maskF Q E e) fun _ => 1))]).wt ≤ 100 * (W + 1) ^ 2 by
          have : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
          omega)
      have := hw.2
      omega
  refine EvalAll.letE dK fun kv c2 hc2 => ?_
  obtain ⟨⟨K, ⟨hs', rfl, hgs', hlen'⟩, hKmem⟩, hc2⟩ := hc2
  have hK := prodKer_eq Q E e hS hb K hKmem
  rw [hK] at hgs'
  -- the generators back from the squares
  have hsq : ∀ g ∈ (1 :: hs'), sqPerm (unsq g) = g := fun g hg => by
    have : g ∈ (groupFin e (Q.coordinateGroup E hS hb)).map sqHom := by
      rcases List.mem_cons.1 hg with rfl | hg
      · exact Subgroup.one_mem _
      · exact hgs' ▸ Subgroup.subset_closure hg
    exact (mem_map_sq this).2
  have hconv : ∀ g ∈ (1 :: hs'), FunDet P fu (.list [cK k, encPerm g]) (encPerm (unsq g))
      (sqConvK * (k + 1) ^ 6) := fun g hg => by
    have := unsqPerm_spec hfu hbmt hfe (unsq g)
    rwa [hsq g hg] at this
  set env3 := [Val.list vs, clsVal (maskF Q E e) (fun _ => 1), encGroup hs']
  have dM := Det.call (Det.mk2 (Det.arg' (P := P) (vs := vs) (rest := env3.tail) (j := 0) rfl)
    (Det.get' (Det.var' (P := P) (env := env3) (i := 2) rfl) (Det.nat 1)
      (v := .list ((1 :: hs').map encPerm)) rfl))
    (mapConv_spec hmu unsq (1 :: hs') hconv)
  refine EvalAll.letE dM fun uv c3 hc3 => ?_
  obtain ⟨rfl, hc3⟩ := hc3
  have hu1 : (1 :: hs').map unsq = 1 :: hs'.map unsq := by simp [unsq_one]
  rw [hu1] at hc3 ⊢
  -- the reduction
  have dR := Det.call (Det.mk2 (Det.get' (Det.arg' (P := P) (vs := vs)
      (rest := (env3 ++ [Val.list ((1 :: hs'.map unsq).map encPerm)]).tail) (j := 0) rfl)
      (Det.nat 0) (v := .nat k) rfl)
    (Det.var' (P := P) (env := env3 ++ [Val.list ((1 :: hs'.map unsq).map encPerm)]) (i := 3) rfl))
    (reduce_spec hm hred hjm (hs'.map unsq))
  refine dR.post fun c4 hc4 => ⟨⟨keepList (hs'.map unsq), rfl, ?_, length_keepList_le _⟩, ?_⟩
  · rw [gens_keepList]; exact gens_map_unsq hs' hgs'
  · clear dM dR dA dA' dK dc hsq hconv hR hKmem hK hf hcls hker hjp hjm hmu hfu hbmt hfe hred
    have hk1 : 1 ≤ k + 1 := by omega
    have hkk6 : (k * k + 1) ^ 6 ≤ (k + 1) ^ 12 := by
      calc (k * k + 1) ^ 6 ≤ ((k + 1) ^ 2) ^ 6 := Nat.pow_le_pow_left (by nlinarith) 6
        _ = (k + 1) ^ 12 := by ring
    have p2 : (k + 1) ^ 2 ≤ (k + 1) ^ 6 := Nat.pow_le_pow_right hk1 (by norm_num)
    have p6 : (k + 1) ^ 6 ≤ (k + 1) ^ 12 := Nat.pow_le_pow_right hk1 (by norm_num)
    have p12 : (k + 1) ^ 12 ≤ (k + 1) ^ 16 := Nat.pow_le_pow_right hk1 (by norm_num)
    have wK := wt_encGroup_le_sq hlen'
    have wKin : (Val.list ((1 :: hs').map encPerm)).wt < (encGroup hs').wt :=
      wt_le_wt_list (vs := [.nat (k * k), .list ((1 :: hs').map encPerm)]) (by simp)
    have wout : (Val.list ((1 :: hs'.map unsq).map encPerm)).wt ≤
        ((k * k) ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) + 4 := by
      have h1 := wt_list_le_of ((1 :: hs'.map unsq).map encPerm) (c := 4 * (k + 1) ^ 2) (by
        intro v hv; obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv; exact wt_encPerm_le g)
      have hl : ((1 :: hs'.map unsq).map encPerm).length ≤ (k * k) ^ 2 + 1 := by simp; omega
      have h2 := Nat.mul_le_mul_right (2 * (4 * (k + 1) ^ 2) + 1) hl
      have e8 : 2 * (4 * (k + 1) ^ 2) + 1 = 8 * (k + 1) ^ 2 + 1 := by ring
      rw [e8] at h1 h2
      omega
    have wcK := wt_cK_le k
    have wi := wt_list2_le (cK k) (Val.list ((1 :: hs').map encPerm))
    have hmc := mapUnsq_cost_le ((1 :: hs').length) (by simp; omega)
      ((Val.list [cK k, Val.list ((1 :: hs').map encPerm)]).wt)
      ((Val.list ((1 :: hs'.map unsq).map encPerm)).wt)
      (aux_wi wi (wcK.trans (Nat.mul_le_mul_left _ (p2.trans p6))) wKin
        (wK.trans (Nat.mul_le_mul_left _ hkk6))) wout
    have wfin := wt_encGroup_le_sq (length_keepList_le (hs'.map unsq))
    have hrc := reduceCost_mono hm k (show (hs'.map unsq).length ≤ (k * k) ^ 2 by simpa using hlen')
    have hlen1 : (1 :: hs').length = hs'.length + 1 := rfl
    have hlen2 : (1 :: hs'.map unsq).length = hs'.length + 1 := by simp
    have e3 := wt_list3_le (Val.list vs) (clsVal (maskF Q E e) fun _ => 1) (encGroup hs')
    have e4 := wt_list4_le (Val.list vs) (clsVal (maskF Q E e) fun _ => 1) (encGroup hs')
      (Val.list ((1 :: hs'.map unsq).map encPerm))
    have wr := wt_list2_le (Val.nat k) (Val.list ((1 :: hs'.map unsq).map encPerm))
    have := wt_nat_le k
    have p16 : 1 ≤ (k + 1) ^ 16 := Nat.one_le_pow _ _ hk1
    have hy : ((k * k) ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) ≤ 9 * (k + 1) ^ 6 := by
      have e1 : (k * k) ^ 2 + 1 ≤ (k + 1) ^ 4 := by nlinarith [Nat.zero_le k]
      have : ((k * k) ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) ≤ (k + 1) ^ 4 * (9 * (k + 1) ^ 2) :=
        Nat.mul_le_mul e1 (by have := Nat.one_le_pow 2 (k + 1) hk1; omega)
      have e : (k + 1) ^ 4 * (9 * (k + 1) ^ 2) = 9 * (k + 1) ^ 6 := by ring
      omega
    have hWW4 : (W + 1) ^ 2 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hkW2 : (k + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    unfold pkerCost
    simp only [List.length_cons, List.length_map] at hc3 hc4 hmc hrc ⊢
    simp only [ecl] at *
    have eKg : (encGroup hs').wt = (Val.list [.nat (k * k), Val.list ((1 :: hs').map encPerm)]).wt :=
      rfl
    clear hlen' hgs' hhs hmask hS hb
    generalize encGroup (keepList (hs'.map unsq)) = Kf at *
    generalize Val.list ((1 :: hs'.map unsq).map encPerm) = Lout at *
    generalize Val.list ((1 :: hs').map encPerm) = Lin at *
    generalize encGroup hs' = Kg at *
    generalize (clsVal (maskF Q E e) fun _ => 1) = Cv at *
    generalize cK k = cv at *
    generalize Val.list vs = Av at *
    have wn := wt_list2_le (encFun (maskF Q E e)) (encFun fun _ : Fin (k * k) => 1)
    omega

end GI.Impl
