/-
**Orbits with a transversal, for a general action.** `orbTFuns b fa` is a program of 22
functions at base `b`. It runs the algorithm of `Workspace.Lang.Lib.OrbitTMath` for a group
`G = ⟨gs⟩ ≤ Sym(n)` that acts on a type `X` through the language function at index `fa`.

* A point `y : X` is the value `natList (key y)`, for an injective `key : X → List ℕ` (a point of
  `Fin n` is `[i]`, a tuple is its list of entries, a permutation is `encPerm`).
* The action function `fa` sends `[ac, encPerm g, natList (key y)]` to `natList (key (g · y))`,
  for a context `ac` that the caller chooses (`OrbTHyp.hfa`).
* The input is `[ac, [encPerm g | g ∈ gs], natList (key x₀), B, n]`, and the result is the list
  of pairs `[natList (key y), encPerm t]` of `orbitPairs` (`orbT_spec`): when the orbit of `x₀`
  has at most `B` points, the points are the orbit, without repeats, and `t ∈ G`, `t · x₀ = y`.

The cost is at most `S² A + orbTK * S⁶`, where `A` bounds the cost of one call of the action and
`S` bounds `n + 1`, the number of generators plus one, `B + 1`, the weight of `ac`, and the weights
of the points of the orbit.
-/
module

public import Workspace.Lang.Lib.OrbitTMath
public import Workspace.Lang.Lib.Orbit

@[expose] public section

namespace GI.Lang

open GI.Machine (BinOp len len_le_self)
open GI.Cited (Val encPerm encPerms)
open Equiv

variable {n : ℕ} {X : Type} [DecidableEq X]

/-! ### Values -/

/-- A pair `(y, t)` as a value. -/
def encPair (key : X → List ℕ) (p : X × Perm (Fin n)) : Val :=
  .list [natList (key p.1), encPerm p.2]

/-- A list of pairs as a value. -/
def encPairs (key : X → List ℕ) (L : List (X × Perm (Fin n))) : Val :=
  .list (L.map (encPair key))

theorem natList_injective : Function.Injective natList := by
  intro a b h
  simp only [natList, Val.list.injEq] at h
  exact (List.map_injective_iff.mpr fun x y h => by simpa using h) h

theorem encPair_injective {key : X → List ℕ} (hk : Function.Injective key) :
    Function.Injective (encPair (n := n) key) := by
  rintro ⟨y, t⟩ ⟨z, u⟩ h
  simp only [encPair, Val.list.injEq, List.cons.injEq, and_true] at h
  rw [hk (natList_injective h.1), encPerm_injective h.2]

/-- The weight of a list whose entries weigh at most `c`. -/
theorem wt_list_le_of (vs : List Val) {c : ℕ} (h : ∀ v ∈ vs, v.wt ≤ c) :
    (Val.list vs).wt ≤ vs.length * (2 * c + 1) + 4 := by
  have h1 := wt_list_le vs
  have h2 := List.sum_le_card_nsmul (vs.map Val.wt) c (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ v hv rfl; exact h v hv)
  simp only [List.length_map, smul_eq_mul] at h2
  have : vs.length * (2 * c + 1) = 2 * (vs.length * c) + vs.length := by ring
  omega

/-! ### The functions -/

/-- The test of the search: on `[yv, [zv, t]]`, whether `yv = zv`. -/
def orbTestF (eq : ℕ) : Expr := .call eq (mk2 (arg 0) (.get (arg 1) (.nat 0)))

/-- The step of the inner `foldl`: on `[[a, [yv, t]], acc, g]`, the image `y' = g · y`; if `y'`
is not a point of `acc`, add `[y', g t]` to `acc`. -/
def orbInnerF (fa find comp : ℕ) : Expr :=
  .letE (.call fa (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 2)
      (.get (.get (arg 0) (.nat 1)) (.nat 0))))
    (.ite (.arith .lt (.call find (mk2 (.var 1) (arg 1))) (.length (arg 1)))
      (arg 1)
      (.snoc (arg 1) (mk2 (.var 1) (.call comp (mk2 (arg 2) (.get (.get (arg 0) (.nat 1))
        (.nat 1)))))))

/-- The step of the outer loop: on `[a, i, acc]`, if `i < |acc|`, fold the inner step over the
generators with the pair `acc[i]`. -/
def orbOuterF (fold : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.length (arg 2)))
    (.call fold (mk3 (mk2 (arg 0) (.get (arg 2) (arg 1))) (.get (arg 0) (.nat 1)) (arg 2)))
    (arg 2)

/-- The entry: on `[ac, gens, x₀v, B, n]`, run the loop on `[ac, gens, [[x₀v, 1]], B]`. -/
def orbTEntry (b rg : ℕ) : Expr :=
  .call (b + 1) (mk4 (arg 0) (arg 1) (mk1 (mk2 (arg 2) (.call rg (arg 4)))) (arg 3))

/-- **The orbit program with a transversal**, at base `b` (22 functions), with the action at
`fa`. -/
def orbTFuns (b fa : ℕ) : List Expr :=
  [orbTEntry b (b + 19)] ++
    loopFuns (b + 1) (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 2)) (orbOuterF (b + 4)) ++
    foldlFuns (b + 4) (b + 7) ++ [orbInnerF fa (b + 8) (b + 12)] ++ findFuns (b + 8) (b + 11) ++
    [orbTestF (b + 16)] ++ composeFuns (b + 12) ++ eqNatsFuns (b + 16) ++ rangeFuns (b + 19)

theorem length_orbTFuns (b fa : ℕ) : (orbTFuns b fa).length = 22 := by
  simp [orbTFuns, loopFuns, foldlFuns, findFuns, composeFuns, mapFuns, eqNatsFuns, rangeFuns]

/-! ### The hypotheses -/

/-- The hypotheses of the orbit program: an action, an injective key, and the bound `S` on
`n + 1`, the number of generators plus one, the weight of the context `ac` and the weights of the
points of the orbit; `A` bounds the cost of the action function `fa`. -/
structure OrbTHyp (P : Program) (fa : ℕ) (key : X → List ℕ) (act : Perm (Fin n) → X → X)
    (gs : List (Perm (Fin n))) (x₀ : X) (ac : Val) (S A : ℕ) : Prop where
  isAct : IsAct act
  key_inj : Function.Injective key
  hn : n + 1 ≤ S
  hm : gs.length + 1 ≤ S
  hac : ac.wt ≤ S
  hkey : ∀ y ∈ actOrbit act gs x₀, (natList (key y)).wt ≤ S
  hfa : ∀ g ∈ gs, ∀ y ∈ actOrbit act gs x₀,
    FunDet P fa (.list [ac, encPerm g, natList (key y)]) (natList (key (act g y))) A

/-- A pair of the orbit: `t ∈ G` and `t · x₀ = y`. -/
def OrbPair (act : Perm (Fin n) → X → X) (gs : List (Perm (Fin n))) (x₀ : X)
    (p : X × Perm (Fin n)) : Prop := p.2 ∈ genGroup gs ∧ act p.2 x₀ = p.1

theorem OrbPair.mem {act : Perm (Fin n) → X → X} {gs : List (Perm (Fin n))} {x₀ : X}
    {p : X × Perm (Fin n)} (h : OrbPair act gs x₀ p) : p.1 ∈ actOrbit act gs x₀ :=
  ⟨p.2, h.1, h.2⟩

theorem act_mem_orbit {act : Perm (Fin n) → X → X} (hact : IsAct act)
    {gs : List (Perm (Fin n))} {x₀ y : X} (hy : y ∈ actOrbit act gs x₀) {g : Perm (Fin n)}
    (hg : g ∈ gs) : act g y ∈ actOrbit act gs x₀ := by
  obtain ⟨h, hh, rfl⟩ := hy
  exact ⟨g * h, (genGroup gs).mul_mem (Subgroup.subset_closure hg) hh, hact.mul g h x₀⟩

section weights

variable {P : Program} {fa : ℕ} {key : X → List ℕ} {act : Perm (Fin n) → X → X}
  {gs : List (Perm (Fin n))} {x₀ : X} {ac : Val} {S A : ℕ}

theorem OrbTHyp.one_le (H : OrbTHyp P fa key act gs x₀ ac S A) : 1 ≤ S := by
  have := H.hn; omega

theorem OrbTHyp.wt_perm (H : OrbTHyp P fa key act gs x₀ ac S A) (t : Perm (Fin n)) :
    (encPerm t).wt ≤ 4 * S ^ 2 :=
  (wt_encPerm_le t).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left H.hn 2))

theorem OrbTHyp.wt_pair (H : OrbTHyp P fa key act gs x₀ ac S A) {p : X × Perm (Fin n)}
    (hp : OrbPair act gs x₀ p) : (encPair key p).wt ≤ 16 * S ^ 2 := by
  have h1 := wt_list2_le (natList (key p.1)) (encPerm p.2)
  have h2 := H.hkey _ hp.mem
  have h3 := H.wt_perm p.2
  have h4 := H.one_le
  have h5 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have h6 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold encPair
  omega

/-- A good list of pairs is short, and its value weighs at most `40 S³`. -/
theorem OrbTHyp.wt_pairs (H : OrbTHyp P fa key act gs x₀ ac S A) {B : ℕ} (hBS : B + 1 ≤ S)
    (hB : (actOrbit act gs x₀).ncard ≤ B) {L : List (X × Perm (Fin n))}
    (hL : Good act gs x₀ L) : L.length + 1 ≤ S ∧ (encPairs key L).wt ≤ 40 * S ^ 3 := by
  have hlen : L.length ≤ B := hL.length_le.trans hB
  refine ⟨by omega, ?_⟩
  have h1 := wt_list_le_of (L.map (encPair key)) (c := 16 * S ^ 2) (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ p hp rfl; exact H.wt_pair (hL.2 p hp))
  simp only [List.length_map] at h1
  have h2 : L.length * (2 * (16 * S ^ 2) + 1) ≤ S * (33 * S ^ 2) :=
    Nat.mul_le_mul (by omega) (by have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ H.one_le; omega)
  have e : S * (33 * S ^ 2) = 33 * S ^ 3 := by ring
  have h3 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ H.one_le
  unfold encPairs
  omega

theorem OrbTHyp.wt_gens (H : OrbTHyp P fa key act gs x₀ ac S A) :
    (Val.list (gs.map encPerm)).wt ≤ 15 * S ^ 3 := by
  have h1 := wt_list_le_of (gs.map encPerm) (c := 4 * S ^ 2) (by
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ g _ rfl; exact H.wt_perm g)
  simp only [List.length_map] at h1
  have h2 : gs.length * (2 * (4 * S ^ 2) + 1) ≤ S * (9 * S ^ 2) :=
    Nat.mul_le_mul (by have := H.hm; omega)
      (by have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ H.one_le; omega)
  have e : S * (9 * S ^ 2) = 9 * S ^ 3 := by ring
  have h3 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ H.one_le
  omega

end weights

/-! ### The test -/

theorem orbTest_spec {P : Program} {f eq : ℕ} (hf : P.funs[f]? = some (orbTestF eq))
    (heq : P.HasAt eq (eqNatsFuns eq)) (key : X → List ℕ) {S : ℕ} (hS : 1 ≤ S) (y : X)
    (p : X × Perm (Fin n)) (hy : (natList (key y)).wt ≤ S) (hp1 : (natList (key p.1)).wt ≤ S)
    (hp : (encPair key p).wt ≤ 16 * S ^ 2) :
    FunDet P f (.list [natList (key y), encPair key p]) (boolVal (decide (key y = key p.1)))
      (100000 * S ^ 2) := by
  have d0 := Det.arg' (P := P) (vs := [natList (key y), encPair key p]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [natList (key y), encPair key p]) (rest := []) (j := 1) rfl
  have dk := Det.get' d1 (Det.nat 0)
    (show [natList (key p.1), encPerm p.2][0]? = some (natList (key p.1)) from rfl)
  refine FunDet.intro hf ((Det.call (Det.mk2 d0 dk) (eqNats_spec heq (key y) (key p.1))).mono ?_)
  have hl : (key y).length < (natList (key y)).wt := by
    have := length_lt_wt_list ((key y).map Val.nat); simpa [natList] using this
  have w1 := wt_list2_le (natList (key y)) (encPair key p)
  have w2 := wt_list2_le (natList (key y)) (natList (key p.1))
  have w3 := wt_boolVal_le (decide (key y = key p.1))
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1 : loopModK * ((key y).length + 1) *
      ((Val.list [natList (key y), natList (key p.1)]).wt + (key y).length + 4) ≤
      loopModK * S * (15 * S) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : loopModK * S * (15 * S) = 15000 * S ^ 2 := by simp only [loopModK]; ring
  omega

/-! ### The search -/

open Classical in
/-- The test of the search for `y`, on values: a pair whose point has the key of `y`. -/
noncomputable def pairTest (n : ℕ) (key : X → List ℕ) (y : X) (v : Val) : Bool :=
  decide (∃ p : X × Perm (Fin n), v = encPair key p ∧ key y = key p.1)

open Classical in
theorem pairTest_encPair {key : X → List ℕ} (hk : Function.Injective key) (y : X)
    (p : X × Perm (Fin n)) : pairTest n key y (encPair key p) = decide (p.1 = y) := by
  unfold pairTest
  refine Bool.decide_congr ⟨fun ⟨p', h1, h2⟩ => ?_, fun h => ⟨p, rfl, by rw [h]⟩⟩
  rw [encPair_injective hk h1]; exact (hk h2).symm

theorem findIdx_map_pairTest {key : X → List ℕ} (hk : Function.Injective key) (y : X)
    (L : List (X × Perm (Fin n))) :
    (L.map (encPair key)).findIdx (pairTest n key y) = L.findIdx (fun q => decide (q.1 = y)) := by
  induction L with
  | nil => rfl
  | cons p L ih => simp only [List.map_cons, List.findIdx_cons, pairTest_encPair hk, ih]

/-- **The search** for the point `y` in a good list `L`: the position of the first pair with
point `y`, or `|L|`. -/
theorem orbFind_spec {P : Program} {fd eq : ℕ} (hfd : P.HasAt fd (findFuns fd (fd + 3)))
    (ht : P.funs[fd + 3]? = some (orbTestF eq)) (heq : P.HasAt eq (eqNatsFuns eq))
    {fa : ℕ} {key : X → List ℕ} {act : Perm (Fin n) → X → X} {gs : List (Perm (Fin n))}
    {x₀ : X} {ac : Val} {S A B : ℕ} (H : OrbTHyp P fa key act gs x₀ ac S A) (hBS : B + 1 ≤ S)
    (hB : (actOrbit act gs x₀).ncard ≤ B) {L : List (X × Perm (Fin n))}
    (hL : Good act gs x₀ L) {y : X} (hy : y ∈ actOrbit act gs x₀) :
    FunDet P fd (.list [natList (key y), encPairs key L])
      (.nat (L.findIdx (fun q => decide (q.1 = y)))) (200000 * S ^ 4) := by
  have hS := H.one_le
  obtain ⟨hlen, hwL⟩ := H.wt_pairs hBS hB hL
  have hF := find_spec hfd (c := natList (key y)) (xs := L.map (encPair key))
    (q := pairTest n key y) (B := fun _ => 100000 * S ^ 2) (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      have hpo : OrbPair act gs x₀ p := hL.2 p hp
      have := orbTest_spec ht heq key hS y p (H.hkey y hy) (H.hkey _ hpo.mem) (H.wt_pair hpo)
      rw [pairTest_encPair H.key_inj]
      have e : decide (key y = key p.1) = decide (p.1 = y) :=
        Bool.decide_congr ⟨fun h => (H.key_inj h).symm, fun h => h ▸ rfl⟩
      rw [e] at this
      exact this)
  refine hF.mono fun w cost hw => ⟨by rw [hw.1, findIdx_map_pairTest H.key_inj], ?_⟩
  have hc := hw.2
  rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
  have e1 : (Val.list [natList (key y), .list (L.map (encPair key))]).wt =
    (Val.list [natList (key y), encPairs key L]).wt := rfl
  rw [e1] at hc
  have w1 := wt_list2_le (natList (key y)) (encPairs key L)
  have w2 := H.hkey y hy
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have h1 : L.length * (100000 * S ^ 2) ≤ S * (100000 * S ^ 2) := Nat.mul_le_mul_right _ (by omega)
  have h2 : loopModK * (L.length + 1) * ((Val.list [natList (key y), encPairs key L]).wt +
      2 * L.length + 3) ≤ loopModK * S * (95 * S ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : S * (100000 * S ^ 2) = 100000 * S ^ 3 := by ring
  have e3 : loopModK * S * (95 * S ^ 3) = 95000 * S ^ 4 := by simp only [loopModK]; ring
  omega

/-! ### The inner step -/

theorem addImg_val {key : X → List ℕ} (act : Perm (Fin n) → X → X) (p : X × Perm (Fin n))
    (L : List (X × Perm (Fin n))) (g : Perm (Fin n)) :
    (if BinOp.eval .lt (L.findIdx (fun q => decide (q.1 = act g p.1)))
      (L.map (encPair key)).length = 0 then
      Val.list (L.map (encPair key) ++ [.list [natList (key (act g p.1)), encPerm (g * p.2)]])
      else encPairs key L) = encPairs key (addImg act p L g) := by
  unfold addImg
  simp only [BinOp.eval, List.length_map]
  by_cases h : L.findIdx (fun q => decide (q.1 = act g p.1)) < L.length
  · simp [h]
  · simp [h, encPairs, encPair]

/-- **The inner step** adds the image of the pair `p` under the generator `g`. -/
theorem orbInner_spec {P : Program} {f fa fd eq cp : ℕ}
    (hf : P.funs[f]? = some (orbInnerF fa fd cp)) (hfd : P.HasAt fd (findFuns fd (fd + 3)))
    (ht : P.funs[fd + 3]? = some (orbTestF eq)) (heq : P.HasAt eq (eqNatsFuns eq))
    (hcp : P.HasAt cp (composeFuns cp))
    {key : X → List ℕ} {act : Perm (Fin n) → X → X} {gs : List (Perm (Fin n))}
    {x₀ : X} {ac : Val} {S A B : ℕ} (H : OrbTHyp P fa key act gs x₀ ac S A) (hBS : B + 1 ≤ S)
    (hB : (actOrbit act gs x₀).ncard ≤ B) {rest : List Val}
    (ha : (Val.list (ac :: rest)).wt ≤ 200 * S ^ 3) {p : X × Perm (Fin n)}
    (hp : OrbPair act gs x₀ p) {L : List (X × Perm (Fin n))} (hL : Good act gs x₀ L)
    {g : Perm (Fin n)} (hg : g ∈ gs) :
    FunDet P f (.list [.list [.list (ac :: rest), encPair key p], encPairs key L, encPerm g])
      (encPairs key (addImg act p L g)) (A + 1000000 * S ^ 4) := by
  have hS := H.one_le
  have hy : act g p.1 ∈ actOrbit act gs x₀ := act_mem_orbit H.isAct hp.mem hg
  have hyp : OrbPair act gs x₀ (act g p.1, g * p.2) :=
    ⟨(genGroup gs).mul_mem (Subgroup.subset_closure hg) hp.1, by
      simp only; rw [H.isAct.mul, hp.2]⟩
  obtain ⟨hlen, hwL⟩ := H.wt_pairs hBS hB hL
  set a := Val.list (ac :: rest) with ha_def
  set vs : List Val := [.list [a, encPair key p], encPairs key L, encPerm g] with hvs
  -- the call of the action
  have dC := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have dA := Det.get' dC (Det.nat 0) (show [a, encPair key p][0]? = some a from rfl)
  have dAc := Det.get' dA (Det.nat 0) (show (ac :: rest)[0]? = some ac from rfl)
  have dG := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have dPv := Det.get' dC (Det.nat 1)
    (show [a, encPair key p][1]? = some (.list [natList (key p.1), encPerm p.2]) from rfl)
  have dK := Det.get' dPv (Det.nat 0)
    (show [natList (key p.1), encPerm p.2][0]? = some (natList (key p.1)) from rfl)
  have dAct := Det.call (Det.mk3 dAc dG dK) (H.hfa g hg p.1 hp.mem)
  -- the search
  have e1 : ∀ r : List Val, Det P (.list vs :: r) (arg 1) (.list (L.map (encPair key)))
      (2 * (Val.list vs).wt + 1 + 5) := fun r => Det.arg' (j := 1) rfl
  have dFind := Det.call (Det.mk2 (Det.var' (P := P) (env := [.list vs, natList (key (act g p.1))])
    (i := 1) rfl) (e1 _)) (orbFind_spec hfd ht heq H hBS hB hL hy)
  have dLen := Det.length (e1 [natList (key (act g p.1))])
  have dCmp := Det.arith (op := .lt) dFind dLen
  -- the new pair
  have dT := Det.get' (Det.get' (Det.arg' (P := P) (vs := vs)
    (rest := [natList (key (act g p.1))]) (j := 0) rfl) (Det.nat 1)
    (show [a, encPair key p][1]? = some (.list [natList (key p.1), encPerm p.2]) from rfl))
    (Det.nat 1) (show [natList (key p.1), encPerm p.2][1]? = some (encPerm p.2) from rfl)
  have dComp := Det.call (Det.mk2 (Det.arg' (P := P) (vs := vs)
    (rest := [natList (key (act g p.1))]) (j := 2) rfl) dT) (compose_spec hcp g p.2)
  have dElse := Det.snoc (e1 [natList (key (act g p.1))])
    (Det.mk2 (Det.var' (P := P) (env := [.list vs, natList (key (act g p.1))]) (i := 1) rfl) dComp)
  have dIte := Det.ite' dCmp (Det.arg' (P := P) (vs := vs) (rest := [natList (key (act g p.1))])
    (j := 1) rfl) dElse
  have dAll := Det.letE dAct dIte
  rw [addImg_val (key := key) act p L g] at dAll
  refine FunDet.intro hf (dAll.mono ?_)
  clear dAll dIte dElse dComp dT dCmp dLen dFind e1 dAct dK dPv dG dAc dA dC
  -- weights
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have wP := H.wt_pair hp
  have wP' : (Val.list [natList (key p.1), encPerm p.2]).wt = (encPair key p).wt := rfl
  have wY := H.wt_pair hyp
  have wY' : (Val.list [natList (key (act g p.1)), encPerm (g * p.2)]).wt =
    (encPair key (act g p.1, g * p.2)).wt := rfl
  have wk1 := H.hkey _ hp.mem
  have wk2 := H.hkey _ hy
  have wg := H.wt_perm g
  have wt2 := H.wt_perm p.2
  have wgt := H.wt_perm (g * p.2)
  have wac := H.hac
  have wc := wt_list2_le a (encPair key p)
  have wv : (Val.list vs).wt ≤ 2 * ((Val.list [a, encPair key p]).wt + (encPairs key L).wt +
      (encPerm g).wt) + 7 := wt_list3_le _ _ _
  have w3 := wt_list3_le ac (encPerm g) (natList (key p.1))
  have wF := wt_list2_le (natList (key (act g p.1))) (encPairs key L)
  have wF' : (Val.list [natList (key (act g p.1)), Val.list (List.map (encPair key) L)]).wt =
    (Val.list [natList (key (act g p.1)), encPairs key L]).wt := rfl
  have wI : L.findIdx (fun q => decide (q.1 = act g p.1)) ≤ L.length := List.findIdx_le_length
  have wI' := wt_nat_le (L.findIdx (fun q => decide (q.1 = act g p.1)))
  have wB : (Val.nat (BinOp.eval .lt (L.findIdx (fun q => decide (q.1 = act g p.1)))
      L.length)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have wGT := wt_list2_le (encPerm g) (encPerm p.2)
  have wN := wt_list2_le (natList (key (act g p.1))) (encPerm (g * p.2))
  have wS := wt_list_snoc_le (L.map (encPair key))
    (.list [natList (key (act g p.1)), encPerm (g * p.2)])
  have wS' : (Val.list (L.map (encPair key))).wt = (encPairs key L).wt := rfl
  have wR := (H.wt_pairs hBS hB (good_addImg H.isAct hL hp hg)).2
  have hperm : permK * (n + 1) ^ 3 ≤ 30000 * S ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left H.hn 3)
  rw [List.length_map]
  generalize (Val.list vs).wt = W at *
  omega

/-! ### The fold over the generators and the outer step -/

/-- The program pieces that the outer step uses, at their indices. -/
structure OrbOuterAt (P : Program) (fb fa : ℕ) : Prop where
  fold : P.HasAt fb (foldlFuns fb (fb + 3))
  inner : P.funs[fb + 3]? = some (orbInnerF fa (fb + 4) (fb + 8))
  find : P.HasAt (fb + 4) (findFuns (fb + 4) (fb + 7))
  test : P.funs[fb + 7]? = some (orbTestF (fb + 12))
  comp : P.HasAt (fb + 8) (composeFuns (fb + 8))
  eq : P.HasAt (fb + 12) (eqNatsFuns (fb + 12))

theorem take_succ_foldl {α β : Type} (f : β → α → β) (l : List α) (b : β) (r : ℕ)
    (hr : r < l.length) : (l.take (r + 1)).foldl f b = f ((l.take r).foldl f b) l[r] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hr, Option.toList_some, List.foldl_append]
  rfl

/-- **The fold** of the inner step over the generators, with the pair `p`. -/
theorem orbFold_spec {P : Program} {fb fa : ℕ} (hP : OrbOuterAt P fb fa)
    {key : X → List ℕ} {act : Perm (Fin n) → X → X} {gs : List (Perm (Fin n))}
    {x₀ : X} {ac : Val} {S A B : ℕ} (H : OrbTHyp P fa key act gs x₀ ac S A) (hBS : B + 1 ≤ S)
    (hB : (actOrbit act gs x₀).ncard ≤ B) {rest : List Val}
    (ha : (Val.list (ac :: rest)).wt ≤ 200 * S ^ 3) {p : X × Perm (Fin n)}
    (hp : OrbPair act gs x₀ p) {L : List (X × Perm (Fin n))} (hL : Good act gs x₀ L) :
    FunDet P fb (.list [.list [.list (ac :: rest), encPair key p], .list (gs.map encPerm),
      encPairs key L]) (encPairs key (gs.foldl (addImg act p) L))
      (S * A + 3000000 * S ^ 5) := by
  have hS := H.one_le
  have hgood : ∀ r, Good act gs x₀ ((gs.take r).foldl (addImg act p) L) := fun r =>
    good_foldl_addImg H.isAct hp _ (fun g hg => List.mem_of_mem_take hg) hL
  have hF := foldl_spec hP.fold (c := .list [.list (ac :: rest), encPair key p])
    (xs := gs.map encPerm) (acc0 := encPairs key L)
    (Inv := fun r acc => acc = encPairs key ((gs.take r).foldl (addImg act p) L))
    (M := 40 * S ^ 3) (B := fun _ => A + 1000000 * S ^ 4) (by simp)
    (fun r acc _ h => h ▸ (H.wt_pairs hBS hB (hgood r)).2) (by
      rintro r acc hr rfl
      rw [List.length_map] at hr
      have hgr : gs[r] ∈ gs := List.getElem_mem hr
      have := orbInner_spec hP.inner hP.find hP.test hP.eq hP.comp H hBS hB ha hp (hgood r) hgr
      rw [← take_succ_foldl (addImg act p) gs L r hr] at this
      simp only [List.getElem_map]
      exact this)
  refine hF.mono fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, List.length_map, List.take_length]
  · have hc := hw.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map] at hc
    have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
    have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
    have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
    have p4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by norm_num)
    have hm := H.hm
    have wc := wt_list2_le (.list (ac :: rest)) (encPair key p)
    have wp := H.wt_pair hp
    have wg := H.wt_gens
    have wL := (H.wt_pairs hBS hB hL).2
    have w3 := wt_list3_le (.list [.list (ac :: rest), encPair key p]) (.list (gs.map encPerm))
      (encPairs key L)
    have h1 : gs.length * (A + 1000000 * S ^ 4) ≤ S * A + S * (1000000 * S ^ 4) :=
      calc gs.length * (A + 1000000 * S ^ 4) ≤ S * (A + 1000000 * S ^ 4) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = S * A + S * (1000000 * S ^ 4) := Nat.mul_add _ _ _
    have h2 : loopModK * (gs.length + 1) * ((Val.list [.list [.list (ac :: rest), encPair key p],
        .list (gs.map encPerm), encPairs key L]).wt + gs.length + 40 * S ^ 3 + 1) ≤
        loopModK * S * (1100 * S ^ 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hm) (by omega)
    have e1 : S * (1000000 * S ^ 4) = 1000000 * S ^ 5 := by ring
    have e2 : loopModK * S * (1100 * S ^ 3) = 1100000 * S ^ 4 := by simp only [loopModK]; ring
    omega

/-- **The outer step** `i`: process the pair `L[i]`, if there is one. -/
theorem orbOuter_det {P : Program} {fb fa : ℕ} (hP : OrbOuterAt P fb fa)
    {key : X → List ℕ} {act : Perm (Fin n) → X → X} {gs : List (Perm (Fin n))}
    {x₀ : X} {ac : Val} {S A B : ℕ} (H : OrbTHyp P fa key act gs x₀ ac S A) (hBS : B + 1 ≤ S)
    (hB : (actOrbit act gs x₀).ncard ≤ B) {rest : List Val}
    (ha : (Val.list (ac :: .list (gs.map encPerm) :: rest)).wt ≤ 200 * S ^ 3)
    {L : List (X × Perm (Fin n))} (hL : Good act gs x₀ L) {i : ℕ} (hiS : i + 1 ≤ S) :
    Det P [.list [.list (ac :: .list (gs.map encPerm) :: rest), .nat i, encPairs key L]]
      (orbOuterF fb) (encPairs key (procStep act gs L i)) (S * A + 4000000 * S ^ 5) := by
  have hS := H.one_le
  set a := Val.list (ac :: .list (gs.map encPerm) :: rest) with ha_def
  set vs : List Val := [a, .nat i, encPairs key L] with hvs
  have e1 : ∀ r : List Val, Det P (.list vs :: r) (arg 2) (.list (L.map (encPair key)))
      (2 * (Val.list vs).wt + 2 + 5) := fun r => Det.arg' (j := 2) rfl
  have dCmp := Det.arith (op := .lt) (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl)
    (Det.length (e1 []))
  have wvs : (Val.list vs).wt ≤ 2 * (a.wt + (Val.nat i).wt + (encPairs key L).wt) + 7 :=
    wt_list3_le _ _ _
  have wL := (H.wt_pairs hBS hB hL).2
  have wR := (H.wt_pairs hBS hB (good_procStep H.isAct hL i)).2
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have p4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by norm_num)
  have wB : (Val.nat (BinOp.eval .lt i (L.map (encPair key)).length)).wt ≤ 3 := by
    simp only [BinOp.eval]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have wa : a.wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have wLv : (encPairs key L).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have wi := wt_nat_le i
  have wg : (Val.list (gs.map encPerm)).wt < a.wt := wt_le_wt_list (by simp)
  have hlen := (H.wt_pairs hBS hB hL).1
  refine (Det.ite dCmp (ct := S * A + 3000000 * S ^ 5 + 100 * (Val.list vs).wt + 40 * S ^ 3 + 200)
    (ce := 2 * (Val.list vs).wt + 7) (v := encPairs key (procStep act gs L i)) (fun hx => ?_)
    (fun hx => ?_)).mono ?_
  · have hi : i < L.length := by
      simp only [BinOp.eval, List.length_map] at hx; split_ifs at hx with h; exact h; exact absurd rfl hx
    have hp : OrbPair act gs x₀ L[i] := hL.2 _ (List.getElem_mem hi)
    have dP := Det.get' (e1 []) (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl)
      (show (L.map (encPair key))[i]? = some (encPair key L[i]) by simp [hi])
    have dA := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
    have dG := Det.get' dA (Det.nat 1)
      (show (ac :: .list (gs.map encPerm) :: rest)[1]? = some (.list (gs.map encPerm)) from rfl)
    have dArg := Det.mk3 (Det.mk2 dA dP) dG (Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl)
    have hfold := orbFold_spec hP H hBS hB (rest := .list (gs.map encPerm) :: rest) ha hp hL
    have dCall := Det.call dArg hfold
    have e : gs.foldl (addImg act L[i]) L = procStep act gs L i := by
      unfold procStep; rw [dif_pos hi]
    rw [e] at dCall
    refine dCall.mono ?_
    clear dCall hfold dArg dG dA dP e1 dCmp
    have wp : (encPair key L[i]).wt < (encPairs key L).wt :=
      wt_le_wt_list (List.mem_map_of_mem (List.getElem_mem hi))
    have w2 := wt_list2_le a (encPair key L[i])
    have w3 := wt_list3_le (.list [a, encPair key L[i]]) (.list (gs.map encPerm)) (encPairs key L)
    omega
  · have hi : ¬ i < L.length := fun h => by simp [BinOp.eval, h] at hx
    have e : procStep act gs L i = L := by unfold procStep; rw [dif_neg hi]
    rw [e]
    exact Det.arg' (j := 2) rfl
  · have hl := length_lt_wt_list (L.map (encPair key))
    have hl' : (Val.list (L.map (encPair key))).wt = (encPairs key L).wt := rfl
    simp only [List.length_map] at hl wB ⊢
    omega

/-! ### The loop and the entry -/

/-- The constant of the cost bound of the orbit program. -/
def orbTK : ℕ := 10000000

theorem orbitPairs_good {act : Perm (Fin n) → X → X} (hact : IsAct act)
    (gs : List (Perm (Fin n))) (x₀ : X) (i : ℕ) : Good act gs x₀ (orbitPairs act gs x₀ i) :=
  (orbitPairs_inv hact gs x₀ i).1

/-- **The loop** of the orbit program, on `[ac, gens, [[x₀v, 1]], B]`. -/
theorem orbLoop_spec {P : Program} {b fa : ℕ}
    (hl : P.HasAt (b + 1)
      (loopFuns (b + 1) (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 2)) (orbOuterF (b + 4))))
    (hP : OrbOuterAt P (b + 4) fa)
    {key : X → List ℕ} {act : Perm (Fin n) → X → X} {gs : List (Perm (Fin n))}
    {x₀ : X} {ac : Val} {S A B : ℕ} (H : OrbTHyp P fa key act gs x₀ ac S A) (hBS : B + 1 ≤ S)
    (hB : (actOrbit act gs x₀).ncard ≤ B) :
    FunDet P (b + 1) (.list [ac, .list (gs.map encPerm), encPairs key [(x₀, (1 : Perm (Fin n)))], .nat B])
      (encPairs key (orbitPairs act gs x₀ B)) (S ^ 2 * A + 5000000 * S ^ 6) := by
  have hS := H.one_le
  have wa := wt_list4_le ac (.list (gs.map encPerm)) (encPairs key [(x₀, (1 : Perm (Fin n)))]) (.nat B)
  set a := Val.list [ac, .list (gs.map encPerm), encPairs key [(x₀, (1 : Perm (Fin n)))], .nat B] with ha_def
  have w0 := (H.wt_pairs hBS hB (orbitPairs_good H.isAct gs x₀ 0)).2
  have w0' : encPairs key (orbitPairs act gs x₀ 0) = encPairs key [(x₀, (1 : Perm (Fin n)))] := rfl
  rw [w0'] at w0
  have wB := wt_nat_le B
  have wg := H.wt_gens
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have p4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by norm_num)
  have p5 : S ^ 5 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by norm_num)
  have hac := H.hac
  have haS : a.wt ≤ 200 * S ^ 3 := by omega
  have hk := Det.get' (P := P) (Det.var' (env := [a]) (i := 0) rfl) (Det.nat 3)
    (show [ac, .list (gs.map encPerm), encPairs key [(x₀, (1 : Perm (Fin n)))], .nat B][3]? = some (.nat B) from rfl)
  have hacc := Det.get' (P := P) (Det.var' (env := [a]) (i := 0) rfl) (Det.nat 2)
    (show [ac, .list (gs.map encPerm), encPairs key [(x₀, (1 : Perm (Fin n)))], .nat B][2]? =
      some (encPairs key [(x₀, (1 : Perm (Fin n)))]) from rfl)
  have har : (Val.list [ac, .list (gs.map encPerm), encPairs key [(x₀, (1 : Perm (Fin n)))],
    .nat B]).wt = a.wt := rfl
  have hBa : (Val.nat B).wt < a.wt := wt_le_wt_list (by simp)
  have h0a : (encPairs key [(x₀, (1 : Perm (Fin n)))]).wt < a.wt := wt_le_wt_list (by simp)
  have h2 := a.two_le_size
  have h3 := a.size_le_wt
  have hL := loopBdd_spec hl hk hacc (by omega) (M := 40 * S ^ 3)
    (Inv := fun i acc => acc = encPairs key (orbitPairs act gs x₀ i))
    (D := fun _ => S * A + 4000000 * S ^ 5) rfl
    (fun i acc _ h => h ▸ (H.wt_pairs hBS hB (orbitPairs_good H.isAct gs x₀ i)).2) (by
      rintro i acc hi rfl
      refine (orbOuter_det hP H hBS hB (rest := [encPairs key [(x₀, (1 : Perm (Fin n)))], .nat B]) haS
        (orbitPairs_good H.isAct gs x₀ i) (i := i) (by omega)).post fun c hc => ⟨?_, ?_⟩
      · show _ = _; rw [orbitPairs_succ]
      · beta_reduce; omega)
  refine hL.mono fun w cost hw => ⟨hw.1, ?_⟩
  have hc := hw.2
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
  have h1 : B * (S * A + 4000000 * S ^ 5) ≤ S ^ 2 * A + 4000000 * S ^ 6 :=
    calc B * (S * A + 4000000 * S ^ 5) ≤ S * (S * A + 4000000 * S ^ 5) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = S ^ 2 * A + 4000000 * S ^ 6 := by ring
  have h4 : loopModK * (B + 1) * (a.wt + B + 40 * S ^ 3 + 1) ≤ loopModK * S * (300 * S ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hBS) (by omega)
  have e : loopModK * S * (300 * S ^ 3) = 300000 * S ^ 4 := by simp only [loopModK]; ring
  omega

/-- The pieces of the orbit program, at their indices. -/
theorem OrbTAt.pieces {P : Program} {b fa : ℕ} (h : P.HasAt b (orbTFuns b fa)) :
    P.funs[b]? = some (orbTEntry b (b + 19)) ∧
    P.HasAt (b + 1)
      (loopFuns (b + 1) (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 2)) (orbOuterF (b + 4))) ∧
    OrbOuterAt P (b + 4) fa ∧ P.HasAt (b + 19) (rangeFuns (b + 19)) := by
  simp only [orbTFuns] at h
  refine ⟨h.left.left.left.left.left.left.left.left.single, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using h.left.left.left.left.left.left.left.right
  · simpa [loopFuns, Nat.add_assoc] using h.left.left.left.left.left.left.right
  · simpa [loopFuns, foldlFuns, Nat.add_assoc] using h.left.left.left.left.left.right.single
  · simpa [loopFuns, foldlFuns, Nat.add_assoc] using h.left.left.left.left.right
  · simpa [loopFuns, foldlFuns, findFuns, Nat.add_assoc] using h.left.left.left.right.single
  · simpa [loopFuns, foldlFuns, findFuns, Nat.add_assoc] using h.left.left.right
  · simpa [loopFuns, foldlFuns, findFuns, composeFuns, mapFuns, Nat.add_assoc] using h.left.right
  · simpa [loopFuns, foldlFuns, findFuns, composeFuns, mapFuns, eqNatsFuns, Nat.add_assoc]
      using h.right

/-- **The orbit program computes the list of pairs** `orbitPairs act gs x₀ B`, at cost at most
`S² A + orbTK * S⁶`. -/
theorem orbT_det {P : Program} {b fa : ℕ} (h : P.HasAt b (orbTFuns b fa))
    {key : X → List ℕ} {act : Perm (Fin n) → X → X} {gs : List (Perm (Fin n))}
    {x₀ : X} {ac : Val} {S A B : ℕ} (H : OrbTHyp P fa key act gs x₀ ac S A) (hBS : B + 1 ≤ S)
    (hB : (actOrbit act gs x₀).ncard ≤ B) :
    FunDet P b (.list [ac, .list (gs.map encPerm), natList (key x₀), .nat B, .nat n])
      (encPairs key (orbitPairs act gs x₀ B)) (S ^ 2 * A + orbTK * S ^ 6) := by
  obtain ⟨he, hl, hP, hr⟩ := OrbTAt.pieces h
  have hS := H.one_le
  set vs : List Val := [ac, .list (gs.map encPerm), natList (key x₀), .nat B, .nat n] with hvs
  have hR : FunDet P (b + 19) (.nat n) (encPerm (1 : Perm (Fin n))) (8000 * S ^ 3) := by
    refine (range_spec hr n).mono fun w c hw => ⟨by rw [hw.1, range_eq_encPerm_one], ?_⟩
    have hc := hw.2
    rw [hw.1, range_eq_encPerm_one] at hc
    have w1 := wt_encPerm_le (1 : Perm (Fin n))
    have w2 := wt_nat_le n
    have h1 : loopModK * (n + 1) * ((Val.nat n).wt + n + (encPerm (1 : Perm (Fin n))).wt + 1) ≤
        loopModK * S * (8 * S ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ H.hn)
        (by
          have := Nat.pow_le_pow_left H.hn 2
          have := H.hn
          have : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
          omega)
    have e : loopModK * S * (8 * S ^ 2) = 8000 * S ^ 3 := by simp only [loopModK]; ring
    omega
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have d3 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 3) rfl
  have d4 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 4) rfl
  have dI := Det.mk1 (Det.mk2 d2 (Det.call d4 hR))
  have dArg := Det.mk4 d0 d1 dI d3
  have e0 : Val.list [Val.list [natList (key x₀), encPerm (1 : Perm (Fin n))]] =
    encPairs key [(x₀, (1 : Perm (Fin n)))] := rfl
  rw [e0] at dArg
  have dAll := Det.call dArg (orbLoop_spec hl hP H hBS hB)
  refine FunDet.intro he (dAll.mono ?_)
  clear dAll dArg dI d0 d1 d2 d3 d4 hR
  have p1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have p2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by norm_num)
  have p3 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
  have p4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS (by norm_num)
  have p5 : S ^ 5 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by norm_num)
  have wv := wt_list_le vs
  have wsum : (vs.map Val.wt).sum = ac.wt + (Val.list (gs.map encPerm)).wt +
      (natList (key x₀)).wt + (Val.nat B).wt + (Val.nat n).wt := by
    simp only [hvs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring
  have wlen : vs.length = 5 := rfl
  have hx₀ : x₀ ∈ actOrbit act gs x₀ := ⟨1, (genGroup gs).one_mem, H.isAct.one x₀⟩
  have wk := H.hkey x₀ hx₀
  have wg := H.wt_gens
  have wB := wt_nat_le B
  have wn := wt_nat_le n
  have hac := H.hac
  have hn := H.hn
  have w1 := H.wt_perm (1 : Perm (Fin n))
  have w2 := wt_list2_le (natList (key x₀)) (encPerm (1 : Perm (Fin n)))
  have w3 := wt_list1_le (Val.list [natList (key x₀), encPerm (1 : Perm (Fin n))])
  have w4 := wt_list4_le ac (.list (gs.map encPerm)) (encPairs key [(x₀, (1 : Perm (Fin n)))])
    (.nat B)
  have w4' : (encPairs key [(x₀, (1 : Perm (Fin n)))]).wt =
    (Val.list [Val.list [natList (key x₀), encPerm (1 : Perm (Fin n))]]).wt := rfl
  have wR := (H.wt_pairs hBS hB (orbitPairs_good H.isAct gs x₀ B)).2
  simp only [orbTK]
  omega

/-- **Orbits with a transversal, for a general action.** When the orbit of `x₀` has at most `B`
points, the result is the value of a list `L` of pairs `(y, t)` whose points are exactly the
orbit of `x₀`, without repeats, with `t ∈ ⟨gs⟩` and `t · x₀ = y`; the first pair is `(x₀, 1)`.
The cost is at most `S² A + orbTK * S⁶`. -/
theorem orbT_spec {P : Program} {b fa : ℕ} (h : P.HasAt b (orbTFuns b fa))
    {key : X → List ℕ} {act : Perm (Fin n) → X → X} {gs : List (Perm (Fin n))}
    {x₀ : X} {ac : Val} {S A B : ℕ} (H : OrbTHyp P fa key act gs x₀ ac S A) (hBS : B + 1 ≤ S)
    (hB : (actOrbit act gs x₀).ncard ≤ B) :
    FunAll P b (.list [ac, .list (gs.map encPerm), natList (key x₀), .nat B, .nat n])
      (fun w cost => ∃ L : List (X × Perm (Fin n)), w = encPairs key L ∧
        (L.map Prod.fst).Nodup ∧ (∀ y, y ∈ L.map Prod.fst ↔ y ∈ actOrbit act gs x₀) ∧
        (∀ p ∈ L, p.2 ∈ genGroup gs ∧ act p.2 x₀ = p.1) ∧ L.head? = some (x₀, 1) ∧
        cost ≤ S ^ 2 * A + orbTK * S ^ 6) := by
  refine FunAll.mono (orbT_det h H hBS hB) fun w cost hw => ?_
  obtain ⟨hg, hmem, hpre⟩ := orbitPairs_spec H.isAct gs x₀ hB
  refine ⟨_, hw.1, hg.1, hmem, hg.2, ?_, hw.2⟩
  obtain ⟨t, ht⟩ := hpre
  rw [← ht]; rfl

end GI.Lang
