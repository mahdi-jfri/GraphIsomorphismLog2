module

public import Workspace.Impl.AggItemHvKer
public import Workspace.Impl.Combine
public import Workspace.Impl.AggCombExact

@[expose] public section

/-!
# Case 2a: first parts, twisted colors and the pieces

Three small programs of the halving item (Lemma A.11):

* `it_hvFst_spec`: the first parts of a list of graph pairs. The generators of `A` on positions
  are the first parts of graph pairs of `A` (`it_hvA_spec`, `mem_gens_fst`).
* `it_hvCol_spec`: the colors `y ∘ τ` from the colors of `y` and the positions of a lift `τ`
  (a gather).
* `it_hvPc_spec`: one piece from the two answers. If the transporter answer is empty, the piece is
  empty. Otherwise the answer is `x₁ ⟨gs₁⟩`, the answer for `x` is `x₀ ⟨gs₀⟩`, and the piece is
  `ρ x₁ ⟨gs₀, gA⟩` ("Combine the successful full cosets and undo the initial alignment"); see
  `it_hv_piece_some`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens)

variable {Ω C : Type} {k : ℕ}

/-! ### First parts -/

/-- The body of the map of first parts, on `[c, pairV p]`. -/
def itHvFstB : Expr := .get (arg 1) (.nat 0)

theorem itHv_fst_body {P : Program} {fb : ℕ} (hfb : P.funs[fb]? = some itHvFstB) {q : ℕ}
    (c : Val) (p : Perm (Fin k) × Perm (Fin q)) :
    FunDet P fb (.list [c, pairV p]) (encPerm p.1) (10 * (c.wt + (pairV p).wt + 10)) := by
  have g := Det.arg' (P := P) (vs := [c, pairV p]) (rest := []) (j := 1) rfl
  refine FunDet.intro hfb ((Det.get' g (Det.nat 0) (vs := [encPerm p.1, encPerm p.2]) rfl).mono ?_)
  have := wt_list2_le c (pairV p)
  have := wt_nat_le 0
  have := wt_nat_le 1
  have : (encPerm p.1).wt < (pairV p).wt := wt_le_wt_list (by simp)
  omega

/-- **The first parts of graph pairs**, by a map. -/
theorem it_hvFst_spec {P : Program} {mp fb : ℕ} (hmp : P.HasAt mp (mapFuns mp fb))
    (hfb : P.funs[fb]? = some itHvFstB) {q : ℕ} (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet P mp (.list [.nat 0, .list (ps.map pairV)]) (.list (ps.map fun p => encPerm p.1))
      (10 ^ 6 * pM k q ps ^ 4) := by
  have hm := mapList_spec hmp ps pairV (fun p => encPerm p.1) (c := .nat 0)
    (B := 10 * ((Val.nat 0).wt + 22 * (k + q + 1) ^ 2 + 10))
    (fun a _ a' _ h => by rw [it_pairV_injective h])
    (fun p _ => (itHv_fst_body hfb (.nat 0) p).mono (by have := wt_pairV_le p; omega))
  refine hm.mono ?_
  obtain ⟨M, hM⟩ : ∃ M, M = pM k q ps := ⟨_, rfl⟩
  rw [← hM]
  have hMd : k + q + ps.length + 2 = M := by rw [hM]; rfl
  have wps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := hM ▸ wt_pairList_le ps
  have wfs : (Val.list (ps.map fun p => encPerm p.1)).wt ≤ 50 * M ^ 3 := by
    have h := wt_list_map_le ps (fun p => encPerm p.1) (W := 4 * (k + 1) ^ 2)
      fun p _ => wt_encPerm_le p.1
    have h2 : (k + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h1M : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 : ps.length * (2 * (4 * (k + 1) ^ 2) + 1) ≤ M * (9 * M ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e3 : M * (9 * M ^ 2) = 9 * M ^ 3 := by ring
    have hM1 : 1 ≤ M := by omega
    have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
    have m12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have w0 := wt_nat_le 0
  have w2 := wt_list2_le (.nat 0) (.list (ps.map pairV))
  have hM1 : 1 ≤ M := by omega
  have m12 : M ≤ M ^ 2 := Nat.le_self_pow (by norm_num) _
  have m23 : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right hM1 (by omega)
  have m34 : M ^ 3 ≤ M ^ 4 := Nat.pow_le_pow_right hM1 (by omega)
  have hkq2 : (k + q + 1) ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have a1 : ps.length * (10 * ((Val.nat 0).wt + 22 * (k + q + 1) ^ 2 + 10)) ≤
      M * (500 * M ^ 2) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : M * (500 * M ^ 2) = 500 * M ^ 3 := by ring
  have a2 : (ps.length + 1) * ((Val.list [.nat 0, .list (ps.map pairV)]).wt +
      (Val.list (ps.map fun p => encPerm p.1)).wt + 1) ≤ M * (300 * M ^ 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : M * (300 * M ^ 3) = 300 * M ^ 4 := by ring
  have hmk : mapK = 1000 := rfl
  rw [hmk, Nat.mul_assoc]
  generalize ps.length * (10 * ((Val.nat 0).wt + 22 * (k + q + 1) ^ 2 + 10)) = A at *
  generalize (ps.length + 1) * ((Val.list [.nat 0, .list (ps.map pairV)]).wt +
      (Val.list (ps.map fun p => encPerm p.1)).wt + 1) = B at *
  generalize M * (500 * M ^ 2) = A' at *
  generalize M * (300 * M ^ 3) = B' at *
  omega

/-- **The generators of `A` on positions** are the first parts of graph pairs of `A`. -/
theorem it_hv_fst_gens {e : Ω ≃ Fin k} {S : State Ω C} {L : GiantLabels S}
    {A : Subgroup (Perm Ω)} (hA : A ≤ S.G) {ps : List (Perm (Fin k) × Perm (Fin L.q))}
    (hps : PairGens e L A ps) : gens (ps.map Prod.fst) = groupFin e A := by
  ext a
  rw [mem_gens_fst hps a]
  constructor
  · rintro ⟨g, -, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hA hg, hg, rfl⟩

/-! ### Twisted colors -/

/-- **The colors `y ∘ τ`** from the colors of `y` and the positions `toFin e τ`, by a gather. -/
theorem it_hvCol_spec {P : Program} {ga : ℕ} (hga : P.HasAt ga (gatherFuns ga)) {e : Ω ≃ Fin k}
    {c : C → ℕ} {y : Ω → C} {yv : Val} (hyv : ColorVal e c yv y) (a : Perm (Fin k)) :
    FunDet P ga (.list [yv, encPerm a]) (encFun fun i => c ((y ∘ (toFin e).symm a) (e.symm i)))
      (gatherK * ((Val.list [yv, encPerm a]).wt + 1) ^ 3) := by
  have hyv0 : yv = .list ((List.finRange k).map fun i => Val.nat (c (y (e.symm i)))) := hyv
  have hgt := gather_spec hga (L := (List.finRange k).map fun i => Val.nat (c (y (e.symm i))))
    (is := (List.finRange k).map fun i => (a i : ℕ)) (by simp)
  have htτ : toFin e ((toFin e).symm a) = a := MulEquiv.apply_symm_apply _ _
  have hgy : (((List.finRange k).map fun i => (a i : ℕ)).map fun j =>
      ((List.finRange k).map fun i => Val.nat (c (y (e.symm i)))).getD j (.nat 0)) =
      (List.finRange k).map fun i => Val.nat (c ((y ∘ (toFin e).symm a) (e.symm i))) := by
    conv_lhs => rw [← htτ]
    exact gather_colors e c y _
  rw [hgy, ← encPerm_eq_natList, ← hyv0] at hgt
  exact hgt

/-! ### One piece -/

/-- On `[ρ, u₀, u, gA]`: one piece. `u₀ = [x₀, ⟨gs₀⟩]` is the answer for `x`, `u` the answer for
the twisted target, `gA` the list of generators of `A`. -/
def itHvPcF (cmp app : ℕ) : Expr :=
  .ite (.length (arg 2))
    (mk2 (.call cmp (mk2 (arg 0) (.get (arg 2) (.nat 0))))
      (mk2 (.get (.get (.get (arg 1) (.nat 1)) (.nat 1)) (.nat 0))
        (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
          (.call app (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 1)) (arg 3))))))
    (mk2 (.get (.get (.get (arg 1) (.nat 1)) (.nat 1)) (.nat 0)) .nil)

/-- The cost bound of `itHvPcF` for inputs of weight at most `W`. -/
def itHvPcC (W : ℕ) : ℕ := 10 ^ 7 * (W + 1) ^ 3

theorem itHvPcC_mono {a b : ℕ} (h : a ≤ b) : itHvPcC a ≤ itHvPcC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

/-- The encoding of a group with more generators. -/
theorem itHv_encGroup_append (gs₀ gA : List (Perm (Fin k))) :
    encGroup (gs₀ ++ gA) = .list [.nat k, .list (((1 : Perm (Fin k)) :: gs₀).map encPerm ++
      gA.map encPerm)] := by
  simp [encGroup, GI.Cited.encPerms]

/-- An append, as a value with a cost bound for inputs of weight at most `W`. -/
theorem itHv_app_det {P : Program} {app : ℕ} (happ : P.HasAt app (appendFuns app))
    (xs ys : List Val) {W : ℕ} (hW : (Val.list [.list xs, .list ys]).wt ≤ W) :
    FunDet P app (.list [.list xs, .list ys]) (.list (xs ++ ys)) (10000 * (W + 1) ^ 2) := by
  refine (append_spec happ xs ys).mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  subst hw
  have h1 := wt_list_append_le xs ys
  have h2 := wt_le_wt_list (show Val.list xs ∈ [Val.list xs, .list ys] by simp)
  have h3 := wt_le_wt_list (show Val.list ys ∈ [Val.list xs, .list ys] by simp)
  have h4 := length_lt_wt_list ys
  have a1 : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      (Val.list (xs ++ ys)).wt + 1) ≤ 1000 * (W + 1) * (4 * (W + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : 1000 * (W + 1) * (4 * (W + 1)) = 4000 * (W + 1) ^ 2 := by ring
  omega

set_option maxHeartbeats 2000000 in
/-- **One piece as a program.** For the answer `u₀ = [x₀, ⟨gs₀⟩]` and an answer `u` that is
empty or `[x₁, ⟨gs₁⟩]`, the program returns `encPiece (1, none)` or
`encPiece (ρ x₁, some (1, gs₀ ++ gA))`. -/
theorem it_hvPc_spec {P : Program} {f cmp app : ℕ} (hf : P.funs[f]? = some (itHvPcF cmp app))
    (hcmp : P.HasAt cmp (composeFuns cmp)) (happ : P.HasAt app (appendFuns app))
    (ρ x₀ : Perm (Fin k)) (gs₀ gA : List (Perm (Fin k))) (u : Val)
    (hu : u = .list [] ∨ ∃ (x₁ : Perm (Fin k)) (gs₁ : List (Perm (Fin k))),
      u = .list [encPerm x₁, encGroup gs₁]) {W : ℕ}
    (hW : (Val.list [encPerm ρ, .list [encPerm x₀, encGroup gs₀], u,
      .list (gA.map encPerm)]).wt ≤ W) :
    ∃ p : Perm (Fin k) × Acc k, (u = .list [] ∧ p = ((1 : Perm (Fin k)), (none : Acc k)) ∨
        ∃ (x₁ : Perm (Fin k)) (gs₁ : List (Perm (Fin k))), u = .list [encPerm x₁, encGroup gs₁] ∧
          p = (ρ * x₁, some (1, gs₀ ++ gA))) ∧
      FunDet P f (.list [encPerm ρ, .list [encPerm x₀, encGroup gs₀], u,
        .list (gA.map encPerm)]) (encPiece p) (itHvPcC W) := by
  set inp := Val.list [encPerm ρ, .list [encPerm x₀, encGroup gs₀], u, .list (gA.map encPerm)]
    with hinp
  have wρ : (encPerm ρ).wt < inp.wt := wt_le_wt_list (by simp)
  have wu0 : (Val.list [encPerm x₀, encGroup gs₀]).wt < inp.wt := wt_le_wt_list (by simp)
  have wu : u.wt < inp.wt := wt_le_wt_list (by simp)
  have wgA : (Val.list (gA.map encPerm)).wt < inp.wt := wt_le_wt_list (by simp)
  have wg0 : (encGroup gs₀).wt < (Val.list [encPerm x₀, encGroup gs₀]).wt := wt_le_wt_list (by simp)
  have eg0 : encGroup gs₀ = .list [.nat k, .list (((1 : Perm (Fin k)) :: gs₀).map encPerm)] := rfl
  have wgl : (Val.list (((1 : Perm (Fin k)) :: gs₀).map encPerm)).wt < (encGroup gs₀).wt := by
    rw [eg0]; exact wt_le_wt_list (by simp)
  have wk : (Val.nat k).wt < (encGroup gs₀).wt := by rw [eg0]; exact wt_le_wt_list (by simp)
  have w1 : (encPerm (1 : Perm (Fin k))).wt <
      (Val.list (((1 : Perm (Fin k)) :: gs₀).map encPerm)).wt := wt_le_wt_list (by simp)
  have hkW : k < W := by
    have h := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (ρ i))
    simp only [List.length_map, List.length_finRange] at h
    have : encPerm ρ = .list ((List.finRange k).map fun i => Val.nat (ρ i)) := rfl
    rw [← this] at h
    omega
  have hgl1 := length_lt_wt_list (((1 : Perm (Fin k)) :: gs₀).map encPerm)
  simp only [List.length_map, List.length_cons] at hgl1
  obtain ⟨W2, hW2⟩ : ∃ W2, W2 = 200 * (W + 1) ^ 2 := ⟨_, rfl⟩
  have hW1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hWW : W ≤ W2 := by omega
  have hW4 : 4 ≤ W2 := by omega
  have hinW2 : inp.wt ≤ W2 := by omega
  have hp1 : ∀ σ : Perm (Fin k), (encPerm σ).wt ≤ 4 * (W + 1) ^ 2 := fun σ =>
    (wt_encPerm_le σ).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have ga : ∀ (j : ℕ) (v : Val), [encPerm ρ, .list [encPerm x₀, encGroup gs₀], u,
      .list (gA.map encPerm)][j]? = some v → j + 2 ≤ W2 → v.wt ≤ W2 →
      StDC P [inp] (arg j) v 3 0 W2 := fun j v hv hj hw =>
    (StDC.get (StDC.var' rfl hinW2) (StDC.nat j hj) hv hw).mono (by omega) le_rfl
  have dG : StDC P [inp] (.get (arg 1) (.nat 1)) (encGroup gs₀) 5 0 W2 :=
    StDC.get (ga 1 _ rfl (by omega) (by omega)) (StDC.nat 1 (by omega)) (v := encGroup gs₀) rfl
      (by omega)
  have dL : StDC P [inp] (.get (.get (arg 1) (.nat 1)) (.nat 1))
      (.list (((1 : Perm (Fin k)) :: gs₀).map encPerm)) 7 0 W2 :=
    StDC.get dG (StDC.nat 1 (by omega))
      (vs := [.nat k, .list (((1 : Perm (Fin k)) :: gs₀).map encPerm)]) rfl (by omega)
  have d1 : StDC P [inp] (.get (.get (.get (arg 1) (.nat 1)) (.nat 1)) (.nat 0))
      (encPerm (1 : Perm (Fin k))) 9 0 W2 :=
    StDC.get dL (StDC.nat 0 (by omega)) rfl (by omega)
  have dk : StDC P [inp] (.get (.get (arg 1) (.nat 1)) (.nat 0)) (.nat k) 7 0 W2 :=
    StDC.get dG (StDC.nat 0 (by omega))
      (vs := [.nat k, .list (((1 : Perm (Fin k)) :: gs₀).map encPerm)]) rfl (by omega)
  have hC : ∀ n E : ℕ, n ≤ 100 → E ≤ 600000 * (W + 1) ^ 3 → n * (W2 + 1) + E ≤ itHvPcC W := by
    intro n E hn hE
    have h3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have : n * (W2 + 1) ≤ 100 * (W2 + 1) := Nat.mul_le_mul_right _ hn
    unfold itHvPcC
    omega
  rcases hu with rfl | ⟨x₁, gs₁, rfl⟩
  · -- the empty answer
    refine ⟨(1, none), Or.inl ⟨rfl, rfl⟩, ?_⟩
    have dl := StDC.length (ga 2 (.list []) rfl (by omega) (by omega)) (vs := []) (by simp; omega)
    have hout : (encPiece ((1 : Perm (Fin k)), (none : Acc k))).wt ≤ W2 := by
      have := wt_list2_le (encPerm (1 : Perm (Fin k))) (.list [])
      have := hp1 1
      show (Val.list [encPerm 1, .list []]).wt ≤ W2
      rw [wt_list_nil] at *
      omega
    have d := itHv_ite0 (t := mk2 (.call cmp (mk2 (arg 0) (.get (arg 2) (.nat 0))))
      (mk2 (.get (.get (.get (arg 1) (.nat 1)) (.nat 1)) (.nat 0))
        (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
          (.call app (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 1)) (arg 3))))))
      dl (StDC.mk2 d1 (StDC.nil hW4) hout hW4) hout
    exact StDC.funDet hf d (hC _ _ (by omega) (by omega))
  · -- a nonempty answer
    refine ⟨(ρ * x₁, some (1, gs₀ ++ gA)), Or.inr ⟨x₁, gs₁, rfl, rfl⟩, ?_⟩
    set u := Val.list [encPerm x₁, encGroup gs₁]
    have wx1 : (encPerm x₁).wt < u.wt := wt_le_wt_list (by simp)
    have dl := StDC.length (ga 2 u rfl (by omega) (by omega)) (vs := [encPerm x₁, encGroup gs₁])
      (by simp; omega)
    have dx := StDC.get (ga 2 u rfl (by omega) (by omega)) (StDC.nat 0 (by omega))
      (vs := [encPerm x₁, encGroup gs₁]) (v := encPerm x₁) rfl (by omega)
    have w2c := wt_list2_le (encPerm ρ) (encPerm x₁)
    have dc := StDC.call (StDC.mk2 (ga 0 _ rfl (by omega) (by omega)) dx (by omega) hW4)
      (compose_spec hcmp ρ x₁) (by have := hp1 (ρ * x₁); omega)
    have wapp := wt_list2_le (.list (((1 : Perm (Fin k)) :: gs₀).map encPerm)) (.list (gA.map encPerm))
    have dA := StDC.call (StDC.mk2 dL (ga 3 _ rfl (by omega) (by omega)) (by omega) hW4)
      (itHv_app_det happ (((1 : Perm (Fin k)) :: gs₀).map encPerm) (gA.map encPerm) (W := 4 * W + 6)
        (by omega))
      (by have := wt_list_append_le (((1 : Perm (Fin k)) :: gs₀).map encPerm) (gA.map encPerm)
          omega)
    have wl := wt_list_append_le (((1 : Perm (Fin k)) :: gs₀).map encPerm) (gA.map encPerm)
    have wkG := wt_list2_le (.nat k) (.list (((1 : Perm (Fin k)) :: gs₀).map encPerm ++
      gA.map encPerm))
    have hG : (Val.list [.nat k, .list (((1 : Perm (Fin k)) :: gs₀).map encPerm ++
        gA.map encPerm)]).wt ≤ 8 * W + 6 := by omega
    have dg := StDC.mk2 dk dA (by omega) hW4
    have w3 := wt_list2_le (encPerm (1 : Perm (Fin k))) (.list [.nat k,
      .list (((1 : Perm (Fin k)) :: gs₀).map encPerm ++ gA.map encPerm)])
    have dacc := StDC.mk2 d1 dg (by omega) hW4
    have w4 := wt_list2_le (encPerm (ρ * x₁)) (.list [encPerm (1 : Perm (Fin k)), .list [.nat k,
      .list (((1 : Perm (Fin k)) :: gs₀).map encPerm ++ gA.map encPerm)]])
    have hp := hp1 (ρ * x₁)
    have hout : (Val.list [encPerm (ρ * x₁), .list [encPerm (1 : Perm (Fin k)), .list [.nat k,
        .list (((1 : Perm (Fin k)) :: gs₀).map encPerm ++ gA.map encPerm)]]]).wt ≤ W2 := by omega
    have d := itHv_ite1 dl (by simp) (StDC.mk2 dc dacc hout hW4) hout
      (e := mk2 (.get (.get (.get (arg 1) (.nat 1)) (.nat 1)) (.nat 0)) .nil)
    have epc : encPiece (ρ * x₁, some ((1 : Perm (Fin k)), gs₀ ++ gA)) =
        .list [encPerm (ρ * x₁), .list [encPerm (1 : Perm (Fin k)), .list [.nat k,
          .list (((1 : Perm (Fin k)) :: gs₀).map encPerm ++ gA.map encPerm)]]] := by
      simp [encPiece, encAcc, encGroup, GI.Cited.encPerms]
    rw [epc]
    refine StDC.funDet hf d (hC _ _ (by omega) ?_)
    have hpk : permK * (k + 1) ^ 3 ≤ 30000 * (W + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    have h23 : (4 * W + 6 + 1) ^ 2 ≤ 49 * (W + 1) ^ 3 := by
      have : (4 * W + 6 + 1) ^ 2 ≤ (7 * (W + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (7 * (W + 1)) ^ 2 = 49 * (W + 1) ^ 2 := by ring
      have h3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    omega

end GI.Impl
