import Workspace.Impl.MBlkMerge

/-!
# The closure under the generators, as a program

* `mblkPtF`: one point step `mblkPt g lab x`, on `[encPerm g, mlab lab, x]`.
* `mblkGenFuns`: a `foldl` of the point steps over the points, giving `mblkGen lab g`.
* `mblkRoundFuns`: a `foldl` of `mblkGen` over the generators, giving `mblkRound gs lab`.
* `mblkClosFuns`: `n` rounds, giving `mblkClos gs lab`.

The costs are polynomials in `n + 1` and in `S = (m + 1) (n + 1)` for `m` generators.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The list of the points, as a value. -/
abbrev mids (n : ℕ) : Val := encFun fun x : Fin n => (x : ℕ)

theorem wt_mids_le (n : ℕ) : (mids n).wt ≤ 4 * (n + 1) ^ 2 :=
  wt_encFun_le_sq _ fun x => x.isLt.le

/-! ### One point step -/

/-- On `[encPerm g, mlab lab, x]`: `mlab (mblkPt g lab x)`. -/
def mblkPtF (mm : ℕ) : Expr :=
  .letE (.get (arg 0) (arg 2))
    (.letE (.get (arg 0) (.get (arg 1) (arg 2)))
      (.call mm (mk2 (mk2 (.get (arg 1) (.var 1)) (.get (arg 1) (.var 2))) (arg 1))))

theorem mblkPt_spec {P : Program} {f mm : ℕ} (hf : P.funs[f]? = some (mblkPtF mm))
    (hm : P.HasAt mm (mblkMergeFuns mm)) (g : Perm (Fin n)) (lab : Fin n → Fin n) (x : Fin n) :
    FunDet P f (.list [encPerm g, mlab lab, .nat x]) (mlab (mblkPt g lab x))
      (200000 * (n + 1) ^ 3) := by
  set A := Val.list [encPerm g, mlab lab, .nat x] with hA
  have du := Det.applyPerm (P := P) (env := [A]) (σ := g) (i := x)
    (Det.arg' (rest := []) (vs := [encPerm g, mlab lab, .nat x]) (j := 0) rfl)
    (Det.arg' (j := 2) rfl)
  have dl := Det.get' (P := P) (env := [A, .nat (g x)])
    (Det.arg' (rest := [.nat (g x)]) (vs := [encPerm g, mlab lab, .nat x]) (j := 1) rfl)
    (Det.arg' (j := 2) rfl) (encFun_getElem? (fun y => (lab y : ℕ)) x)
  have dw := Det.applyPerm (P := P) (σ := g) (i := lab x)
    (Det.arg' (rest := [.nat (g x)]) (vs := [encPerm g, mlab lab, .nat x]) (j := 0) rfl) dl
  set E := [A, Val.nat (g x), Val.nat (g (lab x))] with hE
  have da := Det.get' (P := P) (env := E)
    (Det.arg' (rest := [.nat (g x), .nat (g (lab x))]) (vs := [encPerm g, mlab lab, .nat x])
      (j := 1) rfl) (Det.var' (i := 1) rfl) (encFun_getElem? (fun y => (lab y : ℕ)) (g x))
  have db := Det.get' (P := P) (env := E)
    (Det.arg' (rest := [.nat (g x), .nat (g (lab x))]) (vs := [encPerm g, mlab lab, .nat x])
      (j := 1) rfl) (Det.var' (i := 2) rfl)
    (encFun_getElem? (fun y => (lab y : ℕ)) (g (lab x)))
  have dL := Det.arg' (P := P) (rest := [.nat (g x), .nat (g (lab x))])
    (vs := [encPerm g, mlab lab, .nat x]) (j := 1) rfl
  have dc := Det.call (Det.mk2 (Det.mk2 da db) dL) (mblkMerge_spec hm lab (g x) (g (lab x)))
  refine FunDet.intro hf ((Det.letE du (Det.letE dw dc)).mono ?_)
  have h1 := wt_encPerm_le g
  have h2 := wt_mlab_le lab
  have h3 : (mlab (mblkMerge lab (g x) (g (lab x)))).wt ≤ 4 * (n + 1) ^ 2 := wt_mlab_le _
  have h4 := wt_nat_le x
  have h5 := wt_nat_le (g x)
  have h6 := wt_nat_le (g (lab x))
  have h7 := wt_nat_le (lab x)
  have h8 := wt_nat_le (lab (g x))
  have h9 := wt_nat_le (lab (g (lab x)))
  have h10 : A.wt ≤ 2 * ((encPerm g).wt + (mlab lab).wt + (Val.nat x).wt) + 7 := wt_list3_le _ _ _
  have h11 := wt_list2_le (.nat (lab (g x))) (.nat (lab (g (lab x))))
  have h12 := wt_list2_le (.list [.nat (lab (g x)), .nat (lab (g (lab x)))]) (mlab lab)
  have e1 : (Val.list [encPerm g, mlab lab, .nat x]).wt = A.wt := rfl
  have := x.isLt
  have := (g x).isLt
  have := (g (lab x)).isLt
  have := (lab x).isLt
  have := (lab (g x)).isLt
  have := (lab (g (lab x))).isLt
  have hN1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hN3 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ### The point steps of one generator -/

/-- `foldl mblkPtF` over the points, at base `b` (four functions): on
`[encPerm g, mids n, mlab lab]`, the value `mlab (mblkGen lab g)`. -/
def mblkGenFuns (b mm : ℕ) : List Expr := foldlFuns b (b + 3) ++ [mblkPtF mm]

theorem mblkGen_spec {P : Program} {b mm : ℕ} (h : P.HasAt b (mblkGenFuns b mm))
    (hm : P.HasAt mm (mblkMergeFuns mm)) (g : Perm (Fin n)) (lab : Fin n → Fin n) :
    FunDet P b (.list [encPerm g, mids n, mlab lab]) (mlab (mblkGen lab g))
      (300000 * (n + 1) ^ 4) := by
  have hf : P.funs[b + 3]? = some (mblkPtF mm) := by
    simpa [mblkGenFuns, foldlFuns, loopFuns] using h.right.single
  set xs := (List.finRange n).map fun i : Fin n => Val.nat (i : ℕ) with hxs
  have hlen : xs.length = n := by simp [hxs]
  have hF := foldl_spec h.left (c := encPerm g) (xs := xs) (acc0 := mlab lab)
    (Inv := fun i acc => acc = mlab (((List.finRange n).take i).foldl (mblkPt g) lab))
    (M := 4 * (n + 1) ^ 2) (B := fun _ => 200000 * (n + 1) ^ 3) (by simp)
    (fun i acc _ hacc => hacc ▸ wt_mlab_le _)
    (fun i acc hi hacc => by
      subst hacc
      have hi' : i < (List.finRange n).length := by simpa [hxs] using hi
      have e : xs[i] = Val.nat ((List.finRange n)[i] : ℕ) := by simp [hxs]
      rw [e]
      refine FunAll.mono (mblkPt_spec hf hm g _ (List.finRange n)[i]) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
        List.foldl_append]
      rfl)
  refine hF.mono fun w cost hw => ?_
  obtain ⟨hw1, hc⟩ := hw
  rw [hlen, List.take_of_length_le (by simp)] at hw1
  refine ⟨hw1, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hlen] at hc
  have h1 := wt_encPerm_le g
  have h2 := wt_mlab_le lab
  have h3 := wt_mids_le n
  have h4 := wt_list3_le (encPerm g) (.list xs) (mlab lab)
  have e1 : (Val.list xs).wt = (mids n).wt := rfl
  have hN1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h5 : loopModK * (n + 1) * ((Val.list [encPerm g, .list xs, mlab lab]).wt + n +
      4 * (n + 1) ^ 2 + 1) ≤ loopModK * (n + 1) * (40 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have e5 : loopModK * (n + 1) * (40 * (n + 1) ^ 2) = 40000 * (n + 1) ^ 3 := by
    simp only [loopModK]; ring
  have h6 : n * (200000 * (n + 1) ^ 3) ≤ 200000 * (n + 1) ^ 4 := by
    have : n * (n + 1) ^ 3 ≤ (n + 1) ^ 4 := by
      rw [pow_succ]; rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have e : n * (200000 * (n + 1) ^ 3) = 200000 * (n * (n + 1) ^ 3) := by ring
    omega
  have h7 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-! ### One round -/

/-- The step of the round's `foldl`: on `[mids n, mlab lab, encPerm g]`, `mlab (mblkGen lab g)`. -/
def mblkGenF (gf : ℕ) : Expr := .call gf (mk3 (arg 2) (arg 0) (arg 1))

theorem mblkGenF_spec {P : Program} {f gf mm : ℕ} (hf : P.funs[f]? = some (mblkGenF gf))
    (hg : P.HasAt gf (mblkGenFuns gf mm)) (hm : P.HasAt mm (mblkMergeFuns mm))
    (g : Perm (Fin n)) (lab : Fin n → Fin n) :
    FunDet P f (.list [mids n, mlab lab, encPerm g]) (mlab (mblkGen lab g))
      (400000 * (n + 1) ^ 4) := by
  have d := Det.call (P := P) (Det.mk3 (Det.arg' (rest := []) (vs := [mids n, mlab lab, encPerm g])
    (j := 2) rfl) (Det.arg' (j := 0) rfl) (Det.arg' (j := 1) rfl)) (mblkGen_spec hg hm g lab)
  refine FunDet.intro hf (d.mono ?_)
  have h1 := wt_encPerm_le g
  have h2 := wt_mlab_le lab
  have h3 := wt_mids_le n
  have h4 := wt_mlab_le (mblkGen lab g)
  have h5 := wt_list3_le (mids n) (mlab lab) (encPerm g)
  have h6 := wt_list3_le (encPerm g) (mids n) (mlab lab)
  have hN2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The round's `foldl`, at base `b` (four functions): on `[mids n, gens, mlab lab]`, the value
`mlab (mblkRound gs lab)`. -/
def mblkRoundFuns (b gf : ℕ) : List Expr := foldlFuns b (b + 3) ++ [mblkGenF gf]

theorem mblkRound_spec {P : Program} {b gf mm : ℕ} (h : P.HasAt b (mblkRoundFuns b gf))
    (hg : P.HasAt gf (mblkGenFuns gf mm)) (hm : P.HasAt mm (mblkMergeFuns mm))
    (gs : List (Perm (Fin n))) (lab : Fin n → Fin n) :
    FunDet P b (.list [mids n, .list (gs.map encPerm), mlab lab]) (mlab (mblkRound gs lab))
      (500000 * ((gs.length + 1) * (n + 1)) ^ 5) := by
  have hf : P.funs[b + 3]? = some (mblkGenF gf) := by
    simpa [mblkRoundFuns, foldlFuns, loopFuns] using h.right.single
  have hF := foldl_spec h.left (c := mids n) (xs := gs.map encPerm) (acc0 := mlab lab)
    (Inv := fun i acc => acc = mlab ((gs.take i).foldl mblkGen lab))
    (M := 4 * (n + 1) ^ 2) (B := fun _ => 400000 * (n + 1) ^ 4) (by simp)
    (fun i acc _ hacc => hacc ▸ wt_mlab_le _)
    (fun i acc hi hacc => by
      subst hacc
      have hi' : i < gs.length := by simpa using hi
      have e : (gs.map encPerm)[i] = encPerm gs[i] := List.getElem_map ..
      rw [e]
      refine FunAll.mono (mblkGenF_spec hf hg hm gs[i] _) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
        List.foldl_append]
      rfl)
  refine hF.mono fun w cost hw => ?_
  obtain ⟨hw1, hc⟩ := hw
  rw [List.length_map, List.take_length] at hw1
  refine ⟨hw1, ?_⟩
  simp only [List.length_map, Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
  have h1 := wt_list_encPerms_le gs
  have h2 := wt_mlab_le lab
  have h3 := wt_mids_le n
  have h4 := wt_list3_le (mids n) (.list (gs.map encPerm)) (mlab lab)
  generalize hS : (gs.length + 1) * (n + 1) = S at h1 ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hmS : gs.length + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_right _ (by omega)
  have hS1 : 1 ≤ S := le_trans (by omega) hNS
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have h5 : loopModK * (gs.length + 1) * ((Val.list [mids n, .list (gs.map encPerm),
      mlab lab]).wt + gs.length + 4 * (n + 1) ^ 2 + 1) ≤ loopModK * S * (60 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hmS) (by omega)
  have e5 : loopModK * S * (60 * S ^ 2) = 60000 * S ^ 3 := by simp only [loopModK]; ring
  have h6 : gs.length * (400000 * (n + 1) ^ 4) ≤ 400000 * S ^ 5 := by
    have : gs.length * (n + 1) ^ 4 ≤ S ^ 5 := by
      calc gs.length * (n + 1) ^ 4 ≤ S * S ^ 4 :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hNS 4)
        _ = S ^ 5 := by ring
    have e : gs.length * (400000 * (n + 1) ^ 4) = 400000 * (gs.length * (n + 1) ^ 4) := by ring
    omega
  have h7 : S ^ 3 ≤ S ^ 5 := Nat.pow_le_pow_right hS1 (by omega)
  omega

/-! ### The rounds -/

/-- The body of the iteration: on `[[mids n, gens], i, mlab lab]`, one round. -/
def mblkIterRoundF (rf : ℕ) : Expr :=
  .call rf (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 2))

theorem mblkIterRound_spec {P : Program} {f rf gf mm : ℕ} (hf : P.funs[f]? = some (mblkIterRoundF rf))
    (hr : P.HasAt rf (mblkRoundFuns rf gf)) (hg : P.HasAt gf (mblkGenFuns gf mm))
    (hm : P.HasAt mm (mblkMergeFuns mm)) (gs : List (Perm (Fin n))) (lab : Fin n → Fin n)
    {i : ℕ} (hi : i ≤ n) :
    FunDet P f (.list [.list [mids n, .list (gs.map encPerm)], .nat i, mlab lab])
      (mlab (mblkRound gs lab)) (600000 * ((gs.length + 1) * (n + 1)) ^ 5) := by
  set c := Val.list [mids n, .list (gs.map encPerm)] with hc
  have g0 := Det.get' (P := P) (Det.arg' (rest := []) (vs := [c, .nat i, mlab lab]) (j := 0) rfl)
    (Det.nat 0) (show [mids n, .list (gs.map encPerm)][0]? = some _ from rfl)
  have g1 := Det.get' (P := P) (Det.arg' (rest := []) (vs := [c, .nat i, mlab lab]) (j := 0) rfl)
    (Det.nat 1) (show [mids n, .list (gs.map encPerm)][1]? = some _ from rfl)
  have g2 := Det.arg' (P := P) (rest := []) (vs := [c, .nat i, mlab lab]) (j := 2) rfl
  refine FunDet.intro hf ((Det.call (Det.mk3 g0 g1 g2) (mblkRound_spec hr hg hm gs lab)).mono ?_)
  have h1 := wt_mlab_le lab
  have h2 := wt_mids_le n
  have h3 := wt_mlab_le (mblkRound gs lab)
  have h4 := wt_list_encPerms_le gs
  have h5 : c.wt ≤ 2 * ((mids n).wt + (Val.list (gs.map encPerm)).wt) + 6 := wt_list2_le _ _
  have h6 := wt_list3_le c (.nat i) (mlab lab)
  have h7 := wt_list3_le (mids n) (.list (gs.map encPerm)) (mlab lab)
  have h8 := wt_nat_le i
  generalize hS : (gs.length + 1) * (n + 1) = S at h4 ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hS1 : 1 ≤ S := le_trans (by omega) hNS
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS5 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS1 (by omega)
  omega

/-- `n` rounds, at base `b` (four functions): on `[[mids n, gens], n, mlab lab]`, the value
`mlab (mblkClos gs lab)`. -/
def mblkClosFuns (b rf : ℕ) : List Expr := iterFuns b (b + 3) ++ [mblkIterRoundF rf]

theorem mblkClos_spec {P : Program} {b rf gf mm : ℕ} (h : P.HasAt b (mblkClosFuns b rf))
    (hr : P.HasAt rf (mblkRoundFuns rf gf)) (hg : P.HasAt gf (mblkGenFuns gf mm))
    (hm : P.HasAt mm (mblkMergeFuns mm)) (gs : List (Perm (Fin n))) (lab : Fin n → Fin n) :
    FunDet P b (.list [.list [mids n, .list (gs.map encPerm)], .nat n, mlab lab])
      (mlab (mblkClos gs lab)) (800000 * ((gs.length + 1) * (n + 1)) ^ 6) := by
  have hf : P.funs[b + 3]? = some (mblkIterRoundF rf) := by
    simpa [mblkClosFuns, iterFuns, loopFuns] using h.right.single
  set c := Val.list [mids n, .list (gs.map encPerm)] with hc
  have hI := iter_spec h.left (c := c) (k := n) (acc0 := mlab lab)
    (Inv := fun i acc => acc = mlab ((mblkRound gs)^[i] lab))
    (M := 4 * (n + 1) ^ 2) (B := fun _ => 600000 * ((gs.length + 1) * (n + 1)) ^ 5) rfl
    (fun i acc _ hacc => hacc ▸ wt_mlab_le _)
    (fun i acc hi hacc => by
      subst hacc
      refine FunAll.mono (mblkIterRound_spec hf hr hg hm gs _ hi.le) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, Function.iterate_succ_apply'])
  refine hI.mono fun w cost hw => ⟨hw.1, ?_⟩
  have hc' := hw.2
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc'
  have h1 := wt_mlab_le lab
  have h2 := wt_mids_le n
  have h4 := wt_list_encPerms_le gs
  have h5 : c.wt ≤ 2 * ((mids n).wt + (Val.list (gs.map encPerm)).wt) + 6 := wt_list2_le _ _
  have h6 := wt_list3_le c (.nat n) (mlab lab)
  have h8 := wt_nat_le n
  generalize hS : (gs.length + 1) * (n + 1) = S at h4 hc' ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hS1 : 1 ≤ S := le_trans (by omega) hNS
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have h7 : loopModK * (n + 1) * ((Val.list [c, .nat n, mlab lab]).wt + n +
      4 * (n + 1) ^ 2 + 1) ≤ loopModK * S * (120 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hNS) (by omega)
  have e7 : loopModK * S * (120 * S ^ 2) = 120000 * S ^ 3 := by simp only [loopModK]; ring
  have h9 : n * (600000 * S ^ 5) ≤ 600000 * S ^ 6 := by
    have : n * S ^ 5 ≤ S ^ 6 := by
      rw [pow_succ, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have e : n * (600000 * S ^ 5) = 600000 * (n * S ^ 5) := by ring
    omega
  have h10 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by omega)
  omega

end GI.Impl
