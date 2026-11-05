module

public import Workspace.Impl.TermJProgLabs
public import Workspace.Impl.Reduce

@[expose] public section

/-!
# The answer `[t₀, ⟨t₀⁻¹ t_h, Aut_J⟩]` (program)

`tmJOutF`, on `[⟨t_h⟩, ⟨Aut_J gens⟩, n]` with the label transporters `t₀ :: ts`, returns
`[t₀, red(⟨t₀⁻¹ t | t ∈ t₀ :: ts⟩ ++ Aut_J gens)]` (`tmJ_alg`: the piece is
`t₀ ⟨t₀⁻¹ t_{h₀ u}, Aut_J(X)⟩`). The reduction (`red_spec`, one PointwiseStab call with no
points) brings the generator list to at most `n²` elements, as `AnsC` asks.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens PointwiseStab)

/-- On `[⟨t₀ :: ts⟩, ⟨aj⟩, n]`. -/
def tmJOutF (iv mpC app mk rd : ℕ) : Expr :=
  .letE (.call iv (.get (arg 0) (.nat 0)))
  (.letE (.call mk (mk2 (arg 2) (.call app (mk2 (.call mpC (mk2 (.var 1) (arg 0))) (arg 1)))))
  (.letE (.call rd (mk2 (arg 2) (.var 2)))
  (mk2 (.get (arg 0) (.nat 0)) (.var 3))))

/-- Where the pieces of `tmJOutF` sit. -/
structure TmJOutAt (P : Program) (f iv mpC cp app mk rd j : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJOutF iv mpC app mk rd)
  hiv : P.HasAt iv (invFuns iv)
  hmpC : P.HasAt mpC (mapFuns mpC cp)
  hcp : P.HasAt cp (composeFuns cp)
  happ : P.HasAt app (appendFuns app)
  hmk : P.HasAt mk (mkGroupFuns mk)
  hrd : P.HasAt rd (redFuns rd j)

/-- The bound of `tmJOutF`. -/
def tmJOutK (p : Prim) (W : ℕ) : ℕ :=
  1000 * (W + invK * (W + 1) ^ 4 + permK * (W + 1) ^ 3 + 13 * (W + 1) ^ 3 +
    (W * (permK * (W + 1) ^ 3) + mapK * (W + 1) * (2 * (4 * (W + 1) ^ 2 + W) + 7 +
      13 * (W + 1) ^ 3)) +
    6 * loopModK * (2 * (13 * (W + 1) ^ 3 + W) + 7) ^ 2 +
    mkGroupK * ((2 * W + 2) * (W + 1)) ^ 3 +
    (p.boundSize (2 * (mkGroupK * ((2 * W + 2) * (W + 1)) ^ 3) + 14) +
      20 * (mkGroupK * ((2 * W + 2) * (W + 1)) ^ 3) + 10 ^ 7 * (W + 1) ^ 9) + 100)

theorem tmJOutK_poly (p : Prim) : TmJPoly (tmJOutK p) := by
  have hW : TmJPoly fun W => W := TmJPoly.id
  have h1 : TmJPoly fun W => W + 1 := TmJPoly.add hW (TmJPoly.const 1)
  have hc : TmJPoly fun W => permK * (W + 1) ^ 3 := TmJPoly.smul _ (TmJPoly.pow h1 3)
  have ho : TmJPoly fun W => 13 * (W + 1) ^ 3 := TmJPoly.smul _ (TmJPoly.pow h1 3)
  have hmk : TmJPoly fun W => mkGroupK * ((2 * W + 2) * (W + 1)) ^ 3 :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.mul (TmJPoly.add (TmJPoly.smul 2 hW)
      (TmJPoly.const 2)) h1) 3)
  unfold tmJOutK Prim.boundSize
  refine TmJPoly.smul _ (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add
    (TmJPoly.add (TmJPoly.add (TmJPoly.add hW (TmJPoly.smul _ (TmJPoly.pow h1 4))) hc) ho)
    ?_) ?_) hmk) ?_) (TmJPoly.const 100))
  · exact TmJPoly.add (TmJPoly.mul hW hc) (TmJPoly.mul (TmJPoly.smul _ h1)
      (TmJPoly.add (TmJPoly.add (TmJPoly.smul 2 (TmJPoly.add (TmJPoly.smul 4
        (TmJPoly.pow h1 2)) hW)) (TmJPoly.const 7)) ho))
  · exact TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.smul 2 (TmJPoly.add ho hW))
      (TmJPoly.const 7)) 2)
  · exact TmJPoly.add (TmJPoly.add (TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.add
      (TmJPoly.smul 2 hmk) (TmJPoly.const 14)) (TmJPoly.const 2)) _)) (TmJPoly.smul 20 hmk))
      (TmJPoly.smul _ (TmJPoly.pow h1 9))

private theorem tmJOu_lt_wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : n < (encPerm σ).wt := by
  have h := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simp only [List.length_map, List.length_finRange] at h
  exact h

/-- The weight of a list of permutations of `Fin n`, `n < W`, of length at most `W`. -/
theorem tmJ_wt_perms_le {n W : ℕ} (l : List (Perm (Fin n))) (hn : n < W) (hl : l.length ≤ W) :
    (Val.list (l.map encPerm)).wt ≤ 13 * (W + 1) ^ 3 := by
  have := wt_list_le (l.map encPerm)
  have hs : ((l.map encPerm).map Val.wt).sum ≤ l.length * (4 * (n + 1) ^ 2) := by
    rw [List.map_map]
    refine (List.sum_le_card_nsmul _ (4 * (n + 1) ^ 2) fun x hx => ?_).trans (by simp)
    obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hx
    exact wt_encPerm_le σ
  simp only [List.length_map] at this
  have h2 : 4 * (n + 1) ^ 2 ≤ 4 * (W + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have h3 : l.length * (4 * (W + 1) ^ 2) ≤ W * (4 * (W + 1) ^ 2) := Nat.mul_le_mul_right _ hl
  have h4 : W * (4 * (W + 1) ^ 2) ≤ 4 * (W + 1) ^ 3 := by rw [pow_succ]; nlinarith
  have h5 := Nat.mul_le_mul_left l.length h2
  have h6 : W + 1 ≤ (W + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

/-- **The answer from the label transporters and the `Aut_J` generators.** -/
theorem tmJ_out_spec (hst : PointwiseStab) {P : Program} {f iv mpC cp app mk rd j : ℕ}
    (hA : TmJOutAt P f iv mpC cp app mk rd j) (hj : P.prims[j]? = some (pointwiseStabPrim hst))
    {n : ℕ} (t0 : Perm (Fin n)) (ts aj : List (Perm (Fin n))) :
    FunAll P f (.list [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm), .nat n])
      (fun out cost => (∃ hs : List (Perm (Fin n)), out = .list [encPerm t0, encGroup hs] ∧
          gens hs = gens ((t0 :: ts).map (t0⁻¹ * ·) ++ aj) ∧ hs.length ≤ n ^ 2) ∧
        cost ≤ tmJOutK (pointwiseStabPrim hst)
          (Val.list [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm), .nat n]).wt) := by
  refine FunAll.intro hA.hf ?_
  unfold tmJOutF
  obtain ⟨W, hW⟩ : ∃ W, (Val.list [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm),
      .nat n]).wt = W := ⟨_, rfl⟩
  rw [hW]
  have w0 : (Val.list ((t0 :: ts).map encPerm)).wt < W := hW ▸ wt_le_wt_list (by simp)
  have w1 : (Val.list (aj.map encPerm)).wt < W := hW ▸ wt_le_wt_list (by simp)
  have w2 : (Val.nat n).wt < W := hW ▸ wt_le_wt_list (by simp)
  have wt0 : (encPerm t0).wt < (Val.list ((t0 :: ts).map encPerm)).wt := wt_le_wt_list (by simp)
  have hn : n < W := by have := tmJOu_lt_wt t0; omega
  have l0 : (t0 :: ts).length < W := by
    have := length_lt_wt_list ((t0 :: ts).map encPerm); simp only [List.length_map] at this
    omega
  have l1 : aj.length < W := by
    have := length_lt_wt_list (aj.map encPerm); simp only [List.length_map] at this; omega
  -- the bounds
  obtain ⟨Bi, hBi⟩ : ∃ Bi, invK * (W + 1) ^ 4 = Bi := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc, permK * (W + 1) ^ 3 = Bc := ⟨_, rfl⟩
  obtain ⟨O1, hO1⟩ : ∃ O1, 13 * (W + 1) ^ 3 = O1 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1, W * Bc + mapK * (W + 1) * (2 * (4 * (W + 1) ^ 2 + W) + 7 + O1) = C1 :=
    ⟨_, rfl⟩
  obtain ⟨Ap, hAp⟩ : ∃ Ap, 6 * loopModK * (2 * (O1 + W) + 7) ^ 2 = Ap := ⟨_, rfl⟩
  obtain ⟨Mk, hMk⟩ : ∃ Mk, mkGroupK * ((2 * W + 2) * (W + 1)) ^ 3 = Mk := ⟨_, rfl⟩
  obtain ⟨Rd, hRd⟩ : ∃ Rd, (pointwiseStabPrim hst).boundSize (2 * Mk + 14) + 20 * Mk +
      10 ^ 7 * (W + 1) ^ 9 = Rd := ⟨_, rfl⟩
  obtain ⟨Sb, hSb⟩ : ∃ Sb, W + Bi + Bc + O1 + C1 + Ap + Mk + Rd + 100 = Sb := ⟨_, rfl⟩
  have hK : tmJOutK (pointwiseStabPrim hst) W = 1000 * Sb := by
    unfold tmJOutK; rw [← hSb, ← hRd, ← hMk, ← hAp, ← hC1, ← hO1, ← hBc, ← hBi]
  rw [hK]
  -- step 1: `t₀⁻¹`
  have a0 := Det.arg' (P := P) (vs := [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm),
    .nat n]) (rest := []) (j := 0) (v := .list ((t0 :: ts).map encPerm)) rfl
  have g0 := Det.get' a0 (Det.nat 0) (v := encPerm t0) rfl
  have hiK : invK * (n + 1) ^ 4 ≤ Bi := by
    rw [← hBi]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have dI := inv_spec hA.hiv t0
  have wI := FunDet.wt_lt dI
  have c1 := (Det.call g0 dI).mono (c' := 20 * Sb) (by rw [hW]; omega)
  refine (tmJ_letDet (C := 150 * Sb) c1 ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  -- step 2: the generators `t₀⁻¹ t` and `aj`, as a group value
  have hC : ∀ x ∈ (t0 :: ts).map encPerm, FunAll P cp (.list [encPerm t0⁻¹, x]) (fun w c =>
      (∀ u, x = encPerm u → w = encPerm (t0⁻¹ * u)) ∧ c ≤ permK * (n + 1) ^ 3) := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
    exact FunAll.mono (compose_spec hA.hcp t0⁻¹ u) fun w c h => ⟨fun u' hu' => by
      rw [encPerm_injective hu'] at h; exact h.1, h.2⟩
  have dC := map_spec hA.hmpC hC
  have wmap := tmJ_wt_perms_le ((t0 :: ts).map (t0⁻¹ * ·)) hn (by simp only [List.length_map]; omega)
  rw [hO1] at wmap
  have dC' : FunDet P mpC (.list [encPerm t0⁻¹, .list ((t0 :: ts).map encPerm)])
      (.list (((t0 :: ts).map (t0⁻¹ * ·)).map encPerm)) C1 := by
    refine dC.mono fun w c h => ?_
    obtain ⟨ws, rfl, hws, hc⟩ := h
    have hws' : ws = ((t0 :: ts).map (t0⁻¹ * ·)).map encPerm := by
      rw [List.forall₂_map_left_iff] at hws
      have := tmJ_forall₂_eq_map (fun u => encPerm (t0⁻¹ * u)) (hws.imp fun u w h => h u rfl)
      rw [this, List.map_map]; rfl
    subst hws'
    refine ⟨rfl, hc.trans ?_⟩
    have hsum : (((t0 :: ts).map encPerm).map fun _ => permK * (n + 1) ^ 3).sum ≤ W * Bc := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map, ← hBc]
      exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
    have hin : (Val.list [encPerm t0⁻¹, Val.list ((t0 :: ts).map encPerm)]).wt ≤
        2 * (4 * (W + 1) ^ 2 + W) + 6 := by
      have := wt_list2_le (encPerm t0⁻¹) (Val.list ((t0 :: ts).map encPerm))
      have := wt_encPerm_le t0⁻¹
      have : (n + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    rw [← hC1]
    simp only [List.length_map]
    have : mapK * ((t0 :: ts).length + 1) *
        ((Val.list [encPerm t0⁻¹, Val.list ((t0 :: ts).map encPerm)]).wt +
          (Val.list (((t0 :: ts).map (t0⁻¹ * ·)).map encPerm)).wt + 1) ≤
        mapK * (W + 1) * (2 * (4 * (W + 1) ^ 2 + W) + 7 + O1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega
  obtain ⟨L, hL⟩ : ∃ L, (t0 :: ts).map (t0⁻¹ * ·) ++ aj = L := ⟨_, rfl⟩
  have hLe : ((t0 :: ts).map (t0⁻¹ * ·)).map encPerm ++ aj.map encPerm = L.map encPerm := by
    rw [← hL, List.map_append]
  have hLl : L.length ≤ 2 * W := by
    rw [← hL, List.length_append, List.length_map]; omega
  have v1 := Det.var' (P := P) (env := [Val.list [.list ((t0 :: ts).map encPerm),
    .list (aj.map encPerm), .nat n], encPerm t0⁻¹]) (i := 1) (v := encPerm t0⁻¹) rfl
  have b0 := Det.arg' (P := P) (vs := [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm),
    .nat n]) (rest := [encPerm t0⁻¹]) (j := 0) (v := .list ((t0 :: ts).map encPerm)) rfl
  have b1 := Det.arg' (P := P) (vs := [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm),
    .nat n]) (rest := [encPerm t0⁻¹]) (j := 1) (v := .list (aj.map encPerm)) rfl
  have b2 := Det.arg' (P := P) (vs := [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm),
    .nat n]) (rest := [encPerm t0⁻¹]) (j := 2) (v := .nat n) rfl
  have cm := Det.call (Det.mk2 v1 b0) dC'
  have dAp := tmJ_app_det hA.happ (((t0 :: ts).map (t0⁻¹ * ·)).map encPerm) (aj.map encPerm)
  have hApc : 6 * loopModK * ((Val.list [.list (((t0 :: ts).map (t0⁻¹ * ·)).map encPerm),
      .list (aj.map encPerm)]).wt + 1) ^ 2 ≤ Ap := by
    have := wt_list2_le (.list (((t0 :: ts).map (t0⁻¹ * ·)).map encPerm)) (.list (aj.map encPerm))
    rw [← hAp]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have oAp := tmJ_wt_append_le (((t0 :: ts).map (t0⁻¹ * ·)).map encPerm) (aj.map encPerm)
  have ca := Det.call (Det.mk2 cm b1) dAp
  rw [hLe] at ca oAp
  have dMk := mkGroup_spec hA.hmk L
  have hMkc : mkGroupK * ((L.length + 2) * (n + 1)) ^ 3 ≤ Mk := by
    rw [← hMk]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 3)
  have wMk := FunDet.wt_lt dMk
  have c2 := (Det.call (Det.mk2 b2 ca) dMk).mono (c' := 60 * Sb) (by
    have := wt_list2_le (encPerm t0⁻¹) (Val.list ((t0 :: ts).map encPerm))
    have := wt_list2_le (.list (((t0 :: ts).map (t0⁻¹ * ·)).map encPerm)) (.list (aj.map encPerm))
    have := wt_list2_le (.nat n) (.list (L.map encPerm))
    have := wt_encPerm_le t0⁻¹
    have : (n + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : 4 * (W + 1) ^ 2 ≤ O1 := by
      rw [← hO1]
      have : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [hW]; omega)
  refine (tmJ_letDet (C := 40 * Sb) c2 ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  -- step 3: the reduction
  have dR := red_spec hst hA.hrd hj (gv := encGroup L) (G := gens L) ⟨L, rfl, rfl⟩
  have wnil : (Val.list []).wt = 4 := by simp [Val.wt, GI.Lang.cellWt, GI.Machine.len_zero]
  have hRc : (pointwiseStabPrim hst).bound (.list [encGroup L, .list []]) + 20 * (encGroup L).wt +
      10 ^ 7 * (n + 1) ^ 9 ≤ Rd := by
    have h1 := GI.Impl.Prim.bound_le (pointwiseStabPrim hst) (v := .list [encGroup L, .list []])
      (W := 2 * Mk + 14) (by
        have := wt_list2_le (encGroup L) (.list [])
        omega)
    have h1' : (pointwiseStabPrim hst).boundSize (2 * Mk + 14) =
        (pointwiseStabPrim hst).c * (2 * Mk + 14 + 2) ^ (pointwiseStabPrim hst).k := rfl
    have h2 : 10 ^ 7 * (n + 1) ^ 9 ≤ 10 ^ 7 * (W + 1) ^ 9 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 9)
    rw [← hRd]; omega
  have dR' := dR.mono (Q' := fun w c => (∃ hs : List (Perm (Fin n)), w = encGroup hs ∧
      gens hs = gens L ∧ hs.length ≤ n ^ 2) ∧ c ≤ Rd) fun w c h => by
    obtain ⟨hs, h1, h2, h3, h4⟩ := h
    exact ⟨⟨hs, h1, h2, h3⟩, h4.trans hRc⟩
  have r2 := Det.arg' (P := P) (vs := [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm),
    .nat n]) (rest := [encPerm t0⁻¹, encGroup L]) (j := 2) (v := .nat n) rfl
  have r3 := Det.var' (P := P) (env := [Val.list [.list ((t0 :: ts).map encPerm),
    .list (aj.map encPerm), .nat n], encPerm t0⁻¹, encGroup L]) (i := 2) (v := encGroup L) rfl
  have cr := (Det.mk2 r2 r3).mono (c' := 10 * Sb) (by
    have := wt_list2_le (.nat n) (encGroup L); rw [hW]; omega)
  refine (tmJ_letCall (C := 10 * Sb) cr dR' ?_).mono fun u cu hu => ⟨hu.1, by omega⟩
  rintro gV ⟨hs, rfl, hgs, hl⟩ wg
  have s0 := Det.arg' (P := P) (vs := [.list ((t0 :: ts).map encPerm), .list (aj.map encPerm),
    .nat n]) (rest := [encPerm t0⁻¹, encGroup L, encGroup hs]) (j := 0)
    (v := .list ((t0 :: ts).map encPerm)) rfl
  have s1 := Det.get' s0 (Det.nat 0) (v := encPerm t0) rfl
  have s3 := Det.var' (P := P) (env := [Val.list [.list ((t0 :: ts).map encPerm),
    .list (aj.map encPerm), .nat n], encPerm t0⁻¹, encGroup L, encGroup hs]) (i := 3)
    (v := encGroup hs) rfl
  refine EvalAll.mono (Det.mk2 s1 s3) fun w c h => ⟨⟨hs, h.1, by rw [hgs, ← hL], hl⟩, ?_⟩
  have := wt_list2_le (encPerm t0) (encGroup hs)
  have := h.2
  rw [hW] at this
  omega

end GI.Impl
