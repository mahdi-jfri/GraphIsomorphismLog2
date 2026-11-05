module

public import Workspace.Impl.TermJProgAut

@[expose] public section

/-!
# The labels and their transporters (program)

The answer `w = [h₀, ⟨U⟩]` of the label coset gives the labels `h₀ u` for `u ∈ 1 :: U`
(paper, proof of Theorem A.23: "for the coset representative and for each generator of the
label coset"). `tmJLabsF`, on `[ctx, w]`, composes `h₀` with every `u ∈ 1 :: U` and maps the
per-label function over the results.

`tmJ_labs_spec` is generic in the per-label specification: if the per-label function meets a
relation `R h` at cost `KH ([ctx, h].wt + 1)^DH` for every label `h`, then the program returns
a list of results related to the labels by `R`, at a cost polynomial in the input weight.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens)

/-- On `[ctx, [h₀, ⟨U⟩]]`: the per-label function on `ctx` and each `h₀ u`, `u ∈ 1 :: U`. -/
def tmJLabsF (mpC mpH : ℕ) : Expr :=
  .call mpH (mk2 (arg 0)
    (.call mpC (mk2 (.get (arg 1) (.nat 0)) (.get (.get (arg 1) (.nat 1)) (.nat 1)))))

/-- The labels `h₀ u` for `u ∈ 1 :: U`. -/
def tmJLabs {m : ℕ} (h0 : Perm (Fin m)) (U : List (Perm (Fin m))) : List (Perm (Fin m)) :=
  (1 :: U).map (h0 * ·)

/-- The bound of `tmJLabsF`. -/
def tmJLabsK (KH DH X : ℕ) : ℕ :=
  1000 * (X + permK * (X + 1) ^ 3 + 13 * (X + 1) ^ 3 +
    (X * (permK * (X + 1) ^ 3) + mapK * (X + 1) * (4 * X + 7 + 13 * (X + 1) ^ 3)) +
    KH * (2 * X + 8 * (X + 1) ^ 2 + 7) ^ DH +
    (2 * X * (KH * (2 * X + 8 * (X + 1) ^ 2 + 7) ^ DH) + X + 4) +
    (X * (KH * (2 * X + 8 * (X + 1) ^ 2 + 7) ^ DH) + mapK * (X + 1) *
      (2 * (X + 13 * (X + 1) ^ 3) + 7 +
        (2 * X * (KH * (2 * X + 8 * (X + 1) ^ 2 + 7) ^ DH) + X + 4))) + 100)

theorem tmJLabsK_poly (KH DH : ℕ) : TmJPoly (tmJLabsK KH DH) := by
  have hW : TmJPoly fun W => W := TmJPoly.id
  have h1 : TmJPoly fun W => W + 1 := TmJPoly.add hW (TmJPoly.const 1)
  have hc : TmJPoly fun W => permK * (W + 1) ^ 3 := TmJPoly.smul _ (TmJPoly.pow h1 3)
  have ho : TmJPoly fun W => 13 * (W + 1) ^ 3 := TmJPoly.smul _ (TmJPoly.pow h1 3)
  have hB : TmJPoly fun W => KH * (2 * W + 8 * (W + 1) ^ 2 + 7) ^ DH :=
    TmJPoly.smul _ (TmJPoly.pow (TmJPoly.add (TmJPoly.add (TmJPoly.smul 2 hW)
      (TmJPoly.smul 8 (TmJPoly.pow h1 2))) (TmJPoly.const 7)) _)
  have hO2 : TmJPoly fun W => 2 * W * (KH * (2 * W + 8 * (W + 1) ^ 2 + 7) ^ DH) + W + 4 :=
    TmJPoly.add (TmJPoly.add (TmJPoly.mul (TmJPoly.smul 2 hW) hB) hW) (TmJPoly.const 4)
  have hC1 : TmJPoly fun W => W * (permK * (W + 1) ^ 3) +
      mapK * (W + 1) * (4 * W + 7 + 13 * (W + 1) ^ 3) :=
    TmJPoly.add (TmJPoly.mul hW hc) (TmJPoly.mul (TmJPoly.smul _ h1)
      (TmJPoly.add (TmJPoly.add (TmJPoly.smul 4 hW) (TmJPoly.const 7)) ho))
  have hC2 : TmJPoly fun W => W * (KH * (2 * W + 8 * (W + 1) ^ 2 + 7) ^ DH) + mapK * (W + 1) *
      (2 * (W + 13 * (W + 1) ^ 3) + 7 +
        (2 * W * (KH * (2 * W + 8 * (W + 1) ^ 2 + 7) ^ DH) + W + 4)) :=
    TmJPoly.add (TmJPoly.mul hW hB) (TmJPoly.mul (TmJPoly.smul _ h1)
      (TmJPoly.add (TmJPoly.add (TmJPoly.smul 2 (TmJPoly.add hW ho)) (TmJPoly.const 7)) hO2))
  unfold tmJLabsK
  exact TmJPoly.smul _ (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add (TmJPoly.add
    (TmJPoly.add (TmJPoly.add (TmJPoly.add hW hc) ho) hC1) hB) hO2) hC2) (TmJPoly.const 0)
    |>.mono fun W => by omega) (TmJPoly.const 100))

theorem tmJ_forall₂_eq_map {α β : Type*} (g : α → β) :
    ∀ {l : List α} {ws : List β}, List.Forall₂ (fun a b => b = g a) l ws → ws = l.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h t => by rw [h, tmJ_forall₂_eq_map g t]; rfl

theorem tmJ_sum_wt_le {α : Type*} {B : ℕ} :
    ∀ {l : List α} {ws : List Val}, List.Forall₂ (fun _ w => w.wt < B) l ws →
      (ws.map Val.wt).sum ≤ l.length * B
  | [], [], _ => by simp
  | _ :: _, _ :: _, List.Forall₂.cons h t => by
    have := tmJ_sum_wt_le t
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.add_mul, one_mul]
    omega

private theorem tmJLb_lt_wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : n < (encPerm σ).wt := by
  have h := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (σ i))
  simp only [List.length_map, List.length_finRange] at h
  exact h

/-- **The transporters of all labels.** -/
theorem tmJ_labs_spec (KH DH : ℕ) {P : Program} {f mpC cp mpH pb : ℕ}
    (hf : P.funs[f]? = some (tmJLabsF mpC mpH)) (hmpC : P.HasAt mpC (mapFuns mpC cp))
    (hcp : P.HasAt cp (composeFuns cp)) (hmpH : P.HasAt mpH (mapFuns mpH pb))
    {m : ℕ} (ctx : Val) (h0 : Perm (Fin m)) (U : List (Perm (Fin m)))
    (R : Perm (Fin m) → Val → Prop)
    (hH : ∀ h ∈ tmJLabs h0 U, FunAll P pb (.list [ctx, encPerm h]) (fun out c =>
      R h out ∧ c ≤ KH * ((Val.list [ctx, encPerm h]).wt + 1) ^ DH)) :
    FunAll P f (.list [ctx, .list [encPerm h0, encGroup U]]) (fun out cost =>
      (∃ ws, out = .list ws ∧ List.Forall₂ R (tmJLabs h0 U) ws) ∧
      cost ≤ tmJLabsK KH DH (Val.list [ctx, .list [encPerm h0, encGroup U]]).wt) := by
  refine FunAll.intro hf ?_
  unfold tmJLabsF
  obtain ⟨X, hX⟩ : ∃ X, (Val.list [ctx, .list [encPerm h0, encGroup U]]).wt = X := ⟨_, rfl⟩
  rw [hX]
  have wc : ctx.wt < X := hX ▸ wt_le_wt_list (by simp)
  have ww : (Val.list [encPerm h0, encGroup U]).wt < X := hX ▸ wt_le_wt_list (by simp)
  have wh0 : (encPerm h0).wt < (Val.list [encPerm h0, encGroup U]).wt := wt_le_wt_list (by simp)
  have wg : (encGroup U).wt < (Val.list [encPerm h0, encGroup U]).wt := wt_le_wt_list (by simp)
  have wl : (Val.list ((1 :: U).map encPerm)).wt < (encGroup U).wt :=
    wt_le_wt_list (by simp)
  have hm : m < X := by have := tmJLb_lt_wt h0; omega
  have hlen : (1 :: U).length < X := by
    have := length_lt_wt_list ((1 :: U).map encPerm); simp only [List.length_map] at this; omega
  -- the compositions
  have hC : ∀ x ∈ (1 :: U).map encPerm, FunAll P cp (.list [encPerm h0, x]) (fun w c =>
      (∀ u, x = encPerm u → w = encPerm (h0 * u)) ∧ c ≤ permK * (m + 1) ^ 3) := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
    exact FunAll.mono (compose_spec hcp h0 u) fun w c h => ⟨fun u' hu' => by
      rw [encPerm_injective hu'] at h; exact h.1, h.2⟩
  have dC := map_spec hmpC hC
  -- the labels as values
  obtain ⟨Bc, hBc⟩ : ∃ Bc, permK * (X + 1) ^ 3 = Bc := ⟨_, rfl⟩
  obtain ⟨O1, hO1⟩ : ∃ O1, 13 * (X + 1) ^ 3 = O1 := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1, X * Bc + mapK * (X + 1) * (4 * X + 7 + O1) = C1 := ⟨_, rfl⟩
  have wlab : (Val.list ((tmJLabs h0 U).map encPerm)).wt ≤ O1 := by
    have := wt_list_le ((tmJLabs h0 U).map encPerm)
    have hs : (((tmJLabs h0 U).map encPerm).map Val.wt).sum ≤
        (tmJLabs h0 U).length * (4 * (m + 1) ^ 2) := by
      rw [List.map_map]
      refine (List.sum_le_card_nsmul _ (4 * (m + 1) ^ 2) fun x hx => ?_).trans (by simp)
      obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hx
      exact wt_encPerm_le σ
    have hl : (tmJLabs h0 U).length = (1 :: U).length := by simp [tmJLabs]
    simp only [List.length_map] at this
    rw [← hO1]
    have h2 : 4 * (m + 1) ^ 2 ≤ 4 * (X + 1) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    have h3 : (tmJLabs h0 U).length * (4 * (X + 1) ^ 2) ≤ X * (4 * (X + 1) ^ 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : X * (4 * (X + 1) ^ 2) ≤ 4 * (X + 1) ^ 3 := by
      rw [pow_succ]; nlinarith
    have h5 := Nat.mul_le_mul_left (tmJLabs h0 U).length h2
    have h6 : X + 1 ≤ (X + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have dC' : FunDet P mpC (.list [encPerm h0, .list ((1 :: U).map encPerm)])
      (.list ((tmJLabs h0 U).map encPerm)) C1 := by
    refine dC.mono fun w c h => ?_
    obtain ⟨ws, rfl, hws, hc⟩ := h
    have hws' : ws = (tmJLabs h0 U).map encPerm := by
      rw [List.forall₂_map_left_iff] at hws
      have := tmJ_forall₂_eq_map (fun u => encPerm (h0 * u)) (hws.imp fun u w h => h u rfl)
      rw [this, tmJLabs, List.map_map]; rfl
    subst hws'
    refine ⟨rfl, hc.trans ?_⟩
    have hsum : (((1 :: U).map encPerm).map fun _ => permK * (m + 1) ^ 3).sum ≤ X * Bc := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map, ← hBc]
      exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
    have hin : (Val.list [encPerm h0, Val.list ((1 :: U).map encPerm)]).wt ≤ 4 * X + 6 := by
      have := wt_list2_le (encPerm h0) (Val.list ((1 :: U).map encPerm)); omega
    rw [← hC1]
    simp only [List.length_map]
    have : mapK * ((1 :: U).length + 1) *
        ((Val.list [encPerm h0, Val.list ((1 :: U).map encPerm)]).wt +
          (Val.list ((tmJLabs h0 U).map encPerm)).wt + 1) ≤
        mapK * (X + 1) * (4 * X + 7 + O1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega
  -- the per-label calls
  obtain ⟨BH, hBH⟩ : ∃ BH, KH * (2 * X + 8 * (X + 1) ^ 2 + 7) ^ DH = BH := ⟨_, rfl⟩
  obtain ⟨O2, hO2⟩ : ∃ O2, 2 * X * BH + X + 4 = O2 := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C2, X * BH + mapK * (X + 1) * (2 * (X + O1) + 7 + O2) = C2 := ⟨_, rfl⟩
  have hHx : ∀ x ∈ (tmJLabs h0 U).map encPerm, FunAll P pb (.list [ctx, x]) (fun w c =>
      ((∀ h, x = encPerm h → R h w) ∧ w.wt < BH) ∧ c ≤ BH) := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hx
    have hb : KH * ((Val.list [ctx, encPerm h]).wt + 1) ^ DH ≤ BH := by
      have := wt_list2_le ctx (encPerm h)
      have := wt_encPerm_le h
      have : (m + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [← hBH]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    exact (hH h hh).wt_lt.mono fun w c hw => ⟨⟨fun h' e => by
      rw [← encPerm_injective e]; exact hw.1.1, by omega⟩, by omega⟩
  have dH := map_spec hmpH hHx
  have dH' : FunAll P mpH (.list [ctx, .list ((tmJLabs h0 U).map encPerm)]) (fun w c =>
      (∃ ws, w = .list ws ∧ List.Forall₂ R (tmJLabs h0 U) ws) ∧ c ≤ C2) := by
    refine dH.mono fun w c h => ?_
    obtain ⟨ws, rfl, hws, hc⟩ := h
    rw [List.forall₂_map_left_iff] at hws
    refine ⟨⟨ws, rfl, hws.imp fun h w hw => hw.1 h rfl⟩, hc.trans ?_⟩
    have hl : (tmJLabs h0 U).length = (1 :: U).length := by simp [tmJLabs]
    have hsw := tmJ_sum_wt_le (hws.imp fun h w hw => hw.2)
    have hwo : (Val.list ws).wt ≤ O2 := by
      have := wt_list_le ws
      have := List.Forall₂.length_eq hws
      have : (tmJLabs h0 U).length * BH ≤ X * BH := Nat.mul_le_mul_right _ (by omega)
      rw [← hO2]
      have : 2 * X * BH = 2 * (X * BH) := by ring
      omega
    have hin : (Val.list [ctx, Val.list ((tmJLabs h0 U).map encPerm)]).wt ≤ 2 * (X + O1) + 6 := by
      have := wt_list2_le ctx (Val.list ((tmJLabs h0 U).map encPerm)); omega
    rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map, ← hC2]
    have h1 : (tmJLabs h0 U).length * BH ≤ X * BH := Nat.mul_le_mul_right _ (by omega)
    have h2 : mapK * ((tmJLabs h0 U).length + 1) *
        ((Val.list [ctx, Val.list ((tmJLabs h0 U).map encPerm)]).wt + (Val.list ws).wt + 1) ≤
        mapK * (X + 1) * (2 * (X + O1) + 7 + O2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega
  -- the program
  have a0 := Det.arg' (P := P) (vs := [ctx, .list [encPerm h0, encGroup U]]) (rest := [])
    (j := 0) (v := ctx) rfl
  have a1 := Det.arg' (P := P) (vs := [ctx, .list [encPerm h0, encGroup U]]) (rest := [])
    (j := 1) (v := .list [encPerm h0, encGroup U]) rfl
  have g0 := Det.get' a1 (Det.nat 0) (v := encPerm h0) rfl
  have g1 := Det.get' (Det.get' a1 (Det.nat 1) (v := encGroup U) rfl) (Det.nat 1)
    (vs := [.nat m, .list ((1 :: U).map encPerm)]) (v := .list ((1 :: U).map encPerm)) rfl
  have cC := Det.call (Det.mk2 g0 g1) dC'
  refine (tmJ_lastCall (Det.mk2 a0 cC) dH').mono fun w c h => ⟨h.1, h.2.trans ?_⟩
  have := wt_list2_le (encPerm h0) (.list ((1 :: U).map encPerm))
  have := wt_list2_le ctx (.list ((tmJLabs h0 U).map encPerm))
  have := wt_nat_le 0
  have := wt_nat_le 1
  have hK : tmJLabsK KH DH X = 1000 * (X + Bc + O1 + C1 + BH + O2 + C2 + 100) := by
    unfold tmJLabsK; rw [← hC2, ← hO2, ← hBH, ← hC1, ← hO1, ← hBc]
  rw [hK, ← hX]
  rw [← hX] at wc ww
  omega

end GI.Impl
