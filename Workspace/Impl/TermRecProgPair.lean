import Workspace.Impl.TermRecProgY

/-!
# T5, one entry of the table: `Iso_H(S, T)`

`tmRi_pair_spec`: on `[[c, S], T]` the function `b + 10` returns `Iso_H(S, T)` as a coset in
normal form (`CosetC`). It maps `tmRiYE` over the points `y ∈ S` (one recursive call each), forms
the union of the parts with `GI.Lang.combine` (the parts cover the transporter,
`tmRi_union_eq`, and it is empty or a coset, `tmRi_iso_coset`), and cuts the generators to `n²`
with the coset normal form.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open scoped Pointwise
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

theorem tmRi_forall₂_pieces {α : Type} {Q : α → Perm (Fin n) × Acc n → Prop} :
    ∀ {xs : List α} {ws : List Val},
      List.Forall₂ (fun x w => ∃ p : Perm (Fin n) × Acc n, w = encPiece p ∧ Q x p) xs ws →
      ∃ ps : List (Perm (Fin n) × Acc n), ws = ps.map encPiece ∧ List.Forall₂ Q xs ps
  | [], [], _ => ⟨[], rfl, List.Forall₂.nil⟩
  | _ :: _, _ :: _, List.Forall₂.cons ⟨p, hp, hq⟩ h =>
    let ⟨ps, e, h'⟩ := tmRi_forall₂_pieces h
    ⟨p :: ps, by rw [hp, e]; rfl, List.Forall₂.cons hq h'⟩

theorem tmRi_forall₂_mem {α β : Type} {Q : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Q l₁ l₂ →
      (∀ q ∈ l₂, ∃ a ∈ l₁, Q a q) ∧ ∀ a ∈ l₁, ∃ q ∈ l₂, Q a q
  | [], [], _ => ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l₁, q :: l₂, List.Forall₂.cons h hs => by
    obtain ⟨h1, h2⟩ := tmRi_forall₂_mem hs
    refine ⟨fun q' hq' => ?_, fun a' ha' => ?_⟩
    · rcases List.mem_cons.1 hq' with rfl | hq'
      · exact ⟨a, List.mem_cons_self .., h⟩
      · obtain ⟨a', ha', h'⟩ := h1 q' hq'; exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩
    · rcases List.mem_cons.1 ha' with rfl | ha'
      · exact ⟨q, List.mem_cons_self .., h⟩
      · obtain ⟨q', hq', h'⟩ := h2 a' ha'; exact ⟨q', List.mem_cons_of_mem _ hq', h'⟩

theorem tmRi_wt_piece (p : Perm (Fin n) × Acc n) (h : ∀ c gs, p.2 = some (c, gs) → gs.length ≤ n ^ 2) :
    (encPiece p).wt ≤ 900 * (n + 1) ^ 6 := by
  have h1 := wt_encAcc_le p.2 h
  have h2 := wt_list2_le (encPerm p.1) (encAcc p.2)
  have h3 := wt_encPerm_le p.1
  have h4 : ((n ^ 2 + 2) * (n + 1)) ^ 2 ≤ 4 * (n + 1) ^ 6 := by
    have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have : (n ^ 2 + 2) * (n + 1) ≤ 2 * (n + 1) ^ 3 := by
      calc (n ^ 2 + 2) * (n + 1) ≤ 2 * (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_right _ (by omega)
        _ = 2 * (n + 1) ^ 3 := by ring
    calc _ ≤ (2 * (n + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 4 * (n + 1) ^ 6 := by ring
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  show (Val.list [encPerm p.1, encAcc p.2]).wt ≤ _
  omega

/-- A bound on the weight of the parts of one entry, for at most `M` points. -/
def tmRiB2 (n M : ℕ) : ℕ := 10 ^ 4 * (M + 1) * (n + 1) ^ 6 + 100

/-- The cost bound of one entry besides the parts. -/
noncomputable def tmRiPairC (hm : Membership) (n M W : ℕ) : ℕ :=
  mapK * (M + 1) * (5 * W + tmRiB2 n M + 10) + combCost n (3 * tmRiB2 n M + 30) +
    cosetNFCost hm n (100 * ((tmRiB2 n M + 2) * (n + 1)) ^ 2) +
    100 * (W + tmRiB2 n M + 100 * ((tmRiB2 n M + 2) * (n + 1)) ^ 2) + 10 ^ 4 * (n + 1) ^ 6

/-- **One entry of the table.** -/
theorem tmRi_pair_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {M ℓ T : ℕ} (ih : TmRiIH P b n M ℓ T)
    {σH σN σA : List (Perm (Fin n))} {Pl : Val} {Sl Tl : List (TmRiO n)} {ox : TmRiO n}
    (hsol : IsSolvable (gens σH)) (hHl : σH.length ≤ n ^ 2) (hAl : σA.length ≤ n ^ 2)
    (hNH : gens σN ≤ gens σH) (hNn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hA : gens σA = relDerived (gens σH) (gens σN) ℓ)
    (hfuel : relDerived (gens σH) (gens σN) (ℓ + 1) ≤ gens σN) (hℓ : ℓ ≤ n ^ 2 + 5)
    (hSo : ∀ s ∈ tmGlMs Sl, ∀ s' ∈ tmGlMs Sl, SameOrb (gens σA) s s')
    (hTo : ∀ t ∈ tmGlMs Tl, ∀ t' ∈ tmGlMs Tl, SameOrb (gens σA) t t')
    (hNT : Fixes (gens σN) (tmGlMs Tl)) (hSl : Sl.length ≤ M) (hTl : Tl.length ≤ M)
    (hok : TmRecObjOK M (Sl ++ Tl)) (hT0 : Tl[0]? = some ox) {W : ℕ}
    (hW : (Val.list [.list [.list [.nat ℓ, encGroup σH, encGroup σA, Pl], tmGlObjsVal Sl],
      tmGlObjsVal Tl]).wt ≤ W) :
    FunAll P (b + 10) (.list [.list [.list [.nat ℓ, encGroup σH, encGroup σA, Pl],
        tmGlObjsVal Sl], tmGlObjsVal Tl])
      (fun u cost => CosetC n u (Iso (gens σH) (tmGlMs Sl) (tmGlMs Tl)) ∧
        cost ≤ M * (T + tmRiYC (solvableCosetIntersectionPrim hsci) n M (4 * W + 10)) +
          tmRiPairC hmem n M W) := by
  set c : Val := .list [.nat ℓ, encGroup σH, encGroup σA, Pl] with hc
  set ctx : Val := .list [.list [c, tmGlObjsVal Sl], tmGlObjsVal Tl] with hctx
  set H := gens σH
  set Q : TmRiO n → Perm (Fin n) × Acc n → Prop := fun oy p =>
    p.1 • accSet p.2 = tmRiPart H (tmGlMs Sl) (tmGlMs Tl) (tmRiObj ox) (tmRiObj oy) ∧
      ∀ c gs, p.2 = some (c, gs) → gs.length ≤ n ^ 2 with hQ
  set YC := tmRiYC (solvableCosetIntersectionPrim hsci) n M (4 * W + 10)
  have hSw : (tmGlObjsVal Sl).wt < W := by
    have : (tmGlObjsVal Sl).wt < (Val.list [c, tmGlObjsVal Sl]).wt := wt_le_wt_list (by simp)
    have : (Val.list [c, tmGlObjsVal Sl]).wt < ctx.wt := wt_le_wt_list (by simp)
    omega
  -- the parts
  have hmap := map_spec hP.mapY (c := ctx) (xs := Sl.map tmGlObjVal)
    (R := fun x w => ∃ oy ∈ Sl, x = tmGlObjVal oy ∧ ∃ p : Perm (Fin n) × Acc n,
      w = encPiece p ∧ Q oy p) (B := fun _ => T + YC) (fun x hx => by
      obtain ⟨oy, hy, rfl⟩ := List.mem_map.1 hx
      have hyw : (tmRiYArg ℓ σH σA Pl Sl Tl oy).wt ≤ 4 * W + 10 := by
        have h1 := wt_list2_le ctx (tmGlObjVal oy)
        have h2 : (tmGlObjVal oy).wt < (tmGlObjsVal Sl).wt :=
          wt_le_wt_list (List.mem_map_of_mem hy)
        show (Val.list [ctx, tmGlObjVal oy]).wt ≤ _
        omega
      refine FunAll.mono (tmRi_y_spec hP ih hsol hHl hAl hNH hNn hA hfuel hℓ hSo hTo hNT hSl hTl
        hok hT0 hy hyw) fun w cw h => ⟨⟨oy, hy, rfl, ?_⟩, h.2⟩
      obtain ⟨t, a, rfl, h1, h2⟩ := h.1
      exact ⟨(t, a), rfl, h1, h2⟩)
  have hB2' : tmRiB2 n M = 10 ^ 4 * (M + 1) * (n + 1) ^ 6 + 100 := rfl
  set B2 := tmRiB2 n M with hB2
  set Wo := 700 * (n + 1) ^ 6 with hWo
  have hn6 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hxT : tmRiObj ox ∈ tmGlMs Tl := by
    simp only [tmGlMs, Multiset.mem_coe, List.mem_map]
    exact ⟨ox, List.mem_of_getElem? hT0, rfl⟩
  -- the call of the map
  have dargs := Det.mk2 (Det.var' (P := P) (env := [ctx]) (i := 0) (v := ctx) rfl)
    (Det.get' (Det.arg' (P := P) (vs := [.list [c, tmGlObjsVal Sl], tmGlObjsVal Tl]) (rest := [])
      (j := 0) rfl) (Det.nat 1) (v := .list (Sl.map tmGlObjVal)) rfl)
  have hcall := EvalAll.call_funAll (f := b + 72) dargs
    (Q := fun w cw => (∃ ps : List (Perm (Fin n) × Acc n), w = .list (ps.map encPiece) ∧
      List.Forall₂ Q Sl ps) ∧ w.wt ≤ B2 ∧
      cw ≤ 20 * W + 50 + M * (T + YC) + mapK * (M + 1) * (5 * W + B2 + 10) + B2 + 1)
    fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      refine hmap.mono fun w cw ⟨ws, hw, hR, hcw⟩ => ?_
      have hR' : List.Forall₂ (fun oy w => ∃ p : Perm (Fin n) × Acc n, w = encPiece p ∧ Q oy p)
          Sl ws := by
        rw [List.forall₂_map_left_iff] at hR
        refine hR.imp fun oy w ⟨oy', hy', e, p, hp, hq⟩ => ⟨p, hp, ?_⟩
        rw [tmRi_objVal_inj e]; exact hq
      obtain ⟨ps, rfl, hps⟩ := tmRi_forall₂_pieces hR'
      have hlen : ps.length = Sl.length := hps.length_eq.symm
      have hwps : (Val.list (ps.map encPiece)).wt ≤ B2 := by
        have := tmRi_wt_list_le (ps.map encPiece) (c := 900 * (n + 1) ^ 6) (by
          intro v hv
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hv
          obtain ⟨oy, -, hq⟩ := (tmRi_forall₂_mem hps).1 p hp
          exact tmRi_wt_piece p hq.2)
        rw [List.length_map, hlen] at this
        have : Sl.length * (2 * (900 * (n + 1) ^ 6) + 1) ≤ (M + 1) * (1801 * (n + 1) ^ 6) :=
          Nat.mul_le_mul (by omega) (by omega)
        have : (M + 1) * (1801 * (n + 1) ^ 6) ≤ 10 ^ 4 * (M + 1) * (n + 1) ^ 6 := by nlinarith
        omega
      refine ⟨⟨ps, hw, hps⟩, hw ▸ hwps, ?_⟩
      have hs := tmRi_sum_const (Sl.map tmGlObjVal) (fun _ => T + YC) (K := T + YC)
        (fun _ _ => le_rfl)
      rw [List.length_map] at hs
      have h1 : Sl.length * (T + YC) ≤ M * (T + YC) := Nat.mul_le_mul_right _ hSl
      have h2 := wt_list2_le ctx (.list (Sl.map tmGlObjVal))
      have h3 : mapK * ((Sl.map tmGlObjVal).length + 1) * ((Val.list [ctx, .list (Sl.map tmGlObjVal)]).wt +
          w.wt + 1) ≤ mapK * (M + 1) * (5 * W + B2 + 10) := by
        rw [List.length_map]
        refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
        have : (Val.list (Sl.map tmGlObjVal)).wt = (tmGlObjsVal Sl).wt := rfl
        rw [hw]; omega
      have h4 := wt_list2_le ctx (.list (Sl.map tmGlObjVal))
      have : (tmGlObjsVal Sl) = .list (Sl.map tmGlObjVal) := rfl
      have h5 : (Val.list [.list [c, tmGlObjsVal Sl], tmGlObjsVal Tl]).wt = ctx.wt := rfl
      have h6 : (Val.list (Sl.map tmGlObjVal)).wt < (Val.list [c, tmGlObjsVal Sl]).wt :=
        wt_le_wt_list (by simp [tmGlObjsVal])
      have h7 : (Val.list [c, tmGlObjsVal Sl]).wt < ctx.wt := wt_le_wt_list (by simp)
      have hww : w.wt ≤ B2 := hw ▸ hwps
      omega
  set accW := 100 * ((B2 + 2) * (n + 1)) ^ 2 with haccW
  have hPC : tmRiPairC hmem n M W = mapK * (M + 1) * (5 * W + B2 + 10) + combCost n (3 * B2 + 30) +
      cosetNFCost hmem n accW + 100 * (W + B2 + accW) + 10 ^ 4 * (n + 1) ^ 6 := rfl
  refine FunAll.intro hP.pair (EvalAll.mono (Q := fun u c => CosetC n u (Iso H (tmGlMs Sl)
    (tmGlMs Tl)) ∧ u.wt ≤ Wo ∧ c ≤ M * (T + YC) + tmRiPairC hmem n M W) ?_
    fun u c h => ⟨h.1, h.2.2⟩)
  refine tmRi_letB hcall (fun _ _ h => h.2.2) ?_ fun w1 c1 h1 => ?_
  · rw [hPC]; omega
  obtain ⟨⟨ps, rfl, hps⟩, hw1, -⟩ := h1
  -- the union of the parts is the transporter
  have hU : unionSet ps = Iso H (tmGlMs Sl) (tmGlMs Tl) := by
    rw [← tmRi_union_eq hxT]
    ext g
    simp only [unionSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, hq, hg⟩
      obtain ⟨oy, hy, hQ⟩ := (tmRi_forall₂_mem hps).1 q hq
      refine ⟨tmRiObj oy, ?_, ?_⟩
      · simp only [tmGlMs, Multiset.mem_coe, List.mem_map]; exact ⟨oy, hy, rfl⟩
      · rw [← hQ.1]; exact hg
    · rintro ⟨y, hy, hg⟩
      simp only [tmGlMs, Multiset.mem_coe, List.mem_map] at hy
      obtain ⟨oy, hoy, rfl⟩ := hy
      obtain ⟨q, hq, hQ⟩ := (tmRi_forall₂_mem hps).2 oy hoy
      exact ⟨q, hq, by rw [hQ.1]; exact hg⟩
  -- the combination
  have dcargs := Det.mk3 (Det.nat (P := P) (env := [ctx, .list (ps.map encPiece)]) 0)
    (Det.var' (P := P) (env := [ctx, .list (ps.map encPiece)]) (i := 1) rfl)
    (Det.nil (P := P) (env := [ctx, .list (ps.map encPiece)]))
  have hcomb := comb_spec hP.comb hP.combS hP.comp hP.inv hP.app (.nat 0) ps
  have hin : (Val.list [.nat 0, .list (ps.map encPiece), .list []]).wt ≤ 3 * B2 + 30 := by
    have := wt_list3_le (.nat 0) (.list (ps.map encPiece)) (.list [])
    have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have : (Val.list []).wt ≤ 5 := by decide
    omega
  have hL : ∀ c gs, combine ps = some (c, gs) → gs.length ≤ B2 := fun c gs h => by
    have h1 := length_combine ps c gs h
    have h2 := sum_accLen_le ps
    have h3 := sum_wt_lt_wt_list (ps.map encPiece)
    omega
  have hacc := wt_encAcc_le (combine ps) hL
  have dcomb := (Det.call dcargs hcomb).mono (c' := 10 * B2 + 100 + combCost n (3 * B2 + 30) +
    accW + 1) (by
      have := combCost_mono n hin
      have := wt_list3_le (.nat 0) (.list (ps.map encPiece)) (.list [])
      have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
      have : (Val.list []).wt ≤ 5 := by decide
      omega)
  refine tmRi_letB dcomb (fun _ _ h => h.2) ?_ fun w2 c2 h2 => ?_
  · rw [hPC]; omega
  obtain ⟨rfl, -⟩ := h2
  -- the normal form
  have hcoe : CosetOrEmpty n (encAcc (combine ps)) (unionSet ps) :=
    combine_cosetOrEmpty ps (by rw [hU]; exact tmRi_iso_coset H _ _)
  refine EvalAll.call_funAll (Det.var' (P := P)
    (env := [ctx, .list (ps.map encPiece), encAcc (combine ps)]) (i := 2) rfl)
    fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (cosetNF_spec hmem hP.cnf hP.mem hcoe).mono fun u cu h => ⟨by rw [← hU]; exact h.1, ?_, ?_⟩
  · exact tmRi_wt_ansC h.1
  · have := tmRi_wt_ansC h.1
    have := cosetNFCost_mono hmem n hacc
    have := h.2
    rw [hPC]
    generalize M * (T + YC) = A at *
    generalize mapK * (M + 1) * (5 * W + B2 + 10) = A2 at *
    generalize combCost n (3 * B2 + 30) = A3 at *
    generalize cosetNFCost hmem n accW = A4 at *
    omega

end GI.Impl
