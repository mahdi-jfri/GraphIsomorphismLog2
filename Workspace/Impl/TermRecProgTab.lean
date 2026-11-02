import Workspace.Impl.TermRecProgPair

/-!
# T5, the table of pairwise transporters

For a list `Ps` of pieces (lists of objects), the function `b + 66` on `[c, P]`, with
`c = [ℓ, gens H, gens A, P]` and `P` the encoded pieces, returns the table: row `S` has entry
`T` equal to `Iso_H(S, T)` as a coset in normal form, for all `S, T ∈ Ps`
(`tmRi_table_spec`). Each entry is one `tmRi_pair_spec`.

`tmRi_mapU` is the map of the language with a uniform bound on the weight and the cost of each
call.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

/-- **The map with uniform bounds.** -/
theorem tmRi_mapU {P : Program} {b f : ℕ} (h : P.HasAt b (mapFuns b f)) {c : Val}
    {xs : List Val} {R : Val → Val → Prop} {Wx K : ℕ}
    (hf : ∀ x ∈ xs, FunAll P f (.list [c, x]) (fun w cost => R x w ∧ w.wt ≤ Wx ∧ cost ≤ K)) :
    FunAll P b (.list [c, .list xs]) (fun w cost => ∃ ws, w = .list ws ∧ List.Forall₂ R xs ws ∧
      w.wt ≤ xs.length * (2 * Wx + 1) + 4 ∧
      cost ≤ xs.length * K +
        mapK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + xs.length * (2 * Wx + 1) + 5)) := by
  refine (map_spec h (R := fun x w => R x w ∧ w.wt ≤ Wx) (B := fun _ => K) fun x hx =>
    (hf x hx).mono fun w cw hw => ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩).mono fun w cw ⟨ws, hw, hR, hc⟩ => ?_
  have hlen : ws.length = xs.length := hR.length_eq.symm
  have hwt : w.wt ≤ xs.length * (2 * Wx + 1) + 4 := by
    rw [hw]
    have := tmRi_wt_list_le ws (c := Wx) fun v hv => by
      obtain ⟨x, -, hxv⟩ := (tmRi_forall₂_mem hR).1 v hv
      exact hxv.2
    rwa [hlen] at this
  refine ⟨ws, hw, hR.imp fun _ _ h => h.1, hwt, ?_⟩
  have h1 := tmRi_sum_const xs (fun _ => K) (K := K) fun _ _ => le_rfl
  have h2 : mapK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + w.wt + 1) ≤
      mapK * (xs.length + 1) * ((Val.list [c, .list xs]).wt + xs.length * (2 * Wx + 1) + 5) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- The list of objects in the pieces. -/
def tmRiFlat (Ps : List (List (TmRiO n))) : List (TmRiO n) := Ps.flatten

theorem TmRecObjOK.sub {M : ℕ} {Z Z' : List (TmRiO n)} (h : TmRecObjOK M Z)
    (hs : ∀ o ∈ Z', o ∈ Z) : TmRecObjOK M Z' := fun o ho =>
  ⟨(h o (hs o ho)).1, (h o (hs o ho)).2.1, fun o' ho' => (h o (hs o ho)).2.2 o' (hs o' ho')⟩

/-- What the table needs of each piece. -/
def TmRiPc (σA σN : List (Perm (Fin n))) (M : ℕ) (S : List (TmRiO n)) : Prop :=
  S ≠ [] ∧ S.length ≤ M ∧ (∀ s ∈ tmGlMs S, ∀ s' ∈ tmGlMs S, SameOrb (gens σA) s s') ∧
    Fixes (gens σN) (tmGlMs S)

/-- The encoded table: row `S`, entry `T`, is `Iso_H(S, T)` as a coset. -/
def TmRiTab (H : Subgroup (Perm (Fin n))) (Ps : List (List (TmRiO n))) (tab : List Val) : Prop :=
  List.Forall₂ (fun SV row => ∃ S ∈ Ps, SV = tmGlObjsVal S ∧ ∃ us, row = .list us ∧
    List.Forall₂ (fun TV u => ∃ T ∈ Ps, TV = tmGlObjsVal T ∧ CosetC n u (Iso H (tmGlMs S)
      (tmGlMs T))) (Ps.map tmGlObjsVal) us) (Ps.map tmGlObjsVal) tab

/-- The cost of the table besides the recursive calls, for `m` pieces. -/
noncomputable def tmRiTabC (hm : Membership) (n M m W : ℕ) : ℕ :=
  m * (m * tmRiPairC hm n M (10 * W + 20) +
    mapK * (m + 1) * (10 * W + 20 + m * (1400 * (n + 1) ^ 6 + 1) + 5) + 50 * W + 100 +
      m * (1400 * (n + 1) ^ 6 + 1)) +
    mapK * (m + 1) * (W + m * (2 * (m * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) + 5)

theorem tmRi_obj_mem {S : List (TmRiO n)} {o : TmRiO n} (h : o ∈ S) : tmRiObj o ∈ tmGlMs S := by
  simp only [tmGlMs, Multiset.mem_coe, List.mem_map]
  exact ⟨o, h, rfl⟩

/-- **The table.** -/
theorem tmRi_table_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {M ℓ T : ℕ} (ih : TmRiIH P b n M ℓ T)
    {σH σN σA : List (Perm (Fin n))} {Ps : List (List (TmRiO n))} {Z : List (TmRiO n)}
    (hsol : IsSolvable (gens σH)) (hHl : σH.length ≤ n ^ 2) (hAl : σA.length ≤ n ^ 2)
    (hNH : gens σN ≤ gens σH) (hNn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hA : gens σA = relDerived (gens σH) (gens σN) ℓ)
    (hfuel : relDerived (gens σH) (gens σN) (ℓ + 1) ≤ gens σN) (hℓ : ℓ ≤ n ^ 2 + 5)
    (hPs : ∀ S ∈ Ps, TmRiPc σA σN M S) (hok : TmRecObjOK M Z) (hZ : ∀ S ∈ Ps, ∀ o ∈ S, o ∈ Z)
    {W : ℕ} (hW : (Val.list [.list [.nat ℓ, encGroup σH, encGroup σA, .list (Ps.map tmGlObjsVal)],
      .list (Ps.map tmGlObjsVal)]).wt ≤ W) :
    FunAll P (b + 66) (.list [.list [.nat ℓ, encGroup σH, encGroup σA,
        .list (Ps.map tmGlObjsVal)], .list (Ps.map tmGlObjsVal)])
      (fun w cost => ∃ tab, w = .list tab ∧ TmRiTab (gens σH) Ps tab ∧
        w.wt ≤ Ps.length * (2 * (Ps.length * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) + 4 ∧
        cost ≤ Ps.length * Ps.length *
            (M * (T + tmRiYC (solvableCosetIntersectionPrim hsci) n M (4 * (10 * W + 20) + 10))) +
          tmRiTabC hmem n M Ps.length W) := by
  set PV : Val := .list (Ps.map tmGlObjsVal) with hPV
  set c : Val := .list [.nat ℓ, encGroup σH, encGroup σA, PV] with hc
  set m := Ps.length with hm
  set Cp := M * (T + tmRiYC (solvableCosetIntersectionPrim hsci) n M (4 * (10 * W + 20) + 10)) +
    tmRiPairC hmem n M (10 * W + 20) with hCp
  have hcw : c.wt < W := by
    have : c.wt < (Val.list [c, PV]).wt := wt_le_wt_list (by simp)
    omega
  have hPw : PV.wt < W := by
    have : PV.wt < (Val.list [c, PV]).wt := wt_le_wt_list (by simp)
    omega
  have hSw : ∀ S ∈ Ps, (tmGlObjsVal S).wt < PV.wt := fun S hS =>
    wt_le_wt_list (List.mem_map_of_mem hS)
  have hlenPV : (Ps.map tmGlObjsVal).length = m := by rw [List.length_map]
  -- one row
  have hrow : ∀ SV ∈ Ps.map tmGlObjsVal, FunAll P (b + 9) (.list [c, SV]) (fun w cost =>
      (∃ S ∈ Ps, SV = tmGlObjsVal S ∧ ∃ us, w = .list us ∧ List.Forall₂ (fun TV u =>
        ∃ T ∈ Ps, TV = tmGlObjsVal T ∧ CosetC n u (Iso (gens σH) (tmGlMs S) (tmGlMs T)))
        (Ps.map tmGlObjsVal) us) ∧ w.wt ≤ m * (1400 * (n + 1) ^ 6 + 1) + 4 ∧
      cost ≤ m * Cp + mapK * (m + 1) * (10 * W + 20 + m * (1400 * (n + 1) ^ 6 + 1) + 5) +
        50 * W + 100 + m * (1400 * (n + 1) ^ 6 + 1)) := by
    intro SV hSV
    obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hSV
    obtain ⟨hS0, hSl, hSo, -⟩ := hPs S hS
    have hpair : ∀ TV ∈ Ps.map tmGlObjsVal, FunAll P (b + 10) (.list [.list [c, tmGlObjsVal S], TV])
        (fun w cost => (∃ T ∈ Ps, TV = tmGlObjsVal T ∧
          CosetC n w (Iso (gens σH) (tmGlMs S) (tmGlMs T))) ∧ w.wt ≤ 700 * (n + 1) ^ 6 ∧
          cost ≤ Cp) := by
      intro TV hTV
      obtain ⟨Tl, hT, rfl⟩ := List.mem_map.1 hTV
      obtain ⟨hT0, hTl, hTo, hNT⟩ := hPs Tl hT
      obtain ⟨ox, hox⟩ : ∃ ox, Tl[0]? = some ox := by
        cases Tl with
        | nil => exact absurd rfl hT0
        | cons o _ => exact ⟨o, rfl⟩
      have hW' : (Val.list [.list [c, tmGlObjsVal S], tmGlObjsVal Tl]).wt ≤ 10 * W + 20 := by
        have := wt_list2_le (.list [c, tmGlObjsVal S]) (tmGlObjsVal Tl)
        have := wt_list2_le c (tmGlObjsVal S)
        have := hSw S hS
        have := hSw Tl hT
        omega
      refine (tmRi_pair_spec hP ih hsol hHl hAl hNH hNn hA hfuel hℓ hSo hTo hNT hSl hTl
        (hok.sub fun o ho => ?_) hox hW').mono fun w cw h => ⟨⟨Tl, hT, rfl, h.1⟩,
          tmRi_wt_ansC h.1, h.2⟩
      rcases List.mem_append.1 ho with ho | ho
      · exact hZ S hS o ho
      · exact hZ Tl hT o ho
    have hmap := tmRi_mapU hP.mapPair (c := .list [c, tmGlObjsVal S]) hpair
    refine FunAll.intro hP.row (EvalAll.call_funAll (Det.mk2
      (Det.var' (P := P) (env := [.list [c, tmGlObjsVal S]]) (i := 0) rfl)
      (Det.get' (Det.arg' (P := P) (vs := [c, tmGlObjsVal S]) (rest := []) (j := 0) rfl)
        (Det.nat 3) (v := PV) rfl)) fun v ca hv => ?_)
    obtain ⟨rfl, hca⟩ := hv
    refine hmap.mono fun w cw ⟨ws, hw, hR, hww, hcw'⟩ => ⟨⟨S, hS, rfl, ws, hw, hR.imp
      fun _ _ h => h⟩, by
        rw [hlenPV] at hww
        have e : m * (2 * (700 * (n + 1) ^ 6) + 1) = m * (1400 * (n + 1) ^ 6 + 1) := by ring
        omega, ?_⟩
    have hp1 : (Ps.map tmGlObjsVal).length * Cp = m * Cp := by rw [hlenPV]
    have hp2 : mapK * ((Ps.map tmGlObjsVal).length + 1) *
        ((Val.list [Val.list [c, tmGlObjsVal S], Val.list (List.map tmGlObjsVal Ps)]).wt +
          (List.map tmGlObjsVal Ps).length * (2 * (700 * (n + 1) ^ 6) + 1) + 5) =
        mapK * (m + 1) * ((Val.list [Val.list [c, tmGlObjsVal S], PV]).wt +
          m * (2 * (700 * (n + 1) ^ 6) + 1) + 5) := by rw [hlenPV]
    have hp3 : (Ps.map tmGlObjsVal).length * (2 * (700 * (n + 1) ^ 6) + 1) =
        m * (1400 * (n + 1) ^ 6 + 1) := by rw [hlenPV]; ring
    have h1 := wt_list2_le (.list [c, tmGlObjsVal S]) PV
    have h2 := wt_list2_le c (tmGlObjsVal S)
    have h3 := hSw S hS
    have h4 := wt_list2_le c PV
    have h5 : (Val.nat 3).wt ≤ 5 := by decide
    have e : m * (2 * (700 * (n + 1) ^ 6) + 1) = m * (1400 * (n + 1) ^ 6 + 1) := by ring
    have h6 : (Val.list [Val.list [c, tmGlObjsVal S], PV]).wt + m * (2 * (700 * (n + 1) ^ 6) + 1) + 5 ≤
        10 * W + 20 + m * (1400 * (n + 1) ^ 6 + 1) + 5 := by omega
    have h7 := Nat.mul_le_mul_left (mapK * (m + 1)) h6
    omega
  refine (tmRi_mapU hP.mapRow (c := c) hrow).mono fun w cw ⟨ws, hw, hR, hww, hcw'⟩ =>
    ⟨ws, hw, hR.imp fun _ _ h => h, by rw [hlenPV] at hww; exact hww, ?_⟩
  have hp1 : (Ps.map tmGlObjsVal).length = m := hlenPV
  have hq1 : ∀ K : ℕ, (Ps.map tmGlObjsVal).length * K = m * K := fun K => by rw [hp1]
  have hq2 : ∀ K : ℕ, mapK * ((Ps.map tmGlObjsVal).length + 1) * K = mapK * (m + 1) * K :=
    fun K => by rw [hp1]
  simp only [hq1, hq2] at hcw'
  have e0 : (Val.list [c, Val.list (List.map tmGlObjsVal Ps)]).wt = (Val.list [c, PV]).wt := rfl
  have hY : m * (m * Cp + mapK * (m + 1) * (10 * W + 20 + m * (1400 * (n + 1) ^ 6 + 1) + 5) +
      50 * W + 100 + m * (1400 * (n + 1) ^ 6 + 1)) = m * m * (M * (T + tmRiYC
        (solvableCosetIntersectionPrim hsci) n M (4 * (10 * W + 20) + 10))) +
      m * (m * tmRiPairC hmem n M (10 * W + 20) +
        mapK * (m + 1) * (10 * W + 20 + m * (1400 * (n + 1) ^ 6 + 1) + 5) + 50 * W + 100 +
        m * (1400 * (n + 1) ^ 6 + 1)) := by rw [hCp]; ring
  have h2 : mapK * (m + 1) * ((Val.list [c, PV]).wt + m * (2 * (m * (1400 * (n + 1) ^ 6 + 1) + 4) +
      1) + 5) ≤ mapK * (m + 1) * (W + m * (2 * (m * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) + 5) :=
    Nat.mul_le_mul_left _ (by omega)
  refine le_trans hcw' ?_
  unfold tmRiTabC
  rw [e0]
  omega

end GI.Impl
