import Workspace.Impl.TermRecProgTab

/-!
# T5, one profile

`tmRi_prof_spec`: on `[[gens A, table, o], i]` the function `b + 13` returns the profile of the
piece `P_j`, `j = o + i`: the object `[r, gens (A ⊔ Aut_H(P_r)), t]`, where `r` is the first
index with `Iso_H(P_r, P_j) ≠ ∅` and `t ∈ Iso_H(P_r, P_j)`. By `tmRec_prof_coset` this is the
coset object `A · Iso_H(P_r, P_j)` with color `r`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open scoped Pointwise
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

theorem tmRi_objsVal_inj {S S' : List (TmRiO n)} (h : tmGlObjsVal S = tmGlObjsVal S') : S = S' := by
  simp only [tmGlObjsVal, Val.list.injEq] at h
  exact List.map_injective_iff.2 (fun _ _ e => tmRi_objVal_inj e) h

/-- **An entry of the table**, by position. -/
theorem tmRi_tab_get {H : Subgroup (Perm (Fin n))} {Ps : List (List (TmRiO n))} {tab : List Val}
    (ht : TmRiTab H Ps tab) {k j : ℕ} (hk : k < Ps.length) (hj : j < Ps.length) :
    ∃ us, tab[k]? = some (.list us) ∧ us.length = Ps.length ∧ ∃ u, us[j]? = some u ∧
      CosetC n u (Iso H (tmGlMs (Ps.getD k [])) (tmGlMs (Ps.getD j []))) := by
  have hl := ht.length_eq
  rw [List.length_map] at hl
  have hk' : k < tab.length := hl ▸ hk
  have hR := (List.forall₂_iff_get.1 ht).2 k (by simpa using hk) hk'
  simp only [List.get_eq_getElem, List.getElem_map] at hR
  obtain ⟨S, -, hS, us, hus, hR'⟩ := hR
  have hS' : S = Ps.getD k [] := by
    rw [List.getD_eq_getElem _ _ hk]; exact (tmRi_objsVal_inj hS).symm
  have hul := hR'.length_eq
  rw [List.length_map] at hul
  have hj' : j < us.length := hul ▸ hj
  have hR2 := (List.forall₂_iff_get.1 hR').2 j (by simpa using hj) hj'
  simp only [List.get_eq_getElem, List.getElem_map] at hR2
  obtain ⟨T, -, hT, hc⟩ := hR2
  have hT' : T = Ps.getD j [] := by
    rw [List.getD_eq_getElem _ _ hj]; exact (tmRi_objsVal_inj hT).symm
  refine ⟨us, by rw [List.getElem?_eq_getElem hk', hus], hul.symm, us[j], List.getElem?_eq_getElem hj', ?_⟩
  rw [← hS', ← hT']; exact hc

/-- The column test on a row: whether entry `j` is a nonempty list. -/
def tmRiColQ (j : ℕ) : Val → Bool
  | .list us => match us[j]? with
    | some (.list (_ :: _)) => true
    | _ => false
  | _ => false

open Classical in
theorem tmRi_colQ_eq {us : List Val} {j : ℕ} {u : Val} (hu : us[j]? = some u)
    {C : Set (Perm (Fin n))} (hc : CosetC n u C) : tmRiColQ j (.list us) = decide C.Nonempty := by
  simp only [tmRiColQ, hu]
  rcases hc with ⟨rfl, rfl⟩ | ⟨x, hs, rfl, -, rfl⟩
  · simp
  · have : (x • (gens hs : Set (Perm (Fin n)))).Nonempty := ⟨x, 1, (gens hs).one_mem, mul_one x⟩
    simp [this]

theorem tmRi_gens_one (hs : List (Perm (Fin n))) : gens (1 :: hs) = gens hs := by
  simp only [gens, List.mem_cons]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono fun g hg => Or.inr hg

/-- The generators of the answer for `(R, R)` generate `Aut_H(R)`. -/
theorem tmRi_aut_gens {Ω : Type} [RAct (Perm (Fin n)) Ω] {H : Subgroup (Perm (Fin n))} {R : Ω}
    {x : Perm (Fin n)} {hs : List (Perm (Fin n))}
    (h : Iso H R R = x • (gens hs : Set (Perm (Fin n)))) : gens hs = Aut H R := by
  have hx : x ∈ Aut H R := by
    have : x ∈ x • (gens hs : Set (Perm (Fin n))) := ⟨1, (gens hs).one_mem, mul_one x⟩
    rw [← h] at this; exact this
  ext g
  constructor
  · intro hg
    have : x * g ∈ Iso H R R := by rw [h]; exact ⟨g, hg, rfl⟩
    have := (Aut H R).mul_mem ((Aut H R).inv_mem hx) this
    rwa [inv_mul_cancel_left] at this
  · intro hg
    have : x * g ∈ Iso H R R := (Aut H R).mul_mem hx hg
    rw [h] at this
    obtain ⟨g', hg', e⟩ := this
    rwa [mul_left_cancel e] at hg'

/-- **The column test** on `[j, row]`. -/
theorem tmRi_colP_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {us : List Val} {j : ℕ} {u : Val}
    (hu : us[j]? = some u) {C : Set (Perm (Fin n))} (hc : CosetC n u C) :
    FunDet P (b + 14) (.list [.nat j, .list us]) (boolVal (tmRiColQ j (.list us)))
      (10 * (Val.list [.nat j, .list us]).wt + 40) := by
  set vs : List Val := [.nat j, .list us]
  have hul : (Val.list us).wt < (Val.list vs).wt := wt_le_wt_list (by simp [vs])
  have huw : u.wt < (Val.list us).wt := wt_le_wt_list (List.mem_of_getElem? hu)
  have h1 : (Val.nat 1).wt ≤ 3 := by decide
  have h0 : (Val.nat 0).wt ≤ 3 := by decide
  rcases hc with ⟨rfl, rfl⟩ | ⟨x, hs, rfl, -, rfl⟩
  · have d := tmRi_ite (Det.length (Det.get' (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl)
      (Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl) (v := .list []) hu))
      (Det.nat (P := P) (env := [.list vs]) 1) (Det.nat (P := P) (env := [.list vs]) 0)
    have e : tmRiColQ j (.list us) = false := by simp [tmRiColQ, hu]
    rw [e]
    refine FunDet.intro hP.colP (d.mono ?_)
    simp only [List.length_nil]
    omega
  · have d := tmRi_ite (Det.length (Det.get' (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl)
      (Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl) hu))
      (Det.nat (P := P) (env := [.list vs]) 1) (Det.nat (P := P) (env := [.list vs]) 0)
    have e : tmRiColQ j (.list us) = true := by simp [tmRiColQ, hu]
    rw [e]
    refine FunDet.intro hP.colP (d.mono ?_)
    simp only [List.length_cons, List.length_nil]
    omega

/-- The cost bound of one profile, for an argument of weight at most `Wa`. -/
noncomputable def tmRiProfC (hm : Membership) (n Wa : ℕ) : ℕ :=
  reduceCost hm n (2 * n ^ 2 + 1) + 10 ^ 6 * (Wa + 1) ^ 2 + 10 ^ 7 * (n + 1) ^ 8

/-- What the profile of `P_j` is: color `r`, the first index with `Iso_H(P_r, P_j) ≠ ∅`,
generators of `A ⊔ Aut_H(P_r)`, and a point `t ∈ Iso_H(P_r, P_j)`. -/
def TmRiProfOut (H A : Subgroup (Perm (Fin n))) (Ps : List (List (TmRiO n))) (j : ℕ)
    (o : TmRiO n) : Prop :=
  o.1 < Ps.length ∧ (Iso H (tmGlMs (Ps.getD o.1 [])) (tmGlMs (Ps.getD j []))).Nonempty ∧
    (∀ k < o.1, Iso H (tmGlMs (Ps.getD k [])) (tmGlMs (Ps.getD j [])) = ∅) ∧
    gens o.2.1 = A ⊔ Aut H (tmGlMs (Ps.getD o.1 [])) ∧ o.2.1.length ≤ n ^ 2 ∧
    o.2.2 ∈ Iso H (tmGlMs (Ps.getD o.1 [])) (tmGlMs (Ps.getD j []))

theorem tmRi_sq_le (W : ℕ) : 3 * W + 3 ≤ (W + 1) ^ 2 + 2 := by
  have := Nat.le_mul_self W
  have e : (W + 1) ^ 2 = W * W + 2 * W + 1 := by ring
  omega

set_option maxHeartbeats 1000000 in
open Classical in
/-- **One profile.** -/
theorem tmRi_prof_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {σA : List (Perm (Fin n))}
    (hAl : σA.length ≤ n ^ 2) {H : Subgroup (Perm (Fin n))} {Ps : List (List (TmRiO n))}
    {tab : List Val} (ht : TmRiTab H Ps tab) {o i : ℕ} (hj : o + i < Ps.length) :
    FunAll P (b + 13) (.list [.list [encGroup σA, .list tab, .nat o], .nat i])
      (fun w cost => (∃ ob, w = tmGlObjVal ob ∧ TmRiProfOut H (gens σA) Ps (o + i) ob) ∧
        cost ≤ tmRiProfC hmem n (Val.list [.list [encGroup σA, .list tab, .nat o], .nat i]).wt) := by
  set c0 : Val := .list [encGroup σA, .list tab, .nat o] with hc0
  set a : Val := .list [c0, .nat i] with ha
  set Wa := a.wt with hWa
  set j := o + i with hjdef
  have hc0a : c0.wt < Wa := wt_le_wt_list (by simp [ha])
  have hta : (Val.list tab).wt < Wa := by
    have : (Val.list tab).wt < c0.wt := wt_le_wt_list (by simp [hc0]); omega
  have hAa : (encGroup σA).wt < Wa := by
    have : (encGroup σA).wt < c0.wt := wt_le_wt_list (by simp [hc0]); omega
  have hlen : tab.length = Ps.length := by
    have h := List.Forall₂.length_eq ht
    rw [List.length_map] at h
    exact h.symm
  have htl : tab.length < (Val.list tab).wt := length_lt_wt_list tab
  have hjW : j < Wa := by omega
  -- the rows
  have hrow : ∀ k < Ps.length, ∃ us, tab[k]? = some (.list us) ∧ us.length = Ps.length ∧
      ∀ j' < Ps.length, ∃ u, us[j']? = some u ∧
        CosetC n u (Iso H (tmGlMs (Ps.getD k [])) (tmGlMs (Ps.getD j' []))) := by
    intro k hk
    obtain ⟨us, hus, hl, -⟩ := tmRi_tab_get ht hk hk
    refine ⟨us, hus, hl, fun j' hj' => ?_⟩
    obtain ⟨us', hus', -, u, hu, hc⟩ := tmRi_tab_get ht hk hj'
    rw [hus] at hus'
    cases hus'
    exact ⟨u, hu, hc⟩
  have hq : ∀ k (hk : k < tab.length), tmRiColQ j tab[k] =
      decide (Iso H (tmGlMs (Ps.getD k [])) (tmGlMs (Ps.getD j []))).Nonempty := by
    intro k hk
    obtain ⟨us, hus, -, hu⟩ := hrow k (hlen ▸ hk)
    obtain ⟨u, hu, hc⟩ := hu j hj
    rw [List.getElem?_eq_getElem hk] at hus
    rw [Option.some.inj hus]
    exact tmRi_colQ_eq hu hc
  obtain ⟨r, hr⟩ : ∃ r, r = tab.findIdx (tmRiColQ j) := ⟨_, rfl⟩
  have hjt : j < tab.length := hlen ▸ hj
  have hqj : tmRiColQ j tab[j] = true := by
    rw [hq j hjt, decide_eq_true_eq]
    exact ⟨1, H.one_mem, act_one _⟩
  have hrj : r ≤ j := hr ▸ tmRi_findIdx_le hjt hqj
  have hrt : r < tab.length := by omega
  have hrP : r < Ps.length := by omega
  have hqr : tmRiColQ j tab[r] = true := by subst hr; exact List.findIdx_getElem
  have hne : (Iso H (tmGlMs (Ps.getD r [])) (tmGlMs (Ps.getD j []))).Nonempty := by
    have := hq r hrt; rw [hqr] at this; exact of_decide_eq_true this.symm
  have hlt : ∀ k < r, Iso H (tmGlMs (Ps.getD k [])) (tmGlMs (Ps.getD j [])) = ∅ := by
    intro k hk
    have hkt : k < tab.length := by omega
    have h1 : tmRiColQ j (tab[k]'hkt) = false :=
      List.not_of_lt_findIdx (show k < tab.findIdx (tmRiColQ j) by omega)
    rw [hq k hkt] at h1
    exact Set.not_nonempty_iff_eq_empty.1 (of_decide_eq_false h1)
  -- the row of `r` and its entries `(r, r)` and `(r, j)`
  obtain ⟨us, hus, husl, hu⟩ := hrow r hrP
  obtain ⟨urr, hurr, hcrr⟩ := hu r hrP
  obtain ⟨urj, hurj, hcrj⟩ := hu j hj
  have hrr1 : (Iso H (tmGlMs (Ps.getD r [])) (tmGlMs (Ps.getD r []))).Nonempty :=
    ⟨1, H.one_mem, act_one _⟩
  obtain ⟨x', hs', rfl, hs'l, hx'⟩ := hcrr.resolve_left fun h => by
    rw [h.2] at hrr1; exact Set.not_nonempty_empty hrr1
  obtain ⟨x, hs, rfl, hsl, hx⟩ := hcrj.resolve_left fun h => by
    rw [h.2] at hne; exact Set.not_nonempty_empty hne
  have hrow_w : (Val.list us).wt < (Val.list tab).wt := wt_le_wt_list (List.mem_of_getElem? hus)
  have hrr_w : (Val.list [encPerm x', encGroup hs']).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? hurr)
  have hrj_w : (Val.list [encPerm x, encGroup hs]).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? hurj)
  have hrr_t : (Val.list [encPerm x', encGroup hs']).wt < Wa := by omega
  have hrj_t : (Val.list [encPerm x, encGroup hs]).wt < Wa := by omega
  have hus_t : (Val.list us).wt < Wa := by omega
  -- the program
  set vs : List Val := [c0, .nat i] with hvs
  have dj := Det.arith' (op := .add) (Det.get' (Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl)
    (Det.nat 2) (v := .nat o) rfl) (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl)
    (z := j) rfl
  -- the find
  set e1 : List Val := [a, .nat j] with he1
  have hcol : ∀ x ∈ tab, FunDet P (b + 14) (.list [.nat j, x]) (boolVal (tmRiColQ j x))
      (40 * Wa + 200) := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨us', hus', hl', hu'⟩ := hrow k (hlen ▸ hk)
    rw [List.getElem?_eq_getElem hk] at hus'
    rw [Option.some.inj hus']
    obtain ⟨u, hu, hc⟩ := hu' j hj
    refine (tmRi_colP_spec hP hu hc).mono ?_
    have h1 := wt_list2_le (.nat j) (.list us')
    have h2 : (Val.list us').wt < (Val.list tab).wt := by
      rw [← Option.some.inj hus']; exact wt_le_wt_list (List.getElem_mem hk)
    have h3 := wt_nat_le j
    omega
  have hfind := (find_spec hP.findC (c := .nat j) hcol).mono (Q' := fun w cw => w = .nat r ∧
      cw ≤ 10 ^ 5 * (Wa + 1) ^ 2) fun w cw ⟨hw, hcw⟩ => ⟨by rw [hw, hr], by
    have hs := tmRi_sum_const tab (fun _ => 40 * Wa + 200) (K := 40 * Wa + 200) fun _ _ => le_rfl
    have h1 := wt_list2_le (.nat j) (.list tab)
    have h3 := wt_nat_le j
    have h4 : tab.length * (40 * Wa + 200) ≤ (Wa + 1) * (40 * Wa + 200) :=
      Nat.mul_le_mul_right _ (by omega)
    have h5 : loopModK * (tab.length + 1) * ((Val.list [.nat j, .list tab]).wt + 2 * tab.length + 3) ≤
        1000 * ((Wa + 1) * (10 * Wa + 20)) := by
      rw [mul_assoc]; simp only [loopModK]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have h6 : (Wa + 1) * (40 * Wa + 200) + 1000 * ((Wa + 1) * (10 * Wa + 20)) ≤
        10 ^ 5 * (Wa + 1) ^ 2 := by nlinarith
    omega⟩
  have dr := Det.call (Det.mk2 (Det.var' (P := P) (env := e1) (i := 1) rfl)
    (Det.get' (Det.arg' (P := P) (vs := vs) (rest := [.nat j]) (j := 0) rfl) (Det.nat 1)
      (v := .list tab) rfl)) hfind
  -- the answer for `(r, r)`
  set e2 : List Val := [a, .nat j, .nat r] with he2
  have d3 := Det.get' (Det.get' (Det.get' (Det.arg' (P := P) (vs := vs) (rest := [.nat j, .nat r])
    (j := 0) rfl) (Det.nat 1) (v := .list tab) rfl) (Det.var' (P := P) (env := e2) (i := 2) rfl)
    hus) (Det.var' (P := P) (env := e2) (i := 2) rfl) hurr
  -- the group `A ⊔ Aut_H(P_r)`
  set ans := Val.list [encPerm x', encGroup hs'] with hans
  set e3 : List Val := [a, .nat j, .nat r, ans] with he3
  have dA := Det.get' (Det.arg' (P := P) (vs := vs) (rest := [.nat j, .nat r, ans]) (j := 0) rfl)
    (Det.nat 0) (v := encGroup σA) rfl
  have dn := Det.get' dA (Det.nat 0) (v := .nat n) rfl
  have dgA := Det.get' dA (Det.nat 1) (v := .list ((1 :: σA).map encPerm)) rfl
  have dgs := Det.get' (Det.get' (Det.var' (P := P) (env := e3) (i := 3) rfl) (Det.nat 1)
    (v := encGroup hs') rfl) (Det.nat 1) (v := .list ((1 :: hs').map encPerm)) rfl
  have dapp := Det.call (Det.mk2 dgA dgs) (tmRi_append_det hP.app _ _)
  have happ : Val.list (List.map encPerm (1 :: σA) ++ List.map encPerm (1 :: hs')) =
      .list ((1 :: (σA ++ 1 :: hs')).map encPerm) := by simp
  rw [happ] at dapp
  have dgrp := Det.mk2 dn dapp
  have hgrp : Val.list [.nat n, .list ((1 :: (σA ++ 1 :: hs')).map encPerm)] =
      encGroup (σA ++ 1 :: hs') := by simp [encGroup, GI.Cited.encPerms]
  rw [hgrp] at dgrp
  have dred := Det.call dgrp (reduce_spec hmem hP.red hP.mem (σA ++ 1 :: hs'))
  -- the profile
  set K := keepList (σA ++ 1 :: hs') with hK
  set e4 : List Val := [a, .nat j, .nat r, ans, encGroup K] with he4
  have dfin := Det.mk3 (Det.var' (P := P) (env := e4) (i := 2) rfl)
    (Det.var' (P := P) (env := e4) (i := 4) rfl)
    (Det.get' (Det.get' (Det.get' (Det.get' (Det.arg' (P := P) (vs := vs) (rest := [.nat j, .nat r, ans,
      encGroup K]) (j := 0) rfl) (Det.nat 1) (v := .list tab) rfl)
      (Det.var' (P := P) (env := e4) (i := 2) rfl) hus)
      (Det.var' (P := P) (env := e4) (i := 1) rfl) hurj) (Det.nat 0) (v := encPerm x) rfl)
  have dall := Det.letE dj (Det.letE dr (Det.letE d3 (Det.letE dred dfin)))
  refine FunAll.intro hP.prof (EvalAll.mono dall fun w cw ⟨hw, hcw⟩ => ⟨⟨(r, K, x), hw, ?_⟩, ?_⟩)
  · refine ⟨hrP, hne, hlt, ?_, length_keepList_le _, ?_⟩
    · show gens (keepList _) = _
      rw [gens_keepList, tmRi_gens_append, tmRi_gens_one, tmRi_aut_gens hx']
    · rw [hx]; exact ⟨1, (gens hs).one_mem, mul_one x⟩
  · have hno : (Val.nat o).wt < Wa := by
      have : (Val.nat o).wt < c0.wt := wt_le_wt_list (by simp [hc0]); omega
    have hni : (Val.nat i).wt < Wa := wt_le_wt_list (by simp [ha])
    have hnj := wt_nat_le j
    have hnr := wt_nat_le r
    have hnn : (Val.nat n).wt < (encGroup σA).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
    have hxs : (Val.list ((1 :: σA).map encPerm)).wt < (encGroup σA).wt :=
      wt_le_wt_list (vs := [.nat n, _]) (by simp)
    have hys : (Val.list ((1 :: hs').map encPerm)).wt < (encGroup hs').wt :=
      wt_le_wt_list (vs := [.nat n, _]) (by simp)
    have hgs' : (encGroup hs').wt < ans.wt := wt_le_wt_list (by simp [hans])
    have hx'w : (encPerm x').wt < ans.wt := wt_le_wt_list (by simp [hans])
    have hxw : (encPerm x).wt < (Val.list [encPerm x, encGroup hs]).wt := wt_le_wt_list (by simp)
    have hwA := wt_encGroup_le_sq hAl
    have hwh := wt_encGroup_le_sq hs'l
    have hwK := wt_encGroup_le_sq (length_keepList_le (σA ++ 1 :: hs'))
    have hpx := wt_encPerm_le x
    have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hn2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
    have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    have hl : (σA ++ 1 :: hs').length ≤ 2 * n ^ 2 + 1 := by simp; omega
    have hT : ((σA ++ 1 :: hs').length + 2) * (n + 1) ≤ 3 * (n + 1) ^ 3 := by
      calc _ ≤ 3 * (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_right _ (by omega)
        _ = 3 * (n + 1) ^ 3 := by ring
    have hT2 : (((σA ++ 1 :: hs').length + 2) * (n + 1)) ^ 2 ≤ 9 * (n + 1) ^ 6 := by
      calc _ ≤ (3 * (n + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left hT 2
        _ = 9 * (n + 1) ^ 6 := by ring
    have hG2 := wt_encGroup_le (σA ++ 1 :: hs')
    have hL2 := wt_list_encPerms_le (1 :: (σA ++ 1 :: hs'))
    simp only [List.length_cons] at hL2
    have hL2' : (Val.list ((1 :: (σA ++ 1 :: hs')).map encPerm)).wt ≤ 117 * (n + 1) ^ 6 := by
      have : ((σA ++ 1 :: hs').length + 1 + 1) = (σA ++ 1 :: hs').length + 2 := rfl
      rw [this] at hL2; omega
    have hw2 := wt_list2_le (.list ((1 :: σA).map encPerm)) (.list ((1 :: hs').map encPerm))
    have hlm : loopModK * ((List.map encPerm (1 :: hs')).length + 1) *
        ((Val.list [Val.list (List.map encPerm (1 :: σA)), Val.list (List.map encPerm (1 :: hs'))]).wt +
          (List.map encPerm (1 :: hs')).length +
          (Val.list (List.map encPerm (1 :: (σA ++ 1 :: hs')))).wt + 1) ≤ 4 * 10 ^ 6 * (n + 1) ^ 8 := by
      rw [mul_assoc, List.length_map, List.length_cons]
      calc _ ≤ loopModK * (2 * (n + 1) ^ 2 * (2000 * (n + 1) ^ 6)) := by
            refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
        _ = 4 * 10 ^ 6 * (n + 1) ^ 8 := by simp only [loopModK]; ring
    have hrc := reduceCost_mono hmem n hl
    have hWsq : 3 * Wa + 3 ≤ (Wa + 1) ^ 2 + 2 := tmRi_sq_le Wa
    have hwo := wt_list3_le (.nat r) (encGroup K) (encPerm x)
    have hw4 := wt_list2_le (.nat n) (.list ((1 :: (σA ++ 1 :: hs')).map encPerm))
    have hw5 := wt_list2_le (.nat j) (.list tab)
    have ev : (Val.list vs).wt = Wa := rfl
    have ea : (Val.list [encPerm x', encGroup hs']).wt = ans.wt := rfl
    have eK : (encGroup K).wt = (encGroup (keepList (σA ++ 1 :: hs'))).wt := rfl
    unfold tmRiProfC
    omega

end GI.Impl
