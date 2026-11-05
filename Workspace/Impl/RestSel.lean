module

public import Workspace.Impl.Weights

@[expose] public section

/-!
# The rest of the selector of `Continue`

Above the phase threshold, Algorithm 5 asks two questions before it reaches the general
dispatcher: "if `G` is intransitive" (the orbit chain, case `1`) and "if the active column
floor has been entered" (the floor reset, case `2`). Otherwise the general dispatcher runs
(case `3`). This file decides both, on a canonical state value
`[k, gv, dv, xv, yv, hv, rv, floor, h, N]`.

1. **Transitivity.** The largest-orbit module (`loFuns`, `lo_spec`) returns the indicators of a
   largest orbit `D₁` and of `D \ D₁`. Since `D₁` is the orbit of a point of `D`, the group is
   transitive on `D` exactly when `D \ D₁` is empty (`transitive_iff_diff_empty`), that is, when
   the largest entry of its indicator (`maxFuns`) is `0`.
2. **The column floor.** `S.FloorEntered` asks that the floor flag is set, that a row record
   with a column partition is retained, and that the domain lies in one column. The first two
   are read off the value. For the last, the row test `splitFuns` (`split_spec`) answers `1`
   exactly when the columns split the domain (`State.ColsSplit`).

`restSel_spec`: the function meets `Iface.RestSelSpec` with the cost bound `restSelB`, a
polynomial in the weight bound `stateW` of the state value (`restSelB S = restSelK (stateW + 1)^15`).
No cited task is used.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### The program -/

/-- The floor test, in an environment whose first entry is the state value: `3` unless the
floor flag is set, a row record with a column partition is retained and the row test (at `bs`)
finds that the columns do not split the domain, in which case `2`. -/
def floorTestE (bs : ℕ) : Expr :=
  .ite (arg 7)
    (.ite (.length (arg 6))
      (.ite (.length (.get (.get (arg 6) (.nat 0)) (.nat 2)))
        (.ite (.call bs (mk2 (arg 6) (arg 2))) (.nat 3) (.nat 2))
        (.nat 3))
      (.nat 3))
    (.nat 3)

/-- **The rest of the selector of `Continue`**, with the largest-orbit module at `bl`, the
maximum at `bm` and the row test at `bs`. The environment grows as `[v, [ind D₁, ind (D \ D₁)]]`. -/
def restSelBody (bl bm bs : ℕ) : Expr :=
  .letE (.call bl (mk2 (arg 1) (arg 2)))
    (.ite (.call bm (.get (.var 1) (.nat 1))) (.nat 1) (floorTestE bs))

/-- The cost constant of the rest of the selector. -/
def restSelK : ℕ := 10 ^ 13

/-- **The cost bound of the rest of the selector**: `restSelK (stateW + 1)^15`. -/
noncomputable def restSelB {Ω C : Type} (S : State Ω C) : ℝ :=
  (restSelK : ℝ) * ((stateW (Nat.card Ω) S : ℝ) + 1) ^ 15

/-! ### Transitivity from a largest orbit -/

/-- A group is transitive on `D` exactly when the orbit `D₁ ⊆ D` of a point of `D` is all of
`D`. -/
theorem transitive_iff_diff_empty {S : State Ω C} {D₁ : Set Ω} (hsub : D₁ ⊆ S.dom)
    (horb : ∃ a ∈ S.dom, D₁ = {w | ∃ g ∈ S.G, g a = w}) :
    S.Transitive ↔ S.dom \ D₁ = ∅ := by
  obtain ⟨a, ha, rfl⟩ := horb
  constructor
  · intro htr
    rw [Set.diff_eq_empty]
    intro w hw
    exact htr a ha w hw
  · intro h v hv w hw
    have hsub' : S.dom ⊆ {w | ∃ g ∈ S.G, g a = w} := Set.diff_eq_empty.1 h
    obtain ⟨g, hg, rfl⟩ := hsub' hv
    obtain ⟨g', hg', rfl⟩ := hsub' hw
    exact ⟨g' * g⁻¹, S.G.mul_mem hg' (S.G.inv_mem hg), by simp⟩

open Classical in
/-- The largest entry of an indicator is `0` exactly when the set is empty. -/
theorem foldl_max_indF (e : Ω ≃ Fin k) (D : Set Ω) :
    ((List.finRange k).map (indF e D)).foldl max 0 = if D = ∅ then 0 else 1 := by
  rw [foldl_max_01 _ 0 (by omega) fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx; exact indF_le_one e D j]
  by_cases hD : D = ∅
  · rw [if_pos hD, if_neg]
    simp only [List.mem_map, List.mem_finRange, true_and, not_or, not_exists]
    refine ⟨by omega, fun i => ?_⟩
    simp [indF, hD]
  · rw [if_neg hD, if_pos]
    obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.2 hD
    refine Or.inr (List.mem_map.2 ⟨e v, List.mem_finRange _, ?_⟩)
    simp [indF, hv]

/-! ### The floor test -/

/-- The floor is entered exactly when the flag is set, a row record with a column partition is
retained, and the columns do not split the (nonempty) domain. -/
theorem floorEntered_iff {S : State Ω C} (hne : S.dom.Nonempty) :
    S.FloorEntered ↔ S.floor = true ∧ ∃ R, S.rows = some R ∧ ∃ c, R.cols = some c ∧
      ¬ S.ColsSplit S.dom := by
  constructor
  · rintro ⟨hf, R, hR, c, hc, v, hv, hall⟩
    refine ⟨hf, R, hR, c, hc, fun hs => ?_⟩
    obtain ⟨c', hc', w₁, hw₁, w₂, hw₂, hn⟩ := hs R hR
    rw [hc] at hc'
    cases hc'
    exact hn (c.trans (c.symm (hall w₁ hw₁)) (hall w₂ hw₂))
  · rintro ⟨hf, R, hR, c, hc, hns⟩
    obtain ⟨v, hv⟩ := hne
    refine ⟨hf, R, hR, c, hc, v, hv, fun w hw => ?_⟩
    by_contra hn
    exact hns fun R' hR' => by
      rw [hR] at hR'
      cases hR'
      exact ⟨c, hc, v, hv, w, hw, hn⟩

open Classical in
/-- **The floor test decides the floor.** In an environment whose first entry is a canonical
state value, the floor test returns `2` if the floor is entered and `3` otherwise. -/
theorem floorTest_det {Pg : Program} {bs : ℕ} (hsp : Pg.HasAt bs (splitFuns bs)) (e : Ω ≃ Fin k)
    (S : State Ω C) (hne : S.dom.Nonempty) {gv xv yv hv rv hh : Val} {N : ℕ} {rest : List Val}
    (hrv : OptVal (RowValC e) rv S.rows) :
    Det Pg (.list [.nat k, gv, indVal e S.dom, xv, yv, hv, rv, boolVal S.floor, hh, .nat N] ::
      rest) (floorTestE bs) (.nat (if S.FloorEntered then 2 else 3))
      (splitK * ((Val.list [rv, indVal e S.dom]).wt + 1) ^ 3 +
        40 * ((Val.list [.nat k, gv, indVal e S.dom, xv, yv, hv, rv, boolVal S.floor, hh,
          .nat N]).wt + 20)) := by
  set vs : List Val := [.nat k, gv, indVal e S.dom, xv, yv, hv, rv, boolVal S.floor, hh, .nat N]
    with hvs
  set W := (Val.list vs).wt with hW
  have ha : ∀ (j : ℕ) (v : Val), vs[j]? = some v →
      Det Pg (.list vs :: rest) (arg j) v (2 * W + 15) := fun j v h => by
    have hj : j < 10 := by
      by_contra hj
      rw [List.getElem?_eq_none (by simp [hvs]; omega)] at h
      cases h
    exact (Det.arg' (rest := rest) h).mono (by omega)
  have wRV : rv.wt < W := wt_le_wt_list (by simp [hvs])
  have wD : (indVal e S.dom).wt < W := wt_le_wt_list (by simp [hvs])
  have w3 : (Val.nat 3).wt ≤ 5 := (wt_nat_le 3).trans (by norm_num)
  have w2 : (Val.nat 2).wt ≤ 5 := (wt_nat_le 2).trans (by norm_num)
  have d3 : Det Pg (.list vs :: rest) (.nat 3) (.nat 3) 6 := Det.nat 3
  have d2 : Det Pg (.list vs :: rest) (.nat 2) (.nat 2) 5 := Det.nat 2
  have hfl := ha 7 (boolVal S.floor) rfl
  cases hf : S.floor with
  | false =>
    rw [hf] at hfl
    have hn : ¬ S.FloorEntered := fun h => by rw [(floorEntered_iff hne).1 h |>.1] at hf; cases hf
    rw [if_neg hn]
    refine (Det.ite_zero hfl d3).mono ?_
    omega
  | true =>
    rw [hf] at hfl
    have hrows := ha 6 rv rfl
    cases hR : S.rows with
    | none =>
      rw [hR] at hrv
      change rv = .list [] at hrv
      subst hrv
      have hn : ¬ S.FloorEntered := fun h => by
        obtain ⟨-, R, hR', -⟩ := (floorEntered_iff hne).1 h
        rw [hR] at hR'; cases hR'
      rw [if_neg hn]
      refine (Det.ite_pos hfl (by simp) (Det.ite_zero (Det.length hrows) d3)).mono ?_
      simp only [List.length_nil]
      omega
    | some R =>
      rw [hR] at hrv
      obtain ⟨u, ⟨rv', cv, hrows', hcols, rfl⟩, rfl⟩ := hrv
      have wu : (Val.list [.nat R.m, rv', cv]).wt < W :=
        (wt_le_wt_list (by simp)).trans wRV
      have wcv : cv.wt < W := (wt_le_wt_list (by simp)).trans wu
      have hu := Det.get' hrows (Det.nat 0) (v := .list [.nat R.m, rv', cv]) rfl
      have hcv := Det.get' hu (Det.nat 2) (v := cv) rfl
      have hl0 := Det.length hrows
      cases hc : R.cols with
      | none =>
        rw [hc] at hcols
        change cv = .list [] at hcols
        subst hcols
        have hn : ¬ S.FloorEntered := fun h => by
          obtain ⟨-, R', hR', c, hc', -⟩ := (floorEntered_iff hne).1 h
          rw [hR] at hR'; cases hR'
          rw [hc] at hc'; cases hc'
        rw [if_neg hn]
        refine (Det.ite_pos hfl (by simp) (Det.ite_pos hl0 (by simp)
          (Det.ite_zero (Det.length hcv) d3))).mono ?_
        simp only [List.length_nil, List.length_cons]
        omega
      | some c =>
        rw [hc] at hcols
        obtain ⟨lv, hlv, rfl⟩ := hcols
        have hspl := split_spec hsp e S (rv := .list [.list [.nat R.m, rv', .list [lv]]])
          (by rw [hR]; exact ⟨_, ⟨rv', .list [lv], hrows', by rw [hc]; exact ⟨lv, hlv, rfl⟩,
            rfl⟩, rfl⟩) hne
        have hcall := Det.call (Det.mk2 hrows (ha 2 (indVal e S.dom) rfl)) hspl
        have hiff : S.FloorEntered ↔ ¬ S.ColsSplit S.dom := by
          rw [floorEntered_iff hne]
          exact ⟨fun ⟨_, _, _, _, _, h⟩ => h, fun h => ⟨hf, R, hR, c, hc, h⟩⟩
        have hval : (if S.FloorEntered then 2 else 3 : ℕ) =
            if (if S.ColsSplit S.dom then 1 else 0 : ℕ) = 0 then 2 else 3 := by
          by_cases h : S.ColsSplit S.dom
          · rw [if_neg (fun h' => hiff.1 h' h), if_pos h]; rfl
          · rw [if_pos (hiff.2 h), if_neg h]; rfl
        have hfin := Det.ite' hcall d3 d2
        have heq : (if (if S.ColsSplit S.dom then 1 else 0 : ℕ) = 0 then Val.nat 2 else Val.nat 3) =
            Val.nat (if S.FloorEntered then 2 else 3) := by
          rw [hval]; split_ifs <;> rfl
        rw [heq] at hfin
        refine (Det.ite_pos hfl (by simp) (Det.ite_pos hl0 (by simp)
          (Det.ite_pos (Det.length hcv) (by simp) hfin))).mono ?_
        have wA := wt_list2_le (Val.list [.list [.nat R.m, rv', .list [lv]]]) (indVal e S.dom)
        have wv : (Val.nat (if S.ColsSplit S.dom then 1 else 0)).wt ≤ 3 := by
          split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
        have wv' : (Val.nat (if S.FloorEntered then 2 else 3)).wt ≤ 5 := by
          split_ifs
          · exact w2
          · exact w3
        have : max 6 5 = 6 := rfl
        have : max (Val.nat 3).wt (Val.nat 2).wt ≤ 5 := max_le w3 w2
        simp only [List.length_cons, List.length_nil] at *
        omega

/-! ### The specification -/

namespace Iface

variable (I : Iface) (Pg : Program)

/-- **The rest of the selector of `Continue` meets its specification** with the cost bound
`restSelB`. -/
theorem restSel_spec {f bl bm bs : ℕ} (hf : Pg.funs[f]? = some (restSelBody bl bm bs))
    (hlo : Pg.HasAt bl (loFuns bl)) (hmax : Pg.HasAt bm (maxFuns bm))
    (hsp : Pg.HasAt bs (splitFuns bs)) : I.RestSelSpec Pg f restSelB := by
  intro Ω C S k e c hc v hv hg hs
  classical
  have hv' : Canon e c v S := hv
  haveI : Finite Ω := Finite.of_equiv _ e.symm
  have hwv := hv'.wt_le
  have hk := card_eq e
  have hne := dom_nonempty_of_large hs
  obtain ⟨gv, dv, xv, yv, hv0, rv, hgv, hdv, hxv, hyv, hhv, hrv, hvv⟩ := hv'.val
  obtain ⟨gs, rfl, hgens, hl⟩ := hgv
  have hdv' : dv = indVal e S.dom := hdv
  subst hdv'
  obtain ⟨vs, hvs⟩ : ∃ vs : List Val, vs = [.nat k, encGroup gs, indVal e S.dom, xv, yv, hv0, rv,
    boolVal S.floor, .nat S.h, .nat S.N] := ⟨_, rfl⟩
  rw [← hvs] at hvv
  subst hvv
  -- The largest orbit.
  obtain ⟨D₁, hsub, horb, -, hloD⟩ := lo_spec hlo e S.dom_inv hne hgens hl
  have d1 := Det.call (Det.mk2 (Det.arg' (P := Pg) (vs := vs) (rest := []) (j := 1)
    (v := encGroup gs) (by rw [hvs]; rfl)) (Det.arg' (j := 2) (v := indVal e S.dom)
      (by rw [hvs]; rfl))) hloD
  -- The largest entry of the indicator of `D \ D₁`.
  have hmx := max_spec hmax (xs := (List.finRange k).map (indF e (S.dom \ D₁))) (B := k)
    (fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      have := indF_le_one e (S.dom \ D₁) j
      have : 1 ≤ k := by have := j.2; omega
      omega) (by simp)
  rw [foldl_max_indF] at hmx
  have hP := Det.var' (P := Pg) (env := [.list vs, .list [indVal e D₁, indVal e (S.dom \ D₁)]])
    (i := 1) (v := .list [indVal e D₁, indVal e (S.dom \ D₁)]) rfl
  have hI := Det.get' hP (Det.nat 1) (v := indVal e (S.dom \ D₁)) rfl
  have heqI : indVal e (S.dom \ D₁) = natList ((List.finRange k).map (indF e (S.dom \ D₁))) :=
    encFun_eq_natList _
  have d2 := Det.call hI (heqI ▸ hmx)
  have hftest := floorTest_det (rest := [.list [indVal e D₁, indVal e (S.dom \ D₁)]]) hsp e S hne
    (gv := encGroup gs) (xv := xv) (yv := yv) (hv := hv0) (hh := .nat S.h) (N := S.N) hrv
  rw [← hvs] at hftest
  have htr := transitive_iff_diff_empty hsub horb
  -- The value and the case.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = if S.dom \ D₁ = ∅ then (if S.FloorEntered then 2 else 3) else 1 :=
    ⟨_, rfl⟩
  have hcase : ∃ hjl : j < contCases.length, contCases[j].P e S (.list vs) := by
    subst hj
    by_cases hd : S.dom \ D₁ = ∅
    · have htr' : S.Transitive := htr.2 hd
      by_cases hfe : S.FloorEntered
      · simp only [if_pos hd, if_pos hfe]; exact ⟨by simp [contCases], hs, htr', hfe⟩
      · simp only [if_pos hd, if_neg hfe]; exact ⟨by simp [contCases], hs, htr', hfe⟩
    · simp only [if_neg hd]; exact ⟨by simp [contCases], hs, fun h => hd (htr.1 h)⟩
  have hbody := Det.ite' d2 (Det.nat (P := Pg)
    (env := [.list vs, .list [indVal e D₁, indVal e (S.dom \ D₁)]]) 1) hftest
  have hval : (if (if S.dom \ D₁ = ∅ then 0 else 1 : ℕ) = 0 then
      Val.nat (if S.FloorEntered then 2 else 3) else Val.nat 1) = Val.nat j := by
    rw [hj]; split_ifs <;> simp_all
  rw [hval] at hbody
  have hall := Det.letE d1 hbody
  obtain ⟨hjl, hjP⟩ := hcase
  refine FunAll.mono ((FunDet.intro hf hall).mono (c' := (restSelK * (stateW k S + 1) ^ 15 : ℕ))
    ?_) fun i cost hic => ⟨j, hjl, hic.1, hjP, ?_⟩
  · -- the cost
    have wvs : (Val.list vs).wt ≤ stateW k S := hwv
    have wD : ∀ D' : Set Ω, (indVal e D').wt ≤ k * 7 + 4 := fun D' =>
      DomVal.wt_le (domVal_indVal e D')
    have hkS : k * 7 + 4 ≤ stateW k S := by unfold stateW; omega
    have wG : (encGroup gs).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
    have wRV : rv.wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
    have wDd : (indVal e S.dom).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
    have wL := wt_list2_le (encGroup gs) (indVal e S.dom)
    have wP := wt_list2_le (indVal e D₁) (indVal e (S.dom \ D₁))
    have wD₁ := wD D₁
    have wD₂ := wD (S.dom \ D₁)
    have wSP := wt_list2_le rv (indVal e S.dom)
    have wmx : (Val.nat (if S.dom \ D₁ = ∅ then 0 else 1)).wt ≤ 3 := by
      split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
    have wj : (Val.nat j).wt ≤ 5 := by
      have := wt_nat_le j
      have : j ≤ 3 := by rw [hj]; split_ifs <;> omega
      omega
    have w1 := wt_nat_le 1
    have wfe : (Val.nat (if S.FloorEntered then 2 else 3)).wt ≤ 5 := by
      have := wt_nat_le (if S.FloorEntered then 2 else 3)
      split_ifs at this ⊢ <;> omega
    obtain ⟨X, hX⟩ : ∃ X, X = stateW k S + 1 := ⟨_, rfl⟩
    have hX1 : 1 ≤ X := by omega
    have p3 : X ^ 3 ≤ X ^ 15 := Nat.pow_le_pow_right hX1 (by norm_num)
    have p1 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) _
    have hk15 : (k + 1) ^ 15 ≤ X ^ 15 := Nat.pow_le_pow_left (by omega) _
    have hk3 : (k + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left (by omega) _
    have hsp3 : ((Val.list [rv, indVal e S.dom]).wt + 1) ^ 3 ≤ (5 * X) ^ 3 :=
      Nat.pow_le_pow_left (by omega) _
    have e5 : (5 * X) ^ 3 = 125 * X ^ 3 := by ring
    rw [e5] at hsp3
    have hm1 : maxK * (k + 1) ^ 3 ≤ maxK * X ^ 15 := Nat.mul_le_mul_left _ (hk3.trans p3)
    have hl1 : loK * (k + 1) ^ 15 ≤ loK * X ^ 15 := Nat.mul_le_mul_left _ hk15
    have hs1 : splitK * ((Val.list [rv, indVal e S.dom]).wt + 1) ^ 3 ≤
        splitK * 125 * X ^ 15 := by
      calc splitK * ((Val.list [rv, indVal e S.dom]).wt + 1) ^ 3 ≤ splitK * (125 * X ^ 3) :=
            Nat.mul_le_mul_left _ hsp3
        _ = splitK * 125 * X ^ 3 := by ring
        _ ≤ splitK * 125 * X ^ 15 := Nat.mul_le_mul_left _ p3
    have hX15 : X ≤ X ^ 15 := p1.trans p3
    rw [← hX]
    have hmx4 : ∀ a b : ℕ, max a b ≤ a + b := fun a b => max_le (by omega) (by omega)
    have := hmx4 (1 + 3) (splitK * ((Val.list [rv, indVal e S.dom]).wt + 1) ^ 3 + 40 *
      ((Val.list vs).wt + 20))
    have := hmx4 (Val.nat 1).wt (Val.nat (if S.FloorEntered then 2 else 3)).wt
    generalize hA : X ^ 15 = A at *
    generalize hB : splitK * ((Val.list [rv, indVal e S.dom]).wt + 1) ^ 3 = B at *
    generalize hC : (k + 1) ^ 15 = C' at *
    generalize hD : (k + 1) ^ 3 = D' at *
    simp only [restSelK, loK, maxK, splitK, Nat.reducePow, Nat.reduceMul] at *
    omega
  · -- the cost bound
    have := hic.2
    simp only [restSelB]
    rw [hk]
    exact_mod_cast this

end Iface

/-- The cost bound of the rest of the selector is polynomial in `N` on fitting states:
`restSelB S ≤ restSelK (10⁴ + 1)^15 (N + 2)^90`. -/
theorem restSelB_le {S : State Ω C} (hk : Nat.card Ω ≤ S.N) (hs : Small S) :
    restSelB S ≤ ((restSelK * (10 ^ 4 + 1) ^ 15 : ℕ) : ℝ) * ((S.N : ℝ) + 2) ^ 90 := by
  have h := succ_pow_le (by omega) (stateW_le_of_small hk hs) 15
  have h2 : (stateW (Nat.card Ω) S + 1) ^ 15 * restSelK ≤
      restSelK * (10 ^ 4 + 1) ^ 15 * (S.N + 2) ^ 90 := by
    have := Nat.mul_le_mul_right restSelK h
    have e : (10 ^ 4 + 1) ^ 15 * (S.N + 2) ^ (6 * 15) * restSelK =
      restSelK * (10 ^ 4 + 1) ^ 15 * (S.N + 2) ^ 90 := by ring
    omega
  have h3 : (((stateW (Nat.card Ω) S + 1) ^ 15 * restSelK : ℕ) : ℝ) ≤
      ((restSelK * (10 ^ 4 + 1) ^ 15 * (S.N + 2) ^ 90 : ℕ) : ℝ) := Nat.cast_le.mpr h2
  have e1 : (((stateW (Nat.card Ω) S + 1) ^ 15 * restSelK : ℕ) : ℝ) = restSelB S := by
    simp only [restSelB]; push_cast; ring
  have e2 : ((restSelK * (10 ^ 4 + 1) ^ 15 * (S.N + 2) ^ 90 : ℕ) : ℝ) =
      ((restSelK * (10 ^ 4 + 1) ^ 15 : ℕ) : ℝ) * ((S.N : ℝ) + 2) ^ 90 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  rw [← e1, ← e2]
  exact h3

/-- **The selector of `Continue` for the concrete interface**, with this rest of the selector:
when `R.restSelB` is `restSelB`, the selector meets its specification. -/
theorem Rest.contSel_built (R : Rest)
    (hR : ∀ {Ω C : Type} (S : State Ω C), R.restSelB S = GI.Impl.restSelB S)
    {Pg : Program} {b f bl bm bs : ℕ} (h : Pg.HasAt b (contSelFuns b f))
    (hf : Pg.funs[f]? = some (restSelBody bl bm bs)) (hlo : Pg.HasAt bl (loFuns bl))
    (hmax : Pg.HasAt bm (maxFuns bm)) (hsp : Pg.HasAt bs (splitFuns bs)) :
    R.iface.SelSpec Pg .cont Iface.contCases b := by
  have hrest : R.iface.RestSelSpec Pg f GI.Impl.restSelB := R.iface.restSel_spec Pg hf hlo hmax hsp
  have hrest' : R.iface.RestSelSpec Pg f R.restSelB := by
    intro Ω C S k e c hc v hv hg hs
    refine (hrest S k e c hc v hv hg hs).mono fun i cost ⟨j, hj, hi, hP, hcost⟩ =>
      ⟨j, hj, hi, hP, ?_⟩
    show (cost : ℝ) ≤ R.restSelB S
    rw [hR]; exact hcost
  exact @Rest.contSel R Pg b f h hrest'

end GI.Impl
