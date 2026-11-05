module

public import Workspace.Impl.AggCaseProg
public import Workspace.Impl.AggItemRound

@[expose] public section

/-!
# The source tuple of Case 2b, as a program

In Case 2b the items take as source tuple the eight smallest points of the dominant orbit `Φ` of
`π(F_x)`, followed by the smallest point again (`stSrc2b`, the choice `itSrc`). This file computes
it in two steps.

1. `itDomF` on `encGroup gs`: the dominant points of `⟨gs⟩` in increasing order, that is the
   sorted list of `domSet ⟨gs⟩` (`it_dom_spec`). It runs the first three steps of the case test
   (`acpCaseF`): orbit labels, the list `[0, …, n-1]`, and the filter by the dominance test.
2. `itS2bF` on the sorted list of `Φ` (with at least eight points): its first eight entries, then
   `κ - 7` copies of its first entry (`it_s2b_spec`). The result is the list of the entries of
   `stSrc2b Φ` on `κ + 1` positions (`it_s2b_eq`).

No primitive is called besides those of the orbit program (none).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms gens encGroup encPts)

variable {n : ℕ}

/-! ### The sorted dominant points -/

/-- The dominant points of the list form are the sorted dominant orbit. -/
theorem it_acDom_sort {gs : List (Perm (Fin n))} {lab : Fin n → ℕ}
    (hlab : ∀ x y, lab x = lab y ↔ y ∈ genOrbit (1 :: gs) x) :
    acDom lab = (domSet (gens gs)).sort := by
  rw [ac_domSet (gs := 1 :: gs) (gens_one_cons gs) hlab]
  have hs : (acDom lab).SortedLT := List.sortedLT_iff_pairwise.2
    ((List.sortedLT_iff_pairwise.1 (List.sortedLT_finRange n)).filter _)
  exact hs.eq_of_mem_iff (Finset.sortedLT_sort (acDom lab).toFinset) fun a => by simp

/-- On `encGroup gs`: the dominant points of `⟨gs⟩`, in increasing order. -/
def itDomF (orb rng fd : ℕ) : Expr :=
  .letE (.call orb (.var 0))
    (.letE (.call rng (.get (.var 0) (.nat 0)))
      (.call fd (mk2 (mk2 (.get (.var 0) (.nat 0)) (.var 1)) (.var 2))))

/-- The cost bound of `itDomF` on a group value of weight `G`. -/
def itDomC (G : ℕ) : ℕ := 10 ^ 9 * (G + 1) ^ 6

theorem itDomC_mono {a b : ℕ} (h : a ≤ b) : itDomC a ≤ itDomC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)

set_option maxHeartbeats 1000000 in
/-- **The sorted dominant orbit as a program.** -/
theorem it_dom_spec {P : Program} {f orb rng fd pd cnt : ℕ}
    (hf : P.funs[f]? = some (itDomF orb rng fd)) (horb : P.HasAt orb (orbitFuns orb))
    (hrng : P.HasAt rng (rangeFuns rng)) (hfd : P.HasAt fd (filterFuns fd pd))
    (hpd : P.funs[pd]? = some (acpDomF cnt)) (hcnt : P.HasAt cnt (countFuns cnt))
    (gs : List (Perm (Fin n))) :
    FunDet P f (encGroup gs) (encPts (domSet (gens gs)).sort) (itDomC (encGroup gs).wt) := by
  obtain ⟨lab, hO1, hlab, hlt⟩ := orbits_spec horb (1 :: gs)
  have hlab' : ∀ x, lab x < n := fun x => (hlt x).1
  rw [← it_acDom_sort hlab]
  obtain ⟨G, hGdef⟩ : ∃ G, G = (encGroup gs).wt := ⟨_, rfl⟩
  have hSG : (gs.length + 2) * (n + 1) ≤ G := hGdef ▸ S_le_wt_encGroup gs
  have hnG : n + 1 ≤ G := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hSG
  obtain ⟨W, hWdef⟩ : ∃ W, W = 100 * (G + 1) ^ 2 := ⟨_, rfl⟩
  have hn2 : (n + 1) ^ 2 ≤ (G + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hG2 : G + 1 ≤ (G + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have hlabw : (encFun lab).wt ≤ 4 * (n + 1) ^ 2 := wt_encFun_le_sq lab fun x => (hlab' x).le
  have hrw : (natList (List.range n)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (B := n) (fun x hx => (List.mem_range.1 hx).le) (by simp)
  have hnw := wt_nat_le n
  have egv : (Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt = (encGroup gs).wt := rfl
  have hcw := wt_list2_le (.nat n) (encFun lab)
  have hcw2 := wt_list2_le (.list [.nat n, encFun lab]) (natList (List.range n))
  have hdw := acp_wt_filter (n := n) (acpDomQ lab)
  rw [acp_filter_dom] at hdw
  have d0 : StDC P [encGroup gs] (.var 0) (encGroup gs) 1 0 W := StDC.var' rfl (by omega)
  have d1 := StDC.call d0 hO1 (by omega)
  refine FunDet.intro hf ?_
  have dn : ∀ rest : List Val,
      StDC P (encGroup gs :: rest) (.get (.var 0) (.nat 0)) (.nat n) 3 0 W :=
    fun rest => StDC.get (StDC.var' (v := Val.list [.nat n, .list ((1 :: gs).map encPerm)]) rfl
      (by omega)) (StDC.nat 0 (by omega)) rfl (by omega)
  have hR : FunDet P rng (.nat n) (natList (List.range n))
      (loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)) :=
    (range_spec hrng n).mono fun w c ⟨h1, h2⟩ => ⟨h1, h1 ▸ h2⟩
  have d2 := StDC.call (dn [encFun lab]) hR (by omega)
  set E3 : List Val := [encGroup gs, encFun lab, natList (List.range n)] with hE3
  have dctx : StDC P E3 (mk2 (mk2 (.get (.var 0) (.nat 0)) (.var 1)) (.var 2))
      (.list [.list [.nat n, encFun lab], natList (List.range n)]) 11 0 W :=
    (StDC.mk2 (StDC.mk2 (dn _) (StDC.var' (i := 1) rfl (by omega)) (by omega) (by omega))
      (StDC.var' (i := 2) rfl (by omega)) (by omega) (by omega)).mono (by omega) le_rfl
  have hxs : natList (List.range n) = .list ((List.range n).map Val.nat) := rfl
  have hFd := filter_spec hfd (c := .list [.nat n, encFun lab]) (xs := (List.range n).map Val.nat)
    (q := acpDomQ lab) (B := fun _ => acpTB n (Val.list [.nat n, encFun lab]).wt) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact acp_dom_det hpd hcnt hlab' (List.mem_range.1 hi))
  rw [← hxs] at hFd
  set CF := (((List.range n).map Val.nat).map
      fun _ => acpTB n (Val.list [.nat n, encFun lab]).wt).sum with hCF
  have hFd' : FunDet P fd (.list [.list [.nat n, encFun lab], natList (List.range n)])
      (encPts (acDom lab)) (CF + loopModK * (((List.range n).map Val.nat).length + 1) *
        ((Val.list [.list [.nat n, encFun lab], natList (List.range n)]).wt +
          ((List.range n).map Val.nat).length + (encPts (acDom lab)).wt + 1)) :=
    hFd.mono fun w c ⟨h1, h2⟩ => by
      rw [acp_filter_dom] at h1; subst h1; exact ⟨rfl, h2⟩
  have d3 := StDC.call dctx hFd' (by omega)
  have dall := StDC.letE d1 (StDC.letE d2 d3 (by omega)) (by omega)
  refine dall.det.mono ?_
  -- the cost
  have hlen : (List.map Val.nat (List.range n)).length = n := by simp
  have hl1 : (1 :: gs).length + 1 = gs.length + 2 := by simp
  have hX1 : 1 ≤ G + 1 := by omega
  have p23 : (G + 1) ^ 2 ≤ (G + 1) ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have p36 : (G + 1) ^ 3 ≤ (G + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p46 : (G + 1) ^ 4 ≤ (G + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p56 : (G + 1) ^ 5 ≤ (G + 1) ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have hOrb : orbitK * (((1 :: gs).length + 1) * (n + 1)) ^ 5 ≤ 1000000 * (G + 1) ^ 6 := by
    rw [hl1]
    show 1000000 * _ ≤ _
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) 5).trans p56)
  have hRng : loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1) ≤
      8000 * (G + 1) ^ 6 := by
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (show n + 1 ≤ G + 1 by omega))
      (show (Val.nat n).wt + n + (natList (List.range n)).wt + 1 ≤ 8 * (G + 1) ^ 2 by omega)
    have : loopModK * (G + 1) * (8 * (G + 1) ^ 2) = 8000 * (G + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega
  have hL1 : loopModK * ((List.map Val.nat (List.range n)).length + 1) *
        ((Val.list [Val.list [Val.nat n, encFun lab], natList (List.range n)]).wt +
          (List.map Val.nat (List.range n)).length + (encPts (acDom lab)).wt + 1) ≤
      60000 * (G + 1) ^ 6 := by
    rw [hlen]
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK (show n + 1 ≤ G + 1 by omega))
      (show (Val.list [Val.list [Val.nat n, encFun lab], natList (List.range n)]).wt + n +
        (encPts (acDom lab)).wt + 1 ≤ 60 * (G + 1) ^ 2 by omega)
    have : loopModK * (G + 1) * (60 * (G + 1) ^ 2) = 60000 * (G + 1) ^ 3 := by
      simp only [loopModK]; ring
    omega
  have hCF' : CF = n * acpTB n (Val.list [.nat n, encFun lab]).wt := by
    rw [hCF, List.map_const', List.sum_replicate, List.length_map, List.length_range, smul_eq_mul]
  have hTB : acpTB n (Val.list [.nat n, encFun lab]).wt ≤ 120000 * (G + 1) ^ 3 := by
    unfold acpTB
    have : (n + 1) ^ 3 ≤ (G + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have := Nat.mul_le_mul_left countK this
    simp only [countK] at this ⊢
    omega
  have hCFb : CF ≤ 120000 * (G + 1) ^ 6 := by
    rw [hCF']
    have h := Nat.mul_le_mul (show n ≤ G + 1 by omega) hTB
    have : (G + 1) * (120000 * (G + 1) ^ 3) = 120000 * (G + 1) ^ 4 := by ring
    omega
  have hWW : (11 + 1 + 1 + 1 + (3 + 1) + 1 + 1 + 1) * (W + 1) ≤ 2100 * (G + 1) ^ 2 + 21 := by
    omega
  unfold itDomC
  rw [← hGdef]
  omega

/-! ### The source tuple from the sorted dominant orbit -/

/-- **The source tuple of Case 2b as a list**: the first eight points of the sorted dominant orbit,
then `κ - 7` copies of the first point. -/
theorem it_s2b_eq (Φ : Finset (Fin n)) (hΦ : 8 ≤ Φ.card) {κ : ℕ} (hκ : 7 ≤ κ) :
    stL (fun i : Fin (κ + 1) => (stSrc2b Φ hΦ i : ℕ)) =
      (Φ.sort.take 8 ++ List.replicate (κ - 7) (Φ.sort[0]'(by rw [Finset.length_sort]; omega))).map
        Fin.val := by
  have hl : Φ.sort.length = Φ.card := Finset.length_sort _
  refine List.ext_getElem (by simp [stL, hl]; omega) fun i h1 h2 => ?_
  simp only [stL, List.getElem_map, List.getElem_finRange, stSrc2b, Fin.cast_mk]
  by_cases hi : i < 8
  · rw [dif_pos (by simpa using hi), List.getElem_append_left (by simp [hl]; omega),
      List.getElem_take, Finset.orderEmbOfFin_apply, Fin.getElem_fin]
  · rw [dif_neg (by simpa using hi), List.getElem_append_right (by simp [hl]; omega),
      List.getElem_replicate, Finset.orderEmbOfFin_apply, Fin.getElem_fin]

/-- On the sorted dominant orbit (a list of at least eight points): the first eight points, then
`κ - 7` copies of the first point. -/
def itS2bF (app rep κ : ℕ) : Expr :=
  .call app (mk2
    (.snoc (.snoc (.snoc (.snoc (mk4 (.get (.var 0) (.nat 0)) (.get (.var 0) (.nat 1))
      (.get (.var 0) (.nat 2)) (.get (.var 0) (.nat 3))) (.get (.var 0) (.nat 4)))
      (.get (.var 0) (.nat 5))) (.get (.var 0) (.nat 6))) (.get (.var 0) (.nat 7)))
    (.call rep (mk2 (.nat (κ - 7)) (.get (.var 0) (.nat 0)))))

/-- The cost bound of `itS2bF` for a weight bound `W` of the input, with `κ ≤ W`. -/
def itS2bC (W : ℕ) : ℕ := 10 ^ 6 * (W + 1) ^ 3

theorem itS2bC_mono {a b : ℕ} (h : a ≤ b) : itS2bC a ≤ itS2bC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

set_option maxHeartbeats 1000000 in
/-- **The source tuple of Case 2b as a program**: on the sorted list of `Φ`, `itS2bF` returns the
entries of `stSrc2b Φ` on `κ + 1` positions. -/
theorem it_s2b_spec {P : Program} {f app rep κ : ℕ}
    (hf : P.funs[f]? = some (itS2bF app rep κ)) (happ : P.HasAt app (appendFuns app))
    (hrep : P.HasAt rep (replicateFuns rep)) (Φ : Finset (Fin n)) (hΦ : 8 ≤ Φ.card)
    (hκ : 7 ≤ κ) {W : ℕ} (hW : (encPts Φ.sort).wt ≤ W) (hnW : n + κ + 10 ≤ W) :
    FunDet P f (encPts Φ.sort) (natList (stL fun i : Fin (κ + 1) => (stSrc2b Φ hΦ i : ℕ)))
      (itS2bC W) := by
  have hl : Φ.sort.length = Φ.card := Finset.length_sort _
  have hΦn : Φ.card ≤ n := by simpa using Finset.card_le_univ Φ
  set D := Φ.sort with hD
  set vs : List Val := D.map fun i => Val.nat i.val with hvs
  have hin : encPts D = .list vs := acp_encPts_eq D
  set W' := 100 * (W + 1) ^ 2 with hW'
  have hWW : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- weights of lists of points
  have hsub : ∀ l : List (Fin n), l.length ≤ κ + 1 →
      (Val.list (l.map fun i => Val.nat i.val)).wt ≤ 5 * (W + 1) ^ 2 := fun l hl2 => by
    have := wt_natList_le_sq (xs := l.map Fin.val) (B := W)
      (fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        have := y.2; omega)
      (by simp; omega)
    rw [natList, List.map_map] at this; exact this
  have hpw : ∀ x : Fin n, (Val.nat x.val).wt ≤ W' := fun x => by
    have := wt_nat_le x.val; have := x.2; omega
  have hent : ∀ j (hj : j < 8), vs[j]? = some (.nat (D[j]'(by omega)).val) := fun j hj => by
    simp [hvs, List.getElem?_map, List.getElem?_eq_getElem (show j < D.length by omega)]
  have hd : ∀ j (hj : j < 8), StDC P [encPts D] (.get (.var 0) (.nat j))
      (.nat (D[j]'(by omega)).val) 3 0 W' := fun j hj =>
    StDC.get (StDC.var' (v := .list vs) (by rw [hin]; rfl) (by rw [← hin]; omega))
      (StDC.nat j (by omega)) (hent j hj) (hpw _)
  set a : Fin n := D[0]'(by omega) with ha
  set pre : List (Fin n) := [D[0]'(by omega), D[1]'(by omega), D[2]'(by omega), D[3]'(by omega),
    D[4]'(by omega), D[5]'(by omega), D[6]'(by omega), D[7]'(by omega)] with hpre
  have hpre8 : pre = D.take 8 := by
    refine List.ext_getElem (by simp [hpre]; omega) fun i h1 h2 => ?_
    simp only [hpre, List.length_cons, List.length_nil] at h1
    simp only [List.getElem_take]
    interval_cases i <;> rfl
  have hprew := hsub pre (by simp [hpre]; omega)
  have m4 := StDC.mk4 (hd 0 (by omega)) (hd 1 (by omega)) (hd 2 (by omega)) (hd 3 (by omega))
    (by
      have := hsub [D[0]'(by omega), D[1]'(by omega), D[2]'(by omega), D[3]'(by omega)]
        (by simp; omega)
      simp at this ⊢; omega) (by omega)
  have s5 := StDC.snoc m4 (hd 4 (by omega)) (by
    have := hsub [D[0]'(by omega), D[1]'(by omega), D[2]'(by omega), D[3]'(by omega),
      D[4]'(by omega)] (by simp; omega)
    simp at this ⊢; omega)
  have s6 := StDC.snoc s5 (hd 5 (by omega)) (by
    have := hsub [D[0]'(by omega), D[1]'(by omega), D[2]'(by omega), D[3]'(by omega),
      D[4]'(by omega), D[5]'(by omega)] (by simp; omega)
    simp at this ⊢; omega)
  have s7 := StDC.snoc s6 (hd 6 (by omega)) (by
    have := hsub [D[0]'(by omega), D[1]'(by omega), D[2]'(by omega), D[3]'(by omega),
      D[4]'(by omega), D[5]'(by omega), D[6]'(by omega)] (by simp; omega)
    simp at this ⊢; omega)
  have s8 := StDC.snoc s7 (hd 7 (by omega)) (by simp [hpre] at hprew ⊢; omega)
  have e8 : ((([Val.nat (D[0]'(by omega)).val, .nat (D[1]'(by omega)).val,
      .nat (D[2]'(by omega)).val, .nat (D[3]'(by omega)).val] ++
      [Val.nat (D[4]'(by omega)).val]) ++ [Val.nat (D[5]'(by omega)).val]) ++
      [Val.nat (D[6]'(by omega)).val]) ++ [Val.nat (D[7]'(by omega)).val] =
      pre.map fun i => Val.nat i.val := by simp [hpre]
  rw [e8] at s8
  -- the copies of the first point
  have hd0 : StDC P [encPts D] (.get (.var 0) (.nat 0)) (.nat a.val) 3 0 W' := by
    have h := hd 0 (by omega); rwa [← ha] at h
  have hrepw := hsub (List.replicate (κ - 7) a) (by simp; omega)
  have hR : FunDet P rep (.list [.nat (κ - 7), .nat a.val])
      (.list (List.replicate (κ - 7) (Val.nat a.val)))
      (loopModK * (κ - 7 + 1) * ((Val.list [.nat (κ - 7), .nat a.val]).wt + (κ - 7) +
        (Val.list (List.replicate (κ - 7) (Val.nat a.val))).wt + 1)) :=
    (replicate_spec hrep (κ - 7) (.nat a.val)).mono fun w c ⟨h1, h2⟩ => ⟨h1, h1 ▸ h2⟩
  have er : List.replicate (κ - 7) (Val.nat a.val) =
      (List.replicate (κ - 7) a).map fun i => Val.nat i.val := by simp
  have hrepw' : (Val.list (List.replicate (κ - 7) (Val.nat a.val))).wt ≤ 5 * (W + 1) ^ 2 := by
    rw [er]; exact hrepw
  have hk7 := wt_list2_le (.nat (κ - 7)) (.nat a.val)
  have wk7 := wt_nat_le (κ - 7)
  have wa := wt_nat_le a.val
  have ha2 := a.2
  have dr := StDC.call (StDC.mk2 (StDC.nat (P := P) (env := [encPts D]) (W := W') (κ - 7)
    (by omega)) hd0 (by omega) (by omega)) hR (by rw [er]; omega)
  -- the append
  have hA : FunDet P app (.list [.list (pre.map fun i => Val.nat i.val),
      .list (List.replicate (κ - 7) (Val.nat a.val))])
      (.list ((pre.map fun i => Val.nat i.val) ++ List.replicate (κ - 7) (Val.nat a.val)))
      (loopModK * ((List.replicate (κ - 7) (Val.nat a.val)).length + 1) *
        ((Val.list [.list (pre.map fun i => Val.nat i.val),
          .list (List.replicate (κ - 7) (Val.nat a.val))]).wt +
          (List.replicate (κ - 7) (Val.nat a.val)).length +
          (Val.list ((pre.map fun i => Val.nat i.val) ++
            List.replicate (κ - 7) (Val.nat a.val))).wt + 1)) :=
    (append_spec happ _ _).mono fun w c ⟨h1, h2⟩ => ⟨h1, h1 ▸ h2⟩
  have eout : Val.list ((pre.map fun i => Val.nat i.val) ++ List.replicate (κ - 7) (Val.nat a.val)) =
      natList (stL fun i : Fin (κ + 1) => (stSrc2b Φ hΦ i : ℕ)) := by
    rw [it_s2b_eq Φ hΦ hκ, er, ← List.map_append, hpre8]
    simp [natList, List.map_map, Function.comp_def, ha, hD]
  have hall := hsub (pre ++ List.replicate (κ - 7) a) (by simp [hpre]; omega)
  rw [List.map_append, ← er] at hall
  have hmw := wt_list2_le (.list (pre.map fun i => Val.nat i.val))
    (.list (List.replicate (κ - 7) (Val.nat a.val)))
  have dA := StDC.call (StDC.mk2 s8 dr (by omega) (by omega)) hA (by omega)
  rw [eout] at dA
  refine FunDet.intro hf (dA.det.mono ?_)
  -- the cost
  have hlr : (List.replicate (κ - 7) (Val.nat a.val)).length = κ - 7 := by simp
  rw [hlr]
  have c1 : loopModK * (κ - 7 + 1) * ((Val.list [.nat (κ - 7), .nat a.val]).wt + (κ - 7) +
      (Val.list (List.replicate (κ - 7) (Val.nat a.val))).wt + 1) ≤
      loopModK * (W + 1) * (20 * (W + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have c2 : loopModK * (κ - 7 + 1) *
      ((Val.list [.list (pre.map fun i => Val.nat i.val),
          .list (List.replicate (κ - 7) (Val.nat a.val))]).wt + (κ - 7) +
        (Val.list ((pre.map fun i => Val.nat i.val) ++
          List.replicate (κ - 7) (Val.nat a.val))).wt + 1) ≤
      loopModK * (W + 1) * (40 * (W + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  rw [eout] at c2
  have e1 : loopModK * (W + 1) * (20 * (W + 1) ^ 2) = 20000 * (W + 1) ^ 3 := by
    simp only [loopModK]; ring
  have e2 : loopModK * (W + 1) * (40 * (W + 1) ^ 2) = 40000 * (W + 1) ^ 3 := by
    simp only [loopModK]; ring
  have e3 : (W + 1) * (W + 1) ^ 2 = (W + 1) ^ 3 := by ring
  have hW3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold itS2bC
  omega

end GI.Impl
