module

public import Workspace.Impl.AggItemCiCfgJ

@[expose] public section

/-!
# The configuration query: the outer points by color, as a program

Lemma A.12 aligns the outer color classes of `X` and `Y`. The program lists the outer points of
a pair configuration `Z` by color (`itciFo Z`, `AggItemCiCfgMo.lean`), from ranks:
* `itcqLtT` on `[[cZ, a], b]` (with `cZ = rcCertIn Z z₀`): whether the key of `b` is smaller
  than the key of `a` (`itciLt Z b a`);
* `itcqRkB flt` on `[[cZ, D], a]`: the rank of `a`, the length of the filter of `itcqLtT` over
  the outer points `D` (`itcq_rkB_spec`);
* `itcqAtB fnd` on `[[D, R], i]`: the point of rank `i`, entry `idxOf i R` of `D`
  (`itcq_atB_spec`);
* `itcqDsF` on `cZ`: the outer points `D`, their ranks `R`, and the points of ranks
  `0, 1, …, |D| - 1`. This is `itcqDV Z` (`itcq_dsF_spec`).
* `itcqCoB` on `[cZ, a]`: the color `Z.col a a`; mapped over `itcqDV Z` it gives the colors
  along `itciFo Z` (`itcq_cols_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (Val encPerm gens encGroup encPerms)

variable {q : ℕ}

/-- On `[[cZ, a], b]`: whether `b` comes before `a` (`itciLt`). -/
def itcqLtT : Expr :=
  .ite (.arith .lt (itcqCoE (.get (arg 0) (.nat 0)) (arg 1))
      (itcqCoE (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))))
    (.nat 1)
    (.ite (.arith .eq (itcqCoE (.get (arg 0) (.nat 0)) (arg 1))
        (itcqCoE (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))))
      (.arith .lt (arg 1) (.get (arg 0) (.nat 1))) (.nat 0))

/-- On `[[cZ, D], a]`: the rank of `a`. -/
def itcqRkB (flt : ℕ) : Expr :=
  .length (.call flt (mk2 (mk2 (.get (arg 0) (.nat 0)) (arg 1)) (.get (arg 0) (.nat 1))))

/-- On `[[D, R], i]`: the point of rank `i`. -/
def itcqAtB (fnd : ℕ) : Expr :=
  .get (.get (arg 0) (.nat 0)) (.call fnd (mk2 (arg 1) (.get (arg 0) (.nat 1))))

/-- On `cZ`: the outer points by color. -/
def itcqDsF (fdl frm rng fam : ℕ) : Expr :=
  .letE (.call fdl (.var 0))
  (.letE (.call frm (mk2 (mk2 (.var 0) (.var 1)) (.var 1)))
  (.call fam (mk2 (mk2 (.var 1) (.var 2)) (.call rng (.length (.var 1))))))

/-- On `[cZ, a]`: the color `Z.col a a`. -/
def itcqCoB : Expr := itcqCoE (arg 0) (arg 1)

/-- The cost bound of `itcqDsF`. -/
def itcqDsC (W : ℕ) : ℕ := 10 ^ 19 * (W + 3) ^ 8

/-- The cost bound of the colors along `itciFo Z`. -/
def itcqCoC (W : ℕ) : ℕ := 10 ^ 6 * (W + 2) ^ 3

/-! ### Values -/

/-- The key test on values. -/
def itcqLq (Z : PairCfg q) (a : Fin q) : Val → Bool
  | .nat b => if h : b < q then itciLt Z ⟨b, h⟩ a else false
  | _ => false

theorem itcq_lq_filter (Z : PairCfg q) (a : Fin q) (D : List (Fin q)) :
    ((D.map Fin.val).map Val.nat).filter (itcqLq Z a) =
      (((D.filter fun b => itciLt Z b a)).map Fin.val).map Val.nat := by
  rw [List.map_map, List.filter_map, List.map_map]
  congr 2
  funext b
  simp [itcqLq, b.isLt]

/-- The ranks of the outer points, as a value. -/
def itcqRV (Z : PairCfg q) : Val := natList ((itciFl Z.fiberᶜ).map (itciRk Z))

/-- A list `filterMap` with only `some` values, mapped. -/
theorem itcq_filterMap_eq {α β γ : Type} {f : α → Option β} (g : β → γ) (d : γ) :
    ∀ {l : List α}, (∀ i ∈ l, (f i).isSome) →
      (l.filterMap f).map g = l.map fun i => ((f i).map g).getD d
  | [], _ => rfl
  | i :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h i (List.mem_cons_self ..))
    rw [List.filterMap_cons, hb, List.map_cons, List.map_cons,
      itcq_filterMap_eq g d fun j hj => h j (List.mem_cons_of_mem _ hj)]
    simp only [hb, Option.map_some, Option.getD_some]

/-- **`itcqDV Z` entry by entry**: entry `i` is the point of rank `i`. -/
theorem itcq_dv_at (Z : PairCfg q) :
    ((itciFo Z).map Fin.val).map Val.nat = (List.range (itciFl Z.fiberᶜ).length).map
      fun i => Val.nat (((itciAt Z i).map Fin.val).getD 0) := by
  rw [itciFo, itcq_filterMap_eq Fin.val 0 fun i hi => by
    obtain ⟨a, ha⟩ := itciAt_some Z (List.mem_range.1 hi); rw [ha]; rfl, List.map_map]
  rfl

theorem itcq_rk_le (Z : PairCfg q) (a : Fin q) : itciRk Z a ≤ q := by
  unfold itciRk
  have := (List.filter_sublist (p := fun b => itciLt Z b a) (l := itciFl Z.fiberᶜ)).length_le
  rw [itciFl_length] at this
  have := Z.fiberᶜ.card_le_univ
  simp only [Fintype.card_fin] at this
  omega

theorem itcq_fl_len (Z : PairCfg q) : (itciFl Z.fiberᶜ).length ≤ q := by
  rw [itciFl_length]; exact Finset.card_le_univ _ |>.trans (by simp)

theorem itcq_rv_wt (Z : PairCfg q) : (itcqRV Z).wt ≤ 5 * (q + 1) ^ 2 := by
  refine wt_natList_le_sq (fun x hx => ?_) ?_
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact itcq_rk_le Z a
  · simp only [List.length_map]; exact itcq_fl_len Z

theorem itcq_dr_wt (Z : PairCfg q) : (itcqDR Z).wt ≤ 5 * (q + 1) ^ 2 := by
  refine wt_natList_le_sq (fun x hx => ?_) ?_
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact a.isLt.le
  · simp only [List.length_map]; exact itcq_fl_len Z

theorem itcq_dv_wt' (Z : PairCfg q) : (itcqDV Z).wt ≤ 5 * (q + 1) ^ 2 := by
  refine wt_natList_le_sq (fun x hx => ?_) ?_
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact a.isLt.le
  · simp only [List.length_map, itciFo_length]
    exact Finset.card_le_univ _ |>.trans (by simp)

/-- The two lists of outer points weigh the same, since one is a permutation of the other. -/
theorem itcq_dv_wt_eq (Z : PairCfg q) : (itcqDV Z).wt = (itcqDR Z).wt := by
  have hp := ((itciFo_perm Z).map Fin.val).map Val.nat
  unfold itcqDV itcqDR natList
  rw [wt_list_eq, wt_list_eq, (hp.map Val.wt).sum_eq, (hp.map Val.size).sum_eq, hp.length_eq]

section Prog

variable {P : Program}

/-- **The key test**, in cost `200 (W + 1)`. -/
theorem itcq_ltT_spec {f : ℕ} (hf : P.funs[f]? = some itcqLtT) (Z : PairCfg q) (z₀ : ℕ)
    (a b : Fin q) {W : ℕ}
    (hW : (Val.list [.list [.list [rcColVal Z, .nat Z.j, .nat z₀], .nat a], .nat b]).wt ≤ W) :
    FunDet P f (.list [.list [.list [rcColVal Z, .nat Z.j, .nat z₀], .nat a], .nat b])
      (boolVal (itciLt Z b a)) (200 * (W + 1)) := by
  set cZ : Val := .list [rcColVal Z, .nat Z.j, .nat z₀]
  set c : Val := .list [cZ, .nat a]
  have hc : c.wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hcZ : cZ.wt ≤ W := (st_wt_mem (by simp)).trans hc
  have ha : (Val.nat a).wt ≤ W := (st_wt_mem (by simp)).trans hc
  have hb : (Val.nat b).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have h2 := (Val.list [c, .nat b]).two_le_size
  have h3 := (Val.list [c, .nat b]).size_le_wt
  have hw4 : 4 ≤ W := by have := wt_list_eq [c, .nat b]; omega
  have A0 : StDC P [.list [c, .nat b]] (arg 0) c 3 0 W :=
    StDC.arg (vs := [c, .nat b]) rfl hW (by omega) hc
  have A1 : StDC P [.list [c, .nat b]] (arg 1) (.nat b) 3 0 W :=
    StDC.arg (vs := [c, .nat b]) rfl hW (by omega) hb
  have gZ := StDC.get A0 (StDC.nat 0 (by omega)) (v := cZ) rfl hcZ
  have gA := StDC.get A0 (StDC.nat 1 (by omega)) (v := .nat a) rfl ha
  have cb := itcq_coE_st gZ A1 hcZ
  have ca := itcq_coE_st gZ gA hcZ
  have hcbw := wt_nat_le (Z.col b b)
  have h01 : ∀ p : Prop, [Decidable p] → (Val.nat (if p then 1 else 0)).wt ≤ W := fun p _ => by
    split_ifs <;> exact (wt_nat_le _).trans (by omega)
  have lt1 := StDC.arith cb ca (op := .lt) rfl (h01 _)
  have eq1 := StDC.arith cb ca (op := .eq) rfl (h01 _)
  have lt2 := StDC.arith A1 gA (op := .lt) rfl (h01 _)
  have hv : (boolVal (itciLt Z b a)).wt ≤ W := (wt_boolVal_le _).trans (by omega)
  have body := StDC.ite (v := boolVal (itciLt Z b a)) lt1
    (fun h => by
      rw [Machine.BinOp.eval_lt] at h
      have hl : Z.col b b < Z.col a a := by by_contra h'; exact h (if_neg h')
      have : itciLt Z b a = true := by simp [itciLt, hl]
      rw [this]; exact StDC.nat 1 (by omega))
    (fun h => by
      rw [Machine.BinOp.eval_lt] at h
      have hl : ¬ Z.col b b < Z.col a a := fun h' => by rw [if_pos h'] at h; exact one_ne_zero h
      exact StDC.ite eq1
        (fun h' => by
          rw [Machine.BinOp.eval_eq] at h'
          have he : Z.col b b = Z.col a a := by by_contra h''; exact h' (if_neg h'')
          have : (itciLt Z b a).toNat = Machine.BinOp.lt.eval b a := by
            rw [Machine.BinOp.eval_lt]
            by_cases hba : (b : ℕ) < a
            · rw [if_pos hba]; simp [itciLt, he, Fin.lt_def, hba]
            · rw [if_neg hba]; simp [itciLt, he, Fin.lt_def, hba]
          rw [boolVal, this]; exact lt2)
        (fun h' => by
          rw [Machine.BinOp.eval_eq] at h'
          have he : Z.col b b ≠ Z.col a a := fun e => by rw [if_pos e] at h'; exact one_ne_zero h'
          have : itciLt Z b a = false := by simp [itciLt, he, hl]
          rw [this]; exact StDC.nat 0 (by omega)) hv) hv
  exact StDC.funDet hf body (by omega)

/-- **Map over points**: if `fp` on `[c, a]` gives `g a` for every point `a` of `D`, then
`map fp` on `[c, D]` gives the list of the `g a`. -/
theorem itcq_mapPts_spec {mb fp : ℕ} (hm : P.HasAt mb (mapFuns mb fp)) {c : Val}
    (D : List (Fin q)) {g : Fin q → Val} {Bd : ℕ}
    (hf : ∀ a ∈ D, FunDet P fp (.list [c, .nat a]) (g a) Bd) :
    FunAll P mb (.list [c, natList (D.map Fin.val)]) (fun w cost =>
      w = .list (D.map g) ∧ cost ≤ D.length * Bd +
        mapK * (D.length + 1) * ((Val.list [c, natList (D.map Fin.val)]).wt + w.wt + 1)) := by
  let F : Val → Val := fun x => match x with
    | .nat t => if ht : t < q then g ⟨t, ht⟩ else .nat 0
    | _ => .nat 0
  have key := map_spec (P := P) hm (c := c) (xs := (D.map Fin.val).map Val.nat)
    (R := fun x w => w = F x) (B := fun _ => Bd) (by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ht
      refine FunAll.mono (hf a ha) fun w cost ⟨hw, hc⟩ => ⟨?_, hc⟩
      subst hw
      simp only [F, dif_pos a.isLt, Fin.eta])
  refine key.mono fun w cost ⟨ws, hw, h2, hc⟩ => ?_
  have hval : w = .list (D.map g) := by
    rw [hw, itcq_f2_map h2, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply, F, dif_pos a.isLt, Fin.eta]
  refine ⟨hval, ?_⟩
  simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
  exact hc

/-- The cost bound of the rank of one point. -/
def itcqRkC (W : ℕ) : ℕ := 10 ^ 8 * (W + 3) ^ 3

theorem itcq_rkC_arith {W q n d C Wl : ℕ} (hq : q < W) (hd : d ≤ q) (hn : n ≤ 100)
    (hWl : Wl = 10 * W + 5 * (q + 1) ^ 2 + 30)
    (hC : C ≤ n * (Wl + 1) + (d * (200 * (10 * W + 21)) +
      loopModK * (d + 1) * (10 * W + 18 + d + 5 * (q + 1) ^ 2 + 1))) : C ≤ itcqRkC W := by
  unfold itcqRkC
  unfold loopModK at hC
  have h1 : (q + 1) ^ 2 ≤ (W + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : W + 3 ≤ (W + 3) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : (W + 3) * (W + 3) ^ 2 = (W + 3) ^ 3 := by ring
  have h4 : n * (Wl + 1) ≤ 100 * (16 * (W + 3) ^ 2) := by
    rw [hWl]; exact Nat.mul_le_mul hn (by omega)
  have h5 : d * (200 * (10 * W + 21)) ≤ (W + 3) * (2000 * (W + 3)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h6 : 1000 * (d + 1) * (10 * W + 18 + d + 5 * (q + 1) ^ 2 + 1) ≤
      1000 * ((W + 3) * (16 * (W + 3) ^ 2)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e1 : (W + 3) * (2000 * (W + 3)) = 2000 * (W + 3) ^ 2 := by ring
  have e2 : (W + 3) * (16 * (W + 3) ^ 2) = 16 * (W + 3) ^ 3 := by ring
  have h7 : (W + 3) ^ 2 ≤ (W + 3) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

set_option maxHeartbeats 1000000 in
/-- **The rank of a point**, by the filter of the key test. -/
theorem itcq_rkB_spec {f flt fl : ℕ} (hf : P.funs[f]? = some (itcqRkB flt))
    (hflt : P.HasAt flt (filterFuns flt fl)) (hfl : P.funs[fl]? = some itcqLtT)
    (Z : PairCfg q) (z₀ : ℕ) (a : Fin q) {W : ℕ}
    (hW : (Val.list [.list [.list [rcColVal Z, .nat Z.j, .nat z₀], itcqDR Z], .nat a]).wt ≤ W) :
    FunDet P f (.list [.list [.list [rcColVal Z, .nat Z.j, .nat z₀], itcqDR Z], .nat a])
      (.nat (itciRk Z a)) (itcqRkC W) := by
  set cZ : Val := .list [rcColVal Z, .nat Z.j, .nat z₀]
  set c0 : Val := .list [cZ, itcqDR Z]
  have hc0 : c0.wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hcZ : cZ.wt ≤ W := (st_wt_mem (by simp [c0])).trans hc0
  have hDR : (itcqDR Z).wt ≤ W := (st_wt_mem (by simp [c0])).trans hc0
  have haw : (Val.nat a).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hq : q < W := lt_of_lt_of_le (itcq_q_le Z)
    ((st_wt_mem (show rcColVal Z ∈ [rcColVal Z, .nat Z.j, .nat z₀] by simp)).trans hcZ)
  have hd := itcq_fl_len Z
  set D := itciFl Z.fiberᶜ
  have hDRe : itcqDR Z = .list ((D.map Fin.val).map Val.nat) := rfl
  have hca := wt_list2_le cZ (.nat (a : ℕ))
  have hfin := wt_list2_le (.list [cZ, .nat (a : ℕ)]) (itcqDR Z)
  -- the filter
  have hout : (natList ((D.filter fun b => itciLt Z b a).map Fin.val)).wt ≤ 5 * (q + 1) ^ 2 := by
    refine wt_natList_le_sq (fun x hx => ?_) ?_
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact b.isLt.le
    · simp only [List.length_map]; exact (List.filter_sublist.length_le).trans hd
  have hfd : FunDet P flt (.list [.list [cZ, .nat a], itcqDR Z])
      (natList ((D.filter fun b => itciLt Z b a).map Fin.val))
      (D.length * (200 * (10 * W + 21)) + loopModK * (D.length + 1) *
        (10 * W + 18 + D.length + 5 * (q + 1) ^ 2 + 1)) := by
    rw [hDRe]
    have key := filter_spec (P := P) hflt (c := .list [cZ, .nat a])
      (xs := (D.map Fin.val).map Val.nat) (q := itcqLq Z a)
      (B := fun _ => 200 * (10 * W + 20 + 1)) (by
        intro x hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 ht
        have h2 := wt_list2_le (.list [cZ, .nat (a : ℕ)]) (.nat (b : ℕ))
        have hbw := wt_nat_le (b : ℕ)
        have hb := b.isLt
        have := itcq_ltT_spec hfl Z z₀ a b (W := 10 * W + 20)
          (show (Val.list [.list [cZ, .nat (a : ℕ)], .nat (b : ℕ)]).wt ≤ 10 * W + 20 by omega)
        have e : itcqLq Z a (.nat (b : ℕ)) = itciLt Z b a := by simp [itcqLq, b.isLt]
        rw [e]; exact this)
    refine key.mono fun w c ⟨hw, hc⟩ => ⟨?_, ?_⟩
    · rw [hw, itcq_lq_filter]; rfl
    · have hw' : w = natList ((D.filter fun b => itciLt Z b a).map Fin.val) := by
        rw [hw, itcq_lq_filter]; rfl
      rw [hw'] at hc
      simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
      rw [← hDRe] at hc
      have : (natList ((D.filter fun b => itciLt Z b a).map Fin.val)).wt ≤ 5 * (q + 1) ^ 2 := hout
      calc c ≤ _ := hc
        _ ≤ _ := by
          refine Nat.add_le_add (le_of_eq rfl) (Nat.mul_le_mul_left _ ?_)
          omega
  obtain ⟨Wl, hWl⟩ : ∃ Wl, Wl = 10 * W + 5 * (q + 1) ^ 2 + 30 := ⟨_, rfl⟩
  have hs2 := (Val.list [c0, .nat a]).two_le_size
  have hs3 := (Val.list [c0, .nat a]).size_le_wt
  have A0 := StDC.arg (P := P) (rest := []) (vs := [c0, .nat a]) (j := 0) rfl (W := Wl)
    (by omega) (by omega) (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := [c0, .nat a]) (j := 1) rfl (W := Wl)
    (by omega) (by omega) (by omega)
  have g0 := StDC.get A0 (StDC.nat 0 (by omega)) (v := cZ) rfl (by omega)
  have g1 := StDC.get A0 (StDC.nat 1 (by omega)) (v := itcqDR Z) rfl (by omega)
  have m1 := StDC.mk2 g0 A1 (by omega) (by omega)
  have m2 := StDC.mk2 m1 g1 (by omega) (by omega)
  have cl := StDC.call m2 hfd (by omega)
  have ln := StDC.length cl (by
    simp only [List.length_map]
    have := (List.filter_sublist (p := fun b => itciLt Z b a) (l := D)).length_le
    omega)
  simp only [List.length_map] at ln
  refine StDC.funDet hf ln ?_
  refine itcq_rkC_arith hq hd (n := 100) le_rfl hWl ?_
  clear ln cl m2 m1 g1 g0 A1 A0
  omega

/-- The cost bound of the ranks. -/
def itcqRksC (W : ℕ) : ℕ := 10 ^ 11 * (W + 3) ^ 4

theorem itcq_rksC_arith {W q d R I C : ℕ} (hq : q < W) (hd : d ≤ q) (hR : R ≤ 5 * (q + 1) ^ 2)
    (hI : I ≤ W) (hC : C ≤ d * itcqRkC (4 * W + 10) + mapK * (d + 1) * (I + R + 1)) :
    C ≤ itcqRksC W := by
  unfold itcqRksC itcqRkC mapK at *
  have h1 : (q + 1) ^ 2 ≤ (W + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (4 * W + 10 + 3) ^ 3 ≤ (5 * (W + 3)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have e2 : (5 * (W + 3)) ^ 3 = 125 * (W + 3) ^ 3 := by ring
  have h3 : d * (10 ^ 8 * (4 * W + 10 + 3) ^ 3) ≤ (W + 3) * (10 ^ 8 * (125 * (W + 3) ^ 3)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (e2 ▸ h2))
  have hs : W + 3 ≤ (W + 3) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h4 : 1000 * (d + 1) * (I + R + 1) ≤ 1000 * ((W + 3) * (6 * (W + 3) ^ 2)) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e3 : (W + 3) * (10 ^ 8 * (125 * (W + 3) ^ 3)) = 12500000000 * (W + 3) ^ 4 := by ring
  have e4 : (W + 3) * (6 * (W + 3) ^ 2) = 6 * (W + 3) ^ 3 := by ring
  have h5 : (W + 3) ^ 3 ≤ (W + 3) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [e3] at h3
  rw [e4] at h4
  generalize d * (10 ^ 8 * (4 * W + 10 + 3) ^ 3) = A at *
  generalize 1000 * (d + 1) * (I + R + 1) = B at *
  generalize (W + 3) ^ 3 = T3 at *
  generalize (W + 3) ^ 4 = T4 at *
  norm_num at *
  omega

/-- **The ranks of the outer points**, by the map of `itcqRkB`. -/
theorem itcq_rks_spec {frm f flt fl : ℕ} (hm : P.HasAt frm (mapFuns frm f))
    (hf : P.funs[f]? = some (itcqRkB flt))
    (hflt : P.HasAt flt (filterFuns flt fl)) (hfl : P.funs[fl]? = some itcqLtT)
    (Z : PairCfg q) (z₀ : ℕ) {W : ℕ}
    (hW : (Val.list [.list [.list [rcColVal Z, .nat Z.j, .nat z₀], itcqDR Z], itcqDR Z]).wt ≤ W) :
    FunDet P frm (.list [.list [.list [rcColVal Z, .nat Z.j, .nat z₀], itcqDR Z], itcqDR Z])
      (itcqRV Z) (itcqRksC W) := by
  set cZ : Val := .list [rcColVal Z, .nat Z.j, .nat z₀]
  set c0 : Val := .list [cZ, itcqDR Z]
  have hc0 : c0.wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hcZ : cZ.wt ≤ W := (st_wt_mem (by simp)).trans hc0
  have hq : q < W := lt_of_lt_of_le (itcq_q_le Z)
    ((st_wt_mem (show rcColVal Z ∈ [rcColVal Z, .nat Z.j, .nat z₀] by simp)).trans hcZ)
  have hd := itcq_fl_len Z
  have key := itcq_mapPts_spec (P := P) hm (c := c0) (itciFl Z.fiberᶜ)
    (g := fun a => .nat (itciRk Z a)) (Bd := itcqRkC (4 * W + 10)) (fun a _ => by
      have h2 := wt_list2_le c0 (.nat (a : ℕ))
      have := wt_nat_le (a : ℕ)
      have := a.isLt
      exact itcq_rkB_spec hf hflt hfl Z z₀ a (W := 4 * W + 10)
        (show (Val.list [c0, .nat (a : ℕ)]).wt ≤ 4 * W + 10 by omega))
  refine key.mono fun w c ⟨hw, hc⟩ => ⟨?_, ?_⟩
  · rw [hw, itcqRV, natList, List.map_map]; rfl
  · have hw' : w = itcqRV Z := by rw [hw, itcqRV, natList, List.map_map]; rfl
    rw [hw'] at hc
    exact itcq_rksC_arith hq hd (itcq_rv_wt Z) hW hc

/-- The cost bound of the point of a rank. -/
def itcqAtC (W : ℕ) : ℕ := 10 ^ 6 * (W + 3) ^ 2

theorem itcq_atC_arith {W d r n C : ℕ} (hd : d < W) (hr : r ≤ 4 * W + 6) (hn : n ≤ 50)
    (hC : C ≤ n * (4 * W + 30 + 1) + (d * (20 * d + 100) + loopModK * (d + 1) * (r + 2 * d + 3))) :
    C ≤ itcqAtC W := by
  unfold itcqAtC
  unfold loopModK at hC
  have h1 : d * (20 * d + 100) ≤ (W + 3) * (200 * (W + 3)) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 1000 * (d + 1) * (r + 2 * d + 3) ≤ 1000 * ((W + 3) * (10 * (W + 3))) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have h3 : n * (4 * W + 30 + 1) ≤ 50 * (4 * W + 31) := Nat.mul_le_mul_right _ hn
  have e1 : (W + 3) * (200 * (W + 3)) = 200 * (W + 3) ^ 2 := by ring
  have e2 : (W + 3) * (10 * (W + 3)) = 10 * (W + 3) ^ 2 := by ring
  have h4 : W + 3 ≤ (W + 3) ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [e1] at h1
  rw [e2] at h2
  have : (10 : ℕ) ^ 6 = 1000000 := by norm_num
  rw [this]
  omega

set_option maxHeartbeats 1000000 in
/-- **The point of rank `i`**, by `find` in the ranks. -/
theorem itcq_atB_spec {f fnd fe : ℕ} (hf : P.funs[f]? = some (itcqAtB fnd))
    (hfnd : P.HasAt fnd (findFuns fnd fe)) (hfe : P.funs[fe]? = some eqTestF) (Z : PairCfg q)
    {i : ℕ} (hi : i < (itciFl Z.fiberᶜ).length) {W : ℕ}
    (hW : (Val.list [.list [itcqDR Z, itcqRV Z], .nat i]).wt ≤ W) :
    FunDet P f (.list [.list [itcqDR Z, itcqRV Z], .nat i])
      (.nat (((itciAt Z i).map Fin.val).getD 0)) (itcqAtC W) := by
  have hd := itcq_fl_len Z
  set D := itciFl Z.fiberᶜ
  set c0 : Val := .list [itcqDR Z, itcqRV Z]
  have hc0 : c0.wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hDR : (itcqDR Z).wt ≤ W := (st_wt_mem (by simp [c0])).trans hc0
  have hRV : (itcqRV Z).wt ≤ W := (st_wt_mem (by simp [c0])).trans hc0
  have hiw : (Val.nat i).wt ≤ W := (st_wt_mem (by simp)).trans hW
  obtain ⟨a, ha⟩ := itciAt_some Z hi
  set k := (D.map (itciRk Z)).idxOf i
  have hk : D[k]? = some a := ha
  have hkl : k < D.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hk; exact absurd hk (by simp)
  have hval : ((itciAt Z i).map Fin.val).getD 0 = (a : ℕ) := by rw [ha]; rfl
  rw [hval]
  have hkf : ((D.map (itciRk Z)).map Val.nat).findIdx (natEq i) = k := by
    rw [findIdx_natEq]
    unfold k List.idxOf
    congr 1
  have hRVe : itcqRV Z = .list ((D.map (itciRk Z)).map Val.nat) := rfl
  have hDRe : itcqDR Z = .list ((D.map Fin.val).map Val.nat) := rfl
  have hfd : FunDet P fnd (.list [.nat i, itcqRV Z]) (.nat k)
      (D.length * (20 * D.length + 100) + loopModK * (D.length + 1) *
        ((Val.list [.nat i, itcqRV Z]).wt + 2 * D.length + 3)) := by
    rw [hRVe]
    have key := find_spec (P := P) hfnd (c := .nat i) (xs := (D.map (itciRk Z)).map Val.nat)
      (q := natEq i) (B := fun _ => 20 * D.length + 100) (by
        intro x hx
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
        obtain ⟨b, hbD, rfl⟩ := List.mem_map.1 hr
        have : itciRk Z b < D.length := itciRk_lt_length Z (Finset.mem_compl.1 (itci_mem_fl.1 hbD))
        exact (eqTest_det hfe i (itciRk Z b)).mono (by omega))
    refine key.mono fun w c ⟨hw, hc⟩ => ⟨by rw [hw, hkf], ?_⟩
    simp only [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
    exact hc
  have hdW : D.length < W := by
    have := length_lt_wt_list ((D.map Fin.val).map Val.nat)
    simp only [List.length_map] at this
    rw [hDRe] at hDR; omega
  obtain ⟨Wl, hWl⟩ : ∃ Wl, Wl = 4 * W + 30 := ⟨_, rfl⟩
  have hs2 := (Val.list [c0, .nat i]).two_le_size
  have hs3 := (Val.list [c0, .nat i]).size_le_wt
  have A0 := StDC.arg (P := P) (rest := []) (vs := [c0, .nat i]) (j := 0) rfl (W := Wl)
    (by omega) (by omega) (by omega)
  have A1 := StDC.arg (P := P) (rest := []) (vs := [c0, .nat i]) (j := 1) rfl (W := Wl)
    (by omega) (by omega) (by omega)
  have g0 := StDC.get A0 (StDC.nat 0 (by omega)) (v := itcqDR Z) rfl (by omega)
  have g1 := StDC.get A0 (StDC.nat 1 (by omega)) (v := itcqRV Z) rfl (by omega)
  have hm2 := wt_list2_le (.nat i) (itcqRV Z)
  have m := StDC.mk2 A1 g1 (by omega) (by omega)
  have hkw := wt_nat_le k
  have cl := StDC.call m hfd (by omega)
  have haw : (Val.nat (a : ℕ)).wt ≤ W := (st_wt_mem (vs := (D.map Fin.val).map Val.nat)
    (List.mem_of_getElem? (by rw [List.getElem?_map, List.getElem?_map, hk]; rfl :
      ((D.map Fin.val).map Val.nat)[k]? = some (.nat (a : ℕ))))).trans (hDRe ▸ hDR)
  have gt := StDC.get (by rw [hDRe] at g0; exact g0) cl (v := .nat (a : ℕ))
    (by rw [List.getElem?_map, List.getElem?_map, hk]; rfl) (by omega)
  refine StDC.funDet hf gt ?_
  clear gt cl m g1 g0 A1 A0
  refine itcq_atC_arith (n := 50) (r := (Val.list [.nat i, itcqRV Z]).wt) hdW (by omega) le_rfl ?_
  rw [hWl] at *
  omega

/-- The cost bound of the points of all ranks. -/
def itcqAtsC (W : ℕ) : ℕ := 10 ^ 8 * (W + 3) ^ 3

theorem itcq_atsC_arith {W d R C : ℕ} (hd : d < W) (hR : R ≤ W + 3)
    (hC : C ≤ d * itcqAtC (4 * W + 10) + mapK * (d + 1) * (W + R + 1)) : C ≤ itcqAtsC W := by
  unfold itcqAtsC itcqAtC mapK at *
  have h1 : (4 * W + 10 + 3) ^ 2 ≤ (5 * (W + 3)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e1 : (5 * (W + 3)) ^ 2 = 25 * (W + 3) ^ 2 := by ring
  have h2 : d * (10 ^ 6 * (4 * W + 10 + 3) ^ 2) ≤ (W + 3) * (10 ^ 6 * (25 * (W + 3) ^ 2)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (e1 ▸ h1))
  have h3 : 1000 * (d + 1) * (W + R + 1) ≤ 1000 * ((W + 3) * (3 * (W + 3))) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e2 : (W + 3) * (10 ^ 6 * (25 * (W + 3) ^ 2)) = 25000000 * (W + 3) ^ 3 := by ring
  have e3 : (W + 3) * (3 * (W + 3)) = 3 * (W + 3) ^ 2 := by ring
  have h4 : (W + 3) ^ 2 ≤ (W + 3) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [e2] at h2
  rw [e3] at h3
  have : (10 : ℕ) ^ 8 = 100000000 := by norm_num
  rw [this]
  omega

/-- **The points of ranks `0, …, d - 1`**: the outer points by color, `itcqDV Z`. -/
theorem itcq_ats_spec {fam f fnd fe : ℕ} (hm : P.HasAt fam (mapFuns fam f))
    (hf : P.funs[f]? = some (itcqAtB fnd)) (hfnd : P.HasAt fnd (findFuns fnd fe))
    (hfe : P.funs[fe]? = some eqTestF) (Z : PairCfg q) {W : ℕ}
    (hW : (Val.list [.list [itcqDR Z, itcqRV Z],
      natList (List.range (itciFl Z.fiberᶜ).length)]).wt ≤ W) :
    FunDet P fam (.list [.list [itcqDR Z, itcqRV Z],
      natList (List.range (itciFl Z.fiberᶜ).length)]) (itcqDV Z) (itcqAtsC W) := by
  set c0 : Val := .list [itcqDR Z, itcqRV Z]
  have hc0 : c0.wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hDR : (itcqDR Z).wt ≤ W := (st_wt_mem (by simp [c0])).trans hc0
  have hdW : (itciFl Z.fiberᶜ).length < W := by
    have := length_lt_wt_list (((itciFl Z.fiberᶜ).map Fin.val).map Val.nat)
    simp only [List.length_map] at this
    have e : itcqDR Z = .list (((itciFl Z.fiberᶜ).map Fin.val).map Val.nat) := rfl
    rw [e] at hDR; omega
  have key := itcq_mapPosV_spec (P := P) hm (c := c0) (m := (itciFl Z.fiberᶜ).length)
    (g := fun t => .nat (((itciAt Z t).map Fin.val).getD 0)) (Bd := itcqAtC (4 * W + 10))
    (fun t => by
      have h2 := wt_list2_le c0 (.nat (t : ℕ))
      have := wt_nat_le (t : ℕ)
      have := t.isLt
      exact itcq_atB_spec hf hfnd hfe Z t.isLt (W := 4 * W + 10)
        (show (Val.list [c0, .nat (t : ℕ)]).wt ≤ 4 * W + 10 by omega))
  have hval : Val.list ((List.finRange (itciFl Z.fiberᶜ).length).map
      fun t : Fin (itciFl Z.fiberᶜ).length => Val.nat (((itciAt Z t.1).map Fin.val).getD 0)) =
      itcqDV Z := by
    rw [itcqDV, natList, itcq_dv_at, ← List.map_coe_finRange_eq_range, List.map_map]
    rfl
  refine key.mono fun w c ⟨hw, hc⟩ => ⟨hw.trans hval, ?_⟩
  rw [hw, hval] at hc
  have hDV := itcq_dv_wt_eq Z
  refine itcq_atsC_arith hdW (R := (itcqDV Z).wt) (by omega) (hc.trans ?_)
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _

theorem itcq_dsC_arith {W q d n C Wl : ℕ} (hq : q < W) (hd : d ≤ q) (hn : n ≤ 100)
    (hWl : Wl = 60 * (W + 1) ^ 2 + 100)
    (hC : C ≤ n * (Wl + 1) + (itcqFlC W + (itcqRksC Wl + (10000 * (d + 1) ^ 3 + itcqAtsC Wl)))) :
    C ≤ itcqDsC W := by
  unfold itcqDsC itcqFlC itcqRksC itcqAtsC at *
  have hT : 9 ≤ (W + 3) ^ 2 := by nlinarith
  have hW1 : (W + 1) ^ 2 ≤ (W + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hl : Wl + 3 ≤ 72 * (W + 3) ^ 2 := by omega
  have r4 : (Wl + 3) ^ 4 ≤ (72 * (W + 3) ^ 2) ^ 4 := Nat.pow_le_pow_left hl 4
  have r3 : (Wl + 3) ^ 3 ≤ (72 * (W + 3) ^ 2) ^ 3 := Nat.pow_le_pow_left hl 3
  have e4 : (72 * (W + 3) ^ 2) ^ 4 = 26873856 * (W + 3) ^ 8 := by ring
  have e3 : (72 * (W + 3) ^ 2) ^ 3 = 373248 * (W + 3) ^ 6 := by ring
  have f3 : (W + 2) ^ 3 ≤ (W + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have d3 : (d + 1) ^ 3 ≤ (W + 3) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have p23 : (W + 3) ^ 2 ≤ (W + 3) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p36 : (W + 3) ^ 3 ≤ (W + 3) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have p68 : (W + 3) ^ 6 ≤ (W + 3) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hnW : n * (Wl + 1) ≤ 100 * (72 * (W + 3) ^ 2) := Nat.mul_le_mul hn (by omega)
  rw [e4] at r4
  rw [e3] at r3
  have k1 : (10 : ℕ) ^ 11 * (Wl + 3) ^ 4 ≤ 10 ^ 11 * (26873856 * (W + 3) ^ 8) :=
    Nat.mul_le_mul_left _ r4
  have k2 : (10 : ℕ) ^ 8 * (Wl + 3) ^ 3 ≤ 10 ^ 8 * (373248 * (W + 3) ^ 6) :=
    Nat.mul_le_mul_left _ r3
  generalize (W + 3) ^ 2 = T2 at *
  generalize (W + 3) ^ 3 = T3 at *
  generalize (W + 3) ^ 6 = T6 at *
  generalize (W + 3) ^ 8 = T8 at *
  norm_num at *
  omega

set_option maxHeartbeats 2000000 in
/-- **The outer points by color**, as a program: `itcqDV Z`. -/
theorem itcq_dsF_spec {f fdl fr ff2 fn fb frm frb flt fl fam fat fnd fe : ℕ}
    (hf : P.funs[f]? = some (itcqDsF fdl frm fr fam))
    (hdl : P.funs[fdl]? = some (itcqFlF fr ff2)) (hr : P.HasAt fr (rangeFuns fr))
    (hff2 : P.HasAt ff2 (filterFuns ff2 fn)) (hfn : P.funs[fn]? = some (itcqNfT fb))
    (hfb : P.funs[fb]? = some itcqFbT)
    (hrm : P.HasAt frm (mapFuns frm frb)) (hrb : P.funs[frb]? = some (itcqRkB flt))
    (hflt : P.HasAt flt (filterFuns flt fl)) (hfl : P.funs[fl]? = some itcqLtT)
    (ham : P.HasAt fam (mapFuns fam fat)) (hat : P.funs[fat]? = some (itcqAtB fnd))
    (hfnd : P.HasAt fnd (findFuns fnd fe)) (hfe : P.funs[fe]? = some eqTestF)
    (Z : PairCfg q) (z₀ : ℕ) {W : ℕ} (hW : (Val.list [rcColVal Z, .nat Z.j, .nat z₀]).wt ≤ W) :
    FunDet P f (.list [rcColVal Z, .nat Z.j, .nat z₀]) (itcqDV Z) (itcqDsC W) := by
  set cZ : Val := .list [rcColVal Z, .nat Z.j, .nat z₀]
  have hq : q < W := lt_of_lt_of_le (itcq_q_le Z)
    ((st_wt_mem (show rcColVal Z ∈ [rcColVal Z, .nat Z.j, .nat z₀] by simp)).trans hW)
  have hd := itcq_fl_len Z
  have hDR := itcq_dr_wt Z
  have hRV := itcq_rv_wt Z
  have hDV := itcq_dv_wt_eq Z
  have hq2 : (q + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hq1 : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hRng := itcq_range_wt (itciFl Z.fiberᶜ).length
  have hd2 : ((itciFl Z.fiberᶜ).length + 1) ^ 2 ≤ (q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  obtain ⟨Wl, hWl⟩ : ∃ Wl, Wl = 60 * (W + 1) ^ 2 + 100 := ⟨_, rfl⟩
  have hW1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have x1 := wt_list2_le cZ (itcqDR Z)
  have x2 := wt_list2_le (.list [cZ, itcqDR Z]) (itcqDR Z)
  have x3 := wt_list2_le (itcqDR Z) (itcqRV Z)
  have x4 := wt_list2_le (.list [itcqDR Z, itcqRV Z])
    (natList (List.range (itciFl Z.fiberᶜ).length))
  have x5 := wt_nat_le (itciFl Z.fiberᶜ).length
  have v0 := StDC.var' (P := P) (env := [cZ]) (i := 0) rfl (W := Wl) (by omega)
  have c1 := StDC.call v0 (itcq_dlF_spec hdl hr hff2 hfn hfb Z z₀ hW) (by omega)
  have u0 := StDC.var' (P := P) (env := [cZ, itcqDR Z]) (i := 0) rfl (W := Wl) (by omega)
  have u1 := StDC.var' (P := P) (env := [cZ, itcqDR Z]) (i := 1) rfl (W := Wl) (by omega)
  have m1 := StDC.mk2 (StDC.mk2 u0 u1 (by omega) (by omega)) u1 (by omega) (by omega)
  have c2 := StDC.call m1 (itcq_rks_spec hrm hrb hflt hfl Z z₀ (W := Wl)
    (show (Val.list [.list [cZ, itcqDR Z], itcqDR Z]).wt ≤ Wl by omega)) (by omega)
  have w1 := StDC.var' (P := P) (env := [cZ, itcqDR Z, itcqRV Z]) (i := 1) rfl (W := Wl)
    (by omega)
  have w2 := StDC.var' (P := P) (env := [cZ, itcqDR Z, itcqRV Z]) (i := 2) rfl (W := Wl)
    (by omega)
  have ln := StDC.length (vs := ((itciFl Z.fiberᶜ).map Fin.val).map Val.nat) w1
    (by simp only [List.length_map]; omega)
  simp only [List.length_map] at ln
  have cr := StDC.call ln (st_range_det hr (itciFl Z.fiberᶜ).length) (by omega)
  have m2 := StDC.mk2 (StDC.mk2 w1 w2 (by omega) (by omega)) cr (by omega) (by omega)
  have c3 := StDC.call m2 (itcq_ats_spec ham hat hfnd hfe Z (W := Wl) (by omega)) (by omega)
  have l2 := StDC.letE c2 c3 (by omega)
  have l1 := StDC.letE c1 l2 (by omega)
  refine StDC.funDet hf l1 ?_
  clear l1 l2 c3 m2 cr ln w2 w1 c2 m1 u1 u0 c1 v0
  exact itcq_dsC_arith hq hd (n := 100) le_rfl hWl (by omega)

/-- **The color of a point**, in cost `20 (W + 1)`. -/
theorem itcq_coB_spec {f : ℕ} (hf : P.funs[f]? = some itcqCoB) (Z : PairCfg q) (z₀ : ℕ)
    (a : Fin q) {W : ℕ} (hW : (Val.list [.list [rcColVal Z, .nat Z.j, .nat z₀], .nat a]).wt ≤ W) :
    FunDet P f (.list [.list [rcColVal Z, .nat Z.j, .nat z₀], .nat a]) (.nat (Z.col a a))
      (20 * (W + 1)) := by
  set cZ : Val := .list [rcColVal Z, .nat Z.j, .nat z₀]
  have hcZ : cZ.wt ≤ W := (st_wt_mem (by simp)).trans hW
  have haw : (Val.nat a).wt ≤ W := (st_wt_mem (by simp)).trans hW
  have h4 : 4 ≤ W := by have := wt_list_eq [cZ, .nat (a : ℕ)]; omega
  have A0 := StDC.arg (P := P) (rest := []) (vs := [cZ, .nat a]) (j := 0) rfl hW (by omega) hcZ
  have A1 := StDC.arg (P := P) (rest := []) (vs := [cZ, .nat a]) (j := 1) rfl hW (by omega) haw
  exact StDC.funDet hf (itcq_coE_st A0 A1 hcZ) (by omega)

theorem itcq_coC_arith {W q d A B C : ℕ} (hq : q < W) (hd : d ≤ q) (hA : A ≤ W)
    (hB : B ≤ d * (2 * W + 1) + 4)
    (hC : C ≤ d * (20 * (4 * W + 10 + 1)) + mapK * (d + 1) * (A + B + 1)) : C ≤ itcqCoC W := by
  unfold itcqCoC mapK at *
  have h1 : d * (20 * (4 * W + 10 + 1)) ≤ (W + 2) * (100 * (W + 2)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : d * (2 * W + 1) ≤ (W + 2) * (2 * (W + 2)) := Nat.mul_le_mul (by omega) (by omega)
  have e1 : (W + 2) * (100 * (W + 2)) = 100 * (W + 2) ^ 2 := by ring
  have e2 : (W + 2) * (2 * (W + 2)) = 2 * (W + 2) ^ 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  have hs : W + 2 ≤ (W + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : 1000 * (d + 1) * (A + B + 1) ≤ 1000 * ((W + 2) * (4 * (W + 2) ^ 2)) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have e3 : (W + 2) * (4 * (W + 2) ^ 2) = 4 * (W + 2) ^ 3 := by ring
  rw [e3] at h3
  have h4 : (W + 2) ^ 2 ≤ (W + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have : (10 : ℕ) ^ 6 = 1000000 := by norm_num
  rw [this]
  omega

/-- **The colors along `itciFo Z`**, by the map of `itcqCoB` over `itcqDV Z`. -/
theorem itcq_cols_spec {fcm fco : ℕ} (hm : P.HasAt fcm (mapFuns fcm fco))
    (hf : P.funs[fco]? = some itcqCoB) (Z : PairCfg q) (z₀ : ℕ) {W : ℕ}
    (hW : (Val.list [.list [rcColVal Z, .nat Z.j, .nat z₀], itcqDV Z]).wt ≤ W) :
    FunDet P fcm (.list [.list [rcColVal Z, .nat Z.j, .nat z₀], itcqDV Z])
      (natList ((itciFo Z).map fun a => Z.col a a)) (itcqCoC W) := by
  set cZ : Val := .list [rcColVal Z, .nat Z.j, .nat z₀]
  have hcZ : cZ.wt ≤ W := (st_wt_mem (by simp)).trans hW
  have hq : q < W := lt_of_lt_of_le (itcq_q_le Z)
    ((st_wt_mem (show rcColVal Z ∈ [rcColVal Z, .nat Z.j, .nat z₀] by simp)).trans hcZ)
  have hd : (itciFo Z).length ≤ q := by
    rw [itciFo_length]; exact Finset.card_le_univ _ |>.trans (by simp)
  have key := itcq_mapPts_spec (P := P) hm (c := cZ) (itciFo Z)
    (g := fun a => .nat (Z.col a a)) (Bd := 20 * (4 * W + 10 + 1)) (fun a _ => by
      have h2 := wt_list2_le cZ (.nat (a : ℕ))
      have := wt_nat_le (a : ℕ)
      have := a.isLt
      exact itcq_coB_spec hf Z z₀ a (W := 4 * W + 10)
        (show (Val.list [cZ, .nat (a : ℕ)]).wt ≤ 4 * W + 10 by omega))
  have hcol : ∀ a : Fin q, (Val.nat (Z.col a a)).wt ≤ W := fun a =>
    ((st_wt_mem (List.mem_of_getElem? (encFun_getElem? (Z.col a) a))).trans
      (st_wt_mem (List.mem_of_getElem? (itcq_col_get Z a)))).trans
      ((st_wt_mem (show rcColVal Z ∈ [rcColVal Z, .nat Z.j, .nat z₀] by simp)).trans hcZ)
  have hval : Val.list ((itciFo Z).map fun a => Val.nat (Z.col a a)) =
      natList ((itciFo Z).map fun a => Z.col a a) := by
    rw [natList, List.map_map]; rfl
  refine key.mono fun w c ⟨hw, hc⟩ => ⟨hw.trans hval, ?_⟩
  rw [hw] at hc
  have hout := wt_list_le_of ((itciFo Z).map fun a => Val.nat (Z.col a a)) (c := W) (by
    intro v hv; obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv; exact hcol a)
  simp only [List.length_map] at hout
  exact itcq_coC_arith hq hd hW hout hc

end Prog

end GI.Impl
