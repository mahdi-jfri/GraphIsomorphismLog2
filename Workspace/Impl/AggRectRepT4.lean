module

public import Workspace.Impl.AggRectRepT3

@[expose] public section

/-!
# Stage 3 of the representation program, single labels

`rcR_carF_spec`: for single labels the program reads the row labels of the canonical state, lists
the keys of the rows (`rcRKeysN`) and the row numbers of the positions (`rcRRowN'`), turns each
graph pair `(g, π)` of `G` into `(g, ρ(g) ⊕ π)` and each generator `σ` of `P` into
`embed(σ) ⊕ σ`, and makes one **Preimage** call (`graphPre_spec`) on these lists.
-/

namespace GI.Impl

open GI.Lang
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encPerms encPts encGroup gens Preimage)
open Equiv

section Car

variable {P : Program} {I : RcRIdx}

/-- The row numbers of the positions. -/
def rcRRowT (dl rl : List ℕ) (k : ℕ) : List ℕ := (List.range k).map (rcRRowN' dl rl k)

theorem rcR_keysN_lt {dl rl : List ℕ} {k : ℕ} : ∀ x ∈ rcRKeysN dl rl k, x < k := by
  intro x hx
  unfold rcRKeysN at hx
  exact List.mem_range.1 (List.mem_filter.1 hx).1

theorem rcR_keysN_len (dl rl : List ℕ) (k : ℕ) : (rcRKeysN dl rl k).length ≤ k := by
  unfold rcRKeysN
  have := List.length_filter_le (fun j => dl.getD j 0 == 1 && rcRKeyN dl rl k j == j)
    (List.range k)
  rw [List.length_range] at this
  exact this

theorem rcR_rowT_le (dl rl : List ℕ) (k : ℕ) : ∀ x ∈ rcRRowT dl rl k, x ≤ k := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  unfold rcRRowN'
  exact (List.findIdx_le_length).trans (rcR_keysN_len dl rl k)

set_option maxHeartbeats 8000000 in
/-- **Stage 3, single labels.** -/
theorem rcR_carF_spec (ok : RcROk P I) (hpre : Preimage)
    (hj : P.prims[I.jpre]? = some (preimagePrim hpre)) {k q m : ℕ} (svs : List Val)
    (hsv0 : svs[0]? = some (.nat k)) (dl : List ℕ) (hsv2 : svs[2]? = some (natList dl))
    (rlab : List ℕ) (mv cv : Val) (hsv6 : svs[6]? = some (.list [.list [mv, natList rlab, cv]]))
    (ps : List (Perm (Fin k) × Perm (Fin q))) (wl rl : List ℕ)
    (a0 a1 a2 a4 a5 : Val) (ms : List (Perm (Fin q)))
    (hm : (rcRKeysN dl rlab k).length = m)
    (ρf : Perm (Fin k) × Perm (Fin q) → Perm (Fin m))
    (hρ : ∀ p ∈ ps, (List.range m).map (fun r => (rcRRowT dl rlab k).getD
      ((rcRL fun i => (p.1 i : ℕ)).getD ((rcRKeysN dl rlab k).getD r 0) 0) 0) =
        rcRL fun r => (ρf p r : ℕ))
    (τf : Perm (Fin q) → Perm (Fin m))
    (hτ : ∀ σ ∈ ms, (List.range m).map (fun j => if j < q then (rcRL fun i => (σ i : ℕ)).getD j 0
      else j) = rcRL fun r => (τf σ r : ℕ))
    (hms : ∀ m' ∈ ms.map (fun σ => encPair (τf σ, σ)), ∃ p ∈ Subgroup.closure
      {p | p ∈ ps.map fun p => (p.1, encPair (ρf p, p.2))}, MonoidHom.snd _ _ p = m') {M W : ℕ}
    (hA : (Val.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]).wt ≤ M)
    (hk : k ≤ M) (hq : q ≤ M) (hml : ms.length ≤ (M + 1) ^ 2) (hW : 10 ^ 6 * (M + 1) ^ 10 ≤ W)
    (hIn : (Val.list [.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl],
      .list [a0, a1, a2, .list (ms.map encPerm), a4, a5, natList (List.range k)]]).wt ≤ W) :
    CpFB P I.carF (.list [.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl],
        .list [a0, a1, a2, .list (ms.map encPerm), a4, a5, natList (List.range k)]]) W
      ((preimagePrim hpre).boundSize W + 10 ^ 18 * (W + 1) ^ 8)
      (fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin (m + q))),
        w = .list [.list (qs.map pairV), natList (rcRRowT dl rlab k)] ∧
        qs.length ≤ (k + (m + q)) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} =
          Subgroup.closure {p | p ∈ ps.map fun p => (p.1, encPair (ρf p, p.2))} ⊓
            (gens (ms.map fun σ => encPair (τf σ, σ))).comap (MonoidHom.snd _ _)) := by
  obtain ⟨Av, hAv⟩ : ∃ Av : Val,
      Av = .list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl] := ⟨_, rfl⟩
  obtain ⟨Rv, hRv⟩ : ∃ Rv : Val,
      Rv = .list [a0, a1, a2, .list (ms.map encPerm), a4, a5, natList (List.range k)] := ⟨_, rfl⟩
  rw [← hAv] at hA hIn ⊢
  rw [← hRv] at hIn ⊢
  -- powers
  have hp1 : M + 1 ≤ (M + 1) ^ 2 := by
    calc M + 1 = (M + 1) ^ 1 := (pow_one _).symm
      _ ≤ (M + 1) ^ 2 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp2 : (M + 1) ^ 2 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp3 : (M + 1) ^ 3 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hp6 : (M + 1) ^ 6 ≤ (M + 1) ^ 10 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU : W + 1 ≤ (W + 1) ^ 8 := by
    calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
      _ ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have hL8 : 10 ^ 6 * (W + 1) ≤ (W + 1) ^ 8 := rcR_lin_le (by
    have : 1 ≤ (M + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    omega) (by norm_num)
  have hU2 : (W + 1) ^ 2 ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU3 : (W + 1) ^ 3 ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU5 : (W + 1) ^ 5 ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have hU4 : (W + 1) ^ 4 ≤ (W + 1) ^ 8 := rcR_pow_le_pow (by omega) (by norm_num)
  have h35 : (W + 1) ^ (3 + 2) = (W + 1) ^ 5 := rfl
  -- weights of the input
  have wsv : (Val.list svs).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wqv : (Val.nat q).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wpv : (Val.list (ps.map pairV)).wt < Av.wt := by rw [hAv]; exact wt_le_wt_list (by simp)
  have wkv : (Val.nat k).wt < (Val.list svs).wt := wt_le_wt_list (List.mem_of_getElem? hsv0)
  have wdl : (natList dl).wt < (Val.list svs).wt := wt_le_wt_list (List.mem_of_getElem? hsv2)
  have wr6 : (Val.list [.list [mv, natList rlab, cv]]).wt < (Val.list svs).wt :=
    wt_le_wt_list (List.mem_of_getElem? hsv6)
  have wr60 : (Val.list [mv, natList rlab, cv]).wt < (Val.list [.list [mv, natList rlab, cv]]).wt :=
    wt_le_wt_list (by simp)
  have wrlab : (natList rlab).wt < (Val.list [mv, natList rlab, cv]).wt := wt_le_wt_list (by simp)
  have wAv : Av.wt < (Val.list [Av, Rv]).wt := wt_le_wt_list (by simp)
  have wRv : Rv.wt < (Val.list [Av, Rv]).wt := wt_le_wt_list (by simp)
  have wmv : (Val.list (ms.map encPerm)).wt < Rv.wt := by rw [hRv]; exact wt_le_wt_list (by simp)
  have wrk : (natList (List.range k)).wt ≤ 5 * (M + 1) ^ 2 := rcR_wt_range k M hk
  have wms : (Val.list (ms.map encPerm)).wt ≤ 52 * (M + 1) ^ 6 := by
    have h1 := wt_list_encPerms_le ms
    have h2 : (ms.length + 1) * (q + 1) ≤ 2 * (M + 1) ^ 3 :=
      calc (ms.length + 1) * (q + 1) ≤ (2 * (M + 1) ^ 2) * (M + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 2 * (M + 1) ^ 3 := by ring
    have h3 := rcR_pow_mono h2 2
    have h4 : (2 * (M + 1) ^ 3) ^ 2 = 4 * (M + 1) ^ 6 := by ring
    omega
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  -- the lists computed on the way
  obtain ⟨keys, hkeys⟩ : ∃ keys, keys = rcRKeysN dl rlab k := ⟨_, rfl⟩
  obtain ⟨rowT, hrowT⟩ : ∃ rowT, rowT = rcRRowT dl rlab k := ⟨_, rfl⟩
  have hkl : keys.length = m := by rw [hkeys]; exact hm
  have hmk : m ≤ k := by rw [← hkl, hkeys]; exact rcR_keysN_len dl rlab k
  have hklt : ∀ x ∈ keys, x < k := by rw [hkeys]; exact rcR_keysN_lt
  have wkeys : (natList keys).wt ≤ 5 * (M + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by have := hklt y hy; omega) (by omega)
  have wrowT : (natList rowT).wt ≤ 5 * (M + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by
      rw [hrowT] at hy; have := rcR_rowT_le dl rlab k y hy; omega)
      (by rw [hrowT]; unfold rcRRowT; rw [List.length_map, List.length_range]; exact hk)
  have wrm : (natList (List.range m)).wt ≤ 5 * (M + 1) ^ 2 := rcR_wt_range m M (by omega)
  have wmm := wt_nat_le m
  obtain ⟨ps', hps'⟩ : ∃ ps' : List (Perm (Fin k) × Perm (Fin (m + q))),
      ps' = ps.map fun p => (p.1, encPair (ρf p, p.2)) := ⟨_, rfl⟩
  obtain ⟨ms', hms'⟩ : ∃ ms' : List (Perm (Fin (m + q))),
      ms' = ms.map fun σ => encPair (τf σ, σ) := ⟨_, rfl⟩
  have hpsl : ps'.length = ps.length := by rw [hps', List.length_map]
  have hmsl : ms'.length = ms.length := by rw [hms', List.length_map]
  have hpl : ps.length < M := by
    have := length_lt_wt_list (ps.map pairV)
    rw [List.length_map] at this; omega
  have wps' : (Val.list (ps'.map pairV)).wt ≤ 1000 * (M + 1) ^ 3 := by
    have h1 := wt_list_le_of (ps'.map pairV) (c := 198 * (M + 1) ^ 2) (by
      intro v hv
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hv
      have := wt_pairV_le p
      have h2 : (k + (m + q) + 1) ^ 2 ≤ (3 * (M + 1)) ^ 2 := rcR_pow_mono (by omega) 2
      have h3 : (3 * (M + 1)) ^ 2 = 9 * (M + 1) ^ 2 := by ring
      omega)
    rw [List.length_map, hpsl] at h1
    have h2 : ps.length * (2 * (198 * (M + 1) ^ 2) + 1) ≤ (M + 1) * (397 * (M + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h3 : (M + 1) * (397 * (M + 1) ^ 2) = 397 * (M + 1) ^ 3 := by ring
    have : 1 ≤ (M + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have wms' : (Val.list (ms'.map encPerm)).wt ≤ 208 * (M + 1) ^ 6 := by
    have h1 := wt_list_encPerms_le ms'
    rw [hmsl] at h1
    have h2 : (ms.length + 1) * (m + q + 1) ≤ 4 * (M + 1) ^ 3 :=
      calc (ms.length + 1) * (m + q + 1) ≤ (2 * (M + 1) ^ 2) * (2 * (M + 1)) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 4 * (M + 1) ^ 3 := by ring
    have h3 := rcR_pow_mono h2 2
    have h4 : (4 * (M + 1) ^ 3) ^ 2 = 16 * (M + 1) ^ 6 := by ring
    omega
  -- reading the input
  have dA : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (arg 0)
      (.list [.list svs, .nat q, .list (ps.map pairV), natList wl, natList rl]) W (2 * W + 5) :=
    fun rest => (rcRDW.arg (vs := [Av, Rv]) (rest := rest) (j := 0) (v := Av) hIn rfl).cast hAv
  have dR : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (arg 1)
      (.list [a0, a1, a2, .list (ms.map encPerm), a4, a5, natList (List.range k)]) W
      (2 * W + 6) :=
    fun rest => (rcRDW.arg (vs := [Av, Rv]) (rest := rest) (j := 1) (v := Rv) hIn rfl).cast hRv
  have dsv : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (arg 0) (.nat 0)) (.list svs) W
      (3 * W + 9) := fun rest => (rcRDW.get (dA rest) (j := 0) (v := .list svs) rfl).mono (by omega)
  have dk : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (.get (arg 0) (.nat 0)) (.nat 0))
      (.nat k) W (4 * W + 13) := fun rest => (rcRDW.get (dsv rest) hsv0).mono (by omega)
  have ddl : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (.get (arg 0) (.nat 0)) (.nat 2))
      (natList dl) W (4 * W + 15) := fun rest => (rcRDW.get (dsv rest) hsv2).mono (by omega)
  have dq : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (arg 0) (.nat 1)) (.nat q) W
      (3 * W + 10) := fun rest => (rcRDW.get (dA rest) (j := 1) (v := .nat q) rfl).mono (by omega)
  have drK : ∀ rest, rcRDW P (.list [Av, Rv] :: rest) (.get (arg 1) (.nat 6))
      (natList (List.range k)) W (3 * W + 16) := fun rest =>
    (rcRDW.get (dR rest) (j := 6) (v := natList (List.range k)) rfl).mono (by omega)
  -- the row labels
  have drl := rcRDW.get (rcRDW.get (rcRDW.get (dsv []) hsv6) (j := 0)
    (v := .list [mv, natList rlab, cv]) rfl) (j := 1) (v := natList rlab) rfl
  obtain ⟨F, hF⟩ : ∃ F, F = (preimagePrim hpre).boundSize W + 10 ^ 17 * (W + 1) ^ 8 := ⟨_, rfl⟩
  refine CpFB.intro ok.carF ((rcR_letC (Cb := F + 7 * 10 ^ 16 * (W + 1) ^ 8)
    (rcR_detC drl (C := (W + 1) ^ 8) (by omega) (Q := (· = natList rlab)) rfl) ?_ le_rfl).mono
      (by omega) fun _ h => h)
  rintro _ rfl -
  -- the keys
  let r1 : List Val := [natList rlab]
  have wc2 := rcR_sum3 (natList dl) (natList rlab) (natList (List.range k))
  have wc2' := wt_list3_le (natList dl) (natList rlab) (natList (List.range k))
  have wi2 := wt_list2_le (.list [natList dl, natList rlab, natList (List.range k)])
    (natList (List.range k))
  have dc2 := rcRDW.mk2 (rcRDW.mk3 (ddl r1) (rcRDW.var (env := .list [Av, Rv] :: r1) (i := 1)
    (v := natList rlab) rfl (by omega)) (drK r1) (by omega)) (drK r1) (by omega)
  have hfil := rcR_filterN ok.fKeys (c := .list [natList dl, natList rlab, natList (List.range k)])
    (xs := List.range k) (t := fun j => dl.getD j 0 == 1 && rcRKeyN dl rlab k j == j)
    (K := 10 ^ 15) (d := 3) (W := W) (fun j hj =>
      (rcR_keysP_spec ok.gD ok.keysP ok.keyN ok.fKey ok.keyP dl rlab k j).mono (by
        have h1 := rcR_wt_elemN (c := .list [natList dl, natList rlab, natList (List.range k)]) hj
        have := rcR_cube_cost (K := 10 ^ 12) (W := W)
          (a := (Val.list [.list [natList dl, natList rlab, natList (List.range k)], .nat j]).wt)
          (by omega)
        norm_num at this ⊢
        omega))
    (by omega) (by
      have := rcR_wt_filter (List.range k) (fun j => dl.getD j 0 == 1 && rcRKeyN dl rlab k j == j)
      omega)
  have ekeys : natList ((List.range k).filter fun j => dl.getD j 0 == 1 && rcRKeyN dl rlab k j == j)
      = natList keys := by rw [hkeys]; rfl
  rw [ekeys] at hfil
  have dkeys := rcRDW.call dc2 hfil (by omega)
  refine rcR_letC (Cb := F + 6 * 10 ^ 16 * (W + 1) ^ 8)
    (rcR_detC dkeys (C := 2 * 10 ^ 15 * (W + 1) ^ 8) (by omega) (Q := (· = natList keys)) rfl) ?_
    (by omega)
  rintro _ rfl -
  -- the row numbers
  let r2 : List Val := [natList rlab, natList keys]
  have wc3 := rcR_sum4 (natList dl) (natList rlab) (natList (List.range k)) (natList keys)
  have wc3' := wt_list4_le (natList dl) (natList rlab) (natList (List.range k)) (natList keys)
  have wi3 := wt_list2_le (.list [natList dl, natList rlab, natList (List.range k), natList keys])
    (natList (List.range k))
  have dc3 := rcRDW.mk2 (rcRDW.mk4 (ddl r2) (rcRDW.var (env := .list [Av, Rv] :: r2) (i := 1)
    (v := natList rlab) rfl (by omega)) (drK r2) (rcRDW.var (i := 2) (v := natList keys) rfl
    (by omega)) (by omega)) (drK r2) (by omega)
  have erow : (List.range k).map (fun i => Val.nat (keys.findIdx fun t => t == rcRKeyN dl rlab k i))
      = rowT.map Val.nat := by
    rw [hrowT, hkeys]; unfold rcRRowT; rw [List.map_map]; rfl
  have hmapR := rcR_mapN ok.mRow
    (c := .list [natList dl, natList rlab, natList (List.range k), natList keys])
    (xs := List.range k) (g := fun i => .nat (keys.findIdx fun t => t == rcRKeyN dl rlab k i))
    (K := 10 ^ 15) (d := 3) (W := W) (fun i hi =>
      (rcR_rowF_spec ok.gD ok.rowF ok.keyN ok.fKey ok.keyP ok.fEq dl rlab k keys hklt i).mono (by
        have h1 := rcR_wt_elemN
          (c := .list [natList dl, natList rlab, natList (List.range k), natList keys]) hi
        have := rcR_cube_cost (K := 10 ^ 12) (W := W)
          (a := (Val.list [.list [natList dl, natList rlab, natList (List.range k), natList keys],
            .nat i]).wt) (by omega)
        norm_num at this ⊢
        omega))
    (by omega) (by rw [erow]; show (natList rowT).wt ≤ W; omega)
  rw [erow] at hmapR
  have drow := rcRDW.call dc3 hmapR (by show (natList rowT).wt ≤ W; omega)
  refine rcR_letC (Cb := F + 5 * 10 ^ 16 * (W + 1) ^ 8)
    (rcR_detC drow (C := 2 * 10 ^ 15 * (W + 1) ^ 8) (by omega)
      (Q := (· = natList rowT)) rfl) ?_ (by omega)
  rintro _ rfl -
  -- the number of rows
  let r3 : List Val := [natList rlab, natList keys, natList rowT]
  have dm := (rcRDW.length (rcRDW.var (P := P) (W := W) (env := .list [Av, Rv] :: r3) (i := 2)
    (v := natList keys) rfl (by omega))).cast
    (show Val.nat (keys.map Val.nat).length = .nat m by rw [List.length_map, hkl])
  refine rcR_letC (Cb := F + 4 * 10 ^ 16 * (W + 1) ^ 8)
    (rcR_detC dm (C := (W + 1) ^ 8) (by omega) (Q := (· = .nat m)) rfl) ?_ (by omega)
  rintro _ rfl -
  let r4 : List Val := [natList rlab, natList keys, natList rowT, .nat m]
  have hrng : FunDet P I.rng (.nat m) (natList (List.range m))
      (loopModK * (m + 1) * ((Val.nat m).wt + m + (natList (List.range m)).wt + 1)) :=
    (range_spec ok.rng m).mono fun w c ⟨hw, hc⟩ => ⟨hw, by rw [hw] at hc; exact hc⟩
  have hK : loopModK = 1000 := rfl
  have hrc : loopModK * (m + 1) * ((Val.nat m).wt + m + (natList (List.range m)).wt + 1) ≤
      1000 * (W + 1) ^ 2 := by
    rw [hK, Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc (m + 1) * ((Val.nat m).wt + m + (natList (List.range m)).wt + 1) ≤ (W + 1) * (W + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = (W + 1) ^ 2 := (pow_two _).symm
  have drm := rcRDW.call (rcRDW.var (P := P) (W := W) (env := .list [Av, Rv] :: r4) (i := 4)
    (v := .nat m) rfl (by omega)) hrng (by omega)
  refine rcR_letC (Cb := F + 3 * 10 ^ 16 * (W + 1) ^ 8)
    (rcR_detC drm (C := 10 ^ 4 * (W + 1) ^ 8) (by omega) (Q := (· = natList (List.range m))) rfl)
    ?_ (by omega)
  rintro _ rfl -
  -- the pairs `(g, ρ(g) ⊕ π)`
  let r5 : List Val := [natList rlab, natList keys, natList rowT, .nat m, natList (List.range m)]
  have wc6 := rcR_sum4 (natList rowT) (natList keys) (.nat m) (natList (List.range m))
  have wc6' := wt_list4_le (natList rowT) (natList keys) (.nat m) (natList (List.range m))
  have wi6 := wt_list2_le (.list [natList rowT, natList keys, .nat m, natList (List.range m)])
    (.list (ps.map pairV))
  have dc6 := rcRDW.mk2 (rcRDW.mk4 (rcRDW.var (P := P) (W := W) (env := .list [Av, Rv] :: r5)
      (i := 3) (v := natList rowT) rfl (by omega))
    (rcRDW.var (i := 2) (v := natList keys) rfl (by omega))
    (rcRDW.var (i := 4) (v := .nat m) rfl (by omega))
    (rcRDW.var (i := 5) (v := natList (List.range m)) rfl (by omega)) (by omega))
    ((rcRDW.get (dA r5) (j := 2) (v := .list (ps.map pairV)) rfl)) (by omega)
  have eps : ps.map (fun p => pairV (p.1, encPair (ρf p, p.2))) = ps'.map pairV := by
    rw [hps', List.map_map]; rfl
  have hmapP := mapList_spec ok.mPs ps pairV (fun p => pairV (p.1, encPair (ρf p, p.2)))
    (c := .list [natList rowT, natList keys, .nat m, natList (List.range m)])
    (B := 10 ^ 10 * (W + 1) ^ 3) (fun a _ a' _ he => by rw [pairV_injective he])
    (fun p hp => by
      have hρ' := hρ p hp
      rw [← hrowT, ← hkeys] at hρ'
      refine rcR_ps_spec ok.gD ok.psF ok.mRho ok.rhoF ok.pe rowT keys p.1 p.2 (ρf p) hρ' ?_
      have h1 := wt_pairV_le p
      have h2 := rcR_wt_elem (c := .list [natList rowT, natList keys, .nat m,
        natList (List.range m)]) (ys := ps.map pairV) (List.mem_map.2 ⟨p, hp, rfl⟩)
      have h3 : (k + m + q + 1) ^ 2 ≤ (3 * (M + 1)) ^ 2 := rcR_pow_mono (by omega) 2
      have h4 : (3 * (M + 1)) ^ 2 = 9 * (M + 1) ^ 2 := by ring
      show 10 * (Val.list [.list [natList rowT, natList keys, .nat m, natList (List.range m)],
        pairV p]).wt + 100 * (k + m + q + 1) ^ 2 + 100 ≤ W
      omega)
  rw [eps] at hmapP
  have hmK : mapK = 1000 := rfl
  have cps : ps.length * (10 ^ 10 * (W + 1) ^ 3) + mapK * (ps.length + 1) *
      ((Val.list [.list [natList rowT, natList keys, .nat m, natList (List.range m)],
        .list (ps.map pairV)]).wt + (Val.list (ps'.map pairV)).wt + 1) ≤ 10 ^ 11 * (W + 1) ^ 8 := by
    have h1 : ps.length * (10 ^ 10 * (W + 1) ^ 3) ≤ (W + 1) * (10 ^ 10 * (W + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (W + 1) * (10 ^ 10 * (W + 1) ^ 3) = 10 ^ 10 * (W + 1) ^ 4 := by ring
    have h3 : (ps.length + 1) * ((Val.list [.list [natList rowT, natList keys, .nat m,
        natList (List.range m)], .list (ps.map pairV)]).wt + (Val.list (ps'.map pairV)).wt + 1) ≤
        (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h4 : (W + 1) * (W + 1) = (W + 1) ^ 2 := (pow_two _).symm
    have h5 : mapK * (ps.length + 1) * ((Val.list [.list [natList rowT, natList keys, .nat m,
        natList (List.range m)], .list (ps.map pairV)]).wt + (Val.list (ps'.map pairV)).wt + 1) ≤
        1000 * (W + 1) ^ 2 := by
      rw [hmK, Nat.mul_assoc, ← h4]; exact Nat.mul_le_mul_left _ h3
    omega
  have dps' := rcRDW.call dc6 (hmapP.mono cps) (by omega)
  refine rcR_letC (Cb := F + 2 * 10 ^ 16 * (W + 1) ^ 8)
    (rcR_detC dps' (C := 2 * 10 ^ 11 * (W + 1) ^ 8) (by omega)
      (Q := (· = .list (ps'.map pairV))) rfl) ?_ (by omega)
  rintro _ rfl -
  -- the generators `embed(σ) ⊕ σ`
  let r6 : List Val := [natList rlab, natList keys, natList rowT, .nat m, natList (List.range m),
    .list (ps'.map pairV)]
  have wc7 := rcR_sum3 (.nat q) (.nat m) (natList (List.range m))
  have wc7' := wt_list3_le (.nat q) (.nat m) (natList (List.range m))
  have wi7 := wt_list2_le (.list [.nat q, .nat m, natList (List.range m)]) (.list (ms.map encPerm))
  have dc7 := rcRDW.mk2 (rcRDW.mk3 (dq r6) (rcRDW.var (P := P) (W := W)
      (env := .list [Av, Rv] :: r6) (i := 4) (v := .nat m) rfl (by omega))
    (rcRDW.var (i := 5) (v := natList (List.range m)) rfl (by omega)) (by omega))
    ((rcRDW.get (dR r6) (j := 3) (v := .list (ms.map encPerm)) rfl)) (by omega)
  have ems : ms.map (fun σ => encPerm (encPair (τf σ, σ))) = ms'.map encPerm := by
    rw [hms', List.map_map]; rfl
  have hmapE := mapList_spec ok.mEmb ms encPerm (fun σ => encPerm (encPair (τf σ, σ)))
    (c := .list [.nat q, .nat m, natList (List.range m)])
    (B := 10 ^ 10 * (W + 1) ^ 3) (fun a _ a' _ he => by rw [encPerm_injective he])
    (fun σ hσ => by
      refine rcR_emb_spec ok.gD ok.embF ok.mEmbR ok.embRF ok.pe σ (τf σ) (hτ σ hσ) ?_
      have h2 := rcR_wt_elem (c := .list [.nat q, .nat m, natList (List.range m)])
        (ys := ms.map encPerm) (List.mem_map.2 ⟨σ, hσ, rfl⟩)
      have h3 : (m + q + 1) ^ 2 ≤ (2 * (M + 1)) ^ 2 := rcR_pow_mono (by omega) 2
      have h4 : (2 * (M + 1)) ^ 2 = 4 * (M + 1) ^ 2 := by ring
      have h5 : (Val.list [.list [.nat q, .nat m, natList (List.range m)], .list (ms.map encPerm)]).wt
          ≤ 200 * (M + 1) ^ 6 := by
        have : (M + 1) ^ 2 ≤ (M + 1) ^ 6 := rcR_pow_le_pow (by omega) (by norm_num)
        omega
      omega)
  rw [ems] at hmapE
  have cms : ms.length * (10 ^ 10 * (W + 1) ^ 3) + mapK * (ms.length + 1) *
      ((Val.list [.list [.nat q, .nat m, natList (List.range m)], .list (ms.map encPerm)]).wt +
        (Val.list (ms'.map encPerm)).wt + 1) ≤ 10 ^ 11 * (W + 1) ^ 8 := by
    have h1 : ms.length * (10 ^ 10 * (W + 1) ^ 3) ≤ (W + 1) * (10 ^ 10 * (W + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : (W + 1) * (10 ^ 10 * (W + 1) ^ 3) = 10 ^ 10 * (W + 1) ^ 4 := by ring
    have h3 : (ms.length + 1) * ((Val.list [.list [.nat q, .nat m, natList (List.range m)],
        .list (ms.map encPerm)]).wt + (Val.list (ms'.map encPerm)).wt + 1) ≤
        (W + 1) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h4 : (W + 1) * (W + 1) = (W + 1) ^ 2 := (pow_two _).symm
    have h5 : mapK * (ms.length + 1) * ((Val.list [.list [.nat q, .nat m,
        natList (List.range m)], .list (ms.map encPerm)]).wt + (Val.list (ms'.map encPerm)).wt + 1)
        ≤ 1000 * (W + 1) ^ 2 := by
      rw [hmK, Nat.mul_assoc, ← h4]; exact Nat.mul_le_mul_left _ h3
    omega
  have dms' := rcRDW.call dc7 (hmapE.mono cms) (by omega)
  refine rcR_letC (Cb := F + 10 ^ 16 * (W + 1) ^ 8)
    (rcR_detC dms' (C := 2 * 10 ^ 11 * (W + 1) ^ 8) (by omega)
      (Q := (· = .list (ms'.map encPerm))) rfl) ?_ (by omega)
  rintro _ rfl -
  -- the Preimage call
  let r7 : List Val := [natList rlab, natList keys, natList rowT, .nat m, natList (List.range m),
    .list (ps'.map pairV), .list (ms'.map encPerm)]
  have wmq := wt_nat_le (m + q)
  have wkmq := wt_list2_le (.nat k) (.nat (m + q))
  have dkmq := rcRDW.mk2 (dk r7) (rcRDW.arith (op := .add) (z := m + q)
    (rcRDW.var (P := P) (W := W) (env := .list [Av, Rv] :: r7) (i := 4) (v := .nat m) rfl
      (by omega)) (dq r7) rfl (by omega)) (by omega)
  have wI := wt_list3_le (.list [.nat k, .nat (m + q)]) (.list (ps'.map pairV))
    (.list (ms'.map encPerm))
  have dI := rcRDW.mk3 dkmq (rcRDW.var (i := 6) (v := .list (ps'.map pairV)) rfl (by omega))
    (rcRDW.var (i := 7) (v := .list (ms'.map encPerm)) rfl (by omega)) (by omega)
  have hms'' : ∀ m' ∈ ms', ∃ p ∈ Subgroup.closure {p | p ∈ ps'}, MonoidHom.snd _ _ p = m' := by
    rw [hms', hps']; exact hms
  have hpM : preM k (m + q) ps' ms' ≤ 5 * (M + 1) ^ 2 := by
    unfold preM; rw [hpsl, hmsl]; omega
  have hc := rcR_pre_cost hpre ps' ms' hms'' hpM hW
  have hpre' : CpFB P I.pre (.list [.list [.nat k, .nat (m + q)], .list (ps'.map pairV),
      .list (ms'.map encPerm)]) W ((preimagePrim hpre).boundSize W + 10 ^ 14 * (W + 1) ^ 8)
      (fun w => ∃ qs : List (Perm (Fin k) × Perm (Fin (m + q))), w = .list (qs.map pairV) ∧
        qs.length ≤ (k + (m + q)) ^ 2 ∧
        Subgroup.closure {p | p ∈ qs} =
          Subgroup.closure {p | p ∈ ps'} ⊓ (gens ms').comap (MonoidHom.snd _ _)) := by
    refine FunAll.mono (graphPre_spec hpre ok.pre hj ps' ms' hms'') ?_
    rintro w c ⟨qs, rfl, hl, hcl, hc'⟩
    refine ⟨⟨qs, rfl, hl, hcl⟩, ?_, by omega⟩
    have h1 := rcR_wt_qs (M := 2 * M + 1) (by omega) (by omega) qs hl
    have h2 := rcR_pow_mono (show 2 * M + 1 + 1 ≤ 2 * (M + 1) by omega) 6
    have h3 : (2 * (M + 1)) ^ 6 = 64 * (M + 1) ^ 6 := by ring
    omega
  have hcall := rcR_callC (C := (preimagePrim hpre).boundSize W + (10 ^ 14 + 1) * (W + 1) ^ 8)
    (rcR_detC dI (C := 100 * W + 100) (by omega)
      (Q := (· = .list [.list [.nat k, .nat (m + q)], .list (ps'.map pairV),
        .list (ms'.map encPerm)])) rfl) (fun v hv _ => by subst hv; exact hpre') (by omega)
  refine (rcR_mk2B (C := F) hcall (rcR_detC (rcRDW.var (P := P) (W := W)
      (env := .list [Av, Rv] :: r7) (i := 3) (v := natList rowT) rfl (by omega)) le_rfl
      (Q := (· = natList rowT)) rfl) ?_ (by omega)).mono (by omega) ?_
  · rintro va vb ⟨qs, rfl, hl, -⟩ rfl - -
    have h1 := rcR_wt_qs (M := 2 * M + 1) (by omega) (by omega) qs hl
    have h2 := rcR_pow_mono (show 2 * M + 1 + 1 ≤ 2 * (M + 1) by omega) 6
    have h3 : (2 * (M + 1)) ^ 6 = 64 * (M + 1) ^ 6 := by ring
    have := wt_list2_le (.list (qs.map pairV)) (natList rowT)
    omega
  · rintro v ⟨va, vb, ⟨qs, rfl, hl, hcl⟩, rfl, rfl⟩
    refine ⟨qs, by rw [hrowT], hl, ?_⟩
    rw [hcl, hps', hms']

end Car

end GI.Impl
