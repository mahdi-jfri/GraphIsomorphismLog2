module

public import Workspace.Impl.GMPLuksRepr

@[expose] public section

/-!
# Stage 1 of Luks's two-stage normal-subgroup centralizer

Given `[hv, nv]` with `GroupVal n hv H`, `GroupVal n nv N`, and `Normalizes H N`:
1. `gmpStabListFuns` computes `ws` with `GMPStabList N ws`, the list of encoded point stabilizers
   `pointwiseStab N [i]` (`i : Fin n`).
2. `gmpStabReprFuns` (`Workspace/Impl/GMPLuksRepr.lean`) computes representative labels `rv` for
   the equality relation `gmpStabRel N` on those point stabilizers.
3. `kerFuns` computes the kernel `K₁` of the action of `H` on the equality classes of `gmpStabRel N`.

By `gmpFirstStageKer_normalizes_stab` (`Workspace/Proved/GMPNormalCentralizer.lean`), every subgroup
`A ≤ K₁` normalizes `pointwiseStab N [i]` for every `i : Fin n`, and `C_H(N) ≤ K₁`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

/-! ### Computing a single point stabilizer `pointwiseStab N [i]` -/

/-- On `[nv, .nat i]`: call `pstabFuns` at `ps` on `[nv, [i]]`. -/
def gmpStabOneF (ps : ℕ) : Expr := .call ps (mk2 (arg 0) (mk1 (arg 1)))

/-- Cost bound for `gmpStabOneF` on `[nv, .nat i]` (`i < n`). -/
noncomputable def gmpStabOneCost (hps : PointwiseStab) (T : ℕ) : ℕ :=
  (pointwiseStabPrim hps).boundSize (T + 10) + 10 ^ 16 * (T + 3) ^ 9

theorem gmpStabOne_spec (hps : PointwiseStab) {P : Program} {b jp : ℕ}
    (h1 : P.funs[b]? = some (gmpStabOneF (b + 1)))
    (hps_at : P.HasAt (b + 1) (pstabFuns (b + 1) jp))
    (hjps : P.prims[jp]? = some (pointwiseStabPrim hps))
    {nv : Val} {N : Subgroup (Perm (Fin n))} (hN : GroupVal n nv N) (i : Fin n) :
    FunAll P b (.list [nv, .nat (i : ℕ)]) (fun w c =>
      GroupVal n w (pointwiseStab N [i]) ∧
      w.wt ≤ 320 * (n + 1) ^ 6 ∧
      c ≤ gmpStabOneCost hps nv.wt) := by
  obtain ⟨ns, rfl, rfl⟩ := hN
  have d0 := Det.arg' (P := P) (vs := [encGroup ns, .nat (i : ℕ)]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [encGroup ns, .nat (i : ℕ)]) (rest := []) (j := 1) rfl
  have din := Det.mk2 d0 (Det.mk1 d1)
  have hpts : Val.list [Val.nat (i : ℕ)] = encPts [i] := by rw [encPts_eq]; rfl
  rw [hpts] at din
  obtain ⟨ca, da, hca⟩ : ∃ ca, Det P [Val.list [encGroup ns, .nat (i : ℕ)]]
      (mk2 (arg 0) (mk1 (arg 1))) (.list [encGroup ns, encPts [i]]) ca ∧
      ca ≤ 20 * (encGroup ns).wt + 30 * (Val.nat (i : ℕ)).wt + 100 := by
    refine ⟨_, din, ?_⟩
    have := wt_list2_le (encGroup ns) (.nat (i : ℕ))
    have := wt_list1_le (Val.nat (i : ℕ))
    have := wt_list2_le (encGroup ns) (.list [Val.nat (i : ℕ)])
    rw [← hpts]
    omega
  have hpstab := pstab_spec hps hps_at hjps ⟨ns, rfl, rfl⟩ [i]
  have dcall := EvalAll.call_funAll (f := b + 1) da
    (Q := fun w cost => GroupVal n w (pointwiseStab (gens ns) [i]) ∧
      w.wt ≤ 320 * (n + 1) ^ 6 ∧
      cost ≤ ca + ((pointwiseStabPrim hps).bound (.list [encGroup ns, encPts [i]]) +
        pstabK * (Val.list [encGroup ns, encPts [i]]).wt ^ 9) + w.wt + 1)
    fun v ca' hv => by
      obtain ⟨rfl, hca'⟩ := hv
      exact hpstab.mono fun w cb ⟨hG, hw, hcb⟩ => ⟨hG, hw, by omega⟩
  refine FunAll.intro h1 (dcall.mono ?_)
  rintro w cost ⟨hG, hw, htot⟩
  refine ⟨hG, hw, ?_⟩
  have hS := S_le_wt_encGroup ns
  obtain ⟨-, hnS⟩ := le_S ns.length n
  have hn_wt : n + 1 ≤ (encGroup ns).wt := le_trans hnS hS
  have hi_lt : (i : ℕ) < n := i.isLt
  have hwi : (Val.nat (i : ℕ)).wt ≤ (encGroup ns).wt + 2 := by
    have := wt_nat_le (i : ℕ)
    omega
  have hw_pts : (encPts [i]).wt ≤ 2 * (encGroup ns).wt + 9 := by
    rw [← hpts]
    have := wt_list1_le (Val.nat (i : ℕ))
    omega
  have hw_arg : (Val.list [encGroup ns, encPts [i]]).wt ≤ 10 * ((encGroup ns).wt + 3) := by
    have := wt_list2_le (encGroup ns) (encPts [i])
    omega
  have hsz : (Val.list [encGroup ns, encPts [i]]).size ≤ (encGroup ns).wt + 10 := by
    rw [size_list2, ← hpts]
    have e : (Val.list [Val.nat (i : ℕ)]).size = 5 := by
      simp only [size_list, length_cellsList, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, size_nat]
      omega
    have := (encGroup ns).size_le_wt
    omega
  have hbd := (pointwiseStabPrim hps).bound_le hsz
  have hp9 : pstabK * (Val.list [encGroup ns, encPts [i]]).wt ^ 9 ≤
      10 ^ 15 * ((encGroup ns).wt + 3) ^ 9 := by
    calc pstabK * (Val.list [encGroup ns, encPts [i]]).wt ^ 9
        ≤ 1000000 * (10 * ((encGroup ns).wt + 3)) ^ 9 :=
          Nat.mul_le_mul (by simp [pstabK]) (Nat.pow_le_pow_left hw_arg 9)
      _ = 10 ^ 15 * ((encGroup ns).wt + 3) ^ 9 := by ring
  have hw6_9 : (n + 1) ^ 6 ≤ ((encGroup ns).wt + 3) ^ 9 :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ (encGroup ns).wt + 3) 6).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have h1_9 : (encGroup ns).wt + 3 ≤ ((encGroup ns).wt + 3) ^ 9 :=
    Nat.le_self_pow (by omega) _
  unfold gmpStabOneCost
  generalize (pointwiseStabPrim hps).boundSize ((encGroup ns).wt + 10) = BS at hbd ⊢
  generalize (pointwiseStabPrim hps).bound (.list [encGroup ns, encPts [i]]) = B0 at hbd htot ⊢
  generalize pstabK * (Val.list [encGroup ns, encPts [i]]).wt ^ 9 = P9 at hp9 htot ⊢
  generalize ((encGroup ns).wt + 3) ^ 9 = Q9 at hp9 hw6_9 h1_9 ⊢
  generalize (n + 1) ^ 6 = Q6 at hw hw6_9 ⊢
  omega

/-! ### Tabulating all `n` point stabilizers -/

/-- On `nv`: extract `encPerm 1 = [0, ..., n - 1]` and map `gmpStabOneF` over `[nv, [0, ..., n - 1]]`. -/
def gmpStabListEntry (mp : ℕ) : Expr :=
  .call mp (mk2 (.var 0) (.get (.get (.var 0) (.nat 1)) (.nat 0)))

/-- Computing `.list ws` with `GMPStabList N ws`, at base `b` (13 functions). -/
def gmpStabListFuns (b jp : ℕ) : List Expr :=
  [gmpStabListEntry (b + 1)] ++ mapFuns (b + 1) (b + 4) ++ [gmpStabOneF (b + 5)] ++
    pstabFuns (b + 5) jp

@[simp] theorem length_gmpStabListFuns (b jp : ℕ) : (gmpStabListFuns b jp).length = 13 := rfl

theorem gmpStabList_of_forall₂ {N : Subgroup (Perm (Fin n))} {out : List Val}
    (hrel : List.Forall₂
      (fun x w => ∀ i : Fin n, x = .nat (i : ℕ) →
        GroupVal n w (pointwiseStab N [i]) ∧ w.wt ≤ 320 * (n + 1) ^ 6)
      ((List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)) out) :
    GMPStabList N out := by
  have hlen : out.length = n := by
    have := hrel.length_eq
    simpa using this.symm
  refine ⟨fun i => out[i.val]'(by omega), ?_, ?_⟩
  · apply List.ext_getElem
    · simp [hlen]
    · intro k hk1 hk2
      simp
  · intro i
    have hget := (List.forall₂_iff_get.mp hrel).2 i.val (by simp [i.isLt]) (by omega)
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_finRange, Fin.cast_mk,
      Fin.eta] at hget
    exact hget i rfl

/-- Cost bound for `gmpStabListFuns` on `nv`. -/
noncomputable def gmpStabListCost (hps : PointwiseStab) (T n : ℕ) : ℕ :=
  (n + 1) * gmpStabOneCost hps T + 10 ^ 10 * (T + (n + 1) ^ 8)

theorem gmpStabList_spec (hps : PointwiseStab) {P : Program} {b jp : ℕ}
    (hb : P.HasAt b (gmpStabListFuns b jp))
    (hjps : P.prims[jp]? = some (pointwiseStabPrim hps))
    {nv : Val} {N : Subgroup (Perm (Fin n))} (hN : GroupVal n nv N) :
    FunAll P b nv (fun w cost =>
      ∃ ws, w = .list ws ∧ GMPStabList N ws ∧ cost ≤ gmpStabListCost hps nv.wt n) := by
  simp only [gmpStabListFuns] at hb
  have hentry : P.funs[b]? = some (gmpStabListEntry (b + 1)) := hb.left.left.left.single
  have hmp : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := by simpa using hb.left.left.right
  have hone : P.funs[b + 4]? = some (gmpStabOneF (b + 5)) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using hb.left.right.single
  have hps_at : P.HasAt (b + 5) (pstabFuns (b + 5) jp) := by
    simpa [mapFuns, loopFuns, Nat.add_assoc] using hb.right
  have hN' := hN
  obtain ⟨ns, rfl, rfl⟩ := hN
  let xs : List Val := (List.finRange n).map fun i : Fin n => Val.nat (i : ℕ)
  have d0 := Det.var' (P := P) (env := [encGroup ns]) (i := 0) rfl
  have d1 := Det.get' d0 (Det.nat 1)
    (show [Val.nat n, Val.list ((1 :: ns).map encPerm)][1]? =
      some (.list ((1 :: ns).map encPerm)) from rfl)
  have d2 := Det.get' d1 (Det.nat 0)
    (show ((1 :: ns).map encPerm)[0]? = some (.list xs) from rfl)
  obtain ⟨ca, da, hca⟩ : ∃ ca, Det P [encGroup ns]
      (mk2 (.var 0) (.get (.get (.var 0) (.nat 1)) (.nat 0)))
      (.list [encGroup ns, .list xs]) ca ∧
      ca ≤ 20 * (encGroup ns).wt + 100 := by
    refine ⟨_, Det.mk2 d0 d2, ?_⟩
    have hw_1 : (Val.list ((1 :: ns).map encPerm)).wt < (encGroup ns).wt :=
      wt_le_wt_list (vs := [.nat n, .list ((1 :: ns).map encPerm)]) (by simp)
    have hw_xs_lt : (Val.list xs).wt < (Val.list ((1 :: ns).map encPerm)).wt :=
      wt_le_wt_list (vs := (1 :: ns).map encPerm) (by simp [xs, encPerm])
    have := wt_list2_le (encGroup ns) (.list xs)
    omega
  let R : Val → Val → Prop := fun x w =>
    ∀ i : Fin n, x = .nat (i : ℕ) → GroupVal n w (pointwiseStab (gens ns) [i]) ∧
      w.wt ≤ 320 * (n + 1) ^ 6
  have hmap_call := map_spec (c := encGroup ns) (xs := xs) hmp (R := R)
    (B := fun _ => gmpStabOneCost hps (encGroup ns).wt) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      refine (gmpStabOne_spec hps hone hps_at hjps hN' i).mono fun w c ⟨hG, hw, hc⟩ =>
        ⟨fun j hj => ?_, hc⟩
      have hij : i = j := Fin.ext (by simpa using hj)
      subst hij
      exact ⟨hG, hw⟩)
  have dcall := EvalAll.call_funAll (f := b + 1) da
    (Q := fun w cost => ∃ out, w = .list out ∧ List.Forall₂ R xs out ∧
      cost ≤ ca + ((xs.map fun _ => gmpStabOneCost hps (encGroup ns).wt).sum +
        mapK * (xs.length + 1) * ((Val.list [encGroup ns, .list xs]).wt + w.wt + 1)) + w.wt + 1)
    fun v ca' hv => by
      obtain ⟨rfl, hca'⟩ := hv
      exact hmap_call.mono fun w cb ⟨out, hw_eq, hrel, hcb⟩ =>
        ⟨out, hw_eq, hrel, by omega⟩
  refine FunAll.intro hentry (dcall.mono ?_)
  rintro w cost ⟨ws, rfl, hrel, htot⟩
  have hws : GMPStabList (gens ns) ws := gmpStabList_of_forall₂ hrel
  refine ⟨ws, rfl, hws, ?_⟩
  have hxs_len : xs.length = n := by simp [xs]
  have hsum : (xs.map fun _ => gmpStabOneCost hps (encGroup ns).wt).sum =
      n * gmpStabOneCost hps (encGroup ns).wt := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, hxs_len]
  rw [hsum] at htot
  have hn_mul : n * gmpStabOneCost hps (encGroup ns).wt ≤
      (n + 1) * gmpStabOneCost hps (encGroup ns).wt :=
    Nat.mul_le_mul_right _ (by omega)
  have hw_ws := hws.wt_le
  have hw_xs : (Val.list xs).wt ≤ 4 * (n + 1) ^ 2 := wt_encPerm_le (1 : Perm (Fin n))
  have hw_pair := wt_list2_le (encGroup ns) (.list xs)
  have h2_7 : (n + 1) ^ 2 ≤ (n + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1_7 : 1 ≤ (n + 1) ^ 7 := Nat.one_le_pow _ _ (by omega)
  have h7_8 : (n + 1) ^ 7 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1_8 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hS := S_le_wt_encGroup ns
  obtain ⟨-, hnS⟩ := le_S ns.length n
  have hn_wt : n + 1 ≤ (encGroup ns).wt := le_trans hnS hS
  have hmap_overhead : mapK * (xs.length + 1) *
      ((Val.list [encGroup ns, .list xs]).wt + (Val.list ws).wt + 1) ≤
      10 ^ 7 * (encGroup ns).wt ^ 2 + 10 ^ 7 * (n + 1) ^ 8 := by
    have hmid : (Val.list [encGroup ns, .list xs]).wt + (Val.list ws).wt + 1 ≤
        2 * (encGroup ns).wt + 700 * (n + 1) ^ 7 := by omega
    calc mapK * (xs.length + 1) * ((Val.list [encGroup ns, .list xs]).wt + (Val.list ws).wt + 1)
        ≤ 1000 * (n + 1) * (2 * (encGroup ns).wt + 700 * (n + 1) ^ 7) :=
          Nat.mul_le_mul (by simp [mapK, hxs_len]) hmid
      _ = 2000 * ((n + 1) * (encGroup ns).wt) + 700000 * (n + 1) ^ 8 := by ring
      _ ≤ 2000 * ((encGroup ns).wt * (encGroup ns).wt) + 700000 * (n + 1) ^ 8 := by
          gcongr
      _ ≤ 10 ^ 7 * (encGroup ns).wt ^ 2 + 10 ^ 7 * (n + 1) ^ 8 := by ring_nf; omega
  -- Note `gmpStabOneCost hps (encGroup ns).wt ≥ 10 ^ 16 * ((encGroup ns).wt + 3) ^ 9 ≥ 10 ^ 7 * (encGroup ns).wt ^ 2`
  have hT2_le : 10 ^ 7 * (encGroup ns).wt ^ 2 ≤ gmpStabOneCost hps (encGroup ns).wt := by
    unfold gmpStabOneCost
    have hp : (encGroup ns).wt ^ 2 ≤ ((encGroup ns).wt + 3) ^ 9 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have h1_mul : gmpStabOneCost hps (encGroup ns).wt + n * gmpStabOneCost hps (encGroup ns).wt =
      (n + 1) * gmpStabOneCost hps (encGroup ns).wt := by ring
  unfold gmpStabListCost
  generalize gmpStabOneCost hps (encGroup ns).wt = OC at hn_mul hT2_le h1_mul htot ⊢
  generalize mapK * (xs.length + 1) *
    ((Val.list [encGroup ns, .list xs]).wt + (Val.list ws).wt + 1) = MO at hmap_overhead htot
  generalize 10 ^ 7 * (encGroup ns).wt ^ 2 = T2 at hmap_overhead hT2_le
  generalize (n + 1) ^ 8 = Q8 at hmap_overhead h7_8 h1_8 ⊢
  generalize (n + 1) ^ 7 = Q7 at hw_ws h2_7 h1_7 h7_8 ⊢
  generalize (n + 1) ^ 2 = Q2 at hw_xs h2_7 ⊢
  omega

/-! ### Stage 1: kernel of the action on point-stabilizer equality classes -/

/-- On `[hv, nv]`: compute `ws` (`gmpStabListFuns`), `rv` (`gmpStabReprFuns`), and
`[ker(H, rv), ws]` (`kerFuns`). -/
def gmpStage1Entry (sl sr kr : ℕ) : Expr :=
  .letE (.call sl (arg 1))
    (.letE (.call sr (.var 1))
      (.letE (.call kr (mk2 (arg 0) (.var 2)))
        (mk2 (.var 3) (.var 1))))

/-- Stage 1 of Luks's normal centralizer, at base `b` (49 functions), with membership at `jm`,
pointwise stabilizer at `jp`, and preimage at `jpre`. -/
def gmpStage1Funs (b jm jp jpre : ℕ) : List Expr :=
  [gmpStage1Entry (b + 1) (b + 14) (b + 28)] ++
    gmpStabListFuns (b + 1) jp ++
    gmpStabReprFuns (b + 14) jm ++
    kerFuns (b + 28) jpre

@[simp] theorem length_gmpStage1Funs (b jm jp jpre : ℕ) :
    (gmpStage1Funs b jm jp jpre).length = 49 := rfl

/-- Cost bound for `gmpStage1Funs` on `[hv, nv]` of total weight `T`. -/
noncomputable def gmpStage1Cost (hm : Membership) (hps : PointwiseStab) (hpre : Preimage)
    (T n : ℕ) : ℕ :=
  gmpStabListCost hps T n + gmpStabReprCost hm n +
    (preimagePrim hpre).boundSize (10 * T + 50 * (n + 1) ^ 2) +
    10 ^ 20 * (T + n + 1) ^ 18

theorem gmpStage1_spec (hm : Membership) (hps : PointwiseStab) (hpre : Preimage)
    {P : Program} {b jm jp jpre : ℕ}
    (hb : P.HasAt b (gmpStage1Funs b jm jp jpre))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjps : P.prims[jp]? = some (pointwiseStabPrim hps))
    (hjpre : P.prims[jpre]? = some (preimagePrim hpre))
    {hv nv : Val} {H N : Subgroup (Perm (Fin n))}
    (hH : GroupVal n hv H) (hN : GroupVal n nv N) (hHN : Normalizes H N) :
    FunAll P b (.list [hv, nv]) (fun w cost =>
      ∃ kv₁ ws K₁, w = .list [kv₁, .list ws] ∧
        GroupVal n kv₁ K₁ ∧ kv₁.wt ≤ 320 * (n + 1) ^ 6 ∧
        (∀ h, h ∈ K₁ ↔ h ∈ H ∧ ∀ i : Fin n, pointwiseStab N [h i] = pointwiseStab N [i]) ∧
        GMPStabList N ws ∧
        cost ≤ gmpStage1Cost hm hps hpre (Val.list [hv, nv]).wt n) := by
  simp only [gmpStage1Funs] at hb
  have hentry : P.funs[b]? = some (gmpStage1Entry (b + 1) (b + 14) (b + 28)) :=
    hb.left.left.left.single
  have hsl : P.HasAt (b + 1) (gmpStabListFuns (b + 1) jp) := by simpa using hb.left.left.right
  have hsr : P.HasAt (b + 14) (gmpStabReprFuns (b + 14) jm) := by
    simpa [Nat.add_assoc] using hb.left.right
  have hkr : P.HasAt (b + 28) (kerFuns (b + 28) jpre) := by
    simpa [Nat.add_assoc] using hb.right
  set T := (Val.list [hv, nv]).wt with hT_def
  have hhv_lt : hv.wt < T := wt_le_wt_list (by simp)
  have hnv_lt : nv.wt < T := wt_le_wt_list (by simp)
  -- Step 1: call `gmpStabListFuns` on `nv`
  have d_nv := Det.arg' (P := P) (vs := [hv, nv]) (rest := []) (j := 1) rfl
  have c_sl := EvalAll.call_funAll (f := b + 1) d_nv
    (Q := fun w1 c1 => ∃ ws, w1 = .list ws ∧ GMPStabList N ws ∧
      c1 ≤ (2 * T + 6) + gmpStabListCost hps nv.wt n + w1.wt + 1)
    fun v ca hv' => by
      obtain ⟨rfl, hca⟩ := hv'
      exact (gmpStabList_spec hps hsl hjps hN).mono fun w1 cb ⟨ws, hw1, hws, hcb⟩ =>
        ⟨ws, hw1, hws, by omega⟩
  refine FunAll.intro hentry (EvalAll.letE c_sl fun w1 c1 hw1 => ?_)
  obtain ⟨ws, rfl, hws, hc1⟩ := hw1
  -- Step 2: call `gmpStabReprFuns` on `.list ws`
  have d_ws := Det.var' (P := P) (env := [Val.list [hv, nv], .list ws]) (i := 1) rfl
  have c_sr := EvalAll.call_funAll (f := b + 14) d_ws
    (Q := fun rv c2 => ReprVal n rv (gmpStabRel N) ∧
      c2 ≤ ((Val.list ws).wt + 1) + gmpStabReprCost hm n + rv.wt + 1)
    fun v ca hv' => by
      obtain ⟨rfl, hca⟩ := hv'
      exact (gmpStabRepr_spec hm hsr hjm hws).mono fun rv cb ⟨hrv, hcb⟩ =>
        ⟨hrv, by omega⟩
  refine EvalAll.letE c_sr fun rv c2 hrv_c2 => ?_
  obtain ⟨hrv, hc2⟩ := hrv_c2
  -- Step 3: call `kerFuns` on `[hv, rv]` and pair with `.list ws`
  have d_hv := Det.arg' (P := P) (vs := [hv, nv]) (rest := [.list ws, rv]) (j := 0) rfl
  have d_rv := Det.var' (P := P) (env := [Val.list [hv, nv], .list ws, rv]) (i := 2) rfl
  have d_kr_arg := Det.mk2 d_hv d_rv
  have hker := ker_spec hpre hkr hjpre hH hrv (gmpStabRel_pres hHN)
  have c_kr := EvalAll.call_funAll (f := b + 28) d_kr_arg
    (Q := fun kv₁ c3 => (∃ K₁, GroupVal n kv₁ K₁ ∧ ∀ g, g ∈ K₁ ↔ g ∈ H ∧ ∀ i, gmpStabRel N (g i) i) ∧
      kv₁.wt ≤ 320 * (n + 1) ^ 6 ∧
      c3 ≤ (2 * T + rv.wt + 2 * (Val.list [hv, rv]).wt + 13) +
        ((preimagePrim hpre).boundSize (3 * (Val.list [hv, rv]).wt) +
          kerK * (Val.list [hv, rv]).wt ^ 9) + kv₁.wt + 1)
    fun v ca hv' => by
      obtain ⟨rfl, hca⟩ := hv'
      exact hker.mono fun kv₁ cb ⟨hK₁, hkw, hcb⟩ => ⟨hK₁, hkw, by omega⟩
  refine EvalAll.letE c_kr fun kv₁ c3 hkv₁ => ?_
  obtain ⟨⟨K₁, hK₁, hK₁_mem⟩, hkw, hc3⟩ := hkv₁
  have d_kv := Det.var' (P := P) (env := [Val.list [hv, nv], .list ws, rv, kv₁]) (i := 3) rfl
  have d_ws2 := Det.var' (P := P) (env := [Val.list [hv, nv], .list ws, rv, kv₁]) (i := 1) rfl
  have d_out := Det.mk2 d_kv d_ws2
  refine d_out.post fun c4 hc4 => ⟨kv₁, ws, K₁, rfl, hK₁, hkw, hK₁_mem, hws, ?_⟩
  -- Cost bound arithmetic
  obtain ⟨r, rfl, -, -⟩ := hrv.elim
  have hw_rv : (encFun fun i => (r i : ℕ)).wt ≤ 4 * (n + 1) ^ 2 := wt_encRepr_le r
  have hw_ws := hws.wt_le
  have hw_kr_in : (Val.list [hv, encFun fun i => (r i : ℕ)]).wt ≤ 2 * T + 8 * (n + 1) ^ 2 + 6 := by
    have := wt_list2_le hv (encFun fun i => (r i : ℕ))
    omega
  have h3_kr : 3 * (Val.list [hv, encFun fun i => (r i : ℕ)]).wt ≤
      10 * T + 50 * (n + 1) ^ 2 := by
    have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hpre_mono : (preimagePrim hpre).boundSize (3 * (Val.list [hv, encFun fun i => (r i : ℕ)]).wt) ≤
      (preimagePrim hpre).boundSize (10 * T + 50 * (n + 1) ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hsl_mono : gmpStabListCost hps nv.wt n ≤ gmpStabListCost hps T n := by
    unfold gmpStabListCost gmpStabOneCost
    have h1 : (pointwiseStabPrim hps).boundSize (nv.wt + 10) ≤
        (pointwiseStabPrim hps).boundSize (T + 10) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    have h2 : (nv.wt + 3) ^ 9 ≤ (T + 3) ^ 9 := Nat.pow_le_pow_left (by omega) 9
    have h3 : (n + 1) * ((pointwiseStabPrim hps).boundSize (nv.wt + 10) + 10 ^ 16 * (nv.wt + 3) ^ 9) ≤
        (n + 1) * ((pointwiseStabPrim hps).boundSize (T + 10) + 10 ^ 16 * (T + 3) ^ 9) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hkr_in_le : (Val.list [hv, encFun fun i => (r i : ℕ)]).wt ≤ 16 * (T + n + 1) ^ 2 := by
    have h1 : T ≤ (T + n + 1) ^ 2 :=
      (by omega : T ≤ T + n + 1).trans (Nat.le_self_pow (by omega) _)
    have h2 : (n + 1) ^ 2 ≤ (T + n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h3 : 1 ≤ (T + n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hker_pow : kerK * (Val.list [hv, encFun fun i => (r i : ℕ)]).wt ^ 9 ≤
      10 ^ 19 * (T + n + 1) ^ 18 := by
    calc kerK * (Val.list [hv, encFun fun i => (r i : ℕ)]).wt ^ 9
        ≤ 10000000 * (16 * (T + n + 1) ^ 2) ^ 9 :=
          Nat.mul_le_mul (by simp [kerK]) (Nat.pow_le_pow_left hkr_in_le 9)
      _ = 10000000 * 16 ^ 9 * (T + n + 1) ^ 18 := by ring
      _ ≤ 10 ^ 19 * (T + n + 1) ^ 18 := Nat.mul_le_mul_right _ (by decide)
  have hw_out := wt_list2_le kv₁ (.list ws)
  have h1_18 : 1 ≤ (T + n + 1) ^ 18 := Nat.one_le_pow _ _ (by omega)
  have hT_18 : T ≤ (T + n + 1) ^ 18 :=
    (by omega : T ≤ T + n + 1).trans (Nat.le_self_pow (by omega) _)
  have h2_18 : (n + 1) ^ 2 ≤ (T + n + 1) ^ 18 :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ T + n + 1) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have h6_18 : (n + 1) ^ 6 ≤ (T + n + 1) ^ 18 :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ T + n + 1) 6).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have h7_18 : (n + 1) ^ 7 ≤ (T + n + 1) ^ 18 :=
    (Nat.pow_le_pow_left (by omega : n + 1 ≤ T + n + 1) 7).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  unfold gmpStage1Cost
  generalize gmpStabListCost hps T n = SLC at hsl_mono ⊢
  generalize gmpStabListCost hps nv.wt n = SLC0 at hsl_mono hc1
  generalize gmpStabReprCost hm n = SRC at hc2 ⊢
  generalize (preimagePrim hpre).boundSize (10 * T + 50 * (n + 1) ^ 2) = PBS at hpre_mono ⊢
  generalize (preimagePrim hpre).boundSize (3 * (Val.list [hv, encFun fun i => (r i : ℕ)]).wt) = PBS0 at hpre_mono hc3
  generalize kerK * (Val.list [hv, encFun fun i => (r i : ℕ)]).wt ^ 9 = KP at hker_pow hc3
  generalize (T + n + 1) ^ 18 = Q18 at hker_pow h1_18 hT_18 h2_18 h6_18 h7_18 ⊢
  generalize (n + 1) ^ 7 = Q7 at hw_ws h7_18
  generalize (n + 1) ^ 6 = Q6 at hkw h6_18
  generalize (n + 1) ^ 2 = Q2 at hw_rv hw_kr_in h2_18
  omega

end GI.Impl
