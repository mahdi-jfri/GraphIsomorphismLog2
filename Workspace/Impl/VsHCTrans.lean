import Workspace.Impl.VsHCData

namespace GI.Impl

open GI.Lang GI.Cited Equiv

/-- On `[us,t]`, list the products `t*u`. -/
def vsHCTransRowE (mp : ℕ) : Expr := .call mp (mk2 (arg 1) (arg 0))

/-- On `[ts,us]`, concatenate the rows of products. -/
def vsHCTransE (mp cat : ℕ) : Expr :=
  .call cat (.call mp (mk2 (arg 1) (arg 0)))

structure VsHCTransX where
  (f mp row mpi comp cat : ℕ)

structure VsHCTransLay (P : Program) (x : VsHCTransX) : Prop where
  hf : P.funs[x.f]? = some (vsHCTransE x.mp x.cat)
  hmp : P.HasAt x.mp (mapFuns x.mp x.row)
  hr : P.funs[x.row]? = some (vsHCTransRowE x.mpi)
  hmpi : P.HasAt x.mpi (mapFuns x.mpi x.comp)
  hc : P.HasAt x.comp (composeFuns x.comp)
  hcat : P.HasAt x.cat (vsWFlatFuns x.cat)

set_option maxHeartbeats 1000000 in
/-- A row of the product transversal. -/
theorem vsHCTransRow_spec {P : Program} {x : VsHCTransX} (L : VsHCTransLay P x)
    {n N : ℕ} (hn : n ≤ N) (us : List (Perm (Fin n))) (hu : us.length ≤ N)
    (t : Perm (Fin n)) :
    FunDet P x.row (.list [.list (us.map encPerm), encPerm t])
      (.list (us.map fun u => encPerm (t * u))) (10 ^ 8 * (N + 1) ^ 5) := by
  set U := Val.list (us.map encPerm)
  set A := Val.list [U, encPerm t]
  have a0 := Det.arg' (P := P) (vs := [U, encPerm t]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [U, encPerm t]) (rest := []) (j := 1) rfl
  have dm := Det.call (Det.mk2 a1 a0) (vsQ_map L.hmpi us encPerm
    (fun u => encPerm (t * u)) encPerm_injective (c := encPerm t)
    (B := permK * (N + 1) ^ 3)
    (fun u _ => (compose_spec L.hc t u).mono (by
      exact Nat.mul_le_mul_left permK (Nat.pow_le_pow_left (by omega) 3))))
  refine FunDet.intro L.hr (dm.mono ?_)
  have wU := vsP_wt_perms hn us (by omega)
  have wR := vsP_wt_perms hn (us.map fun u => t * u) (by simp; omega)
  simp only [List.map_map, Function.comp_def] at wR
  have wt : (encPerm t).wt ≤ 4 * (N + 1) ^ 2 :=
    (wt_encPerm_le t).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have wa := wt_list2_le U (encPerm t)
  have wb := wt_list2_le (encPerm t) U
  have p03 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have p23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have p35 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have p45 : (N + 1) ^ 4 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have warg : (Val.list [encPerm t, U]).wt +
      (Val.list (us.map fun u => encPerm (t * u))).wt + 1 ≤ 100 * (N + 1) ^ 3 := by
    change (Val.list (us.map encPerm)).wt ≤ _ at wU
    change U.wt ≤ _ at wU
    omega
  have hloop : mapK * (us.length + 1) * ((Val.list [encPerm t, U]).wt +
      (Val.list (us.map fun u => encPerm (t * u))).wt + 1) ≤ 10 ^ 5 * (N + 1) ^ 4 := by
    calc _ ≤ 1000 * (N + 1) * (100 * (N + 1) ^ 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) warg
      _ = _ := by ring
  have hsum : us.length * (permK * (N + 1) ^ 3) ≤ 30000 * (N + 1) ^ 4 := by
    calc _ ≤ (N + 1) * (30000 * (N + 1) ^ 3) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  change (Val.list (us.map encPerm)).wt ≤ _ at wU
  change U.wt ≤ _ at wU
  dsimp only [U] at hloop
  have hw : (Val.list (us.map encPerm)).wt = U.wt := rfl
  have hA : (Val.list [U, encPerm t]).wt = A.wt := rfl
  omega

set_option maxHeartbeats 1000000 in
/-- Compute the product of two transversals. -/
theorem vsHCTrans_spec {P : Program} {x : VsHCTransX} (L : VsHCTransLay P x)
    {n N : ℕ} (hn : n ≤ N) (ts us : List (Perm (Fin n)))
    (ht : ts.length ≤ N) (hu : us.length ≤ N) (htu : ts.length * us.length ≤ N) :
    FunDet P x.f (.list [.list (ts.map encPerm), .list (us.map encPerm)])
      (.list ((vsHCTrans ts us).map encPerm)) (10 ^ 12 * (N + 1) ^ 7) := by
  set T := Val.list (ts.map encPerm)
  set U := Val.list (us.map encPerm)
  set xss := ts.map fun t => us.map fun u => encPerm (t * u)
  have a0 := Det.arg' (P := P) (vs := [T, U]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [T, U]) (rest := []) (j := 1) rfl
  have dm := Det.call (Det.mk2 a1 a0) (vsQ_map L.hmp ts encPerm
    (fun t => .list (us.map fun u => encPerm (t * u))) encPerm_injective (c := U)
    (fun t _ => vsHCTransRow_spec L hn us hu t))
  have em : Val.list (ts.map fun t => Val.list (us.map fun u => encPerm (t * u))) =
      Val.list (xss.map Val.list) := by simp [xss]
  rw [em] at dm
  have key : ∀ ts0 : List (Perm (Fin n)),
      (ts0.map fun t => us.map fun u => encPerm (t * u)).flatten =
      (ts0.flatMap fun t => us.map fun u => t * u).map encPerm := by
    intro ts0
    induction ts0 with
    | nil => rfl
    | cons t ts0 ih => simp [List.flatMap_cons, ih, List.map_map, Function.comp_def]
  have eflat : xss.flatten = (vsHCTrans ts us).map encPerm := key ts
  have wflat : (Val.list xss.flatten).wt ≤ 20 * (N + 1) ^ 3 := by
    rw [eflat]
    exact vsP_wt_perms hn _ (by rw [vsHCTrans_length]; omega)
  have wxss : (Val.list (xss.map Val.list)).wt ≤ 100 * (N + 1) ^ 4 := by
    have hh := vs_wt_list_le_of (xss.map Val.list) (c := 20 * (N + 1) ^ 3) (by
      intro v hv
      simp only [xss, List.map_map, List.mem_map, Function.comp_def] at hv
      obtain ⟨t, _, rfl⟩ := hv
      simpa [List.map_map, Function.comp_def] using
        vsP_wt_perms hn (us.map fun u => t * u) (by simp; omega))
    simp only [List.length_map, xss] at hh
    change (Val.list (xss.map Val.list)).wt ≤ ts.length * (2 * (20 * (N + 1) ^ 3) + 1) + 4 at hh
    have hb : ts.length * (2 * (20 * (N + 1) ^ 3) + 1) ≤
        (N + 1) * (41 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by have := Nat.one_le_pow 3 (N + 1) (by omega); omega)
    have he : (N + 1) * (41 * (N + 1) ^ 3) = 41 * (N + 1) ^ 4 := by ring
    have hp : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    rw [he] at hb
    omega
  have p34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have dc := Det.call dm (vsWConcat_spec L.hcat xss (N := N) (by simp [xss]; omega)
    (fun xs hxs => by obtain ⟨t, _, rfl⟩ := List.mem_map.1 hxs; simp; omega)
    (by omega) (by omega))
  rw [eflat] at dc
  refine FunDet.intro L.hf (dc.mono ?_)
  have wT := vsP_wt_perms hn ts (by omega)
  have wU := vsP_wt_perms hn us (by omega)
  have wa := wt_list2_le T U
  have wb := wt_list2_le U T
  have p04 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have p47 : (N + 1) ^ 4 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have p67 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have warg : (Val.list [U, T]).wt + (Val.list (xss.map Val.list)).wt + 1 ≤
      200 * (N + 1) ^ 4 := by
    change T.wt ≤ _ at wT
    change U.wt ≤ _ at wU
    omega
  have hloop : mapK * (ts.length + 1) * ((Val.list [U, T]).wt +
      (Val.list (xss.map Val.list)).wt + 1) ≤ 200000 * (N + 1) ^ 5 := by
    calc _ ≤ 1000 * (N + 1) * (200 * (N + 1) ^ 4) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) warg
      _ = _ := by ring
  have hsum : ts.length * (10 ^ 8 * (N + 1) ^ 5) ≤ 10 ^ 8 * (N + 1) ^ 6 := by
    calc _ ≤ (N + 1) * (10 ^ 8 * (N + 1) ^ 5) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have p57 : (N + 1) ^ 5 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  change T.wt ≤ _ at wT
  change U.wt ≤ _ at wU
  dsimp only [T] at hloop
  rw [eflat] at wflat
  omega

end GI.Impl
