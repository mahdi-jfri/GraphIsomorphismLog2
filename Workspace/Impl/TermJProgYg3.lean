import Workspace.Impl.TermJProgYg2

/-!
# The generators of `Aut_{N ≀ Sym(q)}(X)` (program, part 3)

The locals of one row (`tmJRowLocF`), and all rows tabulated (`tmJ_rows_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

/-- The weight of a list of pairs on `Fin (m q)`. -/
theorem wt_tmJPermsVal_le {m q : ℕ} (l : List (Perm (Fin m × Fin q))) :
    (tmJPermsVal l).wt ≤ l.length * (8 * (m * q + 1) ^ 2 + 1) + 4 := by
  have := tmJ_wt_list_le (vs := l.map fun σ =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ))
    (E := 4 * (m * q + 1) ^ 2) (by
      intro v hv
      obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hv
      exact wt_encPerm_le _)
  simp only [List.length_map] at this
  unfold tmJPermsVal
  have e : 2 * (4 * (m * q + 1) ^ 2) + 1 = 8 * (m * q + 1) ^ 2 + 1 := by ring
  rw [e] at this
  exact this

/-- The stored list of a row is lighter than the table. -/
theorem tmJYg_row_wt {m : ℕ} {us : List Val} {k : ℕ} {r : Perm (Fin m)}
    {gs : List (Perm (Fin m))} (hu : us[k]? = some (.list [encPerm r, encGroup gs])) :
    (Val.list ((1 :: gs).map encPerm)).wt < (Val.list us).wt := by
  have h1 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (vs := [.nat m, .list ((1 :: gs).map encPerm)]) (by simp)
  have h2 : (encGroup gs).wt < (Val.list [encPerm r, encGroup gs]).wt := wt_le_wt_list (by simp)
  have h3 : (Val.list [encPerm r, encGroup gs]).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? hu)
  omega

/-- A row has fewer locals than the weight of the table. -/
theorem tmJYgLoc_length_lt {m q : ℕ} (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (a : Fin q) {r : Perm (Fin m)} {gs : List (Perm (Fin m))} (hO : O a a = some (r, gs))
    {us : List Val} {k : ℕ} (hu : us[k]? = some (.list [encPerm r, encGroup gs])) :
    (tmJYgLoc O a).length < (Val.list us).wt := by
  have h1 := tmJYg_row_wt hu
  have h2 := length_lt_wt_list ((1 :: gs).map encPerm)
  have e : (tmJYgLoc O a).length = ((1 :: gs).map encPerm).length := by
    unfold tmJYgLoc; rw [hO]; simp
  omega

/-! ### The locals of one row -/

/-- On `[[us, lc], a]`: read the stored list `L = us[a (2q) + a][1][1]` (the encoded `1 :: gs`)
and map `tmJLocAF` over it. -/
def tmJRowLocF (mp : ℕ) : Expr :=
  .call mp (mk2 (mk2 (.get (arg 0) (.nat 1)) (arg 1))
    (.get (.get (.get (.get (arg 0) (.nat 0)) (.arith .add (.arith .mul (arg 1)
      (.arith .mul (.nat 2) (.get (.get (arg 0) (.nat 1)) (.nat 2)))) (arg 1))) (.nat 1)) (.nat 1)))

/-- The cost of one row, in `V = wt us + (m + 1) (q + 1)`. -/
def tmJYgRowK (V : ℕ) : ℕ := 10 ^ 15 * V ^ 9

theorem tmJ_rowLoc_spec {P : Program} {f mp locA dsA rg tbA tbe pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJRowLocF mp)) (hmp : P.HasAt mp (mapFuns mp locA))
    (hlocA : P.funs[locA]? = some (tmJLocAF dsA pr))
    (hds : P.funs[dsA]? = some (tmJDsAF rg tbA)) (hrg : P.HasAt rg (rangeFuns rg))
    (htb : P.HasAt tbA (mapFuns tbA tbe)) (htbe : P.funs[tbe]? = some tmJDsAEF)
    (hpr : TmJPairAt P pr prg prt prte) {m q : ℕ}
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (a : Fin q)
    {r : Perm (Fin m)} {gs : List (Perm (Fin m))} (hO : O a a = some (r, gs)) (us : List Val)
    (hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs])) :
    FunDet P f (.list [.list [.list us, tmJLocCtx m q], .nat a]) (tmJPermsVal (tmJYgLoc O a))
      (tmJYgRowK ((Val.list us).wt + (m + 1) * (q + 1))) := by
  refine FunDet.intro hf ?_
  unfold tmJRowLocF
  have d0 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q], .nat a]) (rest := [])
    (j := 0) (v := .list [.list us, tmJLocCtx m q]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q], .nat a]) (rest := [])
    (j := 1) (v := .nat a) rfl
  have dus := Det.get' d0 (Det.nat 0) (vs := [.list us, tmJLocCtx m q]) (v := .list us) rfl
  have dlc := Det.get' d0 (Det.nat 1) (vs := [.list us, tmJLocCtx m q]) (v := tmJLocCtx m q) rfl
  have dq := Det.get' dlc (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have d2q := Det.arith' (op := .mul) (Det.nat 2) dq (z := 2 * q) rfl
  have dmul := Det.arith' (op := .mul) d1 d2q (z := (a : ℕ) * (2 * q)) rfl
  have didx := Det.arith' (op := .add) dmul d1 (z := (a : ℕ) * (2 * q) + a) rfl
  have de := Det.get' dus didx hu
  have dg := Det.get' de (Det.nat 1) (vs := [encPerm r, encGroup gs]) (v := encGroup gs) rfl
  have dL := Det.get' dg (Det.nat 1) (vs := [.nat m, .list ((1 :: gs).map encPerm)])
    (v := .list ((1 :: gs).map encPerm)) rfl
  have hM := mapList_spec hmp (1 :: gs) encPerm
    (fun s => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc a s⁻¹)))
    (c := .list [tmJLocCtx m q, .nat a]) (fun s _ s' _ he => by rw [encPerm_injective he])
    (fun s _ => tmJ_locA_spec hlocA hds hrg htb htbe hpr a s)
  have dall := Det.call (Det.mk2 (Det.mk2 dlc d1) dL) hM
  have hval : Val.list ((1 :: gs).map fun s =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc a s⁻¹))) =
      tmJPermsVal (tmJYgLoc O a) := by
    simp only [tmJPermsVal, tmJYgLoc, hO, List.map_map]
    rfl
  rw [hval] at dall
  refine dall.mono ?_
  -- the cost
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hW1 : 1 ≤ (m + 1) * (q + 1) := by omega
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have hV1 : (m + 1) * (q + 1) ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
  have hV2 : (Val.list us).wt + (m + 1) * (q + 1) ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hV23 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hV34 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hV49 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hW2 : ((m + 1) * (q + 1)) ^ 2 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 :=
    Nat.pow_le_pow_left hV1 2
  have hW8 : ((m + 1) * (q + 1)) ^ 8 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8 :=
    Nat.pow_le_pow_left hV1 8
  have hmq2 : (m * q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hmq 2
  have hWW : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have ha := a.2
  have ha2 : (a : ℕ) * (2 * q) ≤ 2 * ((m + 1) * (q + 1)) ^ 2 := by
    have : (a : ℕ) * (2 * q) ≤ (q + 1) * (2 * (q + 1)) := Nat.mul_le_mul (by omega) (by omega)
    have e : (q + 1) * (2 * (q + 1)) = 2 * (q + 1) ^ 2 := by ring
    have : (q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hq1 2
    omega
  have hL := tmJYg_row_wt hu
  have hlen := length_lt_wt_list ((1 :: gs).map encPerm)
  simp only [List.length_map, List.length_cons] at hlen
  have hlen' : (1 :: gs).length = gs.length + 1 := rfl
  have he : (Val.list [encPerm r, encGroup gs]).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? hu)
  have hg : (encGroup gs).wt < (Val.list [encPerm r, encGroup gs]).wt := wt_le_wt_list (by simp)
  have wc := wt_tmJLocCtx_le m q
  have wa := wt_nat_le a
  have wq := wt_nat_le q
  have w2q := wt_nat_le 2
  have wul := wt_list2_le (.list us) (tmJLocCtx m q)
  have win := wt_list2_le (.list [.list us, tmJLocCtx m q]) (.nat a)
  have wca := wt_list2_le (tmJLocCtx m q) (.nat a)
  have wcL := wt_list2_le (.list [tmJLocCtx m q, .nat a]) (.list ((1 :: gs).map encPerm))
  have wres := wt_tmJPermsVal_le (tmJYgLoc O a)
  have hres : (tmJYgLoc O a).length = gs.length + 1 := by
    unfold tmJYgLoc; rw [hO]; simp
  have hval' : (Val.list ((1 :: gs).map fun s =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc a s⁻¹)))).wt =
      (tmJPermsVal (tmJYgLoc O a)).wt := by rw [hval]
  have P0 : (gs.length + 1) * (8 * (m * q + 1) ^ 2 + 1) ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) * (9 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e0 : ((Val.list us).wt + (m + 1) * (q + 1)) * (9 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2)
      = 9 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 := by ring
  rw [hres] at wres
  have P1 : (gs.length + 1) * tmJLocK ((m + 1) * (q + 1)) ≤
      10 ^ 14 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 9 := by
    unfold tmJLocK
    calc (gs.length + 1) * (10 ^ 14 * ((m + 1) * (q + 1)) ^ 8)
        ≤ ((Val.list us).wt + (m + 1) * (q + 1)) *
          (10 ^ 14 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 8) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hW8)
      _ = 10 ^ 14 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 9 := by ring
  have P2 : mapK * ((1 :: gs).length + 1) * ((Val.list [Val.list [tmJLocCtx m q, .nat a],
      .list ((1 :: gs).map encPerm)]).wt + (tmJPermsVal (tmJYgLoc O a)).wt + 1) ≤
      1000 * (2 * ((Val.list us).wt + (m + 1) * (q + 1))) *
        (500 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3) := by
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : 1000 * (2 * ((Val.list us).wt + (m + 1) * (q + 1))) *
      (500 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3) =
      1000000 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := by ring
  have r2 : (1 :: gs).length * tmJLocK ((m + 1) * (q + 1)) =
      (gs.length + 1) * tmJLocK ((m + 1) * (q + 1)) := rfl
  show _ ≤ 10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 9
  omega

/-! ### All rows -/

/-- The row values weigh little. -/
theorem tmJYg_rows_wt {m q : ℕ} (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs)) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) :
    (Val.list ((List.finRange q).map fun a => tmJPermsVal (tmJYgLoc O a))).wt ≤
      40 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := by
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by nlinarith
  have hV1 : (m + 1) * (q + 1) ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
  have hmq2 : (m * q + 1) ^ 2 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 :=
    Nat.pow_le_pow_left (hmq.trans hV1) 2
  have hV2 : (Val.list us).wt + (m + 1) * (q + 1) ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 :=
    Nat.le_self_pow (by norm_num) _
  have hV23 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hrow : ∀ a : Fin q, (tmJPermsVal (tmJYgLoc O a)).wt ≤
      13 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 := by
    intro a
    obtain ⟨r, gs, hO⟩ := hloc a
    have hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs]) := by
      rw [hus a a, hO]; rfl
    have hl := tmJYgLoc_length_lt O a hO hu
    have w := wt_tmJPermsVal_le (tmJYgLoc O a)
    have : (tmJYgLoc O a).length * (8 * (m * q + 1) ^ 2 + 1) ≤
        ((Val.list us).wt + (m + 1) * (q + 1)) * (9 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : ((Val.list us).wt + (m + 1) * (q + 1)) * (9 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2)
        = 9 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 := by ring
    have : 1 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 := Nat.one_le_pow _ _ (by omega)
    omega
  have := tmJ_wt_list_le (vs := (List.finRange q).map fun a => tmJPermsVal (tmJYgLoc O a))
    (E := 13 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3) (by
      intro v hv
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
      exact hrow a)
  simp only [List.length_map, List.length_finRange] at this
  have h2 : q * (2 * (13 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3) + 1) ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) * (27 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3) :=
    Nat.mul_le_mul (by omega) (by
      have : 1 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega)
  have e : ((Val.list us).wt + (m + 1) * (q + 1)) * (27 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 3)
      = 27 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := by ring
  have : 1 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The cost of all rows, in `V = wt us + (m + 1) (q + 1)`. -/
def tmJYgRowsK (V : ℕ) : ℕ := 10 ^ 17 * V ^ 10

/-- **All rows**, tabulated over `0, …, q - 1`. -/
theorem tmJ_rows_spec {P : Program} {tbR row mp locA dsA rg tbA tbe pr prg prt prte : ℕ}
    (htbR : P.HasAt tbR (mapFuns tbR row)) (hrow : P.funs[row]? = some (tmJRowLocF mp))
    (hmp : P.HasAt mp (mapFuns mp locA)) (hlocA : P.funs[locA]? = some (tmJLocAF dsA pr))
    (hds : P.funs[dsA]? = some (tmJDsAF rg tbA)) (hrg : P.HasAt rg (rangeFuns rg))
    (htb : P.HasAt tbA (mapFuns tbA tbe)) (htbe : P.funs[tbe]? = some tmJDsAEF)
    (hpr : TmJPairAt P pr prg prt prte) {m q : ℕ}
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m))))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs)) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a'))) :
    FunDet P tbR (.list [.list [.list us, tmJLocCtx m q], encFun fun i : Fin q => (i : ℕ)])
      (.list ((List.finRange q).map fun a => tmJPermsVal (tmJYgLoc O a)))
      (tmJYgRowsK ((Val.list us).wt + (m + 1) * (q + 1))) := by
  have hT := tabulate_spec htbR (c := .list [.list us, tmJLocCtx m q])
    (F := fun a : Fin q => tmJPermsVal (tmJYgLoc O a))
    (B := tmJYgRowK ((Val.list us).wt + (m + 1) * (q + 1))) (fun a => by
      obtain ⟨r, gs, hO⟩ := hloc a
      have hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs]) := by
        rw [hus a a, hO]; rfl
      exact tmJ_rowLoc_spec hrow hmp hlocA hds hrg htb htbe hpr O a hO us hu)
  refine hT.mono ?_
  have wR := tmJYg_rows_wt O hloc us hus
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hV1 : (m + 1) * (q + 1) ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
  have hV2 : ((m + 1) * (q + 1)) ^ 2 ≤ ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 :=
    Nat.pow_le_pow_left hV1 2
  have hW2 : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hq2 : (q + 1) ^ 2 ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.pow_le_pow_left hq1 2
  have hY1 : 1 ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
  have hV24 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hV12 : (Val.list us).wt + (m + 1) * (q + 1) ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hV510 : ((Val.list us).wt + (m + 1) * (q + 1)) ^ 5 ≤
      ((Val.list us).wt + (m + 1) * (q + 1)) ^ 10 := Nat.pow_le_pow_right hY1 (by norm_num)
  have wc := wt_tmJLocCtx_le m q
  have wid := wt_ids_le q
  have w2 := wt_list2_le (.list us) (tmJLocCtx m q)
  have w3 := wt_list2_le (.list [.list us, tmJLocCtx m q]) (encFun fun i : Fin q => (i : ℕ))
  have P1 : q * tmJYgRowK ((Val.list us).wt + (m + 1) * (q + 1)) ≤
      10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 10 := by
    unfold tmJYgRowK
    calc q * (10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 9)
        ≤ ((Val.list us).wt + (m + 1) * (q + 1)) *
          (10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 9) := Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 15 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 10 := by ring
  have P2 : mapK * (q + 1) * ((Val.list [.list [.list us, tmJLocCtx m q],
      encFun fun i : Fin q => (i : ℕ)]).wt +
      (Val.list ((List.finRange q).map fun a => tmJPermsVal (tmJYgLoc O a))).wt + 1) ≤
      1000 * ((Val.list us).wt + (m + 1) * (q + 1)) *
        (300 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4) := by
    have h1 : q + 1 ≤ (Val.list us).wt + (m + 1) * (q + 1) := by omega
    have h2 : (Val.list [.list [.list us, tmJLocCtx m q], encFun fun i : Fin q => (i : ℕ)]).wt +
        (Val.list ((List.finRange q).map fun a => tmJPermsVal (tmJYgLoc O a))).wt + 1 ≤
        300 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4 := by omega
    unfold mapK
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  have e2 : 1000 * ((Val.list us).wt + (m + 1) * (q + 1)) *
      (300 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 4) =
      300000 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 5 := by ring
  show _ ≤ 10 ^ 17 * ((Val.list us).wt + (m + 1) * (q + 1)) ^ 10
  omega

end GI.Impl
