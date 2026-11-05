module

public import Workspace.Assembly.BuildGens

@[expose] public section

/-!
# Building the pair state (`BuildSpec`)

`buildFuns b` is a program of 34 functions at base `b`. On the input value `inputVal G H`, its
entry returns the value of the pair state `graphState G H` of Algorithm 1 (`build_spec`), at cost
at most `buildK * (n + 1)^8`. So `BuildSpec` holds for every program that holds `buildFuns b` at
`b` (`buildSpec_of_hasAt`).

The entry reads the two adjacency matrices (`decode_inputVal`), builds the points
`ids = [0, …, n² - 1]`, the generators of the diagonal action (`genMap_spec`, with the identity
put in front as `encGroup` asks), the two colorings (`colMap_spec`), the domain indicator (all
ones), and lays out the ten entries of `StateVal`: no hierarchy, no rows, floor flag 0, `h = 2`,
`N = n²`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### The colors -/

theorem adjVal_eq (G : SimpleGraph (Fin n)) :
    adjVal G = .list ((List.finRange n).map fun a => encFun fun b => adjNat G a b) := rfl

theorem wt_adjVal_le (G : SimpleGraph (Fin n)) : (adjVal G).wt ≤ 21 * (n + 1) ^ 3 := by
  rw [← matVal_inputCells_left G G]
  refine wt_matVal_le (fun x hx => ?_) 1
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  exact inputLayout_le (inputMem_layout G G) a

theorem getElem?_map_finRange {α : Type} (F : Fin n → α) (a : Fin n) :
    ((List.finRange n).map F)[(a : ℕ)]? = some (F a) := by simp

/-- On `[[n, adj], p]`: the color code of position `p`, `2 [p / n = p % n] + adj[p / n][p % n]`. -/
def colF : Expr :=
  .letE (.arith .div (arg 1) (.get (arg 0) (.nat 0)))
    (.letE (.arith .mod (arg 1) (.get (arg 0) (.nat 0)))
      (.arith .add (.arith .mul (.nat 2) (.arith .eq (.var 1) (.var 2)))
        (.get (.get (.get (arg 0) (.nat 1)) (.var 1)) (.var 2))))

open Classical in
theorem colF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some colF) (G : SimpleGraph (Fin n))
    (p : Fin (n * n)) :
    FunDet P f (.list [.list [.nat n, adjVal G], .nat p])
      (.nat (pairCode (pairColor G ((pairEnum n).symm p)))) (3000 * (n + 1) ^ 3) := by
  set B := Val.list [.nat n, adjVal G] with hB
  set A := Val.list [B, .nat p] with hA
  have g0 : ∀ rest, Det P (A :: rest) (.get (arg 0) (.nat 0)) (.nat n) _ := fun rest =>
    Det.get' (Det.arg' (vs := [B, .nat p]) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (show [Val.nat n, adjVal G][0]? = some (.nat n) from rfl)
  have d1 := Det.arith' (op := .div) (z := (p.divNat : ℕ))
    (Det.arg' (P := P) (vs := [B, .nat p]) (rest := []) (j := 1) rfl) (g0 []) rfl
  have d2 := Det.arith' (op := .mod) (z := (p.modNat : ℕ))
    (Det.arg' (P := P) (vs := [B, .nat p]) (rest := [.nat (p.divNat : ℕ)]) (j := 1) rfl)
    (g0 _) rfl
  set rest := [Val.nat (p.divNat : ℕ), .nat (p.modNat : ℕ)] with hrest
  have he := Det.arith' (op := .eq) (z := if (p.divNat : ℕ) = p.modNat then 1 else 0)
    (Det.var' (P := P) (env := A :: rest) (i := 1) rfl) (Det.var' (i := 2) rfl) rfl
  have hm := Det.arith' (op := .mul) (z := 2 * if (p.divNat : ℕ) = p.modNat then 1 else 0)
    (Det.nat 2) he rfl
  have ga : Det P (A :: rest) (.get (arg 0) (.nat 1))
      (.list ((List.finRange n).map fun a => encFun fun b => adjNat G a b)) _ :=
    Det.get' (Det.arg' (vs := [B, .nat p]) (rest := rest) (j := 0) rfl) (Det.nat 1)
      (show [Val.nat n, adjVal G][1]? = some (adjVal G) from rfl)
  have gr := Det.get' ga (Det.var' (i := 1) rfl)
    (show ((List.finRange n).map fun a => encFun fun b => adjNat G a b)[(p.divNat : ℕ)]? =
      some (encFun fun b => adjNat G p.divNat b) from
      getElem?_map_finRange (fun a => encFun fun b => adjNat G a b) p.divNat)
  have gc := Det.get' gr (Det.var' (i := 2) rfl) (encFun_getElem? _ p.modNat)
  have ha := Det.arith' (op := .add) (z := pairCode (pairColor G ((pairEnum n).symm p))) hm gc
    (by rw [pairColor_code]; rfl)
  refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 ha)).mono ?_)
  have hp := p.isLt
  have h1 : (p.divNat : ℕ) ≤ p := Nat.div_le_self _ _
  have h2 : (p.modNat : ℕ) ≤ p := Nat.mod_le _ _
  have hc := pairCode_le (pairColor G ((pairEnum n).symm p))
  have hadj : adjNat G p.divNat p.modNat ≤ 1 := by unfold adjNat; split_ifs <;> omega
  have hrow : (encFun fun b => adjNat G p.divNat b).wt ≤ (adjVal G).wt := by
    rw [adjVal_eq]
    exact (wt_le_wt_list ((List.mem_map (f := fun a => encFun fun b => adjNat G a b)).mpr
      ⟨p.divNat, List.mem_finRange _, rfl⟩)).le
  have w0 := wt_nat_le n
  have w1 := wt_nat_le (p : ℕ)
  have w2 := wt_nat_le (p.divNat : ℕ)
  have w3 := wt_nat_le (p.modNat : ℕ)
  have w4 := wt_nat_le (adjNat G p.divNat p.modNat)
  have w5 := wt_nat_le (pairCode (pairColor G ((pairEnum n).symm p)))
  have w6 := wt_adjVal_le G
  have w7 : (Val.list ((List.finRange n).map fun a => encFun fun b => adjNat G a b)).wt =
    (adjVal G).wt := rfl
  have wB := wt_list2_le (.nat n) (adjVal G)
  have wA := wt_list2_le B (.nat (p : ℕ))
  have eB : (Val.list [.nat n, adjVal G]).wt = B.wt := rfl
  have eA : (Val.list [B, .nat (p : ℕ)]).wt = A.wt := rfl
  have hsq := sq_le_pow n
  have hp2 : (p : ℕ) + 2 * n + 1 ≤ (n + 1) ^ 2 := by linarith
  have h23 := pow_le_pow_of_le n (show 2 ≤ 3 by omega)
  have hif : (if (p.divNat : ℕ) = p.modNat then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have w8 := wt_nat_le (if (p.divNat : ℕ) = p.modNat then 1 else 0)
  have w9 := wt_nat_le (2 * if (p.divNat : ℕ) = p.modNat then 1 else 0)
  omega

/-- `map colF`, at base `b` (four functions). -/
def colMapFuns (b : ℕ) : List Expr := mapFuns b (b + 3) ++ [colF]

open Classical in
/-- **The coloring of a graph on the pair positions.** -/
theorem colMap_spec {P : Program} {b : ℕ} (h : P.HasAt b (colMapFuns b))
    (G : SimpleGraph (Fin n)) :
    FunDet P b (.list [.list [.nat n, adjVal G], encFun fun p : Fin (n * n) => (p : ℕ)])
      (encFun fun p => pairCode (pairColor G ((pairEnum n).symm p))) (150000 * (n + 1) ^ 6) := by
  have hf : P.funs[b + 3]? = some colF := by
    simpa [colMapFuns, mapFuns, loopFuns] using h.right.single
  refine (tabulate_spec h.left (F := fun p => .nat (pairCode (pairColor G ((pairEnum n).symm p))))
    fun p => colF_spec hf G p).mono ?_
  set ids := encFun fun p : Fin (n * n) => (p : ℕ) with hids
  have e1 : (Val.list ((List.finRange (n * n)).map
      fun p => Val.nat (pairCode (pairColor G ((pairEnum n).symm p))))).wt =
    (encFun fun p => pairCode (pairColor G ((pairEnum n).symm p))).wt := rfl
  rw [e1]
  have w1 := wt_encFun_le (fun p => pairCode (pairColor G ((pairEnum n).symm p))) (B := 3)
    fun p => pairCode_le _
  have wi : ids.wt ≤ 4 * (n * n + 1) ^ 2 := wt_ids_le (n * n)
  have w0 := wt_nat_le n
  have w6 := wt_adjVal_le G
  have wB := wt_list2_le (.nat n) (adjVal G)
  have wA := wt_list2_le (.list [.nat n, adjVal G]) ids
  have hsq := sq_le_pow n
  have hm2 : (n * n + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc (n * n + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = (n + 1) ^ 4 := by ring
  have h34 := pow_le_pow_of_le n (show 3 ≤ 4 by omega)
  have h24 := pow_le_pow_of_le n (show 2 ≤ 4 by omega)
  have h14 : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by omega) _
  have hY : (Val.list [.list [.nat n, adjVal G], ids]).wt +
      (encFun fun p => pairCode (pairColor G ((pairEnum n).symm p))).wt + 1 ≤
      130 * (n + 1) ^ 4 := by omega
  have hm : n * n + 1 ≤ 1 * (n + 1) ^ 2 := by omega
  have hX := mul_pow_le hm hY
  have hc1 : n * n * (3000 * (n + 1) ^ 3) ≤ 3000 * (n + 1) ^ 6 := by
    have := mul_pow_le (show n * n ≤ 1 * (n + 1) ^ 2 by omega)
      (show 3000 * (n + 1) ^ 3 ≤ 3000 * (n + 1) ^ 3 from le_rfl)
    have h56 := pow_le_pow_of_le n (show 5 ≤ 6 by omega)
    simp only [one_mul, show 2 + 3 = 5 from rfl] at this
    omega
  have e2 : mapK * (n * n + 1) * ((Val.list [.list [.nat n, adjVal G], ids]).wt +
      (encFun fun p => pairCode (pairColor G ((pairEnum n).symm p))).wt + 1) =
    1000 * ((n * n + 1) * ((Val.list [.list [.nat n, adjVal G], ids]).wt +
      (encFun fun p => pairCode (pairColor G ((pairEnum n).symm p))).wt + 1)) := by
    simp only [mapK]; ring
  rw [e2]
  simp only [one_mul, show 2 + 4 = 6 from rfl] at hX
  omega

/-! ### The builder -/

/-- The entry of the builder at base `b`. On `inputVal G H`: decode the graphs (`b + 1`), build
`ids = [0, …, n² - 1]` (`b + 13`), the generators (`b + 23`) with the identity in front
(`b + 31`), the two colorings (`b + 19`), the domain indicator (`b + 16`), and the state value. -/
def buildEntry (b : ℕ) : Expr :=
  .letE (.call (b + 1) (.var 0))
  (.letE (.get (.var 1) (.nat 0))
  (.letE (.arith .mul (.var 2) (.var 2))
  (.letE (.call (b + 13) (.var 3))
  (.letE (.call (b + 23) (mk2 (mk2 (.var 2) (.var 4)) (.var 4)))
  (.letE (.call (b + 31) (mk2 (mk1 (.var 4)) (.var 5)))
  (.letE (.call (b + 19) (mk2 (mk2 (.var 2) (.get (.var 1) (.nat 1))) (.var 4)))
  (.letE (.call (b + 19) (mk2 (mk2 (.var 2) (.get (.var 1) (.nat 2))) (.var 4)))
  (.letE (.call (b + 16) (mk2 (.var 3) (.nat 1)))
    (Expr.mkList [.var 3, mk2 (.var 3) (.var 6), .var 9, .var 7, .var 8, .nil, .nil, .nat 0,
      .nat 2, .var 3])))))))))

/-- **The builder**, at base `b` (34 functions). -/
def buildFuns (b : ℕ) : List Expr :=
  [buildEntry b] ++ decodeFuns (b + 1) ++ rangeFuns (b + 13) ++ replicateFuns (b + 16) ++
    colMapFuns (b + 19) ++ genMapFuns (b + 23) ++ appendFuns (b + 31)

theorem length_buildFuns (b : ℕ) : (buildFuns b).length = 34 := by
  simp [buildFuns, decodeFuns, rangeFuns, replicateFuns, colMapFuns, genMapFuns, entMapFuns,
    appendFuns, matFuns, rowMapFuns, mapFuns, loopFuns]

/-- The constant of the cost bound of the builder. -/
def buildK : ℕ := 10000000000

/-- The value of the pair state, as the builder lays it out. -/
noncomputable def graphStateVal (G H : SimpleGraph (Fin n)) : Val :=
  open Classical in
  .list [.nat (n * n), encGroup (pairGens n), .list (List.replicate (n * n) (.nat 1)),
    encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p))),
    encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p))), .list [], .list [], .nat 0,
    .nat 2, .nat (n * n)]

open Classical in
/-- `graphStateVal G H` is a value of the pair state. -/
theorem stateVal_graphStateVal (G H : SimpleGraph (Fin n)) :
    StateVal (pairEnum n) pairCode (graphStateVal G H) (graphState G H) := by
  refine ⟨encGroup (pairGens n), .list (List.replicate (n * n) (.nat 1)), _, _, .list [], .list [],
    groupVal_pairGens G H, ?_, rfl, rfl, ⟨[], rfl, List.Forall₂.nil⟩, rfl, ?_⟩
  · simp only [DomVal, graphState, Set.mem_univ, if_true, encFun, List.map_const',
      List.length_finRange]
  · simp [graphStateVal, graphState, Fintype.card_prod, Fintype.card_fin]

theorem buildFuns_parts {P : Program} {b : ℕ} (h : P.HasAt b (buildFuns b)) :
    P.funs[b]? = some (buildEntry b) ∧ P.HasAt (b + 1) (decodeFuns (b + 1)) ∧
      P.HasAt (b + 13) (rangeFuns (b + 13)) ∧ P.HasAt (b + 16) (replicateFuns (b + 16)) ∧
      P.HasAt (b + 19) (colMapFuns (b + 19)) ∧ P.HasAt (b + 23) (genMapFuns (b + 23)) ∧
      P.HasAt (b + 31) (appendFuns (b + 31)) := by
  simp only [buildFuns] at h
  refine ⟨h.left.left.left.left.left.left.single, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.left.left.left.left.left.right
  · simpa [decodeFuns, rangeFuns, matFuns, rowMapFuns, mapFuns, loopFuns, Nat.add_assoc]
      using h.left.left.left.left.right
  · simpa [decodeFuns, rangeFuns, matFuns, rowMapFuns, mapFuns, loopFuns, Nat.add_assoc]
      using h.left.left.left.right
  · simpa [decodeFuns, rangeFuns, replicateFuns, matFuns, rowMapFuns, mapFuns, loopFuns,
      Nat.add_assoc] using h.left.left.right
  · simpa [decodeFuns, rangeFuns, replicateFuns, colMapFuns, matFuns, rowMapFuns, mapFuns,
      loopFuns, Nat.add_assoc] using h.left.right
  · simpa [decodeFuns, rangeFuns, replicateFuns, colMapFuns, genMapFuns, entMapFuns, matFuns,
      rowMapFuns, mapFuns, loopFuns, Nat.add_assoc] using h.right

open Classical in
/-- **The builder.** On `inputVal G H`, the entry of `buildFuns b` returns the value of the pair
state `graphState G H`, at cost at most `buildK * (n + 1)^8`. -/
theorem build_spec {P : Program} {b : ℕ} (h : P.HasAt b (buildFuns b))
    (G H : SimpleGraph (Fin n)) :
    FunDet P b (inputVal G H) (graphStateVal G H) (buildK * (n + 1) ^ 8) := by
  obtain ⟨hentry, hdec, hrange, hrep, hcol, hgm, happ⟩ := buildFuns_parts h
  -- the facts about `n + 1`
  have hsq := sq_le_pow n
  have hm1 : (n * n) + 1 ≤ (n + 1) ^ 2 := by omega
  have hm2 : ((n * n) + 1) ^ 2 ≤ (n + 1) ^ 4 := by
    calc ((n * n) + 1) ^ 2 ≤ ((n + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left hm1 2
      _ = (n + 1) ^ 4 := by ring
  have p1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have p2 := pow_le_pow_of_le n (show 2 ≤ 3 by omega)
  have p3 := pow_le_pow_of_le n (show 3 ≤ 4 by omega)
  have p4 := pow_le_pow_of_le n (show 4 ≤ 5 by omega)
  have p5 := pow_le_pow_of_le n (show 5 ≤ 6 by omega)
  have p6 := pow_le_pow_of_le n (show 6 ≤ 8 by omega)
  -- the specifications of the parts
  have sD : FunDet P (b + 1) (inputVal G H) (Val.list [.nat n, adjVal G, adjVal H]) (12400000 * (n + 1) ^ 5) := by
    refine (decode_inputVal hdec G H).mono ?_
    have hi := wt_inputVal_le G H
    have := mul_pow_le (show (n + 1) ^ 2 ≤ 1 * (n + 1) ^ 2 by omega)
      (show (inputVal G H).wt + (n + 1) ^ 2 ≤ 31 * (n + 1) ^ 3 by omega)
    simp only [one_mul, show 2 + 3 = 5 from rfl] at this
    rw [Nat.mul_assoc, decodeK]
    omega
  have wids : (encFun fun p : Fin (n * n) => (p : ℕ)).wt ≤ 4 * (n + 1) ^ 4 := (wt_ids_le (n * n)).trans (by omega)
  have sR : FunDet P (b + 13) (.nat (n * n)) (encFun fun p : Fin (n * n) => (p : ℕ)) (8000 * (n + 1) ^ 6) := by
    refine FunAll.mono (range_spec hrange (n * n)) fun w c hw => ⟨?_, ?_⟩
    · rw [hw.1, encFun_id]
    · have hc := hw.2
      rw [hw.1, ← encFun_id, loopModK_mul] at hc
      have := wt_nat_le (n * n)
      have := mul_pow_le (show (n * n) + 1 ≤ 1 * (n + 1) ^ 2 by omega)
        (show (Val.nat (n * n)).wt + (n * n) + (encFun fun p : Fin (n * n) => (p : ℕ)).wt + 1 ≤ 8 * (n + 1) ^ 4 by omega)
      simp only [one_mul, show 2 + 4 = 6 from rfl] at this
      omega
  have sG : FunDet P (b + 23) (.list [.list [.nat n, (encFun fun p : Fin (n * n) => (p : ℕ))], (encFun fun p : Fin (n * n) => (p : ℕ))]) (Val.list ((pairGens n).map encPerm)) (200000 * (n + 1) ^ 8) :=
    genMap_spec hgm
  have wgl : (Val.list ((pairGens n).map encPerm)).wt ≤ 13 * (n + 1) ^ 6 := wt_pairGens_le n
  have hone : (encFun fun p : Fin (n * n) => (p : ℕ)) = encPerm (1 : Perm (Fin (n * n))) := by rw [encFun_id, range_eq_encPerm_one]
  have wgl1 : (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)).wt ≤ 25 * (n + 1) ^ 6 := by
    have := wt_list_cons_le (encPerm (1 : Perm (Fin (n * n)))) ((pairGens n).map encPerm)
    rw [← hone] at this
    have e : (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)) = Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm) := rfl
    rw [e, ← hone]
    omega
  have sA : FunDet P (b + 31) (.list [.list [(encFun fun p : Fin (n * n) => (p : ℕ))], (Val.list ((pairGens n).map encPerm))]) (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)) (110000 * (n + 1) ^ 8) := by
    refine FunAll.mono (append_spec happ [(encFun fun p : Fin (n * n) => (p : ℕ))] ((pairGens n).map encPerm)) fun w c hw => ?_
    have e : Val.list ([(encFun fun p : Fin (n * n) => (p : ℕ))] ++ (pairGens n).map encPerm) = (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)) := by
      rw [hone]; rfl
    rw [e] at hw
    refine ⟨hw.1, ?_⟩
    have hc := hw.2
    rw [hw.1] at hc
    have hl : ((pairGens n).map encPerm).length = (n * n) := by simp [pairGens]
    rw [hl] at hc
    have w1 := wt_list1_le (encFun fun p : Fin (n * n) => (p : ℕ))
    have w2 := wt_list2_le (.list [(encFun fun p : Fin (n * n) => (p : ℕ))]) (Val.list ((pairGens n).map encPerm))
    have hgl' : (Val.list ((pairGens n).map encPerm)).wt = (Val.list ((pairGens n).map encPerm)).wt := rfl
    have := mul_pow_le (show (n * n) + 1 ≤ 1 * (n + 1) ^ 2 by omega)
      (show (Val.list [.list [(encFun fun p : Fin (n * n) => (p : ℕ))], .list ((pairGens n).map encPerm)]).wt + (n * n) + (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)).wt + 1 ≤
        100 * (n + 1) ^ 6 by omega)
    simp only [one_mul, show 2 + 6 = 8 from rfl] at this
    rw [loopModK_mul] at hc
    omega
  have sX : FunDet P (b + 19) (.list [.list [.nat n, adjVal G], (encFun fun p : Fin (n * n) => (p : ℕ))]) (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p))))
      (150000 * (n + 1) ^ 6) := colMap_spec hcol G
  have sY : FunDet P (b + 19) (.list [.list [.nat n, adjVal H], (encFun fun p : Fin (n * n) => (p : ℕ))]) (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p))))
      (150000 * (n + 1) ^ 6) := colMap_spec hcol H
  have wdv : (Val.list (List.replicate (n * n) (.nat 1))).wt ≤ 7 * (n * n) + 4 := by
    have := wt_encFun_le (fun _ : Fin (n * n) => 1) (B := 1) fun _ => le_rfl
    have e : encFun (fun _ : Fin (n * n) => 1) = (Val.list (List.replicate (n * n) (.nat 1))) := by
      simp [encFun, List.map_const', List.length_finRange]
    rw [e] at this
    omega
  have sP : FunDet P (b + 16) (.list [.nat (n * n), .nat 1]) (Val.list (List.replicate (n * n) (.nat 1))) (30000 * (n + 1) ^ 4) := by
    refine FunAll.mono (replicate_spec hrep (n * n) (.nat 1)) fun w c hw => ⟨hw.1, ?_⟩
    have hc := hw.2
    rw [hw.1] at hc
    have w1 := wt_list2_le (.nat (n * n)) (.nat 1)
    have := wt_nat_le (n * n)
    have := wt_nat_le 1
    have := mul_pow_le (show (n * n) + 1 ≤ 1 * (n + 1) ^ 2 by omega)
      (show (Val.list [.nat (n * n), .nat 1]).wt + (n * n) + (Val.list (List.replicate (n * n) (.nat 1))).wt + 1 ≤ 30 * (n + 1) ^ 2 by omega)
    simp only [one_mul, show 2 + 2 = 4 from rfl] at this
    rw [loopModK_mul] at hc
    omega
  -- the weights of the parts
  have wI := wt_inputVal_le G H
  have wD : (Val.list [.nat n, adjVal G, adjVal H]).wt < 12400000 * (n + 1) ^ 5 := sD.wt_lt
  have wDG : (adjVal G).wt < (Val.list [.nat n, adjVal G, adjVal H]).wt := wt_le_wt_list (by simp)
  have wDH : (adjVal H).wt < (Val.list [.nat n, adjVal G, adjVal H]).wt := wt_le_wt_list (by simp)
  have wn := wt_nat_le n
  have wmm := wt_nat_le (n * n)
  have wx : (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))).wt ≤ (n * n) * (2 * 3 + 5) + 4 :=
    wt_encFun_le (fun p => pairCode (pairColor G ((pairEnum n).symm p))) fun p => pairCode_le _
  have wy : (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))).wt ≤ (n * n) * (2 * 3 + 5) + 4 :=
    wt_encFun_le (fun p => pairCode (pairColor H ((pairEnum n).symm p))) fun p => pairCode_le _
  -- the run
  have eV : (graphStateVal G H) = .list [.nat (n * n), .list [.nat (n * n), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm))], (Val.list (List.replicate (n * n) (.nat 1))), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), .list [], .list [], .nat 0,
      .nat 2, .nat (n * n)] := rfl
  have hsum := sum_wt_lt_wt_list ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  set c := 10 * (Val.list ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])).wt + 50 with hc
  have d10 : Det P ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))]) (Expr.mkList [.var 3, mk2 (.var 3) (.var 6), .var 9, .var 7, .var 8, .nil,
      .nil, .nat 0, .nat 2, .var 3]) (graphStateVal G H) (10 * (c + (graphStateVal G H).wt + 1) + 5) := by
    rw [eV]
    refine Det.mkList (ps := [(.var 3, .nat (n * n)), (mk2 (.var 3) (.var 6), .list [.nat (n * n), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm))]),
      (.var 9, (Val.list (List.replicate (n * n) (.nat 1)))), (.var 7, (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p))))), (.var 8, (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p))))), (.nil, .list []), (.nil, .list []),
      (.nat 0, .nat 0), (.nat 2, .nat 2), (.var 3, .nat (n * n))]) ?_
    have w2 := wt_list2_le (.nat (n * n)) (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm))
    have w0 := wt_nat_le 0
    have w2' := wt_nat_le 2
    simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact (Det.var' (P := P) (env := ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])) (i := 3) rfl).mono (by omega)
    · exact (Det.mk2 (Det.var' (P := P) (env := ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])) (i := 3) rfl)
        (Det.var' (i := 6) rfl)).mono (by omega)
    · exact (Det.var' (P := P) (env := ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])) (i := 9) rfl).mono (by omega)
    · exact (Det.var' (P := P) (env := ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])) (i := 7) rfl).mono (by omega)
    · exact (Det.var' (P := P) (env := ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])) (i := 8) rfl).mono (by omega)
    · exact Det.nil.mono (by omega)
    · exact Det.nil.mono (by omega)
    · exact (Det.nat 0).mono (by omega)
    · exact (Det.nat 2).mono (by omega)
    · exact (Det.var' (P := P) (env := ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])) (i := 3) rfl).mono (by omega)
  have d1 := Det.call (Det.var' (P := P) (env := [inputVal G H]) (i := 0) rfl) sD
  have d2 := Det.get' (Det.var' (P := P) (env := [inputVal G H, (Val.list [.nat n, adjVal G, adjVal H])]) (i := 1) rfl) (Det.nat 0)
    (show [Val.nat n, adjVal G, adjVal H][0]? = some (.nat n) from rfl)
  have d3 := Det.arith' (op := .mul) (z := (n * n)) (Det.var' (P := P) (env := [inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n])
    (i := 2) rfl) (Det.var' (i := 2) rfl) rfl
  have d4 := Det.call (Det.var' (P := P) (env := [inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n)]) (i := 3) rfl) sR
  have d5 := Det.call (Det.mk2 (Det.mk2 (Det.var' (P := P)
    (env := [inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ))]) (i := 2) rfl) (Det.var' (i := 4) rfl))
    (Det.var' (i := 4) rfl)) sG
  have d6 := Det.call (Det.mk2 (Det.mk1 (Det.var' (P := P)
    (env := [inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm))]) (i := 4) rfl)) (Det.var' (i := 5) rfl)) sA
  have d7 := Det.call (Det.mk2 (Det.mk2 (Det.var' (P := P)
    (env := [inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm))]) (i := 2) rfl)
    (Det.get' (Det.var' (i := 1) rfl) (Det.nat 1)
      (show [Val.nat n, adjVal G, adjVal H][1]? = some (adjVal G) from rfl)))
    (Det.var' (i := 4) rfl)) sX
  have d8 := Det.call (Det.mk2 (Det.mk2 (Det.var' (P := P)
    (env := [inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p))))]) (i := 2) rfl)
    (Det.get' (Det.var' (i := 1) rfl) (Det.nat 2)
      (show [Val.nat n, adjVal G, adjVal H][2]? = some (adjVal H) from rfl)))
    (Det.var' (i := 4) rfl)) sY
  have d9 := Det.call (Det.mk2 (Det.var' (P := P)
    (env := [inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p))))]) (i := 3) rfl) (Det.nat 1)) sP
  refine FunDet.intro hentry ((Det.letE d1 (Det.letE d2 (Det.letE d3 (Det.letE d4 (Det.letE d5
    (Det.letE d6 (Det.letE d7 (Det.letE d8 (Det.letE d9 d10))))))))).mono ?_)
  -- the cost
  have wV := wt_list_le [.nat (n * n), .list [.nat (n * n), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm))], (Val.list (List.replicate (n * n) (.nat 1))), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), .list [], .list [], .nat 0,
      .nat 2, .nat (n * n)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, wt_list_nil] at wV
  rw [← eV] at wV
  have w2 := wt_list2_le (.nat (n * n)) (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm))
  have w0 := wt_nat_le 0
  have w2' := wt_nat_le 2
  have wE := wt_list_le ([inputVal G H, (Val.list [.nat n, adjVal G, adjVal H]), .nat n, .nat (n * n), (encFun fun p : Fin (n * n) => (p : ℕ)), (Val.list ((pairGens n).map encPerm)), (Val.list (encPerm (1 : Perm (Fin (n * n))) :: (pairGens n).map encPerm)), (encFun (fun p => pairCode (pairColor G ((pairEnum n).symm p)))), (encFun (fun p => pairCode (pairColor H ((pairEnum n).symm p)))), (Val.list (List.replicate (n * n) (.nat 1)))])
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at wE
  have a1 := wt_list2_le (.list [.nat n, (encFun fun p : Fin (n * n) => (p : ℕ))]) (encFun fun p : Fin (n * n) => (p : ℕ))
  have a2 := wt_list2_le (.nat n) (encFun fun p : Fin (n * n) => (p : ℕ))
  have a3 := wt_list1_le (encFun fun p : Fin (n * n) => (p : ℕ))
  have a4 := wt_list2_le (.list [(encFun fun p : Fin (n * n) => (p : ℕ))]) (Val.list ((pairGens n).map encPerm))
  have a5 := wt_list2_le (.list [.nat n, adjVal G]) (encFun fun p : Fin (n * n) => (p : ℕ))
  have a6 := wt_list2_le (.nat n) (adjVal G)
  have a7 := wt_list2_le (.list [.nat n, adjVal H]) (encFun fun p : Fin (n * n) => (p : ℕ))
  have a8 := wt_list2_le (.nat n) (adjVal H)
  have a9 := wt_list2_le (.nat (n * n)) (.nat 1)
  have a10 := wt_nat_le 1
  have hm' : (n * n) ≤ (n + 1) ^ 2 := by omega
  rw [buildK]
  omega

/-- **`BuildSpec`** for every program that holds the builder at `b`. -/
theorem buildSpec_of_hasAt {P : Program} {b : ℕ} (h : P.HasAt b (buildFuns b)) :
    BuildSpec P b := by
  classical
  refine ⟨buildK, 8, fun n G H => FunAll.mono (build_spec h G H) fun v c hv => ⟨?_, hv.2⟩⟩
  rw [hv.1]
  exact stateVal_graphStateVal G H

end GI.Assembly
