module

public import Workspace.Impl.KRefStep
public import Workspace.Impl.KRefStable

@[expose] public section

/-!
# The whole program

The main function reads `n` and `n^k` from the input `[0^n, c, c']`, builds the tables (the
powers of `n` and of `k`, the maps `τ`, the merge maps, the table of neighbours), and runs
`2 n^k` rounds (`krefRoundG`) from the state `[c, c']`. The result is the state of
`krefIter c c' (2 n^k)`, that is `[d, d']` with `d, d'` as in `kref_joint`.

The program `krefProg k` has 99 functions, at fixed places:
`0` main, `1` range, `4` powers, `8` map of digits, `11` digits, `16` map of merge maps,
`19` merge maps, `24` table, `28` patterns, `36` codes, `44` update lists, `48` iterate (body at
`51`), `52` look-up, `56` Horner, `60` ranks, `68` counts, `77` vector codes, `81` vector-code
table, `85` join, `92` append, `95` signature table.
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (BinOp len)

variable {n k : ℕ}

/-! ### The program -/

/-- `2 * N + n + k + 2`, from `n` (variable 1) and `N = n^k` (variable 2). -/
def krefBE (k : ℕ) : Expr :=
  .arith .add (.arith .add (.arith .add (.arith .mul (.nat 2) (.var 2)) (.var 1)) (.nat k)) (.nat 2)

/-- `2 * N * n`. -/
def krefME : Expr := .arith .mul (.arith .mul (.nat 2) (.var 2)) (.var 1)

/-- The main function. -/
def krefMainE (k : ℕ) : Expr :=
  .letE (.length (arg 0))
   (.letE (.length (arg 1))
    (.letE (.call 4 (mk3 (.var 1) (.nat k) .nil))
     (.letE (.call 4 (mk3 (.nat k) (.nat k) .nil))
      (.letE (.call 8 (mk2 (mk2 (.var 4) (.nat k)) (.call 1 (.nat (k ^ k)))))
       (.letE (.call 16 (mk2 (mk2 (.call 1 (.nat k)) (.nat k)) (.call 1 (.nat k))))
        (.letE (.call 24 (mk2 (.snoc (mk4 (.var 3) (.var 1) (.var 5) (.var 6)) (.call 1 (.var 1)))
            (.call 1 (.var 2))))
          (.call 48 (mk3 (mk3 (.var 7) (krefBE k) (.call 1 krefME))
            (.arith .mul (.nat 2) (.var 2)) (mk2 (arg 1) (arg 2))))))))))

/-- The functions of the program (nested to the right, so that each module is the left part of
a tail). -/
def krefFuns (k : ℕ) : List Expr :=
  [krefMainE k] ++ (rangeFuns 1 ++ (krefPowFuns 4 ++ (mapFuns 8 11 ++ (krefDigFuns 11 ++
    (mapFuns 16 19 ++ (krefRhoFuns 19 ++ (krefNbsFuns 24 11 28 36 44 ++ (krefPatFuns 28 ++
    (krefCodesFuns 36 ++ (krefUpdFuns 44 36 ++ (iterFuns 48 51 ++ ([krefRoundG 81 85 92 95 60] ++
    (krefLookFuns 52 ++ (krefHorFuns 56 ++ (krefRanksFuns 60 ++ (krefCntsFuns 68 ++
    (krefVcsFuns 77 52 56 ++ (krefVtabFuns 81 77 ++ (krefFlatFuns 85 ++ (appendFuns 92 ++
    krefStabFuns 95 52 56 60 68 77))))))))))))))))))))

/-- The program. -/
def krefProg (k : ℕ) : Program := ⟨krefFuns k, []⟩

theorem krefProg_at (k : ℕ) : (krefProg k).HasAt 0 (krefFuns k) := by
  have h := Program.hasAt_append [] (krefFuns k) [] []
  simpa [krefProg] using h

theorem kref_hasAt_shift {P : Program} {b a b' : ℕ} {A B : List Expr} (h : P.HasAt b (A ++ B))
    (ha : A.length = a) (hb : b + a = b') : P.HasAt b' B := by
  subst ha hb; exact h.right

section Layout

variable (k : ℕ)

theorem kref_at_main : (krefProg k).funs[0]? = some (krefMainE k) := rfl

theorem kref_layout : (krefProg k).HasAt 1 (rangeFuns 1) ∧ (krefProg k).HasAt 4 (krefPowFuns 4) ∧
    (krefProg k).HasAt 8 (mapFuns 8 11) ∧ (krefProg k).HasAt 11 (krefDigFuns 11) ∧
    (krefProg k).HasAt 16 (mapFuns 16 19) ∧ (krefProg k).HasAt 19 (krefRhoFuns 19) ∧
    (krefProg k).HasAt 24 (krefNbsFuns 24 11 28 36 44) ∧ (krefProg k).HasAt 28 (krefPatFuns 28) ∧
    (krefProg k).HasAt 36 (krefCodesFuns 36) ∧ (krefProg k).HasAt 44 (krefUpdFuns 44 36) ∧
    (krefProg k).HasAt 48 (iterFuns 48 51) ∧
    (krefProg k).funs[51]? = some (krefRoundG 81 85 92 95 60) ∧
    (krefProg k).HasAt 52 (krefLookFuns 52) ∧ (krefProg k).HasAt 56 (krefHorFuns 56) ∧
    (krefProg k).HasAt 60 (krefRanksFuns 60) ∧ (krefProg k).HasAt 68 (krefCntsFuns 68) ∧
    (krefProg k).HasAt 77 (krefVcsFuns 77 52 56) ∧ (krefProg k).HasAt 81 (krefVtabFuns 81 77) ∧
    (krefProg k).HasAt 85 (krefFlatFuns 85) ∧ (krefProg k).HasAt 92 (appendFuns 92) ∧
    (krefProg k).HasAt 95 (krefStabFuns 95 52 56 60 68 77) := by
  have h0 := krefProg_at k
  unfold krefFuns at h0
  have h1 := kref_hasAt_shift h0 rfl (rfl : 0 + 1 = 1)
  have h2 := kref_hasAt_shift h1 rfl (rfl : 1 + 3 = 4)
  have h3 := kref_hasAt_shift h2 rfl (rfl : 4 + 4 = 8)
  have h4 := kref_hasAt_shift h3 rfl (rfl : 8 + 3 = 11)
  have h5 := kref_hasAt_shift h4 rfl (rfl : 11 + 5 = 16)
  have h6 := kref_hasAt_shift h5 rfl (rfl : 16 + 3 = 19)
  have h7 := kref_hasAt_shift h6 rfl (rfl : 19 + 5 = 24)
  have h8 := kref_hasAt_shift h7 rfl (rfl : 24 + 4 = 28)
  have h9 := kref_hasAt_shift h8 rfl (rfl : 28 + 8 = 36)
  have h10 := kref_hasAt_shift h9 rfl (rfl : 36 + 8 = 44)
  have h11 := kref_hasAt_shift h10 rfl (rfl : 44 + 4 = 48)
  have h12 := kref_hasAt_shift h11 rfl (rfl : 48 + 3 = 51)
  have h13 := kref_hasAt_shift h12 rfl (rfl : 51 + 1 = 52)
  have h14 := kref_hasAt_shift h13 rfl (rfl : 52 + 4 = 56)
  have h15 := kref_hasAt_shift h14 rfl (rfl : 56 + 4 = 60)
  have h16 := kref_hasAt_shift h15 rfl (rfl : 60 + 8 = 68)
  have h17 := kref_hasAt_shift h16 rfl (rfl : 68 + 9 = 77)
  have h18 := kref_hasAt_shift h17 rfl (rfl : 77 + 4 = 81)
  have h19 := kref_hasAt_shift h18 rfl (rfl : 81 + 4 = 85)
  have h20 := kref_hasAt_shift h19 rfl (rfl : 85 + 7 = 92)
  have h21 := kref_hasAt_shift h20 rfl (rfl : 92 + 3 = 95)
  exact ⟨h1.left, h2.left, h3.left, h4.left, h5.left, h6.left, h7.left, h8.left, h9.left,
    h10.left, h11.left, h12.left.single, h13.left, h14.left, h15.left, h16.left, h17.left,
    h18.left, h19.left, h20.left, h21⟩

theorem kref_at_nbAt : KrefNbAt (krefProg k) 11 28 36 44 :=
  ⟨(kref_layout k).2.2.2.1, (kref_layout k).2.2.2.2.2.2.2.1, (kref_layout k).2.2.2.2.2.2.2.2.1,
    (kref_layout k).2.2.2.2.2.2.2.2.2.1⟩

theorem kref_at_roundAt : KrefRoundAt (krefProg k) 52 56 60 68 77 81 85 92 95 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlk, hho, hrk, hcn, hvc, hvt, hfl, hap, hst⟩ :=
    kref_layout k
  exact ⟨⟨hlk, hho, hrk, hcn, hvc⟩, hvt, hfl, hap, hst⟩

end Layout

/-! ### The set-up modules -/

/-- **Range**, with a weight bound. -/
theorem kref_range {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) {m Z : ℕ} (hm : m ≤ Z)
    (hw : (natList (List.range m)).wt ≤ Z) :
    FunDet P b (.nat m) (natList (List.range m)) (3000 * (Z + 1) ^ 2) := by
  refine FunAll.mono (range_spec h m) fun w c hw' => ⟨hw'.1, ?_⟩
  obtain ⟨rfl, hc⟩ := hw'
  have := wt_nat_le m
  have h1 : loopModK * (m + 1) * ((Val.nat m).wt + m + (natList (List.range m)).wt + 1) ≤
      loopModK * (Z + 1) * (3 * (Z + 1)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e : loopModK * (Z + 1) * (3 * (Z + 1)) = 3000 * (Z + 1) ^ 2 := by unfold loopModK; ring
  omega

def krefTausK : ℕ := mapK * (3 * krefDigK + 11) * 2 ^ 5

/-- **The maps `τ`**, as digit lists. -/
theorem kref_taus {P : Program} {b dg : ℕ} (h : P.HasAt b (mapFuns b dg))
    (hdg : P.HasAt dg (krefDigFuns dg)) :
    FunDet P b (.list [.list [natList (krefPowList k k), .nat k], natList (List.range (k ^ k))])
      (krefTausV k) (krefTausK * (krefZ n k + 1) ^ 5) := by
  obtain ⟨hX2, hX12, hX23, hX34, hZ⟩ := kref_X4 (n := n) (k := k)
  have hkX := @k_le_krefX n k
  have hkk := @kk_le_krefX n k
  have hwpw := kref_wt_pwk (n := n) (k := k)
  have hm := kref_mapL h (l := List.range (k ^ k)) (enc := Val.nat)
    (F := fun j => natList ((krefPowList k k).map fun p => j / p % k)) (Y := krefZ n k) (A := 1)
    (K := krefDigK) (d := 3) (by norm_num) (fun a _ a' _ haa => by cases haa; rfl)
    (fun j hj => kref_dig hdg (fun p hp => ((kref_pwk_le (n := n)) p hp).trans X_le_Z)
      (hkX.trans X_le_Z) (by have := List.mem_range.mp hj; omega) (by omega))
    (by have := wt_list2_le (natList (krefPowList k k)) (.nat k); have := wt_nat_le k; omega)
    (by
      have := kref_wt_range (n := n) (k := k) (m := k ^ k) (by omega)
      have e : (Val.list ((List.range (k ^ k)).map Val.nat)).wt =
        (natList (List.range (k ^ k))).wt := rfl
      omega)
  have e : Val.list ((List.range (k ^ k)).map fun j =>
      natList ((krefPowList k k).map fun p => j / p % k)) = krefTausV k := by
    unfold krefTausV krefTups
    rw [kref_range_map, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    rw [kref_digits_eq (n := k) (k := k) j]
  rw [e] at hm
  exact hm.mono (le_of_eq (by unfold krefTausK; ring))

def krefRhosMK : ℕ := mapK * (3 * krefRhoK + 11) * 2 ^ 5

/-- **The merge maps.** -/
theorem kref_rhosM {P : Program} {b rh : ℕ} (h : P.HasAt b (mapFuns b rh))
    (hrh : P.HasAt rh (krefRhoFuns rh)) :
    FunDet P b (.list [.list [natList (List.range k), .nat k], natList (List.range k)])
      (.list ((krefRhos k).map natList)) (krefRhosMK * (krefZ n k + 1) ^ 5) := by
  obtain ⟨hX2, hX12, hX23, hX34, hZ⟩ := kref_X4 (n := n) (k := k)
  have hkX := @k_le_krefX n k
  have hwr := kref_wt_range (n := n) (k := k) (m := k) (by omega)
  have hm := kref_mapL h (l := List.range k) (enc := Val.nat)
    (F := fun i => natList ((List.range k).map fun r => if r = i then k else r)) (Y := krefZ n k)
    (A := 1) (K := krefRhoK) (d := 3) (by norm_num) (fun a _ a' _ haa => by cases haa; rfl)
    (fun i hi => kref_rho hrh (fun r hr => by have := List.mem_range.mp hr; omega) (by omega)
      (by have := List.mem_range.mp hi; omega) (by omega))
    (by have := wt_list2_le (natList (List.range k)) (.nat k); have := wt_nat_le k; omega)
    (by
      have e : (Val.list ((List.range k).map Val.nat)).wt = (natList (List.range k)).wt := rfl
      omega)
  have e : Val.list ((List.range k).map fun i =>
      natList ((List.range k).map fun r => if r = i then k else r)) =
      .list ((krefRhos k).map natList) := by
    simp [krefRhos, List.map_map, Function.comp_def]
  rw [e] at hm
  exact hm.mono (le_of_eq (by unfold krefRhosMK; ring))

/-! ### Encodings -/

theorem kref_encK_eq (c : (Fin k → Fin n) → ℕ) : encKColoring c = natList ((krefTups n k).map c) := by
  simp [encKColoring, natList, krefTups, List.map_map, Function.comp_def]

theorem kref_Av_encK (col : KCol n k) (β : Bool) : natList (krefAv col β) = encKColoring (col β) := by
  rw [kref_encK_eq]; rfl

theorem kref_St_eq (col : KCol n k) :
    krefSt col = .list [encKColoring (col false), encKColoring (col true)] := by
  unfold krefSt; rw [kref_Av_encK, kref_Av_encK]

theorem kref_wt_encK {c : (Fin k → Fin n) → ℕ} (hc : ∀ x, c x ≤ n ^ k) :
    (encKColoring c).wt ≤ 7 * krefX n k ^ 2 := by
  rw [kref_encK_eq]
  exact kref_wt_natList_X (by rw [List.length_map, length_krefTups]; exact N_le_krefX)
    (fun a ha => by obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha; exact (hc x).trans N_le_krefX)

theorem kref_wt_zeros (m : ℕ) : (Val.list (List.replicate m (.nat 0))).wt ≤ 5 * m + 4 := by
  have e : List.replicate m (Val.nat 0) = (List.range m).map fun _ => Val.nat 0 := by simp
  rw [e]
  have h := kref_wt_listMap (l := List.range m) (f := fun _ => Val.nat 0) (C := 2)
    (fun _ _ => wt_nat_le 0)
  simp only [List.length_range] at h
  omega

end GI.Impl
