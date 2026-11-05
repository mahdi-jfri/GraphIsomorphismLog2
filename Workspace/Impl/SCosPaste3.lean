module

public import Workspace.Impl.SCosPaste2

@[expose] public section

/-!
# Pasting the answers of the children, the program

Function `7` (`scosPasteF`) runs on the list of the answers of the children. It keeps the
nonempty answers (`filterFuns 244 8`). If there are none, it returns `[]`. Otherwise, with the
first one `[z₁, lv₁]`, it computes `z₁⁻¹`, the list of the `z₁⁻¹ zⱼ` (`mapFuns 247 9`), the
group value of the generators of `lv₁` and these (`appendFuns 250`, `mkGroupFuns 150`), and
normalizes it by a pointwise stabilizer of no points (`pstabFuns 117 0`). The mathematics is in
`SCosPaste2.lean`. The cost is bounded by `scosOwnP hps n c` (`scos_paste_spec`).

The weights are bounded through `M = scosPasteM n c` (`SCosPaste1.lean`). The group value
given to the pointwise stabilizer has weight at most `scosPasteGW n c = 10^7 M^4`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

/-- The weight bound of the argument of the pointwise stabilizer in the paste. -/
def scosPasteGW (n c : ℕ) : ℕ := 10000000 * scosPasteM n c ^ 4

/-- The own cost of the paste. -/
noncomputable def scosOwnP (hps : PointwiseStab) (n c : ℕ) : ℕ :=
  (pointwiseStabPrim hps).boundSize (scosPasteGW n c) + pstabK * scosPasteGW n c ^ 9 +
    1000000000000000 * scosPasteM n c ^ 6

/-- `a ≤ A X^d` and `d ≤ D` give `a ≤ A X^D`, for `X ≥ 1`. -/
theorem scosPaste_pow_up {a A X d D : ℕ} (hX : 1 ≤ X) (h : a ≤ A * X ^ d) (hd : d ≤ D) :
    a ≤ A * X ^ D :=
  h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hd))

/-- The arithmetic of `scosOwnP_le`, for `M ≤ Z`. -/
theorem scosPaste_own_aux (pc k M Z : ℕ) (hZ : 1 ≤ Z) (hM : M ≤ Z) :
    pc * (10000000 * M ^ 4 + 2) ^ k + pstabK * (10000000 * M ^ 4) ^ 9 +
      1000000000000000 * M ^ 6 ≤
      (pc + pstabK + 1000000000000000) * 10000002 ^ (k + 9) * Z ^ (4 * (k + 9)) := by
  have hA : 1 ≤ 10000002 := by norm_num
  have hM4 : M ^ 4 ≤ Z ^ 4 := Nat.pow_le_pow_left hM 4
  have hZ4 : 1 ≤ Z ^ 4 := Nat.one_le_pow _ _ hZ
  have hb : 10000000 * M ^ 4 + 2 ≤ 10000002 * Z ^ 4 := by omega
  have hb' : 10000000 * M ^ 4 ≤ 10000002 * Z ^ 4 := by omega
  have hP : ∀ j, j ≤ k + 9 → (10000002 * Z ^ 4) ^ j ≤ 10000002 ^ (k + 9) * Z ^ (4 * (k + 9)) := by
    intro j hj
    rw [mul_pow, ← pow_mul]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right hA hj)
      (Nat.pow_le_pow_right hZ (by omega))
  have t1 : pc * (10000000 * M ^ 4 + 2) ^ k ≤ pc * (10000002 ^ (k + 9) * Z ^ (4 * (k + 9))) :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hb k).trans (hP k (by omega)))
  have t2 : pstabK * (10000000 * M ^ 4) ^ 9 ≤
      pstabK * (10000002 ^ (k + 9) * Z ^ (4 * (k + 9))) :=
    Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hb' 9).trans (hP 9 (by omega)))
  have t3 : 1000000000000000 * M ^ 6 ≤
      1000000000000000 * (10000002 ^ (k + 9) * Z ^ (4 * (k + 9))) := by
    refine Nat.mul_le_mul_left _ ?_
    calc M ^ 6 ≤ Z ^ (4 * (k + 9)) :=
          (Nat.pow_le_pow_left hM 6).trans (Nat.pow_le_pow_right hZ (by omega))
      _ ≤ 10000002 ^ (k + 9) * Z ^ (4 * (k + 9)) :=
          Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))
  have e : (pc + pstabK + 1000000000000000) * 10000002 ^ (k + 9) * Z ^ (4 * (k + 9)) =
      pc * (10000002 ^ (k + 9) * Z ^ (4 * (k + 9))) +
      pstabK * (10000002 ^ (k + 9) * Z ^ (4 * (k + 9))) +
      1000000000000000 * (10000002 ^ (k + 9) * Z ^ (4 * (k + 9))) := by ring
  rw [e]
  omega

theorem scosOwnP_le (hps : PointwiseStab) (n c : ℕ) :
    scosOwnP hps n c ≤
      ((pointwiseStabPrim hps).c + pstabK + 1000000000000000) *
        10000002 ^ ((pointwiseStabPrim hps).k + 9) *
        (2 ^ (c + 7)) ^ (4 * ((pointwiseStabPrim hps).k + 9)) *
        (n + 1) ^ ((c + 6) * (4 * ((pointwiseStabPrim hps).k + 9))) := by
  have hZ : 1 ≤ 2 ^ (c + 7) * (n + 1) ^ (c + 6) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h := scosPaste_own_aux (pointwiseStabPrim hps).c (pointwiseStabPrim hps).k
    (scosPasteM n c) _ hZ (scosPasteM_le n c)
  unfold scosOwnP scosPasteGW Prim.boundSize
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, ← pow_mul (n + 1), ← Nat.mul_assoc]

/-- The pointwise stabilizer of no points. -/
theorem scosPaste_pstabNil {m : ℕ} (G : Subgroup (Perm (Fin m))) : pointwiseStab G [] = G := by
  ext g
  simp [pointwiseStab]

/-- The answers `ws` of the map of `9` are the `encPerm (z₁⁻¹ z)`. -/
theorem scosPaste_ws {K : Subgroup (ScosPair n)} {Φ : Finset (Fin n)} {σ : Perm (Fin (n + n))}
    {zs : List (ScosPair n)} {fs ws : List Val}
    (hg : List.Forall₂ (ScosPasteGood n K Φ) zs fs)
    (h : List.Forall₂ (fun a w => ∀ (z : ScosPair n) (lv : Val),
      a = .list [encPerm (nintSum z), lv] → w = encPerm (σ * nintSum z)) fs ws) :
    ws = (zs.map fun z => σ * nintSum z).map encPerm := by
  induction hg generalizing ws with
  | nil => cases h; rfl
  | cons h1 _ ih =>
    cases h with
    | cons h3 h4 =>
      obtain ⟨lv, rfl, -⟩ := h1
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨h3 _ lv rfl, ih h4⟩

section Prog

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- The test `8`. -/
theorem scosPaste_goodTest (l : List Val) :
    FunDet 𝒫 8 (.list [.nat 0, .list l]) (boolVal (scosPasteGood (.list l)))
      (4 * (Val.list [.nat 0, .list l]).wt + 20) := by
  have d1 := Det.arg' (P := 𝒫) (vs := [.nat 0, .list l]) (rest := []) (j := 1) rfl
  have d := Det.arith' (op := .lt) (Det.nat (P := 𝒫) (env := [.list [.nat 0, .list l]]) 0)
    (Det.length d1) (z := (scosPasteGood (.list l)).toNat) (by
      simp only [scosPasteGood, GI.Machine.BinOp.eval_lt]
      by_cases h : 0 < l.length <;> simp [h])
  refine FunDet.intro scos_goodTest (d.mono ?_)
  have h1 : l.length < (Val.list l).wt := length_lt_wt_list l
  have h2 : (Val.list l).wt < (Val.list [.nat 0, .list l]).wt := wt_le_wt_list (by simp)
  have h3 : (scosPasteGood (.list l)).toNat ≤ 1 := Bool.toNat_le _
  omega

/-- The step `9`. -/
theorem scosPaste_extraStep (σ τ : Perm (Fin (n + n))) {lv : Val} (hlv : lv.wt ≤ scosW n) :
    FunDet 𝒫 9 (.list [encPerm σ, .list [encPerm τ, lv]]) (encPerm (σ * τ))
      (100000 * (n + n + 1) ^ 6) := by
  have d0 := Det.arg' (P := 𝒫) (vs := [encPerm σ, .list [encPerm τ, lv]]) (rest := []) (j := 0)
    rfl
  have d1 := Det.arg' (P := 𝒫) (vs := [encPerm σ, .list [encPerm τ, lv]]) (rest := []) (j := 1)
    rfl
  have d := Det.call (Det.mk2 d0 (Det.get' d1 (Det.nat 0) (v := encPerm τ) rfl))
    (compose_spec scos_compose σ τ)
  refine FunDet.intro scos_extraStep (d.mono ?_)
  have hQ := scosPaste_Q n
  have w1 := scosPaste_wt_perm σ
  have w2 := scosPaste_wt_perm τ
  have w3 := scosPaste_wt_perm (σ * τ)
  have wl : lv.wt ≤ 320 * (n + n + 1) ^ 6 := hlv
  have w4 := wt_list2_le (encPerm τ) lv
  have w5 := wt_list2_le (encPerm σ) (.list [encPerm τ, lv])
  have w6 := wt_list2_le (encPerm σ) (encPerm τ)
  have hp3 : permK * (n + n + 1) ^ 3 ≤ 30000 * (n + n + 1) ^ 6 :=
    Nat.mul_le_mul_left _ hQ.2.2.2.1
  generalize permK * (n + n + 1) ^ 3 = P3 at *
  generalize (n + n + 1) ^ 6 = Q at *
  omega

end Prog

end GI.Impl
