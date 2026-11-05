module

public import Workspace.Impl.OutbSuppSearch

@[expose] public section

/-!
# Brute-force Frattini generator correction modulo `R`

Given a subgroup `M = gens ms` (`ms.length ≤ n²`) with `R ≤ M ≤ E_H`, coset representatives `reps`
of `R` in `E_H`, a Sylow `p`-subgroup `P = gens ps` (`ps.length ≤ 2 n²`) of `M / R`
(`OutbSylowMod p R M P`), and a generator `s` normalizing `R` and `M`:

1. `outbConjF` on `[[u, u⁻¹], y]` computes `u * y * u⁻¹`, and `outbConjMap_det` maps it over
   `(1 :: ps).map encPerm` to obtain the generators of `u P u⁻¹`.
2. `outbFixStepE` on `[[encGroup ms, encGroup ps, encPerm s], encPerm t, encPerm e]` computes
   `u = e * s`, `u⁻¹`, the generators of `u P u⁻¹`, tests `e ∈ M` (`membershipPrim`) and
   `u P u⁻¹ ≤ P` (`leFuns`), and returns `encPerm (e * s)` if both hold and `encPerm t` otherwise
   (`outbFixStep_spec`).
3. `outbFixBody` folds `outbFixStepE` over `reps.map encPerm` starting from `encPerm s`
   (`outbFix_spec`), producing `encPerm (g * s)` with `g ∈ M` and
   `g * s ∈ Subgroup.normalizer P` by `outbFixFold_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Helper lemmas for `Det` and `List.Forall₂` -/

theorem Det.ite_val {P : Program} {env : List Val} {e e1 e2 : Expr}
    {k : ℕ} {v1 v2 : Val} {ce c1 c2 : ℕ}
    (he : Det P env e (.nat k) ce)
    (h1 : Det P env e1 v1 c1) (h2 : Det P env e2 v2 c2) :
    Det P env (.ite e e1 e2) (if k = 0 then v2 else v1)
      (ce + max c1 c2 + max v1.wt v2.wt + 1) := by
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte]
    exact (Det.ite_zero he h2).mono (by omega)
  · simp only [hk, ↓reduceIte]
    exact (Det.ite_pos he hk h1).mono (by omega)

/-- An entrywise relation on encoded permutations gives a list of permutations. -/
theorem outb_forall₂_perm {Q : Perm (Fin n) → Perm (Fin n) → Prop} :
    ∀ {ss : List (Perm (Fin n))} {ws : List Val},
      List.Forall₂ (fun x w => ∀ s, x = encPerm s → ∃ t, w = encPerm t ∧ Q s t)
        (ss.map encPerm) ws → ∃ ts, ws = ts.map encPerm ∧ List.Forall₂ Q ss ts
  | [], ws, h => by
    rw [List.map_nil, List.forall₂_nil_left_iff] at h
    exact ⟨[], by rw [h]; rfl, List.Forall₂.nil⟩
  | s :: ss, ws, h => by
    rw [List.map_cons] at h
    obtain ⟨w, ws', hR, hrest, rfl⟩ := List.forall₂_cons_left_iff.mp h
    obtain ⟨t, rfl, hQ⟩ := hR s rfl
    obtain ⟨ts, rfl, hts⟩ := outb_forall₂_perm hrest
    exact ⟨t :: ts, rfl, List.Forall₂.cons hQ hts⟩

/-- An entrywise relation that is a function. -/
theorem outb_forall₂_fun {f : Perm (Fin n) → Perm (Fin n)} :
    ∀ {ss ts : List (Perm (Fin n))}, List.Forall₂ (fun s t => t = f s) ss ts → ts = ss.map f
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h hr => by rw [h, outb_forall₂_fun hr]; rfl

/-! ### Conjugation of generators -/

/-- `outbConjF`, on `[[s, s⁻¹], y]`: `s * y * s⁻¹`. -/
def outbConjF (cp : ℕ) : Expr :=
  .call cp (mk2 (.call cp (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.get (arg 0) (.nat 1)))

theorem outbConj_spec {P : Program} {cp cj : ℕ} (hcp : P.HasAt cp (composeFuns cp))
    (hf : P.funs[cj]? = some (outbConjF cp)) (s y : Perm (Fin n)) :
    FunDet P cj (.list [.list [encPerm s, encPerm s⁻¹], encPerm y]) (encPerm (s * y * s⁻¹))
      (10 ^ 5 * (n + 1) ^ 3) := by
  have h1 := wt_encPerm_le s
  have h2 := wt_encPerm_le s⁻¹
  have h3 := wt_encPerm_le y
  have h4 := wt_encPerm_le (s * y)
  have h5 := wt_encPerm_le (s * y * s⁻¹)
  have hss := wt_list2_le (encPerm s) (encPerm s⁻¹)
  have ha := wt_list2_le (.list [encPerm s, encPerm s⁻¹]) (encPerm y)
  have hb := wt_list2_le (encPerm s) (encPerm y)
  have hc := wt_list2_le (encPerm (s * y)) (encPerm s⁻¹)
  have hn : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have d0 := Det.arg' (P := P) (vs := [.list [encPerm s, encPerm s⁻¹], encPerm y]) (rest := [])
    (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [encPerm s, encPerm s⁻¹], encPerm y]) (rest := [])
    (j := 1) rfl
  have ds := Det.get' d0 (Det.nat 0) (v := encPerm s) rfl
  have dsi := Det.get' d0 (Det.nat 1) (v := encPerm s⁻¹) rfl
  have dsy := Det.call (Det.mk2 ds d1) (compose_spec hcp s y)
  have dall := Det.call (Det.mk2 dsy dsi) (compose_spec hcp (s * y) s⁻¹)
  refine FunDet.intro hf (dall.mono ?_)
  simp only [permK]
  omega

/-- Mapping `outbConjF` over `(1 :: ps).map encPerm` for `ps.length ≤ 2 * n²`. -/
theorem outbConjMap_det {P : Program} {cp cj mc : ℕ} (hcp : P.HasAt cp (composeFuns cp))
    (hf : P.funs[cj]? = some (outbConjF cp)) (hmc : P.HasAt mc (mapFuns mc cj))
    (s : Perm (Fin n)) {ps : List (Perm (Fin n))} (hpl : ps.length ≤ 2 * n ^ 2) :
    FunDet P mc (.list [.list [encPerm s, encPerm s⁻¹], .list ((1 :: ps).map encPerm)])
      (.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)) (10 ^ 8 * (n + 1) ^ 8) := by
  have hm := map_spec hmc (c := .list [encPerm s, encPerm s⁻¹]) (xs := (1 :: ps).map encPerm)
    (R := fun x w => ∀ y, x = encPerm y → ∃ t, w = encPerm t ∧ t = s * y * s⁻¹)
    (B := fun _ => 10 ^ 5 * (n + 1) ^ 3) (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact FunAll.mono (outbConj_spec hcp hf s y) fun w c h => ⟨fun y' hy' => ⟨_, h.1,
        by rw [encPerm_injective hy']⟩, h.2⟩)
  refine hm.mono fun w c h => ?_
  obtain ⟨ws, rfl, h2, hc⟩ := h
  obtain ⟨ts, rfl, hts⟩ := outb_forall₂_perm h2
  have hts' := outb_forall₂_fun hts
  have e : (1 :: ps).map (fun y => s * y * s⁻¹) = 1 :: ps.map fun x => s * x * s⁻¹ := by
    simp
  subst hts'
  rw [e]
  refine ⟨rfl, ?_⟩
  have hl : ((1 :: ps).map encPerm).length ≤ 2 * (n + 1) ^ 2 := by
    simp only [List.length_map, List.length_cons]
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have hsum : (((1 :: ps).map encPerm).map fun _ => 10 ^ 5 * (n + 1) ^ 3).sum ≤
      2 * (n + 1) ^ 2 * (10 ^ 5 * (n + 1) ^ 3) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hl
  have hw1 : (Val.list ((1 :: ps).map encPerm)).wt ≤ 640 * (n + 1) ^ 6 :=
    (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans (wt_encGroup_two_sq hpl)
  have hpl' : (ps.map fun x => s * x * s⁻¹).length ≤ 2 * n ^ 2 := by simpa using hpl
  have hw2 : (Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)).wt ≤ 640 * (n + 1) ^ 6 :=
    (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans (wt_encGroup_two_sq hpl')
  have hss := wt_list2_le (encPerm s) (encPerm s⁻¹)
  have h1 := wt_encPerm_le s
  have h2 := wt_encPerm_le s⁻¹
  have ha := wt_list2_le (.list [encPerm s, encPerm s⁻¹]) (.list ((1 :: ps).map encPerm))
  have hn2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hk1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have e5 : 2 * (n + 1) ^ 2 * (10 ^ 5 * (n + 1) ^ 3) ≤ 2 * 10 ^ 5 * (n + 1) ^ 8 := by
    have : (n + 1) ^ 5 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
    calc 2 * (n + 1) ^ 2 * (10 ^ 5 * (n + 1) ^ 3) = 2 * 10 ^ 5 * (n + 1) ^ 5 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ this
  have eL : mapK * (((1 :: ps).map encPerm).length + 1) * ((Val.list [.list [encPerm s, encPerm s⁻¹],
      .list ((1 :: ps).map encPerm)]).wt +
      (Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)).wt + 1) ≤ 10 ^ 7 * (n + 1) ^ 8 := by
    calc _ ≤ mapK * (3 * (n + 1) ^ 2) * (3000 * (n + 1) ^ 6) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 9 * 10 ^ 6 * (n + 1) ^ 8 := by simp only [mapK]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)
  rw [e] at hc
  omega

/-! ### One step of the Sylow-conjugation fold `outbFixStepE` -/

/-- One step of the brute-force Sylow-conjugation fold over `reps`, on
`[[encGroup ms, encGroup ps, encPerm s], encPerm t, encPerm e]`:
1. `.var 1 = encPerm (e * s)`
2. `.var 2 = encPerm (e * s)⁻¹`
3. `.var 3 = .list ((1 :: ps.map ((e * s) * · * (e * s)⁻¹)).map encPerm)`
4. tests `e ∈ gens ms` and `(e * s) P (e * s)⁻¹ ≤ P`; if both hold, returns `.var 1`, else `arg 1`. -/
def outbFixStepE (cp iv mc le jm : ℕ) : Expr :=
  .letE (.call cp (mk2 (arg 2) (.get (arg 0) (.nat 2))))
  (.letE (.call iv (.var 1))
  (.letE (.call mc (mk2 (mk2 (.var 1) (.var 2)) (.get (.get (arg 0) (.nat 1)) (.nat 1))))
  (.ite (.arith .mul
      (.prim jm (mk2 (.get (arg 0) (.nat 0)) (arg 2)))
      (.call le (mk2 (.get (arg 0) (.nat 1))
        (mk2 (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.var 3)))))
    (.var 1)
    (arg 1))))

/-- Cost bound of `outbFixStepE`. -/
def outbFixStepCost (pm : Prim) (n : ℕ) : ℕ :=
  (10 ^ 4 * (n + 1) ^ 6 + 1) * pm.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    10 ^ 5 * (10 ^ 4 * (n + 1) ^ 6) ^ 3

open Classical in
/-- **Specification of `outbFixStepE`**: computes `encPerm (outbFixStep (gens ms) (gens ps) s t e)`. -/
theorem outbFixStep_spec {hmem : Membership} {P : Program} {st_fx cp iv mc cj le jm : ℕ}
    (hst : P.funs[st_fx]? = some (outbFixStepE cp iv mc le jm))
    (hcp : P.HasAt cp (composeFuns cp))
    (hiv : P.HasAt iv (invFuns iv))
    (hmc : P.HasAt mc (mapFuns mc cj))
    (hcj : P.funs[cj]? = some (outbConjF cp))
    (hle : P.HasAt le (leFuns le jm))
    (hjm : P.prims[jm]? = some (membershipPrim hmem))
    {ms ps : List (Perm (Fin n))} (hml : ms.length ≤ n ^ 2) (hpl : ps.length ≤ 2 * n ^ 2)
    (s t e : Perm (Fin n)) :
    let c := Val.list [encGroup ms, encGroup ps, encPerm s]
    FunDet P st_fx (.list [c, encPerm t, encPerm e])
      (encPerm (outbFixStep (gens ms) (gens ps) s t e))
      (outbFixStepCost (membershipPrim hmem) n) := by
  intro c
  set in_v := Val.list [c, encPerm t, encPerm e] with hin_v
  set u := e * s with hu
  set ps' := ps.map fun x => u * x * u⁻¹ with hps'
  set ql := Val.list ((1 :: ps').map encPerm) with hql
  set Y := 10 ^ 4 * (n + 1) ^ 6 with hY
  have hMw := wt_encGroup_sq hml
  have hPw := wt_encGroup_two_sq hpl
  have hpl' : ps'.length ≤ 2 * n ^ 2 := by simpa [ps'] using hpl
  have hP'w := wt_encGroup_two_sq hpl'
  have hsw := wt_encPerm_le s
  have htw := wt_encPerm_le t
  have hew := wt_encPerm_le e
  have huw := wt_encPerm_le u
  have huiw := wt_encPerm_le u⁻¹
  have hcw : c.wt ≤ 2 * ((encGroup ms).wt + (encGroup ps).wt + (encPerm s).wt) + 7 :=
    wt_list3_le (encGroup ms) (encGroup ps) (encPerm s)
  have hinw : in_v.wt ≤ 2 * (c.wt + (encPerm t).wt + (encPerm e).wt) + 7 :=
    wt_list3_le c (encPerm t) (encPerm e)
  have hn12 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn36 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn_le : n ≤ (n + 1) ^ 6 := (Nat.le_succ n).trans (Nat.le_self_pow (by decide) _)
  -- step 1: `u = e * s`
  have du : Det P [in_v] (.call cp (mk2 (arg 2) (.get (arg 0) (.nat 2))))
      (encPerm u) (10 ^ 5 * (n + 1) ^ 6) := by
    have dc0 := Det.arg' (P := P) (vs := [c, encPerm t, encPerm e]) (rest := [])
      (j := 0) (v := c) rfl
    have de0 := Det.arg' (P := P) (vs := [c, encPerm t, encPerm e]) (rest := [])
      (j := 2) (v := encPerm e) rfl
    rw [← hin_v] at dc0 de0
    have ds0 := Det.get' dc0 (Det.nat 2) (v := encPerm s) rfl
    have dcall := Det.call (Det.mk2 de0 ds0) (compose_spec hcp e s)
    rw [← hu] at dcall
    refine dcall.mono ?_
    have := wt_list2_le (encPerm e) (encPerm s)
    simp only [permK]
    clear dc0 de0 ds0 dcall
    clear_value in_v c u ps' ql Y
    omega
  -- step 2: `u⁻¹`
  set env1 := [in_v, encPerm u]
  have dui : Det P env1 (.call iv (.var 1)) (encPerm u⁻¹) (2 * 10 ^ 5 * (n + 1) ^ 6) := by
    have du1 := Det.var' (P := P) (env := env1) (i := 1) (v := encPerm u) rfl
    have dcall := Det.call du1 (inv_spec hiv u)
    refine dcall.mono ?_
    simp only [invK]
    clear du du1 dcall
    clear_value in_v c u ps' ql Y env1
    omega
  -- step 3: `ql = (1 :: ps').map encPerm`
  set env2 := [in_v, encPerm u, encPerm u⁻¹]
  have dmc : Det P env2
      (.call mc (mk2 (mk2 (.var 1) (.var 2)) (.get (.get (arg 0) (.nat 1)) (.nat 1))))
      ql (2 * 10 ^ 8 * (n + 1) ^ 8) := by
    have du2 := Det.var' (P := P) (env := env2) (i := 1) (v := encPerm u) rfl
    have dui2 := Det.var' (P := P) (env := env2) (i := 2) (v := encPerm u⁻¹) rfl
    have dc2 := Det.arg' (P := P) (vs := [c, encPerm t, encPerm e])
      (rest := [encPerm u, encPerm u⁻¹]) (j := 0) (v := c) rfl
    rw [← hin_v] at dc2
    have dP2 := Det.get' dc2 (Det.nat 1) (v := encGroup ps) rfl
    have dPl2 := Det.get' dP2 (Det.nat 1) (v := .list ((1 :: ps).map encPerm)) rfl
    have dcall := Det.call (Det.mk2 (Det.mk2 du2 dui2) dPl2)
      (outbConjMap_det hcp hcj hmc u hpl)
    rw [← hps', ← hql] at dcall
    refine dcall.mono ?_
    have hPl_w : (Val.list ((1 :: ps).map encPerm)).wt ≤ 640 * (n + 1) ^ 6 :=
      (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans hPw
    have hql_w : ql.wt ≤ 640 * (n + 1) ^ 6 := by
      rw [hql]
      exact (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans hP'w
    have := wt_list2_le (encPerm u) (encPerm u⁻¹)
    have := wt_list2_le (.list [encPerm u, encPerm u⁻¹]) (.list ((1 :: ps).map encPerm))
    have hn68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
    clear du dui du2 dui2 dc2 dP2 dPl2 dcall
    clear_value in_v c u ps' ql Y env1 env2
    omega
  -- step 4: test `e ∈ gens ms` and `gens ps' ≤ gens ps`, and branch
  set env3 := [in_v, encPerm u, encPerm u⁻¹, ql]
  have dc3 := Det.arg' (P := P) (vs := [c, encPerm t, encPerm e])
    (rest := [encPerm u, encPerm u⁻¹, ql]) (j := 0) (v := c) rfl
  have dt3 := Det.arg' (P := P) (vs := [c, encPerm t, encPerm e])
    (rest := [encPerm u, encPerm u⁻¹, ql]) (j := 1) (v := encPerm t) rfl
  have de3 := Det.arg' (P := P) (vs := [c, encPerm t, encPerm e])
    (rest := [encPerm u, encPerm u⁻¹, ql]) (j := 2) (v := encPerm e) rfl
  rw [← hin_v] at dc3 dt3 de3
  have du3 := Det.var' (P := P) (env := env3) (i := 1) (v := encPerm u) rfl
  have dql3 := Det.var' (P := P) (env := env3) (i := 3) (v := ql) rfl
  have dM3 := Det.get' dc3 (Det.nat 0) (v := encGroup ms) rfl
  have dP3 := Det.get' dc3 (Det.nat 1) (v := encGroup ps) rfl
  have dn3 := Det.get' dP3 (Det.nat 0) (v := .nat n) rfl
  have dP'3 : Det P env3 (mk2 (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.var 3))
      (encGroup ps') _ := Det.mk2 dn3 dql3
  set b1 := (decide (e ∈ gens ms)).toNat
  set b2 := (decide (gens ps' ≤ gens ps)).toNat
  have dmem := member_det hmem hjm (Det.mk2 dM3 de3) ⟨ms, rfl, rfl⟩
  have hle_call := le_spec hmem hle hjm
    (⟨ps, rfl, rfl⟩ : GroupVal n (encGroup ps) (gens ps)) ps'
  have dle := Det.call (Det.mk2 dP3 dP'3) hle_call
  have dcond := Det.arith' (op := .mul) dmem dle (z := b1 * b2) rfl
  have dite := Det.ite_val dcond du3 dt3
  have hite_val : (if b1 * b2 = 0 then encPerm t else encPerm u) =
      encPerm (outbFixStep (gens ms) (gens ps) s t e) := by
    unfold outbFixStep
    have hconj : gens ps' = (gens ps).map (MulAut.conj (e * s)).toMonoidHom :=
      outb_gens_conj (e * s) ps
    rw [← hconj]
    dsimp only [b1, b2, u]
    by_cases h1 : e ∈ gens ms <;> by_cases h2 : gens ps' ≤ gens ps <;>
      simp [h1, h2]
  rw [hite_val] at dite
  have dall := Det.letE du (Det.letE dui (Det.letE dmc dite))
  refine FunDet.intro hst (dall.mono ?_)
  clear dall dite dcond dle hle_call dmem dP'3 dn3 dP3 dM3 dql3 du3 de3 dt3 dc3 dmc dui du
  have hql_w : ql.wt ≤ 640 * (n + 1) ^ 6 := by
    rw [hql]
    exact (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans hP'w
  have hnw := wt_nat_le n
  have hm_argw := wt_list2_le (encGroup ms) (encPerm e)
  have hbm1 := (membershipPrim hmem).bound_le
    (show (Val.list [encGroup ms, encPerm e]).size ≤ Y from (Val.size_le_wt _).trans (by omega))
  have hmem1 : (Val.list [encGroup ps, encPerm (1 : Perm (Fin n))]).size ≤ Y := by
    have := wt_list2_le (encGroup ps) (encPerm (1 : Perm (Fin n)))
    have := wt_encPerm_le (1 : Perm (Fin n))
    exact (Val.size_le_wt _).trans (by omega)
  have hbm2 := (membershipPrim hmem).bound_le hmem1
  have hta := wt_list2_le (encGroup ps) (encGroup ps')
  have hT : (Val.list [encGroup ps, encGroup ps']).wt ≤ Y := by omega
  have hT3 : (Val.list [encGroup ps, encGroup ps']).wt ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hT 3
  have hTm : (Val.list [encGroup ps, encGroup ps']).wt *
      (membershipPrim hmem).bound (.list [encGroup ps, encPerm (1 : Perm (Fin n))]) ≤
      Y * (membershipPrim hmem).boundSize Y := Nat.mul_le_mul hT hbm2
  have hY_le_Y3 : Y ≤ Y ^ 3 := Nat.le_self_pow (by decide) Y
  have hn6_Y : (n + 1) ^ 6 ≤ Y := by omega
  have hn6_Y3 : (n + 1) ^ 6 ≤ Y ^ 3 := hn6_Y.trans hY_le_Y3
  have hn8_Y3 : 2 * 10 ^ 8 * (n + 1) ^ 8 ≤ 2 * Y ^ 3 := by
    have h1 : 10 ^ 4 * (n + 1) ^ 4 ≤ Y := by
      rw [hY]; exact Nat.mul_le_mul_left _ hn46
    calc 2 * 10 ^ 8 * (n + 1) ^ 8 = 2 * ((10 ^ 4 * (n + 1) ^ 4) * (10 ^ 4 * (n + 1) ^ 4)) := by
          ring
      _ ≤ 2 * (Y * Y) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul h1 h1)
      _ = 2 * Y ^ 2 := by ring
      _ ≤ 2 * Y ^ 3 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) (by decide))
  have hb1_le : b1 ≤ 1 := Bool.toNat_le _
  have hb2_le : b2 ≤ 1 := Bool.toNat_le _
  have hb12_le : b1 * b2 ≤ 1 := by dsimp [b1, b2]; cases decide (e ∈ gens ms) <;> cases decide (gens ps' ≤ gens ps) <;> decide
  have hb1w := wt_boolVal_le (decide (e ∈ gens ms))
  have hb2w := wt_boolVal_le (decide (gens ps' ≤ gens ps))
  have hstep_w := wt_encPerm_le (outbFixStep (gens ms) (gens ps) s t e)
  have hmax_c : max ((encPerm u).wt + 1) (2 * in_v.wt + 1 + 5) ≤ 10 ^ 4 * (n + 1) ^ 6 := by
    apply max_le <;> omega
  have hmax_w : max (encPerm u).wt (encPerm t).wt ≤ 4 * (n + 1) ^ 2 := by
    apply max_le <;> omega
  have hr1 : (Val.list [.nat n, .list ((1 :: ps').map encPerm)]).wt = (encGroup ps').wt := rfl
  have hr2 : (Val.list [.nat n, ql]).wt = (encGroup ps').wt := rfl
  have hgoal_eq : outbFixStepCost (membershipPrim hmem) n =
      Y * (membershipPrim hmem).boundSize Y + (membershipPrim hmem).boundSize Y +
        10 ^ 5 * Y ^ 3 := by
    simp only [outbFixStepCost, ← hY]; ring
  rw [hgoal_eq]
  clear hgoal_eq hite_val
  clear_value Y b1 b2 ql ps' u in_v c env1 env2 env3
  omega

/-! ### The full generator correction `outbFixBody` -/

/-- **Generator correction `outbFixBody`** on
`[[encGroup ms, encGroup ps, .list (reps.map encPerm)], encPerm s]`:
folds `outbFixStepE` over `reps.map encPerm` starting from `encPerm s`. -/
def outbFixBody (fd : ℕ) : Expr :=
  .call fd (mk3
    (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (arg 1))
    (.get (arg 0) (.nat 2))
    (arg 1))

/-- Where the generator correction and its modules sit. -/
structure OutbFixAt (P : Program) (fx fd st_fx cp iv mc cj le jm : ℕ)
    (hmem : Membership) : Prop where
  fix : P.funs[fx]? = some (outbFixBody fd)
  fold : P.HasAt fd (foldlFuns fd st_fx)
  step : P.funs[st_fx]? = some (outbFixStepE cp iv mc le jm)
  comp : P.HasAt cp (composeFuns cp)
  inv : P.HasAt iv (invFuns iv)
  map : P.HasAt mc (mapFuns mc cj)
  conj : P.funs[cj]? = some (outbConjF cp)
  le : P.HasAt le (leFuns le jm)
  mem : P.prims[jm]? = some (membershipPrim hmem)

/-- Cost bound of `outbFixBody` for `reps` of length `m`. -/
def outbFixCost (pm : Prim) (n m : ℕ) : ℕ :=
  (m + 1) * outbFixStepCost pm n + 10 ^ 7 * (m + 1) ^ 3 * (n + 1) ^ 6

/-- **Specification of `outbFixBody`**: when `OutbSylowMod p R (gens ms) (gens ps)` holds and `s`
normalizes `R` and `gens ms`, returns `encPerm (g * s)` with `g ∈ gens ms` and `g * s` normalizing
`gens ps`. -/
theorem outbFix_spec {hmem : Membership} {P : Program}
    {fx fd st_fx cp iv mc cj le jm : ℕ}
    (hP : OutbFixAt P fx fd st_fx cp iv mc cj le jm hmem)
    {R E_H : Subgroup (Perm (Fin n))} {ms ps reps : List (Perm (Fin n))}
    [(R.subgroupOf (gens ms)).Normal]
    (hME : gens ms ≤ E_H) (hml : ms.length ≤ n ^ 2) (hpl : ps.length ≤ 2 * n ^ 2)
    (hcov : ∀ x ∈ E_H, TmRpCov R reps x)
    {p : ℕ} (hp : p.Prime) (hsyl : OutbSylowMod p R (gens ms) (gens ps))
    (s : Perm (Fin n))
    (hsR_inv : ∀ r ∈ R, s⁻¹ * r * s ∈ R)
    (hsM : ∀ m ∈ gens ms, s * m * s⁻¹ ∈ gens ms) :
    FunAll P fx (.list [.list [encGroup ms, encGroup ps, .list (reps.map encPerm)], encPerm s])
      (fun w cost => ∃ g ∈ gens ms, w = encPerm (g * s) ∧
        g * s ∈ Subgroup.normalizer (gens ps : Set (Perm (Fin n))) ∧
        cost ≤ outbFixCost (membershipPrim hmem) n reps.length) := by
  set xs := reps.map encPerm with hxs
  set c_map := Val.list [encGroup ms, encGroup ps, .list xs] with hcmap
  set c_fold := Val.list [encGroup ms, encGroup ps, encPerm s] with hcfold
  set S_cost := outbFixStepCost (membershipPrim hmem) n with hS_cost
  -- fold invariant: partial fold over `reps.take j`
  have hfold := foldl_spec hP.fold (c := c_fold) (xs := xs) (acc0 := encPerm s)
    (Inv := fun j w => w = encPerm ((reps.take j).foldl (outbFixStep (gens ms) (gens ps) s) s))
    (M := 4 * (n + 1) ^ 2) (B := fun _ => S_cost)
    rfl
    (fun j w _ hw => by rw [hw]; exact wt_encPerm_le _)
    (fun j w hj hw => by
      have hj' : j < reps.length := by simpa [hxs] using hj
      have hx : xs[j] = encPerm (reps[j]'hj') := by simp only [hxs, List.getElem_map]
      rw [hw, hx]
      refine FunAll.mono
        (outbFixStep_spec hP.step hP.comp hP.inv hP.map hP.conj hP.le hP.mem hml hpl s
          ((reps.take j).foldl (outbFixStep (gens ms) (gens ps) s) s) (reps[j]'hj'))
        fun w' cost' hw' => ⟨?_, hw'.2⟩
      rw [hw'.1, List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        List.foldl_append]
      rfl)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hfold
  have hxs_len : xs.length = reps.length := by simp [hxs]
  rw [hxs_len, List.take_length] at hfold
  -- call `fd` from `outbFixBody`
  have d0 := Det.arg' (P := P) (vs := [c_map, encPerm s]) (rest := [])
    (j := 0) (v := c_map) rfl
  have d1 := Det.arg' (P := P) (vs := [c_map, encPerm s]) (rest := [])
    (j := 1) (v := encPerm s) rfl
  have dc0 := Det.get' d0 (Det.nat 0) (v := encGroup ms) rfl
  have dc1 := Det.get' d0 (Det.nat 1) (v := encGroup ps) rfl
  have dc2 := Det.get' d0 (Det.nat 2) (v := .list xs) rfl
  have dcfold := Det.mk3 dc0 dc1 d1
  rw [← hcfold] at dcfold
  have darg := Det.mk3 dcfold dc2 d1
  refine FunAll.intro hP.fix (EvalAll.call_funAll darg fun v_arg ca hv_arg => ?_)
  obtain ⟨rfl, hca⟩ := hv_arg
  refine hfold.mono fun w cw hw => ?_
  obtain ⟨g, hg, hg_eq, hgn⟩ :=
    outbFixFold_spec hp hME hcov hsyl hsR_inv hsM
  have hw_eq : w = encPerm (g * s) := by
    rw [hw.1, ← outbFixFold, hg_eq]
  refine ⟨g, hg, hw_eq, hg_eq ▸ hgn, ?_⟩
  have hMw := wt_encGroup_sq hml
  have hPw := wt_encGroup_two_sq hpl
  have hsw := wt_encPerm_le s
  have hww : w.wt ≤ 4 * (n + 1) ^ 2 := by rw [hw_eq]; exact wt_encPerm_le (g * s)
  have hrepw : (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 :=
    outb_wt_reps_le reps
  have hcmap_w : c_map.wt ≤ 2 * ((encGroup ms).wt + (encGroup ps).wt + (Val.list xs).wt) + 7 :=
    wt_list3_le (encGroup ms) (encGroup ps) (.list xs)
  have hcfold_w : c_fold.wt ≤ 2 * ((encGroup ms).wt + (encGroup ps).wt + (encPerm s).wt) + 7 :=
    wt_list3_le (encGroup ms) (encGroup ps) (encPerm s)
  have hin_w := wt_list2_le c_map (encPerm s)
  have harg_w := wt_list3_le c_fold (.list xs) (encPerm s)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  have hn16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hm12 : 1 ≤ (reps.length + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hm13 : 1 ≤ (reps.length + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hm23 : (reps.length + 1) ^ 2 ≤ (reps.length + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  set Z2 := (reps.length + 1) ^ 2 * (n + 1) ^ 6 with hZ2
  set Z3 := (reps.length + 1) ^ 3 * (n + 1) ^ 6 with hZ3
  have hZ2_pos : 1 ≤ Z2 := Nat.mul_pos hm12 hn16
  have hZ3_pos : 1 ≤ Z3 := Nat.mul_pos hm13 hn16
  have hZ2_Z3 : Z2 ≤ Z3 := Nat.mul_le_mul_right _ hm23
  have hn6_Z2 : (n + 1) ^ 6 ≤ Z2 := by
    calc (n + 1) ^ 6 = 1 * (n + 1) ^ 6 := (one_mul _).symm
      _ ≤ Z2 := Nat.mul_le_mul_right _ hm12
  have hm_Z2 : reps.length ≤ Z2 := by
    have : reps.length ≤ (reps.length + 1) ^ 2 :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
    calc reps.length ≤ (reps.length + 1) ^ 2 * 1 := by omega
      _ ≤ Z2 := Nat.mul_le_mul_left _ hn16
  have hrepw_Z2 : (Val.list xs).wt ≤ 13 * Z2 := by
    calc (Val.list xs).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 := hrepw
      _ ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 6 := Nat.mul_le_mul_left _ hn26
      _ = 13 * Z2 := by rw [hZ2]; ring
  have htot_Z2 : (Val.list [c_fold, .list xs, encPerm s]).wt +
      reps.length + 4 * (n + 1) ^ 2 + 1 ≤ 4000 * Z2 := by
    clear d0 d1 dc0 dc1 dc2 dcfold darg hfold hcmap hcfold
    clear_value Z2 Z3 c_map c_fold xs S_cost
    omega
  have hL : loopModK * (reps.length + 1) *
      ((Val.list [c_fold, .list xs, encPerm s]).wt + reps.length + 4 * (n + 1) ^ 2 + 1) ≤
      4 * 10 ^ 6 * Z3 := by
    calc loopModK * (reps.length + 1) *
        ((Val.list [c_fold, .list xs, encPerm s]).wt + reps.length + 4 * (n + 1) ^ 2 + 1) ≤
        loopModK * (reps.length + 1) * (4000 * Z2) :=
          Nat.mul_le_mul_left _ htot_Z2
      _ = 4 * 10 ^ 6 * Z3 := by simp only [loopModK, hZ2, hZ3]; ring
  have hgoal_eq : outbFixCost (membershipPrim hmem) n reps.length =
      reps.length * S_cost + S_cost + 10 ^ 7 * Z3 := by
    simp only [outbFixCost, hS_cost, hZ3]; ring
  rw [hgoal_eq]
  clear d0 d1 dc0 dc1 dc2 dcfold darg hfold hcmap hcfold htot_Z2 hgoal_eq
  clear_value Z2 Z3 c_map c_fold xs S_cost
  omega

end GI.Impl
