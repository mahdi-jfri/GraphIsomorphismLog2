import Workspace.Impl.TermSupFind

/-!
# T4, the Frattini correction of one generator

The proof of Lemma A.19: "For each generator `s` of `S`, Sylow conjugacy in `K` supplies
`k ∈ K` with `P^k = P^s`. Then `k s^{-1}` normalizes `P` and maps to `s^{-1} K` in `S/K`."

In our notation (`P^x = x⁻¹ P x`, with the left action of the cited `SylowConjugate`) the
function `supFixF`, on `[[gens K, p, gens P], s]`:
1. computes `s⁻¹` and the generators `s x s⁻¹` of `Q = s P s⁻¹` (`supConjF`, mapped over the
   generators of `P`);
2. asks the cited **SylowConjugate** for `g ∈ K` with `x ∈ Q ↔ g x g⁻¹ ∈ P`;
3. returns `t = g s`. It lies in `K s` and normalizes `P` (`sup_corr_normalizer`).

This is the paper's element up to inversion: the paper's `k s⁻¹` is `(s k⁻¹)⁻¹`, and `s k⁻¹`
lies in `s K = K s`. Both choices give a group `S₁` with `S₁ K = S` inside the normalizer of
`P`; we keep the form `g s ∈ K s`, which keeps `s` as the second factor.

`supFix_spec`: the result is `encPerm (g s)` with `g ∈ K` and `g s` in the normalizer of `P`.
It needs `s` to normalize `K` (so that `Q` is again a Sylow subgroup of `K`,
`sup_isSylowOf_conj`).
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### Lists of permutations related entrywise -/

/-- An entrywise relation on encoded permutations gives a list of permutations. -/
theorem sup_forall₂_perm {Q : Perm (Fin n) → Perm (Fin n) → Prop} :
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
    obtain ⟨ts, rfl, hts⟩ := sup_forall₂_perm hrest
    exact ⟨t :: ts, rfl, List.Forall₂.cons hQ hts⟩

/-- An entrywise relation that is a function. -/
theorem sup_forall₂_fun {f : Perm (Fin n) → Perm (Fin n)} :
    ∀ {ss ts : List (Perm (Fin n))}, List.Forall₂ (fun s t => t = f s) ss ts → ts = ss.map f
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h hr => by rw [h, sup_forall₂_fun hr]; rfl

/-! ### Conjugation -/

/-- `supConjF`, on `[[s, s⁻¹], y]`: `s y s⁻¹`. -/
def supConjF (cp : ℕ) : Expr :=
  .call cp (mk2 (.call cp (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.get (arg 0) (.nat 1)))

theorem supConj_spec {P : Program} {cp cj : ℕ} (hcp : P.HasAt cp (composeFuns cp))
    (hf : P.funs[cj]? = some (supConjF cp)) (s y : Perm (Fin n)) :
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
  have hn : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
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

/-- The map of `supConjF` over the generators of `P` (with the identity in front, as in
`encGroup`) is the list of generators of `s P s⁻¹`. -/
theorem supConjMap_det {P : Program} {cp cj mc : ℕ} (hcp : P.HasAt cp (composeFuns cp))
    (hf : P.funs[cj]? = some (supConjF cp)) (hmc : P.HasAt mc (mapFuns mc cj))
    (s : Perm (Fin n)) {ps : List (Perm (Fin n))} (hpl : ps.length ≤ n ^ 2) :
    FunDet P mc (.list [.list [encPerm s, encPerm s⁻¹], .list ((1 :: ps).map encPerm)])
      (.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)) (10 ^ 8 * (n + 1) ^ 8) := by
  have hm := map_spec hmc (c := .list [encPerm s, encPerm s⁻¹]) (xs := (1 :: ps).map encPerm)
    (R := fun x w => ∀ y, x = encPerm y → ∃ t, w = encPerm t ∧ t = s * y * s⁻¹)
    (B := fun _ => 10 ^ 5 * (n + 1) ^ 3) (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact FunAll.mono (supConj_spec hcp hf s y) fun w c h => ⟨fun y' hy' => ⟨_, h.1,
        by rw [encPerm_injective hy']⟩, h.2⟩)
  refine hm.mono fun w c h => ?_
  obtain ⟨ws, rfl, h2, hc⟩ := h
  obtain ⟨ts, rfl, hts⟩ := sup_forall₂_perm h2
  have hts' := sup_forall₂_fun hts
  have e : (1 :: ps).map (fun y => s * y * s⁻¹) = 1 :: ps.map fun x => s * x * s⁻¹ := by
    simp
  subst hts'
  rw [e]
  refine ⟨rfl, ?_⟩
  -- the cost
  have hl : ((1 :: ps).map encPerm).length ≤ (n + 1) ^ 2 := by
    simp only [List.length_map, List.length_cons]
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have hsum : (((1 :: ps).map encPerm).map fun _ => 10 ^ 5 * (n + 1) ^ 3).sum ≤
      (n + 1) ^ 2 * (10 ^ 5 * (n + 1) ^ 3) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hl
  have hw1 : (Val.list ((1 :: ps).map encPerm)).wt ≤ 320 * (n + 1) ^ 6 :=
    (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans (wt_encGroup_le_sq hpl)
  have hpl' : (ps.map fun x => s * x * s⁻¹).length ≤ n ^ 2 := by simpa using hpl
  have hw2 : (Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)).wt ≤ 320 * (n + 1) ^ 6 :=
    (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans (wt_encGroup_le_sq hpl')
  have hss := wt_list2_le (encPerm s) (encPerm s⁻¹)
  have h1 := wt_encPerm_le s
  have h2 := wt_encPerm_le s⁻¹
  have ha := wt_list2_le (.list [encPerm s, encPerm s⁻¹]) (.list ((1 :: ps).map encPerm))
  have hn2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e5 : (n + 1) ^ 2 * (10 ^ 5 * (n + 1) ^ 3) ≤ 10 ^ 5 * (n + 1) ^ 8 := by
    have : (n + 1) ^ 5 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    calc (n + 1) ^ 2 * (10 ^ 5 * (n + 1) ^ 3) = 10 ^ 5 * (n + 1) ^ 5 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ this
  have eL : mapK * (((1 :: ps).map encPerm).length + 1) * ((Val.list [.list [encPerm s, encPerm s⁻¹],
      .list ((1 :: ps).map encPerm)]).wt +
      (Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)).wt + 1) ≤ 10 ^ 7 * (n + 1) ^ 8 := by
    calc _ ≤ mapK * (2 * (n + 1) ^ 2) * (2000 * (n + 1) ^ 6) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by
            have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
            omega)) (by omega)
      _ = 4 * 10 ^ 6 * (n + 1) ^ 8 := by simp only [mapK]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)
  rw [e] at hc
  omega

/-- **The corrected generator** on `[[gens K, p, gens P], s]`. Environment
`[a, s⁻¹, generators of s P s⁻¹, g]`. -/
def supFixF (iv mc cp jsc : ℕ) : Expr :=
  .letE (.call iv (arg 1))
  (.letE (.call mc (mk2 (mk2 (arg 1) (.var 1)) (.get (.get (arg 0) (.nat 2)) (.nat 1))))
  (.letE (.prim jsc (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2))
      (mk2 (.get (.get (arg 0) (.nat 2)) (.nat 0)) (.var 2))))
  (.call cp (mk2 (.var 3) (arg 1)))))

/-- Where the correction and its modules sit. -/
structure SupFixAt (P : Program) (fx iv mc cj cp jsc : ℕ) (hsc : SylowConjugate) : Prop where
  fix : P.funs[fx]? = some (supFixF iv mc cp jsc)
  inv : P.HasAt iv (invFuns iv)
  map : P.HasAt mc (mapFuns mc cj)
  conj : P.funs[cj]? = some (supConjF cp)
  comp : P.HasAt cp (composeFuns cp)
  sc : P.prims[jsc]? = some (sylowConjugatePrim hsc)

/-- The cost bound of one correction. -/
def supFixCost (psc : Prim) (n : ℕ) : ℕ := psc.boundSize (10 ^ 4 * (n + 1) ^ 6) + 10 ^ 9 * (n + 1) ^ 8

/-- **One corrected generator.** If `P` is a Sylow `p`-subgroup of `K` and `s` normalizes `K`,
the result is `g s` with `g ∈ K`, and `g s` normalizes `P`. -/
theorem supFix_spec {hsc : SylowConjugate} {P : Program} {fx iv mc cj cp jsc : ℕ}
    (hP : SupFixAt P fx iv mc cj cp jsc hsc) {ks ps : List (Perm (Fin n))} (hkl : ks.length ≤ n ^ 2)
    (hpl : ps.length ≤ n ^ 2) {p : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    (hsyl : IsSylowOf p (gens ks) (gens ps)) (s : Perm (Fin n))
    (hs : ∀ k ∈ gens ks, s * k * s⁻¹ ∈ gens ks) :
    FunAll P fx (.list [.list [encGroup ks, .nat p, encGroup ps], encPerm s]) (fun w c =>
      ∃ g ∈ gens ks, w = encPerm (g * s) ∧
        g * s ∈ Subgroup.normalizer (gens ps : Set (Perm (Fin n))) ∧
        c ≤ supFixCost (sylowConjugatePrim hsc) n) := by
  set c0 := Val.list [encGroup ks, .nat p, encGroup ps] with hc0
  set a := Val.list [c0, encPerm s] with ha
  have hKw := wt_encGroup_le_sq hkl
  have hPw := wt_encGroup_le_sq hpl
  have hpl' : (ps.map fun x => s * x * s⁻¹).length ≤ n ^ 2 := by simpa using hpl
  have hQw := wt_encGroup_le_sq hpl'
  have h1 := wt_encPerm_le s
  have h2 := wt_encPerm_le s⁻¹
  have hpw := wt_nat_le p
  have hc0w := wt_list3_le (encGroup ks) (.nat p) (encGroup ps)
  have haw := wt_list2_le c0 (encPerm s)
  have hn2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn4 : (n + 1) ^ 4 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn6 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  -- `s⁻¹`
  have ds := Det.arg' (P := P) (vs := [c0, encPerm s]) (rest := []) (j := 1) rfl
  have dinv := Det.call ds (inv_spec hP.inv s)
  refine FunAll.intro hP.fix (EvalAll.letE dinv
    fun v1 c1 h1' => ?_)
  obtain ⟨rfl, hc1⟩ := h1'
  -- the generators of `Q = s P s⁻¹`
  have ds' := Det.arg' (P := P) (vs := [c0, encPerm s]) (rest := [encPerm s⁻¹]) (j := 1) rfl
  have dsi := Det.var' (P := P) (env := [a, encPerm s⁻¹]) (i := 1) (v := encPerm s⁻¹) rfl
  have d0 := Det.arg' (P := P) (vs := [c0, encPerm s]) (rest := [encPerm s⁻¹]) (j := 0) rfl
  have dPv := Det.get' d0 (Det.nat 2) (v := encGroup ps) rfl
  have dPl := Det.get' dPv (Det.nat 1) (v := .list ((1 :: ps).map encPerm)) rfl
  have dmap := Det.call (Det.mk2 (Det.mk2 ds' dsi) dPl) (supConjMap_det hP.comp hP.conj hP.map s hpl)
  refine EvalAll.letE dmap fun v2 c2 h2' => ?_
  obtain ⟨rfl, hc2⟩ := h2'
  -- Sylow conjugation
  set env := [a, encPerm s⁻¹, Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)] with henv
  have e0 := Det.arg' (P := P) (vs := [c0, encPerm s]) (rest := [encPerm s⁻¹,
    Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)]) (j := 0) rfl
  have dK := Det.get' e0 (Det.nat 0) (v := encGroup ks) rfl
  have dp := Det.get' e0 (Det.nat 1) (v := .nat p) rfl
  have dP := Det.get' e0 (Det.nat 2) (v := encGroup ps) rfl
  have dn := Det.get' dP (Det.nat 0) (v := .nat n) rfl
  have dql := Det.var' (P := P) (env := env) (i := 2)
    (v := Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)) rfl
  have dQ : Det P env (mk2 (.get (.get (arg 0) (.nat 2)) (.nat 0)) (.var 2))
      (encGroup (ps.map fun x => s * x * s⁻¹)) _ := Det.mk2 dn dql
  have hQ : gens (ps.map fun x => s * x * s⁻¹) = (gens ps).map (MulAut.conj s).toMonoidHom :=
    sup_gens_conj s ps
  have hsyl2 : IsSylowOf p (gens ks) (gens (ps.map fun x => s * x * s⁻¹)) := by
    rw [hQ]; exact sup_isSylowOf_conj hp hsyl hs
  have darg := Det.mk4 dK dp dP dQ
  have hsz : (Val.list [encGroup ks, .nat p, encGroup ps,
      encGroup (ps.map fun x => s * x * s⁻¹)]).size ≤ 10 ^ 4 * (n + 1) ^ 6 := by
    have := wt_list4_le (encGroup ks) (.nat p) (encGroup ps) (encGroup (ps.map fun x => s * x * s⁻¹))
    exact (Val.size_le_wt _).trans (by omega)
  have hbsc := (sylowConjugatePrim hsc).bound_le hsz
  refine EvalAll.letE (sylowConjugate_call hsc hP.sc darg ⟨ks, rfl, rfl⟩ ⟨ps, rfl, rfl⟩
    ⟨_, rfl, rfl⟩ hp hpn hsyl hsyl2) fun v3 c3 h3 => ?_
  obtain ⟨⟨g, hg, rfl, hconj⟩, hc3⟩ := h3
  -- the product `g s`
  have dg := Det.var' (P := P) (env := env ++ [encPerm g]) (i := 3) (v := encPerm g) rfl
  have ds3 := Det.arg' (P := P) (vs := [c0, encPerm s]) (rest := [encPerm s⁻¹,
    Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm), encPerm g]) (j := 1) rfl
  refine (Det.call (Det.mk2 dg ds3) (compose_spec hP.comp g s)).post fun c hc =>
    ⟨g, hg, rfl, sup_corr_normalizer fun x => by rw [← hQ]; exact hconj x, ?_⟩
  have hl1 : (Val.list ((1 :: ps).map encPerm)).wt < (encGroup ps).wt :=
    wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hl2 : (Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)).wt <
      (encGroup (ps.map fun x => s * x * s⁻¹)).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hl3 : (Val.list [.nat n, Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)]).wt =
      (encGroup (ps.map fun x => s * x * s⁻¹)).wt := rfl
  have hss := wt_list2_le (encPerm s) (encPerm s⁻¹)
  have hsl := wt_list2_le (.list [encPerm s, encPerm s⁻¹]) (.list ((1 :: ps).map encPerm))
  have h4 := wt_list4_le (encGroup ks) (.nat p) (encGroup ps) (encGroup (ps.map fun x => s * x * s⁻¹))
  have hnw := wt_nat_le n
  have hg1 := wt_encPerm_le g
  have hg2 := wt_encPerm_le (g * s)
  have hgs := wt_list2_le (encPerm g) (encPerm s)
  have hn3 : (n + 1) ^ 3 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hk1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hQ' : (Val.list [.nat n, Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)]).wt ≤
      320 * (n + 1) ^ 6 := hl3 ▸ hQw
  have hQ'' : (Val.list ((1 :: ps.map fun x => s * x * s⁻¹).map encPerm)).wt ≤ 320 * (n + 1) ^ 6 :=
    by omega
  have hc0' : c0.wt ≤ 2 * ((encGroup ks).wt + (Val.nat p).wt + (encGroup ps).wt) + 7 := hc0w
  have h4' : (Val.list [encGroup ks, .nat p, encGroup ps, encGroup (ps.map fun x => s * x * s⁻¹)]).wt
      ≤ 2 * ((encGroup ks).wt + (Val.nat p).wt + (encGroup ps).wt +
        320 * (n + 1) ^ 6) + 8 := by omega
  unfold supFixCost
  simp only [invK, permK] at hc1 hc
  clear dinv ds ds' dsi d0 dPv dPl dmap e0 dK dp dP dn dql dQ darg dg ds3
  omega

end GI.Impl
