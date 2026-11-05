module

public import Workspace.Impl.TermJProgYg3

@[expose] public section

/-!
# The local `N*`-stabilizers of one row (program)

`Aut_J(x)` uses, for every row `a`, generators of `Aut_{N*}(x_a) = Aut_N(x_a) ∩ N*`
(`tmJ_autJ_gens`, hypothesis `hns`). The table stores generators `gs` of `Aut_N(x_a)` at the
diagonal entry of row `a`. One normalized intersection with `⟨σS⟩ = N*` gives generators `hs`
of the intersection (`N*` is normal in `N`, so `Aut_N(x_a)` normalizes it). The program then
returns the local elements `(s⁻¹ at a; 1)` for `s ∈ hs`.

This is the paper's step (proof of Theorem A.23: "use the local \(N^*\)-stabilizers", and "The subgroups \(\Aut_N(z_a)\) and
\(\Aut_{N^*}(z_a)\) are likewise normalized-subgroup intersections of the stored stabilizers").
The rows play the role of the representatives `z_a`, as in the rest of the `J`-step.

`tmJ_nsRow_spec`: on `[[us, lc, σS], a]` the program returns
`tmJPermsVal (hs.map fun s => tmJLoc a s⁻¹)` with `⟨hs⟩ = ⟨gs⟩ ⊓ ⟨σS⟩`.
-/

namespace GI.Impl

open GI.Lang GI.Assembly Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens NormalizedIntersection)

variable {m q : ℕ}

/-- On `[[us, lc, σS], a]`: intersect the stored `Aut_N(x_a)` with `⟨σS⟩`, then take the local
elements at row `a`. -/
def tmJNsRowF (ni mp : ℕ) : Expr :=
  .letE (.prim ni (mk2 (.get (.get (.get (arg 0) (.nat 0))
      (.arith .add (.arith .mul (arg 1) (.arith .mul (.nat 2)
        (.get (.get (arg 0) (.nat 1)) (.nat 2)))) (arg 1))) (.nat 1))
      (.get (arg 0) (.nat 2))))
    (.call mp (mk2 (mk2 (.get (arg 0) (.nat 1)) (arg 1)) (.var 1)))

/-- The cost of one row besides the intersection, in `V = wt us + wt σS + (m + 1) (q + 1)`. -/
def tmJNsRowK (V : ℕ) : ℕ := 10 ^ 16 * V ^ 12

theorem tmJ_nsRow_spec (hni : NormalizedIntersection) {P : Program}
    {f ni mp locA dsA rg tbA tbe pr prg prt prte : ℕ}
    (hf : P.funs[f]? = some (tmJNsRowF ni mp))
    (hj : P.prims[ni]? = some (normalizedIntersectionPrim hni))
    (hmp : P.HasAt mp (mapFuns mp locA))
    (hlocA : P.funs[locA]? = some (tmJLocAF dsA pr))
    (hds : P.funs[dsA]? = some (tmJDsAF rg tbA)) (hrg : P.HasAt rg (rangeFuns rg))
    (htb : P.HasAt tbA (mapFuns tbA tbe)) (htbe : P.funs[tbe]? = some tmJDsAEF)
    (hpr : TmJPairAt P pr prg prt prte) (us : List Val) (σS : List (Perm (Fin m))) (a : Fin q)
    {r : Perm (Fin m)} {gs : List (Perm (Fin m))}
    (hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs]))
    (hnorm : GI.Multicoset.Normalizes (gens gs) (gens σS)) :
    FunAll P f (.list [.list [.list us, tmJLocCtx m q, encGroup σS], .nat a]) (fun out cost =>
      (∃ hs : List (Perm (Fin m)), out = tmJPermsVal (hs.map fun s => tmJLoc a s⁻¹) ∧
        gens hs = gens gs ⊓ gens σS ∧ hs.length ≤ m ^ 2) ∧
      cost ≤ (normalizedIntersectionPrim hni).bound (.list [encGroup gs, encGroup σS]) +
        tmJNsRowK ((Val.list us).wt + (encGroup σS).wt + (m + 1) * (q + 1))) := by
  refine FunAll.intro hf ?_
  unfold tmJNsRowF
  set V := (Val.list us).wt + (encGroup σS).wt + (m + 1) * (q + 1) with hV
  set I := Val.list [.list [.list us, tmJLocCtx m q, encGroup σS], .nat a]
  have d0 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q, encGroup σS], .nat a])
    (rest := []) (j := 0) (v := .list [.list us, tmJLocCtx m q, encGroup σS]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q, encGroup σS], .nat a])
    (rest := []) (j := 1) (v := .nat a) rfl
  have dus := Det.get' d0 (Det.nat 0) (vs := [.list us, tmJLocCtx m q, encGroup σS])
    (v := .list us) rfl
  have dlc := Det.get' d0 (Det.nat 1) (vs := [.list us, tmJLocCtx m q, encGroup σS])
    (v := tmJLocCtx m q) rfl
  have dS := Det.get' d0 (Det.nat 2) (vs := [.list us, tmJLocCtx m q, encGroup σS])
    (v := encGroup σS) rfl
  have dq := Det.get' dlc (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have d2q := Det.arith' (op := .mul) (Det.nat 2) dq (z := 2 * q) rfl
  have dmul := Det.arith' (op := .mul) d1 d2q (z := (a : ℕ) * (2 * q)) rfl
  have didx := Det.arith' (op := .add) dmul d1 (z := (a : ℕ) * (2 * q) + a) rfl
  have de := Det.get' dus didx hu
  have dg := Det.get' de (Det.nat 1) (vs := [encPerm r, encGroup gs]) (v := encGroup gs) rfl
  refine EvalAll.letE (normalizedIntersection_call hni hj (Det.mk2 dg dS) ⟨gs, rfl, rfl⟩
    ⟨σS, rfl, rfl⟩ hnorm) fun w cw hw => ?_
  obtain ⟨⟨hs, rfl, hl, hg⟩, hcw⟩ := hw
  -- the body, in the environment extended by the generators
  have e0 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q, encGroup σS], .nat a])
    (rest := [.list (hs.map encPerm)]) (j := 0)
    (v := .list [.list us, tmJLocCtx m q, encGroup σS]) rfl
  have e1 := Det.arg' (P := P) (vs := [.list [.list us, tmJLocCtx m q, encGroup σS], .nat a])
    (rest := [.list (hs.map encPerm)]) (j := 1) (v := .nat a) rfl
  have elc := Det.get' e0 (Det.nat 1) (vs := [.list us, tmJLocCtx m q, encGroup σS])
    (v := tmJLocCtx m q) rfl
  have ev := Det.var' (P := P) (env := [I, .list (hs.map encPerm)]) (i := 1)
    (v := .list (hs.map encPerm)) rfl
  have hM := mapList_spec hmp hs encPerm
    (fun s => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc a s⁻¹)))
    (c := .list [tmJLocCtx m q, .nat a]) (fun s _ s' _ he => by rw [encPerm_injective he])
    (fun s _ => tmJ_locA_spec hlocA hds hrg htb htbe hpr a s)
  have dall := Det.call (Det.mk2 (Det.mk2 elc e1) ev) hM
  have hval : Val.list (hs.map fun s =>
      encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) (tmJLoc a s⁻¹))) =
      tmJPermsVal (hs.map fun s => tmJLoc a s⁻¹) := by
    simp only [tmJPermsVal, List.map_map, Function.comp_def]
  rw [hval] at dall
  refine dall.post fun c hc => ⟨⟨hs, rfl, hg, hl⟩, ?_⟩
  clear_value V
  clear dall hM ev elc e1 e0 dg de didx dmul d2q dq dS dlc dus d1 d0
  -- the cost
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by
    have e : (m + 1) * (q + 1) = m * q + m + q + 1 := by ring
    omega
  have hV1 : (m + 1) * (q + 1) ≤ V := by omega
  have hY1 : 1 ≤ V := by omega
  have hpow : ∀ i j, i ≤ j → V ^ i ≤ V ^ j := fun i j h => Nat.pow_le_pow_right hY1 h
  have h1 := hpow 1 12 (by norm_num)
  simp only [pow_one] at h1
  have h2 := hpow 2 12 (by norm_num)
  have h3 := hpow 3 12 (by norm_num)
  have h4 := hpow 4 12 (by norm_num)
  have h6 := hpow 6 12 (by norm_num)
  have hW2 : ((m + 1) * (q + 1)) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hV1 2
  have hW8 : ((m + 1) * (q + 1)) ^ 8 ≤ V ^ 8 := Nat.pow_le_pow_left hV1 8
  have hm6 : (m + 1) ^ 6 ≤ V ^ 6 := Nat.pow_le_pow_left (hm1.trans hV1) 6
  have hmq2 : (m * q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (hmq.trans hV1) 2
  have hWW : (m + 1) * (q + 1) ≤ ((m + 1) * (q + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  have ha := a.2
  have ha2 : (a : ℕ) * (2 * q) ≤ 2 * V ^ 2 := by
    have : (a : ℕ) * (2 * q) ≤ (q + 1) * (2 * (q + 1)) := Nat.mul_le_mul (by omega) (by omega)
    have e : (q + 1) * (2 * (q + 1)) = 2 * (q + 1) ^ 2 := by ring
    have : (q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (hq1.trans hV1) 2
    omega
  have he : (Val.list [encPerm r, encGroup gs]).wt < (Val.list us).wt :=
    wt_le_wt_list (List.mem_of_getElem? hu)
  have hgw : (encGroup gs).wt < (Val.list [encPerm r, encGroup gs]).wt := wt_le_wt_list (by simp)
  have hmm : m ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hlen : hs.length ≤ V ^ 2 := hl.trans hmm
  have wc := wt_tmJLocCtx_le m q
  have wa := wt_nat_le a
  have wq := wt_nat_le q
  have w2q := wt_nat_le (2 * q)
  have w2 := wt_nat_le 2
  have wmul := wt_nat_le ((a : ℕ) * (2 * q))
  have widx := wt_nat_le ((a : ℕ) * (2 * q) + a)
  have w3 := wt_list3_le (.list us) (tmJLocCtx m q) (encGroup σS)
  have win := wt_list2_le (.list [.list us, tmJLocCtx m q, encGroup σS]) (.nat a)
  have wgS := wt_list2_le (encGroup gs) (encGroup σS)
  have wca := wt_list2_le (tmJLocCtx m q) (.nat a)
  have whs := wt_list_le (hs.map encPerm)
  have hsum : ((hs.map encPerm).map Val.wt).sum ≤ hs.length * (4 * (m + 1) ^ 2) := by
    have := List.sum_le_card_nsmul ((hs.map encPerm).map Val.wt) (4 * (m + 1) ^ 2) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact wt_encPerm_le s)
    simpa using this
  have hsum' : hs.length * (4 * (m + 1) ^ 2) ≤ V ^ 2 * (4 * V ^ 2) :=
    Nat.mul_le_mul hlen (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hm1.trans hV1) 2))
  have e4 : V ^ 2 * (4 * V ^ 2) = 4 * V ^ 4 := by ring
  simp only [List.length_map] at whs
  have wcL := wt_list2_le (.list [tmJLocCtx m q, .nat a]) (.list (hs.map encPerm))
  have wres := wt_tmJPermsVal_le (hs.map fun s => tmJLoc (q := q) a s⁻¹)
  simp only [List.length_map] at wres
  have P0 : hs.length * (8 * (m * q + 1) ^ 2 + 1) ≤ V ^ 2 * (9 * V ^ 2) :=
    Nat.mul_le_mul hlen (by omega)
  have e0 : V ^ 2 * (9 * V ^ 2) = 9 * V ^ 4 := by ring
  have P1 : hs.length * tmJLocK ((m + 1) * (q + 1)) ≤ 10 ^ 14 * V ^ 10 := by
    unfold tmJLocK
    have : hs.length * (10 ^ 14 * ((m + 1) * (q + 1)) ^ 8) ≤ V ^ 2 * (10 ^ 14 * V ^ 8) :=
      Nat.mul_le_mul hlen (Nat.mul_le_mul_left _ hW8)
    have e : V ^ 2 * (10 ^ 14 * V ^ 8) = 10 ^ 14 * V ^ 10 := by ring
    omega
  have h10 := hpow 10 12 (by norm_num)
  have h0 := hpow 0 12 (by norm_num)
  simp only [pow_zero] at h0
  have P2 : mapK * (hs.length + 1) * ((Val.list [Val.list [tmJLocCtx m q, .nat a],
      .list (hs.map encPerm)]).wt + (tmJPermsVal (hs.map fun s => tmJLoc (q := q) a s⁻¹)).wt + 1)
      ≤ 1000 * (2 * V ^ 2) * (300 * V ^ 6) := by
    unfold mapK
    have hGw : (Val.list (hs.map encPerm)).wt ≤ 13 * (m + 1) ^ 6 :=
      GensVal.wt_le (G := gens gs ⊓ gens σS) ⟨hs, rfl, hl, hg⟩
    have := hpow 2 6 (by norm_num)
    have := hpow 4 6 (by norm_num)
    have := hpow 0 2 (by norm_num); simp at this
    have hlc : (tmJLocCtx m q).wt ≤ 40 * V ^ 2 := wc.trans (Nat.mul_le_mul_left _ hW2)
    have hy : (Val.list (hs.map encPerm)).wt ≤ 13 * V ^ 6 := hGw.trans (Nat.mul_le_mul_left _ hm6)
    have hz := wt_list2_le (.list [tmJLocCtx m q, .nat a]) (.list (hs.map encPerm))
    have hx := wt_list2_le (tmJLocCtx m q) (.nat a)
    have hV6 := hpow 1 6 (by norm_num)
    have hV26 := hpow 2 6 (by norm_num)
    have hV46 := hpow 4 6 (by norm_num)
    have hV06 := hpow 0 6 (by norm_num)
    simp only [pow_one, pow_zero] at hV6 hV06
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e2 : 1000 * (2 * V ^ 2) * (300 * V ^ 6) = 600000 * V ^ 8 := by ring
  have h8 := hpow 8 12 (by norm_num)
  unfold tmJNsRowK
  omega

/-! ### All rows -/

/-- A list related entrywise to `0, …, q - 1` is a tabulation. -/
theorem tmJNs_extract {β : Type} {R : Fin q → β → Prop} {ws : List β}
    (h : List.Forall₂ R (List.finRange q) ws) :
    ∃ F : Fin q → β, ws = (List.finRange q).map F ∧ ∀ i, R i (F i) := by
  have hl : ws.length = q := by rw [← h.length_eq, List.length_finRange]
  refine ⟨fun i => ws.get ⟨i, by omega⟩, ?_, fun i => ?_⟩
  · apply List.ext_get (by simp [hl])
    intro n h1 h2
    simp
  · have := (List.forall₂_iff_get.1 h).2 i (by simp) (by omega)
    simpa using this

/-- The local `N*`-stabilizers of all rows. -/
def tmJNsList (hsA : Fin q → List (Perm (Fin m))) : List (Perm (Fin m × Fin q)) :=
  ((List.finRange q).map fun a => (hsA a).map fun s => tmJLoc a s⁻¹).flatten

/-- On `[us, lc, σS]`: map the row program over `0, …, q - 1` and flatten. -/
def tmJNsF (rg mpR fl : ℕ) : Expr :=
  .call fl (.call mpR (mk2 (.var 0) (.call rg (.get (arg 1) (.nat 2)))))

/-- The cost of all rows besides the intersections. -/
def tmJNsK (V : ℕ) : ℕ := 10 ^ 18 * V ^ 16

structure TmJNsAt (P : Program) (f rg mpR row ni mp locA dsA tbA tbe pr prg prt prte fl app : ℕ) :
    Prop where
  hf : P.funs[f]? = some (tmJNsF rg mpR fl)
  hrg : P.HasAt rg (rangeFuns rg)
  hmpR : P.HasAt mpR (mapFuns mpR row)
  hrow : P.funs[row]? = some (tmJNsRowF ni mp)
  hmp : P.HasAt mp (mapFuns mp locA)
  hlocA : P.funs[locA]? = some (tmJLocAF dsA pr)
  hds : P.funs[dsA]? = some (tmJDsAF rg tbA)
  htb : P.HasAt tbA (mapFuns tbA tbe)
  htbe : P.funs[tbe]? = some tmJDsAEF
  hpr : TmJPairAt P pr prg prt prte
  hfl : P.funs[fl]? = some (tmJFlatF (fl + 1))
  hflF : P.HasAt (fl + 1) (foldlFuns (fl + 1) (fl + 4))
  hst : P.funs[fl + 4]? = some (tmJFlatStepF app)
  happ : P.HasAt app (appendFuns app)

/-- **The local `N*`-stabilizers of all rows.** -/
theorem tmJ_ns_spec (hni : NormalizedIntersection) {P : Program}
    {f rg mpR row ni mp locA dsA tbA tbe pr prg prt prte fl app : ℕ}
    (hA : TmJNsAt P f rg mpR row ni mp locA dsA tbA tbe pr prg prt prte fl app)
    (hj : P.prims[ni]? = some (normalizedIntersectionPrim hni))
    (O : Fin q → Fin q → Option (Perm (Fin m) × List (Perm (Fin m)))) (us : List Val)
    (hus : ∀ a a' : Fin q, us[(a : ℕ) * (2 * q) + a']? = some (tmJEntVal (O a a')))
    (σS : List (Perm (Fin m)))
    (hloc : ∀ a, ∃ r gs, O a a = some (r, gs) ∧ GI.Multicoset.Normalizes (gens gs) (gens σS)) :
    FunAll P f (.list [.list us, tmJLocCtx m q, encGroup σS]) (fun out cost =>
      (∃ hsA : Fin q → List (Perm (Fin m)), out = tmJPermsVal (tmJNsList hsA) ∧
        ∀ a r gs, O a a = some (r, gs) → gens (hsA a) = gens gs ⊓ gens σS) ∧
      cost ≤ ((Val.list us).wt + (encGroup σS).wt + (m + 1) * (q + 1)) *
          (normalizedIntersectionPrim hni).boundSize
            (2 * ((Val.list us).wt + (encGroup σS).wt + (m + 1) * (q + 1)) + 6) +
        tmJNsK ((Val.list us).wt + (encGroup σS).wt + (m + 1) * (q + 1))) := by
  refine FunAll.intro hA.hf ?_
  unfold tmJNsF
  set V := (Val.list us).wt + (encGroup σS).wt + (m + 1) * (q + 1) with hV
  set c := Val.list [.list us, tmJLocCtx m q, encGroup σS] with hc
  set BS := (normalizedIntersectionPrim hni).boundSize (2 * V + 6)
  clear_value V
  have hm1 : m + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hq1 : q + 1 ≤ (m + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hmq : m * q + 1 ≤ (m + 1) * (q + 1) := by
    have e : (m + 1) * (q + 1) = m * q + m + q + 1 := by ring
    omega
  have hV1 : (m + 1) * (q + 1) ≤ V := by omega
  have hY1 : 1 ≤ V := by omega
  have hpow : ∀ i j, i ≤ j → V ^ i ≤ V ^ j := fun i j h => Nat.pow_le_pow_right hY1 h
  have hmq2 : (m * q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (hmq.trans hV1) 2
  have hmm : m ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (by omega) 2
  -- the rows
  have hrowS : ∀ x ∈ (List.finRange q).map (fun i : Fin q => Val.nat (i : ℕ)),
      FunAll P row (.list [c, x]) (fun w cost =>
        (∀ i : Fin q, x = .nat i → ∃ hs : List (Perm (Fin m)),
          w = tmJPermsVal (hs.map fun s => tmJLoc i s⁻¹) ∧ hs.length ≤ m ^ 2 ∧
          ∀ r gs, O i i = some (r, gs) → gens hs = gens gs ⊓ gens σS) ∧
        cost ≤ BS + tmJNsRowK V) := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨r, gs, hO, hn⟩ := hloc a
    have hu : us[(a : ℕ) * (2 * q) + a]? = some (.list [encPerm r, encGroup gs]) := by
      rw [hus a a, hO]; rfl
    have he : (Val.list [encPerm r, encGroup gs]).wt < (Val.list us).wt :=
      wt_le_wt_list (List.mem_of_getElem? hu)
    have hgw : (encGroup gs).wt < (Val.list [encPerm r, encGroup gs]).wt :=
      wt_le_wt_list (by simp)
    have hsz : (Val.list [encGroup gs, encGroup σS]).size ≤ 2 * V + 6 := by
      have := wt_list2_le (encGroup gs) (encGroup σS)
      exact (Val.size_le_wt _).trans (by omega)
    have hb := (normalizedIntersectionPrim hni).bound_le hsz
    refine (tmJ_nsRow_spec hni hA.hrow hj hA.hmp hA.hlocA hA.hds hA.hrg hA.htb hA.htbe hA.hpr
      us σS a hu hn).mono fun w cost hw => ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨⟨hs, hws, hg, hl⟩, -⟩ := hw
      have hia : i = a := Fin.ext (by simpa using hi.symm)
      subst hia
      refine ⟨hs, hws, hl, fun r' gs' hO' => ?_⟩
      rw [hO] at hO'
      simp only [Option.some.injEq, Prod.mk.injEq] at hO'
      obtain ⟨-, rfl⟩ := hO'
      exact hg
    · have := hw.2
      simp only [← hV] at this
      omega
  have hM := map_spec hA.hmpR hrowS
  -- the arguments
  have dc := Det.var' (P := P) (env := [c]) (i := 0) (v := c) rfl
  have d1 := Det.arg' (P := P) (vs := [.list us, tmJLocCtx m q, encGroup σS]) (rest := [])
    (j := 1) (v := tmJLocCtx m q) rfl
  have dq := Det.get' d1 (Det.nat 2) (vs := [encPerm (1 : Perm (Fin m)),
    encPerm (1 : Perm (Fin q)), .nat q, .nat m]) (v := .nat q) rfl
  have dr := Det.call dq (tmJ_range_det hA.hrg q)
  have dargs := Det.mk2 dc dr
  -- weights
  have wlc := wt_tmJLocCtx_le m q
  have w3 := wt_list3_le (.list us) (tmJLocCtx m q) (encGroup σS)
  have wid := wt_ids_le q
  have wq := wt_nat_le q
  have hW2 : ((m + 1) * (q + 1)) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left hV1 2
  have hq2 : (q + 1) ^ 2 ≤ V ^ 2 := Nat.pow_le_pow_left (hq1.trans hV1) 2
  have hq3 : (q + 1) ^ 3 ≤ V ^ 3 := Nat.pow_le_pow_left (hq1.trans hV1) 3
  have wca := wt_list2_le c (encFun fun i : Fin q => (i : ℕ))
  have hrowW : ∀ (a : Fin q) (hs : List (Perm (Fin m))), hs.length ≤ m ^ 2 →
      (tmJPermsVal (hs.map fun s => tmJLoc (q := q) a s⁻¹)).wt ≤ 13 * V ^ 4 := by
    intro a hs hl
    have w := wt_tmJPermsVal_le (hs.map fun s => tmJLoc (q := q) a s⁻¹)
    simp only [List.length_map] at w
    have : hs.length * (8 * (m * q + 1) ^ 2 + 1) ≤ V ^ 2 * (9 * V ^ 2) :=
      Nat.mul_le_mul (hl.trans hmm) (by have := hpow 0 2 (by norm_num); simp at this; omega)
    have e : V ^ 2 * (9 * V ^ 2) = 9 * V ^ 4 := by ring
    have := hpow 0 4 (by norm_num); simp at this
    omega
  have hwR : ∀ hsA : Fin q → List (Perm (Fin m)), (∀ a, (hsA a).length ≤ m ^ 2) →
      (Val.list ((List.finRange q).map fun a =>
        tmJPermsVal ((hsA a).map fun s => tmJLoc a s⁻¹))).wt ≤ 27 * V ^ 5 + 4 := by
    intro hsA hsl
    have := tmJ_wt_list_le (vs := (List.finRange q).map fun a =>
      tmJPermsVal ((hsA a).map fun s => tmJLoc a s⁻¹)) (E := 13 * V ^ 4) (by
        intro v hv
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv
        exact hrowW a (hsA a) (hsl a))
    simp only [List.length_map, List.length_finRange] at this
    have h1 : q * (2 * (13 * V ^ 4) + 1) ≤ V * (27 * V ^ 4) :=
      Nat.mul_le_mul (by omega) (by have := hpow 0 4 (by norm_num); simp at this; omega)
    have e : V * (27 * V ^ 4) = 27 * V ^ 5 := by ring
    omega
  set CM := q * (BS + tmJNsRowK V) + 400000 * V ^ 6 with hCM
  refine EvalAll.call_funAll (Ra := fun v ca => ∃ hsA : Fin q → List (Perm (Fin m)),
      v = Val.list ((List.finRange q).map fun a =>
        tmJPermsVal ((hsA a).map fun s => tmJLoc a s⁻¹)) ∧
      (∀ a, (hsA a).length ≤ m ^ 2) ∧
      (∀ a r gs, O a a = some (r, gs) → gens (hsA a) = gens gs ⊓ gens σS) ∧ ca ≤ CM)
    (EvalAll.call_funAll dargs fun v ca hv => ?_) fun v ca hv => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hM.mono fun w cost hw => ?_
    obtain ⟨ws, rfl, hR, hc'⟩ := hw
    have hR' : List.Forall₂ (fun (i : Fin q) w => ∃ hs : List (Perm (Fin m)),
        w = tmJPermsVal (hs.map fun s => tmJLoc i s⁻¹) ∧ hs.length ≤ m ^ 2 ∧
        ∀ r gs, O i i = some (r, gs) → gens hs = gens gs ⊓ gens σS) (List.finRange q) ws := by
      rw [List.forall₂_map_left_iff] at hR
      exact hR.imp fun i w h => h i rfl
    obtain ⟨F, rfl, hF⟩ := tmJNs_extract hR'
    choose hsA hsw hsl hsg using hF
    have hF' : (List.finRange q).map F = (List.finRange q).map fun a =>
        tmJPermsVal ((hsA a).map fun s => tmJLoc a s⁻¹) :=
      List.map_congr_left fun a _ => hsw a
    refine ⟨hsA, by rw [hF'], hsl, hsg, ?_⟩
    -- the cost of the map
    rw [hF'] at hc'
    have wR := hwR hsA hsl
    have hsum : (((List.finRange q).map fun i : Fin q => Val.nat (i : ℕ)).map
        fun _ => BS + tmJNsRowK V).sum = q * (BS + tmJNsRowK V) := by
      simp only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate,
        List.length_finRange, smul_eq_mul]
    rw [hsum] at hc'
    have hmk : mapK * (((List.finRange q).map fun i : Fin q => Val.nat (i : ℕ)).length + 1) *
        ((Val.list [c, .list ((List.finRange q).map fun i : Fin q => Val.nat (i : ℕ))]).wt +
          (Val.list ((List.finRange q).map fun a =>
            tmJPermsVal ((hsA a).map fun s => tmJLoc a s⁻¹))).wt + 1) ≤
        1000 * V * (300 * V ^ 5) := by
      unfold mapK
      simp only [List.length_map, List.length_finRange]
      refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) ?_
      have e : (Val.list [c, .list ((List.finRange q).map fun i : Fin q => Val.nat (i : ℕ))]).wt =
          (Val.list [c, encFun fun i : Fin q => (i : ℕ)]).wt := rfl
      have := hpow 2 5 (by norm_num)
      have := hpow 1 5 (by norm_num); simp only [pow_one] at this
      have := hpow 0 5 (by norm_num); simp only [pow_zero] at this
      have wc'' : c.wt ≤ 2 * ((Val.list us).wt + (tmJLocCtx m q).wt + (encGroup σS).wt) + 7 := w3
      have wid' : (encFun fun i : Fin q => (i : ℕ)).wt ≤ 4 * (q + 1) ^ 2 := wid
      have hlc : (tmJLocCtx m q).wt ≤ 40 * V ^ 2 := wlc.trans (Nat.mul_le_mul_left _ hW2)
      omega
    have h45 := hpow 4 5 (by norm_num)
    have h25 := hpow 2 5 (by norm_num)
    have h35 := hpow 3 5 (by norm_num)
    have h15 := hpow 1 5 (by norm_num); simp only [pow_one] at h15
    have wc' : c.wt ≤ 2 * ((Val.list us).wt + (tmJLocCtx m q).wt + (encGroup σS).wt) + 7 := w3
    have : 1000 * V * (300 * V ^ 5) = 300000 * V ^ 6 := by ring
    have h56 := hpow 5 6 (by norm_num)
    have h16 := hpow 1 6 (by norm_num); simp only [pow_one] at h16
    have hd1 : (((List.finRange q).map fun i : Fin q => Val.nat (i : ℕ)).map
        fun _ => BS + tmJNsRowK V).sum = q * (BS + tmJNsRowK V) := by
      simp only [List.map_map, Function.comp_def, List.map_const', List.sum_replicate,
        List.length_finRange, smul_eq_mul]
    have hf1 : (Val.list ((List.finRange q).map F)).wt = (Val.list ((List.finRange q).map fun a =>
        tmJPermsVal ((hsA a).map fun s => tmJLoc a s⁻¹))).wt := by rw [hF']
    rw [hCM]
    omega
  · obtain ⟨hsA, rfl, hsl, hsg, hca⟩ := hv
    have hval : Val.list ((List.finRange q).map fun a =>
        tmJPermsVal ((hsA a).map fun s => tmJLoc a s⁻¹)) =
        Val.list (((List.finRange q).map fun a => ((hsA a).map fun s => tmJLoc a s⁻¹).map
          fun σ => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)).map
          Val.list) := by
      simp only [tmJPermsVal, List.map_map, Function.comp_def]
    rw [hval]
    refine FunAll.mono (tmJ_flat_spec hA.hfl hA.hflF hA.hst hA.happ ((List.finRange q).map fun a =>
      ((hsA a).map fun s => tmJLoc a s⁻¹).map
        fun σ => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)))
      fun w cost hw => ?_
    obtain ⟨rfl, hcost⟩ := hw
    have hout : Val.list (((List.finRange q).map fun a => ((hsA a).map fun s => tmJLoc a s⁻¹).map
        fun σ => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)).flatten) =
        tmJPermsVal (tmJNsList hsA) := by
      simp only [tmJPermsVal, tmJNsList, List.map_flatten, List.map_map, Function.comp_def]
    refine ⟨⟨hsA, hout, hsg⟩, ?_⟩
    have wR := hwR hsA hsl
    rw [hval] at wR
    have wfl := tmJ_wt_flatten_le ((List.finRange q).map fun a =>
      ((hsA a).map fun s => tmJLoc a s⁻¹).map
        fun σ => encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ))
    have P3 : tmJFlatK (Val.list (((List.finRange q).map fun a =>
        ((hsA a).map fun s => tmJLoc a s⁻¹).map fun σ =>
          encPerm (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) σ)).map Val.list)).wt ≤
        10 ^ 6 * (32 * V ^ 5) ^ 3 := by
      unfold tmJFlatK
      have := hpow 0 5 (by norm_num); simp at this
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    have e4 : 10 ^ 6 * (32 * V ^ 5) ^ 3 = 32768000000 * V ^ 15 := by ring
    have hqB : q * (BS + tmJNsRowK V) ≤ V * BS + 10 ^ 16 * V ^ 13 := by
      unfold tmJNsRowK
      have := Nat.mul_le_mul_right (BS + 10 ^ 16 * V ^ 12) (show q ≤ V by omega)
      have e : V * (BS + 10 ^ 16 * V ^ 12) = V * BS + 10 ^ 16 * V ^ 13 := by ring
      omega
    have h5 := hpow 5 16 (by norm_num)
    have h6 := hpow 6 16 (by norm_num)
    have h13 := hpow 13 16 (by norm_num)
    have h15 := hpow 15 16 (by norm_num)
    have h0 := hpow 0 16 (by norm_num); simp only [pow_zero] at h0
    unfold tmJNsK
    rw [hCM] at hca
    omega

end GI.Impl
