import Workspace.Impl.TermRecProgShift

/-!
# T5, one point of the pairwise step

`tmRi_y_spec`: for pieces `S, T` (lists `Sl`, `Tl`, `x` the first object of `Tl`) and a point
`y ∈ S`, the function `b + 11` returns a piece `(t, a)` of the combination whose set
`t • accSet a` is the part `{h ∈ Iso_H(S, T) : x^{h⁻¹} = y}` (`tmRiPart`). It uses the
recursion at fuel `ℓ'` as a hypothesis (`TmRiIH`), with the preconditions of the recursive call
checked: the group `H_x = Aut_H(x)` is solvable, `A ∩ H_x` is normal in it, the fuel drops
(`relDerived_mono`), and `A ∩ H_x` fixes `S^{τ⁻¹}` and `T` (`tmRec_pair_fix`, with the roles of
`S` and `T` swapped).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open scoped Pointwise
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

/-- **The recursion at fuel `ℓ`, as a hypothesis**: `TermRecSpec` at one fuel, with the
answer as a coset of `Perm (Fin n)` and a cost bound `T`. -/
def TmRiIH (P : Program) (b n M ℓ T : ℕ) : Prop :=
  ∀ (σH σN : List (Perm (Fin n))) (X Y : List (TmRiO n)),
    IsSolvable (gens σH) → gens σN ≤ gens σH → GI.Multicoset.Normalizes (gens σH) (gens σN) →
    relDerived (gens σH) (gens σN) ℓ ≤ gens σN → ℓ ≤ n ^ 2 + 5 →
    Fixes (gens σN) (tmGlMs X) → Fixes (gens σN) (tmGlMs Y) →
    σH.length ≤ n ^ 2 → σN.length ≤ n ^ 2 → X.length ≤ M → Y.length ≤ M →
    TmRecObjOK M (X ++ Y) →
    FunAll P b (tmRecIn ℓ σH σN X Y) (fun u cost =>
      CosetC n u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧ cost ≤ T)

/-- `letE` with additive cost bounds. -/
theorem tmRi_letE {P : Program} {env : List Val} {e body : Expr} {Ra : Val → ℕ → Prop}
    {R : Val → Prop} {Ka Wo B : ℕ} (ha : EvalAll P env e Ra) (hKa : ∀ v ca, Ra v ca → ca ≤ Ka)
    (hb : ∀ v ca, Ra v ca →
      EvalAll P (env ++ [v]) body (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ B)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Ka + B + Wo + 1) :=
  EvalAll.letE ha fun v ca h => (hb v ca h).mono fun w cb hw =>
    ⟨hw.1, hw.2.1, by have := hKa v ca h; omega⟩

theorem tmRi_letD {P : Program} {env : List Val} {e body : Expr} {v : Val} {ca : ℕ}
    {R : Val → Prop} {Wo B : ℕ} (ha : Det P env e v ca)
    (hb : EvalAll P (env ++ [v]) body (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ B)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ ca + B + Wo + 1) :=
  tmRi_letE ha (fun _ _ h => h.2) fun v' ca' h => by obtain ⟨rfl, -⟩ := h; exact hb

/-- `letE` with a cost budget. -/
theorem tmRi_letB {P : Program} {env : List Val} {e body : Expr} {Ra : Val → ℕ → Prop}
    {R : Val → Prop} {Ka Wo Bud : ℕ} (ha : EvalAll P env e Ra)
    (hKa : ∀ v ca, Ra v ca → ca ≤ Ka) (hB : Ka + Wo + 1 ≤ Bud)
    (hb : ∀ v ca, Ra v ca →
      EvalAll P (env ++ [v]) body (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ Bud - Ka - Wo - 1)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) :=
  EvalAll.letE ha fun v ca h => (hb v ca h).mono fun w cb hw =>
    ⟨hw.1, hw.2.1, by have := hKa v ca h; omega⟩

/-- `ite` with a cost budget. -/
theorem tmRi_iteB {P : Program} {env : List Val} {c t e : Expr} {x cc : ℕ}
    {R : Val → Prop} {Wo Bud : ℕ} (hc : Det P env c (.nat x) cc) (hB : cc + Wo + 1 ≤ Bud)
    (ht : x ≠ 0 → EvalAll P env t (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ Bud - cc - Wo - 1))
    (he : x = 0 → EvalAll P env e (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ Bud - cc - Wo - 1)) :
    EvalAll P env (.ite c t e) (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) :=
  (sup_ite hc ht he).mono fun w c' ⟨ce, ⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, by omega⟩

/-- A final deterministic step with a cost budget. -/
theorem tmRi_detB {P : Program} {env : List Val} {e : Expr} {v : Val} {cv : ℕ}
    {R : Val → Prop} {Wo Bud : ℕ} (h : Det P env e v cv) (hR : R v) (hw : v.wt ≤ Wo)
    (hc : cv ≤ Bud) : EvalAll P env e (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) :=
  h.post fun c' hc' => ⟨hR, hw, by omega⟩

theorem TmRecObjOK.of_same {M : ℕ} {L L' : List (TmRiO n)} (h : TmRecObjOK M L)
    (h' : ∀ o ∈ L', ∃ o₀ ∈ L, o.1 = o₀.1 ∧ o.2.1 = o₀.2.1) : TmRecObjOK M L' := by
  intro o ho
  obtain ⟨o₀, ho₀, e1, e2⟩ := h' o ho
  obtain ⟨h1, h2, h3⟩ := h o₀ ho₀
  refine ⟨e2 ▸ h1, e1 ▸ h2, fun o' ho' hc => ?_⟩
  obtain ⟨o₁, ho₁, e1', e2'⟩ := h' o' ho'
  rw [e2, e2']
  exact h3 o₁ ho₁ (by rw [← e1, ← e1', hc])

theorem tmRi_wt_ansC {u : Val} {C : Set (Perm (Fin n))} (h : CosetC n u C) :
    u.wt ≤ 700 * (n + 1) ^ 6 := by
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨x, hs, rfl, hl, -⟩
  · have : (Val.list []).wt ≤ 5 := by decide
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  · have := wt_list2_le (encPerm x) (encGroup hs)
    have := wt_encPerm_le x
    have := wt_encGroup_le_sq hl
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega

/-- The universal bound used for the small steps of `tmRiYE`, for an argument of weight `W`. -/
def tmRiK0 (n W : ℕ) : ℕ := 10 ^ 9 * (W + (n + 1) ^ 9 + 1) ^ 3

section Pre

variable {G : Type} [Group G] {Ω : Type} [RAct G Ω]

open scoped commutatorElement in
/-- **The preconditions of the recursive call of the pairwise step.** -/
theorem tmRi_y_pre {H N : Subgroup G} {ℓ : ℕ} (hsol : IsSolvable H) (hNH : N ≤ H)
    (hNn : GI.Multicoset.Normalizes H N) (hfuel : relDerived H N (ℓ + 1) ≤ N)
    {S T : Multiset Ω}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, SameOrb (relDerived H N ℓ) s s')
    (hT : ∀ t ∈ T, ∀ t' ∈ T, SameOrb (relDerived H N ℓ) t t') (hNT : Fixes N T) {x : Ω}
    (hx : x ∈ T) {τ : G} (hτ : τ ∈ H) (hy : x ↼ τ ∈ S) :
    IsSolvable (Aut H x) ∧ relDerived H N ℓ ⊓ Aut H x ≤ Aut H x ∧
      GI.Multicoset.Normalizes (Aut H x) (relDerived H N ℓ ⊓ Aut H x) ∧
      relDerived (Aut H x) (relDerived H N ℓ ⊓ Aut H x) ℓ ≤ relDerived H N ℓ ⊓ Aut H x ∧
      Fixes (relDerived H N ℓ ⊓ Aut H x) (S ↼ τ⁻¹) ∧ Fixes (relDerived H N ℓ ⊓ Aut H x) T := by
  set A := relDerived H N ℓ
  have hAH : A ≤ H := relDerived_le hNH ℓ
  have hAn : GI.Multicoset.Normalizes H A := relDerived_normalizes hNn ℓ
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ N := fun a ha b hb => by
    simpa [commutatorElement_def] using relDerived_commutator_mem hfuel ha hb
  have hfix := tmRec_pair_fix hNn hAH hAn hcomm hT hS hNT hx hτ hy
  refine ⟨?_, inf_le_right, ?_, ?_, hfix.2, hfix.1⟩
  · exact solvable_of_solvable_injective (Subgroup.inclusion_injective (aut_le H x))
  · intro h hh k hk
    exact ⟨hAn h (aut_le H x hh) k hk.1, (Aut H x).mul_mem ((Aut H x).mul_mem hh hk.2)
      ((Aut H x).inv_mem hh)⟩
  · have h1 := relDerived_mono hNH (aut_le H x) (M := A ⊓ Aut H x) (ℓ := ℓ) inf_le_left ℓ le_rfl
    have h2 := relDerived_le (H := Aut H x) (N := A ⊓ Aut H x) inf_le_right ℓ
    exact le_inf h1 h2

end Pre

theorem tmRiMapShC_mono (n C : ℕ) {m m' : ℕ} (h : m ≤ m') : tmRiMapShC n C m ≤ tmRiMapShC n C m' := by
  unfold tmRiMapShC
  gcongr

/-- The argument of `tmRiYE`: `[[[c, S], T], y]` with `c = [ℓ, gens H, gens A, P]`. -/
def tmRiYArg (ℓ : ℕ) (σH σA : List (Perm (Fin n))) (Pl : Val) (Sl Tl : List (TmRiO n))
    (oy : TmRiO n) : Val :=
  .list [.list [.list [.list [.nat ℓ, encGroup σH, encGroup σA, Pl], tmGlObjsVal Sl],
    tmGlObjsVal Tl], tmGlObjVal oy]

/-- The size parameter of `tmRiYE`. -/
def tmRiV (n M W : ℕ) : ℕ := W + M + (n + 1) ^ 9 + 1

/-- The cost bound of `tmRiYE` besides the recursive call. -/
noncomputable def tmRiYC (psci : Prim) (n M W : ℕ) : ℕ :=
  tmRiTestC psci n (2 * M) + psci.boundSize (10 ^ 4 * (n + 1) ^ 6) +
    tmRiMapShC n (2 * M) M + 10 ^ 12 * tmRiV n M W ^ 3

/-- **One point `y ∈ S` of the pairwise step.** -/
theorem tmRi_y_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {M ℓ T : ℕ} (ih : TmRiIH P b n M ℓ T)
    {σH σN σA : List (Perm (Fin n))} {Pl : Val} {Sl Tl : List (TmRiO n)} {ox oy : TmRiO n}
    (hsol : IsSolvable (gens σH)) (hHl : σH.length ≤ n ^ 2) (hAl : σA.length ≤ n ^ 2)
    (hNH : gens σN ≤ gens σH) (hNn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hA : gens σA = relDerived (gens σH) (gens σN) ℓ)
    (hfuel : relDerived (gens σH) (gens σN) (ℓ + 1) ≤ gens σN) (hℓ : ℓ ≤ n ^ 2 + 5)
    (hSo : ∀ s ∈ tmGlMs Sl, ∀ s' ∈ tmGlMs Sl, SameOrb (gens σA) s s')
    (hTo : ∀ t ∈ tmGlMs Tl, ∀ t' ∈ tmGlMs Tl, SameOrb (gens σA) t t')
    (hNT : Fixes (gens σN) (tmGlMs Tl)) (hSl : Sl.length ≤ M) (hTl : Tl.length ≤ M)
    (hok : TmRecObjOK M (Sl ++ Tl)) (hT0 : Tl[0]? = some ox) (hy : oy ∈ Sl) {W : ℕ}
    (hW : (tmRiYArg ℓ σH σA Pl Sl Tl oy).wt ≤ W) :
    FunAll P (b + 11) (tmRiYArg ℓ σH σA Pl Sl Tl oy) (fun w cost =>
      (∃ t a, w = encPiece (t, a) ∧
        t • accSet a = tmRiPart (gens σH) (tmGlMs Sl) (tmGlMs Tl) (tmRiObj ox) (tmRiObj oy) ∧
        ∀ c gs, a = some (c, gs) → gs.length ≤ n ^ 2) ∧
      cost ≤ T + tmRiYC (solvableCosetIntersectionPrim hsci) n M W) := by
  set c : Val := .list [.nat ℓ, encGroup σH, encGroup σA, Pl] with hc
  set SV := tmGlObjsVal Sl with hSV
  set TV := tmGlObjsVal Tl with hTV
  set cS : Val := .list [c, SV] with hcS
  set cST : Val := .list [cS, TV] with hcST
  set vs : List Val := [cST, tmGlObjVal oy] with hvs
  have hargv : tmRiYArg ℓ σH σA Pl Sl Tl oy = .list vs := rfl
  rw [hargv] at hW ⊢
  set V := tmRiV n M W with hV
  -- weights
  have w1 : cST.wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have w2 : (tmGlObjVal oy).wt < (Val.list vs).wt := wt_le_wt_list (by simp [hvs])
  have w3 : cS.wt < cST.wt := wt_le_wt_list (by simp [hcST])
  have w4 : TV.wt < cST.wt := wt_le_wt_list (by simp [hcST])
  have w5 : c.wt < cS.wt := wt_le_wt_list (by simp [hcS])
  have w6 : SV.wt < cS.wt := wt_le_wt_list (by simp [hcS])
  have w7 : (encGroup σH).wt < c.wt := wt_le_wt_list (by simp [hc])
  have w8 : (encGroup σA).wt < c.wt := wt_le_wt_list (by simp [hc])
  have w9 : (Val.nat ℓ).wt < c.wt := wt_le_wt_list (by simp [hc])
  have hox : ox ∈ Tl := List.mem_of_getElem? hT0
  have w10 : (tmGlObjVal ox).wt < TV.wt := wt_le_wt_list (List.mem_map_of_mem hox)
  have hTV0 : (Tl.map tmGlObjVal)[0]? = some (tmGlObjVal ox) := by simp [hT0]
  have hokx := hok ox (by simp [hox])
  have hoky := hok oy (by simp [hy])
  have hn6 : (n + 1) ^ 6 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hV1 : W + M + (n + 1) ^ 9 + 1 ≤ V := le_rfl
  have hVV : V ≤ V ^ 2 := Nat.le_self_pow (by norm_num) _
  have hVV3 : V ^ 2 ≤ V ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  set Part := tmRiPart (gens σH) (tmGlMs Sl) (tmGlMs Tl) (tmRiObj ox) (tmRiObj oy) with hPart
  set R : Val → Prop := fun w => ∃ t a, w = encPiece (t, a) ∧ t • accSet a = Part ∧
      ∀ c gs, a = some (c, gs) → gs.length ≤ n ^ 2 with hR
  set Wo := 2000 * (n + 1) ^ 6 with hWo
  set K0 := 10 ^ 7 * V ^ 2 with hK0
  set Bud := T + tmRiYC (solvableCosetIntersectionPrim hsci) n M W with hBud
  have hBud' : Bud = T + tmRiTestC (solvableCosetIntersectionPrim hsci) n (2 * M) +
      (solvableCosetIntersectionPrim hsci).boundSize (10 ^ 4 * (n + 1) ^ 6) +
      tmRiMapShC n (2 * M) M + 10 ^ 12 * V ^ 3 := by
    rw [hBud]; unfold tmRiYC; rw [← hV]; ring
  have hfV : (n + 1) ^ 9 ≤ V := by omega
  have hWV : W ≤ V := by omega
  have hMV : M ≤ V := by omega
  have h1V : 1 ≤ V := by omega
  have hmk : 8 * mkGroupK * (n + 1) ^ 9 ≤ 800000 * V := by
    simp only [mkGroupK]; omega
  have hinvK : invK * (n + 1) ^ 4 ≤ 100000 * V := by
    have : (n + 1) ^ 4 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [invK]; omega
  have hpermK : permK * (n + 1) ^ 3 ≤ 30000 * V := by
    have : (n + 1) ^ 3 ≤ (n + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [permK]; omega
  have hp2 : ∀ σ : Perm (Fin n), (encPerm σ).wt ≤ 4 * V := fun σ => by
    have := wt_encPerm_le σ; omega
  have hf6V : (n + 1) ^ 6 ≤ V := by omega
  -- Dets of the argument
  have dYc : ∀ rest, Det P (.list vs :: rest) tmRiYc c (4 * W + 30) := fun rest =>
    (Det.get' (Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (v := cS) rfl) (Det.nat 0) (v := c) rfl).mono (by omega)
  have dYH : ∀ rest, Det P (.list vs :: rest) tmRiYH (encGroup σH) (5 * W + 40) := fun rest =>
    (Det.get' (dYc rest) (Det.nat 1) (v := encGroup σH) rfl).mono (by omega)
  have dYS : ∀ rest, Det P (.list vs :: rest) tmRiYS SV (4 * W + 30) := fun rest =>
    (Det.get' (Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl) (Det.nat 0)
      (v := cS) rfl) (Det.nat 1) (v := SV) rfl).mono (by omega)
  have dYT : ∀ rest, Det P (.list vs :: rest) tmRiYT (.list (Tl.map tmGlObjVal)) (4 * W + 30) :=
    fun rest => (Det.get' (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 0) rfl) (Det.nat 1)
      (v := TV) rfl).mono (by omega)
  have dT0 : ∀ rest, Det P (.list vs :: rest) (.get tmRiYT (.nat 0)) (tmGlObjVal ox) (5 * W + 40) :=
    fun rest => (Det.get' (dYT rest) (Det.nat 0) hTV0).mono (by omega)
  have dy : ∀ rest, Det P (.list vs :: rest) (arg 1) (tmGlObjVal oy) (2 * W + 6) := fun rest =>
    (Det.arg' (P := P) (vs := vs) (rest := rest) (j := 1) rfl).mono (by omega)
  have dn : ∀ rest, Det P (.list vs :: rest) (.get tmRiYH (.nat 0)) (.nat n) (6 * W + 50) :=
    fun rest => (Det.get' (dYH rest) (Det.nat 0) (v := .nat n) rfl).mono (by
      have : (Val.nat n).wt < (encGroup σH).wt := wt_le_wt_list (by simp [encGroup]); omega)
  have d1 : ∀ rest, Det P (.list vs :: rest) (.get (.get tmRiYH (.nat 1)) (.nat 0)) (encPerm 1)
      (7 * W + 60) := fun rest => (Det.get' (Det.get' (dYH rest) (Det.nat 1)
        (v := .list ((1 :: σH).map encPerm)) rfl) (Det.nat 0) (v := encPerm 1) rfl).mono (by
      have h1 : (Val.list ((1 :: σH).map encPerm)).wt < (encGroup σH).wt :=
        wt_le_wt_list (by simp [encGroup, GI.Cited.encPerms])
      have h2 : (encPerm 1 : Val).wt < (Val.list ((1 :: σH).map encPerm)).wt :=
        wt_le_wt_list (List.mem_cons_self ..)
      omega)
  refine FunAll.intro hP.y (EvalAll.mono (Q := fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) ?_
    fun w c h => ⟨h.1, h.2.2⟩)
  -- the object test
  have dargs := Det.mk3 (dYH []) (dT0 []) (dy [])
  have htest := EvalAll.call_funAll (f := b + 5) dargs
    (Q := fun w cw => TmRiTestOut (gens σH) ox oy w ∧ cw ≤ 30 * W + 300 + tmRiTestC (solvableCosetIntersectionPrim hsci) n (2 * M) +
      40 * (n + 1) ^ 6) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine FunAll.mono (tmRi_test_spec hP hsol hHl hokx.1 hoky.1
      (hokx.2.2 oy (by simp [hy])) (C := 2 * M) (by omega) (by omega)) fun w cb h => ⟨h.1, ?_⟩
    have := h.1.wt_le
    have := wt_list3_le (encGroup σH) (tmGlObjVal ox) (tmGlObjVal oy)
    omega
  refine tmRi_letB htest (fun v ca h => h.2) ?_ fun w1 c1 h1 => ?_
  · omega
  have hw1 := h1.1.wt_le
  have dnat := (Det.isNat (Det.var' (P := P) (env := [.list vs, w1]) (i := 1) (v := w1)
    rfl)).mono (c' := 40 * V + 5) (by omega)
  refine tmRi_iteB dnat ?_ (fun hne => ?_) (fun heq => ?_)
  · omega
  · -- no element of `H` carries `x` to `y`
    have h01 := tmRi_isNatNum_le w1
    have hno := h1.1.zero_iff.1 (by omega)
    have hw2 := wt_list2_le (encPerm (1 : Perm (Fin n))) (.list [])
    have hnil : (Val.list []).wt ≤ 5 := by decide
    have dthen := (Det.mk2 (d1 [w1]) (Det.nil (P := P) (env := [.list vs, w1]))).mono
      (c' := K0) (by have := hp2 (1 : Perm (Fin n)); omega)
    refine tmRi_detB dthen ⟨1, none, rfl, ?_, fun c gs h => by cases h⟩ ?_ ?_
    · rw [hPart, tmRi_piece_empty (fun g hg he => hno ⟨g, hg, he⟩)]
      simp [accSet]
    · have := wt_encPerm_le (1 : Perm (Fin n)); omega
    · omega
  · -- `τ` with `x^τ = y`
    rcases h1.1 with ⟨rfl, -⟩ | ⟨z, L, rfl, hz, hact, hL⟩
    · simp [Val.isNatNum] at heq
    set τ := z * (ox.2.2⁻¹ * oy.2.2) with hτdef
    have hxy : tmRiObj ox ↼ τ = tmRiObj oy := hact
    -- `τ`
    set e1 : List Val := [.list [encPerm z, L]] with he1
    have dz := Det.get' (Det.var' (P := P) (env := .list vs :: e1) (i := 1) rfl) (Det.nat 0)
      (v := encPerm z) rfl
    have dhx := Det.get' (dT0 e1) (Det.nat 2) (v := encPerm ox.2.2) rfl
    have dhxi := Det.call dhx (inv_spec hP.inv ox.2.2)
    have dhy := Det.get' (dy e1) (Det.nat 2) (v := encPerm oy.2.2) rfl
    have dc1 := Det.call (Det.mk2 dhxi dhy) (compose_spec hP.comp ox.2.2⁻¹ oy.2.2)
    have dτ := (Det.call (Det.mk2 dz dc1) (compose_spec hP.comp z (ox.2.2⁻¹ * oy.2.2))).mono
      (c' := K0) (by
        have := hp2 z; have := hp2 ox.2.2; have := hp2 oy.2.2; have := hp2 ox.2.2⁻¹
        have := hp2 (ox.2.2⁻¹ * oy.2.2); have := hp2 τ; have := hp2 (z * (ox.2.2⁻¹ * oy.2.2))
        have := wt_list2_le (encPerm z) L
        have := wt_list2_le (encPerm ox.2.2⁻¹) (encPerm oy.2.2)
        have := wt_list2_le (encPerm z) (encPerm (ox.2.2⁻¹ * oy.2.2))
        have : (encPerm z).wt < (Val.list [encPerm z, L]).wt := wt_le_wt_list (by simp)
        have : (encPerm ox.2.2).wt < (tmGlObjVal ox).wt := wt_le_wt_list (by simp [tmGlObjVal])
        have : (encPerm oy.2.2).wt < (tmGlObjVal oy).wt := wt_le_wt_list (by simp [tmGlObjVal])
        omega)
    refine tmRi_letB dτ (fun _ _ h => h.2) ?_ fun v2 c2 h2 => ?_
    · omega
    obtain ⟨rfl, -⟩ := h2
    -- `τ⁻¹`
    have dτi := Det.call (Det.var' (P := P) (env := .list vs :: (e1 ++ [encPerm τ])) (i := 2)
      (v := encPerm τ) rfl) (inv_spec hP.inv τ) |>.mono (c' := K0) (by
        have := hp2 τ; have := hp2 τ⁻¹; omega)
    refine tmRi_letB dτi (fun _ _ h => h.2) ?_ fun v3 c3 h3 => ?_
    · omega
    obtain ⟨rfl, -⟩ := h3
    -- `H_x`
    obtain ⟨hs, rfl, hsl, hsfd, ⟨hs', ehs, hgs⟩, hsw⟩ := mkGroup_gensVal hP.mg hL
    obtain rfl := GI.CitedChecks.detm_encGroup_inj ehs
    set e4 : List Val := e1 ++ [encPerm τ, encPerm τ⁻¹] with he4
    have dgHx := Det.call (Det.mk2 (dn e4) (Det.get' (Det.var' (P := P) (env := .list vs :: e4)
      (i := 1) rfl) (Det.nat 1) (v := .list (hs.map encPerm)) rfl)) hsfd |>.mono
        (c' := K0 + 800000 * V) (by
          have := wt_list2_le (encPerm z) (.list (hs.map encPerm))
          have := wt_list2_le (.nat n) (.list (hs.map encPerm))
          have : (Val.list (hs.map encPerm)).wt < (Val.list [encPerm z, .list (hs.map encPerm)]).wt :=
            wt_le_wt_list (by simp)
          have := hp2 z
          have : (Val.nat n).wt ≤ n + 2 := wt_nat_le n
          have : n + 2 ≤ V := by have : n + 1 ≤ (n + 1) ^ 9 := Nat.le_self_pow (by norm_num) _; omega
          omega)
    refine tmRi_letB dgHx (fun _ _ h => h.2) ?_ fun v4 c4 h4 => ?_
    · omega
    obtain ⟨rfl, -⟩ := h4
    -- `A ∩ H_x`
    set e5 : List Val := e4 ++ [encGroup hs] with he5
    have dgA := Det.get' (dYc e5) (Det.nat 2) (v := encGroup σA) rfl
    have dv4 := Det.var' (P := P) (env := .list vs :: e5) (i := 4) (v := encGroup hs) rfl
    have hsolA : IsSolvable (gens σA) := by
      rw [hA]
      exact solvable_of_solvable_injective (Subgroup.inclusion_injective (relDerived_le hNH ℓ))
    have hwA := wt_encGroup_le_sq hAl
    have hsz : (Val.list [encGroup σA, encGroup hs, encPerm (1 : Perm (Fin n))]).size ≤
        10 ^ 4 * (n + 1) ^ 6 := by
      have := wt_list3_le (encGroup σA) (encGroup hs) (encPerm (1 : Perm (Fin n)))
      have := wt_encPerm_le (1 : Perm (Fin n))
      exact (Val.size_le_wt _).trans (by omega)
    have hbd := (solvableCosetIntersectionPrim hsci).bound_le hsz
    have hsci' := (solvableCosetIntersection_call hsci hP.sci (Det.mk3 dgA dv4 (d1 e5))
      ⟨σA, rfl, rfl⟩ hsolA (H := gens hs) ⟨hs, rfl, rfl⟩ (x := 1)).mono
      (Q' := fun w cw => CosetIntOut (gens σA) (gens hs) 1 w ∧ cw ≤ K0 +
        (solvableCosetIntersectionPrim hsci).boundSize (10 ^ 4 * (n + 1) ^ 6) + 40 * V + 1)
      fun w cw h => ⟨h.1, by
        have := wt_list3_le (encGroup σA) (encGroup hs) (encPerm (1 : Perm (Fin n)))
        have := hp2 (1 : Perm (Fin n))
        have : (encGroup σA).wt < c.wt := w8
        omega⟩
    refine tmRi_letB hsci' (fun _ _ h => h.2) ?_ fun w5 c5 h5 => ?_
    · omega
    rcases h5.1 with ⟨-, hno⟩ | ⟨y', -, -, L', rfl, hL'⟩
    · exact absurd (by simpa using (gens hs).one_mem) (hno 1 (gens σA).one_mem)
    obtain ⟨hk, rfl, hkl, hkfd, ⟨hk', ehk, hgk⟩, hkw⟩ := mkGroup_gensVal hP.mg hL'
    obtain rfl := GI.CitedChecks.detm_encGroup_inj ehk
    set e6 : List Val := e5 ++ [.list [encPerm y', .list (hk.map encPerm)]] with he6
    have dgK := Det.call (Det.mk2 (dn e6) (Det.get' (Det.var' (P := P) (env := .list vs :: e6)
      (i := 5) rfl) (Det.nat 1) (v := .list (hk.map encPerm)) rfl)) hkfd |>.mono
        (c' := K0 + 800000 * V) (by
          have := wt_list2_le (encPerm y') (.list (hk.map encPerm))
          have := wt_list2_le (.nat n) (.list (hk.map encPerm))
          have : (Val.list (hk.map encPerm)).wt < (Val.list [encPerm y', .list (hk.map encPerm)]).wt :=
            wt_le_wt_list (by simp)
          have := hp2 y'
          have := wt_list_encPerms_le_sq hkl
          have : (Val.nat n).wt ≤ n + 2 := wt_nat_le n
          have : n + 2 ≤ V := by have : n + 1 ≤ (n + 1) ^ 9 := Nat.le_self_pow (by norm_num) _; omega
          omega)
    refine tmRi_letB dgK (fun _ _ h => h.2) ?_ fun v6 c6 h6 => ?_
    · omega
    obtain ⟨rfl, -⟩ := h6
    -- `S^{τ⁻¹}`
    set e7 : List Val := e6 ++ [encGroup hk] with he7
    have hokS : TmRiOK (2 * M) Sl := fun o ho =>
      ⟨(hok o (by simp [ho])).1, by have := (hok o (by simp [ho])).2.1; omega,
        fun o' ho' hc => (hok o (by simp [ho])).2.2 o' (by simp [ho']) hc⟩
    have dS' := Det.call (Det.mk2 (Det.var' (P := P) (env := .list vs :: e7) (i := 3)
      (v := encPerm τ⁻¹) rfl) (dYS e7)) (tmRi_mapShift_spec hP τ⁻¹ hokS) |>.mono
        (c' := K0 + tmRiMapShC n (2 * M) M + 10 * V ^ 2) (by
          have := tmRiMapShC_mono n (2 * M) hSl
          have := wt_list2_le (encPerm τ⁻¹) SV
          have := hp2 τ⁻¹
          have h1 := tmRi_wt_objs (tmRiOK_shift hokS τ⁻¹)
          rw [List.length_map] at h1
          have h2 : Sl.length * (2 * (1000 * (n + 1) ^ 6 + 2 * (2 * M)) + 1) ≤ V * (2010 * V) :=
            Nat.mul_le_mul (by omega) (by omega)
          have h3 : V * (2010 * V) = 2010 * V ^ 2 := by ring
          omega)
    refine tmRi_letB dS' (fun _ _ h => h.2) ?_ fun v7 c7 h7 => ?_
    · omega
    obtain ⟨rfl, -⟩ := h7
    -- the recursive call
    have hxT : tmRiObj ox ∈ tmGlMs Tl := by
      simp only [tmGlMs, Multiset.mem_coe, List.mem_map]; exact ⟨ox, hox, rfl⟩
    have hyS : tmRiObj ox ↼ τ ∈ tmGlMs Sl := by
      rw [hxy]; simp only [tmGlMs, Multiset.mem_coe, List.mem_map]; exact ⟨oy, hy, rfl⟩
    obtain ⟨p1, -, p3, p4, p5, p6⟩ := tmRi_y_pre hsol hNH hNn hfuel (hA ▸ hSo) (hA ▸ hTo) hNT
      hxT hz hyS
    rw [← hA, ← hgs, ← hgk] at p3 p4 p5 p6
    rw [← hgs] at p1
    have hkle : gens hk ≤ gens hs := by rw [hgk]; exact inf_le_right
    rw [← tmRi_ms_shift] at p5
    have hokR : TmRecObjOK M (Sl.map (tmRiSh τ⁻¹) ++ Tl) := hok.of_same fun o ho => by
      rcases List.mem_append.1 ho with ho | ho
      · obtain ⟨o₀, ho₀, rfl⟩ := List.mem_map.1 ho
        exact ⟨o₀, by simp [ho₀], rfl, rfl⟩
      · exact ⟨o, by simp [ho], rfl, rfl⟩
    have hrec := ih hs hk (Sl.map (tmRiSh τ⁻¹)) Tl p1 hkle p3 p4 hℓ p5 p6 hsl hkl
      (by simpa using hSl) hTl hokR
    set e8 : List Val := e7 ++ [tmGlObjsVal (Sl.map (tmRiSh τ⁻¹))] with he8
    have dl := Det.get' (dYc e8) (Det.nat 0) (v := .nat ℓ) rfl
    set K1 := 6 * W + 400 * (n + 1) ^ 6 + (tmGlObjsVal (Sl.map (tmRiSh τ⁻¹))).wt + 50 with hK1
    have dml := Det.mkList (P := P) (env := .list vs :: e8) (c := K1)
      [(.get tmRiYc (.nat 0), .nat ℓ), (.var 4, encGroup hs), (.var 6, encGroup hk),
        (.var 7, tmGlObjsVal (Sl.map (tmRiSh τ⁻¹))), (tmRiYT, .list (Tl.map tmGlObjVal))]
      (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        have := wt_encGroup_le_sq hsl
        have := wt_encGroup_le_sq hkl
        have : (Val.nat ℓ).wt < c.wt := w9
        rcases hp with rfl | rfl | rfl | rfl | rfl
        · exact dl.mono (by omega)
        · exact (Det.var' (P := P) (env := .list vs :: e8) (i := 4) rfl).mono (by omega)
        · exact (Det.var' (P := P) (env := .list vs :: e8) (i := 6) rfl).mono (by omega)
        · exact (Det.var' (P := P) (env := .list vs :: e8) (i := 7) rfl).mono (by omega)
        · exact (dYT e8).mono (by omega))
    have hcall := EvalAll.call_funAll (f := b) dml (Q := fun u cu =>
      CosetC n u (Iso (gens hs) (tmGlMs (Sl.map (tmRiSh τ⁻¹))) (tmGlMs Tl)) ∧
        cu ≤ 5 * (K1 + (Val.list [.nat ℓ, encGroup hs, encGroup hk, tmGlObjsVal (Sl.map (tmRiSh τ⁻¹)),
          .list (Tl.map tmGlObjVal)]).wt + 1) + 5 + T +
          700 * (n + 1) ^ 6 + 1) fun v ca hv => by
      obtain ⟨rfl, hca⟩ := hv
      exact hrec.mono fun u cu h => ⟨h.1, by have := tmRi_wt_ansC h.1; simp at hca; omega⟩
    have hS'w : (tmGlObjsVal (Sl.map (tmRiSh τ⁻¹))).wt ≤ 2010 * V ^ 2 + 4 := by
      have h1 := tmRi_wt_objs (tmRiOK_shift hokS τ⁻¹)
      rw [List.length_map] at h1
      have h2 : Sl.length * (2 * (1000 * (n + 1) ^ 6 + 2 * (2 * M)) + 1) ≤ V * (2010 * V) :=
        Nat.mul_le_mul (by omega) (by omega)
      have h3 : V * (2010 * V) = 2010 * V ^ 2 := by ring
      omega
    have hRw : (Val.list [.nat ℓ, encGroup hs, encGroup hk, tmGlObjsVal (Sl.map (tmRiSh τ⁻¹)),
        .list (Tl.map tmGlObjVal)]).wt ≤ 5000 * V ^ 2 + 2000 * V + 100 := by
      have := wt_list_le [.nat ℓ, encGroup hs, encGroup hk, tmGlObjsVal (Sl.map (tmRiSh τ⁻¹)),
        .list (Tl.map tmGlObjVal)]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at this
      have := wt_encGroup_le_sq hsl
      have := wt_encGroup_le_sq hkl
      have : (Val.nat ℓ).wt < c.wt := w9
      have : (Val.list (Tl.map tmGlObjVal)).wt < cST.wt := w4
      omega
    refine tmRi_letB hcall (fun _ _ h => h.2) ?_ fun ans c8 h8 => ?_
    · omega
    -- the piece
    have dfin := Det.mk2 (Det.var' (P := P) (env := .list vs :: (e8 ++ [ans])) (i := 3)
      (v := encPerm τ⁻¹) rfl) (Det.var' (P := P) (env := .list vs :: (e8 ++ [ans])) (i := 8)
      (v := ans) rfl)
    have hpiece : τ⁻¹ • Iso (gens hs) (tmGlMs (Sl.map (tmRiSh τ⁻¹))) (tmGlMs Tl) = Part := by
      rw [hPart, tmRi_ms_shift, hgs]
      exact tmRi_piece_eq hz hxy
    have hansw := tmRi_wt_ansC h8.1
    have hfw := wt_list2_le (encPerm τ⁻¹) ans
    have := hp2 τ⁻¹
    have := wt_encPerm_le τ⁻¹
    have dfin' := dfin.mono (c' := K0) (by omega)
    refine tmRi_detB dfin' ?_ ?_ ?_
    · rcases h8.1 with ⟨rfl, he⟩ | ⟨k, gs, rfl, hgsl, he⟩
      · refine ⟨τ⁻¹, none, rfl, ?_, fun c gs h => by cases h⟩
        rw [← hpiece, he]; rfl
      · refine ⟨τ⁻¹, some (k, gs), rfl, ?_, fun c gs' h => by cases h; exact hgsl⟩
        rw [← hpiece, he]; rfl
    · have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
      omega
    · omega

end GI.Impl
