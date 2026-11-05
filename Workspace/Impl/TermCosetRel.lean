module

public import Workspace.Impl.TermJ
public import Workspace.Lang.Lib.Orbit
public import Workspace.Lang.Lib.Tabulate

@[expose] public section

/-!
# Relabeling a pair answer to the domain positions

`TermJSpec` returns its answer on `Fin (m q)`: the pair `(c, i)` sits at `finProdFinEquiv (c, i)`.
`TermCosetSpec` wants the answer on the domain positions `Fin s` of the state, numbered by
`domEquiv e S.dom`. The two numberings differ by the bijection
`ρ = finProdFinEquiv⁻¹ ≫ E ≫ domEquiv : Fin (m q) ≃ Fin s` (`tmCsRho`), and `s = m q`.
So the relabeling conjugates the representative and every generator by `ρ`
(`tmCs_rel_cons`, from `tmJ_toFin_trans` and `tmJ_domSet_eq`).

The program builds the table of `ρ` once, as a permutation of `Fin (m q)`: entry `t` is
`pos[cv[t % q][t / q]]`, with `pos` the position table of the domain and `cv` the coordinates
(`tmCsTabF`, `tmCs_tab_spec`). It then conjugates with two `compose` calls (`tmCsConjF`) and maps
this over the generators (`tmCsRelF`, `tmCs_rel_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encPerms encGroup gens)
open scoped Pointwise

variable {Ω C : Type} {k : ℕ}

/-! ### The mathematics -/

/-- The numbering of the pairs by the domain positions. -/
noncomputable def tmCsRho (e : Ω ≃ Fin k) {S : State Ω C} {m q : ℕ} (E : Fin m × Fin q ≃ S.dom) :
    Fin (m * q) ≃ Fin (domFin e S.dom).length :=
  finProdFinEquiv.symm.trans (E.trans (domEquiv e S.dom))

/-- The same numbering as a permutation of `Fin (m q)`, when `s = m q`. -/
noncomputable def tmCsRhoP (e : Ω ≃ Fin k) {S : State Ω C} {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (hs : (domFin e S.dom).length = m * q) : Perm (Fin (m * q)) :=
  (tmCsRho e E).trans (finCongr hs)

theorem tmCsRhoP_apply (e : Ω ≃ Fin k) {S : State Ω C} {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (hs : (domFin e S.dom).length = m * q) (t : Fin (m * q)) :
    (tmCsRhoP e E hs t : ℕ) =
      posOf (domNat e S.dom) (e (E (finProdFinEquiv.symm t)).val) := rfl

/-- Conjugation by a numbering is conjugation in `Perm (Fin n)`, up to the cast `s = n`. -/
theorem tmCs_encPerm_toFin {s n : ℕ} (hs : s = n) (ρ : Fin n ≃ Fin s) (x : Perm (Fin n)) :
    encPerm (toFin ρ x) =
      encPerm (ρ.trans (finCongr hs) * x * (ρ.trans (finCongr hs))⁻¹) := by
  subst hs
  congr 1

theorem tmCs_encGroup_toFin {s n : ℕ} (hs : s = n) (ρ : Fin n ≃ Fin s)
    (gs : List (Perm (Fin n))) :
    encGroup (gs.map (toFin ρ)) = encGroup (gs.map fun g =>
      ρ.trans (finCongr hs) * g * (ρ.trans (finCongr hs))⁻¹) := by
  subst hs
  congr 1

/-- **The empty answer stays empty.** -/
theorem tmCs_rel_nil {S : State Ω C} (e : Ω ≃ Fin k) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    {T : Set ((Fin q → Perm (Fin m)) × Perm (Fin q))}
    (h : tmJSet T = ∅) : AnsC (domEquiv e S.dom) (.list []) (tmDomSet E T) := by
  refine Or.inl ⟨rfl, ?_⟩
  rw [tmJ_domSet_eq, h, Set.image_empty]

/-- **A coset answer is conjugated by the numbering.** -/
theorem tmCs_rel_cons {S : State Ω C} (e : Ω ≃ Fin k) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (hs : (domFin e S.dom).length = m * q)
    {T : Set ((Fin q → Perm (Fin m)) × Perm (Fin q))} {x : Perm (Fin (m * q))}
    {gs : List (Perm (Fin (m * q)))} (hgl : gs.length ≤ (m * q) ^ 2)
    (hA : toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) '' tmJSet T =
      x • (gens gs : Set (Perm (Fin (m * q))))) :
    AnsC (domEquiv e S.dom)
      (.list [encPerm (tmCsRhoP e E hs * x * (tmCsRhoP e E hs)⁻¹),
        encGroup (gs.map fun g => tmCsRhoP e E hs * g * (tmCsRhoP e E hs)⁻¹)])
      (tmDomSet E T) := by
  have h1 := tmJ_toFin_trans finProdFinEquiv (tmCsRho e E) hA
  have htr : (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)).trans (tmCsRho e E) =
      E.trans (domEquiv e S.dom) := by
    ext a; simp [tmCsRho]
  have hcomp : ∀ σ : Perm (Fin m × Fin q),
      toFin (E.trans (domEquiv e S.dom)) σ = toFin (domEquiv e S.dom) (E.permCongr σ) := by
    intro σ; ext a; simp [Equiv.permCongr_apply]
  rw [htr] at h1
  refine Or.inr ⟨toFin (tmCsRho e E) x, gs.map (toFin (tmCsRho e E)), ?_, ?_, ?_⟩
  · rw [tmCs_encPerm_toFin hs, tmCs_encGroup_toFin hs]; rfl
  · rw [List.length_map, hs]; exact hgl
  · rw [← h1, tmJ_domSet_eq, Set.image_image]
    exact Set.image_congr fun σ _ => (hcomp σ).symm

/-! ### Conjugating an answer -/

/-- On `[[ρ, ρ⁻¹], σ]`: `ρ σ ρ⁻¹`, by two `compose` calls. -/
def tmCsConjF (cp : ℕ) : Expr :=
  .call cp (mk2 (.call cp (mk2 (.get (arg 0) (.nat 0)) (arg 1))) (.get (arg 0) (.nat 1)))

/-- The cost of one conjugation. -/
def tmCsConjK (n : ℕ) : ℕ := 10 ^ 6 * (n + 1) ^ 3

theorem tmCs_conj_spec {P : Program} {f cp : ℕ} (hf : P.funs[f]? = some (tmCsConjF cp))
    (hcp : P.HasAt cp (composeFuns cp)) {n : ℕ} (ρ σ : Perm (Fin n)) :
    FunDet P f (.list [.list [encPerm ρ, encPerm ρ⁻¹], encPerm σ]) (encPerm (ρ * σ * ρ⁻¹))
      (tmCsConjK n) := by
  refine FunDet.intro hf ?_
  set a := Val.list [.list [encPerm ρ, encPerm ρ⁻¹], encPerm σ] with ha
  have d0 := Det.arg' (P := P) (vs := [.list [encPerm ρ, encPerm ρ⁻¹], encPerm σ]) (rest := [])
    (j := 0) (v := .list [encPerm ρ, encPerm ρ⁻¹]) rfl
  have d1 := Det.arg' (P := P) (vs := [.list [encPerm ρ, encPerm ρ⁻¹], encPerm σ]) (rest := [])
    (j := 1) (v := encPerm σ) rfl
  have dr := Det.get' d0 (Det.nat 0) (vs := [encPerm ρ, encPerm ρ⁻¹]) (v := encPerm ρ) rfl
  have dri := Det.get' d0 (Det.nat 1) (vs := [encPerm ρ, encPerm ρ⁻¹]) (v := encPerm ρ⁻¹) rfl
  have c1 := Det.call (Det.mk2 dr d1) (compose_spec hcp ρ σ)
  have c2 := Det.call (Det.mk2 c1 dri) (compose_spec hcp (ρ * σ) ρ⁻¹)
  refine c2.mono ?_
  have w1 := wt_encPerm_le ρ
  have w2 := wt_encPerm_le ρ⁻¹
  have w3 := wt_encPerm_le σ
  have w4 := wt_encPerm_le (ρ * σ)
  have w5 := wt_encPerm_le (ρ * σ * ρ⁻¹)
  have wa := wt_list2_le (Val.list [encPerm ρ, encPerm ρ⁻¹]) (encPerm σ)
  have wb := wt_list2_le (encPerm ρ) (encPerm ρ⁻¹)
  have wc := wt_list2_le (encPerm ρ) (encPerm σ)
  have wd := wt_list2_le (encPerm (ρ * σ)) (encPerm ρ⁻¹)
  have hpk : permK = 30000 := rfl
  have h23 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h12 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold tmCsConjK
  rw [hpk]
  omega

/-- On `[[ρ, ρ⁻¹], u]`: the empty answer stays empty; `[x, [n, gs]]` becomes
`[ρ x ρ⁻¹, [n, ρ gs ρ⁻¹]]`. -/
def tmCsRelF (conj mp : ℕ) : Expr :=
  .ite (.length (arg 1))
    (mk2 (.call conj (mk2 (arg 0) (.get (arg 1) (.nat 0))))
      (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
        (.call mp (mk2 (arg 0) (.get (.get (arg 1) (.nat 1)) (.nat 1))))))
    .nil

/-- The cost of the relabeling of one answer. -/
def tmCsRelK (n : ℕ) : ℕ := 10 ^ 12 * (n + 1) ^ 9

/-- **The relabeling of a pair answer**, given the table of the numbering. -/
theorem tmCs_rel_spec {P : Program} {f conj cp mp : ℕ} (hf : P.funs[f]? = some (tmCsRelF conj mp))
    (hconj : P.funs[conj]? = some (tmCsConjF cp)) (hcp : P.HasAt cp (composeFuns cp))
    (hmp : P.HasAt mp (mapFuns mp conj))
    {S : State Ω C} (e : Ω ≃ Fin k) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (hs : (domFin e S.dom).length = m * q) (hmq0 : 0 < m * q)
    {T : Set ((Fin q → Perm (Fin m)) × Perm (Fin q))} {u : Val}
    (hu : AnsC (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q)) u (tmJSet T)) :
    FunAll P f (.list [.list [encPerm (tmCsRhoP e E hs), encPerm (tmCsRhoP e E hs)⁻¹], u])
      (fun w cost => AnsC (domEquiv e S.dom) w (tmDomSet E T) ∧
        cost ≤ tmCsRelK (m * q)) := by
  set ρ := tmCsRhoP e E hs with hρ
  set c := Val.list [encPerm ρ, encPerm ρ⁻¹] with hc
  have w1 := wt_encPerm_le ρ
  have w2 := wt_encPerm_le ρ⁻¹
  have wc : c.wt ≤ 2 * ((encPerm ρ).wt + (encPerm ρ⁻¹).wt) + 6 := wt_list2_le _ _
  have h1 : 1 ≤ (m * q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h27 : (m * q + 1) ^ 2 ≤ (m * q + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have h37 : (m * q + 1) ^ 3 ≤ (m * q + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have h26 : (m * q + 1) ^ 2 ≤ (m * q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  rcases hu with ⟨rfl, hT⟩ | ⟨x, gs, rfl, hgl, hA⟩
  · -- the empty answer
    have hd := Det.ite_zero (t := mk2 (.call conj (mk2 (arg 0) (.get (arg 1) (.nat 0))))
      (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
        (.call mp (mk2 (arg 0) (.get (.get (arg 1) (.nat 1)) (.nat 1)))))) (P := P)
      (Det.length (Det.arg' (vs := [c, .list []]) (rest := []) (j := 1) rfl)) Det.nil
    refine FunAll.mono (FunDet.intro hf hd) fun w cost h => ⟨h.1 ▸ tmCs_rel_nil e E hT, ?_⟩
    have hc2 := h.2
    have wa := wt_list2_le c (Val.list [])
    have : (Val.list []).wt ≤ 5 := by decide
    unfold tmCsRelK
    simp only [List.length_nil] at hc2
    omega
  · set u := Val.list [encPerm x, encGroup gs] with hu
    have d0 := Det.arg' (P := P) (vs := [c, u]) (rest := []) (j := 0) (v := c) rfl
    have d1 := Det.arg' (P := P) (vs := [c, u]) (rest := []) (j := 1) (v := u) rfl
    have dx := Det.get' d1 (Det.nat 0) (vs := [encPerm x, encGroup gs]) (v := encPerm x) rfl
    have dg := Det.get' d1 (Det.nat 1) (vs := [encPerm x, encGroup gs]) (v := encGroup gs) rfl
    have dgn := Det.get' dg (Det.nat 0) (vs := [.nat (m * q), .list ((1 :: gs).map encPerm)])
      (v := .nat (m * q)) rfl
    have dgl := Det.get' dg (Det.nat 1) (vs := [.nat (m * q), .list ((1 :: gs).map encPerm)])
      (v := .list ((1 :: gs).map encPerm)) rfl
    have cx := Det.call (Det.mk2 d0 dx) (tmCs_conj_spec hconj hcp ρ x)
    have hM := map_spec hmp (c := c) (xs := (1 :: gs).map encPerm)
      (R := fun v w => ∀ σ : Perm (Fin (m * q)), v = encPerm σ → w = encPerm (ρ * σ * ρ⁻¹))
      (B := fun _ => tmCsConjK (m * q)) (by
        intro v hv
        obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hv
        refine FunAll.mono (tmCs_conj_spec hconj hcp ρ σ) fun w cost h => ⟨fun σ' h' => ?_, h.2⟩
        rw [h.1, encPerm_injective h'])
    set ws := (1 :: gs.map fun g => ρ * g * ρ⁻¹).map encPerm with hwsd
    have hws : ∀ ws', List.Forall₂ (fun v w => ∀ σ : Perm (Fin (m * q)), v = encPerm σ →
        w = encPerm (ρ * σ * ρ⁻¹)) ((1 :: gs).map encPerm) ws' → ws' = ws := by
      intro ws' h
      have := forall₂_map_eq (g := fun σ => encPerm (ρ * σ * ρ⁻¹)) (fun a _ w hw => hw a rfl) h
      rw [this, hwsd]
      simp
    set gs' := gs.map fun g => ρ * g * ρ⁻¹ with hgs'
    have hgl' : gs'.length ≤ (m * q) ^ 2 := by rw [hgs', List.length_map]; exact hgl
    have wG := wt_encGroup_le_sq hgl
    have wG' := wt_encGroup_le_sq hgl'
    have wL : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
      wt_le_wt_list (by simp [encGroup, encPerms])
    have wL' : (Val.list ws).wt < (encGroup gs').wt :=
      wt_le_wt_list (by simp [encGroup, encPerms, hwsd, hgs'])
    have hlen : ((1 :: gs).map encPerm).length + 1 ≤ (m * q + 1) ^ 2 := by
      simp only [List.length_map, List.length_cons]
      have : (m * q) ^ 2 + 2 ≤ (m * q + 1) ^ 2 := by nlinarith
      omega
    set W := (Val.list [c, .list ((1 :: gs).map encPerm)]).wt + (Val.list ws).wt + 1 with hW
    have wcl := wt_list2_le c (.list ((1 :: gs).map encPerm))
    have hWb : W ≤ 2000 * (m * q + 1) ^ 6 := by omega
    have hsum : (((1 :: gs).map encPerm).map fun _ => tmCsConjK (m * q)).sum ≤
        10 ^ 6 * (m * q + 1) ^ 5 := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul]
      unfold tmCsConjK
      calc ((1 :: gs).map encPerm).length * (10 ^ 6 * (m * q + 1) ^ 3)
          ≤ (m * q + 1) ^ 2 * (10 ^ 6 * (m * q + 1) ^ 3) := Nat.mul_le_mul_right _ (by omega)
        _ = 10 ^ 6 * (m * q + 1) ^ 5 := by ring
    have hloop : mapK * (((1 :: gs).map encPerm).length + 1) * W ≤ 2 * 10 ^ 6 * (m * q + 1) ^ 8 := by
      calc mapK * (((1 :: gs).map encPerm).length + 1) * W
          ≤ 1000 * (m * q + 1) ^ 2 * (2000 * (m * q + 1) ^ 6) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hlen) hWb
        _ = 2 * 10 ^ 6 * (m * q + 1) ^ 8 := by ring
    have hMd : FunDet P mp (.list [c, .list ((1 :: gs).map encPerm)]) (.list ws)
        (10 ^ 6 * (m * q + 1) ^ 5 + 2 * 10 ^ 6 * (m * q + 1) ^ 8) := by
      refine FunAll.mono hM fun w cost ⟨ws', hw, h2, hcost⟩ => ?_
      have := hws ws' h2
      subst this
      subst hw
      have hl := hloop
      rw [hW] at hl
      exact ⟨rfl, by omega⟩
    have cm := Det.call (Det.mk2 d0 dgl) hMd
    have dall := Det.mk2 cx (Det.mk2 dgn cm)
    have dite := Det.ite_pos (e := .nil)
      (Det.length (Det.arg' (P := P) (vs := [c, u]) (rest := []) (j := 1) (v := u) rfl))
      (by simp) dall
    refine FunAll.mono (FunDet.intro hf dite) fun w cost h => ⟨?_, ?_⟩
    · have hv : Val.list [encPerm (ρ * x * ρ⁻¹), Val.list [Val.nat (m * q), Val.list ws]] =
          Val.list [encPerm (ρ * x * ρ⁻¹), encGroup gs'] := by
        simp only [encGroup, encPerms, hwsd, hgs', List.map_cons]
      rw [h.1, hv]
      exact tmCs_rel_cons e E hs hgl hA
    · have hc2 := h.2
      have h58 : (m * q + 1) ^ 5 ≤ (m * q + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
      have h89 : (m * q + 1) ^ 8 ≤ (m * q + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
      have h69 : (m * q + 1) ^ 6 ≤ (m * q + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
      have wx := wt_encPerm_le x
      have wx' := wt_encPerm_le (ρ * x * ρ⁻¹)
      have wu := wt_list2_le (encPerm x) (encGroup gs)
      have wcu := wt_list2_le c u
      have wcx := wt_list2_le c (encPerm x)
      have wnl := wt_list2_le (Val.nat (m * q)) (Val.list ((1 :: gs).map encPerm))
      have wn := wt_nat_le (m * q)
      have wcl2 := wt_list2_le c (Val.list ((1 :: gs).map encPerm))
      have wnw := wt_list2_le (Val.nat (m * q)) (Val.list ws)
      have wtop := wt_list2_le (encPerm (ρ * x * ρ⁻¹)) (Val.list [Val.nat (m * q), Val.list ws])
      have hmq : m * q ≤ (m * q + 1) ^ 2 := by
        have := Nat.le_self_pow (n := 2) (by norm_num) (m * q + 1); omega
      have hlen2 : [encPerm x, encGroup gs].length = 2 := rfl
      have hu' : u.wt = (Val.list [encPerm x, encGroup gs]).wt := rfl
      have hck := (show tmCsConjK (m * q) = 10 ^ 6 * (m * q + 1) ^ 3 from rfl)
      unfold tmCsRelK
      rw [hlen2] at hc2
      omega

/-! ### The table of the numbering -/

/-- On `[[pos, cv, q], t]`: `pos[cv[t % q][t / q]]`, the domain position of the pair
`(t / q, t % q)`. -/
def tmCsTabEF : Expr :=
  .get (.get (arg 0) (.nat 0))
    (.get (.get (.get (arg 0) (.nat 1)) (.arith .mod (arg 1) (.get (arg 0) (.nat 2))))
      (.arith .div (arg 1) (.get (arg 0) (.nat 2))))

theorem tmCs_getElem?_mem {l : List Val} {i : ℕ} {v : Val} (h : l[i]? = some v) : v ∈ l :=
  List.mem_of_getElem? h

/-- **One entry of the table.** -/
theorem tmCs_tabE_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some tmCsTabEF)
    {S : State Ω C} (e : Ω ≃ Fin k) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (hs : (domFin e S.dom).length = m * q) (t : Fin (m * q)) :
    FunDet P f (.list [.list [posVal e S.dom, coordsVal e S E, .nat q], .nat t])
      (.nat (tmCsRhoP e E hs t))
      (100 * ((Val.list [posVal e S.dom, coordsVal e S E, .nat q]).wt + m * q + 10)) := by
  refine FunDet.intro hf ?_
  set ctx := Val.list [posVal e S.dom, coordsVal e S E, .nat q] with hctx
  have hq : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at t; exact t.elim0)
  have htq : (t : ℕ) / q < m := (Nat.div_lt_iff_lt_mul hq).2 t.2
  have htm : (t : ℕ) % q < q := Nat.mod_lt _ hq
  set j : Fin q := ⟨t % q, htm⟩ with hj
  set β : Fin m := ⟨t / q, htq⟩ with hβ
  set row := Val.list ((List.finRange m).map fun β => Val.nat ((e (E (β, j)).val : Fin k) : ℕ))
    with hrow
  set a : Fin k := e (E (β, j)).val with ha
  have d0 := Det.arg' (P := P) (vs := [ctx, .nat t]) (rest := []) (j := 0) (v := ctx) rfl
  have d1 := Det.arg' (P := P) (vs := [ctx, .nat t]) (rest := []) (j := 1) (v := .nat t) rfl
  have dpos := Det.get' d0 (Det.nat 0) (vs := [posVal e S.dom, coordsVal e S E, .nat q])
    (v := posVal e S.dom) rfl
  have dcv := Det.get' d0 (Det.nat 1) (vs := [posVal e S.dom, coordsVal e S E, .nat q])
    (v := coordsVal e S E) rfl
  have dq := Det.get' d0 (Det.nat 2) (vs := [posVal e S.dom, coordsVal e S E, .nat q])
    (v := .nat q) rfl
  have dmod := Det.arith' (op := .mod) d1 dq (z := t % q) rfl
  have ddiv := Det.arith' (op := .div) d1 dq (z := t / q) rfl
  have hr : ((List.finRange q).map fun j => natList ((List.finRange m).map
      fun β => ((e (E (β, j)).val : Fin k) : ℕ)))[(t : ℕ) % q]? = some row := by
    simp [hrow, hj, natList, htm, Function.comp_def]
  have drow := Det.get' dcv dmod hr
  have he : ((List.finRange m).map fun β => Val.nat ((e (E (β, j)).val : Fin k) : ℕ))[(t : ℕ) / q]?
      = some (.nat a) := by
    simp [ha, hβ, htq]
  have dent := Det.get' drow ddiv he
  have hp : ((List.finRange k).map fun i : Fin k => Val.nat (posOf (domNat e S.dom) i))[(a : ℕ)]?
      = some (.nat (tmCsRhoP e E hs t)) := by
    rw [tmCsRhoP_apply]
    have hsymm : finProdFinEquiv.symm t = (β, j) := by
      ext <;> simp [hβ, hj]
    simp [hsymm, ha]
  have dres := Det.get' dpos dent hp
  refine dres.mono ?_
  have w1 : (posVal e S.dom).wt < ctx.wt := wt_le_wt_list (by simp [hctx])
  have w2 : (coordsVal e S E).wt < ctx.wt := wt_le_wt_list (by simp [hctx])
  have w3 : (Val.nat q).wt < ctx.wt := wt_le_wt_list (by simp [hctx])
  have w4 : row.wt < (coordsVal e S E).wt := by
    have : coordsVal e S E = .list ((List.finRange q).map fun j => natList ((List.finRange m).map
      fun β => ((e (E (β, j)).val : Fin k) : ℕ))) := rfl
    rw [this]; exact wt_le_wt_list (List.mem_of_getElem? hr)
  have w5 : (Val.nat a).wt < row.wt := wt_le_wt_list (List.mem_of_getElem? he)
  have w6 : (Val.nat (tmCsRhoP e E hs t)).wt < (posVal e S.dom).wt :=
    wt_le_wt_list (List.mem_of_getElem? hp)
  have wa := wt_list2_le ctx (Val.nat t)
  have wt := wt_nat_le t
  have h1 : (t : ℕ) % q ≤ t := Nat.mod_le _ _
  have h2 : (t : ℕ) / q ≤ t := Nat.div_le_self _ _
  have h3 := t.2
  omega

/-- On `[sv, cv]`: the table `[ρ, ρ⁻¹]` of the numbering, with `ρ t = pos[cv[t % q][t / q]]`. -/
def tmCsTabF (dom rg tb inv : ℕ) : Expr :=
  .letE (.call dom (.get (arg 0) (.nat 2)))
  (.letE (.call (dom + 8) (mk2 (.var 1) (.get (arg 0) (.nat 0))))
  (.letE (.length (arg 1))
  (.letE (.length (.get (arg 1) (.nat 0)))
  (.letE (.call tb (mk2 (mk3 (.var 2) (arg 1) (.var 3))
    (.call rg (.arith .mul (.var 4) (.var 3)))))
  (mk2 (.var 5) (.call inv (.var 5)))))))

/-- The cost of the table, in `X = wt [sv, cv] + k`. -/
def tmCsTabK (X : ℕ) : ℕ := 10 ^ 10 * (X + 1) ^ 4

/-- Where the pieces of the table program sit. -/
structure TmCsTabAt (P : Program) (f dom rg tb tbe inv : ℕ) : Prop where
  hf : P.funs[f]? = some (tmCsTabF dom rg tb inv)
  hdom : DomAt P dom
  hrg : P.HasAt rg (rangeFuns rg)
  htb : P.HasAt tb (mapFuns tb tbe)
  htbe : P.funs[tbe]? = some tmCsTabEF
  hinv : P.HasAt inv (invFuns inv)

/-- **The table of the numbering.** -/
theorem tmCs_tab_spec {P : Program} {f dom rg tb tbe inv : ℕ} (hA : TmCsTabAt P f dom rg tb tbe inv)
    {S : State Ω C} (e : Ω ≃ Fin k) (c : C → ℕ) {sv : Val} (hsv : Canon e c sv S)
    {m q : ℕ} (E : Fin m × Fin q ≃ S.dom) (hs : (domFin e S.dom).length = m * q) (hq : 0 < q) :
    FunDet P f (.list [sv, coordsVal e S E])
      (.list [encPerm (tmCsRhoP e E hs), encPerm (tmCsRhoP e E hs)⁻¹])
      (tmCsTabK ((Val.list [sv, coordsVal e S E]).wt + k)) := by
  obtain ⟨gv, dv, xv, yv, hv, rv, -, hd, -, -, -, -, hsv'⟩ := hsv.val
  have hd' : dv = indVal e S.dom := DomVal.eq_indVal hd
  subst hd'
  refine FunDet.intro hA.hf ?_
  unfold tmCsTabF
  set ρ := tmCsRhoP e E hs with hρ
  set cv := coordsVal e S E with hcv
  set svl := [Val.nat k, gv, indVal e S.dom, xv, yv, hv, rv, boolVal S.floor, .nat S.h, .nat S.N]
    with hsvl
  set X := (Val.list [sv, cv]).wt + k with hX
  have wsv : sv.wt < (Val.list [sv, cv]).wt := wt_le_wt_list (by simp)
  have wcv : cv.wt < (Val.list [sv, cv]).wt := wt_le_wt_list (by simp)
  set rows := (List.finRange q).map fun j => natList ((List.finRange m).map
      fun β => ((e (E (β, j)).val : Fin k) : ℕ)) with hrows
  have hcvl : cv = .list rows := rfl
  have hmqk : m * q ≤ k := hs ▸ length_domFin_le
  -- step 1: the domain list
  have d0 := Det.arg' (P := P) (vs := [sv, cv]) (rest := []) (j := 0) (v := .list svl)
    (by simp [hsv', hsvl])
  have ddv := Det.get' d0 (Det.nat 2) (vs := svl) (v := indVal e S.dom) rfl
  have c1 := Det.call ddv (domList_spec hA.hdom e S.dom)
  -- step 2: the position table
  set env1 := [Val.list [sv, cv], natList (domNat e S.dom)] with henv1
  have e0 := Det.arg' (P := P) (vs := [sv, cv]) (rest := [natList (domNat e S.dom)]) (j := 0)
    (v := .list svl) (by simp [hsv', hsvl])
  have ek := Det.get' e0 (Det.nat 0) (vs := svl) (v := .nat k) rfl
  have e1 := Det.var' (P := P) (env := env1) (i := 1) (v := natList (domNat e S.dom)) rfl
  have c2 := Det.call (Det.mk2 e1 ek) (posTab_spec hA.hdom e S.dom)
  -- steps 3 and 4: `q` and `m`
  set env2 := env1 ++ [posVal e S.dom] with henv2
  have f1 := Det.arg' (P := P) (vs := [sv, cv]) (rest := [natList (domNat e S.dom), posVal e S.dom])
    (j := 1) (v := cv) rfl
  rw [hcvl] at f1
  have c3 := Det.length f1
  rw [show rows.length = q by simp [hrows]] at c3
  set env3 := env2 ++ [.nat q] with henv3
  have g1 := Det.arg' (P := P) (vs := [sv, cv])
    (rest := [natList (domNat e S.dom), posVal e S.dom, .nat q]) (j := 1) (v := cv) rfl
  rw [hcvl] at g1
  have hr0 : rows[0]? = some (.list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))) := by
    simp [hrows, natList, hq, Function.comp_def]
  have g0 := Det.get' g1 (Det.nat 0) hr0
  have c4 := Det.length g0
  rw [show ((List.finRange m).map fun β => Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ)).length
    = m by simp] at c4
  -- step 5: the table
  set env4 := env3 ++ [.nat m] with henv4
  set ctx := Val.list [posVal e S.dom, cv, .nat q] with hctx
  have h2 := Det.var' (P := P) (env := env4) (i := 2) (v := posVal e S.dom) rfl
  have h3 := Det.var' (P := P) (env := env4) (i := 3) (v := .nat q) rfl
  have h4 := Det.var' (P := P) (env := env4) (i := 4) (v := .nat m) rfl
  have h1 := Det.arg' (P := P) (vs := [sv, cv])
    (rest := [natList (domNat e S.dom), posVal e S.dom, .nat q, .nat m]) (j := 1) (v := cv) rfl
  have hctxd := Det.mk3 h2 h1 h3
  have hmul := Det.arith' (op := .mul) h4 h3 (z := m * q) rfl
  have hR : FunDet P rg (.nat (m * q)) (encFun fun i : Fin (m * q) => (i : ℕ))
      (loopModK * (m * q + 1) * ((Val.nat (m * q)).wt + m * q +
        (natList (List.range (m * q))).wt + 1)) := by
    rw [encFun_id]
    exact FunAll.mono (range_spec hA.hrg (m * q)) fun w c h => by
      obtain ⟨rfl, h2⟩ := h; exact ⟨rfl, h2⟩
  have c5r := Det.call hmul hR
  have hT := tabulate_spec hA.htb (c := ctx) (F := fun t => .nat (ρ t))
    (fun t => tmCs_tabE_spec hA.htbe e E hs t)
  have c5 := Det.call (Det.mk2 hctxd c5r) hT
  -- step 6: the inverse
  set env5 := env4 ++ [encPerm ρ] with henv5
  have k5 := Det.var' (P := P) (env := env5) (i := 5) (v := encPerm ρ) rfl
  have k5' := Det.var' (P := P) (env := env5) (i := 5) (v := encPerm ρ) rfl
  have c6 := Det.call k5' (inv_spec hA.hinv ρ)
  have dall := Det.mk2 k5 c6
  refine (Det.letE c1 (Det.letE c2 (Det.letE c3 (Det.letE c4 (Det.letE c5 dall))))).mono ?_
  -- the cost
  set Y := X + 1 with hY
  set W := (Val.list [sv, cv]).wt with hW
  have hY1 : 1 ≤ Y := by omega
  have hkY : k + 1 ≤ Y := by omega
  have hmqY : m * q + 1 ≤ Y := by omega
  have hWY : W + 1 ≤ Y := by omega
  have hY12 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hY34 : Y ^ 3 ≤ Y ^ 4 := Nat.pow_le_pow_right hY1 (by norm_num)
  have hk2 : (k + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hkY 2
  have hk3 : (k + 1) ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left hkY 3
  have hk4 : (k + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hkY 4
  have hq2 : (m * q + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hmqY 2
  have hq4 : (m * q + 1) ^ 4 ≤ Y ^ 4 := Nat.pow_le_pow_left hmqY 4
  have wind : (indVal e S.dom).wt < sv.wt := by
    rw [hsv']; exact wt_le_wt_list (by simp [hsvl])
  have wk : (Val.nat k).wt < sv.wt := by
    rw [hsv']; exact wt_le_wt_list (by simp [hsvl])
  have wdn := wt_domNat_le e S.dom
  have wpos := wt_posVal_le e S.dom
  have wq : q < cv.wt := by
    have := length_lt_wt_list rows
    rw [hcvl]; simpa [hrows] using this
  have wr0 : (Val.list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt < cv.wt := by
    rw [hcvl]; exact wt_le_wt_list (List.mem_of_getElem? hr0)
  have wm : m < (Val.list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))).wt := by
    have := length_lt_wt_list ((List.finRange m).map fun β =>
      Val.nat ((e (E (β, ⟨0, hq⟩)).val : Fin k) : ℕ))
    simpa using this
  have wnq := wt_nat_le q
  have wnm := wt_nat_le m
  have wnmq := wt_nat_le (m * q)
  have wctx : ctx.wt ≤ 2 * ((posVal e S.dom).wt + cv.wt + (Val.nat q).wt) + 7 := wt_list3_le _ _ _
  have wid := wt_ids_le (m * q)
  have wrg : (natList (List.range (m * q))).wt ≤ 4 * (m * q + 1) ^ 2 := by
    rw [← encFun_id]; exact wid
  have wρ := wt_encPerm_le ρ
  have wρi := wt_encPerm_le ρ⁻¹
  have wtab : (Val.list ((List.finRange (m * q)).map fun t => Val.nat (ρ t))).wt ≤
      4 * (m * q + 1) ^ 2 := wρ
  have wl1 := wt_list2_le (natList (domNat e S.dom)) (Val.nat k)
  have wl2 := wt_list2_le ctx (encFun fun i : Fin (m * q) => (i : ℕ))
  have wl3 := wt_list2_le (encPerm ρ) (encPerm ρ⁻¹)
  have wsc := wt_list2_le sv cv
  have hctxY : ctx.wt + m * q + 10 ≤ 40 * Y ^ 2 := by omega
  have P1 : m * q * (100 * (ctx.wt + m * q + 10)) ≤ 4000 * Y ^ 3 := by
    calc m * q * (100 * (ctx.wt + m * q + 10)) ≤ Y * (100 * (40 * Y ^ 2)) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 4000 * Y ^ 3 := by ring
  have P2 : mapK * (m * q + 1) * ((Val.list [ctx, encFun fun i : Fin (m * q) => (i : ℕ)]).wt +
      (Val.list ((List.finRange (m * q)).map fun t => Val.nat (ρ t))).wt + 1) ≤ 10 ^ 5 * Y ^ 3 := by
    calc _ ≤ 1000 * Y * (100 * Y ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hmqY) (by omega)
      _ = 10 ^ 5 * Y ^ 3 := by ring
  have P3 : loopModK * (m * q + 1) * ((Val.nat (m * q)).wt + m * q +
      (natList (List.range (m * q))).wt + 1) ≤ 10 ^ 4 * Y ^ 3 := by
    calc _ ≤ 1000 * Y * (10 * Y ^ 2) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hmqY) (by omega)
      _ = 10 ^ 4 * Y ^ 3 := by ring
  have hK1 : domListK = 10 ^ 6 := rfl
  have hK2 : posTabK = 10 ^ 7 := rfl
  have hK3 : invK = 100000 := rfl
  have hEq : (Val.list [Val.list [sv, cv], natList (domNat e S.dom)]).wt ≥ 0 := Nat.zero_le _
  have r1 : (Val.list [sv, Val.list rows]).wt = W := rfl
  have r2 : (Val.list [posVal e S.dom, cv, Val.nat q]).wt = ctx.wt := rfl
  have r3 : (Val.list [Val.list [posVal e S.dom, cv, Val.nat q],
      encFun fun i : Fin (m * q) => (i : ℕ)]).wt =
      (Val.list [ctx, encFun fun i : Fin (m * q) => (i : ℕ)]).wt := rfl
  have r4 : m * q * (100 * ((Val.list [posVal e S.dom, coordsVal e S E, Val.nat q]).wt +
      m * q + 10)) = m * q * (100 * (ctx.wt + m * q + 10)) := rfl
  show _ ≤ 10 ^ 10 * Y ^ 4
  rw [hK1, hK2, hK3]
  omega

end GI.Impl
