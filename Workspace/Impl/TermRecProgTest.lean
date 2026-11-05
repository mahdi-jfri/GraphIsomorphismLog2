module

public import Workspace.Impl.TermRecProg

@[expose] public section

/-!
# T5, the object test and the orbit predicate

`tmRi_test_spec`: on `[gens G, L h, L' h']` with `G` solvable, the function `b + 5` returns `0`
when no element of `G` carries `L h` to `L' h'`, and otherwise `[z, gens Aut_G(L h)]` such that
`z h⁻¹ h' ∈ G` carries `L h` to `L' h'` (`TmRiTestOut`). One call of
**SolvableCosetIntersection** on `G (h'⁻¹ h) ∩ h⁻¹ L h` (`tmRi_act_eq_iff`, `tmRi_mem_aut`).

`tmRi_objP_spec`: the predicate `b + 3` decides `SameOrb G`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

/-- An object as a triple `(color, generators, representative)`. -/
abbrev TmRiO (n : ℕ) := ℕ × List (Perm (Fin n)) × Perm (Fin n)

/-- The coset object of a triple. -/
abbrev tmRiObj (o : TmRiO n) : CObj ℕ (Perm (Fin n)) := tmGlObj o.1 o.2.1 o.2.2

/-- The stabilizer `h⁻¹ L h` of the object `(c, σL, h)`. -/
def tmRiStab (o : TmRiO n) : Subgroup (Perm (Fin n)) :=
  gens (o.2.1.map fun x => o.2.2⁻¹ * x * o.2.2⁻¹⁻¹)

/-- Every object stabilizer in `Z` normalizes `G`. -/
def TmRiListNorm (G : Subgroup (Perm (Fin n))) (Z : List (TmRiO n)) : Prop :=
  ∀ o ∈ Z, GI.Lang.Normalizes (tmRiStab o) G

/-- Every object stabilizer in `Z` lies in `H`. -/
def TmRiListIn (H : Subgroup (Perm (Fin n))) (Z : List (TmRiO n)) : Prop :=
  ∀ o ∈ Z, tmRiStab o ≤ H

theorem TmRiListNorm.bot (Z : List (TmRiO n)) : TmRiListNorm (gens ([] : List (Perm (Fin n)))) Z := by
  intro o _ k _ g hg
  have hbot : gens ([] : List (Perm (Fin n))) = ⊥ := by
    simp [gens]
  rw [hbot, Subgroup.mem_bot] at hg ⊢
  simp [hg]

theorem TmRiListNorm.sub {G : Subgroup (Perm (Fin n))} {Z Z' : List (TmRiO n)}
    (h : TmRiListNorm G Z) (hs : ∀ o ∈ Z', o ∈ Z) : TmRiListNorm G Z' :=
  fun o ho => h o (hs o ho)

theorem TmRiListIn.sub {H : Subgroup (Perm (Fin n))} {Z Z' : List (TmRiO n)}
    (h : TmRiListIn H Z) (hs : ∀ o ∈ Z', o ∈ Z) : TmRiListIn H Z' :=
  fun o ho => h o (hs o ho)

theorem TmRiListIn.norm_of {H A : Subgroup (Perm (Fin n))} {Z : List (TmRiO n)}
    (hZ : TmRiListIn H Z) (hNA : GI.Multicoset.Normalizes H A) : TmRiListNorm A Z :=
  fun o ho k hk g hg => hNA k (hZ o ho hk) g hg

theorem TmRiListIn.norm_self {H : Subgroup (Perm (Fin n))} {Z : List (TmRiO n)}
    (hZ : TmRiListIn H Z) : TmRiListNorm H Z :=
  hZ.norm_of (fun _ hh _ hg => H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh))

theorem mem_tmRiStab_iff {o : TmRiO n} {g : Perm (Fin n)} :
    g ∈ tmRiStab o ↔ tmRiObj o ↼ g = tmRiObj o := by
  obtain ⟨c, σL, h⟩ := o
  rw [tmRiStab, tmRiObj, tmRi_act_eq_iff (fun _ => rfl)]
  simp

theorem tmRiStab_le_of {H : Subgroup (Perm (Fin n))} {o : TmRiO n}
    (hL : gens o.2.1 ≤ H) (hh : o.2.2 ∈ H) : tmRiStab o ≤ H := by
  intro g hg
  rw [tmRiStab, tmRi_mem_conj, inv_inv] at hg
  have h1 : o.2.2 * g * o.2.2⁻¹ ∈ H := hL hg
  have h2 : o.2.2⁻¹ * (o.2.2 * g * o.2.2⁻¹) * o.2.2 ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh
  simpa [mul_assoc] using h2

theorem tmRiStab_le_of_sameOrb {B : Subgroup (Perm (Fin n))} {o o' : TmRiO n}
    (ho : tmRiStab o ≤ B) {a : Perm (Fin n)} (ha : a ∈ B) (hact : tmRiObj o ↼ a = tmRiObj o') :
    tmRiStab o' ≤ B := by
  intro g hg
  rw [mem_tmRiStab_iff, ← hact, act_act] at hg
  have h1 : tmRiObj o ↼ (a * g * a⁻¹) = tmRiObj o := by
    have := congrArg (· ↼ a⁻¹) hg
    simpa [act_act] using this
  have h2 : a * g * a⁻¹ ∈ B := ho (mem_tmRiStab_iff.2 h1)
  have h3 : a⁻¹ * (a * g * a⁻¹) * a ∈ B := B.mul_mem (B.mul_mem (B.inv_mem ha) h2) ha
  simpa [mul_assoc] using h3

theorem TmRiListNorm.append {G : Subgroup (Perm (Fin n))} {X Y : List (TmRiO n)}
    (hX : TmRiListNorm G X) (hY : TmRiListNorm G Y) : TmRiListNorm G (X ++ Y) := by
  intro o ho
  rcases List.mem_append.1 ho with ho | ho
  · exact hX o ho
  · exact hY o ho

theorem TmRiListIn.append {H : Subgroup (Perm (Fin n))} {X Y : List (TmRiO n)}
    (hX : TmRiListIn H X) (hY : TmRiListIn H Y) : TmRiListIn H (X ++ Y) := by
  intro o ho
  rcases List.mem_append.1 ho with ho | ho
  · exact hX o ho
  · exact hY o ho

theorem TmRiListIn.mono {H K : Subgroup (Perm (Fin n))} {Z : List (TmRiO n)}
    (h : TmRiListIn H Z) (hHK : H ≤ K) : TmRiListIn K Z :=
  fun o ho => (h o ho).trans hHK

/-- The result of the object test. -/
def TmRiTestOut (G : Subgroup (Perm (Fin n))) (o o' : TmRiO n) (w : Val) : Prop :=
  (w = .nat 0 ∧ ∀ g ∈ G, tmRiObj o ↼ g ≠ tmRiObj o') ∨
  ∃ (z : Perm (Fin n)) (L : Val), w = .list [encPerm z, L] ∧ z * (o.2.2⁻¹ * o'.2.2) ∈ G ∧
    tmRiObj o ↼ (z * (o.2.2⁻¹ * o'.2.2)) = tmRiObj o' ∧ GensVal n L (Aut G (tmRiObj o))

theorem TmRiTestOut.wt_le {G : Subgroup (Perm (Fin n))} {o o' : TmRiO n} {w : Val}
    (h : TmRiTestOut G o o' w) : w.wt ≤ 40 * (n + 1) ^ 6 := by
  have h1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨z, L, rfl, -, -, hL⟩
  · have : (Val.nat 0).wt = 2 := by decide
    omega
  · have := wt_list2_le (encPerm z) L
    have := wt_encPerm_le z
    have := GensVal.wt_le hL
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem TmRiTestOut.zero_iff {G : Subgroup (Perm (Fin n))} {o o' : TmRiO n} {w : Val}
    (h : TmRiTestOut G o o' w) : w.isNatNum = 1 ↔ ¬ ∃ g ∈ G, tmRiObj o ↼ g = tmRiObj o' := by
  rcases h with ⟨rfl, h⟩ | ⟨z, L, rfl, hz, he, -⟩
  · simp only [Val.isNatNum, true_iff]
    rintro ⟨g, hg, he⟩
    exact h g hg he
  · simp only [Val.isNatNum, zero_ne_one, false_iff, not_not]
    exact ⟨_, hz, he⟩

/-- The weight of an object with at most `n²` generators. -/
theorem tmRi_wt_obj (o : TmRiO n) (hl : o.2.1.length ≤ n ^ 2) :
    (tmGlObjVal o).wt ≤ 1000 * (n + 1) ^ 6 + 2 * o.1 := by
  have h1 := wt_list3_le (.nat o.1) (encGroup o.2.1) (encPerm o.2.2)
  have h2 := wt_nat_le o.1
  have h3 := wt_encGroup_le_sq hl
  have h4 := wt_encPerm_le o.2.2
  have : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  show (Val.list [.nat o.1, encGroup o.2.1, encPerm o.2.2]).wt ≤ _
  omega

/-- The cost bound of the object test, for colors at most `C`. -/
def tmRiTestC (psci : Prim) (n C : ℕ) : ℕ :=
  psci.boundSize (10 ^ 4 * (n + 1) ^ 6) + 10 ^ 10 * (n + 1) ^ 8 + 1000 * C

open Classical in
/-- **The object test.** -/
theorem tmRi_test_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {gs : List (Perm (Fin n))}
    {o o' : TmRiO n} (hsol : GI.Lang.Normalizes (tmRiStab o) (gens gs))
    (hgl : gs.length ≤ n ^ 2)
    (hl : o.2.1.length ≤ n ^ 2) (hl' : o'.2.1.length ≤ n ^ 2)
    (hL : o.1 = o'.1 → gens o.2.1 = gens o'.2.1) {C : ℕ} (hC : o.1 ≤ C) (hC' : o'.1 ≤ C) :
    FunAll P (b + 5) (.list [encGroup gs, tmGlObjVal o, tmGlObjVal o'])
      (fun w cost => TmRiTestOut (gens gs) o o' w ∧
        cost ≤ tmRiTestC (solvableCosetIntersectionPrim hsci) n C) := by
  obtain ⟨c, σL, h⟩ := o
  obtain ⟨c', σL', h'⟩ := o'
  simp only [tmRiStab] at hl hl' hL hC hC' hsol ⊢
  set vs : List Val := [encGroup gs, tmGlObjVal (c, σL, h), tmGlObjVal (c', σL', h')] with hvs
  set W := (Val.list vs).wt with hW
  have hwG := wt_encGroup_le_sq hgl
  have hwo := tmRi_wt_obj (c, σL, h) hl
  have hwo' := tmRi_wt_obj (c', σL', h') hl'
  have hW3 : W ≤ 2 * ((encGroup gs).wt + (tmGlObjVal (c, σL, h)).wt +
      (tmGlObjVal (c', σL', h')).wt) + 7 := wt_list3_le _ _ _
  have hn6 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn4 : (n + 1) ^ 4 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn3 : (n + 1) ^ 3 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn81 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hn26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only at hwo hwo'
  have hWb : W ≤ 5000 * (n + 1) ^ 6 + 8 * C + 10 := by omega
  -- the colors
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have d2 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 2) rfl
  have dc := Det.get' d1 (Det.nat 0) (v := .nat c) rfl
  have dc' := Det.get' d2 (Det.nat 0) (v := .nat c') rfl
  have deq := Det.arith' (op := .eq) dc dc' rfl
  have hcw := wt_nat_le c
  have hcw' := wt_nat_le c'
  have hC1 : (Val.nat c).wt ≤ C + 2 := by omega
  have hC1' : (Val.nat c').wt ≤ C + 2 := by omega
  refine FunAll.intro hP.test ((sup_ite deq (R := fun w cost => TmRiTestOut (gens gs) (c, σL, h)
    (c', σL', h') w ∧ cost ≤ (solvableCosetIntersectionPrim hsci).boundSize (10 ^ 4 * (n + 1) ^ 6) +
      10 ^ 9 * (n + 1) ^ 8 + 50 * W) ?_ ?_).mono ?_)
  rotate_right
  · rintro w cost ⟨ce, ⟨hw, hce⟩, hc⟩
    refine ⟨hw, ?_⟩
    have := hw.wt_le
    have e : BinOp.eval .eq c c' ≤ 1 := by simp only [BinOp.eval]; split <;> omega
    unfold tmRiTestC
    omega
  · intro hne
    have hcc : c = c' := by
      by_contra hcc; simp [BinOp.eval, hcc] at hne
    subst hcc
    -- `h⁻¹`, `h'⁻¹`
    have dh := Det.get' d1 (Det.nat 2) (v := encPerm h) rfl
    have dh' := Det.get' d2 (Det.nat 2) (v := encPerm h') rfl
    have di := Det.call dh (inv_spec hP.inv h)
    have di' := Det.call dh' (inv_spec hP.inv h')
    have hwh := wt_encPerm_le h
    have hwh' := wt_encPerm_le h'
    have hwhi := wt_encPerm_le h⁻¹
    have hwhi' := wt_encPerm_le h'⁻¹
    refine EvalAll.letE di fun v1 c1 hv1 => ?_
    obtain ⟨rfl, hc1⟩ := hv1
    have d2' := Det.arg' (P := P) (vs := vs) (rest := [encPerm h⁻¹]) (j := 2) rfl
    have di2 := Det.call (Det.get' d2' (Det.nat 2) (v := encPerm h') rfl) (inv_spec hP.inv h')
    refine EvalAll.letE di2 fun v2 c2 hv2 => ?_
    obtain ⟨rfl, hc2⟩ := hv2
    -- the conjugate group `h⁻¹ L h`
    set env3 : List Val := [.list vs, encPerm h⁻¹, encPerm h'⁻¹] with henv3
    have e1 := Det.arg' (P := P) (vs := vs) (rest := [encPerm h⁻¹, encPerm h'⁻¹]) (j := 1) rfl
    have dgo := Det.get' e1 (Det.nat 1) (v := encGroup σL) rfl
    have dn := Det.get' dgo (Det.nat 0) (v := .nat n) rfl
    have dlist := Det.get' dgo (Det.nat 1) (v := .list ((1 :: σL).map encPerm)) rfl
    have dhh := Det.get' e1 (Det.nat 2) (v := encPerm h) rfl
    have dv1 := Det.var' (P := P) (env := env3) (i := 1) (v := encPerm h⁻¹) rfl
    have dss := Det.mk2 dv1 dhh
    have hcm := supConjMap_det hP.comp hP.cj hP.mapConj h⁻¹ hl
    rw [inv_inv] at hcm
    have dcm := Det.call (Det.mk2 dss dlist) hcm
    have dK := Det.mk2 dn dcm
    have hKl : (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹).length ≤ n ^ 2 := by simpa using hl
    have hwK := wt_encGroup_le_sq hKl
    have eK : Val.list [.nat n, .list (List.map encPerm (1 :: σL.map fun x => h⁻¹ * x * h))] =
        encGroup (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹) := by simp [encGroup, GI.Cited.encPerms]
    rw [eK] at dK
    refine EvalAll.letE dK fun v3 c3 hv3 => ?_
    obtain ⟨rfl, hc3⟩ := hv3
    -- `h'⁻¹ h`
    set env4 : List Val := env3 ++ [encGroup (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹)] with henv4
    have e1' := Det.arg' (P := P) (vs := vs)
      (rest := [encPerm h⁻¹, encPerm h'⁻¹, encGroup (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹)]) (j := 1) rfl
    have dhh' := Det.get' e1' (Det.nat 2) (v := encPerm h) rfl
    have dv2 := Det.var' (P := P) (env := env4) (i := 2) (v := encPerm h'⁻¹) rfl
    have dx := Det.call (Det.mk2 dv2 dhh') (compose_spec hP.comp h'⁻¹ h)
    refine EvalAll.letE dx fun v4 c4 hv4 => ?_
    obtain ⟨rfl, hc4⟩ := hv4
    -- the coset intersection
    set env5 : List Val := env4 ++ [encPerm (h'⁻¹ * h)] with henv5
    have e0 := Det.arg' (P := P) (vs := vs)
      (rest := [encPerm h⁻¹, encPerm h'⁻¹, encGroup (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹),
        encPerm (h'⁻¹ * h)]) (j := 0) rfl
    have dv3 := Det.var' (P := P) (env := env5) (i := 3)
      (v := encGroup (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹)) rfl
    have dv4 := Det.var' (P := P) (env := env5) (i := 4) (v := encPerm (h'⁻¹ * h)) rfl
    have dsa := Det.mk3 e0 dv3 dv4
    have hsz : (Val.list [encGroup gs, encGroup (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹),
        encPerm (h'⁻¹ * h)]).size ≤ 10 ^ 4 * (n + 1) ^ 6 := by
      have := wt_list3_le (encGroup gs) (encGroup (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹))
        (encPerm (h'⁻¹ * h))
      have := wt_encPerm_le (h'⁻¹ * h)
      have : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      exact (Val.size_le_wt _).trans (by omega)
    have hb := (solvableCosetIntersectionPrim hsci).bound_le hsz
    refine (solvableCosetIntersection_call hsci hP.sci dsa ⟨gs, rfl, rfl⟩ hsol
      ⟨_, rfl, rfl⟩ (x := h'⁻¹ * h)).mono fun w cost hw => ⟨?_, ?_⟩
    · obtain ⟨hout, -⟩ := hw
      rcases hout with ⟨rfl, hno⟩ | ⟨z, ⟨g, hg, rfl⟩, hz, L, rfl, hL'⟩
      · refine Or.inl ⟨rfl, fun g hg he => hno g hg ?_⟩
        exact ((tmRi_act_eq_iff hL h h' g).1 he).2
      · refine Or.inr ⟨g * (h'⁻¹ * h), L, rfl, ?_, ?_, ?_⟩
        · simpa [mul_assoc] using hg
        · rw [show g * (h'⁻¹ * h) * (h⁻¹ * h') = g by group]
          exact (tmRi_act_eq_iff hL h h' g).2 ⟨rfl, hz⟩
        · have e : Aut (gens gs) (tmRiObj (c, σL, h)) =
              gens gs ⊓ gens (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹) := by
            ext k; exact tmRi_mem_aut k
          rw [e]; exact hL'
    · have hcost := hw.2
      have hww := CosetIntOut.wt_le hw.1
      have h8 : invK * (n + 1) ^ 4 ≤ invK * (n + 1) ^ 8 := Nat.mul_le_mul_left _ hn4
      have h9 : permK * (n + 1) ^ 3 ≤ permK * (n + 1) ^ 8 := Nat.mul_le_mul_left _ hn3
      have hwx := wt_encPerm_le (h'⁻¹ * h)
      have hss := wt_list2_le (encPerm h⁻¹) (encPerm h)
      have hlw : (Val.list ((1 :: σL).map encPerm)).wt ≤ 320 * (n + 1) ^ 6 :=
        (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans (wt_encGroup_le_sq hl)
      have hcmw := wt_list2_le (.list [encPerm h⁻¹, encPerm h]) (.list ((1 :: σL).map encPerm))
      have hlw' : (Val.list ((1 :: σL.map fun x => h⁻¹ * x * h).map encPerm)).wt ≤
          320 * (n + 1) ^ 6 := by
        have := wt_encGroup_le_sq (hs := σL.map fun x => h⁻¹ * x * h) (by simpa using hl)
        exact (wt_le_wt_list (vs := [.nat n, _]) (by simp)).le.trans this
      have hxw := wt_list2_le (encPerm h'⁻¹) (encPerm h)
      have hsaw := wt_list3_le (encGroup gs) (encGroup (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹))
        (encPerm (h'⁻¹ * h))
      have hgw : (encGroup σL).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hl
      have hnw : (Val.nat n).wt ≤ n + 2 := wt_nat_le n
      have hn1 : n + 1 ≤ (n + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
      have hl4 := wt_list_mono (show [Val.list vs, encPerm h⁻¹] <+: [Val.list vs, encPerm h⁻¹,
        encPerm h'⁻¹] from ⟨_, rfl⟩)
      simp only [invK, permK] at *
      clear dsa dv3 dv4 e0 dx dv2 dhh' e1' dK dcm dss dv1 dhh dlist dn dgo e1 di di' dh dh' deq
        dc dc' d1 d2 hcm di2 d2'
      simp only [inv_inv] at *
      have hW5 : (Val.list vs).wt ≤ W := le_rfl
      have he1 : BinOp.eval .eq c c = 1 := by simp [BinOp.eval]
      omega
  · -- different colors
    intro heq
    have hcc : c ≠ c' := by
      intro hcc; simp [BinOp.eval, hcc] at heq
    refine (Det.nat (P := P) (env := [.list vs]) 0).post fun cost hc => ⟨Or.inl ⟨rfl, ?_⟩, ?_⟩
    · intro g _ he
      exact hcc ((tmRi_act_eq_iff hL h h' g).1 he).1
    · have : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
      omega

theorem tmRi_isNatNum_le (v : Val) : v.isNatNum ≤ 1 := by cases v <;> simp [Val.isNatNum]

open Classical in
theorem TmRiTestOut.isNatNum_eq {G : Subgroup (Perm (Fin n))} {o o' : TmRiO n} {w : Val}
    (h : TmRiTestOut G o o' w) :
    w.isNatNum = if SameOrb G (tmRiObj o) (tmRiObj o') then 0 else 1 := by
  have h1 := h.zero_iff
  have h2 := tmRi_isNatNum_le w
  unfold SameOrb
  split_ifs with hs
  · by_contra hne
    exact (h1.1 (by omega)) hs
  · exact h1.2 hs

/-- The cost bound of the orbit predicate. -/
def tmRiObjPC (psci : Prim) (n C : ℕ) : ℕ := tmRiTestC psci n C + 10 ^ 6 * (n + 1) ^ 6 + 1000 * C

open Classical in
/-- **The orbit predicate**: on `[[gens G, o], z]`, whether `z` lies in the `G`-orbit of `o`. -/
theorem tmRi_objP_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {gs : List (Perm (Fin n))}
    {o o' : TmRiO n} (hsol : GI.Lang.Normalizes (tmRiStab o) (gens gs))
    (hgl : gs.length ≤ n ^ 2)
    (hl : o.2.1.length ≤ n ^ 2) (hl' : o'.2.1.length ≤ n ^ 2)
    (hL : o.1 = o'.1 → gens o.2.1 = gens o'.2.1) {C : ℕ} (hC : o.1 ≤ C) (hC' : o'.1 ≤ C) :
    FunDet P (b + 3) (.list [.list [encGroup gs, tmGlObjVal o], tmGlObjVal o'])
      (boolVal (decide (SameOrb (gens gs) (tmRiObj o) (tmRiObj o'))))
      (tmRiObjPC (solvableCosetIntersectionPrim hsci) n C) := by
  set c : Val := .list [encGroup gs, tmGlObjVal o] with hc
  set vs : List Val := [c, tmGlObjVal o'] with hvs
  have d0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have dg := Det.get' d0 (Det.nat 0) (v := encGroup gs) rfl
  have dobj := Det.get' d0 (Det.nat 1) (v := tmGlObjVal o) rfl
  have hwo := tmRi_wt_obj o hl
  have hwo' := tmRi_wt_obj o' hl'
  have hwG := wt_encGroup_le_sq hgl
  have hcw : c.wt ≤ 2 * ((encGroup gs).wt + (tmGlObjVal o).wt) + 6 := wt_list2_le _ _
  have hvw : (Val.list vs).wt ≤ 2 * (c.wt + (tmGlObjVal o').wt) + 6 := wt_list2_le _ _
  have h3 := wt_list3_le (encGroup gs) (tmGlObjVal o) (tmGlObjVal o')
  have h1n : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hVW : (Val.list vs).wt ≤ 10 ^ 4 * (n + 1) ^ 6 + 16 * C + 40 := by omega
  obtain ⟨CA, dargs, hCA⟩ : ∃ CA, Det P [.list vs] (mk3 (.get (arg 0) (.nat 0))
      (.get (arg 0) (.nat 1)) (arg 1)) (.list [encGroup gs, tmGlObjVal o, tmGlObjVal o']) CA ∧
      CA ≤ 20 * (Val.list vs).wt + 3 * (Val.list [encGroup gs, tmGlObjVal o, tmGlObjVal o']).wt +
        3 * (encGroup gs).wt + 3 * (tmGlObjVal o).wt + 40 :=
    ⟨_, Det.mk3 dg dobj d1, by omega⟩
  have dcall := EvalAll.call_funAll (f := b + 5) dargs (Q := fun w cw => TmRiTestOut (gens gs) o o' w ∧
      cw ≤ CA + tmRiTestC (solvableCosetIntersectionPrim hsci) n C + w.wt + 1) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    exact (tmRi_test_spec hP hsol hgl hl hl' hL hC hC').mono fun w cb h => ⟨h.1, by omega⟩
  have dis : Det P [.list vs] (.isNat (.call (b + 5) (mk3 (.get (arg 0) (.nat 0))
      (.get (arg 0) (.nat 1)) (arg 1))))
      (.nat (if SameOrb (gens gs) (tmRiObj o) (tmRiObj o') then 0 else 1))
      (CA + tmRiTestC (solvableCosetIntersectionPrim hsci) n C + 40 * (n + 1) ^ 6 + 5) :=
    EvalAll.isNat dcall fun va ca h => by
      refine ⟨by rw [h.1.isNatNum_eq], ?_⟩
      have := h.1.wt_le
      have : (Val.nat va.isNatNum).wt ≤ 3 := by
        have := wt_nat_le va.isNatNum; have := tmRi_isNatNum_le va; omega
      omega
  refine FunDet.intro hP.objP ((Det.ite' dis (Det.nat 0) (Det.nat 1)).mono ?_ |>.post
    fun cost hcost => ⟨?_, hcost⟩)
  rotate_left
  · by_cases hs : SameOrb (gens gs) (tmRiObj o) (tmRiObj o') <;> simp [hs]
  · have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have : (Val.nat 1).wt ≤ 3 := wt_nat_le 1
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    unfold tmRiObjPC
    omega

end GI.Impl
