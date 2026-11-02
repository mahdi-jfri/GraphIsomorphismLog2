import Workspace.Impl.TermJGMath
import Workspace.Impl.TermJProgWr

/-!
# Generators of `G|_dom` on `Fin (m q)` (program)

On `[sv, [ρ, ρ⁻¹]]` (`sv` the state value, `ρ = tmCsRhoP e E hs` the table of
`TermCosetRel.lean`), `tmJGF` returns the generators `gs` of `G` stored in `sv` (with the
identity in front), restricted to the domain positions (`restrList_spec`) and conjugated by
`ρ⁻¹` (`tmCs_conj_spec`). By `tmJ_gens_dom` they generate the domain group on the pairs.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv
open GI.Cited (Val encPerm encGroup encPerms gens)

variable {Ω C : Type} {k : ℕ}

/-- Conjugation by `ρ⁻¹` of a permutation of the positions is the relabeling by `ρ.symm`. -/
theorem tmJ_encPerm_conj (e : Ω ≃ Fin k) {S : State Ω C} {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (hs : (domFin e S.dom).length = m * q) (x : Perm (Fin (domFin e S.dom).length)) :
    encPerm ((tmCsRhoP e E hs)⁻¹ * (finCongr hs).permCongr x * ((tmCsRhoP e E hs)⁻¹)⁻¹) =
      encPerm (toFin (tmCsRho e E).symm x) := by
  congr 1

/-- The cast of a permutation does not change its value. -/
theorem tmJ_encPerm_cast {s n : ℕ} (h : s = n) (x : Perm (Fin s)) :
    encPerm ((finCongr h).permCongr x) = encPerm x := by
  subst h
  congr 1

/-- On `[sv, [ρ, ρ⁻¹]]`: the generators of `G|_dom` on `Fin (m q)`. -/
def tmJGF (dom mpc : ℕ) : Expr :=
  .letE (.call dom (.get (arg 0) (.nat 2)))
  (.letE (.call (dom + 8) (mk2 (.var 1) (.get (arg 0) (.nat 0))))
  (.letE (.call (dom + 22) (mk2 (mk2 (.var 1) (.var 2)) (.get (.get (arg 0) (.nat 1)) (.nat 1))))
  (.call mpc (mk2 (mk2 (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 0))) (.var 3)))))

/-- The cost of `tmJGF`, in `X = wt [sv, tab] + k`. -/
def tmJGK (X : ℕ) : ℕ := 10 ^ 17 * (X + 1) ^ 21

/-- Where the pieces of `tmJGF` sit. -/
structure TmJGAt (P : Program) (f dom mpc cj cp : ℕ) : Prop where
  hf : P.funs[f]? = some (tmJGF dom mpc)
  hdom : DomAt P dom
  hmpc : P.HasAt mpc (mapFuns mpc cj)
  hcj : P.funs[cj]? = some (tmCsConjF cp)
  hcp : P.HasAt cp (composeFuns cp)

/-- The generators of `G|_dom` on `Fin (m q)`, from the generators `gs` of `G`. -/
noncomputable def tmJGList (e : Ω ≃ Fin k) (S : State Ω C) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    (gs : List (Perm (Fin k))) : List (Perm (Fin (m * q))) :=
  ((1 :: gs).map (restrP e S.G S.dom S.dom_inv)).map (toFin (tmCsRho e E).symm)

theorem tmJGList_gens (e : Ω ≃ Fin k) (S : State Ω C) {m q : ℕ} (E : Fin m × Fin q ≃ S.dom)
    {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e S.G) :
    gens (tmJGList e S E gs) =
      (tmJGE S E).map (toFin (finProdFinEquiv : Fin m × Fin q ≃ Fin (m * q))).toMonoidHom := by
  apply tmJ_gens_dom
  rw [← hgs]
  unfold gens
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg

set_option maxHeartbeats 2000000 in
theorem tmJ_g_spec {P : Program} {f dom mpc cj cp : ℕ} (hA : TmJGAt P f dom mpc cj cp)
    (e : Ω ≃ Fin k) (c : C → ℕ) {S : State Ω C} {sv : Val} (hsv : Canon e c sv S) {m q : ℕ}
    (E : Fin m × Fin q ≃ S.dom) (hs : (domFin e S.dom).length = m * q) :
    ∃ gs : List (Perm (Fin k)), gens gs = groupFin e S.G ∧ gs.length ≤ k ^ 2 ∧
      FunDet P f (.list [sv, .list [encPerm (tmCsRhoP e E hs), encPerm (tmCsRhoP e E hs)⁻¹]])
        (.list ((tmJGList e S E gs).map encPerm))
        (tmJGK ((Val.list [sv, .list [encPerm (tmCsRhoP e E hs), encPerm (tmCsRhoP e E hs)⁻¹]]).wt
          + k)) := by
  obtain ⟨gv, dv, xv, yv, hv, rv, ⟨gs, hgv, hgs, hgl⟩, hd, -, -, -, -, hsv'⟩ := hsv.val
  have hd' : dv = indVal e S.dom := DomVal.eq_indVal hd
  subst hd' hgv
  refine ⟨gs, hgs, hgl, FunDet.intro hA.hf ?_⟩
  unfold tmJGF
  set ρ := tmCsRhoP e E hs with hρ
  have hgm : ∀ g ∈ 1 :: gs, g ∈ groupFin e S.G := by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact Subgroup.one_mem _
    · rw [← hgs]; exact Subgroup.subset_closure hg
  set svl := [Val.nat k, encGroup gs, indVal e S.dom, xv, yv, hv, rv, boolVal S.floor,
    .nat S.h, .nat S.N] with hsvl
  have a0 := Det.arg' (P := P) (vs := [sv, .list [encPerm ρ, encPerm ρ⁻¹]]) (rest := []) (j := 0)
    (v := .list svl) (by simp [hsv', hsvl])
  have c1 := Det.call (Det.get' a0 (Det.nat 2) (vs := svl) (v := indVal e S.dom) rfl)
    (domList_spec hA.hdom e S.dom)
  have b0 := Det.arg' (P := P) (vs := [sv, .list [encPerm ρ, encPerm ρ⁻¹]])
    (rest := [natList (domNat e S.dom)]) (j := 0) (v := .list svl) (by simp [hsv', hsvl])
  have v1 := Det.var' (P := P) (env := [Val.list [sv, .list [encPerm ρ, encPerm ρ⁻¹]],
    natList (domNat e S.dom)]) (i := 1) (v := natList (domNat e S.dom)) rfl
  have c2 := Det.call (Det.mk2 v1 (Det.get' b0 (Det.nat 0) (vs := svl) (v := .nat k) rfl))
    (posTab_spec hA.hdom e S.dom)
  set env2 := [Val.list [sv, .list [encPerm ρ, encPerm ρ⁻¹]], natList (domNat e S.dom),
    posVal e S.dom] with henv2
  have b0' := Det.arg' (P := P) (vs := [sv, .list [encPerm ρ, encPerm ρ⁻¹]])
    (rest := [natList (domNat e S.dom), posVal e S.dom]) (j := 0) (v := .list svl)
    (by simp [hsv', hsvl])
  have w1 := Det.var' (P := P) (env := env2) (i := 1) (v := natList (domNat e S.dom)) rfl
  have w2 := Det.var' (P := P) (env := env2) (i := 2) (v := posVal e S.dom) rfl
  have gl := Det.get' (Det.get' b0' (Det.nat 1) (vs := svl) (v := encGroup gs) rfl) (Det.nat 1)
    (vs := [Val.nat k, .list ((1 :: gs).map encPerm)]) (v := .list ((1 :: gs).map encPerm)) rfl
  have c3 := Det.call (Det.mk2 (Det.mk2 w1 w2) gl)
    (restrList_spec e S.G S.dom S.dom_inv hA.hdom hgm)
  set env3 := env2 ++ [.list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))]
    with henv3
  have d1 := Det.arg' (P := P) (vs := [sv, .list [encPerm ρ, encPerm ρ⁻¹]])
    (rest := [natList (domNat e S.dom), posVal e S.dom,
      .list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))]) (j := 1)
    (v := .list [encPerm ρ, encPerm ρ⁻¹]) rfl
  have t1 := Det.get' d1 (Det.nat 1) (vs := [encPerm ρ, encPerm ρ⁻¹]) (v := encPerm ρ⁻¹) rfl
  have t0 := Det.get' d1 (Det.nat 0) (vs := [encPerm ρ, encPerm ρ⁻¹]) (v := encPerm ρ) rfl
  rw [show encPerm ρ = encPerm ρ⁻¹⁻¹ by rw [inv_inv]] at t0
  have v3 := Det.var' (P := P) (env := env3) (i := 3)
    (v := .list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))) rfl
  have hM := mapList_spec hA.hmpc (1 :: gs) (fun g => encPerm (restrP e S.G S.dom S.dom_inv g))
    (fun g => encPerm (toFin (tmCsRho e E).symm (restrP e S.G S.dom S.dom_inv g)))
    (c := .list [encPerm ρ⁻¹, encPerm ρ⁻¹⁻¹]) (fun a _ a' _ he => by simp only; rw [encPerm_injective he])
    (fun g _ => by
      have := tmCs_conj_spec hA.hcj hA.hcp ρ⁻¹
        ((finCongr hs).permCongr (restrP e S.G S.dom S.dom_inv g))
      rw [tmJ_encPerm_cast, tmJ_encPerm_conj] at this
      exact this)
  have c4 := Det.call (Det.mk2 (Det.mk2 t1 t0) v3) hM
  have hval : Val.list ((tmJGList e S E gs).map encPerm) = Val.list ((1 :: gs).map fun g =>
      encPerm (toFin (tmCsRho e E).symm (restrP e S.G S.dom S.dom_inv g))) := by
    simp [tmJGList, Function.comp_def]
  rw [hval]
  refine (Det.letE c1 (Det.letE c2 (Det.letE c3 c4))).mono ?_
  -- the cost
  set X := (Val.list [sv, .list [encPerm ρ, encPerm ρ⁻¹]]).wt + k with hX
  set Y := X + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have hkY : k + 1 ≤ Y := by omega
  have hmq : m * q ≤ k := hs ▸ length_domFin_le
  have hpow : ∀ i j, i ≤ j → Y ^ i ≤ Y ^ j := fun i j h => Nat.pow_le_pow_right hY1 h
  have hk : ∀ i, (k + 1) ^ i ≤ Y ^ i := fun i => Nat.pow_le_pow_left hkY i
  have hmqk : ∀ i, (m * q + 1) ^ i ≤ Y ^ i := fun i => Nat.pow_le_pow_left (by omega) i
  have wsv : sv.wt < (Val.list [sv, .list [encPerm ρ, encPerm ρ⁻¹]]).wt := wt_le_wt_list (by simp)
  have wtab : (Val.list [encPerm ρ, encPerm ρ⁻¹]).wt <
      (Val.list [sv, .list [encPerm ρ, encPerm ρ⁻¹]]).wt := wt_le_wt_list (by simp)
  have hsvl' : (Val.list svl).wt = sv.wt := by rw [hsv']
  have wl : ∀ v ∈ svl, v.wt < sv.wt := fun v hv => hsvl' ▸ wt_le_wt_list hv
  have wind := wl (indVal e S.dom) (by simp [hsvl])
  have wkk := wl (.nat k) (by simp [hsvl])
  have wgs := wl (encGroup gs) (by simp [hsvl])
  have wgl : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (by simp [encGroup, encPerms])
  have wdn := wt_domNat_le e S.dom
  have wpos := wt_posVal_le e S.dom
  have wctx := wt_list2_le (natList (domNat e S.dom)) (posVal e S.dom)
  have wlen : (1 :: gs).length ≤ k ^ 2 + 1 := by simp; omega
  -- the restricted and the conjugated lists
  have wr : (Val.list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))).wt ≤
      (k ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) + 4 := by
    have := tmJ_wt_list_le (vs := (1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))
      (E := 4 * (k + 1) ^ 2) (by
        intro v hv
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
        have := wt_encPerm_le (restrP e S.G S.dom S.dom_inv g)
        have : ((domFin e S.dom).length + 1) ^ 2 ≤ (k + 1) ^ 2 :=
          Nat.pow_le_pow_left (by have := length_domFin_le (e := e) (D := S.dom); omega) 2
        omega)
    simp only [List.length_map] at this
    have : (1 :: gs).length * (2 * (4 * (k + 1) ^ 2) + 1) ≤ (k ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) :=
      Nat.mul_le_mul wlen (by omega)
    omega
  have wo : (Val.list ((1 :: gs).map fun g =>
      encPerm (toFin (tmCsRho e E).symm (restrP e S.G S.dom S.dom_inv g)))).wt ≤
      (k ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) + 4 := by
    have := tmJ_wt_list_le (vs := (1 :: gs).map fun g =>
      encPerm (toFin (tmCsRho e E).symm (restrP e S.G S.dom S.dom_inv g)))
      (E := 4 * (k + 1) ^ 2) (by
        intro v hv
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hv
        have := wt_encPerm_le (toFin (tmCsRho e E).symm (restrP e S.G S.dom S.dom_inv g))
        have : (m * q + 1) ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        omega)
    simp only [List.length_map] at this
    have : (1 :: gs).length * (2 * (4 * (k + 1) ^ 2) + 1) ≤ (k ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) :=
      Nat.mul_le_mul wlen (by omega)
    omega
  have hk2 : k ^ 2 + 1 ≤ Y ^ 2 := by nlinarith
  have hL : (k ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) ≤ 9 * Y ^ 4 := by
    calc (k ^ 2 + 1) * (8 * (k + 1) ^ 2 + 1) ≤ Y ^ 2 * (9 * Y ^ 2) :=
          Nat.mul_le_mul hk2 (by have := hk 2; have := hpow 0 2 (by norm_num); simp at this; omega)
      _ = 9 * Y ^ 4 := by ring
  have wi1 := wt_encPerm_le ρ⁻¹
  have wi2 := wt_encPerm_le ρ⁻¹⁻¹
  have wcc := wt_list2_le (encPerm ρ⁻¹) (encPerm ρ⁻¹⁻¹)
  have hRL : restrListK * (((1 :: gs).length + 1) * (k + 1)) ^ 7 ≤ 10 ^ 16 * Y ^ 21 := by
    have h1 : ((1 :: gs).length + 1) * (k + 1) ≤ 2 * Y ^ 3 := by
      calc ((1 :: gs).length + 1) * (k + 1) ≤ (2 * Y ^ 2) * Y := Nat.mul_le_mul (by omega) hkY
        _ = 2 * Y ^ 3 := by ring
    calc restrListK * (((1 :: gs).length + 1) * (k + 1)) ^ 7 ≤ 10 ^ 13 * (2 * Y ^ 3) ^ 7 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 7)
      _ = 1280000000000000 * Y ^ 21 := by ring
      _ ≤ 10 ^ 16 * Y ^ 21 := by omega
  have hMC : (1 :: gs).length * tmCsConjK (m * q) +
      mapK * ((1 :: gs).length + 1) *
        ((Val.list [Val.list [encPerm ρ⁻¹, encPerm ρ⁻¹⁻¹],
          Val.list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))]).wt +
        (Val.list ((1 :: gs).map fun g =>
          encPerm (toFin (tmCsRho e E).symm (restrP e S.G S.dom S.dom_inv g)))).wt + 1) ≤
      10 ^ 16 * Y ^ 21 := by
    have w2 := wt_list2_le (Val.list [encPerm ρ⁻¹, encPerm ρ⁻¹⁻¹])
      (Val.list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g)))
    have h3 := hmqk 2
    have hin : (Val.list [Val.list [encPerm ρ⁻¹, encPerm ρ⁻¹⁻¹],
          Val.list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))]).wt +
        (Val.list ((1 :: gs).map fun g =>
          encPerm (toFin (tmCsRho e E).symm (restrP e S.G S.dom S.dom_inv g)))).wt + 1 ≤
        100 * Y ^ 4 := by
      have := hpow 2 4 (by norm_num)
      omega
    have e1 : (1 :: gs).length * tmCsConjK (m * q) ≤ 10 ^ 6 * Y ^ 5 := by
      unfold tmCsConjK
      calc (1 :: gs).length * (10 ^ 6 * (m * q + 1) ^ 3) ≤ Y ^ 2 * (10 ^ 6 * Y ^ 3) :=
            Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (hmqk 3))
        _ = 10 ^ 6 * Y ^ 5 := by ring
    have e2 : mapK * ((1 :: gs).length + 1) * ((Val.list [Val.list [encPerm ρ⁻¹, encPerm ρ⁻¹⁻¹],
          Val.list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g))]).wt +
        (Val.list ((1 :: gs).map fun g =>
          encPerm (toFin (tmCsRho e E).symm (restrP e S.G S.dom S.dom_inv g)))).wt + 1) ≤
        10 ^ 6 * Y ^ 6 := by
      unfold mapK
      calc _ ≤ 1000 * (2 * Y ^ 2) * (100 * Y ^ 4) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hin
        _ = 200000 * Y ^ 6 := by ring
        _ ≤ _ := by omega
    have := hpow 5 21 (by norm_num)
    have := hpow 6 21 (by norm_num)
    omega
  have hDL : domListK * (k + 1) ^ 3 ≤ 10 ^ 6 * Y ^ 21 := by
    have := (hk 3).trans (hpow 3 21 (by norm_num))
    exact Nat.mul_le_mul (le_of_eq rfl) this
  have hPT : posTabK * (k + 1) ^ 4 ≤ 10 ^ 7 * Y ^ 21 := by
    have := (hk 4).trans (hpow 4 21 (by norm_num))
    exact Nat.mul_le_mul (le_of_eq rfl) this
  have h4 := hpow 4 21 (by norm_num)
  have h1 := hpow 1 21 (by norm_num)
  have h2 := hpow 2 21 (by norm_num)
  have hk2' := (hk 2).trans h2
  have wtx : (Val.list [sv, .list [encPerm ρ, encPerm ρ⁻¹]]).wt + 1 ≤ Y := by omega
  have hY121 : Y ≤ Y ^ 21 := by exact Nat.le_self_pow (by norm_num) _
  have hK : tmJGK X = 10 ^ 17 * Y ^ 21 := rfl
  rw [hK]
  have wq1 := wt_list2_le (natList (domNat e S.dom)) (Val.nat k)
  have wq2 := wt_list2_le (Val.list [natList (domNat e S.dom), posVal e S.dom])
    (Val.list ((1 :: gs).map encPerm))
  have wq3 := wt_list2_le (Val.list [encPerm ρ⁻¹, encPerm ρ⁻¹⁻¹])
    (Val.list ((1 :: gs).map fun g => encPerm (restrP e S.G S.dom S.dom_inv g)))
  have hii : ρ⁻¹⁻¹ = ρ := inv_inv ρ
  have wsv2 : (Val.list [sv, Val.list [encPerm ρ⁻¹⁻¹, encPerm ρ⁻¹]]).wt =
      (Val.list [sv, Val.list [encPerm ρ, encPerm ρ⁻¹]]).wt := by rw [hii]
  have wi3 : (encPerm ρ⁻¹⁻¹).wt = (encPerm ρ).wt := by rw [hii]
  have wr1 := wt_encPerm_le ρ
  have hk4 := (hk 2).trans (hpow 2 21 (by norm_num))
  have hk5 := (hk 3).trans (hpow 3 21 (by norm_num))
  have hmq2 := (hmqk 2).trans (hpow 2 21 (by norm_num))
  omega

end GI.Impl
