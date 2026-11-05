module

public import Workspace.Impl.TermGlueLabPOr
public import Workspace.Impl.TermConj
public import Workspace.Lang.Prims.BlockHom

@[expose] public section

/-!
# Conjugating the residual generators (step 4)

Step 4 of the label program (Theorem A.23). The residual answer is `w = [τ, U]` with
`Res = τ ⟨U⟩` and `D ⊓ R = τ ⟨U⟩ τ⁻¹` (`tmGL_res_iff`). The program conjugates the
generators of `U` by `τ` (`supConjF`, two `compose` calls per generator) and drops the
leading identity (`tailFuns`) to return the generator list of `S = τ ⟨U⟩ τ⁻¹ = D ⊓ R`
(`tmGLPSup_spec`). Since `N ≤ D ⊓ R` is normal with `(D ⊓ R)/N` solvable, and `N` lies in
the kernel of the linear action on `A / B(x) ⊕ C₂`, the linear image in step 6 is solvable.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens GensOf)

variable {n : ℕ}

/-- On `[gens N, [τ, U]]`: conjugate the generators of `U` by `τ` and drop the leading identity.
Inverse at `inv`, the conjugation map at `mc` (a `map` of `supConjF`), `tail` at `tl`. -/
def tmGLPSupF (inv mc tl : ℕ) : Expr :=
  .letE (.call inv (.get (arg 1) (.nat 0)))
    (.call tl (.call mc (mk2 (mk2 (.get (arg 1) (.nat 0)) (.var 1))
      (.get (.get (arg 1) (.nat 1)) (.nat 1)))))

/-- The cost bound, for an input of weight `W`. -/
def tmGLPSupC (K D W : ℕ) : ℕ := 3 * (K * (10 ^ 4 * (W + 1) ^ 6) ^ D) + 10 ^ 9 * (W + 1) ^ 8

theorem tmGLP_encGroup_wt_le {gs : List (Perm (Fin n))} (hl : gs.length ≤ n ^ 2) {W : ℕ}
    (hn : n < W) : (encGroup gs).wt ≤ 400 * (W + 1) ^ 6 := by
  have h1 := wt_encGroup_le gs
  have h2 : (gs.length + 2) * (n + 1) ≤ 2 * (W + 1) ^ 3 := by
    have : n ^ 2 + 2 ≤ 2 * (W + 1) ^ 2 := by
      have := Nat.pow_le_pow_left (show n ≤ W + 1 by omega) 2
      have : 4 ≤ (W + 1) ^ 2 := by
        have := Nat.pow_le_pow_left (show 2 ≤ W + 1 by omega) 2
        omega
      omega
    calc (gs.length + 2) * (n + 1) ≤ (2 * (W + 1) ^ 2) * (W + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 2 * (W + 1) ^ 3 := by ring
  have h3 := Nat.pow_le_pow_left h2 2
  have e : (2 * (W + 1) ^ 3) ^ 2 = 4 * (W + 1) ^ 6 := by ring
  omega

set_option maxHeartbeats 2000000 in
/-- **The conjugated residual group.** For a residual answer `[τ, U]` and `N ≤ R' = τ ⟨U⟩ τ⁻¹`
normal with `R'/N` solvable, the program returns generators of `S = R'` with `S ⊔ N = R'` and
`S/N` solvable. -/
theorem tmGLPSup_spec {P : Program} {f inv cp cj mc tl : ℕ} (Ks Ds : ℕ)
    (hf : P.funs[f]? = some (tmGLPSupF inv mc tl)) (hinv : P.HasAt inv (invFuns inv))
    (hcp : P.HasAt cp (composeFuns cp)) (hcj : P.funs[cj]? = some (supConjF cp))
    (hmc : P.HasAt mc (mapFuns mc cj)) (htl : P.HasAt tl (tailFuns tl))
    {σN U : List (Perm (Fin n))} (hU : U.length ≤ n ^ 2) (τ : Perm (Fin n))
    (hNR : gens σN ≤ gens (U.map fun x => τ * x * τ⁻¹))
    [hnorm : ((gens σN).subgroupOf (gens (U.map fun x => τ * x * τ⁻¹))).Normal]
    (hsol : IsSolvable ((gens (U.map fun x => τ * x * τ⁻¹)) ⧸
      (gens σN).subgroupOf (gens (U.map fun x => τ * x * τ⁻¹)))) :
    FunAll P f (.list [encGroup σN, .list [encPerm τ, encGroup U]]) (fun u c =>
      ∃ S : Subgroup (Perm (Fin n)), GensOf S u ∧
        S ≤ gens (U.map fun x => τ * x * τ⁻¹) ∧
        (∃ _ : ((gens σN).subgroupOf S).Normal, IsSolvable (S ⧸ (gens σN).subgroupOf S)) ∧
        S ⊔ gens σN = gens (U.map fun x => τ * x * τ⁻¹) ∧
        c ≤ tmGLPSupC Ks Ds (Val.list [encGroup σN, .list [encPerm τ, encGroup U]]).wt) := by
  set a : Val := .list [encGroup σN, .list [encPerm τ, encGroup U]] with ha
  set W := a.wt with hW
  set V := U.map fun x => τ * x * τ⁻¹ with hV
  apply FunAll.intro hf
  have g1 := Det.arg' (P := P) (vs := [encGroup σN, .list [encPerm τ, encGroup U]]) (rest := [])
    (j := 1) rfl
  have dτ := Det.get' g1 (Det.nat 0) (vs := [encPerm τ, encGroup U]) (v := encPerm τ) rfl
  have dτi := Det.call dτ (inv_spec hinv τ)
  refine EvalAll.letE dτi fun v cv hv => ?_
  obtain ⟨rfl, hcv⟩ := hv
  have e1 := Det.arg' (P := P) (vs := [encGroup σN, .list [encPerm τ, encGroup U]])
    (rest := [encPerm τ⁻¹]) (j := 1) rfl
  have eτ := Det.get' e1 (Det.nat 0) (vs := [encPerm τ, encGroup U]) (v := encPerm τ) rfl
  have eU := Det.get' e1 (Det.nat 1) (vs := [encPerm τ, encGroup U]) (v := encGroup U) rfl
  have exs := Det.get' eU (Det.nat 1) (vs := [.nat n, .list ((1 :: U).map encPerm)])
    (v := .list ((1 :: U).map encPerm)) rfl
  have eτi := Det.var' (P := P) (env := [a, encPerm τ⁻¹]) (i := 1) (v := encPerm τ⁻¹) rfl
  have dmap := Det.call (Det.mk2 (Det.mk2 eτ eτi) exs) (supConjMap_det hcp hcj hmc τ hU)
  have dtl := Det.call dmap (GI.Lang.tail_spec htl (encPerm (1 : Perm (Fin n))) (V.map encPerm))
  refine dtl.post fun cb hcb => ?_
  have hVl : V.length ≤ n ^ 2 := by simpa [hV] using hU
  refine ⟨gens V, ⟨V, rfl, hVl, rfl⟩, le_rfl, ⟨hnorm, hsol⟩, sup_eq_left.mpr hNR, ?_⟩
  -- the cost
  have wN : (encGroup σN).wt < W := wt_le_wt_list (by simp)
  have w2 : (Val.list [encPerm τ, encGroup U]).wt < W := wt_le_wt_list (by simp)
  have wτ : (encPerm τ).wt < (Val.list [encPerm τ, encGroup U]).wt := wt_le_wt_list (by simp)
  have wU : (encGroup U).wt < (Val.list [encPerm τ, encGroup U]).wt := wt_le_wt_list (by simp)
  have hnW : n < W := by have := tmGLP_n_lt_wt τ; omega
  have wV := tmGLP_encGroup_wt_le hVl hnW
  have wτi := wt_encPerm_le τ⁻¹
  have wτ' := wt_encPerm_le τ
  have hn8 : (n + 1) ^ 8 ≤ (W + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  have hn4 : (n + 1) ^ 4 ≤ (W + 1) ^ 8 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 4).trans
      (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hn2 : (n + 1) ^ 2 ≤ (W + 1) ^ 8 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by omega) 2).trans
      (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hW6 : (W + 1) ^ 6 ≤ (W + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hW1 : W + 1 ≤ (W + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
  have wexs : (Val.list ((1 :: U).map encPerm)).wt ≤ (encGroup U).wt := by
    have : (Val.list ((1 :: U).map encPerm)).wt <
        (Val.list [.nat n, .list ((1 :: U).map encPerm)]).wt := wt_le_wt_list (by simp)
    exact this.le
  have wVl : (Val.list ((1 :: V).map encPerm)).wt ≤ (encGroup V).wt := by
    have : (Val.list ((1 :: V).map encPerm)).wt <
        (Val.list [.nat n, .list ((1 :: V).map encPerm)]).wt := wt_le_wt_list (by simp)
    exact this.le
  have wVl' : (Val.list ((1 :: U.map fun x => τ * x * τ⁻¹).map encPerm)).wt ≤ (encGroup V).wt :=
    wVl
  have wVsub : (Val.list (V.map encPerm)).wt ≤ (Val.list ((1 :: V).map encPerm)).wt :=
    wt_list_sublist (List.sublist_cons_self _ _)
  have htlC : loopModK * ((V.map encPerm).length + 1) *
      (3 * (Val.list (encPerm (1 : Perm (Fin n)) :: V.map encPerm)).wt + 1) ≤
      2 * 10 ^ 6 * (W + 1) ^ 8 := by
    have hlV : (V.map encPerm).length + 1 ≤ (W + 1) ^ 2 := by
      simp only [List.length_map]
      have : (W + 1) ^ 2 = W ^ 2 + 2 * W + 1 := by ring
      have : n ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have hwV1 : 3 * (Val.list (encPerm (1 : Perm (Fin n)) :: V.map encPerm)).wt + 1 ≤
        2000 * (W + 1) ^ 6 := by
      have : 1 ≤ (W + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
      have ec : Val.list (encPerm (1 : Perm (Fin n)) :: V.map encPerm) =
          Val.list ((1 :: V).map encPerm) := rfl
      rw [ec]
      omega
    calc loopModK * ((V.map encPerm).length + 1) *
          (3 * (Val.list (encPerm (1 : Perm (Fin n)) :: V.map encPerm)).wt + 1)
        ≤ loopModK * (W + 1) ^ 2 * (2000 * (W + 1) ^ 6) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hlV) hwV1
      _ = 2 * 10 ^ 6 * (W + 1) ^ 8 := by simp only [loopModK]; ring
  have hinvK : invK * (n + 1) ^ 4 ≤ 10 ^ 5 * (W + 1) ^ 8 := by unfold invK; omega
  have wp1 := wt_list2_le (encPerm τ) (encPerm τ⁻¹)
  have wp2 := wt_list2_le (.list [encPerm τ, encPerm τ⁻¹]) (.list ((1 :: U).map encPerm))
  have wn := wt_nat_le n
  have wa1 := wt_list2_le a (encPerm τ⁻¹)
  have eW : W = (Val.list [encGroup σN, .list [encPerm τ, encGroup U]]).wt := rfl
  have econs : Val.list (encPerm (1 : Perm (Fin n)) :: V.map encPerm) =
      Val.list ((1 :: U.map fun x => τ * x * τ⁻¹).map encPerm) := rfl
  rw [econs] at hcb htlC
  unfold tmGLPSupC
  clear dtl dmap dτi
  generalize 3 * (Ks * (10 ^ 4 * (W + 1) ^ 6) ^ Ds) = KB at ⊢
  generalize (W + 1) ^ 8 = S8 at *
  generalize (W + 1) ^ 6 = S6 at *
  omega

end GI.Impl
