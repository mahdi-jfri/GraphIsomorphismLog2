import Workspace.Impl.TermGlueLabPOr
import Workspace.Impl.TermSupFix
import Workspace.Impl.TermHyp

/-!
# The solvable supplement (step 4)

Step 4 of the label program (Theorem A.23: "Compute a solvable supplement `S`
with `S N = D ∩ R` by Lemma A.19"). The residual answer is `w = [τ, U]` with
`Res = τ ⟨U⟩` and `D ⊓ R = τ ⟨U⟩ τ⁻¹` (`tmGL_res_iff`). The program conjugates the
generators of `U` by `τ` (Lemma A.19's own conjugation map `supConjF`, two `compose` calls per
generator) and calls T4 (`Iface.TermSupSpec`, at index `sup`) on `[τ⟨U⟩τ⁻¹, N]`.
The result generates a solvable `S ≤ τ⟨U⟩τ⁻¹` with `S ⊔ N = τ⟨U⟩τ⁻¹` (`tmGLPSup_spec`), where
`τ⟨U⟩τ⁻¹` is written `gens (U.map fun x => τ * x * τ⁻¹)` (`sup_gens_conj` turns it into the image
of `⟨U⟩` under conjugation).
The solvability of `S` is the precondition of the affine call of step 6.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens GensOf)

variable {n : ℕ}

/-- On `[gens N, [τ, U]]`: T4 on `[τ ⟨U⟩ τ⁻¹, N]`. Inverse at `inv`, the conjugation map at
`mc` (a `map` of `supConjF`), T4 at `sup`. -/
def tmGLPSupF (inv mc sup : ℕ) : Expr :=
  .letE (.call inv (.get (arg 1) (.nat 0)))
    (.call sup (mk2 (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
        (.call mc (mk2 (mk2 (.get (arg 1) (.nat 0)) (.var 1)) (.get (.get (arg 1) (.nat 1)) (.nat 1)))))
      (arg 0)))

/-- The cost bound, for an input of weight `W`, with T4's constants `K`, `D`. -/
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
/-- **The supplement call.** For a residual answer `[τ, U]` and `N ≤ R' = τ ⟨U⟩ τ⁻¹` normal with
`R'/N` solvable, the program returns generators of a solvable `S ≤ R'` with `S ⊔ N = R'`. -/
theorem tmGLPSup_spec {P : Program} {f inv cp cj mc sup Ks Ds : ℕ}
    (hf : P.funs[f]? = some (tmGLPSupF inv mc sup)) (hinv : P.HasAt inv (invFuns inv))
    (hcp : P.HasAt cp (composeFuns cp)) (hcj : P.funs[cj]? = some (supConjF cp))
    (hmc : P.HasAt mc (mapFuns mc cj)) (hsup : Iface.TermSupSpec P Ks Ds sup)
    {σN U : List (Perm (Fin n))} (hU : U.length ≤ n ^ 2) (τ : Perm (Fin n))
    (hNR : gens σN ≤ gens (U.map fun x => τ * x * τ⁻¹))
    [hnorm : ((gens σN).subgroupOf (gens (U.map fun x => τ * x * τ⁻¹))).Normal]
    (hsol : IsSolvable ((gens (U.map fun x => τ * x * τ⁻¹)) ⧸
      (gens σN).subgroupOf (gens (U.map fun x => τ * x * τ⁻¹)))) :
    FunAll P f (.list [encGroup σN, .list [encPerm τ, encGroup U]]) (fun u c =>
      ∃ S : Subgroup (Perm (Fin n)), GensOf S u ∧
        S ≤ gens (U.map fun x => τ * x * τ⁻¹) ∧ IsSolvable S ∧
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
  have e0 := Det.arg' (P := P) (vs := [encGroup σN, .list [encPerm τ, encGroup U]])
    (rest := [encPerm τ⁻¹]) (j := 0) rfl
  have e1 := Det.arg' (P := P) (vs := [encGroup σN, .list [encPerm τ, encGroup U]])
    (rest := [encPerm τ⁻¹]) (j := 1) rfl
  have eτ := Det.get' e1 (Det.nat 0) (vs := [encPerm τ, encGroup U]) (v := encPerm τ) rfl
  have eU := Det.get' e1 (Det.nat 1) (vs := [encPerm τ, encGroup U]) (v := encGroup U) rfl
  have en := Det.get' eU (Det.nat 0) (vs := [.nat n, .list ((1 :: U).map encPerm)])
    (v := .nat n) rfl
  have exs := Det.get' eU (Det.nat 1) (vs := [.nat n, .list ((1 :: U).map encPerm)])
    (v := .list ((1 :: U).map encPerm)) rfl
  have eτi := Det.var' (P := P) (env := [a, encPerm τ⁻¹]) (i := 1) (v := encPerm τ⁻¹) rfl
  have dmap := Det.call (Det.mk2 (Det.mk2 eτ eτi) exs) (supConjMap_det hcp hcj hmc τ hU)
  have dR : Det P [a, encPerm τ⁻¹] (mk2 (.get (.get (arg 1) (.nat 1)) (.nat 0))
      (.call mc (mk2 (mk2 (.get (arg 1) (.nat 0)) (.var 1)) (.get (.get (arg 1) (.nat 1)) (.nat 1)))))
      (encGroup V) _ := Det.mk2 en dmap
  have hspec := hsup V σN hNR hsol
  refine EvalAll.call_funAll (Det.mk2 dR e0) fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine FunAll.mono (FunAll.wt_lt hspec) fun u cb ⟨⟨S, hS, hSR, hSs, hSN, hcb⟩, hub⟩ =>
    ⟨S, hS, hSR, hSs, hSN, ?_⟩
  -- the cost
  have wN : (encGroup σN).wt < W := wt_le_wt_list (by simp)
  have w2 : (Val.list [encPerm τ, encGroup U]).wt < W := wt_le_wt_list (by simp)
  have wτ : (encPerm τ).wt < (Val.list [encPerm τ, encGroup U]).wt := wt_le_wt_list (by simp)
  have wU : (encGroup U).wt < (Val.list [encPerm τ, encGroup U]).wt := wt_le_wt_list (by simp)
  have hnW : n < W := by have := tmGLP_n_lt_wt τ; omega
  have hVl : V.length ≤ n ^ 2 := by simpa [hV] using hU
  have wV := tmGLP_encGroup_wt_le hVl hnW
  have win := wt_list2_le (encGroup V) (encGroup σN)
  have hin : (Val.list [encGroup V, encGroup σN]).wt + 1 ≤ 10 ^ 4 * (W + 1) ^ 6 := by
    have : 1 ≤ (W + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have : W ≤ (W + 1) ^ 6 := by
      have := Nat.le_self_pow (show 6 ≠ 0 by norm_num) (W + 1)
      omega
    omega
  have hK : Ks * ((Val.list [encGroup V, encGroup σN]).wt + 1) ^ Ds ≤
      Ks * (10 ^ 4 * (W + 1) ^ 6) ^ Ds := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hin Ds)
  -- the cost of the argument
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
  have eVr : (Val.list [.nat n, .list ((1 :: V).map encPerm)]).wt = (encGroup V).wt := rfl
  have hinvK : invK * (n + 1) ^ 4 ≤ 10 ^ 5 * (W + 1) ^ 8 := by unfold invK; omega
  have wp1 := wt_list2_le (encPerm τ) (encPerm τ⁻¹)
  have wp2 := wt_list2_le (.list [encPerm τ, encPerm τ⁻¹]) (.list ((1 :: U).map encPerm))
  have wn := wt_nat_le n
  have wa1 := wt_list2_le a (encPerm τ⁻¹)
  have eW : W = (Val.list [encGroup σN, .list [encPerm τ, encGroup U]]).wt := rfl
  unfold tmGLPSupC
  have ek : ((Val.list [encGroup V, encGroup σN]).wt + 1) ^ Ds =
      ((Val.list [encGroup V, encGroup σN]).wt + 1) ^ Ds := rfl
  clear hspec dmap dR dτi
  generalize Ks * ((Val.list [encGroup V, encGroup σN]).wt + 1) ^ Ds = KT at hcb hK
  generalize Ks * (10 ^ 4 * (W + 1) ^ 6) ^ Ds = KB at hK ⊢
  generalize (W + 1) ^ 8 = S8 at *
  generalize (W + 1) ^ 6 = S6 at *
  omega

end GI.Impl
