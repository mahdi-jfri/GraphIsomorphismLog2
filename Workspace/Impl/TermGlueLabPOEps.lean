import Workspace.Impl.TermGlueLabPOBlk
import Workspace.Impl.TermGlueLabPOr

/-!
# The orientation entry of one element (step 5, all types distinct)

Step 5 of the label program. The offset of `g` with the orientation coordinate is
`(ε(g⁻¹), c(g))` (`tmGLP_cO_vec`). The program `tmGLPEpsF off or` computes the entry `ε(g⁻¹)`
on `[[gens N, vs, q, xl], g]`: the row transporters for `g⁻¹` (`tmGLPOff_spec`, input
`[gens N, vs, q, xl, g]`), then the parity of the permutation of the types they give
(`tmGLPOr_spec`), then `encInt` of it. `tmGLPEps_spec`: the result is
`encInt (tmGLPEc N X g⁻¹)`, the orientation of `g⁻¹` read in `ℤ/2` (`tmGLP_Ec_eq`).

The transporters are computed again here (they are also computed inside the offset vector);
the result does not depend on the choices made there, since the orientation depends only on the
types (`tmGLε_eq`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv Equiv.Perm
open GI.Cited (Val encInt encPerm encGroup gens Membership NormalizedFactor)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

theorem tmGLPEc_lt (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (h : Perm (Fin n)) :
    tmGLPEc N X h < 2 :=
  ZMod.val_lt _

/-- **The orientation as a number** is the parity of the permutation of the types. -/
theorem tmGLP_Ec_eq {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω}
    (hT : (types N X).Nodup) {h : Perm (Fin n)} {ρ : Perm (Fin q)}
    (hρ : ∀ i, orbitN N (X (ρ i)) = orbitN N (X i) ↼ h) : tmGLPEc N X h = itpNInv ρ % 2 := by
  unfold tmGLPEc
  rw [tmGLε_eq hT hρ, ← tmGLP_par_units, ZMod.val_natCast, Nat.mod_mod]

theorem tmGLP_encEc_wt (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (h : Perm (Fin n)) :
    (encInt (tmGLPEc N X h : ℤ)).wt ≤ 100 := by
  have := tmGLPEc_lt N X h
  have ⟨w0, w1⟩ := tmGLP_encInt01_wt
  interval_cases (tmGLPEc N X h) <;> simpa

theorem tmGLPOrC_mono (q : ℕ) {W W' : ℕ} (h : W ≤ W') : tmGLPOrC q W ≤ tmGLPOrC q W' := by
  unfold tmGLPOrC; gcongr

/-- **The orientation entry**, on `[[gens N, vs, q, xl], g]`. -/
def tmGLPEpsF (off or : ℕ) : Expr :=
  .letE (.call or (.call off (.snoc (arg 0) (arg 1)))) (.ite (.var 1) tmGLPOneE tmGLPZeroE)

/-- The cost bound of the orientation entry. -/
def tmGLPEpsC (pm pf : Prim) (q W : ℕ) : ℕ :=
  1000 * (W + 1) + 10 * (tmGLPOffC pm pf (3 * W + 5) + tmGLPOrC q (tmGLPOffC pm pf (3 * W + 5)))

theorem tmGLPEpsC_mono (pm pf : Prim) (q : ℕ) {W W' : ℕ} (h : W ≤ W') :
    tmGLPEpsC pm pf q W ≤ tmGLPEpsC pm pf q W' := by
  have h1 := tmGLPOffC_mono pm pf (show 3 * W + 5 ≤ 3 * W' + 5 by omega)
  have h2 := tmGLPOrC_mono q h1
  unfold tmGLPEpsC
  omega

/-- **The orientation entry of `g⁻¹`.** -/
theorem tmGLPEps_spec (hm : Membership) (hfac : NormalizedFactor) {P : Program} {f off or : ℕ}
    (hf : P.funs[f]? = some (tmGLPEpsF off or)) (hoffA : TmGLPOffAt P off hm hfac)
    (hor : P.HasAt or (tmGLPOrFuns or))
    {H : Subgroup (Perm (Fin n))} {σN : List (Perm (Fin n))} (hNH : gens σN ≤ H)
    (hn : GI.Multicoset.Normalizes H (gens σN)) {q : ℕ} {X Y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H X Y vs) (hY : ∀ j : Fin q, ∃ l : Fin q, (Iso H (X j) (Y l)).Nonempty)
    {xl : List Val} (hxl : TmGLPXOut (gens σN) X (.list xl)) (j0 : Fin q)
    (hTd : (types (gens σN) X).Nodup) {g : Perm (Fin n)}
    (hD : g⁻¹ ∈ Aut H (types (gens σN) X)) :
    FunAll P f (.list [.list [encGroup σN, .list vs, .nat q, .list xl], encPerm g]) (fun w c =>
      w = encInt (tmGLPEc (gens σN) X g⁻¹ : ℤ) ∧
        c ≤ tmGLPEpsC (membershipPrim hm) (normalizedFactorPrim hfac) q
          (Val.list [.list [encGroup σN, .list vs, .nat q, .list xl], encPerm g]).wt) := by
  obtain ⟨find, rel, jm, jf, hoff, hfd, hr, hjm, hjf⟩ := hoffA
  set pm := membershipPrim hm
  set pf := normalizedFactorPrim hfac
  set c1 : Val := .list [encGroup σN, .list vs, .nat q, .list xl] with hc1
  set a : Val := .list [c1, encPerm g] with ha
  set W := a.wt with hW
  have wc1 : c1.wt < W := wt_le_wt_list (by simp)
  have wg : (encPerm g).wt < W := wt_le_wt_list (by simp)
  have hgH : g⁻¹ ∈ H := (mem_aut.mp hD).1
  have hO := tmGLPOff_spec hm hfac hoff hfd hr hjm hjf hNH hn hT hY hxl (g := g⁻¹) hgH
  rw [inv_inv] at hO
  -- the input of the transporters
  have d0 := Det.arg' (P := P) (vs := [c1, encPerm g]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [c1, encPerm g]) (rest := []) (j := 1) rfl
  have ds : Det P [a] (.snoc (arg 0) (arg 1)) (tmGLPOIn σN vs q xl g) _ := Det.snoc d0 d1
  have win : (tmGLPOIn σN vs q xl g).wt ≤ 3 * W + 5 := by
    have := wt_list_snoc_le [encGroup σN, .list vs, .nat q, .list xl] (encPerm g)
    have e : (tmGLPOIn σN vs q xl g).wt =
      (Val.list ([encGroup σN, .list vs, .nat q, .list xl] ++ [encPerm g])).wt := rfl
    have e2 : c1.wt = (Val.list [encGroup σN, .list vs, .nat q, .list xl]).wt := rfl
    omega
  obtain ⟨O, hOe⟩ : ∃ O, tmGLPOffC pm pf (3 * W + 5) = O := ⟨_, rfl⟩
  have hO' : FunAll P off (tmGLPOIn σN vs q xl g) (fun u c =>
      TmGLPOOut (gens σN) X g⁻¹ u ∧ c ≤ O) :=
    FunAll.mono hO fun u c h => ⟨h.1, h.2.trans (by rw [← hOe]; exact tmGLPOffC_mono pm pf win)⟩
  have c2 := tmGLP_callAll_le ds le_rfl hO'
  apply FunAll.intro hf
  refine EvalAll.letE (EvalAll.call_funAll c2 (Q := fun w c => ∃ ρ : Perm (Fin q),
      (∀ i, orbitN (gens σN) (X (ρ i)) = orbitN (gens σN) (X i) ↼ g⁻¹) ∧
      w = .nat (itpNInv ρ % 2) ∧ c ≤ 20 * W + 100 + 2 * O + tmGLPOrC q O + w.wt + 1)
    fun v cv ⟨hv, hcv, hvw⟩ => ?_) fun v cv hv => ?_
  · have hv' := hv
    obtain ⟨l, rfl, -⟩ := hv'
    refine FunAll.mono (tmGLPOr_spec hor hn j0 hTd hD hv) fun w c ⟨ρ, hρ, hw, hc⟩ =>
      ⟨ρ, hρ, hw, ?_⟩
    have := tmGLPOrC_mono q hvw.le
    have e2 : c1.wt = (Val.list [encGroup σN, .list vs, .nat q, .list xl]).wt := rfl
    have e3 : a.wt = W := rfl
    have e4 : (Val.list [c1, encPerm g]).wt = W := rfl
    have := wt_list_snoc_le [encGroup σN, .list vs, .nat q, .list xl] (encPerm g)
    omega
  · obtain ⟨ρ, hρ, rfl, hcv⟩ := hv
    have hE := tmGLP_Ec_eq hTd hρ
    have dv := Det.var' (P := P) (env := [a, .nat (itpNInv ρ % 2)]) (i := 1)
      (v := .nat (itpNInv ρ % 2)) rfl
    have hwE := tmGLP_encEc_wt (gens σN) X g⁻¹
    have hk := wt_nat_le (itpNInv ρ % 2)
    have hk2 : itpNInv ρ % 2 < 2 := Nat.mod_lt _ (by omega)
    have := wt_nat_le 0
    have := wt_nat_le 1
    have hBnd : 20 * W + 100 + 2 * O + tmGLPOrC q O + 3 + 200 + 400 + 300 + 1 ≤
        tmGLPEpsC pm pf q W := by
      unfold tmGLPEpsC; rw [hOe]; omega
    rcases Nat.mod_two_eq_zero_or_one (itpNInv ρ) with h0 | h1
    · rw [h0] at dv hE ⊢
      have dt := Det.ite_zero (t := tmGLPOneE) dv (tmGLP_zeroE (P := P))
      refine dt.post fun c hc => ⟨by rw [hE]; rfl, ?_⟩
      rw [hE] at hwE
      simp only [Nat.cast_zero] at hwE
      omega
    · rw [h1] at dv hE ⊢
      have dt := Det.ite_pos (e := tmGLPZeroE) dv one_ne_zero (tmGLP_oneE (P := P))
      refine dt.post fun c hc => ⟨by rw [hE]; rfl, ?_⟩
      rw [hE] at hwE
      simp only [Nat.cast_one] at hwE
      omega

end GI.Impl
