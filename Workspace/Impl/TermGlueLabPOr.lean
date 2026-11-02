import Workspace.Impl.TermGlueLabPOffM
import Workspace.Impl.AggItemC1Par
import Workspace.Impl.TermGlueLabPE

/-!
# The orientation `ε(h)`

Step 3 of the label program. When every type of `x` is distinct, the torsor has
the extra orientation coordinate, and `h` moves it by `ε(h)`, the sign of the permutation `ρ`
of the types with `type(x_{ρ i}) = type(x_i)^h` (`tmGLε`).

The transporters for `h` (`TmGLPOOut`) hold, for every row `i`, a pair `[j_i, s_i]` with `x_{j_i}`
the first row of the type of `rep(type x_i)^h`. So `ρ i = j_i` (`tmGLP_or_perm`), and
`ρ` is a permutation because the types are distinct. The program `tmGLPOrFuns` reads the `j_i`
(a `map`) and runs the parity program of Case 1 (`itParF`, `it_par_spec`) on `encPerm ρ`. The
result `itpNInv ρ % 2` is `ε(h)` read in `ℤ/2` (`tmGLP_par_units`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-! ### The mathematics -/

/-- **The permutation of the types from the transporters.** When the types of `x` are distinct
and `h ∈ Aut_H(T)`, the first entries of the transporters for `h` form a permutation `ρ` with
`type(x_{ρ i}) = type(x_i)^h`. -/
theorem tmGLP_or_perm {H N : Subgroup (Perm (Fin n))} (hn : GI.Multicoset.Normalizes H N)
    {q : ℕ} {X : Fin q → Ω} (j0 : Fin q) (hT : (types N X).Nodup) {h : Perm (Fin n)}
    (hD : h ∈ Aut H (types N X)) {l : List Val} (hl : TmGLPOOut N X h (.list l)) :
    ∃ ρ : Perm (Fin q), (∀ i, orbitN N (X (ρ i)) = orbitN N (X i) ↼ h) ∧
      ∀ i : Fin q, ∃ s : Perm (Fin n), l[i.1]? = some (.list [.nat (ρ i), encPerm s]) := by
  obtain ⟨l', hl', hlen, hlv⟩ := hl
  cases hl'
  have hhH := (mem_aut.mp hD).1
  -- the entry of row `i`
  have hrow : ∀ i : Fin q, ∃ j : Fin q, ∃ s : Perm (Fin n),
      l[i.1]? = some (.list [.nat j, encPerm s]) ∧ orbitN N (X j) = orbitN N (X i) ↼ h := by
    intro i
    obtain ⟨v, hv, hit⟩ := hlv i
    obtain ⟨J, hJ, -⟩ := id hit
    obtain ⟨j, s, -, rfl, hfst, -⟩ := tmGLP_off_item hn j0 hD hit
    refine ⟨j, s, hv, ?_⟩
    rw [tmGLP_rep_eq j0 hJ] at hfst
    rw [← tmGLP_orbit_eq hfst.1, ← orbitN_act hn hhH, tmGLP_orbit_eq hJ.1]
  choose ρ0 s hs hρ0 using hrow
  -- `ρ0` is injective, since the types are distinct
  have hinj : Function.Injective ρ0 := by
    intro i i' he
    have h1 : orbitN N (X i) ↼ h = orbitN N (X i') ↼ h := by rw [← hρ0, ← hρ0, he]
    have h2 : orbitN N (X i) = orbitN N (X i') := by
      have := congrArg (fun S : Set Ω => S ↼ h⁻¹) h1
      simpa only [act_act, mul_inv_cancel, act_one] using this
    exact tmGL_types_inj rfl hT h2
  set ρ := Equiv.ofBijective ρ0 (Finite.injective_iff_bijective.mp hinj)
  exact ⟨ρ, fun i => hρ0 i, fun i => ⟨s i, hs i⟩⟩

/-- **The parity is the orientation in `ℤ/2`.** -/
theorem tmGLP_par_units {q : ℕ} (ρ : Perm (Fin q)) :
    ((itpNInv ρ % 2 : ℕ) : ZMod 2) = tmGLPUnits (Additive.ofMul (sign ρ)) := by
  rw [ZMod.natCast_mod]
  unfold tmGLPUnits
  simp only [AddEquiv.coe_mk, Equiv.coe_fn_mk, toMul_ofMul]
  rcases Nat.even_or_odd (itpNInv ρ) with he | ho
  · rw [if_pos ((itp_sign_one_iff ρ).2 he)]
    exact (ZMod.natCast_eq_zero_iff_even).2 he
  · have hne : sign ρ ≠ 1 := fun h1 => (Nat.not_even_iff_odd.2 ho) ((itp_sign_one_iff ρ).1 h1)
    rw [if_neg hne]
    exact (ZMod.natCast_eq_one_iff_odd).2 ho

/-! ### The program -/

/-- On `[c, v]` with `v = [j, s]`: the number `j`. -/
def tmGLPGet0F : Expr := .get (arg 1) (.nat 0)

/-- The parity program of Case 1 with its helpers (16 functions). -/
def tmGLPParFuns (b : ℕ) : List Expr :=
  [itParF (b + 1) (b + 4) (b + 7)] ++ rangeFuns (b + 1) ++ mapFuns (b + 4) (b + 10) ++
    foldlFuns (b + 7) (b + 15) ++ [itInvB (b + 11)] ++ filterFuns (b + 11) (b + 14) ++
    [itInvT, itParS]

theorem length_tmGLPParFuns (b : ℕ) : (tmGLPParFuns b).length = 16 := rfl

/-- On the transporters `l`: the parity of `ρ`. -/
def tmGLPOrF (mp par : ℕ) : Expr := .call par (.call mp (mk2 .nil (.var 0)))

/-- **The orientation program** (21 functions). -/
def tmGLPOrFuns (b : ℕ) : List Expr :=
  [tmGLPOrF (b + 1) (b + 5)] ++ mapFuns (b + 1) (b + 4) ++ [tmGLPGet0F] ++ tmGLPParFuns (b + 5)

theorem length_tmGLPOrFuns (b : ℕ) : (tmGLPOrFuns b).length = 21 := rfl

/-- The parity program meets `it_par_spec`. -/
theorem tmGLP_par_spec {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPParFuns b)) {q : ℕ}
    (σ : Perm (Fin q)) : FunDet P b (encPerm σ) (.nat (itpNInv σ % 2)) (itParC q) := by
  have h1 : P.funs[b]? = some (itParF (b + 1) (b + 4) (b + 7)) := by
    simpa using (h.block (gs := [itParF (b + 1) (b + 4) (b + 7)]) 0 rfl).single
  exact it_par_spec h1 (h.block 1 rfl) (h.block 4 rfl)
    (h.block (gs := [itInvB (b + 11)]) 10 rfl).single (h.block 11 rfl)
    (h.block (gs := [itInvT]) 14 rfl).single
    (h.block 7 rfl) (h.block (gs := [itParS]) 15 rfl).single σ

/-- The cost bound of the orientation program, for `q` rows and transporters of weight `W`. -/
def tmGLPOrC (q W : ℕ) : ℕ := itParC q + 10 ^ 6 * (W + 1) ^ 3

set_option maxHeartbeats 2000000 in
/-- **The orientation.** On the transporters for `h ∈ Aut_H(T)`, with distinct types, the
program returns `itpNInv ρ % 2` for the permutation `ρ` of the types under `h`. -/
theorem tmGLPOr_spec {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPOrFuns b))
    {H N : Subgroup (Perm (Fin n))} (hn : GI.Multicoset.Normalizes H N)
    {q : ℕ} {X : Fin q → Ω} (j0 : Fin q) (hT : (types N X).Nodup) {g : Perm (Fin n)}
    (hD : g ∈ Aut H (types N X)) {l : List Val} (hl : TmGLPOOut N X g (.list l)) :
    FunAll P b (.list l) (fun w c => ∃ ρ : Perm (Fin q),
      (∀ i, orbitN N (X (ρ i)) = orbitN N (X i) ↼ g) ∧ w = .nat (itpNInv ρ % 2) ∧
      c ≤ tmGLPOrC q (Val.list l).wt) := by
  obtain ⟨ρ, hρ, hlρ⟩ := tmGLP_or_perm hn j0 hT hD hl
  have hlen : l.length = q := by
    obtain ⟨l', hl', hlen, -⟩ := hl
    cases hl'; exact hlen
  have hf : P.funs[b]? = some (tmGLPOrF (b + 1) (b + 5)) := by
    simpa using (h.block (gs := [tmGLPOrF (b + 1) (b + 5)]) 0 rfl).single
  have hmp : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hg0 : P.funs[b + 4]? = some tmGLPGet0F := (h.block (gs := [tmGLPGet0F]) 4 rfl).single
  have hpar : P.HasAt (b + 5) (tmGLPParFuns (b + 5)) := h.block 5 rfl
  set W := (Val.list l).wt with hW
  -- the map reads the first entries
  have hget : ∀ x ∈ l, FunAll P (b + 4) (.list [.list [], x]) (fun w c =>
      (∀ (j : ℕ) (s : Perm (Fin n)), x = .list [.nat j, encPerm s] → w = .nat j) ∧
        c ≤ 10 * W + 50) := by
    intro x hx
    have hxW : x.wt < W := wt_le_wt_list hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiq : i < q := hlen ▸ hi
    obtain ⟨s, hs⟩ := hlρ ⟨i, hiq⟩
    have hxe : l[i] = .list [.nat (ρ ⟨i, hiq⟩), encPerm s] :=
      Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hs)
    rw [hxe] at hxW ⊢
    have d1 := Det.arg' (P := P) (vs := [.list [], .list [.nat (ρ ⟨i, hiq⟩), encPerm s]])
      (rest := []) (j := 1) rfl
    have d2 := Det.get' d1 (Det.nat 0) (vs := [.nat (ρ ⟨i, hiq⟩), encPerm s])
      (v := .nat (ρ ⟨i, hiq⟩)) rfl
    refine FunAll.intro hg0 (d2.post fun c hc => ⟨fun j s' he => ?_, ?_⟩)
    · simp only [Val.list.injEq, List.cons.injEq, Val.nat.injEq] at he
      rw [he.1]
    · have w2 := wt_list2_le (.list []) (.list [.nat (ρ ⟨i, hiq⟩), encPerm s])
      have w0 : (Val.list []).wt ≤ 5 := by decide
      have wj : (Val.nat (ρ ⟨i, hiq⟩)).wt <
          (Val.list [.nat (ρ ⟨i, hiq⟩), encPerm s]).wt := wt_le_wt_list (by simp)
      omega
  have hm := map_spec hmp hget
  -- the result of the map is `encPerm ρ`
  have hws : ∀ ws : List Val, List.Forall₂ (fun x w => ∀ (j : ℕ) (s : Perm (Fin n)),
      x = .list [.nat j, encPerm s] → w = .nat j) l ws → Val.list ws = encPerm ρ := by
    intro ws hF
    have hlw := hF.length_eq
    unfold encPerm
    congr 1
    refine List.ext_getElem (by simp [← hlw, hlen]) fun i h1 h2 => ?_
    have hiq : i < q := by simpa using h2
    obtain ⟨s, hs⟩ := hlρ ⟨i, hiq⟩
    have hil : i < l.length := by omega
    have hR := hF.get hil h1
    simp only [List.get_eq_getElem] at hR
    have hxe : l[i] = .list [.nat (ρ ⟨i, hiq⟩), encPerm s] :=
      Option.some.inj ((List.getElem?_eq_getElem hil).symm.trans hs)
    rw [hR _ _ hxe]
    simp
  have wl := length_lt_wt_list l
  have hpw := wt_encPerm_le ρ
  apply FunAll.intro hf
  have dinner : EvalAll P [.list l] (.call (b + 1) (mk2 .nil (.var 0))) (fun w c =>
      w = encPerm ρ ∧ c ≤ 10 ^ 5 * (W + 1) ^ 3) := by
    refine EvalAll.call_funAll (Det.mk2 Det.nil (Det.var' (P := P) (env := [.list l]) (i := 0)
      (v := .list l) rfl)) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine hm.mono fun w c ⟨ws, hw, hF, hc⟩ => ⟨hw.trans (hws ws hF), ?_⟩
    subst hw
    have hwt : (Val.list ws).wt = (encPerm ρ).wt := congrArg Val.wt (hws ws hF)
    have hsum : (l.map fun _ => 10 * W + 50).sum = l.length * (10 * W + 50) := by simp
    rw [hsum] at hc
    have w2 := wt_list2_le (.list []) (.list l)
    have w0 : (Val.list []).wt ≤ 5 := by decide
    have hq2 : (q + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hS3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : l.length * (10 * W + 50) ≤ (W + 1) * (50 * (W + 1)) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h2 : mapK * (l.length + 1) *
        ((Val.list [.list [], .list l]).wt + (Val.list ws).wt + 1) ≤
        1000 * ((W + 1) * (30 * (W + 1) ^ 2)) := by
      rw [Nat.mul_assoc]; unfold mapK
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e1 : (W + 1) * (50 * (W + 1)) = 50 * (W + 1) ^ 2 := by ring
    have e2 : (W + 1) * (30 * (W + 1) ^ 2) = 30 * (W + 1) ^ 3 := by ring
    have hfin := hc.trans (Nat.add_le_add h1 h2)
    rw [e1, e2] at hfin
    clear hc h1 h2
    omega
  refine EvalAll.call_funAll dinner fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine FunAll.mono (tmGLP_par_spec hpar ρ) fun w c ⟨hw, hc⟩ => ⟨ρ, hρ, hw, ?_⟩
  subst hw
  have : (Val.nat (itpNInv ρ % 2)).wt ≤ 3 := by
    have := wt_nat_le (itpNInv ρ % 2)
    have := Nat.mod_lt (itpNInv ρ) (show 2 > 0 by omega)
    omega
  have : 1 ≤ (W + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  unfold tmGLPOrC
  omega

end GI.Impl
