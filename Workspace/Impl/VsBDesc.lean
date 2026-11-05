module

public import Workspace.Impl.VsBChain

@[expose] public section

/-!
# Looking up a target along a chain of small orbits

The chain of `vsBChain_spec` cuts `G₀` down stage by stage. Suppose a map `ψ` from `G₀` to a
group `M` is a homomorphism, and stage `q` sees an element `h` only through the point
`T q (ψ h)` (`α q h y₀ = T q (ψ h)`). To find `h ∈ G₀` with `ψ h = τ`, we go down the chain: at
stage `i` we look up the point `T q τ_i` in the orbit list. If it is there, with element `t`, we
continue with `τ_{i+1} = ψ(t)⁻¹ τ_i` and remember `t`; if not, there is no solution. At the end
`τ_m = 1`, so the product of the remembered elements is a solution.

* `VsBDescHyp`: the hypotheses on `α`, `ψ`, `T`.
* `VsBDescOK`: the invariant of the descent; `vsBDesc_found`, `vsBDesc_missing`, `vsBDesc_end`.
* `vsBDescFuns b tk fnd up cmp` (3 functions), `vsBDesc_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ} {Y M : Type} [Group M]

/-- The hypotheses of the descent. -/
structure VsBDescHyp (α : ℕ → Perm (Fin n) → Y → Y) (y₀ : Y) (G₀ : Subgroup (Perm (Fin n)))
    (ψ : Perm (Fin n) → M) (T : ℕ → M → Y) (ps : List ℕ) : Prop where
  act : ∀ q ∈ ps, VsQPAct G₀ (α q)
  hom : ∀ g ∈ G₀, ∀ h ∈ G₀, ψ (g * h) = ψ g * ψ h
  aT : ∀ q ∈ ps, ∀ h ∈ G₀, α q h y₀ = T q (ψ h)
  kerT : ∀ q ∈ ps, ∀ a b, T q a = T q b ↔ T q (b⁻¹ * a) = T q 1
  fin : ∀ a, (∀ q ∈ ps, T q a = T q 1) → a = 1

/-- The invariant of the descent after `i` stages: `prod · τ_i` is the target, `τ_i` passes the
first `i` stages, and a solution in `G₀` gives one for `τ_i` in the group of stage `i`. -/
def VsBDescOK (α : ℕ → Perm (Fin n) → Y → Y) (y₀ : Y) (G₀ : Subgroup (Perm (Fin n)))
    (ψ : Perm (Fin n) → M) (T : ℕ → M → Y) (ps : List ℕ) (τ : M) (i : ℕ) (τi : M)
    (prod : Perm (Fin n)) : Prop :=
  prod ∈ G₀ ∧ ψ prod * τi = τ ∧ (∀ q ∈ ps.take i, T q τi = T q 1) ∧
    ((∃ h ∈ G₀, ψ h = τ) → ∃ h ∈ vsBKs α y₀ G₀ (ps.take i), ψ h = τi)

section

variable {α : ℕ → Perm (Fin n) → Y → Y} {y₀ : Y} {G₀ : Subgroup (Perm (Fin n))}
  {ψ : Perm (Fin n) → M} {T : ℕ → M → Y} {ps : List ℕ} (H : VsBDescHyp α y₀ G₀ ψ T ps)
include H

theorem VsBDescHyp.one : ψ 1 = 1 := by
  have := H.hom 1 (one_mem _) 1 (one_mem _)
  rw [one_mul] at this
  exact (mul_eq_left.mp this.symm)

theorem VsBDescHyp.inv {g : Perm (Fin n)} (hg : g ∈ G₀) : ψ g⁻¹ = (ψ g)⁻¹ := by
  have := H.hom g⁻¹ (inv_mem hg) g hg
  rw [inv_mul_cancel, H.one] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem VsBDescHyp.base {q : ℕ} (hq : q ∈ ps) : y₀ = T q 1 := by
  have := H.aT q hq 1 (one_mem _)
  rw [(H.act q hq).one, H.one] at this
  exact this

theorem vsBDesc_start (τ : M) : VsBDescOK α y₀ G₀ ψ T ps τ 0 τ 1 := by
  refine ⟨one_mem _, by rw [H.one, one_mul], by simp, fun ⟨h, hh, he⟩ => ⟨h, ?_, he⟩⟩
  simp [vsBKs, hh]

theorem vsBDesc_found {τ τi : M} {i : ℕ} {prod t : Perm (Fin n)}
    (hok : VsBDescOK α y₀ G₀ ψ T ps τ i τi prod) (hi : i < ps.length)
    (ht : t ∈ vsBKs α y₀ G₀ (ps.take i)) (hpt : α ps[i] t y₀ = T ps[i] τi) :
    VsBDescOK α y₀ G₀ ψ T ps τ (i + 1) ((ψ t)⁻¹ * τi) (prod * t) := by
  obtain ⟨hp, hpe, hT, hex⟩ := hok
  have hq : ps[i] ∈ ps := List.getElem_mem hi
  have htG : t ∈ G₀ := ht.1
  have hTt : T ps[i] (ψ t) = T ps[i] τi := by rw [← H.aT _ hq t htG, hpt]
  refine ⟨mul_mem hp htG, ?_, ?_, ?_⟩
  · rw [H.hom _ hp _ htG, mul_assoc, mul_inv_cancel_left, hpe]
  · intro q hq'
    rw [List.take_succ_eq_append_getElem hi] at hq'
    rcases List.mem_append.mp hq' with hq' | hq'
    · -- `t` fixes `y₀` at the earlier stage `q`
      have hqps : q ∈ ps := List.mem_of_mem_take hq'
      have h1 : T q (ψ t) = T q 1 := by rw [← H.aT q hqps t htG, ht.2 q hq', ← H.base hqps]
      have h2 : T q τi = T q (ψ t) := by rw [h1, hT q hq']
      exact (H.kerT q hqps _ _).mp h2
    · rw [List.mem_singleton.mp hq']
      exact (H.kerT _ hq _ _).mp hTt.symm
  · intro hs
    obtain ⟨h, hh, he⟩ := hex hs
    have hhG : h ∈ G₀ := hh.1
    refine ⟨t⁻¹ * h, ?_, ?_⟩
    · rw [List.take_succ_eq_append_getElem hi, vsBKs_snoc]
      refine ⟨⟨mul_mem (inv_mem htG) hhG, fun q hq' => ?_⟩, ?_⟩
      · have hqps : q ∈ ps := List.mem_of_mem_take hq'
        rw [(H.act q hqps).mul _ (inv_mem htG) _ hhG, hh.2 q hq']
        conv_lhs => rw [← ht.2 q hq']
        rw [← (H.act q hqps).mul _ (inv_mem htG) _ htG, inv_mul_cancel, (H.act q hqps).one]
      · rw [(H.act _ hq).mul _ (inv_mem htG) _ hhG, H.aT _ hq h hhG, he, ← hTt, ← H.aT _ hq t htG,
          ← (H.act _ hq).mul _ (inv_mem htG) _ htG, inv_mul_cancel, (H.act _ hq).one]
    · rw [H.hom _ (inv_mem htG) _ hhG, H.inv htG, he]

theorem vsBDesc_missing {τ τi : M} {i : ℕ} {prod : Perm (Fin n)}
    (hok : VsBDescOK α y₀ G₀ ψ T ps τ i τi prod) (hi : i < ps.length)
    (hno : ¬ ∃ g ∈ vsBKs α y₀ G₀ (ps.take i), α ps[i] g y₀ = T ps[i] τi) :
    ¬ ∃ h ∈ G₀, ψ h = τ := by
  intro hs
  obtain ⟨h, hh, he⟩ := hok.2.2.2 hs
  exact hno ⟨h, hh, by rw [H.aT _ (List.getElem_mem hi) h hh.1, he]⟩

theorem vsBDesc_end {τ τi : M} {prod : Perm (Fin n)}
    (hok : VsBDescOK α y₀ G₀ ψ T ps τ ps.length τi prod) : prod ∈ G₀ ∧ ψ prod = τ := by
  obtain ⟨hp, hpe, hT, -⟩ := hok
  rw [List.take_length] at hT
  rw [H.fin τi hT, mul_one] at hpe
  exact ⟨hp, hpe⟩

end

/-! ### The program -/

/-- The step of the descent, on `[a, i, acc]` with `a = [ctx, ps, orbit lists, τ, 1]` and
`acc = [ok, τ_i, prod]`. -/
def vsBDescStep (tk fnd up cmp : ℕ) : Expr :=
  .ite (.get (arg 2) (.nat 0))
    (.letE (.call tk (mk3 (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 1)) (arg 1))
        (.get (arg 2) (.nat 1))))
      (.letE (.call fnd (mk2 (.var 1) (.get (.get (arg 0) (.nat 2)) (arg 1))))
        (.ite (.arith .lt (.var 2) (.length (.get (.get (arg 0) (.nat 2)) (arg 1))))
          (.letE (.get (.get (.get (.get (arg 0) (.nat 2)) (arg 1)) (.var 2)) (.nat 1))
            (mk3 (.nat 1) (.call up (mk3 (.get (arg 0) (.nat 0)) (.get (arg 2) (.nat 1)) (.var 3)))
              (.call cmp (mk2 (.get (arg 2) (.nat 2)) (.var 3)))))
          (mk3 (.nat 0) (.get (arg 2) (.nat 1)) (.get (arg 2) (.nat 2))))))
    (arg 2)

/-- The descent at base `b` (3 functions). -/
def vsBDescFuns (b tk fnd up cmp : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 1))) (mk3 (.nat 1) (.get (.var 0) (.nat 3)) (.get (.var 0) (.nat 4)))
    (vsBDescStep tk fnd up cmp)

/-- The argument of the descent. -/
def vsBDescIn (ctx : Val) (ps : List ℕ) (keyY : Y → List ℕ) (Ls : List (List (Y × Perm (Fin n))))
    (enc : M → Val) (τ : M) : Val :=
  .list [ctx, .list (ps.map .nat), .list (Ls.map (vsQPairs keyY)), enc τ, encPerm (1 : Perm (Fin n))]

/-- What the descent returns. -/
def VsBDescOut (G₀ : Subgroup (Perm (Fin n))) (ψ : Perm (Fin n) → M) (enc : M → Val) (τ : M)
    (w : Val) : Prop :=
  ∃ (ok : ℕ) (τm : M) (prod : Perm (Fin n)), w = .list [.nat ok, enc τm, encPerm prod] ∧
    (ok = 1 ∧ prod ∈ G₀ ∧ ψ prod = τ ∨ ok = 0 ∧ ¬ ∃ h ∈ G₀, ψ h = τ)

set_option maxHeartbeats 4000000 in
/-- **The descent.** -/
theorem vsBDesc_spec {P : Program} {b sot0 fa jp jm tk up cmp : ℕ}
    (h : P.HasAt b (vsBDescFuns b tk (sot0 + 8) up cmp))
    (hsot : P.HasAt sot0 (vsQSotFuns sot0 fa jp jm)) (hcmp : P.HasAt cmp (composeFuns cmp))
    {α : ℕ → Perm (Fin n) → Y → Y} {y₀ : Y} {G₀ : Subgroup (Perm (Fin n))}
    {ψ : Perm (Fin n) → M} {T : ℕ → M → Y} {ps : List ℕ} (H : VsBDescHyp α y₀ G₀ ψ T ps)
    {keyY : Y → List ℕ} (hk : Function.Injective keyY) {ctx : Val} {enc : M → Val}
    {Ls : List (List (Y × Perm (Fin n)))} (hLl : Ls.length = ps.length)
    (hLs : ∀ i (hi : i < Ls.length), VsBOrbL (α (ps.getD i 0)) (vsBKs α y₀ G₀ (ps.take i)) y₀ Ls[i])
    {S We Ctk Cup : ℕ} (hS1 : 1 ≤ S) (hLw : ∀ L ∈ Ls, VsBPW S keyY L)
    (hW : ∀ τ', (enc τ').wt ≤ We) (hTw : ∀ q ∈ ps, ∀ τ', (natList (0 :: keyY (T q τ'))).wt ≤ S)
    (htk : ∀ q ∈ ps, ∀ τ', FunDet P tk (.list [ctx, .nat q, enc τ']) (natList (0 :: keyY (T q τ'))) Ctk)
    (hup : ∀ τ', ∀ t ∈ G₀, FunDet P up (.list [ctx, enc τ', encPerm t]) (enc ((ψ t)⁻¹ * τ')) Cup)
    (τ : M) :
    FunAll P b (vsBDescIn ctx ps keyY Ls enc τ) (fun w c => VsBDescOut G₀ ψ enc τ w ∧
      c ≤ ps.length * (Ctk + Cup + 10 ^ 6 * S ^ 4 + permK * (n + 1) ^ 3 +
          10 ^ 4 * ((vsBDescIn ctx ps keyY Ls enc τ).wt + We + 4 * (n + 1) ^ 2 + 20)) +
        loopModK * (ps.length + 1) * ((vsBDescIn ctx ps keyY Ls enc τ).wt + ps.length +
          (2 * (We + 4 * (n + 1) ^ 2 + 3) + 7) + 1)) := by
  classical
  set a := vsBDescIn ctx ps keyY Ls enc τ with ha
  set M0 := 2 * (We + 4 * (n + 1) ^ 2 + 3) + 7
  set Inv : ℕ → Val → Prop := fun i acc =>
    (∃ τi prod, acc = .list [.nat 1, enc τi, encPerm prod] ∧ VsBDescOK α y₀ G₀ ψ T ps τ i τi prod) ∨
    (∃ τi prod, acc = .list [.nat 0, enc τi, encPerm prod] ∧ ¬ ∃ h ∈ G₀, ψ h = τ) with hInv
  have wacc : ∀ (o : ℕ) τi (prod : Perm (Fin n)), o ≤ 1 →
      (Val.list [.nat o, enc τi, encPerm prod]).wt ≤ M0 := by
    intro o τi prod ho
    have := wt_list3_le (.nat o) (enc τi) (encPerm prod)
    have := wt_nat_le o
    have := hW τi
    have := wt_encPerm_le prod
    omega
  have hM : ∀ i acc, i ≤ ps.length → Inv i acc → acc.wt ≤ M0 := by
    intro i acc _ hinv
    rcases hinv with ⟨τi, prod, hac, -⟩ | ⟨τi, prod, hac, -⟩
    · rw [hac]; exact wacc 1 τi prod le_rfl
    · rw [hac]; exact wacc 0 τi prod (by omega)
  have la : ∀ k v, [ctx, .list (ps.map Val.nat), .list (Ls.map (vsQPairs keyY)), enc τ,
      encPerm (1 : Perm (Fin n))][k]? = some v → Det P [a] (.get (.var 0) (.nat k)) v _ :=
    fun k v hv => Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat k) hv
  have hkd := Det.length (la 1 _ rfl)
  rw [List.length_map] at hkd
  have hacc := Det.mk3 (Det.nat (P := P) (env := [a]) 1) (la 3 _ rfl) (la 4 _ rfl)
  have ea : (Val.list [ctx, .list (ps.map Val.nat), .list (Ls.map (vsQPairs keyY)), enc τ,
      encPerm (1 : Perm (Fin n))]).wt = a.wt := rfl
  have wsum := sum_wt_lt_wt_list [ctx, .list (ps.map Val.nat), .list (Ls.map (vsQPairs keyY)), enc τ,
      encPerm (1 : Perm (Fin n))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at wsum
  have hpl : (ps.map Val.nat).length < (Val.list (ps.map Val.nat)).wt := length_lt_wt_list _
  rw [List.length_map] at hpl
  refine (loopBdd_spec h hkd hacc ?_ (Or.inl ⟨τ, 1, rfl, vsBDesc_start H τ⟩) hM
    (D := fun _ => Ctk + Cup + 10 ^ 6 * S ^ 4 + permK * (n + 1) ^ 3 +
      10 ^ 4 * (a.wt + We + 4 * (n + 1) ^ 2 + 20)) ?_).mono ?_
  · have := wt_list3_le (.nat 1) (enc τ) (encPerm (1 : Perm (Fin n)))
    have := wt_nat_le 1; have := wt_nat_le 3; have := wt_nat_le 4
    have := wt_list_eq (ps.map Val.nat)
    have := wt_list_eq (Ls.map (vsQPairs keyY))
    have := ctx.two_le_size; have := ctx.size_le_wt
    omega
  · intro i acc hi hinv
    have hip : i < ps.length := hi
    have hiL : i < Ls.length := by omega
    have wM := hM i acc hi.le hinv
    have wsa := wt_stepArg_le a i acc
    have wps : (Val.list (ps.map Val.nat)).wt < a.wt := by omega
    have hD0 : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ hS1
    rcases hinv with ⟨τi, prod, hac, hok⟩ | ⟨τi, prod, hac, hno⟩
    swap
    · -- already failed: return the accumulator
      subst hac
      have g2 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, .list [.nat 0, enc τi, encPerm prod]])
        (j := 2) rfl
      have d0 := Det.get' g2 (Det.nat 0) (show [Val.nat 0, enc τi, encPerm prod][0]? = some (.nat 0) from rfl)
      refine (Det.ite_zero d0 g2).post fun c hc => ⟨Or.inr ⟨τi, prod, rfl, hno⟩, ?_⟩
      have := wt_nat_le 0
      omega
    · subst hac
      set acc := Val.list [.nat 1, enc τi, encPerm prod]
      set sa := Val.list [a, .nat i, acc]
      set q := ps[i]
      have hq : q ∈ ps := List.getElem_mem hip
      have hqd : ps.getD i 0 = q := by simp [q, hip]
      set L := Ls[i]
      have hLv : (Ls.map (vsQPairs keyY))[i]? = some (vsQPairs keyY L) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hiL]; rfl
      have hOL := hLs i hiL
      rw [hqd] at hOL
      have hPW := hLw L (List.getElem_mem hiL)
      -- in the environment `[sa]`
      have g0 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, acc]) (j := 0) rfl
      have g1 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, acc]) (j := 1) rfl
      have g2 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, acc]) (j := 2) rfl
      have d0 := Det.get' g2 (Det.nat 0) (show [Val.nat 1, enc τi, encPerm prod][0]? = some (.nat 1) from rfl)
      have dctx := Det.get' g0 (Det.nat 0)
        (show [ctx, .list (ps.map Val.nat), .list (Ls.map (vsQPairs keyY)), enc τ,
          encPerm (1 : Perm (Fin n))][0]? = some ctx from rfl)
      have dq := Det.get' (Det.get' g0 (Det.nat 1)
        (show [ctx, .list (ps.map Val.nat), .list (Ls.map (vsQPairs keyY)), enc τ,
          encPerm (1 : Perm (Fin n))][1]? = some (.list (ps.map Val.nat)) from rfl)) g1
        (show (ps.map Val.nat)[i]? = some (.nat q) by simp [q, hip])
      have dτ := Det.get' g2 (Det.nat 1) (show [Val.nat 1, enc τi, encPerm prod][1]? = some (enc τi) from rfl)
      have dkey := Det.call (Det.mk3 dctx dq dτ) (htk q hq τi)
      set kv := natList (0 :: keyY (T q τi))
      set idx := L.findIdx fun p => decide (p.1 = T q τi)
      have gA : ∀ rest (j : ℕ) v, [a, .nat i, acc][j]? = some v → Det P (sa :: rest) (arg j) v _ :=
        fun rest j v hv => Det.arg' hv
      have gL : ∀ rest, Det P (sa :: rest) (.get (.get (arg 0) (.nat 2)) (arg 1)) (vsQPairs keyY L) _ :=
        fun rest => Det.get' (Det.get' (gA rest 0 a rfl) (Det.nat 2)
          (show [ctx, .list (ps.map Val.nat), .list (Ls.map (vsQPairs keyY)), enc τ,
            encPerm (1 : Perm (Fin n))][2]? = some (.list (Ls.map (vsQPairs keyY))) from rfl))
          (gA rest 1 _ rfl) hLv
      have didx := Det.call (Det.mk2 (Det.var' (P := P) (env := [sa, kv]) (i := 1) rfl) (gL [kv]))
        (vsB_find hsot hk hS1 hPW (hTw q hq τi))
      have eLl : (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2]).length = L.length :=
        List.length_map _
      have wL : (vsQPairs keyY L).wt < a.wt := by
        have h1 : (vsQPairs keyY L).wt < (Val.list (Ls.map (vsQPairs keyY))).wt :=
          wt_le_wt_list (List.mem_map_of_mem (List.getElem_mem hiL))
        omega
      have wkv : kv.wt ≤ S := hTw q hq τi
      have hidxl : idx ≤ L.length := List.findIdx_le_length
      have wLl : L.length + 1 ≤ S := hPW.1
      have widx := wt_nat_le idx
      have wτi := hW τi
      have wpr := wt_encPerm_le prod
      have wacc' := wacc 1 τi prod le_rfl
      have wctx : ctx.wt < a.wt := by omega
      have wLs : (Val.list (Ls.map (vsQPairs keyY))).wt < a.wt := by omega
      have wq : (Val.nat q).wt < (Val.list (ps.map Val.nat)).wt := wt_le_wt_list (List.mem_map_of_mem hq)
      have w1 := wt_nat_le 1; have w0 := wt_nat_le 0; have w2 := wt_nat_le 2
      have wk3 := wt_list3_le ctx (.nat q) (enc τi)
      have wk2 := wt_list2_le kv (vsQPairs keyY L)
      have h34 : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by norm_num)
      have h14 : S ≤ S ^ 4 := Nat.le_self_pow (by norm_num) _
      by_cases hf : idx < L.length
      · -- found
        set p := L[idx]
        have hp1 : p.1 = T q τi := by
          have := List.findIdx_getElem (xs := L) (p := fun p => decide (p.1 = T q τi)) (w := hf)
          exact of_decide_eq_true this
        have hpL : p ∈ L := List.getElem_mem hf
        obtain ⟨ht, hpt⟩ := hOL.pr p hpL
        have htG : p.2 ∈ G₀ := ht.1
        have hv : (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2])[idx]? =
            some (.list [natList (0 :: keyY p.1), encPerm p.2]) := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hf]; rfl
        have env2 := [sa, kv, Val.nat idx]
        have dlt := Det.arith' (op := .lt) (Det.var' (P := P) (env := [sa, kv, .nat idx]) (i := 2) rfl)
          (Det.length (gL [kv, .nat idx])) (z := 1) (by
            show (if idx < (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2]).length then 1 else 0) = 1
            rw [eLl, if_pos hf])
        have dt := Det.get' (Det.get' (gL [kv, .nat idx]) (Det.var' (P := P) (env := [sa, kv, .nat idx])
          (i := 2) rfl) hv) (Det.nat 1)
          (show [natList (0 :: keyY p.1), encPerm p.2][1]? = some (encPerm p.2) from rfl)
        have dctx3 := Det.get' (gA [kv, .nat idx, encPerm p.2] 0 a rfl) (Det.nat 0)
          (show [ctx, .list (ps.map Val.nat), .list (Ls.map (vsQPairs keyY)), enc τ,
            encPerm (1 : Perm (Fin n))][0]? = some ctx from rfl)
        have dτ3 := Det.get' (gA [kv, .nat idx, encPerm p.2] 2 acc rfl) (Det.nat 1)
          (show [Val.nat 1, enc τi, encPerm prod][1]? = some (enc τi) from rfl)
        have dpr3 := Det.get' (gA [kv, .nat idx, encPerm p.2] 2 acc rfl) (Det.nat 2)
          (show [Val.nat 1, enc τi, encPerm prod][2]? = some (encPerm prod) from rfl)
        have dt3 := Det.var' (P := P) (env := [sa, kv, .nat idx, encPerm p.2]) (i := 3) rfl
        have dup := Det.call (Det.mk3 dctx3 dτ3 dt3) (hup τi p.2 htG)
        have dcmp := Det.call (Det.mk2 dpr3 dt3) (compose_spec hcmp prod p.2)
        have dres := Det.mk3 (Det.nat (P := P) (env := [sa, kv, .nat idx, encPerm p.2]) 1) dup dcmp
        have dall := Det.ite_pos (e := arg 2) d0 one_ne_zero (Det.letE dkey (Det.letE didx
          (Det.ite_pos (e := mk3 (.nat 0) (.get (arg 2) (.nat 1)) (.get (arg 2) (.nat 2))) dlt one_ne_zero
            (Det.letE dt dres))))
        refine dall.post fun c hc => ⟨Or.inl ⟨(ψ p.2)⁻¹ * τi, prod * p.2, rfl,
          vsBDesc_found H hok hip ht (by rw [← hp1]; exact hpt)⟩, ?_⟩
        have wpi := (hPW.2.2 p hpL).1
        have wt1 := wt_encPerm_le p.2
        have wt2 := wt_encPerm_le (prod * p.2)
        have wnew := hW ((ψ p.2)⁻¹ * τi)
        have wo3 := wt_list3_le (.nat 1) (enc ((ψ p.2)⁻¹ * τi)) (encPerm (prod * p.2))
        have wu3 := wt_list3_le ctx (enc τi) (encPerm p.2)
        have wc2 := wt_list2_le (encPerm prod) (encPerm p.2)
        have wi1 := wt_nat_le i
        have hiS : i < a.wt := by omega
        have h2n : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
        have eidx : (Val.nat (List.findIdx (fun q_1 => decide (q_1.1 = T q τi)) L)).wt = (Val.nat idx).wt := rfl
        have esa : (Val.list [a, Val.nat i, acc]).wt = sa.wt := rfl
        have hidxS : idx ≤ S := by omega
        have eacc : acc.wt = (Val.list [Val.nat 1, enc τi, encPerm prod]).wt := rfl
        clear * - wLs wLl eacc eLl hc wsa wacc' wk3 wk2 wkv widx hidxS wpi wt1 wt2 wnew wo3 wu3 wc2 wτi wpr w1 w0 w2 wL wctx wq wps hiS wi1 eidx esa h34 h14 hD0 h2n hidxl
        omega
      · -- not found
        have hidx : idx = L.length := by omega
        have dlt := Det.arith' (op := .lt) (Det.var' (P := P) (env := [sa, kv, .nat idx]) (i := 2) rfl)
          (Det.length (gL [kv, .nat idx])) (z := 0) (by
            show (if idx < (L.map fun q => Val.list [natList (0 :: keyY q.1), encPerm q.2]).length then 1 else 0) = 0
            rw [eLl, if_neg hf])
        have dτ2 := Det.get' (gA [kv, .nat idx] 2 acc rfl) (Det.nat 1)
          (show [Val.nat 1, enc τi, encPerm prod][1]? = some (enc τi) from rfl)
        have dpr2 := Det.get' (gA [kv, .nat idx] 2 acc rfl) (Det.nat 2)
          (show [Val.nat 1, enc τi, encPerm prod][2]? = some (encPerm prod) from rfl)
        have dres := Det.mk3 (Det.nat (P := P) (env := [sa, kv, .nat idx]) 0) dτ2 dpr2
        have dall := Det.ite_pos (e := arg 2) d0 one_ne_zero (Det.letE dkey (Det.letE didx
          (Det.ite_zero (t := .letE (.get (.get (.get (.get (arg 0) (.nat 2)) (arg 1)) (.var 2)) (.nat 1))
            (mk3 (.nat 1) (.call up (mk3 (.get (arg 0) (.nat 0)) (.get (arg 2) (.nat 1)) (.var 3)))
              (.call cmp (mk2 (.get (arg 2) (.nat 2)) (.var 3))))) dlt dres)))
        have hno : ¬ ∃ g ∈ vsBKs α y₀ G₀ (ps.take i), α ps[i] g y₀ = T ps[i] τi := by
          rintro ⟨g, hg, hge⟩
          have hm : T q τi ∈ L.map Prod.fst := (hOL.mem _).2 ⟨g, hg, hge⟩
          obtain ⟨r, hr, hr1⟩ := List.mem_map.mp hm
          exact hf (List.findIdx_lt_length_of_exists ⟨r, hr, by simp [hr1]⟩)
        refine dall.post fun c hc => ⟨Or.inr ⟨τi, prod, rfl, vsBDesc_missing H hok hip hno⟩, ?_⟩
        have wo3 := wt_list3_le (.nat 0) (enc τi) (encPerm prod)
        have wi1 := wt_nat_le i
        have hiS : i < a.wt := by omega
        have eidx : (Val.nat (List.findIdx (fun q_1 => decide (q_1.1 = T q τi)) L)).wt = (Val.nat idx).wt := rfl
        have esa : (Val.list [a, Val.nat i, acc]).wt = sa.wt := rfl
        have hidxS : idx ≤ S := by omega
        have eacc : acc.wt = (Val.list [Val.nat 1, enc τi, encPerm prod]).wt := rfl
        clear * - wLs wLl eacc eLl hc wsa wacc' wk3 wk2 wkv widx hidxS wo3 wτi wpr w1 w0 w2 wL wctx wq wps hiS wi1 eidx esa h34 h14 hD0 hidxl
        omega
  · rintro w c ⟨hw, hc⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    refine ⟨?_, hc⟩
    rcases hw with ⟨τi, prod, rfl, hok⟩ | ⟨τi, prod, rfl, hno⟩
    · exact ⟨1, τi, prod, rfl, Or.inl ⟨rfl, vsBDesc_end H hok⟩⟩
    · exact ⟨0, τi, prod, rfl, Or.inr ⟨rfl, hno⟩⟩

end GI.Impl
