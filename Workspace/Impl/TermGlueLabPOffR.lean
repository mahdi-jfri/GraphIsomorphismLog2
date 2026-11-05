module

public import Workspace.Impl.TermGlueLabPYLab

@[expose] public section

/-!
# The transporters `t_a(h)` for one element `h`: one row

Step 3 of the label program (Theorem A.23: "for a later `h` carrying type `a` to
type `c`, the known membership in `N Iso_H(z_a, z_c)`, together with constructive
factorization in the normalized product `N Aut_H(z_a)`, supplies the required local
`N`-transporter").

Fix `h ∈ H` and a row `x_i`. Its pair `[J, n]` from the labels of `x` (`TmGLPXOut`) names the
first row `x_J` of its type, which is the representative of that type. The program looks for
an `N`-transporter from the first row of the type of `x_J^h` to `x_J^h`:

1. it takes the first column `l` with a nonempty stored coset `Iso_H(x_J, y_l) = g ⟨A⟩`
   (`tmCsFirstF`), and reads `g`;
2. it forms `w = h⁻¹ g`, so that `(x_J^h)^w = x_J^g = y_l` and `w ∈ H`;
3. it runs the search of `TermGlueLabPFind` with this `w` and `l`.

The result is `TmGLPOItem`: the search result for `x_J^h` (`tmGLPORow_spec`). No string call.
The input is `[a, i]` with `a = [gens N, vs, q, xl, h⁻¹]` (`tmGLPOIn`).
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens Membership NormalizedFactor)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-- One row, on `[a, i]` with `a = [gens N, vs, q, xl, h⁻¹]`; the composition sits at
`rel + 3` (inside the reading module). -/
def tmGLPORowF (first find rel : ℕ) : Expr :=
  .letE (.get (.get (.get (arg 0) (.nat 3)) (arg 1)) (.nat 0))
    (.letE (.call first (mk2 (mk4 (.get (arg 0) (.nat 1))
        (.arith .mul (.var 1) (.get (arg 0) (.nat 2))) (.nat 1) (.get (arg 0) (.nat 2))) (.nat 0)))
      (.call find (mk2 (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
          (.get (arg 0) (.nat 2)) (.var 2))
        (.call (rel + 3) (mk2 (.get (arg 0) (.nat 4))
          (.get (.get (.get (arg 0) (.nat 1))
            (.arith .add (.arith .mul (.var 1) (.get (arg 0) (.nat 2))) (.var 2))) (.nat 0)))))))

/-- The context `[gens N, vs, q, xl, h⁻¹]`. -/
def tmGLPOIn (σN : List (Perm (Fin n))) (vs : List Val) (q : ℕ) (xl : List Val)
    (hi : Perm (Fin n)) : Val :=
  .list [encGroup σN, .list vs, .nat q, .list xl, encPerm hi]

/-- The result for row `i`: the search result for `x_J^h`, with `x_J` the first row of the type
of `x_i`. -/
def TmGLPOItem (N : Subgroup (Perm (Fin n))) {q : ℕ} (X : Fin q → Ω) (h : Perm (Fin n))
    (i : Fin q) (u : Val) : Prop :=
  ∃ J : Fin q, TmGLPFirst N X (X i) J ∧ TmGLPFindOut N X (X J ↼ h) u

/-- The cost bound of one row, for a context of weight `W`. -/
def tmGLPORowC (pm pf : Prim) (W : ℕ) : ℕ :=
  4 * tmGLPFindC pm pf (100 * (W + 1) ^ 2) + 10 ^ 7 * (W + 1) ^ 3

/-- A canonical answer of a coset is a list. -/
theorem tmGLP_ansC_list {v : Val} {A : Set (Perm (Fin n))} (h : AnsC (Equiv.refl (Fin n)) v A) :
    ∃ l : List Val, v = .list l := by
  rcases h with ⟨rfl, -⟩ | ⟨x, gs, rfl, -, -⟩
  · exact ⟨[], rfl⟩
  · exact ⟨_, rfl⟩

/-- **The stored element of the first nonempty coset of a row.** If the coset table has a
nonempty entry in row `J`, the first search of the row finds a column `L < q` whose entry is
`[g, gs]` with `g ∈ Iso_H(x_J, y_L)`. -/
theorem tmGLP_first_col {H : Subgroup (Perm (Fin n))} {q : ℕ} {X Y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H X Y vs) (J : Fin q) (hY : ∃ l : Fin q, (Iso H (X J) (Y l)).Nonempty)
    {L : ℕ} (hLq : L ≤ q)
    (hLe : ∀ j', 0 ≤ j' → j' < L → vs[J.1 * q + 1 * j']? = some (.list []))
    (hLn : L < q → ∃ a l, vs[J.1 * q + 1 * L]? = some (.list (a :: l))) :
    ∃ hL : L < q, ∃ g : Perm (Fin n), ∃ gs : List (Perm (Fin n)),
      vs[J.1 * q + L]? = some (.list [encPerm g, encGroup gs]) ∧ g ∈ Iso H (X J) (Y ⟨L, hL⟩) := by
  obtain ⟨l0, k, hk⟩ := hY
  have hL : L < q := by
    by_contra hc
    obtain ⟨v, hv, hA⟩ := hT.2 J l0
    have h0 := hLe l0.1 (Nat.zero_le _) (by omega)
    rw [one_mul] at h0
    rw [h0] at hv
    have := tmCs_ansC_nil hA (Option.some.inj hv).symm
    rw [this] at hk
    exact hk
  obtain ⟨v, hv, hA⟩ := hT.2 J ⟨L, hL⟩
  obtain ⟨a0, l1, hl1⟩ := hLn hL
  rw [one_mul] at hl1
  rw [hl1] at hv
  cases hv
  rcases id hA with ⟨h1, -⟩ | ⟨g, gs, hv, -, -⟩
  · cases h1
  have hI := tmCs_ansC_cons hA hv
  refine ⟨hL, g, gs, hv ▸ hl1, ?_⟩
  rw [hI]
  exact ⟨1, (gens gs).one_mem, mul_one g⟩

set_option maxHeartbeats 4000000 in
/-- **One row.** For `h ∈ H`, a coset table `vs` of `x, y` with a nonempty entry in every row,
and the labels `xl` of `x`, row `i` gives the search result for `x_J^h` (`TmGLPOItem`). -/
theorem tmGLPORow_spec (hm : Membership) (hfac : NormalizedFactor) {P : Program}
    {f first find rel jm jf : ℕ} (hf : P.funs[f]? = some (tmGLPORowF first find rel))
    (hfirst : P.funs[first]? = some (tmCsFirstF first))
    (hfd : P.HasAt find (tmGLPFindFuns find rel)) (hr : TmGLPRelAt P rel jm jf)
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {H : Subgroup (Perm (Fin n))} {σN : List (Perm (Fin n))} (hNH : gens σN ≤ H)
    (hn : GI.Multicoset.Normalizes H (gens σN)) {q : ℕ} {X Y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H X Y vs) (hY : ∀ j : Fin q, ∃ l : Fin q, (Iso H (X j) (Y l)).Nonempty)
    {xl : List Val} (hxl : TmGLPXOut (gens σN) X (.list xl)) {h : Perm (Fin n)} (hh : h ∈ H)
    (i : Fin q) :
    FunAll P f (.list [tmGLPOIn σN vs q xl h⁻¹, .nat i]) (fun u c =>
      TmGLPOItem (gens σN) X h i u ∧
        c ≤ tmGLPORowC (membershipPrim hm) (normalizedFactorPrim hfac)
          (tmGLPOIn σN vs q xl h⁻¹).wt) := by
  set a := tmGLPOIn σN vs q xl h⁻¹ with ha
  set W := a.wt with hW
  set va : List Val := [encGroup σN, .list vs, .nat q, .list xl, encPerm h⁻¹] with hva
  obtain ⟨l, hl0, hll, hlv⟩ := hxl
  cases hl0
  obtain ⟨v, hv, J, x, hxN, rfl, hfst, -⟩ := hlv i
  apply FunAll.intro hf
  -- weights of the context
  have wvs : (Val.list vs).wt < W := wt_le_wt_list (by simp)
  have wN : (encGroup σN).wt < W := wt_le_wt_list (by simp)
  have wq : (Val.nat q).wt < W := wt_le_wt_list (by simp)
  have wxl : (Val.list xl).wt < W := wt_le_wt_list (by simp)
  have whi : (encPerm h⁻¹).wt < W := wt_le_wt_list (by simp)
  have hnW : n < W := (tmGLP_n_lt_wt h⁻¹).trans whi
  have hqW : q < W := by
    have := length_lt_wt_list xl
    omega
  have wv : (Val.list [.nat J, encPerm x]).wt < W :=
    (wt_le_wt_list (List.mem_of_getElem? hv)).trans wxl
  have hJW : (Val.nat J).wt < W := (wt_le_wt_list (by simp)).trans wv
  have wi := wt_nat_le i
  have w2 := wt_list2_le a (.nat i)
  have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  -- `J`
  have g0 := Det.arg' (P := P) (vs := [a, .nat i]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [a, .nat i]) (rest := []) (j := 1) rfl
  have dxl := Det.get' g0 (Det.nat 3) (vs := va) (v := .list xl) rfl
  have dv := Det.get' dxl g1 hv
  have dJ := Det.get' dv (Det.nat 0) (vs := [.nat J, encPerm x]) (v := .nat J) rfl
  refine EvalAll.letE dJ fun vJ cJ hvJ => ?_
  obtain ⟨rfl, hcJ⟩ := hvJ
  -- the first column `L`
  have hl' : ∀ j < q, ∃ l', vs[J.1 * q + 1 * j]? = some (.list l') := by
    intro j hj
    obtain ⟨u, hu, hA'⟩ := hT.2 J ⟨j, hj⟩
    obtain ⟨l', rfl⟩ := tmGLP_ansC_list hA'
    exact ⟨l', by rw [one_mul]; exact hu⟩
  obtain ⟨L, hL, -, hLq, hLe, hLn⟩ := tmCs_first_spec hfirst (vs := vs) (base := J.1 * q)
    (stride := 1) (q := q) hl' q 0 (by omega) (by omega)
  obtain ⟨hLlt, g, gs, hg, hgI⟩ := tmGLP_first_col hT J (hY J) hLq hLe hLn
  set A : Val := .list [a, .nat i] with hA
  have e0 := Det.arg' (P := P) (vs := [a, .nat i]) (rest := [.nat J]) (j := 0) rfl
  have eJ := Det.var' (P := P) (env := [A, .nat J]) (i := 1) (v := .nat J) rfl
  have evs := Det.get' e0 (Det.nat 1) (vs := va) (v := .list vs) rfl
  have eq := Det.get' e0 (Det.nat 2) (vs := va) (v := .nat q) rfl
  have eJq := Det.arith' (op := .mul) eJ eq (z := J.1 * q) rfl
  have dL := Det.call (Det.mk2 (Det.mk4 evs eJq (Det.nat 1) eq) (Det.nat 0)) hL
  refine EvalAll.letE dL fun vL cL hvL => ?_
  obtain ⟨rfl, hcL⟩ := hvL
  -- `w = h⁻¹ g` and the search
  have f0 := Det.arg' (P := P) (vs := [a, .nat i]) (rest := [.nat J, .nat L]) (j := 0) rfl
  have fJ := Det.var' (P := P) (env := [A, .nat J, .nat L]) (i := 1) (v := .nat J) rfl
  have fL := Det.var' (P := P) (env := [A, .nat J, .nat L]) (i := 2) (v := .nat L) rfl
  have fN := Det.get' f0 (Det.nat 0) (vs := va) (v := encGroup σN) rfl
  have fvs := Det.get' f0 (Det.nat 1) (vs := va) (v := .list vs) rfl
  have fq := Det.get' f0 (Det.nat 2) (vs := va) (v := .nat q) rfl
  have fhi := Det.get' f0 (Det.nat 4) (vs := va) (v := encPerm h⁻¹) rfl
  have fJq := Det.arith' (op := .mul) fJ fq (z := J.1 * q) rfl
  have fidx := Det.arith' (op := .add) fJq fL (z := J.1 * q + L) rfl
  have fe := Det.get' fvs fidx hg
  have fg := Det.get' fe (Det.nat 0) (vs := [encPerm g, encGroup gs]) (v := encPerm g) rfl
  have fw := Det.call (Det.mk2 fhi fg) (compose_spec hr.comp h⁻¹ g)
  have dargs := Det.mk2 (Det.mk4 fN fvs fq fL) fw
  have hwH : h⁻¹ * g ∈ H := H.mul_mem (H.inv_mem hh) hgI.1
  have hZ : X J ↼ h ↼ (h⁻¹ * g) = Y ⟨L, hLlt⟩ := by
    rw [act_act, mul_inv_cancel_left]; exact hgI.2
  have hspec := tmGLPFind_spec hm hfac hfd hr hjm hjf hNH hn hT ⟨L, hLlt⟩ hwH hZ
  have ectx : Val.list [encGroup σN, .list vs, .nat q, .nat L] = tmGLPCtx σN vs q L := rfl
  rw [ectx] at dargs
  -- weights of the search input
  have wL : (Val.nat L).wt < W := by
    have := wt_nat_le L
    have := (Val.nat q).two_le_size
    rw [wt_nat, wt_nat] at *
    have := GI.Machine.len_mono hLq
    omega
  have wctx := wt_list4_le (encGroup σN) (.list vs) (.nat q) (.nat L)
  have wenc := wt_encPerm_le (h⁻¹ * g)
  have hn2 : (n + 1) ^ 2 ≤ (W + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have win := wt_list2_le (tmGLPCtx σN vs q L) (encPerm (h⁻¹ * g))
  have ectxw : (tmGLPCtx σN vs q L).wt = (Val.list [encGroup σN, .list vs, .nat q, .nat L]).wt :=
    rfl
  have hinW : (Val.list [tmGLPCtx σN vs q L, encPerm (h⁻¹ * g)]).wt ≤ 100 * (W + 1) ^ 2 := by
    omega
  have hmono := tmGLPFindC_mono (membershipPrim hm) (normalizedFactorPrim hfac) hinW
  refine EvalAll.call_funAll dargs fun vin ca hvin => ?_
  obtain ⟨rfl, hca⟩ := hvin
  refine FunAll.mono (FunAll.wt_lt hspec) fun u cb hu => ⟨⟨J, hfst, hu.1.1⟩, ?_⟩
  -- the cost
  have hcb : cb ≤ tmGLPFindC (membershipPrim hm) (normalizedFactorPrim hfac)
      (Val.list [tmGLPCtx σN vs q L, encPerm (h⁻¹ * g)]).wt := hu.1.2
  have eva : a.wt = (Val.list va).wt := rfl
  have eA : A.wt = (Val.list [a, .nat i]).wt := rfl
  have hub := hu.2
  have hJq : J.1 * q ≤ (W + 1) ^ 2 :=
    (Nat.mul_le_mul (show J.1 ≤ W + 1 by omega) (show q ≤ W + 1 by omega)).trans_eq (sq _).symm
  have wJq : (Val.nat (J.1 * q)).wt ≤ (W + 1) ^ 2 + 2 := by
    have := wt_nat_le (J.1 * q)
    omega
  have wJqL : (Val.nat (J.1 * q + L)).wt ≤ (W + 1) ^ 2 + W + 4 := by
    have := wt_nat_le (J.1 * q + L)
    omega
  have wfc := wt_list4_le (.list vs) (.nat (J.1 * q)) (.nat 1) (.nat q)
  have efc : (tmCsFirstCtx vs (J.1 * q) 1 q).wt =
      (Val.list [.list vs, .nat (J.1 * q), .nat 1, .nat q]).wt := rfl
  have wfc2 := wt_list2_le (.list [.list vs, .nat (J.1 * q), .nat 1, .nat q]) (.nat 0)
  have hfc : (q - 0 + 1) * tmCsFirstK (tmCsFirstCtx vs (J.1 * q) 1 q).wt ≤
      10 ^ 4 * (W + 1) ^ 3 := by
    unfold tmCsFirstK
    have : (tmCsFirstCtx vs (J.1 * q) 1 q).wt ≤ 10 * (W + 1) ^ 2 := by
      have := wt_nat_le 1
      omega
    calc (q - 0 + 1) * (200 * (tmCsFirstCtx vs (J.1 * q) 1 q).wt + 400)
        ≤ (W + 1) * (200 * (10 * (W + 1) ^ 2) + 400) := Nat.mul_le_mul (by omega) (by omega)
      _ = 2000 * ((W + 1) * (W + 1) ^ 2) + 400 * (W + 1) := by ring
      _ ≤ 10 ^ 4 * (W + 1) ^ 3 := by
        have : (W + 1) * (W + 1) ^ 2 = (W + 1) ^ 3 := by ring
        omega
  have wg : (Val.list [encPerm g, encGroup gs]).wt < (Val.list vs).wt :=
    wt_le_wt_list (List.mem_of_getElem? hg)
  have wgg : (encPerm g).wt < (Val.list [encPerm g, encGroup gs]).wt := wt_le_wt_list (by simp)
  have wcomp := wt_list2_le (encPerm h⁻¹) (encPerm g)
  have hn3 : (n + 1) ^ 3 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have wJL : (Val.nat L).wt ≤ W := by omega
  have wva := wt_list_le va
  have hz : (tmGLPCtx σN vs q L).wt ≤ 10 * W + 20 := by rw [ectxw]; omega
  have hi1 : (tmCsFirstCtx vs (J.1 * q) 1 q).wt ≤ 10 * (W + 1) ^ 2 := by
    have := wt_nat_le 1
    omega
  have hk1 : (Val.list [.list [.list vs, .nat (J.1 * q), .nat 1, .nat q], .nat 0]).wt ≤
      30 * (W + 1) ^ 2 := by
    have := wt_nat_le 0
    have := wt_nat_le 1
    omega
  have ho1 : (Val.list [.list vs, .nat (J.1 * q), .nat 1, .nat q]).wt ≤ 10 * (W + 1) ^ 2 := hi1
  have hiq := i.2
  have hfw : (Val.list [encPerm h⁻¹, encPerm g]).wt ≤ 4 * W + 6 := by omega
  clear wctx ectxw efc wfc wfc2 wcomp
  unfold tmGLPORowC
  generalize tmGLPFindC (membershipPrim hm) (normalizedFactorPrim hfac)
    (Val.list [tmGLPCtx σN vs q L, encPerm (h⁻¹ * g)]).wt = F at hcb hmono
  generalize tmGLPFindC (membershipPrim hm) (normalizedFactorPrim hfac) (100 * (W + 1) ^ 2) = F'
    at hmono ⊢
  generalize (q - 0 + 1) * tmCsFirstK (tmCsFirstCtx vs (J.1 * q) 1 q).wt = FC at hfc hcL
  have hpk : permK * (n + 1) ^ 3 ≤ 30000 * (W + 1) ^ 3 := by unfold permK; omega
  generalize permK * (n + 1) ^ 3 = PK at hpk hca
  beta_reduce at *
  generalize (W + 1) ^ 2 = S2 at *
  generalize (W + 1) ^ 3 = S3 at *
  omega

end GI.Impl
