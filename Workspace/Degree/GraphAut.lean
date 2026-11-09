module

public import Workspace.Degree.GraphRI
public import Workspace.Degree.GraphWhole

/-!
# Generators of the automorphism group

Lemma 9.5 of the paper. The loop runs over all pairs `(v, w)`. For each pair with a
rooted isomorphism `τ` of `X` it adds the automorphism `swPerm τ` and the generators of the ball
group of `v`. The closure of the result is `autGroup X` (`autGens_eq`).
-/

@[expose] public section

namespace GI.Degree

open GI.Lang GI.Cited GI.Algorithm GI.Impl GI.Assembly GI.Statement Equiv
open GI.Machine (BinOp)

variable {n D : ℕ}

/-- The entry of the table of `swMap`, on `[[τ, lv, lw, τ⁻¹, n], u]`. -/
def swapE : Expr :=
  let c := arg 0
  let u := arg 1
  .ite (.arith .lt (.get (.get c (.nat 1)) u) (.get c (.nat 4))) (.get (.get c (.nat 0)) u)
    (.ite (.arith .lt (.get (.get c (.nat 2)) u) (.get c (.nat 4))) (.get (.get c (.nat 3)) u) u)

/-- The context of the table of `swMap`. -/
noncomputable def swCtx (X : SimpleGraph (Fin n)) (v w : Fin n) (τ : Perm (Fin n)) : Val :=
  .list [encPerm τ, encFun (lev X v), encFun (lev X w), encPerm τ⁻¹, .nat n]

/-- The budget of an entry of the table. -/
def swT (n : ℕ) : ℕ := 1000 * levB n

/-- The cost of the table. -/
def swC (n : ℕ) : ℕ := n * (1000 * swT n) + mapK * (n + 1) * swT n

theorem swCtx_wt (X : SimpleGraph (Fin n)) (v w : Fin n) (τ : Perm (Fin n)) :
    (swCtx X v w τ).wt ≤ 5 * (2 * levB n + 1) + 4 := by
  have h1 : ∀ σ : Perm (Fin n), (encPerm σ).wt ≤ levB n := fun σ => by
    rw [encPerm_eq_encFun]
    exact wt_table_le fun i => (σ i).isLt.le
  have h2 : ∀ x : Fin n, (encFun (lev X x)).wt ≤ levB n := fun x => wt_table_le (lev_le X x)
  have h3 : (Val.nat n).wt ≤ levB n := wt_nat_levB (by omega)
  exact wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl)
    · exact h1 τ
    · exact h2 v
    · exact h2 w
    · exact h1 τ⁻¹
    · exact h3)

set_option maxHeartbeats 1000000 in
theorem swapE_lv {P : Program} (X : SimpleGraph (Fin n)) (v w : Fin n) (τ : Perm (Fin n))
    (u : Fin n) :
    Lv P [.list [swCtx X v w τ, .nat u]] (swT n) swapE (.nat (swMap X v w τ u)) 1000 := by
  classical
  have h0 := levB_pos n
  have hl := le_levB n
  have wc := swCtx_wt X v w τ
  have wu : (Val.nat u).wt ≤ levB n := wt_nat_levB (by omega)
  have w2 : (Val.list [swCtx X v w τ, .nat u]).wt ≤
      2 * (2 * (5 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hT : swT n = 1000 * levB n := rfl
  set E := [Val.list [swCtx X v w τ, .nat u]] with hE
  have a0 : Lv P E (swT n) (arg 0) (.list [encFun fun i => (τ i : ℕ), encFun (lev X v),
      encFun (lev X w), encFun fun i => (τ⁻¹ i : ℕ), .nat n]) 1 := by
    have := Lv.arg (P := P) (rest := []) (vs := [swCtx X v w τ, .nat u]) (j := 0) (T := swT n) rfl
      (by omega)
    rwa [swCtx, encPerm_eq_encFun, encPerm_eq_encFun] at this
  have a1 : Lv P E (swT n) (arg 1) (.nat u) 1 := Lv.arg rfl (by omega)
  have n0 : ∀ k, k ≤ 4 → Lv P E (swT n) (.nat k) (.nat k) 1 := fun k hk => Lv.nat k (by omega)
  have g := fun k (hk : k ≤ 4) {x : Val} (hx : [encFun fun i => (τ i : ℕ), encFun (lev X v),
      encFun (lev X w), encFun fun i => (τ⁻¹ i : ℕ), Val.nat n][k]? = some x) =>
    Lv.get a0 (n0 k hk) hx
  have gt := Lv.tget (g 0 (by omega) rfl) a1
  have gv := Lv.tget (g 1 (by omega) rfl) a1
  have gw := Lv.tget (g 2 (by omega) rfl) a1
  have gi := Lv.tget (g 3 (by omega) rfl) a1
  have gn := g 4 (by omega) rfl
  have hv := lev_le X v u
  have hw := lev_le X w u
  have c1 := Lv.arith (op := .lt) (z := if lev X v u < n then 1 else 0) gv gn rfl (by split <;> omega)
  have c2 := Lv.arith (op := .lt) (z := if lev X w u < n then 1 else 0) gw gn rfl (by split <;> omega)
  by_cases h1 : X.Reachable v u
  · rw [if_pos (lev_lt_iff.2 h1)] at c1
    have e : swMap X v w τ u = τ u := by simp [swMap, h1]
    rw [e]
    exact Lv.mono (e := swapE) (Lv.ite_pos (e := .ite _ _ _) c1 (by omega) gt) (by norm_num)
  · rw [if_neg (fun h => h1 (lev_lt_iff.1 h))] at c1
    by_cases h2 : X.Reachable w u
    · rw [if_pos (lev_lt_iff.2 h2)] at c2
      have e : swMap X v w τ u = τ⁻¹ u := by simp [swMap, h1, h2]
      rw [e]
      exact Lv.mono (e := swapE) (Lv.ite_zero (t := _) c1 (Lv.ite_pos (e := arg 1) c2 (by omega) gi))
        (by norm_num)
    · rw [if_neg (fun h => h2 (lev_lt_iff.1 h))] at c2
      have e : swMap X v w τ u = u := by simp [swMap, h1, h2]
      rw [e]
      exact Lv.mono (e := swapE) (Lv.ite_zero (t := _) c1 (Lv.ite_zero (t := _) c2 a1)) (by norm_num)

/-- **The table of `swPerm`.** -/
theorem sw_spec {P : Program} {a : ℕ} (h : P.HasAt a (tabFuns a swapE)) {X : SimpleGraph (Fin n)}
    {v w : Fin n} {τ : Perm (Fin n)} (hτ : IsRooted X v X w τ) :
    FunDet P a (.list [swCtx X v w τ, ids n]) (encPerm (swPerm hτ)) (swC n) := by
  have h0 := levB_pos n
  have hl := le_levB n
  have wc := swCtx_wt X v w τ
  have wi : (ids n).wt ≤ levB n := wt_table_le fun i => i.isLt.le
  have ws : (encPerm (swPerm hτ)).wt ≤ levB n := by
    rw [encPerm_eq_encFun]
    exact wt_table_le fun i => (swPerm hτ i).isLt.le
  have w2 : (Val.list [swCtx X v w τ, ids n]).wt ≤
      2 * (2 * (5 * (2 * levB n + 1) + 4 + levB n) + 1) + 4 := wt_lit _ (by simp; omega)
  have hT : swT n = 1000 * levB n := rfl
  rw [encPerm_eq_encFun]
  exact tabN_spec (T := swT n) (K := 1000) (W := swT n) h (fun u => swapE_lv X v w τ u)
    (by rw [← encPerm_eq_encFun]; omega)

/-- The body of a step of the loop over pairs, on `[riCtx D X X, i, acc]`. -/
def autStepE (ri lev inv sw app : ℕ) : Expr :=
  let c := arg 0
  let nn := Expr.get c (.nat 2)
  let v := Expr.arith .div (arg 1) nn
  let w := Expr.arith .mod (arg 1) nn
  .letE (.call ri (mk3 c v w))
    (.ite (.length (.var 1))
      (.letE (.call lev (mk4 (.get c (.nat 0)) nn (.get c (.nat 3)) v))
      (.letE (.call lev (mk4 (.get c (.nat 0)) nn (.get c (.nat 3)) w))
      (.letE (.call inv (.get (.var 1) (.nat 0)))
      (.letE (.call sw (mk2 (mk5 (.get (.var 1) (.nat 0)) (.var 2) (.var 3) (.var 4) nn)
          (.get c (.nat 3))))
        (.call app (mk2 (arg 2) (.snoc (.get (.get (.var 1) (.nat 1)) (.nat 1)) (.var 5))))))))
      (arg 2))

/-- The functions of a step. One hundred and twenty-six functions. -/
def autStepFuns (a fd j : ℕ) : List Expr :=
  [autStepE (a + 20) (a + 21) (a + 5) (a + 1) (a + 17)] ++ tabFuns (a + 1) swapE ++
    invFuns (a + 5) ++ appendFuns (a + 17) ++ riFuns (a + 20) fd j

/-- What the list must give for the pair `(v, w)`. -/
def AutCond (X : SimpleGraph (Fin n)) (v w : Fin n) (L : List (Perm (Fin n))) : Prop :=
  ((∃ g ∈ autGroup X, g v = w) → ∃ s ∈ L, s v = w ∧
      ∀ u, ¬X.Reachable v u → ¬X.Reachable w u → s u = u) ∧
    (v = w → ballGroup (lev X v) (n - 1) X ≤ Subgroup.closure {g | g ∈ L})

/-- The invariant of the loop over pairs. -/
def AutInv (X : SimpleGraph (Fin n)) (i : ℕ) (acc : Val) : Prop :=
  ∃ L : List (Perm (Fin n)), acc = .list (L.map encPerm) ∧ L.length ≤ i * (n ^ 2 + 2) ∧
    (∀ s ∈ L, s ∈ autGroup X) ∧ ∀ v w : Fin n, (v : ℕ) * n + w < i → AutCond X v w L

theorem AutCond.mono {X : SimpleGraph (Fin n)} {v w : Fin n} {L L' : List (Perm (Fin n))}
    (h : AutCond X v w L) (hL : ∀ s ∈ L, s ∈ L') : AutCond X v w L' := by
  refine ⟨fun hg => ?_, fun hvw => ?_⟩
  · obtain ⟨s, hs, h1⟩ := h.1 hg
    exact ⟨s, hL s hs, h1⟩
  · exact (h.2 hvw).trans (Subgroup.closure_mono fun s hs => hL s hs)

/-- **The generators.** At the end of the loop, the closure of the list is `autGroup X`. -/
theorem autGens_eq {X : SimpleGraph (Fin n)} {L : List (Perm (Fin n))}
    (hL : ∀ s ∈ L, s ∈ autGroup X) (hc : ∀ v w : Fin n, AutCond X v w L) :
    Subgroup.closure {g | g ∈ L} = autGroup X := by
  refine eq_autGroup ((Subgroup.closure_le _).2 fun s hs => hL s hs) (fun v w hg => ?_)
    fun v => (hc v v).2 rfl
  obtain ⟨s, hs, h1⟩ := (hc v w).1 hg
  exact ⟨s, Subgroup.subset_closure hs, h1⟩

/-- A bound on the weights of the accumulator. -/
def AL (n : ℕ) : ℕ := (n ^ 2 * (n ^ 2 + 2) + 2) * (2 * WB n + 1) + 4

theorem permList_AL {L : List (Perm (Fin n))} (hl : L.length ≤ n ^ 2 * (n ^ 2 + 2) + 2) :
    (Val.list (L.map encPerm)).wt ≤ AL n := by
  have := wt_lit (L.map encPerm) (c := WB n) (by
    intro x hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
    exact perm_wt (by have := le_kB n; omega) g)
  simp only [List.length_map] at this
  refine this.trans ?_
  have := Nat.mul_le_mul_right (2 * WB n + 1) hl
  simp only [AL]
  omega

theorem autInv_wt {X : SimpleGraph (Fin n)} {i : ℕ} (hi : i ≤ n * n) {acc : Val}
    (h : AutInv X i acc) : acc.wt ≤ AL n := by
  obtain ⟨L, rfl, hl, -, -⟩ := h
  have := wt_lit (L.map encPerm) (c := WB n) (by
    intro x hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
    exact perm_wt (by have := le_kB n; omega) g)
  simp only [List.length_map] at this
  refine this.trans ?_
  have e1 : L.length ≤ n ^ 2 * (n ^ 2 + 2) + 2 := by
    have := Nat.mul_le_mul_right (n ^ 2 + 2) hi
    rw [← sq] at this
    omega
  have := Nat.mul_le_mul_right (2 * WB n + 1) e1
  simp only [AL]
  omega

/-- The cost of the append. -/
def appC (n : ℕ) : ℕ := loopModK * (n ^ 2 + 3) * (10 * AL n + n ^ 2 + 10)

/-- The budget of a step. -/
noncomputable def autT (h : Membership) (S n : ℕ) : ℕ :=
  riC h S n + 2 * levC n + invK * (n + 1) ^ 4 + swC n + appC n + 100 * AL n

/-- The bound of a step. -/
noncomputable def autC (h : Membership) (S n : ℕ) : ℕ := 100000000 * autT h S n

theorem pair_eq {i : ℕ} {v w : ℕ} (hw : w < n) (h : v * n + w = i) : v = i / n ∧ w = i % n := by
  subst h
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hw, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]

theorem one_rooted (X : SimpleGraph (Fin n)) (v : Fin n) : IsRooted X v X v 1 :=
  isRooted_of_aut (one_mem _) v

theorem sq_le_kB (n : ℕ) : n * n ≤ kB n := by
  have h1 : n * n ≤ n * (n + 6) := Nat.mul_le_mul_left _ (by omega)
  exact h1.trans (Nat.le_self_pow (by omega) _)

/-- The invariant moves to the next pair. -/
theorem autInv_next {X : SimpleGraph (Fin n)} {i : ℕ} {L L' : List (Perm (Fin n))}
    (hI : ∀ v w : Fin n, (v : ℕ) * n + w < i → AutCond X v w L) (hL : ∀ s ∈ L, s ∈ L')
    (hnew : ∀ v w : Fin n, (v : ℕ) * n + w = i → AutCond X v w L') :
    ∀ v w : Fin n, (v : ℕ) * n + w < i + 1 → AutCond X v w L' := fun v w hvw => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hvw with h | h
  · exact (hI v w h).mono hL
  · exact hnew v w h

set_option maxHeartbeats 4000000 in
/-- **A step of the loop over pairs.** -/
theorem autStep_spec {P : Program} {a fd j S : ℕ} (h : Membership)
    (hP : P.HasAt a (autStepFuns a fd j)) (hj : P.prims[j]? = some (membershipPrim h))
    (hSol : SolverAt P fd D (n * D * (n * D)) S) (hS : Sz n D) (X : SimpleGraph (Fin n))
    (dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D)
    (dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U X) u).length ≤ D)
    {i : ℕ} (hi : i < n * n) {acc : Val} (hI : AutInv X i acc) :
    FunAll P a (.list [riCtx D X X, .nat i, acc]) fun out cost =>
      AutInv X (i + 1) out ∧ cost ≤ autC h S n := by
  classical
  have hM : P.funs[a]? = some (autStepE (a + 20) (a + 21) (a + 5) (a + 1) (a + 17)) :=
    hP.left.left.left.left.single
  have hSw : P.HasAt (a + 1) (tabFuns (a + 1) swapE) := hP.left.left.left.right
  have hIv : P.HasAt (a + 5) (invFuns (a + 5)) := hP.left.left.right
  have hAp : P.HasAt (a + 17) (appendFuns (a + 17)) := hP.left.right
  have hRi : P.HasAt (a + 20) (riFuns (a + 20) fd j) := hP.right
  have hLv : P.HasAt (a + 21) (levFuns (a + 21)) := hRi.left.left.left.right
  have hn : 0 < n := hS.pos
  have h0 := WB_ge n
  have hV := WB_le_VB n
  have hk := hS.k_le
  have hlk := le_kB n
  have hlB := levB_le_WB n
  have hvlt : i / n < n := Nat.div_lt_of_lt_mul hi
  have hwlt : i % n < n := Nat.mod_lt _ hn
  set v : Fin n := ⟨i / n, hvlt⟩ with hv
  set w : Fin n := ⟨i % n, hwlt⟩ with hw
  have hvw : (v : ℕ) * n + w = i := by simp only [hv, hw]; exact Nat.div_add_mod' i n
  obtain ⟨L, rfl, hlL, hLa, hLc⟩ := hI
  have wc := riCtx_wt hS X X
  have wacc := autInv_wt hi.le ⟨L, rfl, hlL, hLa, hLc⟩
  have hnn := sq_le_kB n
  have wi : (Val.nat i).wt ≤ WB n := nat_wt (by omega)
  set A := Val.list [riCtx D X X, .nat i, .list (L.map encPerm)] with hA
  have wA : A.wt ≤ 3 * (2 * (9 * (2 * WB n + 1) + 4 + AL n + WB n) + 1) + 4 := wt_lit _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl) <;> omega)
  have hAL : 4 * WB n + 6 ≤ AL n := by
    have := Nat.mul_le_mul_right (2 * WB n + 1) (show 2 ≤ n ^ 2 * (n ^ 2 + 2) + 2 by omega)
    simp only [AL]
    omega
  set T := autT h S n with hT
  have hTA : 2 * A.wt + 100 ≤ T := by simp only [hT, autT]; omega
  have hTAL : 100 * AL n ≤ T := by simp only [hT, autT]; omega
  have hTr : riC h S n + 2 * levC n + invK * (n + 1) ^ 4 + swC n + appC n ≤ T := by
    simp only [hT, autT]; omega
  have ga : ∀ rest {k : ℕ} {x : Val}, [riCtx D X X, .nat i, .list (L.map encPerm)][k]? = some x →
      k ≤ 2 → Lv P (A :: rest) T (arg k) x 1 := fun rest k x hx hk =>
    Lv.arg hx (by change 2 * A.wt + k + 5 ≤ T; omega)
  have n9 : ∀ env : List Val, ∀ k, k ≤ 8 → Lv P env T (.nat k) (.nat k) 1 := fun env k hk =>
    Lv.nat k (by omega)
  have gc : ∀ rest (k : ℕ) {x : Val}, [adjVal X, adjVal X, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))][k]? = some x → k ≤ 8 →
      Lv P (A :: rest) T (.get (arg 0) (.nat k)) x _ := fun rest k x hx hk =>
    Lv.get (vs := [adjVal X, adjVal X, .nat n, ids n, .nat D, .nat (n * D),
      .nat (n * D * (n * D)), ids (n * D), ids (n * D * (n * D))]) (ga rest (k := 0) rfl (by omega))
      (n9 _ k hk) hx
  have cv : ∀ rest, Lv P (A :: rest) T (.arith .div (arg 1) (.get (arg 0) (.nat 2))) (.nat v) _ :=
    fun rest => Lv.arith (ga rest (k := 1) rfl (by omega)) (gc rest 2 rfl (by omega)) rfl
      (by simp only [hv]; omega)
  have cw : ∀ rest, Lv P (A :: rest) T (.arith .mod (arg 1) (.get (arg 0) (.nat 2))) (.nat w) _ :=
    fun rest => Lv.arith (ga rest (k := 1) rfl (by omega)) (gc rest 2 rfl (by omega)) rfl
      (by simp only [hw]; omega)
  have cA := Lv.mono (Lv.mk3 (ga [] (k := 0) rfl (by omega)) (cv []) (cw []) (by omega))
    (show _ ≤ 1000 by norm_num)
  have hri := ri_spec h hRi hj hSol hS X X dX dY v w
  refine FunAll.intro hM (EvalAll.letE (Ra := fun out c => RIOut X v X w out ∧
      c ≤ 1000 * T + riC h S n + riC h S n + 1 ∧ out.wt < riC h S n)
    (EvalAll.call_funAll cA fun va ca hva => ?_) fun out cout hout => ?_)
  · obtain ⟨rfl, hca⟩ := hva
    refine FunAll.mono hri.wt_lt fun x c hx => ⟨hx.1.1, ?_, ?_⟩
    · have := hx.1.2
      have := hx.2
      omega
    · have := hx.1.2
      have := hx.2
      omega
  obtain ⟨hRO, hcout, hwout⟩ := hout
  have v1 : ∀ tl, Lv P (A :: out :: tl) T (.var 1) out 1 := fun tl => Lv.var rfl (by omega)
  rcases hRO with ⟨rfl, hno⟩ | ⟨τ, gs, rfl, hτ, hgs, hgl⟩
  · -- no rooted isomorphism
    have c0 := Lv.length (vs := []) (v1 []) (by omega)
    refine Det.post (Lv.mono (Lv.ite_zero c0 (ga [.list []] (k := 2) rfl (by omega)))
      (show _ ≤ 100 by norm_num)) fun c' hc' => ⟨⟨L, rfl, ?_, hLa, autInv_next hLc (fun s hs => hs) ?_⟩, ?_⟩
    · have : (i + 1) * (n ^ 2 + 2) = i * (n ^ 2 + 2) + (n ^ 2 + 2) := by ring
      omega
    · intro v' w' hvw'
      obtain ⟨e1, e2⟩ := pair_eq w'.isLt hvw'
      have ev : v' = v := Fin.ext e1
      have ew : w' = w := Fin.ext e2
      subst ev ew
      refine ⟨fun ⟨g, hg, hgv⟩ => absurd (hgv ▸ isRooted_of_aut hg v) (hno g), fun hvv => ?_⟩
      exact absurd (by rw [← hvv]; exact one_rooted X v) (hno 1)
    · simp only [autC]
      omega
  · -- a rooted isomorphism `τ`
    have eG : encGroup gs = .list [.nat n, .list ((1 :: gs).map encPerm)] := rfl
    set swp := swPerm hτ with hswp
    have c0 := Lv.length (vs := [encPerm τ, encGroup gs]) (v1 []) (by omega)
    have hlv := lev_spec hLv X v
    have hlw := lev_spec hLv X w
    have wlv : (encFun (lev X v)).wt ≤ WB n := table_wt (by omega) (lev_le X v)
    have wlw : (encFun (lev X w)).wt ≤ WB n := table_wt (by omega) (lev_le X w)
    have wt1 : (encPerm τ⁻¹).wt ≤ WB n := perm_wt (by omega) _
    have wsw : (encPerm swp).wt ≤ WB n := perm_wt (by omega) _
    set O := Val.list [encPerm τ, encGroup gs] with hO
    have cLv := Lv.call (Lv.mk4 (gc [O] 0 rfl (by omega)) (gc [O] 2 rfl (by omega))
      (gc [O] 3 rfl (by omega)) (cv [O]) (by omega)) hlv (by omega)
    have cLw := Lv.call (Lv.mk4 (gc [O, encFun (lev X v)] 0 rfl (by omega))
      (gc [O, encFun (lev X v)] 2 rfl (by omega))
      (gc [O, encFun (lev X v)] 3 rfl (by omega)) (cw [O, encFun (lev X v)]) (by omega)) hlw
      (by omega)
    have gτ := fun tl => Lv.get (vs := [encPerm τ, encGroup gs]) (v1 tl) (n9 _ 0 (by omega)) rfl
    have cInv := Lv.call (gτ [encFun (lev X v), encFun (lev X w)]) (inv_spec hIv τ) (by omega)
    set E4 := [A, O, encFun (lev X v), encFun (lev X w),
      encPerm τ⁻¹] with hE4
    have vv : ∀ {k : ℕ} {x : Val}, E4[k]? = some x → x.wt ≤ WB n → Lv P E4 T (.var k) x 1 :=
      fun hx hw' => Lv.var hx (by omega)
    have cSw := Lv.call (Lv.mk2 (Lv.mk5 (gτ [encFun (lev X v), encFun (lev X w), encPerm τ⁻¹])
      (vv (k := 2) rfl wlv) (vv (k := 3) rfl wlw) (vv (k := 4) rfl wt1)
      (gc [O, encFun (lev X v), encFun (lev X w), encPerm τ⁻¹] 2 rfl (by omega)) (by omega))
      (gc [O, encFun (lev X v), encFun (lev X w), encPerm τ⁻¹] 3 rfl (by omega)) (by omega))
      (sw_spec hSw hτ) (by omega)
    set xs := L.map encPerm with hxs
    set ys := (1 :: gs).map encPerm ++ [encPerm swp] with hys
    have hlen1 : L.length ≤ n ^ 2 * (n ^ 2 + 2) := by
      have : i * (n ^ 2 + 2) ≤ n * n * (n ^ 2 + 2) := Nat.mul_le_mul_right _ hi.le
      rw [← sq] at this
      omega
    have hys1 : ys.length ≤ n ^ 2 + 2 := by
      simp only [hys, List.length_append, List.length_map, List.length_cons,
        List.length_singleton, List.length_nil]
      omega
    have wxs : (Val.list xs).wt ≤ AL n := permList_AL (by omega)
    have hysL : ys = ((1 :: gs) ++ [swp]).map encPerm := by simp [hys]
    have wys : (Val.list ys).wt ≤ AL n := by
      rw [hysL]
      refine permList_AL ?_
      have : n ^ 2 + 2 ≤ n ^ 2 * (n ^ 2 + 2) + 2 := by
        have : n ^ 2 ≤ n ^ 2 * (n ^ 2 + 2) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil]
      omega
    have hres : xs ++ ys = (L ++ ((1 :: gs) ++ [swp])).map encPerm := by
      rw [List.map_append, ← hysL]
    have wres : (Val.list (xs ++ ys)).wt ≤ AL n := by
      rw [hres]
      refine permList_AL ?_
      have : (i + 1) * (n ^ 2 + 2) ≤ n * n * (n ^ 2 + 2) := Nat.mul_le_mul_right _ hi
      rw [← sq] at this
      have e : (i + 1) * (n ^ 2 + 2) = i * (n ^ 2 + 2) + (n ^ 2 + 2) := by ring
      simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil]
      omega
    have w2 : (Val.list [.list xs, .list ys]).wt ≤ 2 * (2 * (AL n + AL n) + 1) + 4 :=
      wt_lit _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro x (rfl | rfl) <;> omega)
    have hApD : FunDet P (a + 17) (.list [.list xs, .list ys]) (.list (xs ++ ys)) (appC n) := by
      refine FunAll.mono (append_spec hAp xs ys) fun x c hx => ⟨hx.1, ?_⟩
      have h1 := hx.2
      rw [hx.1] at h1
      have e2 : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
          (Val.list (xs ++ ys)).wt + 1) ≤ loopModK * (n ^ 2 + 3) * (10 * AL n + n ^ 2 + 10) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      simp only [appC]
      omega
    set E5 := [A, O, encFun (lev X v), encFun (lev X w), encPerm τ⁻¹, encPerm swp] with hE5
    have gG := Lv.get (vs := [.nat n, .list ((1 :: gs).map encPerm)])
      (Lv.get (vs := [encPerm τ, encGroup gs]) (v1 [encFun (lev X v), encFun (lev X w),
        encPerm τ⁻¹, encPerm swp]) (n9 _ 1 (by omega)) rfl) (n9 _ 1 (by omega)) rfl
    have v5 : Lv P E5 T (.var 5) (encPerm swp) 1 := Lv.var rfl (by omega)
    have cAp := Lv.call (Lv.mk2 (ga [O, encFun (lev X v), encFun (lev X w), encPerm τ⁻¹,
      encPerm swp] (k := 2) rfl (by omega)) (Lv.snoc gG v5 (by omega)) (by omega)) hApD (by omega)
    have l4 := Lv.letE cSw cAp
    have l3 := Lv.letE cInv l4
    have l2 := Lv.letE cLw l3
    have l1 := Lv.letE cLv l2
    refine Det.post (Lv.mono (Lv.ite_pos (e := arg 2) c0 (by simp) l1)
      (show _ ≤ 10000000 by norm_num)) fun c' hc' => ⟨⟨L ++ ((1 :: gs) ++ [swp]), congrArg Val.list hres, ?_, ?_,
        autInv_next hLc (fun s hs => List.mem_append_left _ hs) ?_⟩, ?_⟩
    · have e : (i + 1) * (n ^ 2 + 2) = i * (n ^ 2 + 2) + (n ^ 2 + 2) := by ring
      simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil]
      omega
    · intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact hLa s hs
      · rcases List.mem_append.1 hs with hs | hs
        · rcases List.mem_cons.1 hs with rfl | hs
          · exact one_mem _
          · have : s ∈ ballGroup (lev X v) (n - 1) X := hgs ▸ Subgroup.subset_closure hs
            exact (ballGroup_top_mem_aut this).1
        · rw [List.mem_singleton.1 hs]
          exact swPerm_mem hτ
    · intro v' w' hvw'
      obtain ⟨e1, e2⟩ := pair_eq w'.isLt hvw'
      have ev : v' = v := Fin.ext e1
      have ew : w' = w := Fin.ext e2
      subst ev ew
      refine ⟨fun _ => ⟨swp, by simp, swPerm_root hτ, fun u h1 h2 => swPerm_fix hτ h1 h2⟩,
        fun _ => ?_⟩
      rw [← hgs]
      exact Subgroup.closure_mono fun s hs => List.mem_append_right _
        (List.mem_append_left _ (List.mem_cons_of_mem _ hs))
    · simp only [autC]
      omega

/-- The loop over pairs. -/
def autFuns (b fd j : ℕ) : List Expr :=
  iterFuns b (b + 3) ++ autStepFuns (b + 3) fd j

/-- The cost of the loop over pairs. -/
noncomputable def autLC (h : Membership) (S n : ℕ) : ℕ :=
  n * n * autC h S n + loopModK * (n * n + 1) * (200 * WB n + n * n + AL n + 1)

/-- **Generators of the automorphism group.** The loop over all pairs gives a list of at most
`n ^ 2 * (n ^ 2 + 2)` automorphisms that generate `autGroup X`. -/
theorem aut_spec {P : Program} {b fd j S : ℕ} (h : Membership)
    (hP : P.HasAt b (autFuns b fd j)) (hj : P.prims[j]? = some (membershipPrim h))
    (hSol : SolverAt P fd D (n * D * (n * D)) S) (hS : Sz n D) (X : SimpleGraph (Fin n))
    (dX : ∀ (ℓ : Fin n → ℕ) u, (fwd ℓ X u).length ≤ D)
    (dY : ∀ (ℓ : Fin n → ℕ) (U : Perm (Fin n)) u, (fwd ℓ (pull U X) u).length ≤ D) :
    FunAll P b (.list [riCtx D X X, .nat (n * n), .list []]) fun out cost =>
      (∃ L : List (Perm (Fin n)), out = .list (L.map encPerm) ∧ L.length ≤ n ^ 2 * (n ^ 2 + 2) ∧
        Subgroup.closure {g | g ∈ L} = autGroup X) ∧ cost ≤ autLC h S n := by
  have hIt : P.HasAt b (iterFuns b (b + 3)) := hP.left
  have hSt : P.HasAt (b + 3) (autStepFuns (b + 3) fd j) := hP.right
  have h0 : AutInv X 0 (.list []) := ⟨[], rfl, by simp, by simp, fun v w h => by omega⟩
  have hit := iter_spec (c := riCtx D X X) (k := n * n) (acc0 := .list []) hIt (Inv := AutInv X)
    (M := AL n) (B := fun _ => autC h S n) h0 (fun i acc hi hI => autInv_wt hi hI)
    (fun i acc hi hI => autStep_spec h hSt hj hSol hS X dX dY hi hI)
  refine FunAll.mono hit fun out c hw => ⟨?_, ?_⟩
  · obtain ⟨L, rfl, hl, hLa, hc⟩ := hw.1
    refine ⟨L, rfl, by simpa [sq] using hl, autGens_eq hLa fun v w => hc v w ?_⟩
    have h1 : (v : ℕ) * n + w < (v + 1) * n := by
      have := w.isLt
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have h2 : ((v : ℕ) + 1) * n ≤ n * n := Nat.mul_le_mul_right _ v.isLt
    omega
  · have hc := hw.2
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have h0 := WB_ge n
    have wc := riCtx_wt hS X X
    have wk : (Val.nat (n * n)).wt ≤ WB n := nat_wt (by have := sq_le_kB n; omega)
    have wn : (Val.nat 0).wt ≤ WB n := nat_wt (by omega)
    have wl : (Val.list []).wt ≤ WB n := by
      have := wt_lit (c := 0) [] (by simp)
      simp only [List.length_nil] at this
      omega
    have w3 : (Val.list [riCtx D X X, .nat (n * n), .list []]).wt ≤
        3 * (2 * (9 * (2 * WB n + 1) + 4 + WB n) + 1) + 4 := wt_lit _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl) <;> omega)
    have e2 : loopModK * (n * n + 1) * ((Val.list [riCtx D X X, .nat (n * n), .list []]).wt +
        n * n + AL n + 1) ≤ loopModK * (n * n + 1) * (200 * WB n + n * n + AL n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [autLC]
    omega

end GI.Degree
