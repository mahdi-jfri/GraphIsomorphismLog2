import Workspace.Impl.VsBOrb

/-!
# A chain of small orbits

The field-line base cuts a group down by a chain of stabilizers. Stage `i` of the chain has a
parameter `q_i` and an action `α q_i` with small orbits; the group of stage `i + 1` is the
stabilizer of the base point `y₀` in the group of stage `i`. The program runs the small orbit
transporter once per stage and keeps every orbit list, so that later a target can be looked up
stage by stage.

* `vsBKs α y₀ G ps`: the elements of `G` that fix `y₀` under `α q` for every `q ∈ ps`.
* `VsBOrbL α G y₀ L`: `L` lists the orbit of `y₀` under `G`, each point with an element of `G`
  that moves `y₀` to it.
* `vsBChainFuns b sot` (3 functions), `vsBChain_spec`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ} {Y : Type}

/-- The elements of `G` that fix `y₀` at every stage of `ps`. -/
def vsBKs (α : ℕ → Perm (Fin n) → Y → Y) (y₀ : Y) (G : Set (Perm (Fin n))) (ps : List ℕ) :
    Set (Perm (Fin n)) :=
  {h | h ∈ G ∧ ∀ q ∈ ps, α q h y₀ = y₀}

/-- An orbit list of `y₀` under a set `G` of elements. -/
structure VsBOrbL (α : Perm (Fin n) → Y → Y) (G : Set (Perm (Fin n))) (y₀ : Y)
    (L : List (Y × Perm (Fin n))) : Prop where
  nodup : (L.map Prod.fst).Nodup
  mem : ∀ y, y ∈ L.map Prod.fst ↔ ∃ g ∈ G, α g y₀ = y
  pr : ∀ p ∈ L, p.2 ∈ G ∧ α p.2 y₀ = p.1

theorem vsBKs_nil (α : ℕ → Perm (Fin n) → Y → Y) (y₀ : Y) (G : Set (Perm (Fin n))) :
    vsBKs α y₀ G [] = G := by
  ext h; simp [vsBKs]

theorem vsBKs_snoc (α : ℕ → Perm (Fin n) → Y → Y) (y₀ : Y) (G : Set (Perm (Fin n))) (ps : List ℕ)
    (q : ℕ) : vsBKs α y₀ G (ps ++ [q]) = {h | h ∈ vsBKs α y₀ G ps ∧ α q h y₀ = y₀} := by
  ext h
  simp only [vsBKs, List.mem_append, List.mem_singleton, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hG, hq⟩
    exact ⟨⟨hG, fun q' hq' => hq q' (Or.inl hq')⟩, hq q (Or.inr rfl)⟩
  · rintro ⟨⟨hG, hq⟩, h1⟩
    refine ⟨hG, fun q' hq' => ?_⟩
    rcases hq' with hq' | rfl
    · exact hq q' hq'
    · exact h1

theorem VsBOrbL.of_vsQ {α : Perm (Fin n) → Y → Y} {gs : List (Perm (Fin n))} {y₀ : Y}
    {L : List (Y × Perm (Fin n))} (hL : VsQOrbL α gs y₀ L) {G : Set (Perm (Fin n))}
    (hG : (genGroup gs : Set (Perm (Fin n))) = G) : VsBOrbL α G y₀ L where
  nodup := hL.nodup
  mem y := by
    rw [hL.mem y, ← hG]; rfl
  pr p hp := by
    rw [← hG]; exact hL.pr p hp

/-- The step of the chain, on `[a, i, acc]` with `a = [ctx, gs₀, ps, key y₀, B, n]` and
`acc = [gs, orbit lists]`. -/
def vsBChainStep (sot : ℕ) : Expr :=
  .letE (.call sot (vsBmk5 (mk2 (.get (arg 0) (.nat 0)) (.get (.get (arg 0) (.nat 2)) (arg 1)))
      (.get (arg 2) (.nat 0)) (.get (arg 0) (.nat 3)) (.get (arg 0) (.nat 4)) (.get (arg 0) (.nat 5))))
    (mk2 (.get (.get (.var 1) (.nat 1)) (.nat 1)) (.snoc (.get (arg 2) (.nat 1)) (.get (.var 1) (.nat 0))))

/-- The chain program at base `b` (3 functions); `sot` is the entry of the transporter. -/
def vsBChainFuns (b sot : ℕ) : List Expr :=
  loopFuns b (.length (.get (.var 0) (.nat 2))) (mk2 (.get (.var 0) (.nat 1)) .nil) (vsBChainStep sot)

/-- The argument of the chain program. -/
def vsBChainIn (ctx : Val) (gs₀ : List (Perm (Fin n))) (ps : List ℕ) (keyY : Y → List ℕ) (y₀ : Y)
    (B : ℕ) : Val :=
  .list [ctx, .list (gs₀.map encPerm), .list (ps.map .nat), natList (0 :: keyY y₀), .nat B, .nat n]

/-- The weight facts of an orbit list that the lookups need. -/
def VsBPW (S : ℕ) (keyY : Y → List ℕ) (L : List (Y × Perm (Fin n))) : Prop :=
  L.length + 1 ≤ S ∧ (vsQPairs keyY L).wt ≤ 40 * S ^ 3 ∧
    ∀ p ∈ L, (Val.list [natList (0 :: keyY p.1), encPerm p.2]).wt ≤ 16 * S ^ 2 ∧
      (natList (0 :: keyY p.1)).wt ≤ S

theorem VsQSotHyp.pw {P : Program} {fa : ℕ} {K : Subgroup (Perm (Fin n))} {α : Perm (Fin n) → Y → Y}
    {gs : List (Perm (Fin n))} {keyY : Y → List ℕ} {y₀ : Y} {ac : Val} {S A B : ℕ}
    (H : VsQSotHyp P fa K α gs keyY y₀ ac S A B) {L : List (Y × Perm (Fin n))}
    (hL : VsQOrbL α gs y₀ L) : VsBPW S keyY L :=
  ⟨(H.wt_pairs hL).1, (H.wt_pairs hL).2.2, fun p hp =>
    ⟨(H.wt_pairs hL).2.1 p hp, H.hkey p.1 ((hL.mem _).1 (List.mem_map_of_mem hp))⟩⟩

theorem vsB_genGroup_one (ks : List (Perm (Fin n))) : genGroup (1 :: ks) = gens ks := by
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.mpr fun g hg => ?_
    rcases List.mem_cons.mp hg with rfl | hg
    · exact one_mem _
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg

theorem vsB_wt_grp {S Gl : ℕ} {ks : List (Perm (Fin n))} (hks : ks.length ≤ n ^ 2)
    (hgl2 : n ^ 2 + 1 ≤ Gl) (hGS : Gl + 1 ≤ S) (hn : n + 1 ≤ S) :
    (Val.list ((1 :: ks).map encPerm)).wt ≤ 13 * S ^ 4 ∧ (encGroup ks).wt ≤ 40 * S ^ 4 := by
  have h1 := wt_list_encPerms_le (1 :: ks)
  have h2 : (((1 :: ks).length + 1) * (n + 1)) ^ 2 ≤ (S * S) ^ 2 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul (by simp; omega) hn) 2
  have e2 : (S * S) ^ 2 = S ^ 4 := by ring
  have h3 := wt_list2_le (.nat n) (.list ((1 :: ks).map encPerm))
  have h4 := wt_nat_le n
  have h5 : n + 1 ≤ S ^ 4 := le_trans hn (Nat.le_self_pow (by norm_num) _)
  have e : encGroup ks = .list [.nat n, .list ((1 :: ks).map encPerm)] := rfl
  rw [e]
  omega

theorem vsB_wt_acc {S : ℕ} (hS : 1 ≤ S) {gs : List (Perm (Fin n))} {Ls : List Val}
    (hn : n + 1 ≤ S) (hg : gs.length + 1 ≤ S) (hl : Ls.length ≤ S) (hL : ∀ v ∈ Ls, v.wt ≤ 40 * S ^ 3) :
    (Val.list [.list (gs.map encPerm), .list Ls]).wt ≤ 1000 * S ^ 4 := by
  have h1 := wt_list_encPerms_le gs
  have h2 : ((gs.length + 1) * (n + 1)) ^ 2 ≤ (S * S) ^ 2 := Nat.pow_le_pow_left (Nat.mul_le_mul hg hn) 2
  have e2 : (S * S) ^ 2 = S ^ 4 := by ring
  have h3 := GI.Lang.wt_list_le_of Ls hL
  have h4 : Ls.length * (2 * (40 * S ^ 3) + 1) ≤ S * (81 * S ^ 3) :=
    Nat.mul_le_mul hl (by have : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS; omega)
  have e4 : S * (81 * S ^ 3) = 81 * S ^ 4 := by ring
  have h5 := wt_list2_le (.list (gs.map encPerm)) (.list Ls)
  have : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ hS
  omega

set_option maxHeartbeats 4000000 in
/-- **The chain.** It runs the transporter once per stage. The result lists the generators of
the last group (the elements of `⟨gs₀⟩` that fix `y₀` at every stage) and the orbit list of
every stage. -/
theorem vsBChain_spec [Countable Y] (hps : PointwiseStab) (hm : Membership) {P : Program}
    {b sot0 fa jp jm : ℕ} (h : P.HasAt b (vsBChainFuns b (sot0 + 22)))
    (hsot : P.HasAt sot0 (vsQSotFuns sot0 fa jp jm)) (hjp : P.prims[jp]? = some (pointwiseStabPrim hps))
    (hjm : P.prims[jm]? = some (membershipPrim hm)) {K₀ : Subgroup (Perm (Fin n))}
    {α : ℕ → Perm (Fin n) → Y → Y} {keyY : Y → List ℕ} {y₀ : Y} {ctx : Val} {ps : List ℕ}
    {gs₀ : List (Perm (Fin n))} {S A B Gl : ℕ}
    (hα : ∀ q ∈ ps, VsQPAct K₀ (α q)) (hgs₀ : genGroup gs₀ ≤ K₀) (hgl : gs₀.length ≤ Gl)
    (hgl2 : n ^ 2 + 1 ≤ Gl) (hnS : n + 1 ≤ S) (hGS : Gl + 1 ≤ S) (hpsS : ps.length ≤ S)
    (H : ∀ q ∈ ps, ∀ gs : List (Perm (Fin n)), genGroup gs ≤ K₀ → gs.length ≤ Gl →
      VsQSotHyp P fa K₀ (α q) gs keyY y₀ (.list [ctx, .nat q]) S A B) :
    FunAll P b (vsBChainIn ctx gs₀ ps keyY y₀ B) (fun w c => ∃ (gsF : List (Perm (Fin n)))
      (Ls : List (List (Y × Perm (Fin n)))),
      w = .list [.list (gsF.map encPerm), .list (Ls.map (vsQPairs keyY))] ∧ Ls.length = ps.length ∧
      (genGroup gsF : Set (Perm (Fin n))) = vsBKs α y₀ (genGroup gs₀) ps ∧ gsF.length ≤ Gl ∧
      (∀ i (hi : i < Ls.length), VsBOrbL (α (ps.getD i 0))
        (vsBKs α y₀ (genGroup gs₀) (ps.take i)) y₀ Ls[i]) ∧ (∀ L ∈ Ls, VsBPW S keyY L) ∧
      c ≤ ps.length * (vsQSotCost hps hm n S A +
          10 ^ 4 * ((vsBChainIn ctx gs₀ ps keyY y₀ B).wt + 1000 * S ^ 4)) +
        loopModK * (ps.length + 1) * ((vsBChainIn ctx gs₀ ps keyY y₀ B).wt + ps.length +
          1000 * S ^ 4 + 1)) := by
  set a := vsBChainIn ctx gs₀ ps keyY y₀ B with ha
  have hS : 1 ≤ S := by omega
  set M := 1000 * S ^ 4
  set Inv : ℕ → Val → Prop := fun i acc => ∃ (gs : List (Perm (Fin n)))
      (Ls : List (List (Y × Perm (Fin n)))),
      acc = .list [.list (gs.map encPerm), .list (Ls.map (vsQPairs keyY))] ∧ Ls.length = i ∧
      (genGroup gs : Set (Perm (Fin n))) = vsBKs α y₀ (genGroup gs₀) (ps.take i) ∧ gs.length ≤ Gl ∧
      (∀ j (hj : j < Ls.length), VsBOrbL (α (ps.getD j 0))
        (vsBKs α y₀ (genGroup gs₀) (ps.take j)) y₀ Ls[j]) ∧
      ∀ L ∈ Ls, VsBPW S keyY L with hInv
  have hk := Det.length (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 2)
      (show [ctx, .list (gs₀.map encPerm), .list (ps.map Val.nat), natList (0 :: keyY y₀), .nat B,
        .nat n][2]? = some (.list (ps.map Val.nat)) from rfl))
  rw [List.length_map] at hk
  have hacc := Det.mk2 (Det.get' (Det.var' (P := P) (env := [a]) (i := 0) rfl) (Det.nat 1)
      (show [ctx, .list (gs₀.map encPerm), .list (ps.map Val.nat), natList (0 :: keyY y₀), .nat B,
        .nat n][1]? = some (.list (gs₀.map encPerm)) from rfl)) (Det.nil (P := P) (env := [a]))
  have wa : (Val.list (gs₀.map encPerm)).wt < a.wt := wt_le_wt_list (by simp)
  have wps : (Val.list (ps.map Val.nat)).wt < a.wt := wt_le_wt_list (by simp)
  have hpl : (ps.map Val.nat).length < (Val.list (ps.map Val.nat)).wt := length_lt_wt_list _
  rw [List.length_map] at hpl
  have hM : ∀ i acc, i ≤ ps.length → Inv i acc → acc.wt ≤ M := by
    rintro i acc hi ⟨gs, Ls, rfl, hLl, -, hgl', -, hLw⟩
    exact vsB_wt_acc hS hnS (by omega) (by simp; omega) (by
      intro v hv
      obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hv
      exact (hLw L hL).2.1)
  have h0 : Inv 0 (.list [.list (gs₀.map encPerm), .list []]) :=
    ⟨gs₀, [], rfl, rfl, by simp [vsBKs_nil], hgl, by simp, by simp⟩
  refine (loopBdd_spec h hk hacc ?_ h0 hM (D := fun _ => vsQSotCost hps hm n S A +
      10 ^ 4 * (a.wt + 1000 * S ^ 4)) ?_).mono ?_
  · have := wt_list2_le (.list (gs₀.map encPerm)) (.list [])
    have w2 := wt_nat_le 2
    have w1 := wt_nat_le 1
    have := wt_le_wt_list (show Val.list (gs₀.map encPerm) ∈ [Val.list (gs₀.map encPerm), .list []] by simp)
    simp only [wt_list_nil] at *
    have ea : (Val.list [ctx, .list (gs₀.map encPerm), .list (ps.map Val.nat), natList (0 :: keyY y₀),
      .nat B, .nat n]).wt = a.wt := rfl
    have := sum_wt_lt_wt_list [ctx, .list (gs₀.map encPerm), .list (ps.map Val.nat), natList (0 :: keyY y₀),
      .nat B, .nat n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this
    have := wt_nat B; have := wt_nat n
    omega
  · rintro i acc hi ⟨gs, Ls, rfl, hLl, hG, hgl', hLs, hLw⟩
    have hiq : i < ps.length := hi
    set q := ps[i]
    have hq : q ∈ ps := List.getElem_mem hi
    have hK : genGroup gs ≤ K₀ := by
      intro g hg
      have : g ∈ (genGroup gs : Set (Perm (Fin n))) := hg
      rw [hG] at this
      exact hgs₀ this.1
    have HH := H q hq gs hK hgl'
    have hα' := hα q hq
    set acc := Val.list [.list (gs.map encPerm), .list (Ls.map (vsQPairs keyY))]
    set sa := Val.list [a, .nat i, acc]
    have g0 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, acc]) (j := 0) rfl
    have g1 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, acc]) (j := 1) rfl
    have g2 := Det.arg' (P := P) (rest := []) (vs := [a, .nat i, acc]) (j := 2) rfl
    have la : ∀ k v, [ctx, .list (gs₀.map encPerm), .list (ps.map Val.nat), natList (0 :: keyY y₀),
        .nat B, .nat n][k]? = some v → Det P [sa] (.get (arg 0) (.nat k)) v _ :=
      fun k v hv => Det.get' g0 (Det.nat k) hv
    have dctx := la 0 ctx rfl
    have dq := Det.get' (la 2 _ rfl) g1 (show (ps.map Val.nat)[i]? = some (.nat q) by
      simp [q, hi])
    have dgs := Det.get' g2 (Det.nat 0)
      (show [Val.list (gs.map encPerm), .list (Ls.map (vsQPairs keyY))][0]? =
        some (.list (gs.map encPerm)) from rfl)
    have dargs := Det.vsBmk5 (Det.mk2 dctx dq) dgs (la 3 _ rfl) (la 4 _ rfl) (la 5 _ rfl)
    have hS' := vsQSot_spec hps hm hsot hjp hjm hα' HH
    have wacc : acc.wt ≤ M := hM i acc hi.le ⟨gs, Ls, rfl, hLl, hG, hgl', hLs, hLw⟩
    have wsa := wt_stepArg_le a i acc
    have wIn := (wt_vsQSotIn_le hα' HH).1
    have eIn : (Val.list [Val.list [ctx, .nat q], .list (gs.map encPerm), natList (0 :: keyY y₀),
      .nat B, .nat n]).wt = (vsQSotIn (.list [ctx, .nat q]) gs keyY y₀ B).wt := rfl
    have wctx : ctx.wt < a.wt := wt_le_wt_list (by simp [a, vsBChainIn])
    have wkey : (natList (0 :: keyY y₀)).wt < a.wt := wt_le_wt_list (by simp [a, vsBChainIn])
    have wBn : (Val.nat B).wt < a.wt := wt_le_wt_list (by simp [a, vsBChainIn])
    have wnn : (Val.nat n).wt < a.wt := wt_le_wt_list (by simp [a, vsBChainIn])
    have wgsv : (Val.list (gs.map encPerm)).wt < acc.wt := wt_le_wt_list (by simp [acc])
    have wLsv : (Val.list (Ls.map (vsQPairs keyY))).wt < acc.wt := wt_le_wt_list (by simp [acc])
    have wqn : (Val.nat q).wt < (Val.list (ps.map Val.nat)).wt :=
      wt_le_wt_list (List.mem_map_of_mem hq)
    have ea : (Val.list [ctx, .list (gs₀.map encPerm), .list (ps.map Val.nat), natList (0 :: keyY y₀),
      .nat B, .nat n]).wt = a.wt := rfl
    have es : (Val.list [a, .nat i, acc]).wt = sa.wt := rfl
    have wcq := wt_list2_le ctx (.nat q)
    have hM4 : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ hS
    have w0 := wt_nat_le 0; have w1 := wt_nat_le 1; have w2 := wt_nat_le 2; have w3 := wt_nat_le 3
    have w4 := wt_nat_le 4; have w5 := wt_nat_le 5; have wi := wt_nat_le i
    refine EvalAll.letE (Ra := fun r cr => ∃ (L : List (Y × Perm (Fin n))) (ks : List (Perm (Fin n))),
        r = .list [vsQPairs keyY L, encGroup ks] ∧ VsQOrbL (α q) gs y₀ L ∧
        gens ks = vsQStabG hα' hK y₀ ∧ ks.length ≤ n ^ 2 ∧
        cr ≤ vsQSotCost hps hm n S A + 1000 * (a.wt + M))
      (EvalAll.call_funAll dargs fun v ca hv => ?_) fun r cr hr => ?_
    · obtain ⟨rfl, hca⟩ := hv
      refine hS'.mono fun w c hw => ?_
      obtain ⟨L, ks, rfl, hL, hks, hksl, hc⟩ := hw
      refine ⟨L, ks, rfl, hL, hks, hksl, ?_⟩
      have wP := (HH.wt_pairs hL).2.2
      have wK := (vsB_wt_grp hksl hgl2 hGS hnS).2
      have wo := wt_list2_le (vsQPairs keyY L) (encGroup ks)
      have h34 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
      omega
    · obtain ⟨L, ks, rfl, hL, hks, hksl, hcr⟩ := hr
      set r := Val.list [vsQPairs keyY L, encGroup ks]
      have v1 := Det.var' (P := P) (env := [sa, r]) (i := 1) rfl
      have d1 := Det.get' (Det.get' v1 (Det.nat 1)
        (show [vsQPairs keyY L, encGroup ks][1]? = some (encGroup ks) from rfl)) (Det.nat 1)
        (show [Val.nat n, .list ((1 :: ks).map encPerm)][1]? = some (.list ((1 :: ks).map encPerm)) from rfl)
      have g2' := Det.arg' (P := P) (rest := [r]) (vs := [a, .nat i, acc]) (j := 2) rfl
      have d2 := Det.snoc (Det.get' g2' (Det.nat 1)
        (show [Val.list (gs.map encPerm), .list (Ls.map (vsQPairs keyY))][1]? =
          some (.list (Ls.map (vsQPairs keyY))) from rfl))
        (Det.get' v1 (Det.nat 0) (show [vsQPairs keyY L, encGroup ks][0]? = some (vsQPairs keyY L) from rfl))
      refine (Det.mk2 d1 d2).post fun c hc => ⟨⟨1 :: ks, Ls ++ [L], by simp, by simp [hLl], ?_,
        by simp; omega, ?_, ?_⟩, ?_⟩
      · rw [vsB_genGroup_one, hks, List.take_succ_eq_append_getElem hi, vsBKs_snoc, ← hG]
        rfl
      · intro j hj
        rw [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [List.getElem_append_left (by omega)]
          exact hLs j (by omega)
        · rw [List.getElem_append_right (by omega)]
          simp only [hLl, Nat.sub_self, List.getElem_cons_zero]
          have e : ps.getD i 0 = q := by simp [q, hi]
          rw [e]
          exact VsBOrbL.of_vsQ hL hG
      · intro L' hL'
        rcases List.mem_append.mp hL' with hL' | hL'
        · exact hLw L' hL'
        · rw [List.mem_singleton.mp hL']; exact HH.pw hL
      · have wP := (HH.wt_pairs hL).2.2
        have wK := vsB_wt_grp hksl hgl2 hGS hnS
        have wr := wt_list2_le (vsQPairs keyY L) (encGroup ks)
        have wnew := vsB_wt_acc hS hnS (gs := 1 :: ks) (Ls := Ls.map (vsQPairs keyY) ++ [vsQPairs keyY L])
          (by simp; omega) (by simp; omega) (by
            intro v hv
            rcases List.mem_append.mp hv with hv | hv
            · obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hv; exact (hLw L' hL').2.1
            · rw [List.mem_singleton.mp hv]; exact wP)
        have wgsn : (Val.list ((1 :: ks).map encPerm)).wt <
            (Val.list [.list ((1 :: ks).map encPerm), .list (Ls.map (vsQPairs keyY) ++ [vsQPairs keyY L])]).wt :=
          wt_le_wt_list (by simp)
        have wLsn : (Val.list (Ls.map (vsQPairs keyY) ++ [vsQPairs keyY L])).wt <
            (Val.list [.list ((1 :: ks).map encPerm), .list (Ls.map (vsQPairs keyY) ++ [vsQPairs keyY L])]).wt :=
          wt_le_wt_list (by simp)
        have wgK : (encGroup ks).wt < r.wt := wt_le_wt_list (by simp [r])
        have wPr : (vsQPairs keyY L).wt < r.wt := wt_le_wt_list (by simp [r])
        have wsr := wt_list2_le sa r
        have er : (Val.list [vsQPairs keyY L, encGroup ks]).wt = r.wt := rfl
        have esr : (Val.list [sa, r]).wt = (Val.list [sa, r]).wt := rfl
        have h34 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by norm_num)
        have eg : (encGroup ks).wt = (Val.list [Val.nat n, .list ((1 :: ks).map encPerm)]).wt := rfl
        simp only [List.map_cons] at *
        omega
  · rintro w c ⟨⟨gs, Ls, rfl, hLl, hG, hgl', hLs, hLw⟩, hc⟩
    refine ⟨gs, Ls, rfl, hLl, by rw [hG, List.take_length], hgl', hLs, hLw, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    exact hc

open Classical in
set_option maxHeartbeats 1000000 in
/-- **Lookup in an orbit list**, with the search functions inside the transporter block. -/
theorem vsB_find {P : Program} {sot0 fa jp jm : ℕ} (hsot : P.HasAt sot0 (vsQSotFuns sot0 fa jp jm))
    {keyY : Y → List ℕ} (hk : Function.Injective keyY) {S : ℕ} (hS1 : 1 ≤ S)
    {L : List (Y × Perm (Fin n))} (hL : VsBPW S keyY L) {t : Y} (ht : (natList (0 :: keyY t)).wt ≤ S) :
    FunDet P (sot0 + 8) (.list [natList (0 :: keyY t), vsQPairs keyY L])
      (.nat (L.findIdx fun q => decide (q.1 = t))) (200000 * S ^ 4) := by
  obtain ⟨hLS, wP, hpw⟩ := hL
  set key : Y → List ℕ := fun y => 0 :: keyY y with hkey
  have hk' : Function.Injective key := fun a b' e => hk (List.cons.inj e).2
  obtain ⟨hO, -⟩ := hsot.split (length_orbTFuns _ _)
  have hfd : P.HasAt (sot0 + 8) (findFuns (sot0 + 8) (sot0 + 8 + 3)) := hO.block 8 (by rfl)
  have htt : P.funs[sot0 + 8 + 3]? = some (orbTestF (sot0 + 16)) :=
    (hO.block 11 (gs := [_]) (by rfl)).single
  have heq : P.HasAt (sot0 + 16) (eqNatsFuns (sot0 + 16)) := hO.block 16 (by rfl)
  have hF := find_spec hfd (c := natList (key t)) (xs := L.map (GI.Lang.encPair key))
    (q := pairTest n key t) (B := fun _ => 100000 * S ^ 2) (by
      intro v hv
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
      have := orbTest_spec htt heq key hS1 t q ht (hpw q hq).2 (hpw q hq).1
      rw [pairTest_encPair hk']
      have e : decide (key t = key q.1) = decide (q.1 = t) :=
        Bool.decide_congr ⟨fun h => (hk' h).symm, fun h => h ▸ rfl⟩
      rw [e] at this
      exact this)
  refine hF.mono fun w cost hw => ⟨by rw [hw.1, findIdx_map_pairTest hk'], ?_⟩
  have hc := hw.2
  rw [List.map_const', List.sum_replicate, List.length_map, smul_eq_mul] at hc
  have w1 := wt_list2_le (natList (key t)) (.list (L.map (GI.Lang.encPair key)))
  have w2 : (natList (key t)).wt ≤ S := ht
  have e0 : (vsQPairs keyY L).wt = (Val.list (L.map (GI.Lang.encPair key))).wt := rfl
  have h1 : L.length * (100000 * S ^ 2) ≤ S * (100000 * S ^ 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : loopModK * (L.length + 1) * ((Val.list [natList (key t),
      .list (L.map (GI.Lang.encPair key))]).wt + 2 * L.length + 3) ≤ loopModK * S * (95 * S ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
      have : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
      omega)
  have e2 : S * (100000 * S ^ 2) = 100000 * S ^ 3 := by ring
  have e3 : loopModK * S * (95 * S ^ 3) = 95000 * S ^ 4 := by simp only [loopModK]; ring
  have : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by norm_num)
  omega

end GI.Impl
