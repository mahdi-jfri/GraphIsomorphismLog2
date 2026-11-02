import Workspace.Impl.FreshMath

/-!
# The hierarchy of a fresh phase, in `GI.Lang`

`hierF` on `[s, encGroup hs]` (a group `G'` on `s` points, with at most `s²` generators)
returns `[ones, fhierVal labels M]`: the indicator of all points, and the value of the stored
hierarchy `freshHier G' M`: no interval if `M = 1`, and otherwise `orbitHier G' M` with the orbit
labels of `G'`, where `M` is the size of a largest orbit.

1. `ones`: `replicate s 1`, the indicator of all points.
2. A largest orbit `D₁` (`lo_spec`, the largest-orbit module of the orbit chain).
3. `M = |D₁|`, the number of ones of its indicator (`count_indF`).
4. The orbit labels (`orbits_spec`), and the interval unless `M = 1`.

`hier_spec`: cost at most `hierK (s + 1)¹⁵`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

/-- The body of `hierF` on `[s, g]` (see the module docstring). -/
def hierBody (rep lo cnt ob : ℕ) : Expr :=
  .letE (.call rep (mk2 (arg 0) (.nat 1)))
  (.letE (.call lo (mk2 (arg 1) (.var 1)))
  (.letE (.call cnt (mk2 (.nat 1) (.get (.var 2) (.nat 0))))
  (mk2 (.var 1) (.ite (.arith .eq (.var 3) (.nat 1)) .nil
    (mk1 (mk4 (.call ob (arg 1)) (.var 3) (.var 3) (.nat 0)))))))

/-- The cost constant of `hierF`. -/
def hierK : ℕ := 10 ^ 14

theorem wt_replicate_one_le (s : ℕ) : (Val.list (List.replicate s (.nat 1))).wt ≤ 7 * (s + 1) := by
  have h := wt_list_le (List.replicate s (Val.nat 1))
  have h1 : ((List.replicate s (Val.nat 1)).map Val.wt).sum ≤ s * 3 := by
    rw [List.map_replicate, List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_left _ (wt_nat_le 1)
  simp only [List.length_replicate] at h
  omega

theorem replicate_eq_indVal {Ω' : Type} {s : ℕ} (e' : Ω' ≃ Fin s) :
    Val.list (List.replicate s (.nat 1)) = indVal e' Set.univ :=
  DomVal.eq_indVal (domVal_univ e')

/-- **The hierarchy of a fresh phase.** -/
theorem hier_spec {P : Program} {f rep lo cnt ob : ℕ} (hf : P.funs[f]? = some (hierBody rep lo cnt ob))
    (hrep : P.HasAt rep (replicateFuns rep)) (hlo : P.HasAt lo (loFuns lo))
    (hcnt : P.HasAt cnt (countFuns cnt)) (horb : P.HasAt ob (orbitFuns ob))
    {Ω' : Type} {s : ℕ} (e' : Ω' ≃ Fin s) (G' : Subgroup (Perm Ω')) (hne : Nonempty Ω')
    {hs : List (Perm (Fin s))} (hg : gens hs = groupFin e' G') (hl : hs.length ≤ s ^ 2) :
    ∃ (lab : Fin s → ℕ) (a : Ω'),
      (∀ i j, lab i = lab j ↔ (orbitSetoid G').r (e'.symm i) (e'.symm j)) ∧ (∀ i, lab i < s) ∧
      (∀ b, Nat.card (orb G' b) ≤ Nat.card (orb G' a)) ∧
      FunDet P f (.list [.nat s, encGroup hs])
        (.list [.list (List.replicate s (.nat 1)), fhierVal (encFun lab) (Nat.card (orb G' a))])
        (hierK * (s + 1) ^ 15) := by
  classical
  haveI : Finite Ω' := Finite.of_equiv _ e'.symm
  obtain ⟨D₁, -, ⟨a, -, hD₁⟩, hmax, hlo'⟩ := lo_spec hlo e' (G := G') (D := Set.univ)
    (fun _ _ _ => by simp) (by obtain ⟨x⟩ := hne; exact ⟨x, trivial⟩) hg hl
  obtain ⟨lab, horb', hlab, hlab'⟩ := orbits_spec horb (1 :: hs)
  have hs1 : 1 ≤ s := by
    obtain ⟨x⟩ := hne
    have := (e' x).isLt
    omega
  refine ⟨lab, a, fun i j => ?_, fun i => (hlab' i).1, fun b => ?_, ?_⟩
  · rw [hlab i j, mem_genOrbit_iff hg]
    rfl
  · have := hmax b trivial
    rw [hD₁] at this
    exact this
  have hM : Nat.card D₁ = Nat.card (orb G' a) := by rw [hD₁]; rfl
  -- the pieces
  set inp := Val.list [.nat s, encGroup hs] with hinp
  set ones := Val.list (List.replicate s (.nat 1)) with hones
  have g0 := Det.arg' (P := P) (vs := [.nat s, encGroup hs]) (rest := []) (j := 0) rfl
  have g1 : ∀ rest, Det P (inp :: rest) (arg 1) (encGroup hs) (2 * inp.wt + 1 + 5) := fun rest =>
    Det.arg' (vs := [.nat s, encGroup hs]) rfl
  have hrs := replicate_spec hrep s (.nat 1)
  have hrs' : FunDet P rep (.list [.nat s, .nat 1]) ones
      (loopModK * (s + 1) * ((Val.list [.nat s, .nat 1]).wt + s + ones.wt + 1)) :=
    hrs.mono fun w c ⟨hw, hc⟩ => ⟨hw, by subst hw; exact hc⟩
  have d1 := Det.call (Det.mk2 g0 (Det.nat 1)) hrs'
  have e1 : ones = indVal e' Set.univ := replicate_eq_indVal e'
  have d2 := Det.call (Det.mk2 (g1 [ones]) (Det.var' (P := P) (env := [inp, ones]) (i := 1) rfl))
    (e1 ▸ hlo')
  have hc3 := count_spec hcnt (xs := (List.finRange s).map (indF e' D₁)) (j := 1) (B := s)
    (fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (indF_le_one e' D₁ i).trans hs1) hs1 (by simp)
  rw [count_indF, hM] at hc3
  have e2 : indVal e' D₁ = natList ((List.finRange s).map (indF e' D₁)) := encFun_eq_natList _
  have d3 := Det.call (Det.mk2 (Det.nat 1) (Det.get' (Det.var' (P := P)
    (env := [inp, ones, .list [indVal e' D₁, indVal e' (Set.univ \ D₁)]]) (i := 2) rfl)
    (Det.nat 0) (e2 ▸ rfl))) hc3
  have d4 := Det.call (g1 [ones, .list [indVal e' D₁, indVal e' (Set.univ \ D₁)],
    .nat (Nat.card (orb G' a))]) horb'
  set env := [inp, ones, Val.list [indVal e' D₁, indVal e' (Set.univ \ D₁)],
    Val.nat (Nat.card (orb G' a))] with henv
  have d5i := Det.ite' (Det.arith' (op := .eq) (Det.var' (P := P) (env := env) (i := 3) rfl) (Det.nat 1) rfl)
    (Det.nil (P := P) (env := env))
    (Det.mk1 (Det.mk4 d4 (Det.var' (P := P) (env := env) (i := 3) rfl)
      (Det.var' (P := P) (env := env) (i := 3) rfl) (Det.nat 0)))
  have hfv : (if GI.Machine.BinOp.eval .eq (Nat.card (orb G' a)) 1 = 0 then
      Val.list [Val.list [encFun lab, .nat (Nat.card (orb G' a)), .nat (Nat.card (orb G' a)),
        .nat 0]] else Val.list []) = fhierVal (encFun lab) (Nat.card (orb G' a)) := by
    simp only [GI.Machine.BinOp.eval, fhierVal, hierVal]
    split_ifs <;> simp_all
  rw [hfv] at d5i
  have d5 := Det.mk2 (Det.var' (P := P) (env := env) (i := 1) rfl) d5i
  have wfh := wt_fhierVal_le (encFun lab) (Nat.card (orb G' a))
  have wnil : (Val.list []).wt = 4 := by simp
  have weq : (Val.nat (GI.Machine.BinOp.eval .eq (Nat.card (orb G' a)) 1)).wt ≤ 3 := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> simp [wt_nat, GI.Machine.len_zero]
  have weq' : GI.Machine.BinOp.eval .eq (Nat.card (orb G' a)) 1 ≤ 1 := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega
  refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 (Det.letE d3 d5))).mono ?_)
  -- the cost
  have hMs : Nat.card (orb G' a) ≤ s := by
    rw [← hM, ← count_indF e' D₁]
    exact List.count_le_length.trans (by simp only [List.length_map, List.length_finRange]; rfl)
  set X := s + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have p12 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by omega)
  have p36 : X ^ 3 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by omega)
  have p615 : X ^ 6 ≤ X ^ 15 := Nat.pow_le_pow_right hX1 (by omega)
  have wg : (encGroup hs).wt ≤ 320 * X ^ 6 := wt_encGroup_le_sq hl
  have wi : inp.wt ≤ 2 * ((Val.nat s).wt + (encGroup hs).wt) + 6 := wt_list2_le _ _
  have wns := wt_nat_le s
  have wo : ones.wt ≤ 7 * X := wt_replicate_one_le s
  have wD1 : (indVal e' D₁).wt ≤ s * (2 * 1 + 5) + 4 := wt_encFun_le _ (indF_le_one e' D₁)
  have wD2 : (indVal e' (Set.univ \ D₁)).wt ≤ s * (2 * 1 + 5) + 4 :=
    wt_encFun_le _ (indF_le_one e' _)
  have wlo := wt_list2_le (indVal e' D₁) (indVal e' (Set.univ \ D₁))
  have wlab : (encFun lab).wt ≤ 4 * X ^ 2 := wt_encFun_le_sq lab fun i => (hlab' i).1.le
  have wM := wt_nat_le (Nat.card (orb G' a))
  have w1 := wt_list2_le (.nat s) (.nat 1)
  have w1' := wt_nat_le 1
  have w2 := wt_list2_le (encGroup hs) ones
  have w3 := wt_list2_le (.nat 1) (indVal e' D₁)
  have w4 := wt_list4_le (encFun lab) (.nat (Nat.card (orb G' a))) (.nat (Nat.card (orb G' a)))
    (.nat 0)
  have w5 := wt_list1_le (Val.list [encFun lab, .nat (Nat.card (orb G' a)),
    .nat (Nat.card (orb G' a)), .nat 0])
  have w6 := wt_list2_le ones (hierVal (encFun lab) (Nat.card (orb G' a)))
  have w0 : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
  have hsX : s * (2 * 1 + 5) + 4 ≤ 11 * X := by omega
  have hrepc : loopModK * X * ((Val.list [.nat s, .nat 1]).wt + s + ones.wt + 1) ≤
      loopModK * X * (50 * X) := Nat.mul_le_mul_left _ (by omega)
  have hrepc' : loopModK * X * (50 * X) = 50000 * X ^ 2 := by simp only [loopModK]; ring
  have horbc : orbitK * (((1 :: hs).length + 1) * X) ^ 5 ≤ orbitK * (32 * X ^ 15) := by
    refine Nat.mul_le_mul_left _ ?_
    calc (((1 :: hs).length + 1) * X) ^ 5 = ((hs.length + 2) * X) ^ 5 := by simp
      _ ≤ (2 * X ^ 3) ^ 5 := Nat.pow_le_pow_left (measure_le_of_sq hl) 5
      _ = 32 * X ^ 15 := by ring
  have hcnt' : countK * (s + 1) ^ 3 = countK * X ^ 3 := rfl
  have hinp : (Val.list [.nat s, encGroup hs]).wt = inp.wt := rfl
  have q1 : (natList ((List.finRange s).map (indF e' D₁))).wt = (indVal e' D₁).wt := by rw [e2]
  have q2 : (Val.list [.nat 1, natList ((List.finRange s).map (indF e' D₁))]).wt =
      (Val.list [.nat 1, indVal e' D₁]).wt := by rw [e2]
  have q3 : (Val.list [ones, Val.list [Val.list [encFun lab, .nat (Nat.card (orb G' a)),
      .nat (Nat.card (orb G' a)), .nat 0]]]).wt =
      (Val.list [ones, hierVal (encFun lab) (Nat.card (orb G' a))]).wt := rfl
  have q4 : (Val.list [Val.list [encFun lab, .nat (Nat.card (orb G' a)),
      .nat (Nat.card (orb G' a)), .nat 0]]).wt =
      (hierVal (encFun lab) (Nat.card (orb G' a))).wt := rfl
  have q5 : (s + 1) ^ 3 = X ^ 3 := rfl
  have q6 : (s + 1) ^ 15 = X ^ 15 := rfl
  have w7 := wt_list2_le ones (fhierVal (encFun lab) (Nat.card (orb G' a)))
  have mx : ∀ a b : ℕ, max a b ≤ a + b := fun a b => max_le (by omega) (by omega)
  have mx1 := mx 5 (2 * inp.wt + 1 + 5 + orbitK * (((1 :: hs).length + 1) * (s + 1)) ^ 5 +
    (encFun lab).wt + 1 + ((Val.nat (Nat.card (orb G' a))).wt + 1) +
    ((Val.nat (Nat.card (orb G' a))).wt + 1) + (0 + 3) +
    4 * (Val.list [encFun lab, Val.nat (Nat.card (orb G' a)), Val.nat (Nat.card (orb G' a)),
      Val.nat 0]).wt + 9 + (Val.list [Val.list [encFun lab, Val.nat (Nat.card (orb G' a)),
      Val.nat (Nat.card (orb G' a)), Val.nat 0]]).wt + 6)
  have mx2 := mx (Val.list []).wt (Val.list [Val.list [encFun lab, Val.nat (Nat.card (orb G' a)),
      Val.nat (Nat.card (orb G' a)), Val.nat 0]]).wt
  simp only [hierK, loK, countK, orbitK] at *
  omega

end GI.Impl
