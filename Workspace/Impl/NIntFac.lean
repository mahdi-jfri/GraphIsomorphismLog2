import Workspace.Impl.NIntLib
import Workspace.Proved.NIntMath

/-!
# Factorization in a normalized product, as a program

Source: [LM] = Luks–Miyazaki, DMTCS 13:4 (2011), Theorem 3.1(viii)(c); Luks 1993, Prop. 7.1.
The task is `GI.Cited.NormalizedFactorTask`: `G = ⟨gs⟩` normalizes `N = ⟨ns⟩` and `x ∈ G N`;
output `[g, m]` with `g ∈ G`, `m ∈ N` and `x = g m`.

The program `nintFacProgram hc` calls constructive membership (`hc`) once:

1. Let `L = (1 :: gs) ++ (1 :: ns)`. Then `x ∈ ⟨L⟩`, so constructive membership returns a
   straight-line program `prog` that reaches `x` from `L`.
2. Evaluate `prog` on `L` with each entry of `1 :: ns` replaced by `1`. This gives `y`.
3. By `GI.Proved.nint_factor`, `y ∈ G` and `y⁻¹ x ∈ N`. Output `[y, y⁻¹ x]`.

The functions (base 0): the entry; `append` at 1; `replicate` at 4; the evaluator of
straight-line programs `linGroupSlpFuns` at 7; `compose` at 12; `inverse` at 16.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

/-- The entry, on `[encGroup gs, encGroup ns, encPerm x]`. The environment after the `let`s:
`[input, encPerm 1, A ++ B, membership answer, table, y, y⁻¹ x]`, where `A` and `B` are the
stored generator lists of `G` and `N`. -/
def nintFacEntry : Expr :=
  .letE (.get (.get (arg 0) (.nat 1)) (.nat 0))
  (.letE (.call 1 (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1))))
  (.letE (.prim 0 (mk2 (mk2 (.get (arg 0) (.nat 0)) (.call 1 (mk2 (mk1 (.var 1)) (.var 2))))
    (arg 2)))
  (.letE (.call 1 (mk2 (.get (arg 0) (.nat 1))
    (.call 4 (mk2 (.length (.get (arg 1) (.nat 1))) (.var 1)))))
  (.letE (.call 7 (mk3 (.var 4) (.get (.var 3) (.nat 1)) (.var 1)))
  (.letE (.call 12 (mk2 (.call 16 (.var 5)) (arg 2)))
  (mk2 (.var 5) (.var 6)))))))

/-- The functions of the program. -/
def nintFacFuns : List Expr :=
  [nintFacEntry] ++ appendFuns 1 ++ replicateFuns 4 ++ linGroupSlpFuns 7 12 16 ++
    composeFuns 12 ++ invFuns 16

/-- **The factorization program**, with constructive membership as primitive `0`. -/
noncomputable def nintFacProgram (hc : ConstructiveMembership) : Program :=
  ⟨nintFacFuns, [linMembershipPrim hc]⟩

section Layout

variable (hc : ConstructiveMembership)

theorem nintFac_hasAt : (nintFacProgram hc).HasAt 0 nintFacFuns := by
  simpa using Program.hasAt_append [] nintFacFuns [] [linMembershipPrim hc]

theorem nintFac_entry : (nintFacProgram hc).funs[0]? = some nintFacEntry := rfl

theorem nintFac_append : (nintFacProgram hc).HasAt 1 (appendFuns 1) :=
  (nintFac_hasAt hc).block 1 rfl

theorem nintFac_replicate : (nintFacProgram hc).HasAt 4 (replicateFuns 4) :=
  (nintFac_hasAt hc).block 4 rfl

theorem nintFac_slp : linGroupSlpAt (nintFacProgram hc) 7 12 16 :=
  linGroupSlpAt_of ((nintFac_hasAt hc).block 7 rfl)

theorem nintFac_compose : (nintFacProgram hc).HasAt 12 (composeFuns 12) :=
  (nintFac_hasAt hc).block 12 rfl

theorem nintFac_inv : (nintFacProgram hc).HasAt 16 (invFuns 16) :=
  (nintFac_hasAt hc).block 16 rfl

theorem nintFac_prim : (nintFacProgram hc).prims[0]? = some (linMembershipPrim hc) := rfl

end Layout

/-! ### Mathematics of the encodings -/

theorem nint_gens_cons_one {n : ℕ} (l : List (Perm (Fin n))) : gens (1 :: l) = gens l := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun g hg => ?_
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg

theorem nint_gens_append_left {n : ℕ} (l l' : List (Perm (Fin n))) : gens l ≤ gens (l ++ l') :=
  Subgroup.closure_mono fun _ hg => List.mem_append_left _ hg

theorem nint_gens_append_right {n : ℕ} (l l' : List (Perm (Fin n))) : gens l' ≤ gens (l ++ l') :=
  Subgroup.closure_mono fun _ hg => List.mem_append_right _ hg

theorem nint_table {n : ℕ} (gs ns : List (Perm (Fin n))) :
    linGroupSlpTable encPerm (nintLeft (1 :: gs) (1 :: ns)) =
      .list ((1 :: gs).map encPerm ++
        List.replicate ((1 :: ns).map encPerm).length (encPerm (1 : Perm (Fin n)))) := by
  simp [linGroupSlpTable, nintLeft, List.map_const', List.replicate_succ]

/-! ### The cost -/

/-- The size bound of the membership input. -/
def nintFacS (X : ℕ) : ℕ := 10 ^ 8 * (X + 1) ^ 2

/-- The bound on the weight of the membership answer. -/
def nintFacMW (d X : ℕ) : ℕ :=
  400 * (nintFacS X ^ d + 1) * (nintFacS X + nintFacS X ^ d + 2) + 100

/-- The bound on the small weights and costs. -/
def nintFacV (X : ℕ) : ℕ := 10 ^ 12 * (X + 1) ^ 4

/-- **The cost of the factorization program** on an input of weight `X`. -/
noncomputable def nintFacCost (hc : ConstructiveMembership) (X : ℕ) : ℕ :=
  1000 * (nintFacV X + nintFacMW (linMembershipDegree hc) X) +
    (linMembershipPrim hc).boundSize (nintFacS X) +
    linGroupSlpCost (10 * (nintFacV X + nintFacMW (linMembershipDegree hc) X))
      (nintFacS X ^ linMembershipDegree hc) (invK * (X + 1) ^ 4) (invK * (X + 1) ^ 4)

theorem nintFacCost_poly (hc : ConstructiveMembership) :
    PBU (fun _ X _ => nintFacCost hc X) := by
  have hs : PBU (fun _ X _ => nintFacS X) := by unfold nintFacS; norm_poly
  have hmw : PBU (fun _ X _ => nintFacMW (linMembershipDegree hc) X) := by
    unfold nintFacMW nintFacS; norm_poly
  have hv : PBU (fun _ X _ => nintFacV X) := by unfold nintFacV; norm_poly
  have hb : PBU (fun _ X _ => (linMembershipPrim hc).boundSize (nintFacS X)) := by
    unfold Prim.boundSize nintFacS; norm_poly
  have hslp := linPoly_subst linGroupSlpCost_poly (PBU.pow hs (linMembershipDegree hc))
    (PBU.smul 10 (PBU.add hv hmw)) (PBU.smul invK (PBU.pow (PBU.addc PBU.W 1) 4))
  exact PBU.add (PBU.add (PBU.smul 1000 (PBU.add hv hmw)) hb) hslp

/-! ### The specification -/

theorem nintFacMW_le {d X c g : ℕ} (hc : c ≤ nintFacS X) (hg : g ≤ nintFacS X) :
    400 * (c ^ d + 1) * (g + c ^ d + 2) + 100 ≤ nintFacMW d X := by
  unfold nintFacMW
  have := Nat.pow_le_pow_left hc d
  gcongr

/-- The weight facts of the input. -/
structure NIntFacW {n : ℕ} (gs ns : List (Perm (Fin n))) (x : Perm (Fin n)) (X : ℕ) : Prop where
  wGA : (encGroup gs).wt + (encGroup ns).wt + (encPerm x).wt < X
  wA : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt
  wB : (Val.list ((1 :: ns).map encPerm)).wt < (encGroup ns).wt
  we1 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt
  hn : n < (encPerm x).wt
  hBl : ((1 :: ns).map encPerm).length < (Val.list ((1 :: ns).map encPerm)).wt
  wn : (Val.nat n).wt ≤ n + 2

theorem nintFacW_of {n : ℕ} (gs ns : List (Perm (Fin n))) (x : Perm (Fin n)) :
    NIntFacW gs ns x (Val.list [encGroup gs, encGroup ns, encPerm x]).wt where
  wGA := by
    have := sum_wt_lt_wt_list [encGroup gs, encGroup ns, encPerm x]
    simp at this; omega
  wA := wt_le_wt_list (by simp [encGroup, encPerms])
  wB := wt_le_wt_list (by simp [encGroup, encPerms])
  we1 := wt_le_wt_list (by simp)
  hn := by
    have := length_lt_wt_list ((List.finRange n).map fun i => Val.nat (x i))
    simpa [encPerm] using this
  hBl := length_lt_wt_list _
  wn := wt_nat_le n

section Spec

variable (hc : ConstructiveMembership) {n : ℕ} (gs ns : List (Perm (Fin n))) (x : Perm (Fin n))


/-- Step 1: `encPerm 1`. -/
theorem nintFac_d1 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns, encPerm x]).wt = X) (hw : NIntFacW gs ns x X) :
    Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x])] (.get (.get (arg 0) (.nat 1)) (.nat 0)) (encPerm (1 : Perm (Fin n))) (20 * (X + 1)) := by
  have h0 := Det.arg' (P := nintFacProgram hc) (vs := [encGroup gs, encGroup ns, encPerm x])
    (rest := []) (j := 0) rfl
  have h2 := Det.getPerm (gs := 1 :: gs) (t := 0) (by simp) (Det.encPerms_gens (gs := 1 :: gs) h0)
    (Det.nat 0)
  refine h2.mono ?_
  have := hw.wGA; have := hw.wA; have := hw.we1
  simp only [List.getElem_cons_zero]
  omega

/-- Step 2: `((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)`. -/
theorem nintFac_d2 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns, encPerm x]).wt = X) (hw : NIntFacW gs ns x X) :
    Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n)))] (.call 1 (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1))))
      (.list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))) (10 ^ 6 * (X + 1) ^ 2) := by
  have hA := Det.encPerms_gens (gs := 1 :: gs) (Det.arg' (P := nintFacProgram hc)
    (vs := [encGroup gs, encGroup ns, encPerm x]) (rest := [(encPerm (1 : Perm (Fin n)))]) (j := 0) rfl)
  have hB := Det.encPerms_gens (gs := 1 :: ns) (Det.arg' (P := nintFacProgram hc)
    (vs := [encGroup gs, encGroup ns, encPerm x]) (rest := [(encPerm (1 : Perm (Fin n)))]) (j := 1) rfl)
  refine (Det.call (Det.mk2 hA hB) (nint_append (nintFac_append hc) ((1 :: gs).map encPerm) ((1 :: ns).map encPerm))).mono ?_
  have := hw.wGA; have := hw.wA; have := hw.wB
  have h1 := wt_list2_le (.list ((1 :: gs).map encPerm)) (.list ((1 :: ns).map encPerm))
  have h2 := nint_wt_append ((1 :: gs).map encPerm) ((1 :: ns).map encPerm)
  have h3 := nint_pow_le (W := (Val.list [.list ((1 :: gs).map encPerm), .list ((1 :: ns).map encPerm)]).wt) (c := 7) (Y := X + 1) (by omega) 2
  have h4 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

/-- The membership instance. -/
def nintFacMI : MemberInst := ⟨n, (1 :: gs) ++ (1 :: ns), x⟩

theorem nintFac_memberInput :
    memberInput (nintFacMI gs ns x) = .list [.list [.nat n, .list ([(encPerm (1 : Perm (Fin n)))] ++ (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)))], encPerm x] := by
  simp only [memberInput, nintFacMI, encGroup, encPerms, List.map_cons, List.map_append,
    List.cons_append, List.nil_append]
  rfl

/-- Step 3, the argument of the membership call. -/
theorem nintFac_d3 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns, encPerm x]).wt = X) (hw : NIntFacW gs ns x X) :
    Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))]
      (mk2 (mk2 (.get (arg 0) (.nat 0)) (.call 1 (mk2 (mk1 (.var 1)) (.var 2)))) (arg 2))
      (memberInput (nintFacMI gs ns x)) (nintFacS X) := by
  have h0 := Det.encPerms_size (gs := 1 :: gs) (Det.arg' (P := nintFacProgram hc)
    (vs := [encGroup gs, encGroup ns, encPerm x]) (rest := [(encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))]) (j := 0) rfl)
  have hv1 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))] (.var 1) (encPerm (1 : Perm (Fin n))) _ := Det.var' rfl
  have hv2 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))] (.var 2) (.list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))) _ :=
    Det.var' rfl
  have hcons := Det.call (Det.mk2 (Det.mk1 hv1) hv2) (nint_append (nintFac_append hc) [(encPerm (1 : Perm (Fin n)))] (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)))
  have hx := Det.arg' (P := nintFacProgram hc) (vs := [encGroup gs, encGroup ns, encPerm x])
    (rest := [(encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))]) (j := 2) rfl
  rw [nintFac_memberInput]
  refine (Det.mk2 (Det.mk2 h0 hcons) hx).mono ?_
  have := hw.wGA; have := hw.wA; have := hw.wB; have := hw.we1; have := hw.hn; have := hw.wn
  have h1 := wt_list2_le (.list [(encPerm (1 : Perm (Fin n)))]) (.list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)))
  have h1' := wt_list1_le (encPerm (1 : Perm (Fin n)))
  have h2 := nint_wt_append ((1 :: gs).map encPerm) ((1 :: ns).map encPerm)
  have h2' := nint_wt_append [(encPerm (1 : Perm (Fin n)))] (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))
  have h5 := wt_list2_le (.nat n) (.list ([(encPerm (1 : Perm (Fin n)))] ++ (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))))
  have h6 := wt_list2_le (.list [.nat n, .list ([(encPerm (1 : Perm (Fin n)))] ++ (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)))]) (encPerm x)
  have h3 := nint_pow_le (W := (Val.list [.list [(encPerm (1 : Perm (Fin n)))], .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm))]).wt) (c := 30) (Y := X + 1)
    (by omega) 2
  have h4 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold nintFacS
  omega

/-- Step 4: the table of `nintLeft (1 :: gs) (1 :: ns)`. -/
theorem nintFac_d4 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns, encPerm x]).wt = X) (hw : NIntFacW gs ns x X) (r : Val) :
    Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r]
      (.call 1 (mk2 (.get (arg 0) (.nat 1)) (.call 4 (mk2 (.length (.get (arg 1) (.nat 1))) (.var 1)))))
      (linGroupSlpTable encPerm (nintLeft (1 :: gs) (1 :: ns))) (10 ^ 8 * (X + 1) ^ 4) := by
  rw [nint_table]
  have hA := Det.encPerms_gens (gs := 1 :: gs) (Det.arg' (P := nintFacProgram hc)
    (vs := [encGroup gs, encGroup ns, encPerm x]) (rest := [(encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r]) (j := 0) rfl)
  have hBl := Det.length (Det.encPerms_gens (gs := 1 :: ns) (Det.arg' (P := nintFacProgram hc)
    (vs := [encGroup gs, encGroup ns, encPerm x]) (rest := [(encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r]) (j := 1) rfl))
  have hv1 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r] (.var 1) (encPerm (1 : Perm (Fin n))) _ := Det.var' rfl
  have hrep := Det.call (Det.mk2 hBl hv1) (nint_replicate (nintFac_replicate hc) ((1 :: ns).map encPerm).length (encPerm (1 : Perm (Fin n))))
  refine (Det.call (Det.mk2 hA hrep) (nint_append (nintFac_append hc) ((1 :: gs).map encPerm)
    (List.replicate ((1 :: ns).map encPerm).length (encPerm (1 : Perm (Fin n)))))).mono ?_
  have := hw.wGA; have := hw.wA; have := hw.wB; have := hw.we1; have := hw.hBl
  set k := ((1 :: ns).map encPerm).length
  obtain ⟨R, hR⟩ : ∃ R, (Val.list (List.replicate k (encPerm (1 : Perm (Fin n))))).wt = R := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, (Val.list (((1 :: gs).map encPerm) ++ List.replicate k (encPerm (1 : Perm (Fin n))))).wt = T := ⟨_, rfl⟩
  obtain ⟨Wa, hWa⟩ : ∃ W, (Val.list [.list ((1 :: gs).map encPerm), .list (List.replicate k (encPerm (1 : Perm (Fin n))))]).wt = W := ⟨_, rfl⟩
  obtain ⟨Wr, hWr⟩ : ∃ W, (Val.list [.nat k, (encPerm (1 : Perm (Fin n)))]).wt = W := ⟨_, rfl⟩
  have h1 := wt_list_le (List.replicate k (encPerm (1 : Perm (Fin n))))
  simp only [List.map_replicate, List.sum_replicate, smul_eq_mul, List.length_replicate, hR] at h1
  have h2 : k * (encPerm (1 : Perm (Fin n))).wt ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have e2 : (X + 1) ^ 2 = X * X + 2 * X + 1 := by ring
  have h3 := nint_wt_append ((1 :: gs).map encPerm) (List.replicate k (encPerm (1 : Perm (Fin n))))
  have h4 := wt_list2_le (.list ((1 :: gs).map encPerm)) (.list (List.replicate k (encPerm (1 : Perm (Fin n)))))
  have h5 := wt_list2_le (.nat k) (encPerm (1 : Perm (Fin n)))
  have h6 := wt_nat_le k
  rw [hR, hT, hWa] at *
  rw [hWr] at h5 ⊢
  have p1 := nint_pow_le (W := Wa) (c := 21) (Y := (X + 1) ^ 2) (by omega) 2
  have p2 := nint_pow_le (W := Wr + k) (c := 11) (Y := X + 1) (by omega) 3
  have e4 : ((X + 1) ^ 2) ^ 2 = (X + 1) ^ 4 := by rw [← pow_mul]
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  have q3 : (X + 1) ^ 3 ≤ (X + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  rw [e4] at p1
  omega

/-- The bound of the evaluation of the straight-line program. -/
noncomputable def nintFacSlpC (hc : ConstructiveMembership) (X : ℕ) : ℕ :=
  linGroupSlpCost (10 * (nintFacV X + nintFacMW (linMembershipDegree hc) X))
    (nintFacS X ^ linMembershipDegree hc) (invK * (X + 1) ^ 4) (invK * (X + 1) ^ 4)

/-- The table value. -/
abbrev nintTab {n : ℕ} (gs ns : List (Perm (Fin n))) : Val :=
  linGroupSlpTable encPerm (nintLeft (1 :: gs) (1 :: ns))

/-- Step 5: evaluate the straight-line program on the table. -/
theorem nintFac_d5 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns, encPerm x]).wt = X) (hw : NIntFacW gs ns x X) (prog : List SlpInstr)
    (es : List (Perm (Fin n))) (hes : linSlpEntries (nintLeft (1 :: gs) (1 :: ns)) prog [] = some es)
    (hr : (Val.list [.nat 1, .list (prog.map encSlpInstr)]).wt ≤ nintFacMW (linMembershipDegree hc) X)
    (hL : prog.length ≤ nintFacS X ^ linMembershipDegree hc) :
    Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), .list [.nat 1, .list (prog.map encSlpInstr)],
        nintTab gs ns]
      (.call 7 (mk3 (.var 4) (.get (.var 3) (.nat 1)) (.var 1))) (encPerm (es.getLast?.getD 1))
      (nintFacSlpC hc X + 20 * (nintFacV X + nintFacMW (linMembershipDegree hc) X)) := by
  have := hw.wGA; have := hw.wA; have := hw.we1; have := hw.hn
  have hn4 : (n + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hn2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have hn3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have hB : ∀ σ : Perm (Fin n), (encPerm σ).wt ≤ invK * (n + 1) ^ 4 := fun σ => by
    have := wt_encPerm_le σ; unfold invK; omega
  have hm : ∀ σ τ : Perm (Fin n), FunDet (nintFacProgram hc) 12 (.list [encPerm σ, encPerm τ])
      (encPerm (σ * τ)) (invK * (n + 1) ^ 4) := fun σ τ =>
    (compose_spec (nintFac_compose hc) σ τ).mono (by unfold permK invK; omega)
  have hi : ∀ σ : Perm (Fin n), FunDet (nintFacProgram hc) 16 (encPerm σ) (encPerm σ⁻¹)
      (invK * (n + 1) ^ 4) := fun σ => inv_spec (nintFac_inv hc) σ
  have hs := linGroupSlp_spec (nintFac_slp hc) encPerm hB hm hi _ prog es hes
  have wT : (linGroupSlpTable encPerm (nintLeft (1 :: gs) (1 :: ns))).wt < 10 ^ 8 * (X + 1) ^ 4 :=
    (nintFac_d4 hc gs ns x hX hw (.list [.nat 1, .list (prog.map encSlpInstr)])).wt_lt
  set T := linGroupSlpTable encPerm (nintLeft (1 :: gs) (1 :: ns))
  set pl := Val.list (prog.map encSlpInstr)
  have wpl : pl.wt < (Val.list [.nat 1, pl]).wt := wt_le_wt_list (by simp)
  have hr' : (Val.list [.nat 1, pl]).wt ≤ nintFacMW (linMembershipDegree hc) X := hr
  have q1 : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have wa := wt_list3_le T pl (encPerm (1 : Perm (Fin n)))
  have hs' := hs.mono (nint_slpCost_mono (W' := 10 * (nintFacV X + nintFacMW (linMembershipDegree hc) X))
    (by unfold nintFacV; omega) hL (show invK * (n + 1) ^ 4 ≤ invK * (X + 1) ^ 4 by
      unfold invK; omega) (show invK * (n + 1) ^ 4 ≤ invK * (X + 1) ^ 4 by unfold invK; omega))
  have hv4 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), .list [.nat 1, pl], T] (.var 4) T _ :=
    Det.var' rfl
  have hv3 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), .list [.nat 1, pl], T] (.var 3)
    (.list [.nat 1, pl]) _ := Det.var' rfl
  have hv1 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), .list [.nat 1, pl], T] (.var 1) (encPerm (1 : Perm (Fin n))) _ :=
    Det.var' rfl
  refine (Det.call (Det.mk3 hv4 (Det.get' hv3 (Det.nat 1) rfl) hv1) hs').mono ?_
  have := hB (es.getLast?.getD 1)
  unfold nintFacSlpC
  unfold nintFacV at *
  unfold invK at *
  omega

/-- Step 6: `y⁻¹ x`. -/
theorem nintFac_d6 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns, encPerm x]).wt = X) (hw : NIntFacW gs ns x X) (r T : Val)
    (y : Perm (Fin n)) :
    Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r, T, encPerm y]
      (.call 12 (mk2 (.call 16 (.var 5)) (arg 2))) (encPerm (y⁻¹ * x)) (10 ^ 6 * (X + 1) ^ 4) := by
  have := hw.wGA; have := hw.hn
  have hv5 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r, T, encPerm y] (.var 5)
    (encPerm y) _ := Det.var' rfl
  have hx := Det.arg' (P := nintFacProgram hc) (vs := [encGroup gs, encGroup ns, encPerm x])
    (rest := [(encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r, T, encPerm y]) (j := 2) rfl
  refine (Det.call (Det.mk2 (Det.call hv5 (inv_spec (nintFac_inv hc) y)) hx)
    (compose_spec (nintFac_compose hc) y⁻¹ x)).mono ?_
  have h1 := wt_encPerm_le y
  have h2 := wt_encPerm_le y⁻¹
  have h3 := wt_encPerm_le (y⁻¹ * x)
  have h4 := wt_list2_le (encPerm y⁻¹) (encPerm x)
  have hn4 : (n + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have hn2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have hn3 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have q1 : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  unfold invK permK
  omega

/-- Step 7: the answer. -/
theorem nintFac_d7 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns, encPerm x]).wt = X) (hw : NIntFacW gs ns x X) (r T : Val)
    (y : Perm (Fin n)) :
    Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r, T, encPerm y, encPerm (y⁻¹ * x)]
      (mk2 (.var 5) (.var 6)) (.list [encPerm y, encPerm (y⁻¹ * x)]) (100 * (X + 1) ^ 2) := by
  have := hw.wGA; have := hw.hn
  have hv5 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r, T, encPerm y,
    encPerm (y⁻¹ * x)] (.var 5) (encPerm y) _ := Det.var' rfl
  have hv6 : Det (nintFacProgram hc) [(Val.list [encGroup gs, encGroup ns, encPerm x]), (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map encPerm) ++ ((1 :: ns).map encPerm)), r, T, encPerm y,
    encPerm (y⁻¹ * x)] (.var 6) (encPerm (y⁻¹ * x)) _ := Det.var' rfl
  refine (Det.mk2 hv5 hv6).mono ?_
  have h1 := wt_encPerm_le y
  have h3 := wt_encPerm_le (y⁻¹ * x)
  have h4 := wt_list2_le (encPerm y) (encPerm (y⁻¹ * x))
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : 1 ≤ (X + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

end Spec

/-- **The factorization program is correct, at cost `nintFacCost`.** -/
theorem nintFac_spec (hc : ConstructiveMembership) (I : FactorInst) :
    FunAll (nintFacProgram hc) 0 (.list [encGroup I.gs, encGroup I.ns, encPerm I.x])
      (fun v c => (∃ g ∈ gens I.gs, ∃ m ∈ gens I.ns, I.x = g * m ∧
          v = .list [encPerm g, encPerm m]) ∧
        c ≤ nintFacCost hc (Val.list [encGroup I.gs, encGroup I.ns, encPerm I.x]).wt) := by
  obtain ⟨n, gs, ns, hnorm, x, hmem⟩ := I
  dsimp only
  have hw := nintFacW_of gs ns x
  obtain ⟨X, hX⟩ : ∃ X, (Val.list [encGroup gs, encGroup ns, encPerm x]).wt = X := ⟨_, rfl⟩
  rw [hX] at hw ⊢
  have hnormal : gens (1 :: gs) ≤ Subgroup.normalizer (gens (1 :: ns) : Set (Perm (Fin n))) := by
    rw [nint_gens_cons_one, nint_gens_cons_one]; exact nint_normalizer hnorm
  have hxm : x ∈ gens ((1 :: gs) ++ (1 :: ns)) := by
    obtain ⟨g, hg, m, hm, rfl⟩ := hmem
    refine Subgroup.mul_mem _ (nint_gens_append_left _ _ ?_) (nint_gens_append_right _ _ ?_)
    · rwa [nint_gens_cons_one]
    · rwa [nint_gens_cons_one]
  have d1 := nintFac_d1 hc gs ns x hX hw
  have d2 := nintFac_d2 hc gs ns x hX hw
  have d3 := nintFac_d3 hc gs ns x hX hw
  have wM := d3.wt_lt
  have hp := EvalAll.prim_spec_le (nintFac_prim hc) d3
    (linMembershipPrim_spec hc (nintFacMI gs ns x) hxm) (fun w hw => linMembershipOut_wt hw)
  -- The size of the membership input and its number of generators are below `nintFacS X`.
  have hS : (memberInput (nintFacMI gs ns x)).cells.length ≤ nintFacS X := by
    have := (memberInput (nintFacMI gs ns x)).size_le_wt
    rw [size_eq_length] at this; omega
  have hgl : (nintFacMI gs ns x).gs.length ≤ nintFacS X := by
    have h1 := length_lt_wt_list ((1 :: (nintFacMI gs ns x).gs).map encPerm)
    have h2 : (Val.list ((1 :: (nintFacMI gs ns x).gs).map encPerm)).wt <
        (encGroup (nintFacMI gs ns x).gs).wt := wt_le_wt_list (by simp)
    have h3 : (encGroup (nintFacMI gs ns x).gs).wt < (memberInput (nintFacMI gs ns x)).wt :=
      wt_le_wt_list (by simp)
    simp only [List.length_map, List.length_cons] at h1
    omega
  have hMW : linMembershipWt (linMembershipDegree hc) (nintFacMI gs ns x) ≤ nintFacMW (linMembershipDegree hc) X := nintFacMW_le hS hgl
  have hbd : (linMembershipPrim hc).bound (memberInput (nintFacMI gs ns x)) ≤
      (linMembershipPrim hc).boundSize (nintFacS X) :=
    Prim.bound_le _ (by have := (memberInput (nintFacMI gs ns x)).size_le_wt; omega)
  apply FunAll.intro (nintFac_entry hc)
  refine EvalAll.letE d1 fun v1 c1 h1 => ?_
  obtain ⟨rfl, hc1⟩ := h1
  refine EvalAll.letE d2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  refine EvalAll.letE hp fun r cr hr => ?_
  obtain ⟨⟨prog, rfl, hlen, hreach⟩, hcr⟩ := hr
  obtain ⟨y, hy, hyG, hyN⟩ := nint_factor hnormal hreach
  obtain ⟨es, hes, rfl⟩ := Option.map_eq_some_iff.mp hy
  have hL : prog.length ≤ nintFacS X ^ linMembershipDegree hc := hlen.trans (Nat.pow_le_pow_left hS _)
  have hrw := (linMembershipOut_wt (d := linMembershipDegree hc) (I := nintFacMI gs ns x) ⟨prog, rfl, hlen, hreach⟩).trans hMW
  have d4 := nintFac_d4 hc gs ns x hX hw (.list [.nat 1, .list (prog.map encSlpInstr)])
  have d5 := nintFac_d5 hc gs ns x hX hw prog es hes hrw hL
  have d6 := nintFac_d6 hc gs ns x hX hw (.list [.nat 1, .list (prog.map encSlpInstr)])
    (nintTab gs ns) (es.getLast?.getD 1)
  have d7 := nintFac_d7 hc gs ns x hX hw (.list [.nat 1, .list (prog.map encSlpInstr)])
    (nintTab gs ns) (es.getLast?.getD 1)
  have dt := Det.letE d4 (Det.letE d5 (Det.letE d6 d7))
  refine dt.post fun c hct => ⟨⟨_, by rwa [nint_gens_cons_one] at hyG, _,
    by rwa [nint_gens_cons_one] at hyN, by group, rfl⟩, ?_⟩
  -- The cost.
  have := hw.wGA; have := hw.wA; have := hw.wB; have := hw.we1; have := hw.hn
  set y := es.getLast?.getD 1
  have w1 := wt_encPerm_le y
  have w2 := wt_encPerm_le (y⁻¹ * x)
  have w3 := wt_list2_le (encPerm y) (encPerm (y⁻¹ * x))
  have w4 := nint_wt_append ((1 :: gs).map encPerm) ((1 :: ns).map encPerm)
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have wT : (nintTab gs ns).wt < 10 ^ 8 * (X + 1) ^ 4 := d4.wt_lt
  unfold nintFacCost
  unfold nintFacSlpC at hct
  unfold nintFacS at *
  unfold nintFacV at *
  omega


end GI.Impl

namespace GI.Impl

open GI.Cited GI.Lang

/-- A uniform polynomial bound in the weight alone. -/
theorem nint_poly_bound {f : ℕ → ℕ} (h : PBU (fun _ W _ => f W)) :
    ∃ K D : ℕ, ∀ W, f W ≤ K * (W + 1) ^ D := by
  obtain ⟨C, D, h⟩ := h
  refine ⟨C * 2 ^ D, D, fun W => ?_⟩
  have h1 : f W ≤ C * (W + 0 + 0 + 2) ^ D := h 0 W 0
  have h2 : (W + 0 + 0 + 2) ^ D ≤ (2 * (W + 1)) ^ D := Nat.pow_le_pow_left (by omega) D
  calc f W ≤ C * (2 * (W + 1)) ^ D := h1.trans (Nat.mul_le_mul_left _ h2)
    _ = C * 2 ^ D * (W + 1) ^ D := by rw [mul_pow]; ring

/-- The cells of a list of values, each with cells at most its size plus one. -/
theorem nint_cells_bound {v : Val} (h : NIntCells v) : ∀ a ∈ v.cells, a ≤ 1 * (v.size + 1) ^ 1 := by
  intro a ha; simpa using h a ha

/-- **Factorization in a normalized product, from constructive membership** ([LM, Theorem
3.1(viii)(c)]). -/
theorem nint_normalizedFactor (hc : ConstructiveMembership) : NormalizedFactor := by
  obtain ⟨K, D, hK⟩ := nint_poly_bound (nintFacCost_poly hc)
  refine polyTimeAt_ofVal_of_lang_cells (nintFacProgram hc) 0 K D 1 1
    (fun I => nint_cells_bound (nint_cells_list (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact nint_cells_group _
      · exact nint_cells_group _
      · exact nint_cells_perm _))) fun I => ?_
  exact (nintFac_spec hc I).mono fun v c h => ⟨h.1, h.2.trans (hK _)⟩

end GI.Impl
