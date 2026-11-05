module

public import Workspace.Proved.VsQDrvMath
public import Workspace.Impl.VsQSot

@[expose] public section

/-!
# The pasting program

An answer is stored as `vsQAnsV a`: `[0]` for `none`, `[1, h, ⟨ks⟩]` for `some (h, ks)`. The
program `vsQPasteE` takes the list of the answers of the cosets (already multiplied by their
representatives) and returns `vsQAnsV (vsQPaste rs)` (`vsQPaste_spec`): it finds the first
nonempty answer `(h₀, ks₀)`, maps every answer to `h₀⁻¹ g` (or `h₀⁻¹ h₀` for an empty one), puts
`ks₀` in front, and reduces the list to at most `n²` generators.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {n : ℕ}

/-- The value of an answer. -/
def vsQAnsV : Option (Perm (Fin n) × List (Perm (Fin n))) → Val
  | none => .list [.nat 0]
  | some (h, ks) => .list [.nat 1, encPerm h, encGroup ks]

theorem encGroup_injective : Function.Injective (encGroup (n := n)) := by
  intro gs hs h
  have := encPerms_injective h
  exact (List.cons.inj this).2

theorem vsQAnsV_injective : Function.Injective (vsQAnsV (n := n)) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => obtain ⟨g, ks⟩ := b; simp [vsQAnsV] at h
  | some a =>
    obtain ⟨g, ks⟩ := a
    cases b with
    | none => simp [vsQAnsV] at h
    | some b =>
      obtain ⟨g', ks'⟩ := b
      simp only [vsQAnsV, Val.list.injEq, List.cons.injEq, and_true, true_and] at h
      rw [encPerm_injective h.1, encGroup_injective h.2]

theorem wt_vsQAnsV_le {a : Option (Perm (Fin n) × List (Perm (Fin n)))}
    (ha : ∀ r ∈ a, r.2.length ≤ n ^ 2) : (vsQAnsV a).wt ≤ 700 * (n + 1) ^ 6 := by
  have q : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  cases a with
  | none =>
    have := wt_list1_le (.nat 0)
    have := wt_nat_le 0
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    simp only [vsQAnsV]; omega
  | some r =>
    obtain ⟨g, ks⟩ := r
    have h1 := wt_list3_le (.nat 1) (encPerm g) (encGroup ks)
    have h2 := wt_encPerm_le g
    have h3 := wt_encGroup_le_sq (n := n) (hs := ks) (ha _ rfl)
    have := wt_nat_le 1
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    simp only [vsQAnsV]; omega

/-- The test of the search: the answer is not empty. -/
def vsQIsSome : Val → Bool
  | .list (.nat 1 :: _) => true
  | _ => false

theorem vsQIsSome_ans (a : Option (Perm (Fin n) × List (Perm (Fin n)))) :
    vsQIsSome (vsQAnsV a) = a.isSome := by
  cases a with
  | none => rfl
  | some r => obtain ⟨g, ks⟩ := r; rfl

/-- The test, on `[c, x]`. -/
def vsQPTestE : Expr := .get (arg 1) (.nat 0)

theorem vsQPTest_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsQPTestE) (c : Val)
    (a : Option (Perm (Fin n) × List (Perm (Fin n)))) :
    FunDet P f (.list [c, vsQAnsV a]) (boolVal (vsQIsSome (vsQAnsV a)))
      (3 * (Val.list [c, vsQAnsV a]).wt + 20) := by
  apply FunDet.intro hf
  have d1 := Det.arg' (P := P) (vs := [c, vsQAnsV a]) (rest := []) (j := 1) rfl
  cases a with
  | none =>
    refine (Det.get' d1 (Det.nat 0) rfl).mono ?_
    have := wt_nat_le 0; have := wt_nat_le 1
    simp only [vsQAnsV] at *; omega
  | some r =>
    obtain ⟨g, ks⟩ := r
    refine (Det.get' d1 (Det.nat 0) rfl).mono ?_
    have := wt_nat_le 0; have := wt_nat_le 1
    simp only [vsQAnsV] at *; omega

/-- The element of an answer after pasting: `h₀⁻¹ g`, or `h₀⁻¹ h₀` for an empty answer. -/
def vsQPasteG (h₀ : Perm (Fin n)) : Option (Perm (Fin n) × List (Perm (Fin n))) → Perm (Fin n)
  | some (g, _) => h₀⁻¹ * g
  | none => h₀⁻¹ * h₀

/-- The map step, on `[[h₀⁻¹, h₀], a]`. -/
def vsQPMapE (cmp : ℕ) : Expr :=
  .ite (.get (arg 1) (.nat 0))
    (.call cmp (mk2 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 1))))
    (.call cmp (mk2 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))))

theorem vsQPMap_spec {P : Program} {f cmp : ℕ} (hf : P.funs[f]? = some (vsQPMapE cmp))
    (hc : P.HasAt cmp (composeFuns cmp)) (h₀ : Perm (Fin n))
    (a : Option (Perm (Fin n) × List (Perm (Fin n)))) :
    FunDet P f (.list [.list [encPerm h₀⁻¹, encPerm h₀], vsQAnsV a]) (encPerm (vsQPasteG h₀ a))
      (10 * (Val.list [.list [encPerm h₀⁻¹, encPerm h₀], vsQAnsV a]).wt + permK * (n + 1) ^ 3 +
        100 * (n + 1) ^ 2 + 40) := by
  apply FunDet.intro hf
  set c := Val.list [encPerm h₀⁻¹, encPerm h₀]
  have d0 := Det.arg' (P := P) (vs := [c, vsQAnsV a]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [c, vsQAnsV a]) (rest := []) (j := 1) rfl
  have dh := Det.get' d0 (Det.nat 0) (show [encPerm h₀⁻¹, encPerm h₀][0]? = some (encPerm h₀⁻¹) from rfl)
  have dh' := Det.get' d0 (Det.nat 1) (show [encPerm h₀⁻¹, encPerm h₀][1]? = some (encPerm h₀) from rfl)
  have w1 := wt_encPerm_le h₀⁻¹
  have w2 := wt_encPerm_le h₀
  have wc := wt_list2_le (encPerm h₀⁻¹) (encPerm h₀)
  have := wt_nat_le 0; have := wt_nat_le 1
  have hcw := wt_le_wt_list (show c ∈ [c, vsQAnsV a] by simp)
  have ec : c.wt = (Val.list [encPerm h₀⁻¹, encPerm h₀]).wt := rfl
  have hcw2 := wt_le_wt_list (show vsQAnsV a ∈ [c, vsQAnsV a] by simp)
  have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  cases a with
  | none =>
    have dt := Det.get' d1 (Det.nat 0) (show [Val.nat 0][0]? = some (.nat 0) from rfl)
    have dc := Det.call (Det.mk2 dh dh') (compose_spec hc h₀⁻¹ h₀)
    refine (Det.ite_zero dt dc).mono ?_
    have := wt_encPerm_le (h₀⁻¹ * h₀)
    have := wt_list2_le (encPerm h₀⁻¹) (encPerm h₀)
    simp only [vsQAnsV, vsQPasteG] at *; omega
  | some r =>
    obtain ⟨g, ks⟩ := r
    have dt := Det.get' d1 (Det.nat 0)
      (show [Val.nat 1, encPerm g, encGroup ks][0]? = some (.nat 1) from rfl)
    have dg := Det.get' d1 (Det.nat 1)
      (show [Val.nat 1, encPerm g, encGroup ks][1]? = some (encPerm g) from rfl)
    have dc := Det.call (Det.mk2 dh dg) (compose_spec hc h₀⁻¹ g)
    refine (Det.ite_pos dt (by norm_num) dc).mono ?_
    have := wt_encPerm_le (h₀⁻¹ * g)
    have := wt_encPerm_le g
    have := wt_list2_le (encPerm h₀⁻¹) (encPerm g)
    have := wt_le_wt_list (show encPerm g ∈ [Val.nat 1, encPerm g, encGroup ks] by simp)
    simp only [vsQAnsV, vsQPasteG] at *; omega

/-- The first nonempty answer. -/
theorem vsQ_findSome {α : Type} : ∀ rs : List (Option α),
    (∀ hi : rs.findIdx Option.isSome < rs.length, rs.findSome? id = rs[rs.findIdx Option.isSome]) ∧
      (rs.length ≤ rs.findIdx Option.isSome → rs.findSome? id = none)
  | [] => ⟨fun h => absurd h (by simp), fun _ => rfl⟩
  | none :: rs => by
    obtain ⟨h1, h2⟩ := vsQ_findSome rs
    simp only [List.findIdx_cons, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, List.findSome?_cons, id, List.getElem_cons_succ]
    exact ⟨fun hi => h1 (by omega), fun hi => h2 (by omega)⟩
  | some a :: rs => by
    simp [List.findIdx_cons]

theorem vsQ_findIdx_map (rs : List (Option (Perm (Fin n) × List (Perm (Fin n))))) :
    (rs.map vsQAnsV).findIdx vsQIsSome = rs.findIdx Option.isSome := by
  induction rs with
  | nil => rfl
  | cons a rs ih => simp only [List.map_cons, List.findIdx_cons, vsQIsSome_ans, ih]

/-- The pasting program, on the list of answers. -/
def vsQPasteE (fd inv mp app mkg red : ℕ) : Expr :=
  .letE (.call fd (mk2 (.nat 0) (.var 0)))
    (.ite (.arith .sub (.length (.var 0)) (.var 1))
      (.letE (.get (.var 0) (.var 1))
        (.letE (.call inv (.get (.var 2) (.nat 1)))
          (mk3 (.nat 1) (.get (.var 2) (.nat 1))
            (.call red (.call mkg (mk2 (.get (.get (.var 2) (.nat 2)) (.nat 0))
              (.call app (mk2 (.get (.get (.var 2) (.nat 2)) (.nat 1))
                (.call mp (mk2 (mk2 (.var 3) (.get (.var 2) (.nat 1))) (.var 0)))))))))))
      (mk1 (.nat 0)))

/-- The cost of pasting. -/
noncomputable def vsQPasteCost (hm : Membership) (n S : ℕ) : ℕ :=
  reduceCost hm n (2 * S ^ 2) + 10 ^ 13 * S ^ 14

theorem vsQPaste_some {rs : List (Option (Perm (Fin n) × List (Perm (Fin n))))}
    {h₀ : Perm (Fin n)} {ks₀ : List (Perm (Fin n))} (h : rs.findSome? id = some (h₀, ks₀)) :
    vsQPaste rs = some (h₀, keepList (ks₀ ++ rs.map (vsQPasteG h₀))) := by
  unfold vsQPaste
  rw [h]
  congr 3

set_option maxHeartbeats 4000000 in
/-- **Pasting.** -/
theorem vsQPaste_spec (hm : Membership) {P : Program} {f fd inv mp app mkg red jm cmp : ℕ}
    (hf : P.funs[f]? = some (vsQPasteE fd inv mp app mkg red))
    (hfd : P.HasAt fd (findFuns fd (fd + 3))) (ht : P.funs[fd + 3]? = some vsQPTestE)
    (hinv : P.HasAt inv (invFuns inv)) (hmp : P.HasAt mp (mapFuns mp (mp + 3)))
    (hmpE : P.funs[mp + 3]? = some (vsQPMapE cmp)) (hc : P.HasAt cmp (composeFuns cmp))
    (happ : P.HasAt app (appendFuns app)) (hmkg : P.HasAt mkg (mkGroupFuns mkg))
    (hred : P.HasAt red (reduceFuns red jm)) (hj : P.prims[jm]? = some (membershipPrim hm))
    {S : ℕ} (rs : List (Option (Perm (Fin n) × List (Perm (Fin n)))))
    (hS : n + 1 ≤ S) (hT : rs.length + 1 ≤ S) (hks : ∀ a ∈ rs, ∀ r ∈ a, r.2.length ≤ n ^ 2) :
    FunDet P f (.list (rs.map vsQAnsV)) (vsQAnsV (vsQPaste rs)) (vsQPasteCost hm n S) := by
  have hS1 : 1 ≤ S := by omega
  set T := rs.length with hTdef
  set xs := rs.map vsQAnsV with hxs
  set L := Val.list xs with hL
  set i := rs.findIdx Option.isSome with hi
  have q1 : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have qk : ∀ a b, a ≤ b → S ^ a ≤ S ^ b := fun a b h => Nat.pow_le_pow_right hS1 h
  have hn6 : (n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hS 6
  have hn3 : (n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hS 3
  have hn2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS 2
  have hnn : n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
  -- weights of the answers
  have wA : ∀ x ∈ xs, x.wt ≤ 700 * S ^ 6 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact (wt_vsQAnsV_le (hks a ha)).trans (by omega)
  have wL : L.wt ≤ 1500 * S ^ 7 := by
    have h := vs_wt_list_le_of xs wA
    have eL : L.wt = (Val.list xs).wt := rfl
    have hlx : xs.length = T := by simp [hxs, hTdef]
    rw [hlx] at h
    have : T * (2 * (700 * S ^ 6) + 1) ≤ S * (1401 * S ^ 6) :=
      Nat.mul_le_mul (by omega) (by have : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega); omega)
    have e : S * (1401 * S ^ 6) = 1401 * S ^ 7 := by ring
    have : 1 ≤ S ^ 7 := Nat.one_le_pow _ _ (by omega)
    omega
  -- the search
  have hfind : FunDet P fd (.list [.nat 0, L]) (.nat i)
      ((xs.map fun x => 3 * (Val.list [.nat 0, x]).wt + 20).sum +
        loopModK * (xs.length + 1) * ((Val.list [.nat 0, L]).wt + 2 * xs.length + 3)) := by
    have h := find_spec hfd (c := .nat 0) (xs := xs) (q := vsQIsSome)
      (B := fun x => 3 * (Val.list [.nat 0, x]).wt + 20) (by
        intro x hx
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
        exact vsQPTest_spec ht (.nat 0) a)
    refine h.mono fun w c hw => ⟨?_, hw.2⟩
    rw [hw.1, hxs, vsQ_findIdx_map]
  have dfind := Det.call (Det.mk2 (Det.nat 0) (Det.var' (P := P) (env := [L]) (i := 0) rfl)) hfind
  have cfind : (xs.map fun x => 3 * (Val.list [.nat 0, x]).wt + 20).sum +
      loopModK * (xs.length + 1) * ((Val.list [.nat 0, L]).wt + 2 * xs.length + 3) ≤
        10 ^ 7 * S ^ 8 := by
    have h1 : (xs.map fun x => 3 * (Val.list [.nat 0, x]).wt + 20).sum ≤ xs.length * (5000 * S ^ 6) := by
      have hb : ∀ y ∈ xs.map (fun x => 3 * (Val.list [.nat 0, x]).wt + 20), y ≤ 5000 * S ^ 6 := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        have := wt_list2_le (.nat 0) x
        have := wA x hx
        have := wt_nat_le 0
        have : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
        omega
      have := List.sum_le_card_nsmul _ _ hb
      simpa using this
    have hlx : xs.length = T := by simp [hxs, hTdef]
    rw [hlx] at h1 ⊢
    have h2 : T * (5000 * S ^ 6) ≤ S * (5000 * S ^ 6) := Nat.mul_le_mul_right _ (by omega)
    have e2 : S * (5000 * S ^ 6) = 5000 * S ^ 7 := by ring
    have w2 := wt_list2_le (.nat 0) L
    have := wt_nat_le 0
    have h3 : loopModK * (T + 1) * ((Val.list [.nat 0, L]).wt + 2 * T + 3) ≤
        loopModK * S * (4000 * S ^ 7) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by
        have : S ≤ S ^ 7 := Nat.le_self_pow (by norm_num) _
        have : 1 ≤ S ^ 7 := Nat.one_le_pow _ _ (by omega)
        omega)
    have e3 : loopModK * S * (4000 * S ^ 7) = 4 * 10 ^ 6 * S ^ 8 := by simp [loopModK]; ring
    have := qk 7 8 (by norm_num)
    omega
  apply FunDet.intro hf
  have hxl : xs.length = T := by simp [hxs, hTdef]
  have dsub : Det P [L, .nat i] (.arith .sub (.length (.var 0)) (.var 1)) (.nat (T - i)) _ :=
    Det.arith' (Det.length (Det.var' (P := P) (env := [L, .nat i]) (i := 0) (v := Val.list xs) rfl))
      (Det.var' (i := 1) rfl) (by simp [GI.Machine.BinOp.eval, hxl])
  have hval : ∀ v : Val, v = vsQAnsV (vsQPaste rs) → v.wt ≤ 700 * S ^ 6 := by
    rintro v rfl
    refine (wt_vsQAnsV_le ?_).trans (by omega)
    intro r hr
    unfold vsQPaste at hr
    cases hfs : rs.findSome? id with
    | none => rw [hfs] at hr; simp at hr
    | some a =>
      rw [hfs] at hr
      obtain ⟨h₀, ks₀⟩ := a
      simp only [Option.mem_def, Option.some.injEq] at hr
      rw [← hr]; exact length_keepList_le _
  -- the branch with a nonempty answer
  have dfound : T - i ≠ 0 → Det P [L, .nat i]
      (.letE (.get (.var 0) (.var 1))
        (.letE (.call inv (.get (.var 2) (.nat 1)))
          (mk3 (.nat 1) (.get (.var 2) (.nat 1))
            (.call red (.call mkg (mk2 (.get (.get (.var 2) (.nat 2)) (.nat 0))
              (.call app (mk2 (.get (.get (.var 2) (.nat 2)) (.nat 1))
                (.call mp (mk2 (mk2 (.var 3) (.get (.var 2) (.nat 1))) (.var 0)))))))))))
      (vsQAnsV (vsQPaste rs)) (reduceCost hm n (2 * S ^ 2) + 10 ^ 12 * S ^ 14) := by
    intro hne
    have hiT : i < rs.length := by omega
    have hsome : (rs[i]'hiT).isSome := List.findIdx_getElem (w := hiT)
    obtain ⟨⟨h₀, ks₀⟩, hr⟩ := Option.isSome_iff_exists.mp hsome
    have hfs : rs.findSome? id = some (h₀, ks₀) := by rw [(vsQ_findSome rs).1 hiT]; exact hr
    have hks₀ : ks₀.length ≤ n ^ 2 := hks _ (List.getElem_mem hiT) (h₀, ks₀) (by simp [hr])
    rw [vsQPaste_some hfs]
    set a0 := Val.list [.nat 1, encPerm h₀, encGroup ks₀] with ha0
    set hs := 1 :: (ks₀ ++ rs.map (vsQPasteG h₀)) with hhs
    set c := Val.list [encPerm h₀⁻¹, encPerm h₀] with hcdef
    set ys := rs.map fun a => encPerm (vsQPasteG h₀ a) with hys
    set ks' := (1 :: ks₀).map encPerm with hks'
    have da0 : Det P [L, .nat i] (.get (.var 0) (.var 1)) a0 _ :=
      Det.get' (Det.var' (P := P) (env := [L, .nat i]) (i := 0) (v := Val.list xs) rfl)
        (Det.var' (i := 1) rfl) (by
          simp only [hxs, List.getElem?_map]; rw [List.getElem?_eq_getElem hiT, hr]; rfl)
    have dinv := Det.call (Det.get' (Det.var' (P := P) (env := [L, .nat i, a0]) (i := 2) rfl)
      (Det.nat 1) (show [Val.nat 1, encPerm h₀, encGroup ks₀][1]? = some (encPerm h₀) from rfl))
      (inv_spec hinv h₀)
    set E4 := [L, .nat i, a0, encPerm h₀⁻¹] with hE4
    have dh0 : Det P E4 (.get (.var 2) (.nat 1)) (encPerm h₀) _ :=
      Det.get' (Det.var' (i := 2) rfl) (Det.nat 1)
        (show [Val.nat 1, encPerm h₀, encGroup ks₀][1]? = some (encPerm h₀) from rfl)
    have dc : Det P E4 (mk2 (.var 3) (.get (.var 2) (.nat 1))) c _ :=
      Det.mk2 (Det.var' (i := 3) rfl) dh0
    have hmapF : FunDet P mp (.list [c, .list (rs.map vsQAnsV)]) (.list ys)
        (rs.length * (10 ^ 5 * S ^ 6) + mapK * (rs.length + 1) *
          ((Val.list [c, .list (rs.map vsQAnsV)]).wt + (Val.list ys).wt + 1)) := by
      have := mapList_spec hmp rs vsQAnsV (fun a => encPerm (vsQPasteG h₀ a)) (c := c)
        (B := 10 ^ 5 * S ^ 6)
        (fun a _ a' _ he => by rw [vsQAnsV_injective he])
        (fun a ha => (vsQPMap_spec hmpE hc h₀ a).mono (by
          have w1 := wt_encPerm_le h₀⁻¹
          have w2 := wt_encPerm_le h₀
          have w3 := wt_list2_le (encPerm h₀⁻¹) (encPerm h₀)
          have w4 := wt_list2_le c (vsQAnsV a)
          have w5 := wA (vsQAnsV a) (List.mem_map_of_mem ha)
          have ec : c.wt = (Val.list [encPerm h₀⁻¹, encPerm h₀]).wt := rfl
          have ec2 : (Val.list [c, vsQAnsV a]).wt =
            (Val.list [Val.list [encPerm h₀⁻¹, encPerm h₀], vsQAnsV a]).wt := rfl
          have p2 : S ^ 2 ≤ S ^ 6 := qk 2 6 (by norm_num)
          have p3 : S ^ 3 ≤ S ^ 6 := qk 3 6 (by norm_num)
          have : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ (by omega)
          simp only [permK] at *
          omega))
      simpa [hys, List.map_map, Function.comp_def] using this
    have dmap : Det P E4 (.call mp (mk2 (mk2 (.var 3) (.get (.var 2) (.nat 1))) (.var 0)))
        (.list ys) _ := Det.call (Det.mk2 dc (Det.var' (i := 0) (v := Val.list (rs.map vsQAnsV)) rfl)) hmapF
    have dks : Det P E4 (.get (.get (.var 2) (.nat 2)) (.nat 1)) (.list ks') _ :=
      Det.get' (Det.get' (Det.var' (i := 2) rfl) (Det.nat 2)
        (show [Val.nat 1, encPerm h₀, encGroup ks₀][2]? = some (encGroup ks₀) from rfl)) (Det.nat 1)
        (show [Val.nat n, .list ks'][1]? = some (.list ks') from rfl)
    have dn : Det P E4 (.get (.get (.var 2) (.nat 2)) (.nat 0)) (.nat n) _ :=
      Det.get' (Det.get' (Det.var' (i := 2) rfl) (Det.nat 2)
        (show [Val.nat 1, encPerm h₀, encGroup ks₀][2]? = some (encGroup ks₀) from rfl)) (Det.nat 0)
        (show [Val.nat n, .list ks'][0]? = some (.nat n) from rfl)
    have e1 : ks' ++ ys = hs.map encPerm := by
      simp [hks', hys, hhs, List.map_append]
    have happF : FunDet P app (.list [.list ks', .list ys]) (.list (hs.map encPerm))
        (loopModK * (ys.length + 1) * ((Val.list [.list ks', .list ys]).wt + ys.length +
          (Val.list (hs.map encPerm)).wt + 1)) := by
      refine (append_spec happ ks' ys).mono fun w c' hw => ⟨by rw [hw.1, e1], ?_⟩
      have := hw.2; rw [hw.1, e1] at this; exact this
    have dapp := Det.call (Det.mk2 dks dmap) happF
    have dmk := Det.call (Det.mk2 dn dapp) (mkGroup_spec hmkg hs)
    have dred := Det.call dmk (reduce_spec hm hred hj hs)
    have dres := Det.mk3 (Det.nat (P := P) (env := E4) 1) dh0 dred
    have ev : Val.list [.nat 1, encPerm h₀, encGroup (keepList hs)] =
        vsQAnsV (some (h₀, keepList (ks₀ ++ rs.map (vsQPasteG h₀)))) := by
      rw [hhs, keepList_one_cons]; rfl
    rw [← ev]
    refine (Det.letE da0 (Det.letE dinv dres)).mono ?_
    -- the cost
    have hTS : T + 1 ≤ S := hT
    have hn1 : n + 1 ≤ S := hS
    have hH : hs.length ≤ S ^ 2 := by
      have e : hs.length = 1 + ks₀.length + T := by simp [hhs, hTdef]; omega
      have : (n + 1) ^ 2 ≤ S ^ 2 := hn2
      have : n ^ 2 + T + 1 ≤ S ^ 2 := by nlinarith
      omega
    have hysl : ys.length = T := by simp [hys, hTdef]
    have w1 := wt_encPerm_le h₀
    have w2 := wt_encPerm_le h₀⁻¹
    have w3 := wt_encGroup_le_sq hks₀
    have w4 := wt_list3_le (.nat 1) (encPerm h₀) (encGroup ks₀)
    have w5 := wt_encGroup_le_sq (length_keepList_le hs)
    have w6 := wt_list3_le (.nat 1) (encPerm h₀) (encGroup (keepList hs))
    have w7 := wt_list2_le (encPerm h₀⁻¹) (encPerm h₀)
    have ec : c.wt = (Val.list [encPerm h₀⁻¹, encPerm h₀]).wt := rfl
    have ea0 : a0.wt = (Val.list [.nat 1, encPerm h₀, encGroup ks₀]).wt := rfl
    have eks : (encGroup ks₀) = .list [.nat n, .list ks'] := rfl
    have wks' : (Val.list ks').wt < (encGroup ks₀).wt := by
      rw [eks]; exact wt_le_wt_list (by simp)
    have wys : (Val.list ys).wt ≤ 9 * S ^ 3 + 4 := by
      have h := vs_wt_list_le_of ys (c := 4 * S ^ 2) (by
        intro y hy
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
        exact (wt_encPerm_le _).trans (by omega))
      rw [hysl] at h
      have : T * (2 * (4 * S ^ 2) + 1) ≤ S * (9 * S ^ 2) :=
        Nat.mul_le_mul (by omega) (by have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
      have e : S * (9 * S ^ 2) = 9 * S ^ 3 := by ring
      omega
    have whs : (Val.list (hs.map encPerm)).wt ≤ 9 * S ^ 4 + 4 := by
      have h := vs_wt_list_le_of (hs.map encPerm) (c := 4 * S ^ 2) (by
        intro y hy
        obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
        exact (wt_encPerm_le _).trans (by omega))
      rw [List.length_map] at h
      have : hs.length * (2 * (4 * S ^ 2) + 1) ≤ S ^ 2 * (9 * S ^ 2) :=
        Nat.mul_le_mul hH (by have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega); omega)
      have e : S ^ 2 * (9 * S ^ 2) = 9 * S ^ 4 := by ring
      omega
    have whg : (encGroup hs).wt ≤ 360 * S ^ 6 := by
      have h := wt_encGroup_le hs
      have : (hs.length + 2) * (n + 1) ≤ (3 * S ^ 2) * S :=
        Nat.mul_le_mul (by have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega); omega) hn1
      have h2 := Nat.pow_le_pow_left this 2
      have e : ((3 * S ^ 2) * S) ^ 2 = 9 * S ^ 6 := by ring
      omega
    have cmk : mkGroupK * ((hs.length + 2) * (n + 1)) ^ 3 ≤ 27 * 10 ^ 5 * S ^ 9 := by
      have : (hs.length + 2) * (n + 1) ≤ (3 * S ^ 2) * S :=
        Nat.mul_le_mul (by have : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega); omega) hn1
      have h2 := Nat.pow_le_pow_left this 3
      have e : ((3 * S ^ 2) * S) ^ 3 = 27 * S ^ 9 := by ring
      simp only [mkGroupK]; omega
    have cred : reduceCost hm n hs.length ≤ reduceCost hm n (2 * S ^ 2) :=
      reduceCost_mono hm n (by omega)
    have wcL := wt_list2_le c (.list (rs.map vsQAnsV))
    have eL' : (Val.list (rs.map vsQAnsV)).wt = L.wt := rfl
    have eL : L.wt = (Val.list xs).wt := rfl
    have cmap1 : rs.length * (10 ^ 5 * S ^ 6) ≤ 10 ^ 5 * S ^ 7 := by
      have := Nat.mul_le_mul_right (10 ^ 5 * S ^ 6) (show rs.length ≤ S by omega)
      have e : S * (10 ^ 5 * S ^ 6) = 10 ^ 5 * S ^ 7 := by ring
      omega
    have p23 : S ^ 2 ≤ S ^ 3 := qk 2 3 (by norm_num)
    have p34 : S ^ 3 ≤ S ^ 4 := qk 3 4 (by norm_num)
    have p46 : S ^ 4 ≤ S ^ 6 := qk 4 6 (by norm_num)
    have p67 : S ^ 6 ≤ S ^ 7 := qk 6 7 (by norm_num)
    have p79 : S ^ 7 ≤ S ^ 9 := qk 7 9 (by norm_num)
    have p914 : S ^ 9 ≤ S ^ 14 := qk 9 14 (by norm_num)
    have p0 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ (by omega)
    have cmap2 : mapK * (rs.length + 1) *
        ((Val.list [c, .list (rs.map vsQAnsV)]).wt + (Val.list ys).wt + 1) ≤ 10 ^ 3 * S * (4000 * S ^ 7) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      omega
    have e2 : 10 ^ 3 * S * (4000 * S ^ 7) = 4 * 10 ^ 6 * S ^ 8 := by ring
    have p78 : S ^ 7 ≤ S ^ 8 := qk 7 8 (by norm_num)
    have p814 : S ^ 8 ≤ S ^ 14 := qk 8 14 (by norm_num)
    have wkl := wt_list2_le (.list ks') (.list ys)
    have capp : loopModK * (ys.length + 1) * ((Val.list [.list ks', .list ys]).wt + ys.length +
        (Val.list (hs.map encPerm)).wt + 1) ≤ 10 ^ 3 * S * (2000 * S ^ 6) := by
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      omega
    have e3 : 10 ^ 3 * S * (2000 * S ^ 6) = 2 * 10 ^ 6 * S ^ 7 := by ring
    have wn := wt_nat_le n
    have wi := wt_nat_le i
    have eg0 : (Val.list [.nat n, .list ((1 :: ks₀).map encPerm)]).wt = (encGroup ks₀).wt := rfl
    have wmk := wt_list2_le (.nat n) (.list (hs.map encPerm))
    have w1' := wt_nat_le 1
    have hiS : i ≤ S := by omega
    have hn4 : (n + 1) ^ 4 ≤ S ^ 4 := Nat.pow_le_pow_left hS 4
    simp only [invK] at *
    clear dmap dapp dmk dred dres dinv da0 dks dn dh0 dc happF hmapF
    generalize reduceCost hm n (2 * S ^ 2) = R at *
    generalize reduceCost hm n hs.length = R' at *
    omega
  have dnone : T - i = 0 → Det P [L, .nat i] (mk1 (.nat 0)) (vsQAnsV (vsQPaste rs)) 20 := by
    intro h0
    have hfs : rs.findSome? id = none := (vsQ_findSome rs).2 (by omega)
    have : vsQPaste rs = none := by unfold vsQPaste; rw [hfs]
    rw [this]
    refine (Det.mk1 (Det.nat 0)).mono ?_
    have := wt_list1_le (.nat 0); have := wt_nat_le 0
    omega
  have dbody := Det.ite dsub dfound dnone
  refine (Det.letE dfind dbody).mono ?_
  have := hval _ rfl
  have wi := wt_nat_le i
  have hiT : i ≤ T := List.findIdx_le_length
  have := wt_list2_le (.nat 0) L
  have := wt_nat_le 0
  have p7 : S ^ 7 ≤ S ^ 14 := qk 7 14 (by norm_num)
  have p8 : S ^ 8 ≤ S ^ 14 := qk 8 14 (by norm_num)
  have p6 : S ^ 6 ≤ S ^ 14 := qk 6 14 (by norm_num)
  have : 1 ≤ S ^ 14 := Nat.one_le_pow _ _ (by omega)
  have eL : L.wt = (Val.list xs).wt := rfl
  have : S ≤ S ^ 14 := Nat.le_self_pow (by norm_num) _
  simp only [vsQPasteCost]
  clear dbody dfound dnone dsub dfind hfind
  generalize S ^ 14 = Q at *
  generalize reduceCost hm n (2 * S ^ 2) = R at *
  omega

end GI.Impl
