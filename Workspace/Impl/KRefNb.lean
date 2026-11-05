module

public import Workspace.Impl.KRefBounds

@[expose] public section

/-!
# The table of neighbours of each tuple

For the tuple `x` with index `j`, the program stores `nb(x) = [j, pat x, tidx x, upd x]`:
* `pat x`, the equality pattern (`krefPat`);
* `tidx x`, the indices of `x ∘ τ` for all `τ : Fin k → Fin k`;
* `upd x`, for each point `z`, the indices of `x` with entry `i` replaced by `z`, over `i`.

These are the only places where the program looks at the entries of tuples; a round of the
refinement only reads colors at these indices. `krefNbVal x` is the value, and `kref_nbF`
computes it from `j`.
-/

namespace GI.Impl

open GI.Lang GI.Cited

variable {n k : ℕ}

/-! ### The values -/

/-- The index of a tuple. -/
def krefIdx (x : Fin k → Fin n) : ℕ := (finFunctionFinEquiv x : ℕ)

theorem krefIdx_lt (x : Fin k → Fin n) : krefIdx x < n ^ k := (finFunctionFinEquiv x).isLt

/-- The indices of `x ∘ τ`. -/
def krefTidx (x : Fin k → Fin n) : List ℕ := (krefTups k k).map fun τ => krefIdx (x ∘ τ)

/-- The indices of `x` with entry `i` replaced by `z`. -/
def krefUpd (x : Fin k → Fin n) : List (List ℕ) :=
  (List.finRange n).map fun z => (List.finRange k).map fun i => krefIdx (Function.update x i z)

/-- The table entry of `x`. -/
def krefNbVal (x : Fin k → Fin n) : Val :=
  .list [.nat (krefIdx x), natList (krefPat x), natList (krefTidx x),
    .list ((krefUpd x).map natList)]

/-! ### Digits and indices -/

theorem kref_range_map {β : Type} (m : ℕ) (f : ℕ → β) :
    (List.range m).map f = (List.finRange m).map fun i : Fin m => f (i : ℕ) := by
  rw [show (fun i : Fin m => f (i : ℕ)) = f ∘ (fun i : Fin m => (i : ℕ)) from rfl, ← List.map_map,
    List.map_coe_finRange_eq_range]

theorem kref_digits_eq (j : Fin (n ^ k)) :
    (krefPowList n k).map (fun p => (j : ℕ) / p % n) = krefDig (finFunctionFinEquiv.symm j) := by
  unfold krefPowList krefDig
  rw [List.map_map, kref_range_map, List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  simp [finFunctionFinEquiv_symm_apply_val]

theorem kref_dig_getD (x : Fin k → Fin n) (r : Fin k) : (krefDig x).getD r 0 = x r := by
  simp [krefDig, List.getD_eq_getElem?_getD]

theorem kref_pw_getD (r : Fin k) : (krefPowList n k).getD r 0 = n ^ (r : ℕ) := by
  simp [krefPowList, List.getD_eq_getElem?_getD, List.getElem?_range r.isLt]

theorem kref_dot_eq {E ρ : List ℕ} {y : Fin k → Fin n}
    (h : ∀ r : Fin k, E.getD (ρ.getD r 0) 0 = (y r : ℕ)) :
    krefDot (krefPowList n k) E ρ k = krefIdx y := by
  unfold krefDot krefIdx
  rw [finFunctionFinEquiv_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun r => E.getD (ρ.getD r 0) 0 * (krefPowList n k).getD r 0)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [h r, kref_pw_getD]

theorem kref_dot_tau (x : Fin k → Fin n) (τ : Fin k → Fin k) (z : ℕ) :
    krefDot (krefPowList n k) (krefDig x ++ [z]) (krefDig τ) k = krefIdx (x ∘ τ) := by
  refine kref_dot_eq fun r => ?_
  rw [kref_dig_getD, List.getD_append _ _ _ _ (by rw [length_krefDig]; exact (τ r).isLt),
    kref_dig_getD]
  rfl

theorem kref_rho_getD (i r : Fin k) :
    ((List.range k).map fun r' => if r' = (i : ℕ) then k else r').getD r 0 =
      if r = i then k else r := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range r.isLt,
    Option.map_some, Option.getD_some, Fin.val_inj]

theorem kref_dot_rho (x : Fin k → Fin n) (i : Fin k) (z : Fin n) :
    krefDot (krefPowList n k) (krefDig x ++ [(z : ℕ)])
      ((List.range k).map fun r' => if r' = (i : ℕ) then k else r') k =
      krefIdx (Function.update x i z) := by
  refine kref_dot_eq fun r => ?_
  rw [kref_rho_getD]
  by_cases hr : r = i
  · subst hr
    rw [if_pos rfl, List.getD_append_right _ _ _ _ (by rw [length_krefDig]),
      length_krefDig, Nat.sub_self, Function.update_self]
    rfl
  · rw [if_neg hr, List.getD_append _ _ _ _ (by rw [length_krefDig]; exact r.isLt),
      kref_dig_getD, Function.update_of_ne hr]

/-! ### The update lists -/

/-- On `[[pw, D, rhos], z]`: the indices `codes [[pw, D ++ [z]], rhos]`. -/
def krefUpdF (codes : ℕ) : Expr :=
  .call codes (mk2 (mk2 (.get (arg 0) (.nat 0)) (.snoc (.get (arg 0) (.nat 1)) (arg 1)))
    (.get (arg 0) (.nat 2)))

/-- `upd`, at base `b` (four functions); `codes` is the index of the codes module. -/
def krefUpdFuns (b codes : ℕ) : List Expr := mapFuns b (b + 3) ++ [krefUpdF codes]

def krefUpdBodyK : ℕ := 2 * krefCodesK + 200

def krefUpdK : ℕ := mapK * (3 * krefUpdBodyK + 11) * 3 ^ 7

theorem kref_codesOK_rho (x : Fin k → Fin n) {z : ℕ} (hz : z < n) :
    KrefCodesOK (krefZ n k) (krefPowList n k) (krefDig x ++ [z]) (krefRhos k) := by
  have hX2 := kref_X_le_sq (n := n) (k := k)
  refine ⟨fun a ha => (kref_pw_le a ha).trans X_le_Z, fun a ha => ?_, fun ρ hρ => ?_,
    kref_le_Z (c := 7) (a := 2) (by norm_num) (by norm_num) kref_wt_pw, ?_,
    kref_le_Z (c := 30) (a := 3) (by norm_num) (by norm_num) kref_wt_rhos, ?_⟩
  · rcases List.mem_append.mp ha with ha | ha
    · exact ((kref_dig_le x a ha).le.trans n_le_krefX).trans X_le_Z
    · rw [List.mem_singleton.mp ha]; exact (hz.le.trans n_le_krefX).trans X_le_Z
  · refine ⟨by rw [length_krefPowList, length_krefRho hρ], fun a ha => ?_, ?_,
      kref_le_Z (c := 7) (a := 2) (by norm_num) (by norm_num) (kref_wt_rho hρ)⟩
    · have := kref_rho_le hρ a ha
      simp [length_krefDig]; omega
    · unfold krefRhos at hρ
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hρ
      rw [length_krefPowList, kref_dot_rho x ⟨i, List.mem_range.mp hi⟩ ⟨z, hz⟩]
      exact ((krefIdx_lt _).le.trans N_le_krefX).trans X_le_Z
  · refine kref_le_Z (c := 10) (a := 2) (by norm_num) (by norm_num) ?_
    have := kref_wt_dig_snoc x hz.le
    have := kref_two_X_le_sq (n := n) (k := k)
    have := @krefX_two n k
    omega
  · rw [length_krefPowList]; exact k_le_krefX.trans X_le_Z

/-- **The update lists.** -/
theorem kref_upd {P : Program} {b codes : ℕ} (h : P.HasAt b (krefUpdFuns b codes))
    (hc : P.HasAt codes (krefCodesFuns codes)) (x : Fin k → Fin n) :
    FunDet P b (.list [.list [natList (krefPowList n k), natList (krefDig x),
        .list ((krefRhos k).map natList)], natList (List.range n)])
      (.list ((krefUpd x).map natList)) (krefUpdK * (krefZ n k + 1) ^ 7) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have hf : P.funs[b + 3]? = some (krefUpdF codes) := by
    simpa [krefUpdFuns, mapFuns, loopFuns] using h.right.single
  set Z := krefZ n k with hZ
  have hX := @krefX_two n k
  have hwpw := kref_le_Z (n := n) (k := k) (c := 7) (a := 2) (by norm_num) (by norm_num) kref_wt_pw
  have hwD := kref_le_Z (n := n) (k := k) (c := 7) (a := 2) (by norm_num) (by norm_num)
    (kref_wt_dig x)
  have hwR := kref_le_Z (n := n) (k := k) (c := 30) (a := 3) (by norm_num) (by norm_num)
    (kref_wt_rhos (n := n))
  obtain ⟨hX2, hX12, hX23, hX34, hZ4⟩ := kref_X4 (n := n) (k := k)
  have hwpw' := kref_wt_pw (n := n) (k := k)
  have hwD' := kref_wt_dig x
  have hwR' := kref_wt_rhos (n := n) (k := k)
  have hwc : (Val.list [natList (krefPowList n k), natList (krefDig x),
      .list ((krefRhos k).map natList)]).wt ≤ Z := by
    have := wt_list3_le (natList (krefPowList n k)) (natList (krefDig x))
      (.list ((krefRhos k).map natList))
    omega
  have hnX := @n_le_krefX n k
  have hrn : (natList (List.range n)).wt ≤ Z := by
    have := kref_wt_range (n := n) (k := k) (m := n) (by omega); omega
  have hbody : ∀ z ∈ List.range n, FunDet P (b + 3)
      (.list [.list [natList (krefPowList n k), natList (krefDig x),
        .list ((krefRhos k).map natList)], .nat z])
      (natList ((krefRhos k).map fun ρ => krefDot (krefPowList n k) (krefDig x ++ [z]) ρ k))
      (krefUpdBodyK * (Z + 1) ^ 5) := by
    intro z hz
    rw [List.mem_range] at hz
    have hcod := kref_codes hc (kref_codesOK_rho x hz)
    rw [length_krefPowList, ← hZ] at hcod
    have e : natList (krefDig x ++ [z]) = .list ((krefDig x).map Val.nat ++ [.nat z]) := by
      simp [natList]
    rw [e] at hcod
    have hDz := kref_wt_dig_snoc x hz.le
    rw [e] at hDz
    have hWA : (Val.list [.list [natList (krefPowList n k), natList (krefDig x),
        .list ((krefRhos k).map natList)], .nat z]).wt ≤ 2 * Z + 2 * n + 10 := by
      have := wt_list2_le (.list [natList (krefPowList n k), natList (krefDig x),
        .list ((krefRhos k).map natList)]) (.nat z)
      have := wt_nat_le z
      omega
    set A : List Val := [.list [natList (krefPowList n k), natList (krefDig x),
        .list ((krefRhos k).map natList)], .nat z] with hA
    have dpw : Det P [.list A] (.get (arg 0) (.nat 0)) (natList (krefPowList n k))
        (3 * (Val.list A).wt + 0 + 0 + 9) := Det.arg2 rfl rfl
    have dD : Det P [.list A] (.get (arg 0) (.nat 1)) (.list ((krefDig x).map Val.nat))
        (3 * (Val.list A).wt + 0 + 1 + 9) := Det.arg2 rfl rfl
    have dz : Det P [.list A] (arg 1) (.nat z) (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
    have dR : Det P [.list A] (.get (arg 0) (.nat 2)) (.list ((krefRhos k).map natList))
        (3 * (Val.list A).wt + 0 + 2 + 9) := Det.arg2 rfl rfl
    have dargs := Det.mk2 (Det.mk2 dpw (Det.snoc dD dz)) dR
    refine FunDet.intro hf ((Det.call dargs hcod).mono ?_)
    have hw := FunDet.wt_lt hcod
    have h1 := wt_list2_le (natList (krefPowList n k))
      (.list ((krefDig x).map Val.nat ++ [.nat z]))
    have h2 := wt_list2_le (.list [natList (krefPowList n k),
      .list ((krefDig x).map Val.nat ++ [.nat z])]) (.list ((krefRhos k).map natList))
    have hT : Z + 1 ≤ (Z + 1) ^ 5 := kref_le_pow (by norm_num)
    unfold krefUpdBodyK
    rw [Nat.add_mul, Nat.mul_assoc 2]
    omega
  have hm := kref_mapL hmap (l := List.range n) (enc := Val.nat)
    (F := fun z => natList ((krefRhos k).map fun ρ =>
      krefDot (krefPowList n k) (krefDig x ++ [z]) ρ k)) (Y := Z) (A := 2) (by norm_num)
    (fun a _ a' _ haa => by cases haa; rfl) hbody (by omega) (by rw [natList_wt_eq]; omega)
  have e : List.map (fun z => natList ((krefRhos k).map fun ρ =>
      krefDot (krefPowList n k) (krefDig x ++ [z]) ρ k)) (List.range n) =
      (krefUpd x).map natList := by
    rw [kref_range_map]
    unfold krefUpd
    rw [List.map_map]
    apply List.map_congr_left
    intro z _
    simp only [Function.comp_apply, krefRhos, List.map_map]
    congr 1
    rw [kref_range_map]
    apply List.map_congr_left
    intro i _
    exact kref_dot_rho x i z
  rw [e] at hm
  exact hm

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited

variable {n k : ℕ}

/-! ### The table entry of one tuple -/

/-- The list of all `τ`, as digit lists. -/
def krefTausV (k : ℕ) : Val := .list (((krefTups k k).map krefDig).map natList)

/-- The context of the table: `[pw, n, taus, rhos, range n]`. -/
def krefNbCtx (n k : ℕ) : Val :=
  .list [natList (krefPowList n k), .nat n, krefTausV k, .list ((krefRhos k).map natList),
    natList (List.range n)]

/-- On `[ctx, j]`: the table entry of the tuple with index `j`. -/
def krefNbF (dig pat codes upd : ℕ) : Expr :=
  .letE (.call dig (mk2 (mk2 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (arg 1)))
    (mk4 (arg 1) (.call pat (mk2 (.var 1) (.var 1)))
      (.call codes (mk2 (mk2 (.get (arg 0) (.nat 0)) (.snoc (.var 1) (.nat 0)))
        (.get (arg 0) (.nat 2))))
      (.call upd (mk2 (mk3 (.get (arg 0) (.nat 0)) (.var 1) (.get (arg 0) (.nat 3)))
        (.get (arg 0) (.nat 4)))))

def krefNbK : ℕ := 30 * (krefDigK + krefPatK + krefCodesK + krefUpdK) + 1000

/-- Where the modules used by the table sit. -/
structure KrefNbAt (P : Program) (dig pat codes upd : ℕ) : Prop where
  hdig : P.HasAt dig (krefDigFuns dig)
  hpat : P.HasAt pat (krefPatFuns pat)
  hcodes : P.HasAt codes (krefCodesFuns codes)
  hupd : P.HasAt upd (krefUpdFuns upd codes)

theorem kref_wt_nbCtx : (krefNbCtx n k).wt ≤ 250 * krefX n k ^ 4 := by
  obtain ⟨hX2, hX12, hX23, hX34, -⟩ := kref_X4 (n := n) (k := k)
  have h1 := kref_wt_pw (n := n) (k := k)
  have h2 := kref_wt_taus (n := n) (k := k)
  have h3 := kref_wt_rhos (n := n) (k := k)
  have h4 := kref_wt_range (n := n) (k := k) (m := n) (by have := @n_le_krefX n k; omega)
  have h5 := wt_nat_le n
  have h6 := @n_le_krefX n k
  have e : krefTausV k = .list ((krefTups k k).map fun τ => natList (krefDig τ)) := by
    simp [krefTausV, List.map_map, Function.comp_def]
  have h7 := wt_list_le [natList (krefPowList n k), .nat n, krefTausV k,
    .list ((krefRhos k).map natList), natList (List.range n)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil] at h7
  unfold krefNbCtx
  rw [e] at h7 ⊢
  omega

theorem kref_codesOK_tau (x : Fin k → Fin n) :
    KrefCodesOK (krefZ n k) (krefPowList n k) (krefDig x ++ [0]) ((krefTups k k).map krefDig) := by
  have hX2 := kref_X_le_sq (n := n) (k := k)
  refine ⟨fun a ha => (kref_pw_le a ha).trans X_le_Z, fun a ha => ?_, fun ρ hρ => ?_,
    kref_le_Z (c := 7) (a := 2) (by norm_num) (by norm_num) kref_wt_pw, ?_, ?_, ?_⟩
  · rcases List.mem_append.mp ha with ha | ha
    · exact ((kref_dig_le x a ha).le.trans n_le_krefX).trans X_le_Z
    · rw [List.mem_singleton.mp ha]; exact Nat.zero_le _
  · obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hρ
    refine ⟨by rw [length_krefPowList, length_krefDig], fun a ha => ?_, ?_,
      kref_le_Z (c := 7) (a := 2) (by norm_num) (by norm_num) (kref_wt_dig_tau τ)⟩
    · have := kref_dig_le τ a ha
      simp [length_krefDig]; omega
    · rw [length_krefPowList, kref_dot_tau]
      exact ((krefIdx_lt _).le.trans N_le_krefX).trans X_le_Z
  · refine kref_le_Z (c := 10) (a := 2) (by norm_num) (by norm_num) ?_
    have := kref_wt_dig_snoc x (z := 0) (Nat.zero_le _)
    have := kref_two_X_le_sq (n := n) (k := k)
    have := @krefX_two n k
    omega
  · refine kref_le_Z (c := 30) (a := 3) (by norm_num) (by norm_num) ?_
    have := kref_wt_taus (n := n) (k := k)
    simpa [List.map_map, Function.comp_def] using this
  · rw [length_krefPowList]; exact k_le_krefX.trans X_le_Z

/-- **The table entry of one tuple.** -/
theorem kref_nbF {P : Program} {f dig pat codes upd : ℕ}
    (hf : P.funs[f]? = some (krefNbF dig pat codes upd)) (hat : KrefNbAt P dig pat codes upd)
    (x : Fin k → Fin n) :
    FunDet P f (.list [krefNbCtx n k, .nat (krefIdx x)]) (krefNbVal x)
      (krefNbK * (krefZ n k + 1) ^ 7) := by
  obtain ⟨hX2, hX12, hX23, hX34, hZ4⟩ := kref_X4 (n := n) (k := k)
  have hjN := krefIdx_lt x
  have hNX := @N_le_krefX n k
  have hnX := @n_le_krefX n k
  have hkX := @k_le_krefX n k
  have hwpw := kref_wt_pw (n := n) (k := k)
  have hwD := kref_wt_dig x
  have hwc := kref_wt_nbCtx (n := n) (k := k)
  -- the four calls
  have hdig := kref_dig hat.hdig (pw := krefPowList n k) (base := n) (x := krefIdx x)
    (Z := krefZ n k) (fun p hp => (kref_pw_le p hp).trans X_le_Z) (hnX.trans X_le_Z)
    (by omega) (by omega)
  have ed : (krefPowList n k).map (fun p => krefIdx x / p % n) = krefDig x := by
    have := kref_digits_eq (n := n) (k := k) (finFunctionFinEquiv x)
    simpa [krefIdx] using this
  rw [ed] at hdig
  have hpat := kref_pat hat.hpat (D := krefDig x) (Z := krefZ n k)
    (fun a ha => ((kref_dig_le x a ha).le.trans hnX).trans X_le_Z)
    (by rw [length_krefDig]; omega) (by omega)
  have hcod := kref_codes hat.hcodes (kref_codesOK_tau x)
  have ecod : ((krefTups k k).map krefDig).map
      (fun ρ => krefDot (krefPowList n k) (krefDig x ++ [0]) ρ (krefPowList n k).length) =
      krefTidx x := by
    unfold krefTidx
    rw [List.map_map]
    apply List.map_congr_left
    intro τ _
    simp only [Function.comp_apply, length_krefPowList]
    exact kref_dot_tau x τ 0
  rw [ecod] at hcod
  have esn : natList (krefDig x ++ [0]) = .list ((krefDig x).map Val.nat ++ [.nat 0]) := by
    simp [natList]
  rw [esn] at hcod
  have hupd := kref_upd hat.hupd hat.hcodes x
  -- reading the arguments
  have hWA : (Val.list [krefNbCtx n k, .nat (krefIdx x)]).wt ≤ 520 * krefX n k ^ 4 := by
    have := wt_list2_le (krefNbCtx n k) (.nat (krefIdx x))
    have := wt_nat_le (krefIdx x)
    omega
  set A : List Val := [krefNbCtx n k, .nat (krefIdx x)] with hA
  have dpw : Det P [.list A] (.get (arg 0) (.nat 0)) (natList (krefPowList n k))
      (3 * (Val.list A).wt + 0 + 0 + 9) := Det.arg2 rfl rfl
  have dn : Det P [.list A] (.get (arg 0) (.nat 1)) (.nat n)
      (3 * (Val.list A).wt + 0 + 1 + 9) := Det.arg2 rfl rfl
  have dj : Det P [.list A] (arg 1) (.nat (krefIdx x)) (2 * (Val.list A).wt + 1 + 5) :=
    Det.arg' rfl
  have d1 := Det.call (Det.mk2 (Det.mk2 dpw dn) dj) hdig
  have e1 : (List.map Val.nat (krefDig x)) = (krefDig x).map Val.nat := rfl
  have q1 : Det P [.list A, natList (krefDig x)] (arg 1) (.nat (krefIdx x))
      (2 * (Val.list A).wt + 1 + 5) := Det.arg' rfl
  have vD : Det P [.list A, natList (krefDig x)] (.var 1) (natList (krefDig x))
      ((natList (krefDig x)).wt + 1) := Det.var' rfl
  have vD' : Det P [.list A, natList (krefDig x)] (.var 1) (.list ((krefDig x).map Val.nat))
      ((natList (krefDig x)).wt + 1) := Det.var' rfl
  have q2 := Det.call (Det.mk2 vD vD) hpat
  have epw : Det P [.list A, natList (krefDig x)] (.get (arg 0) (.nat 0))
      (natList (krefPowList n k)) (3 * (Val.list A).wt + 0 + 0 + 9) := Det.arg2 rfl rfl
  have etau : Det P [.list A, natList (krefDig x)] (.get (arg 0) (.nat 2))
      (.list (((krefTups k k).map krefDig).map natList)) (3 * (Val.list A).wt + 0 + 2 + 9) :=
    Det.arg2 rfl rfl
  have erho : Det P [.list A, natList (krefDig x)] (.get (arg 0) (.nat 3))
      (.list ((krefRhos k).map natList)) (3 * (Val.list A).wt + 0 + 3 + 9) := Det.arg2 rfl rfl
  have ern : Det P [.list A, natList (krefDig x)] (.get (arg 0) (.nat 4))
      (natList (List.range n)) (3 * (Val.list A).wt + 0 + 4 + 9) := Det.arg2 rfl rfl
  have q3 := Det.call (Det.mk2 (Det.mk2 epw (Det.snoc vD' (Det.nat 0))) etau) hcod
  have q4 := Det.call (Det.mk2 (Det.mk3 epw vD erho) ern) hupd
  have body := Det.mk4 q1 q2 q3 q4
  have hall := Det.letE d1 body
  refine FunDet.intro hf (hall.mono ?_)
  -- weights of the results
  have w1 := FunDet.wt_lt hdig
  have w2 := FunDet.wt_lt hpat
  have w3 := FunDet.wt_lt hcod
  have w4 := FunDet.wt_lt hupd
  have wn := wt_nat_le (krefIdx x)
  have wl4 := wt_list4_le (.nat (krefIdx x))
    (natList ((krefDig x).map fun a => (krefDig x).findIdx fun y => decide (y = a)))
    (natList (krefTidx x)) (.list ((krefUpd x).map natList))
  have a1 := wt_list2_le (.list [natList (krefPowList n k), .nat n]) (.nat (krefIdx x))
  have a2 := wt_list2_le (natList (krefPowList n k)) (.nat n)
  have a3 := wt_list2_le (natList (krefDig x)) (natList (krefDig x))
  have a4 := wt_list2_le (.list [natList (krefPowList n k),
    .list ((krefDig x).map Val.nat ++ [.nat 0])]) (.list (((krefTups k k).map krefDig).map natList))
  have a5 := wt_list2_le (natList (krefPowList n k)) (.list ((krefDig x).map Val.nat ++ [.nat 0]))
  have a6 := wt_list_snoc_le ((krefDig x).map Val.nat) (.nat 0)
  have a7 := wt_list2_le (.list [natList (krefPowList n k), natList (krefDig x),
    .list ((krefRhos k).map natList)]) (natList (List.range n))
  have a8 := wt_list3_le (natList (krefPowList n k)) (natList (krefDig x))
    (.list ((krefRhos k).map natList))
  have a9 := kref_wt_taus (n := n) (k := k)
  have a10 := kref_wt_rhos (n := n) (k := k)
  have a11 := kref_wt_range (n := n) (k := k) (m := n) (by omega)
  have a12 := wt_nat_le n
  have a13 := wt_nat_le 0
  have etaus : (Val.list (((krefTups k k).map krefDig).map natList)) =
      .list ((krefTups k k).map fun τ => natList (krefDig τ)) := by
    simp [List.map_map, Function.comp_def]
  rw [← etaus] at a9
  have e2 : (Val.list ((krefDig x).map Val.nat)).wt = (natList (krefDig x)).wt := rfl
  have p3 : krefDigK * (krefZ n k + 1) ^ 3 ≤ krefDigK * (krefZ n k + 1) ^ 7 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have p5 : krefPatK * (krefZ n k + 1) ^ 5 ≤ krefPatK * (krefZ n k + 1) ^ 7 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have p5' : krefCodesK * (krefZ n k + 1) ^ 5 ≤ krefCodesK * (krefZ n k + 1) ^ 7 :=
    Nat.mul_le_mul_left _ (kref_pow_mono (by norm_num))
  have hT : krefZ n k + 1 ≤ (krefZ n k + 1) ^ 7 := kref_le_pow (by norm_num)
  have hW : (Val.list A).wt ≤ krefZ n k := by omega
  unfold krefNbK
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc 30]
  omega

/-! ### The whole table -/

/-- The table module: a map over the indices with body `krefNbF` (four functions). -/
def krefNbsFuns (b dig pat codes upd : ℕ) : List Expr :=
  mapFuns b (b + 3) ++ [krefNbF dig pat codes upd]

def krefNbsK : ℕ := mapK * (3 * krefNbK + 11) * 2 ^ 9

/-- The table: the entries of all tuples, in index order. -/
def krefNbs (n k : ℕ) : Val := .list ((krefTups n k).map krefNbVal)

/-- **The table.** -/
theorem kref_nbs {P : Program} {b dig pat codes upd : ℕ}
    (h : P.HasAt b (krefNbsFuns b dig pat codes upd)) (hat : KrefNbAt P dig pat codes upd) :
    FunDet P b (.list [krefNbCtx n k, natList (List.range (n ^ k))]) (krefNbs n k)
      (krefNbsK * (krefZ n k + 1) ^ 9) := by
  have hmap : P.HasAt b (mapFuns b (b + 3)) := h.left
  have hf : P.funs[b + 3]? = some (krefNbF dig pat codes upd) := by
    simpa [krefNbsFuns, mapFuns, loopFuns] using h.right.single
  obtain ⟨hX2, hX12, hX23, hX34, hZ4⟩ := kref_X4 (n := n) (k := k)
  have hNX := @N_le_krefX n k
  let F : ℕ → Val := fun j => if hj : j < n ^ k then krefNbVal (finFunctionFinEquiv.symm ⟨j, hj⟩)
    else .nat 0
  have hbody : ∀ j ∈ List.range (n ^ k), FunDet P (b + 3) (.list [krefNbCtx n k, .nat j]) (F j)
      (krefNbK * (krefZ n k + 1) ^ 7) := by
    intro j hj
    rw [List.mem_range] at hj
    have := kref_nbF hf hat (finFunctionFinEquiv.symm ⟨j, hj⟩)
    simp only [krefIdx, Equiv.apply_symm_apply] at this
    simpa [F, hj] using this
  have hm := kref_mapL hmap (l := List.range (n ^ k)) (enc := Val.nat) (F := F)
    (Y := krefZ n k) (A := 1) (by norm_num) (fun a _ a' _ haa => by cases haa; rfl) hbody
    (by have := kref_wt_nbCtx (n := n) (k := k); omega)
    (by
      rw [natList_wt_eq]
      have := kref_wt_range (n := n) (k := k) (m := n ^ k) (by omega)
      omega)
  have e : (List.range (n ^ k)).map F = (krefTups n k).map krefNbVal := by
    rw [kref_range_map]
    unfold krefTups
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    simp [F, j.isLt]
  rw [e] at hm
  exact hm

end GI.Impl
