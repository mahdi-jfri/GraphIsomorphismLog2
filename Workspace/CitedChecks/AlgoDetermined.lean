import Workspace.CitedChecks.AlgoTotality

/-!
# The encodings determine the instances

A program reads only the encoding `enc x` of an instance `x`. If two instances had the same
encoding but no common correct output, no program could solve the task, and the axiom
`∃ p, PolyTimeAt t p` would be false. This file checks, for the tasks that the implementation
uses, that the encoding determines the instance (up to its proof fields, which are equal by
proof irrelevance). Then the correct outputs of the two instances are the same. Nothing here is
trusted.
-/

namespace GI.CitedChecks

open GI.Cited Equiv

/-- `Val.list` is injective. -/
theorem detm_list_inj {a b : List Val} (h : Val.list a = Val.list b) : a = b := by
  injection h

/-- `Val.nat` is injective. -/
theorem detm_nat_inj {a b : ℕ} (h : Val.nat a = Val.nat b) : a = b := by
  injection h

/-- A permutation is determined by its encoding. -/
theorem detm_encPerm_inj {n : ℕ} {σ τ : Perm (Fin n)} (h : encPerm σ = encPerm τ) : σ = τ := by
  have h1 := List.map_inj_left.mp (detm_list_inj h)
  ext i
  exact detm_nat_inj (h1 i (List.mem_finRange i))

/-- A list of permutations is determined by its encoding. -/
theorem detm_encPerms_list_inj {n : ℕ} {gs hs : List (Perm (Fin n))}
    (h : gs.map encPerm = hs.map encPerm) : gs = hs :=
  List.map_injective_iff.mpr (fun _ _ e => detm_encPerm_inj e) h

/-- A group value determines the degree. -/
theorem detm_encGroup_n {n n' : ℕ} {gs : List (Perm (Fin n))} {gs' : List (Perm (Fin n'))}
    (h : encGroup gs = encGroup gs') : n = n' := by
  simp only [encGroup, encPerms] at h
  have h1 := detm_list_inj h
  simp only [List.cons.injEq] at h1
  exact detm_nat_inj h1.1

/-- A group value of a fixed degree determines the generator list. -/
theorem detm_encGroup_inj {n : ℕ} {gs gs' : List (Perm (Fin n))}
    (h : encGroup gs = encGroup gs') : gs = gs' := by
  simp only [encGroup, encPerms] at h
  have h1 := detm_list_inj h
  simp only [List.cons.injEq] at h1
  have h2 := detm_encPerms_list_inj (detm_list_inj h1.2.1)
  simp only [List.cons.injEq] at h2
  exact h2.2

/-- A list of points is determined by its encoding. -/
theorem detm_encPts_inj {n : ℕ} {S S' : List (Fin n)} (h : encPts S = encPts S') : S = S' := by
  have h1 := List.map_injective_iff.mpr (fun _ _ e => detm_nat_inj e) (detm_list_inj h)
  have e : ∀ T : List (Fin n), (do let a ← T; pure (Fin.val a) : List ℕ) = T.map Fin.val := by
    intro T; induction T with
    | nil => rfl
    | cons a T ih => simpa using ih
  have h2 : S.map Fin.val = S'.map Fin.val := by
    rw [← e, ← e]; exact h1
  exact List.map_injective_iff.mpr Fin.val_injective h2

/-- **`GroupOrderTask`, `OrbitsTask`** (instances `GroupInst`). -/
theorem detm_groupInst (I J : GroupInst) (h : encGroup I.gs = encGroup J.gs) : I = J := by
  obtain ⟨n, gs⟩ := I
  obtain ⟨n', gs'⟩ := J
  obtain rfl := detm_encGroup_n h
  obtain rfl := detm_encGroup_inj h
  rfl

/-- **`MembershipTask`**. -/
theorem detm_memberInst (I J : MemberInst)
    (h : Val.list [encGroup I.gs, encPerm I.x] = Val.list [encGroup J.gs, encPerm J.x]) :
    I = J := by
  obtain ⟨n, gs, x⟩ := I
  obtain ⟨n', gs', x'⟩ := J
  simp only [List.cons.injEq, Val.list.injEq, and_true] at h
  obtain rfl := detm_encGroup_n h.1
  obtain rfl := detm_encGroup_inj h.1
  obtain rfl := detm_encPerm_inj h.2
  rfl

/-- **`PointwiseStabTask`**. -/
theorem detm_pointsInst (I J : PointsInst)
    (h : Val.list [encGroup I.gs, encPts I.S] = Val.list [encGroup J.gs, encPts J.S]) :
    I = J := by
  obtain ⟨n, gs, S⟩ := I
  obtain ⟨n', gs', S'⟩ := J
  simp only [List.cons.injEq, Val.list.injEq, and_true] at h
  obtain rfl := detm_encGroup_n h.1
  obtain rfl := detm_encGroup_inj h.1
  obtain rfl := detm_encPts_inj h.2
  rfl

/-- **`MinimalBlocksTask`**. -/
theorem detm_transitiveInst (I J : TransitiveInst) (h : encGroup I.gs = encGroup J.gs) :
    I = J := by
  obtain ⟨n, gs, _, _⟩ := I
  obtain ⟨n', gs', _, _⟩ := J
  obtain rfl := detm_encGroup_n h
  obtain rfl := detm_encGroup_inj h
  rfl

/-- **`CameronRecognitionTask`**. -/
theorem detm_primitiveInst (I J : PrimitiveInst) (h : encGroup I.gs = encGroup J.gs) :
    I = J := by
  obtain ⟨n, _, gs, _⟩ := I
  obtain ⟨n', _, gs', _⟩ := J
  obtain rfl := detm_encGroup_n h
  obtain rfl := detm_encGroup_inj h
  rfl

/-- **`NormalizedFactorTask`**. -/
theorem detm_factorInst (I J : FactorInst)
    (h : Val.list [encGroup I.gs, encGroup I.ns, encPerm I.x] =
      Val.list [encGroup J.gs, encGroup J.ns, encPerm J.x]) : I = J := by
  obtain ⟨n, gs, ns, _, x, _⟩ := I
  obtain ⟨n', gs', ns', _, x', _⟩ := J
  simp only [List.cons.injEq, Val.list.injEq, and_true] at h
  obtain rfl := detm_encGroup_n h.1
  obtain rfl := detm_encGroup_inj h.1
  obtain rfl := detm_encGroup_inj h.2.1
  obtain rfl := detm_encPerm_inj h.2.2
  rfl

/-- `sumToFin` is injective. -/
theorem detm_sumToFin_inj {n n' : ℕ} {g g' : Perm (Fin n ⊕ Fin n')}
    (h : sumToFin g = sumToFin g') : g = g' := by
  ext x : 1
  have := congrArg (fun f : Perm (Fin (n + n')) => f (finSumFinEquiv x)) h
  simpa [sumToFin] using this

/-- **`PreimageTask`**: the first entry gives `n`, the group of `M` gives `n'`, and then the
generator lists are determined. -/
theorem detm_preimageInst (I J : PreimageInst)
    (h : Val.list [.nat I.n, encGroup (I.ds.map sumToFin), encGroup I.ms] =
      Val.list [.nat J.n, encGroup (J.ds.map sumToFin), encGroup J.ms]) : I = J := by
  obtain ⟨n, n', ds, ms, _, _⟩ := I
  obtain ⟨m, m', es, ns, _, _⟩ := J
  simp only [List.cons.injEq, Val.list.injEq, and_true] at h
  obtain rfl := detm_nat_inj h.1
  obtain rfl := detm_encGroup_n h.2.2
  obtain rfl := detm_encGroup_inj h.2.2
  have h1 := detm_encGroup_inj h.2.1
  obtain rfl : ds = es :=
    List.map_injective_iff.mpr (fun _ _ e => detm_sumToFin_inj e) h1
  rfl

end GI.CitedChecks
