import Workspace.Impl.AggItemPartEven
import Workspace.Impl.AggItemOv

/-!
# The Case 1 item from orbit labels

The program of the Case 1 item gets orbit labels `labX`, `labY` of the certificate groups
`π(F_x) = X.grp` and `π(F_y) = Y.grp` (`orbits_spec`: the label of a point is the least point of
its orbit, `ItcLab`). From them it computes, with the mathematics of `AggItemPart*`:

* the generators `itcGens labX` of the stabilizer of the orbit partition of `X`
  (`itc_closure`): the transpositions `(lab x, x)` and the block swaps;
* an odd transposition `t = (lab a, a)` inside a block, for a point `a` that is not the least of
  its orbit (one exists in Case 1, since some orbit has two points);
* the Schreier generators `itpSch t (itcGens labX)` of the even stabilizer (`itc_gens_even`);
* the aligning permutation `itpAlign labX labY`, made even by `t` if it is odd (`itcSig`).

`it_c1_item` states what this gives for the model's `caseOneItem X Y`: its script returns no
piece and the overcosets `ovs`, and the program's list `os` (one overcoset if the numbers of
points in orbits of each size agree, none otherwise) stands for `ovs` entry by entry
(`asOvAt`), with generators of each group.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm Finset
open GI.Cited (gens)

variable {q : ℕ}

/-- **Orbit labels** of a list of generators, as `orbits_spec` returns them: two points have the
same label exactly when they are in one orbit, and the label is the least point of the orbit. -/
structure ItcLab (gs : List (Perm (Fin q))) (lab : Fin q → ℕ) : Prop where
  eq : ∀ x y, lab x = lab y ↔ y ∈ genOrbit gs x
  min : ∀ x, ∃ hx : lab x < q, (⟨lab x, hx⟩ : Fin q) ∈ genOrbit gs x ∧
    ∀ y ∈ genOrbit gs x, lab x ≤ y

/-- The center of the block of `x`: the point `lab x`. -/
def itcC (lab : Fin q → ℕ) (x : Fin q) : Fin q := if h : lab x < q then ⟨lab x, h⟩ else x

variable {gs : List (Perm (Fin q))} {lab : Fin q → ℕ}

theorem itcC_val (h : ItcLab gs lab) (x : Fin q) : (itcC lab x : ℕ) = lab x := by
  obtain ⟨hx, -⟩ := h.min x
  simp [itcC, hx]

theorem itcC_lab (h : ItcLab gs lab) (x : Fin q) : lab (itcC lab x) = lab x := by
  obtain ⟨hx, hmem, -⟩ := h.min x
  have e : itcC lab x = ⟨lab x, hx⟩ := by simp [itcC, hx]
  rw [e]
  exact ((h.eq x _).2 hmem).symm

theorem itcC_le (h : ItcLab gs lab) {x y : Fin q} (hxy : lab x = lab y) : itcC lab x ≤ y := by
  obtain ⟨hx, -, hle⟩ := h.min x
  rw [Fin.le_def, itcC_val h]
  exact hle y ((h.eq x y).1 hxy)

/-! ### The generators -/

open Classical in
/-- The block swap of the blocks of `x` and `y` if they have the same size, else `1`. -/
noncomputable def itcGen (lab : Fin q → ℕ) (x y : Fin q) : Perm (Fin q) :=
  if itpSz lab x = itpSz lab y then itpBs lab (itcC lab x) (itcC lab y) else 1

/-- **The generators of the stabilizer**: the transpositions with the centers, then the block
swaps of all pairs of points. -/
noncomputable def itcGens (lab : Fin q → ℕ) : List (Perm (Fin q)) :=
  (List.finRange q).map (fun x => Equiv.swap (itcC lab x) x) ++
    (List.finRange q).flatMap fun x => (List.finRange q).map (itcGen lab x)

/-- **The generators generate the stabilizer of the partition.** -/
theorem itc_closure (h : ItcLab gs lab) :
    gens (itcGens lab) = MulAction.stabilizer (Perm (Fin q)) (itpPart lab) := by
  classical
  have hc1 := itcC_lab h
  have hc2 : ∀ x y, lab x = lab y → itcC lab x ≤ y := fun x y => itcC_le h
  refine itp_closure_eq hc1 hc2 (fun g hg => ?_) (fun x => ?_) (fun x y hs _ => ?_)
  · simp only [Set.mem_setOf_eq, itcGens, List.mem_append, List.mem_map, List.mem_flatMap,
      List.mem_finRange, true_and] at hg
    rcases hg with ⟨x, rfl⟩ | ⟨x, y, rfl⟩
    · exact itp_swap_mem_stab (hc1 x)
    · unfold itcGen
      split_ifs with hs
      · exact itpBs_mem_stab ⟨itp_c_rk hc1 hc2 x, itp_c_rk hc1 hc2 y, by
          rw [itpSz_congr (hc1 x), itpSz_congr (hc1 y), hs]⟩
      · exact Subgroup.one_mem _
  · simp [itcGens]
  · simp only [Set.mem_setOf_eq, itcGens, List.mem_append, List.mem_map, List.mem_flatMap,
      List.mem_finRange, true_and]
    exact Or.inr ⟨x, y, by rw [itcGen, if_pos hs]⟩

/-- The transposition of a point with the center of its block. -/
def itcT (lab : Fin q → ℕ) (a : Fin q) : Perm (Fin q) := Equiv.swap (itcC lab a) a

theorem itcT_ne (h : ItcLab gs lab) {a : Fin q} (ha : lab a ≠ a) : itcC lab a ≠ a := by
  intro e
  apply ha
  rw [← itcC_val h, e]

theorem itcT_mem_stab (h : ItcLab gs lab) (a : Fin q) :
    itcT lab a ∈ MulAction.stabilizer (Perm (Fin q)) (itpPart lab) :=
  itp_swap_mem_stab (itcC_lab h a)

/-- **The Schreier generators generate the even stabilizer.** -/
theorem itc_gens_even (h : ItcLab gs lab) {a : Fin q} (ha : lab a ≠ a) :
    gens (itpSch (itcT lab a) (itcGens lab)) =
      MulAction.stabilizer (Perm (Fin q)) (itpPart lab) ⊓ alternatingGroup (Fin q) := by
  have hcl := itc_closure h
  unfold gens at hcl ⊢
  rw [itp_schreier, hcl]
  · rw [hcl]; exact itcT_mem_stab h a
  · exact Equiv.swap_mul_self _ _
  · exact Perm.sign_swap (itcT_ne h ha)

/-! ### The aligning permutation -/

open Classical in
/-- **The even aligning permutation**: the alignment, times `t` if it is odd. -/
noncomputable def itcSig (labX labY : Fin q → ℕ) (a : Fin q) : Perm (Fin q) :=
  if sign (itpAlign labX labY) = 1 then itpAlign labX labY
  else itpAlign labX labY * itcT labX a

theorem itcSig_smul {gx : List (Perm (Fin q))} {labX labY : Fin q → ℕ} (h : ItcLab gx labX)
    (hc : ∀ s, itpCnt labX s = itpCnt labY s) (a : Fin q) :
    itcSig labX labY a • itpPart labX = itpPart labY := by
  unfold itcSig
  split_ifs
  · exact itpAlign_smul hc
  · rw [mul_smul, (MulAction.mem_stabilizer_iff).1 (itcT_mem_stab h a), itpAlign_smul hc]

theorem itcSig_sign {gx : List (Perm (Fin q))} {labX labY : Fin q → ℕ} (h : ItcLab gx labX)
    {a : Fin q} (ha : labX a ≠ a) : sign (itcSig labX labY a) = 1 := by
  unfold itcSig
  split_ifs with hs
  · exact hs
  · rw [Perm.sign_mul, (itp_sign_cases _).resolve_left hs, itcT, Perm.sign_swap (itcT_ne h ha)]
    decide

/-- **In Case 1 some point is not the least of its orbit**: the support has at least `q/2 > 0`
points, so some orbit has two points. -/
theorem itc_exists_a {gx : List (Perm (Fin q))} {H : Subgroup (Perm (Fin q))}
    (hH : gens gx = H) (h : ItcLab gx lab) (hq : 0 < q) (hcase : aggCase H = .one) :
    ∃ a : Fin q, lab a ≠ a := by
  classical
  have hsupp : q ≤ 2 * (suppSet H).card := by
    unfold aggCase at hcase
    split_ifs at hcase with h1 h2 h3
    exact h3
  obtain ⟨b, hb⟩ : (suppSet H).Nonempty := Finset.card_pos.1 (by omega)
  rw [mem_suppSet] at hb
  have hblk : lorb H b = itpBlk lab b := by
    have := itpPart_eq hH h.eq
    exact congrArg (fun z : ColPart (Fin q) => z.blk b) this
  rw [hblk] at hb
  have h2 : 1 < (itpBlk lab b).card := by
    have : 0 < (itpBlk lab b).card := Finset.card_pos.2 ⟨b, itp_mem_blk.2 rfl⟩
    omega
  obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_ne h2 (itcC lab b)
  refine ⟨y, fun e => hyc ?_⟩
  rw [itp_mem_blk] at hy
  apply Fin.ext
  rw [itcC_val h, ← hy, e]

/-! ### The item -/

open Classical in
/-- **The program's overcosets of the Case 1 item**: one overcoset `(σ, E₀, ms)` if the numbers
of points in orbits of each size agree, else none. -/
noncomputable def itcOs {gx : List (Perm (Fin q))} {labX : Fin q → ℕ}
    (h : ItcLab gx labX) (labY : Fin q → ℕ) {a : Fin q} (ha : labX a ≠ a)
    (E₀ : Subgroup (alternatingGroup (Fin q))) : List (LcOver q) :=
  if ∀ s, itpCnt labX s = itpCnt labY s then
    [(⟨itcSig labX labY a, itcSig_sign h ha⟩, E₀, itpSch (itcT labX a) (itcGens labX))]
  else []

variable {Ω C : Type} {P : Params} {S : State Ω C}

/-- **The Case 1 item, as the program computes it.** For orbit labels of generators of `X.grp`
and `Y.grp` and a point `a` that is not the least of its orbit, the script of `caseOneItem X Y`
returns no piece and overcosets `ovs`, the program's list `itcOs` stands for `ovs` entry by entry,
and each of its groups is generated by its list. -/
theorem it_c1_item (L : GiantLabels S) {ℓ : ℕ} (X Y : GI.Algorithm.Canon L.q P.κ ℓ)
    {gx gy : List (Perm (Fin L.q))} {labX labY : Fin L.q → ℕ}
    (hX : gens gx = X.grp) (hY : gens gy = Y.grp) (hlX : ItcLab gx labX) (hlY : ItcLab gy labY)
    {a : Fin L.q} (ha : labX a ≠ a) :
    ∃ ovs, (caseOneItem (P := P) (S := S) X Y).script = Script.done ⟨[], ovs⟩ ∧
      List.Forall₂ (asOvAt L)
        (itcOs hlX labY ha (evenStab (q := L.q) (labelOrbitPart X.grp))) ovs ∧
      ∀ o ∈ itcOs hlX labY ha (evenStab (q := L.q) (labelOrbitPart X.grp)),
        gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
  classical
  have hPX : labelOrbitPart X.grp = itpPart labX := itpPart_eq hX hlX.eq
  have hPY : labelOrbitPart Y.grp = itpPart labY := itpPart_eq hY hlY.eq
  have hgens : ∀ o ∈ itcOs hlX labY ha (evenStab (q := L.q) (labelOrbitPart X.grp)),
      gens o.2.2 = o.2.1.map (alternatingGroup (Fin L.q)).subtype := by
    intro o ho
    unfold itcOs at ho
    split_ifs at ho
    · rw [List.mem_singleton] at ho
      subst ho
      rw [itp_evenStab_map, hPX]
      exact itc_gens_even hlX ha
    · simp at ho
  unfold caseOneItem invItem
  split_ifs with hex
  · -- an even aligner exists: the counts agree, and the program's aligner stands for it
    have hc : ∀ s, itpCnt labX s = itpCnt labY s := by
      obtain ⟨σ, hσ⟩ := hex
      change (σ : Perm (Fin L.q)) • labelOrbitPart X.grp = labelOrbitPart Y.grp at hσ
      rw [hPX, hPY] at hσ
      exact (itp_exists_smul_iff labY).1 ⟨_, hσ⟩
    refine ⟨_, rfl, ?_, hgens⟩
    simp only [itcOs, if_pos hc]
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    refine it_invItem_ovAt L (fun Z : GI.Algorithm.Canon L.q P.κ ℓ => labelOrbitPart Z.grp) hex
      (σ' := ⟨itcSig labX labY a, itcSig_sign hlX ha⟩) ?_ _
    show itcSig labX labY a • labelOrbitPart X.grp = labelOrbitPart Y.grp
    rw [hPX, hPY]
    exact itcSig_smul hlX hc a
  · -- no even aligner: the counts differ, since an odd aligner times `t` would be one
    have hc : ¬ ∀ s, itpCnt labX s = itpCnt labY s := by
      intro hc
      exact hex ⟨⟨itcSig labX labY a, itcSig_sign hlX ha⟩, by
        show itcSig labX labY a • labelOrbitPart X.grp = labelOrbitPart Y.grp
        rw [hPX, hPY]; exact itcSig_smul hlX hc a⟩
    refine ⟨[], rfl, ?_, hgens⟩
    simp only [itcOs, if_neg hc]
    exact List.Forall₂.nil

end GI.Impl
