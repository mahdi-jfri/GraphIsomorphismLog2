import Workspace.Impl.GenCls

/-!
# The candidate of the exposure program

The exposure program (`Workspace/Impl/GenExpose.lean`) numbers the classes of a base partition
`B` on the domain (the fine end `f` of the prefix before the split interval, or the retained
columns when they are coarser than `f`), lets `G` act on the numbers, and calls `MinimalBlocks`
on that action. Its output `lab'` is a minimal block system of the numbers. Pulled back to the
points, it gives the partition `M` (`pull_cand`):

* `M` is a candidate above `f` (`IsCand`): invariant, coarser than `f`, not one class;
* no candidate is strictly coarser than `M` on the domain;
* `M` is coarser than `B`.

These are the hypotheses of `exists_primitiveQuotient_of_cand`. We also count classes with a
numbering (`Numbering.classCount_eq`) and test `UnivOn` with it (`Numbering.univOn_iff`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val gens IsMinimalBlocks InvariantLabeling encGroup encPerms encPerm)

variable {Ω C : Type} {k : ℕ}

namespace Cls

variable {e : Ω ≃ Fin k} {D : Set Ω} {R : Setoid Ω} {num : Fin k → ℕ} {d : ℕ}

/-- **A numbering counts the classes**: the domain meets `d` classes. -/
theorem Numbering.classCount_eq [Finite Ω] (h : Numbering e D R num d) : classCount R D = d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hD : D = ∅ := Set.eq_empty_of_forall_notMem fun v hv => by
      have := h.lt v hv; omega
    subst hD
    unfold classCount
    haveI : IsEmpty (Quotient (Setoid.comap (Subtype.val : (∅ : Set Ω) → Ω) R)) :=
      ⟨fun q => Quotient.inductionOn q fun x => x.2⟩
    exact Nat.card_of_isEmpty
  · unfold classCount
    let F : Quotient (Setoid.comap (Subtype.val : D → Ω) R) → Fin d :=
      Quotient.lift (fun x : D => h.toMap hd x) fun a b hab =>
        (h.toMap_eq_iff hd a.2 b.2).2 hab
    have hF : Function.Bijective F := by
      constructor
      · intro p q hpq
        induction p using Quotient.inductionOn
        induction q using Quotient.inductionOn
        exact Quotient.sound ((h.toMap_eq_iff hd (Subtype.prop _) (Subtype.prop _)).1 hpq)
      · intro t
        obtain ⟨v, hv, rfl⟩ := h.toMap_onto hd t
        exact ⟨Quotient.mk _ ⟨v, hv⟩, rfl⟩
    rw [Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **One class exactly when the number of classes is `1`**, on a nonempty domain. -/
theorem Numbering.univOn_iff (h : Numbering e D R num d) (hne : D.Nonempty) :
    UnivOn D R ↔ d = 1 := by
  obtain ⟨a, ha⟩ := hne
  have hd : 0 < d := by have := h.lt a ha; omega
  constructor
  · intro hu
    refine le_antisymm ?_ hd
    by_contra hlt
    obtain ⟨v, hv, hv1⟩ := h.onto 1 (by omega)
    obtain ⟨w, hw, hw0⟩ := h.onto 0 hd
    have := (h.eq_iff v hv w hw).2 (hu v hv w hw)
    omega
  · intro h1 v hv w hw
    refine (h.eq_iff v hv w hw).1 ?_
    have := h.lt v hv
    have := h.lt w hw
    omega

end Cls

/-! ### The pulled-back minimal block system -/

section Pull

variable {S : State Ω C} {e : Ω ≃ Fin k} {B : Setoid Ω} {num : Fin k → ℕ} {d : ℕ}

/-- **The pulled-back minimal block system is a coarsest candidate.** Let `num` number the
classes of `B` on the domain, `ρ` the action of `G` on the numbers, `lab'` a minimal block
system of `ρ(G)`, and `lab2` the labels `lab'` of the numbers. Then the kernel `M` of `lab2` is a
candidate above any `f` finer than `B`, no candidate is strictly coarser on the domain, and
`M` is coarser than `B` on the domain. -/
theorem pull_cand (h : Cls.Numbering e S.dom B num d) (hd : 0 < d)
    {ρ : S.G →* Perm (Fin d)}
    (hρ : ∀ g : S.G, ∀ v ∈ S.dom, ρ g (h.toMap hd v) = h.toMap hd ((g : Perm Ω) v))
    {lab' : Fin d → ℕ} (hmin : IsMinimalBlocks ρ.range lab') {lab2 : Fin k → ℕ}
    (h2 : ∀ v ∈ S.dom, lab2 (e v) = lab' (h.toMap hd v)) {f : Setoid Ω}
    (hfB : ∀ v ∈ S.dom, ∀ w ∈ S.dom, f.r v w → B.r v w) :
    IsCand S.G S.dom f (Setoid.ker fun v => lab2 (e v)) ∧
    (∀ M', IsCand S.G S.dom f M' →
      (∀ v ∈ S.dom, ∀ w ∈ S.dom, (Setoid.ker fun v => lab2 (e v)).r v w → M'.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, M'.r v w → (Setoid.ker fun v => lab2 (e v)).r v w) ∧
    (∀ v ∈ S.dom, ∀ w ∈ S.dom, B.r v w → (Setoid.ker fun v => lab2 (e v)).r v w) := by
  classical
  set M := Setoid.ker fun v => lab2 (e v) with hM
  have hMr : ∀ v ∈ S.dom, ∀ w ∈ S.dom, M.r v w ↔ lab' (h.toMap hd v) = lab' (h.toMap hd w) :=
    fun v hv w hw => by
      show lab2 (e v) = lab2 (e w) ↔ _
      rw [h2 v hv, h2 w hw]
  obtain ⟨hinvL, ⟨i, j, hij⟩, hmaxL⟩ := hmin
  have hBM : ∀ v ∈ S.dom, ∀ w ∈ S.dom, B.r v w → M.r v w := fun v hv w hw hvw => by
    rw [hMr v hv w hw, (h.toMap_eq_iff hd hv hw).2 hvw]
  have hgdom : ∀ g : S.G, ∀ v ∈ S.dom, (g : Perm Ω) v ∈ S.dom := fun g v hv =>
    (S.dom_inv g.1 g.2 v).2 hv
  have hcand : IsCand S.G S.dom f M := by
    refine ⟨fun g hg v hv w hw => ?_, fun v hv w hw hvw => hBM v hv w hw (hfB v hv w hw hvw),
      fun hu => ?_⟩
    · have hgv := hgdom ⟨g, hg⟩ v hv
      have hgw := hgdom ⟨g, hg⟩ w hw
      rw [hMr _ hgv _ hgw, hMr v hv w hw, ← hρ ⟨g, hg⟩ v hv, ← hρ ⟨g, hg⟩ w hw]
      exact hinvL _ ⟨⟨g, hg⟩, rfl⟩ _ _
    · obtain ⟨v, hv, rfl⟩ := h.toMap_onto hd i
      obtain ⟨w, hw, rfl⟩ := h.toMap_onto hd j
      exact hij ((hMr v hv w hw).1 (hu v hv w hw))
  refine ⟨hcand, fun M' hM' hMM' => ?_, hBM⟩
  -- A point of each number, and the labels of `M'` on the numbers.
  choose pt hpt hpt' using h.toMap_onto hd
  let lab'' : Fin d → ℕ := fun t => e (Quotient.mk M' (pt t)).out
  have hlab'' : ∀ s t, lab'' s = lab'' t ↔ M'.r (pt s) (pt t) := fun s t => by
    simp only [lab'']
    rw [Fin.val_inj, e.apply_eq_iff_eq, Quotient.out_inj, Quotient.eq]
  have hptB : ∀ v ∈ S.dom, M'.r v (pt (h.toMap hd v)) := fun v hv =>
    hMM' _ hv _ (hpt _) (hBM _ hv _ (hpt _) ((h.toMap_eq_iff hd hv (hpt _)).1 (hpt' _).symm))
  have hM'pt : ∀ v ∈ S.dom, ∀ w ∈ S.dom, M'.r v w ↔
      lab'' (h.toMap hd v) = lab'' (h.toMap hd w) := fun v hv w hw => by
    rw [hlab'']
    exact ⟨fun hvw => M'.trans (M'.symm (hptB v hv)) (M'.trans hvw (hptB w hw)),
      fun h' => M'.trans (hptB v hv) (M'.trans h' (M'.symm (hptB w hw)))⟩
  have hinv'' : InvariantLabeling ρ.range lab'' := by
    rintro _ ⟨g, rfl⟩ s t
    rw [← hpt' s, ← hpt' t, hρ g _ (hpt s), hρ g _ (hpt t),
      ← hM'pt _ (hgdom g _ (hpt s)) _ (hgdom g _ (hpt t)), ← hM'pt _ (hpt s) _ (hpt t)]
    exact hM'.inv g.1 g.2 _ (hpt s) _ (hpt t)
  have hfib : ∀ s t, lab' s = lab' t → lab'' s = lab'' t := fun s t hst => by
    rw [hlab'']
    refine hMM' _ (hpt s) _ (hpt t) ((hMr _ (hpt s) _ (hpt t)).2 ?_)
    rw [hpt' s, hpt' t]; exact hst
  intro v hv w hw hvw
  rcases hmaxL lab'' hinv'' hfib with hsame | hall
  · rw [hMr v hv w hw, ← hsame]
    exact (hM'pt v hv w hw).1 hvw
  · exact absurd (fun v hv w hw => (hM'pt v hv w hw).2 (hall _ _)) hM'.proper

end Pull

/-! ### The outputs of the program for a quotient numbered by the program -/

namespace Cls

variable {lab dm : Fin k → ℕ}

/-- Two points have the same key exactly when they have the same number. -/
theorem keyOf_eq_iff_numOf (hl : LabOK lab dm) (i j : Fin k) :
    keyOf lab dm i = keyOf lab dm j ↔
      numOf dm (keyOf lab dm) i = numOf dm (keyOf lab dm) j := by
  by_cases hi : dm i = 0 <;> by_cases hj : dm j = 0
  · simp [keyOf, numOf, hi, hj]
  · have h1 := numOf_lt hl hj
    have h2 := hl j hj
    rw [numOf_off hi]
    simp only [keyOf, hi, hj, if_true, if_false]
    omega
  · have h1 := numOf_lt hl hi
    have h2 := hl i hi
    rw [numOf_off hj]
    simp only [keyOf, hi, hj, if_true, if_false]
    omega
  · rw [numOf_eq_iff hl hi hj]
    simp [keyOf, hi, hj]

/-- **The representatives give the number relation.** -/
theorem reprVal_numOf (hl : LabOK lab dm) :
    ReprVal k (encFun (repOf (keyOf lab dm)))
      (fun i j => numOf dm (keyOf lab dm) i = numOf dm (keyOf lab dm) j) := by
  refine ⟨fun i => ⟨repOf (keyOf lab dm) i, repOf_lt _ i⟩, rfl, fun i j => ?_, fun i => ?_⟩
  · rw [Fin.mk.injEq, repOf_eq_iff, keyOf_eq_iff_numOf hl]
  · exact Fin.ext (repOf_idem _ i)

end Cls

section Quot

variable {S : State Ω C} {e : Ω ≃ Fin k}

/-- The block labeling of a quotient whose blocks the program numbers is the program's
numbering. -/
theorem labFin_eq_numOf (Q : PrimitiveQuotient S) {lab : Fin k → ℕ}
    (hd : Q.d = (Cls.repsOf (indF e S.dom) (Cls.keyOf lab (indF e S.dom))).length)
    (hblk : ∀ v ∈ S.dom, (Q.blk v : ℕ) =
      Cls.numOf (indF e S.dom) (Cls.keyOf lab (indF e S.dom)) (e v)) (i : Fin k) :
    Q.labFin e i = Cls.numOf (indF e S.dom) (Cls.keyOf lab (indF e S.dom)) i := by
  classical
  unfold PrimitiveQuotient.labFin
  by_cases hi : e.symm i ∈ S.dom
  · rw [if_pos hi, hblk _ hi, Equiv.apply_symm_apply]
  · rw [if_neg hi, Cls.numOf_off, hd]
    have := (Cls.indF_ne_zero e S.dom (e.symm i)).not.2 hi
    rw [Equiv.apply_symm_apply] at this
    omega

/-- **The representatives of the program's numbering give the block relation** (the input
`lv` of `enum_spec`). -/
theorem reprVal_labFin (Q : PrimitiveQuotient S) {lab : Fin k → ℕ}
    (hl : Cls.LabOK lab (indF e S.dom))
    (hd : Q.d = (Cls.repsOf (indF e S.dom) (Cls.keyOf lab (indF e S.dom))).length)
    (hblk : ∀ v ∈ S.dom, (Q.blk v : ℕ) =
      Cls.numOf (indF e S.dom) (Cls.keyOf lab (indF e S.dom)) (e v)) :
    ReprVal k (encFun (Cls.repOf (Cls.keyOf lab (indF e S.dom))))
      (fun i j => Q.labFin e i = Q.labFin e j) := by
  have h := Cls.reprVal_numOf hl
  simp only [labFin_eq_numOf Q hd hblk]
  exact h

/-- **The computed action generates the image of an action on numbers.** If `b` numbers the
points of the domain as `num` does, `ρ` acts on the numbers compatibly with `b`, and the `t`-th
representative is a point of the domain with number `t`, then the computed action is a group
value of `ρ(G)`. -/
theorem actVal_groupVal_of {d : ℕ} (ρ : S.G →* Perm (Fin d)) (b : Ω → Fin d)
    {num : Fin k → ℕ} {reps : List ℕ} (hd : reps.length = d)
    (hb : ∀ v ∈ S.dom, (b v : ℕ) = num (e v))
    (hρb : ∀ g : S.G, ∀ v ∈ S.dom, ρ g (b v) = b ((g : Perm Ω) v))
    (hrep : ∀ t (ht : t < reps.length), ∃ hr : reps[t] < k, e.symm ⟨_, hr⟩ ∈ S.dom ∧
      num ⟨_, hr⟩ = t)
    {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e S.G) :
    GroupVal d (actVal num reps gs) ρ.range := by
  refine ⟨gs.map (homFin e ρ), ?_, range_eq_gens e ρ hgs⟩
  have hρ : ∀ g : Perm (Fin k), (toFin e).symm g ∈ S.G → ∀ (r : Fin k), e.symm r ∈ S.dom →
      ∀ hlt : num r < d, ((homFin e ρ g) ⟨num r, hlt⟩ : ℕ) = num (g r) := by
    intro g hg r hr hlt
    have h1 : (⟨num r, hlt⟩ : Fin d) = b (e.symm r) :=
      Fin.ext (by rw [hb _ hr, Equiv.apply_symm_apply])
    have hgr : (toFin e).symm g (e.symm r) = e.symm (g r) := by
      simp [toFin, Equiv.permCongrHom, Equiv.permCongr_apply]
    unfold homFin
    rw [dif_pos hg, h1, hρb ⟨_, hg⟩ _ hr]
    show (b ((toFin e).symm g (e.symm r)) : ℕ) = _
    rw [hgr, hb _ (by rw [← hgr]; exact (S.dom_inv _ hg _).2 hr), Equiv.apply_symm_apply]
  have hmem : ∀ g ∈ 1 :: gs, (toFin e).symm g ∈ S.G := by
    intro g hg
    have : g ∈ groupFin e S.G := by
      rw [← hgs]
      rcases List.mem_cons.1 hg with rfl | hg
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure hg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 this
    show (toFin e).symm (toFin e g') ∈ S.G
    rw [MulEquiv.symm_apply_apply]; exact hg'
  unfold actVal encGroup encPerms
  rw [hd]
  have e1 : ((1 :: gs.map (homFin e ρ)).map encPerm) =
      (1 :: gs).map (fun g => encPerm (homFin e ρ g)) := by
    simp [homFin_one]
  rw [e1]
  congr 3
  refine congrArg Val.list (List.map_congr_left ?_)
  intro g hg
  exact actList_eq hd hrep hρ (hmem g hg)

/-- **The computed action generates the image of the block action** (the input of
`case_spec`). -/
theorem actVal_groupVal (Q : PrimitiveQuotient S) {num : Fin k → ℕ} {reps : List ℕ}
    (hd : reps.length = Q.d)
    (hblk : ∀ v ∈ S.dom, (Q.blk v : ℕ) = num (e v))
    (hrep : ∀ t (ht : t < reps.length), ∃ hr : reps[t] < k, e.symm ⟨_, hr⟩ ∈ S.dom ∧
      num ⟨_, hr⟩ = t)
    {gs : List (Perm (Fin k))} (hgs : gens gs = groupFin e S.G) :
    GroupVal Q.d (actVal num reps gs) Q.ρ.range :=
  actVal_groupVal_of Q.ρ Q.blk hd hblk (fun g v hv => (Q.equivariant g v hv).symm) hrep hgs

/-- The representatives of the program's numbering are points of the domain with their own
numbers. -/
theorem repsOf_rep {D : Set Ω} {lab : Fin k → ℕ} (t : ℕ)
    (ht : t < (Cls.repsOf (indF e D) (Cls.keyOf lab (indF e D))).length) :
    ∃ hr : (Cls.repsOf (indF e D) (Cls.keyOf lab (indF e D)))[t] < k, e.symm ⟨_, hr⟩ ∈ D ∧
      Cls.numOf (indF e D) (Cls.keyOf lab (indF e D)) ⟨_, hr⟩ = t := by
  obtain ⟨hr, h1, h2⟩ := Cls.numOf_getElem (lab := lab) (dm := indF e D) ht
  refine ⟨hr, ?_, h2⟩
  have := (Cls.indF_ne_zero e D (e.symm ⟨_, hr⟩)).1
  rw [Equiv.apply_symm_apply] at this
  exact this h1

end Quot

/-! ### The exposed quotient from the program's data -/

section Expose

variable {S : State Ω C} {e : Ω ≃ Fin k}

/-- **The exposed quotient from the program's data.** Let the hierarchy be `pre ++ J :: post`
with `J` holding the domain, let `B` be coarser than the fine end `f` of `pre` and coarser than
every comparable retained column partition coarser than `f`, let `num` number the classes of `B`,
`ρ` act on the numbers, `lab'` be a minimal block system of `ρ(G)`, and `lab2` be `lab'` of the
numbers on the domain. Then there is a primitive quotient whose blocks are numbered by the
program's numbering of `lab2`, that kills the columns, keeps the levels, and whose hierarchy
splits `J` at the kernel of `lab2`. -/
theorem expose_quot [Finite Ω] (htr : S.Transitive) (hinv : S.HierInv)
    {pre : List (Interval Ω)} {J : Interval Ω} {post : List (Interval Ω)}
    (hl : S.hier = pre ++ J :: post) (hJ : UnivOn S.dom J.part) {B : Setoid Ω}
    (hfB : ∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ pre).r v w → B.r v w)
    (hBcols : ∀ c, S.retainedCols = some c → ColsComparable S c →
      (∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ pre).r v w → c.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → B.r v w)
    {num : Fin k → ℕ} {d : ℕ} (h1 : Cls.Numbering e S.dom B num d) (hd : 0 < d)
    {ρ : S.G →* Perm (Fin d)}
    (hρ : ∀ g : S.G, ∀ v ∈ S.dom, ρ g (h1.toMap hd v) = h1.toMap hd ((g : Perm Ω) v))
    {lab' : Fin d → ℕ} (hmin : GI.Cited.IsMinimalBlocks ρ.range lab') {lab2 : Fin k → ℕ}
    (h2 : ∀ v ∈ S.dom, lab2 (e v) = lab' (h1.toMap hd v)) (hlab2 : ∀ i, lab2 i < k) :
    ∃ Q : PrimitiveQuotient S,
      Q.d = (Cls.repsOf (indF e S.dom) (Cls.keyOf lab2 (indF e S.dom))).length ∧
      (∀ v ∈ S.dom, (Q.blk v : ℕ) = Cls.numOf (indF e S.dom) (Cls.keyOf lab2 (indF e S.dom)) (e v)) ∧
      Q.KillsCols ∧ Q.KeepsLevels ∧
      ∃ c₁ : ℕ, c₁ * Q.d = classCount (fineEnd ⊥ pre) S.dom ∧
        Q.pre = (if c₁ = 1 then pre else
          pre ++ [⟨Setoid.ker fun v => lab2 (e v), c₁, min J.cap c₁, J.origin⟩]) ∧
        Q.top = ⟨J.part, Q.d, min J.cap Q.d, J.origin⟩ ∧ Q.post = post := by
  set M : Setoid Ω := Setoid.ker fun v => lab2 (e v) with hM
  obtain ⟨hcand, hmax, hBM⟩ := pull_cand h1 hd hρ hmin h2 hfB
  have hcols : ∀ c, S.retainedCols = some c → ColsComparable S c →
      (∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ pre).r v w → c.r v w) →
      ∀ v ∈ S.dom, ∀ w ∈ S.dom, c.r v w → M.r v w :=
    fun c hc hcc hfc v hv w hw hvw => hBM v hv w hw (hBcols c hc hcc hfc v hv w hw hvw)
  obtain ⟨Q0, hblk0, hA0, hK0, c₁, hc1, hpre, htop, hpost⟩ :=
    exists_primitiveQuotient_of_cand S htr hinv pre J post hl hJ M hcand hmax hcols
  have hR : ∀ i j, lab2 i = lab2 j ↔ M.r (e.symm i) (e.symm j) := fun i j => by
    show _ ↔ lab2 (e (e.symm i)) = lab2 (e (e.symm j))
    simp
  have hn2 := Cls.numbering e S.dom M lab2 hlab2 hR
  obtain ⟨a, ha⟩ : S.dom.Nonempty := by
    by_contra hne
    exact hcand.proper fun v hv => absurd ⟨v, hv⟩ hne
  have hd2 : 0 < (Cls.repsOf (indF e S.dom) (Cls.keyOf lab2 (indF e S.dom))).length := by
    have := hn2.lt a ha; omega
  have hfib : ∀ v ∈ S.dom, ∀ w ∈ S.dom, hn2.toMap hd2 v = hn2.toMap hd2 w ↔
      Q0.blk v = Q0.blk w := fun v hv w hw => by
    rw [hn2.toMap_eq_iff hd2 hv hw, hblk0 v hv w hw]
  obtain ⟨Q, hQd, hQb, hpre', htop', hpost', -, hK, hKL, hA⟩ :=
    Q0.exists_relabel (hn2.toMap hd2) (hn2.toMap_onto hd2) hfib
  have hd0 : Q0.d = Q.d := by
    obtain ⟨σ, -⟩ := exists_numEquiv (D := S.dom) Q0.blk (hn2.toMap hd2) Q0.onto
      (hn2.toMap_onto hd2) fun v hv w hw => (hfib v hv w hw).symm
    rw [hQd]
    simpa using Fintype.card_congr σ
  refine ⟨Q, hQd, fun v hv => by rw [hQb v hv, hn2.toMap_val hd2 hv], Q.killsCols_of (hA hA0) hinv,
    hKL hK0, c₁, by rw [← hd0]; exact hc1, by rw [hpre', hpre], by rw [htop', htop, hd0],
    by rw [hpost', hpost]⟩

end Expose

end GI.Impl
