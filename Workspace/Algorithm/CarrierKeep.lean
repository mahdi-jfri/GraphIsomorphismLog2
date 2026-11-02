import Workspace.Algorithm.Expose

/-!
# Keeping the carrier of the retained rows

The state records that its retained rows are a carrier (`CarrierOK`,
`Workspace/Algorithm/State.lean`): the column partition is invariant and is a level of the
hierarchy, and the subgroup `J` of the elements that fix every column acts on the rows as the
whole of `Alt(m)`, with `M = J ∩ ker ρ` transitive on every cell (`CarrierSpec`). This file
proves what keeps it.

* **A subgroup that contains `J` keeps it** (`CarrierSpec.mono`, `CarrierOK.mono`). Section A.4,
  "Inheritance of the retained row action": "While processing the quotient `Q`, use full
  preimages of all quotient restrictions. This keeps the entire kernel `J`, hence keeps the
  natural row carrier."
* **A new hierarchy with the same partitions keeps the column level** (`ColsLevel.of_parts`),
  for example after a cap update.
* **The exposed quotient lies above the columns** (`State.expose_killsCols`). The columns are a
  level of the hierarchy, so they are comparable with every level (`ColsLevel.comparable`), and
  the exposed quotient is chosen above them (`State.expose_aboveCols`; Algorithm 5: "Expose the
  next primitive quotient above any retained column partition"). So every element that fixes
  every column acts trivially on the exposed blocks (`PrimitiveQuotient.KillsCols`).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

variable {Ω : Type}

/-! ### The carrier passes to a subgroup that contains `J` -/

/-- A subgroup that contains every column-fixing element keeps the carrier. -/
theorem CarrierSpec.mono {G G' : Subgroup (Perm Ω)} {D : Set Ω} {m : ℕ} {rows cols : Setoid Ω}
    {row : Ω → Fin m} {ρ : G →* alternatingGroup (Fin m)} (h : CarrierSpec G D m rows cols row ρ)
    (hG : G' ≤ G) (hJ : ∀ g ∈ G, FixesCols cols D g → g ∈ G') :
    CarrierSpec G' D m rows cols row (ρ.comp (Subgroup.inclusion hG)) where
  three_le := h.three_le
  row_iff := h.row_iff
  row_onto := h.row_onto
  row_equivariant g v hv := h.row_equivariant (Subgroup.inclusion hG g) v hv
  cols_inv g hg := h.cols_inv g (hG hg)
  two_cols := h.two_cols
  indep a := by
    obtain ⟨g, hg, hf⟩ := h.indep a
    exact ⟨⟨g, hJ g g.2 hf⟩, hg, hf⟩
  cells v hv w hw h1 h2 := by
    obtain ⟨g, hg, hf, hgv⟩ := h.cells v hv w hw h1 h2
    exact ⟨⟨g, hJ g g.2 hf⟩, hg, hf, hgv⟩

/-- **The carrier invariant passes to a subgroup that contains `J`**, with a hierarchy that keeps
the column level. -/
theorem CarrierOK.mono {G G' : Subgroup (Perm Ω)} {D : Set Ω} {rows : Option (RowRecord Ω)}
    {hier hier' : List (Interval Ω)} (h : CarrierOK G D rows hier) (hG : G' ≤ G)
    (hJ : ∀ R c, rows = some R → R.cols = some c → ∀ g ∈ G, FixesCols c D g → g ∈ G')
    (hl : ∀ c, ColsLevel D hier c → ColsLevel D hier' c) : CarrierOK G' D rows hier' := by
  intro R hR
  obtain ⟨c, hc, ⟨row, ρ, hs⟩, hlev⟩ := h R hR
  exact ⟨c, hc, ⟨row, _, hs.mono hG (hJ R c hR hc)⟩, hl c hlev⟩

/-- A product of column-fixing elements fixes every column. -/
theorem FixesCols.mul {G : Subgroup (Perm Ω)} {D : Set Ω} (hD : Invariant G D) {c : Setoid Ω}
    {g k : Perm Ω} (hk : k ∈ G) (hg : FixesCols c D g) (hk' : FixesCols c D k) :
    FixesCols c D (g * k) := fun v hv =>
  c.iseqv.trans (hg (k v) ((hD k hk v).2 hv)) (hk' v hv)

/-! ### The column level -/

theorem hierLevel_eq (pre : List (Interval Ω)) : hierLevel pre = fineEnd ⊥ pre := rfl

/-- The fine end depends only on the partitions of the intervals. -/
theorem foldl_part_congr : ∀ (l l' : List (Interval Ω)) (f : Setoid Ω),
    l.map Interval.part = l'.map Interval.part →
      l.foldl (fun _ I => I.part) f = l'.foldl (fun _ I => I.part) f
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | I :: l, I' :: l', f, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.foldl_cons]
    rw [h.1]
    exact foldl_part_congr l l' _ h.2

/-- **A hierarchy with the same partitions keeps the column level.** -/
theorem ColsLevel.of_parts {D : Set Ω} {hier hier' : List (Interval Ω)} {c : Setoid Ω}
    (h : ColsLevel D hier c) (hp : hier'.map Interval.part = hier.map Interval.part) :
    ColsLevel D hier' c := by
  obtain ⟨pre, post, rfl, hc⟩ := h
  refine ⟨hier'.take pre.length, hier'.drop pre.length, (List.take_append_drop _ _).symm, ?_⟩
  have : hierLevel (hier'.take pre.length) = hierLevel pre := by
    unfold hierLevel
    apply foldl_part_congr
    rw [List.map_take, hp, List.map_append, List.take_left' (by simp)]
  rw [this]
  exact hc

/-- Changing the bound of one interval keeps the partitions. -/
theorem map_part_set_cap (l : List (Interval Ω)) (i : ℕ) (hi : i < l.length) (c : ℕ) :
    (l.set i { l[i] with cap := c }).map Interval.part = l.map Interval.part := by
  rw [List.map_set]
  apply List.ext_getElem (by simp)
  intro n h1 h2
  rw [List.getElem_set]
  split_ifs with hn
  · subst hn; simp
  · rfl

/-- The column level on a smaller domain. -/
theorem ColsLevel.subset {D D' : Set Ω} {hier : List (Interval Ω)} {c : Setoid Ω}
    (h : ColsLevel D hier c) (hD : D' ⊆ D) : ColsLevel D' hier c := by
  obtain ⟨pre, post, hh, hc⟩ := h
  exact ⟨pre, post, hh, fun v hv w hw => hc v (hD hv) w (hD hw)⟩

/-- Along a chain, the fine end only gets coarser. -/
theorem chain_le {G : Subgroup (Perm Ω)} {D : Set Ω} (l : List (Interval Ω)) :
    ∀ {f : Setoid Ω}, Chain G D f l → ∀ v ∈ D, ∀ w ∈ D, f.r v w → (fineEnd f l).r v w := by
  induction l with
  | nil => intro f _ v _ w _ h; exact h
  | cons I l ih =>
    intro f hch v hv w hw h
    obtain ⟨-, h2, -, -, h5⟩ := hch
    exact ih h5 v hv w hw (h2 v hv w hw h)

/-- **A level of a chain is comparable with every level.** -/
theorem ColsLevel.comparable {G : Subgroup (Perm Ω)} {D : Set Ω} {hier : List (Interval Ω)}
    {c : Setoid Ω} (hch : Chain G D ⊥ hier) (hl : ColsLevel D hier c) :
    ∀ pre post, hier = pre ++ post →
      (∀ v ∈ D, ∀ w ∈ D, (fineEnd ⊥ pre).r v w → c.r v w) ∨
        (∀ v ∈ D, ∀ w ∈ D, c.r v w → (fineEnd ⊥ pre).r v w) := by
  obtain ⟨pre₀, post₀, h0, hc⟩ := hl
  intro pre post h
  rw [h0] at hch
  rcases List.append_eq_append_iff.1 (h0.symm.trans h) with ⟨a', h1, h2⟩ | ⟨c', h1, -⟩
  · -- `pre = pre₀ ++ a'`: the columns lie below the level of `pre`.
    right
    rw [h2] at hch
    have hch' := (chain_append.1 (chain_append.1 hch).2).1
    intro v hv w hw hvw
    rw [h1, fineEnd_append]
    exact chain_le a' hch' v hv w hw ((hc v hv w hw).2 hvw)
  · -- `pre₀ = pre ++ c'`: the level of `pre` lies below the columns.
    left
    rw [h1, List.append_assoc] at hch
    have hch' := (chain_append.1 (chain_append.1 hch).2).1
    intro v hv w hw hvw
    apply (hc v hv w hw).1
    rw [h1, hierLevel_eq, fineEnd_append]
    exact chain_le c' hch' v hv w hw hvw

/-! ### The exposed quotient lies above the columns -/

variable {C : Type}

/-- The carrier of a state, for a retained record `R` with columns `c`. -/
theorem State.carrier_of {S : State Ω C} {R : RowRecord Ω} {c : Setoid Ω} (hR : S.rows = some R)
    (hc : R.cols = some c) :
    (∃ row ρ, CarrierSpec S.G S.dom R.m R.rows c row ρ) ∧ ColsLevel S.dom S.hier c := by
  obtain ⟨c', hc', hs, hl⟩ := S.carrier R hR
  rw [hc] at hc'
  cases hc'
  exact ⟨hs, hl⟩

/-- **The retained columns are comparable with the stored levels**: they are an invariant
partition that splits the domain and a level of the hierarchy (`ColsComparable`). -/
theorem State.colsComparable {S : State Ω C} (hinv : S.HierInv) {R : RowRecord Ω} {c : Setoid Ω}
    (hR : S.rows = some R) (hc : R.cols = some c) : ColsComparable S c := by
  obtain ⟨⟨row, ρ, hs⟩, hl⟩ := S.carrier_of hR hc
  refine ⟨hs.cols_inv, fun hu => ?_, hl.comparable hinv.chain⟩
  obtain ⟨v, hv, w, hw, hvw⟩ := hs.two_cols
  exact hvw (hu v hv w hw)

/-- **The blocks of a primitive quotient lie above the retained columns**: an element that fixes
every retained column acts trivially on the blocks. -/
def PrimitiveQuotient.KillsCols {S : State Ω C} (Q : PrimitiveQuotient S) : Prop :=
  ∀ R c, S.rows = some R → R.cols = some c → ∀ g : S.G, FixesCols c S.dom g → Q.ρ g = 1

theorem PrimitiveQuotient.killsCols_of {S : State Ω C} (Q : PrimitiveQuotient S)
    (hQ : Q.AboveCols) (hinv : S.HierInv) : Q.KillsCols := by
  intro R c hR hc g hg
  ext i
  obtain ⟨v, hv, rfl⟩ := Q.onto i
  rw [← Q.equivariant g v hv, Perm.one_apply]
  have hgv : (g : Perm Ω) v ∈ S.dom := (S.dom_inv g.1 g.2 v).2 hv
  have hcR : S.retainedCols = some c := by simp [State.retainedCols, hR, hc]
  exact congrArg Fin.val (hQ c hcR (S.colsComparable hinv hR hc) _ hgv v hv (hg v hv))

/-- **The exposed quotient lies above the retained columns** (Algorithm 5: "Expose the next
primitive quotient above any retained column partition"). -/
theorem State.expose_killsCols [Finite Ω] (S : State Ω C) (htr : S.Transitive)
    (hinv : S.HierInv) (h2 : ¬ UnivOn S.dom ⊥) : (S.expose htr hinv h2).KillsCols :=
  (S.expose htr hinv h2).killsCols_of (S.expose_aboveCols htr hinv h2) hinv

end GI.Algorithm
