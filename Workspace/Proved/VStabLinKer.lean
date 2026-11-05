module

public import Workspace.Proved.VStabLinMath
public import Workspace.Impl.VStabLinAll

@[expose] public section

/-!
# What the insertion of a list computes

We insert pairs `(x_i, t_i)` one by one (`vsInsertAll`). We read each pair as a pair of vectors
and look at the span `S` of the input pairs. The result has echelon rows and relation tags.

* `vsInsertAll_inv`: the rows are in echelon form, and the row pairs together with the pairs
  `(0, relation)` span exactly `S`.
* `vsPairs_fst_zero`: a combination of echelon row pairs with main part `0` is `0`.
* `vsInsertAll_ker`: `(0, s) ∈ S` exactly when `s` is in the span of the relations. With unit
  tags `t_i = e_i`, this says the relations span the kernel of `a ↦ ∑ a_i x_i`.
* `vsInsertAll_span`: the main parts of the rows span the main parts of the inputs.
* `vsSolve`: sifting `(u, 0)` through the rows gives main part `0` exactly when `u` is in that
  span, and then `(u, -sifted tag)` lies in `S`. With unit tags the negated sifted tag holds
  the coefficients of `u`.
-/

namespace GI.Proved

open GI.Impl

variable {p : ℕ}

/-- The span of a list of vector pairs. -/
def vsPairSpan (p : ℕ) (L : List (List ℕ × List ℕ)) :
    Submodule (ZMod p) ((ℕ → ZMod p) × (ℕ → ZMod p)) :=
  Submodule.span (ZMod p) {v | v ∈ L.map (vsP p)}

/-- The span of the row pairs. -/
def vsRowSpan (p : ℕ) (rows : List VsRow) : Submodule (ZMod p) ((ℕ → ZMod p) × (ℕ → ZMod p)) :=
  Submodule.span (ZMod p) {v | v ∈ rows.map (vsR p)}

/-- The pair `(0, t)` of a relation tag. -/
def vsRelP (p : ℕ) (t : List ℕ) : (ℕ → ZMod p) × (ℕ → ZMod p) := (0, vsF p t)

/-- The span of the pairs `(0, t)` for the relation tags `t`. -/
def vsRelSpan (p : ℕ) (rels : List (List ℕ)) : Submodule (ZMod p) ((ℕ → ZMod p) × (ℕ → ZMod p)) :=
  Submodule.span (ZMod p) {v | v ∈ rels.map (vsRelP p)}

/-- The span of an accumulator: row pairs and relation pairs. -/
def vsAccSpan (p : ℕ) (acc : List VsRow × List (List ℕ)) :
    Submodule (ZMod p) ((ℕ → ZMod p) × (ℕ → ZMod p)) :=
  vsRowSpan p acc.1 ⊔ vsRelSpan p acc.2

theorem vsSpan_mono_append_left {α : Type*} (f : α → (ℕ → ZMod p) × (ℕ → ZMod p)) (l : List α) (a : α) :
    Submodule.span (ZMod p) {v | v ∈ (l ++ [a]).map f} =
      Submodule.span (ZMod p) {v | v ∈ l.map f} ⊔ Submodule.span (ZMod p) {f a} := by
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp [eq_comm, or_comm]

theorem vsPairSpan_append (L : List (List ℕ × List ℕ)) (xt : List ℕ × List ℕ) :
    vsPairSpan p (L ++ [xt]) = vsPairSpan p L ⊔ Submodule.span (ZMod p) {vsP p xt} :=
  vsSpan_mono_append_left _ L xt

/-- **Sifting changes the pair by a combination of the row pairs.** -/
theorem vsSift_psub_mem (hp : 0 < p) (rows : List VsRow) {xt : List ℕ × List ℕ}
    (hb : VsBelow p xt) (hs : VsShort xt rows) :
    vsP p xt - vsP p (vsSift p rows xt) ∈ vsRowSpan p rows := by
  induction rows generalizing xt with
  | nil => simp [vsSift]
  | cons r rs ih =>
    have hr0 := hs r (by simp)
    have hs' : VsShort (vsSiftStep p xt r) rs :=
      vsShort_step (fun r' hr' => hs r' (by simp [hr']))
    have h1 := ih (vsSiftStep_below hp xt r) hs'
    rw [vsSiftStep_vsP hb hr0.1 hr0.2] at h1
    have hmono : vsRowSpan p rs ≤ vsRowSpan p (r :: rs) :=
      Submodule.span_mono fun v hv => by
        simp only [Set.mem_setOf_eq, List.mem_map, List.mem_cons] at hv ⊢
        obtain ⟨r', hr', rfl⟩ := hv
        exact ⟨r', Or.inr hr', rfl⟩
    have h2 : vsF p xt.1 r.j • vsR p r ∈ vsRowSpan p (r :: rs) :=
      Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have := Submodule.add_mem _ (hmono h1) h2
    rw [vsSift_cons]
    convert this using 1
    abel

/-- The main parts of a combination of row pairs lie in the span of the rows. -/
theorem vsRowSpan_fst {rows : List VsRow} {v : (ℕ → ZMod p) × (ℕ → ZMod p)}
    (hv : v ∈ vsRowSpan p rows) : v.1 ∈ vsSpan p rows := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_setOf_eq, List.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact vsF_mem_vsSpan p hr
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

/-- **Echelon row pairs are independent.** A combination of echelon row pairs whose main part
is `0` is `0`. -/
theorem vsPairs_fst_zero {rows : List VsRow} (he : VsEch p rows)
    {v : (ℕ → ZMod p) × (ℕ → ZMod p)} (hv : v ∈ vsRowSpan p rows) (h0 : v.1 = 0) : v = 0 := by
  induction rows generalizing v with
  | nil =>
    have : vsRowSpan p [] = ⊥ := by simp [vsRowSpan]
    rw [this] at hv
    exact (Submodule.mem_bot _).mp hv
  | cons r rs ih =>
    obtain ⟨h1, hz, hrs⟩ := he
    have e : vsRowSpan p (r :: rs) = Submodule.span (ZMod p)
        (insert (vsR p r) {v | v ∈ rs.map (vsR p)}) := by
      unfold vsRowSpan
      congr 1
      ext w
      simp [eq_comm]
    rw [e, Submodule.mem_span_insert] at hv
    obtain ⟨a, w, hw, rfl⟩ := hv
    have hw' : w ∈ vsRowSpan p rs := hw
    have hwj : w.1 r.j = 0 := vsSpan_apply_zero hz (vsRowSpan_fst hw')
    have ha : a = 0 := by
      have := congrFun h0 r.j
      simpa [vsR, h1, hwj] using this
    subst ha
    rw [zero_smul, zero_add] at h0 ⊢
    exact ih hrs hw' h0

/-- The relation pairs have main part `0`, and their tags span the relations' tags. -/
theorem vsRelSpan_mem {rels : List (List ℕ)} {v : (ℕ → ZMod p) × (ℕ → ZMod p)}
    (hv : v ∈ vsRelSpan p rels) :
    v.1 = 0 ∧ v.2 ∈ Submodule.span (ZMod p) {w | w ∈ rels.map (vsF p)} := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_setOf_eq, List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact ⟨rfl, Submodule.subset_span (by simp only [Set.mem_setOf_eq, List.mem_map]; exact ⟨t, ht, rfl⟩)⟩
  | zero => exact ⟨rfl, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    exact ⟨by rw [Prod.fst_add, hx.1, hy.1, add_zero], Submodule.add_mem _ hx.2 hy.2⟩
  | smul a x _ hx => exact ⟨by rw [Prod.smul_fst, hx.1, smul_zero], Submodule.smul_mem _ a hx.2⟩

/-- Pairs `(0, s)` with `s` in the span of the tags lie in the relation span. -/
theorem vsRelSpan_of_mem {rels : List (List ℕ)} {s : ℕ → ZMod p}
    (hs : s ∈ Submodule.span (ZMod p) {w | w ∈ rels.map (vsF p)}) :
    ((0 : ℕ → ZMod p), s) ∈ vsRelSpan p rels := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_setOf_eq, List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact Submodule.subset_span (by simp only [Set.mem_setOf_eq, List.mem_map]; exact ⟨t, ht, rfl⟩)
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    rwa [Prod.mk_add_mk, add_zero] at this
  | smul a x _ hx =>
    have := Submodule.smul_mem _ a hx
    rwa [Prod.smul_mk, smul_zero] at this

/-- The invariant of the fold: echelon rows, the accumulator spans the inputs, and the rows
have the lengths of the inputs. -/
structure VsAllInv (p lx lt : ℕ) (L : List (List ℕ × List ℕ))
    (acc : List VsRow × List (List ℕ)) : Prop where
  ech : VsEch p acc.1
  span : vsAccSpan p acc = vsPairSpan p L
  len : ∀ r ∈ acc.1, r.x.length = lx ∧ r.t.length = lt

theorem vsAllStep_inv (hp : p.Prime) {lx lt : ℕ} {L : List (List ℕ × List ℕ)}
    {acc : List VsRow × List (List ℕ)} (hI : VsAllInv p lx lt L acc) {xt : List ℕ × List ℕ}
    (hb : VsBelow p xt) (hlx : xt.1.length = lx) (hlt : xt.2.length = lt) :
    VsAllInv p lx lt (L ++ [xt]) (vsAllStep p acc xt) := by
  have hp0 := hp.pos
  haveI := Fact.mk hp
  have hs : VsShort xt acc.1 := fun r hr => by
    rw [(hI.len r hr).1, (hI.len r hr).2, hlx, hlt]; exact ⟨le_rfl, le_rfl⟩
  have hd := vsSift_psub_mem hp0 acc.1 hb hs
  obtain ⟨e1, e2⟩ := vsSift_length p acc.1 xt
  unfold vsAllStep
  split_ifs with hk
  · obtain ⟨hech, -, hW⟩ := vsInsert_new hp hI.ech hb hs hk
    set y := vsSift p acc.1 xt
    set nr := vsNewRow p y (vsNzIdx y.1)
    refine ⟨hech, ?_, fun r hr => ?_⟩
    · have hsp : vsAccSpan p (acc.1 ++ [nr], acc.2) =
          vsAccSpan p acc ⊔ Submodule.span (ZMod p) {vsR p nr} := by
        unfold vsAccSpan vsRowSpan
        dsimp only
        rw [vsSpan_mono_append_left]
        ac_rfl
      rw [hsp, vsPairSpan_append, ← hI.span]
      apply le_antisymm
      · refine sup_le le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
        refine hW (vsAccSpan p acc ⊔ Submodule.span (ZMod p) {vsP p xt}) (fun r hr => ?_)
          (Submodule.mem_sup_right (Submodule.subset_span rfl))
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span (by simpa using ⟨r, hr, rfl⟩)))
      · refine sup_le le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
        have hyb := vsSift_below hp0 acc.1 hb
        have hscale := vsNewRow_scale hp hyb hk
        set s : ZMod p := (vsInv p (y.1.getD (vsNzIdx y.1) 0) : ZMod p)
        have hs0 : s ≠ 0 := fun h0 => by rw [h0, zero_mul] at hscale; exact zero_ne_one hscale
        have e : vsP p xt = (vsP p xt - vsP p y) + s⁻¹ • vsR p nr := by
          rw [vsNewRow_vsR, smul_smul, ZMod.inv_mul_of_unit _ (Ne.isUnit (G₀ := ZMod p) hs0),
            one_smul, sub_add_cancel]
        rw [SetLike.mem_coe, e]
        refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left hd))
          (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.subset_span rfl)))
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hI.len r hr
      · simp only [nr, vsNewRow, vsLin_length]
        exact ⟨e1.trans hlx, e2.trans hlt⟩
  · have h0 : vsF p (vsSift p acc.1 xt).1 = 0 := by
      by_contra hne
      exact hk ((vsNzIdx_lt_iff (vsSift_below hp0 acc.1 hb)).mpr hne)
    set y := vsSift p acc.1 xt
    refine ⟨hI.ech, ?_, hI.len⟩
    have hsp : vsAccSpan p (acc.1, acc.2 ++ [y.2]) =
        vsAccSpan p acc ⊔ Submodule.span (ZMod p) {vsP p y} := by
      have ey : vsP p y = vsRelP p y.2 := by simp [vsP, vsRelP, h0]
      unfold vsAccSpan vsRelSpan
      dsimp only
      rw [vsSpan_mono_append_left, ey, sup_assoc]
    rw [hsp, vsPairSpan_append, ← hI.span]
    have hdr : vsP p xt - vsP p y ∈ vsAccSpan p acc := Submodule.mem_sup_left hd
    apply le_antisymm
    · refine sup_le le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
      have e : vsP p y = vsP p xt - (vsP p xt - vsP p y) := by abel
      rw [SetLike.mem_coe, e]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span rfl))
        (Submodule.mem_sup_left hdr)
    · refine sup_le le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
      have e : vsP p xt = (vsP p xt - vsP p y) + vsP p y := by abel
      rw [SetLike.mem_coe, e]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hdr)
        (Submodule.mem_sup_right (Submodule.subset_span rfl))

theorem vsFoldAll_inv (hp : p.Prime) {lx lt : ℕ} :
    ∀ (L L0 : List (List ℕ × List ℕ)) (acc : List VsRow × List (List ℕ)),
    (∀ xt ∈ L, VsBelow p xt ∧ xt.1.length = lx ∧ xt.2.length = lt) →
    VsAllInv p lx lt L0 acc → VsAllInv p lx lt (L0 ++ L) (L.foldl (vsAllStep p) acc)
  | [], L0, acc, _, h => by rw [List.append_nil]; exact h
  | xt :: L, L0, acc, hL, h => by
    obtain ⟨h1, h2, h3⟩ := hL xt (List.mem_cons_self ..)
    have := vsFoldAll_inv hp L (L0 ++ [xt]) (vsAllStep p acc xt)
      (fun y hy => hL y (List.mem_cons_of_mem _ hy)) (vsAllStep_inv hp h h1 h2 h3)
    rw [List.foldl_cons]
    simpa using this

/-- **The invariant of the insertion of a list.** -/
theorem vsInsertAll_inv (hp : p.Prime) {lx lt : ℕ} {L : List (List ℕ × List ℕ)}
    (hL : ∀ xt ∈ L, VsBelow p xt ∧ xt.1.length = lx ∧ xt.2.length = lt) :
    VsAllInv p lx lt L (vsInsertAll p L) := by
  have h0 : VsAllInv p lx lt [] ([], []) :=
    ⟨trivial, by simp [vsAccSpan, vsRowSpan, vsRelSpan, vsPairSpan], by simp⟩
  have := vsFoldAll_inv hp L [] ([], []) hL h0
  rwa [List.nil_append] at this

/-- **The relations span the kernel.** A pair `(0, s)` lies in the span of the inputs exactly
when `s` lies in the span of the relation tags. -/
theorem vsInsertAll_ker (hp : p.Prime) {lx lt : ℕ} {L : List (List ℕ × List ℕ)}
    (hL : ∀ xt ∈ L, VsBelow p xt ∧ xt.1.length = lx ∧ xt.2.length = lt) (s : ℕ → ZMod p) :
    ((0 : ℕ → ZMod p), s) ∈ vsPairSpan p L ↔
      s ∈ Submodule.span (ZMod p) {w | w ∈ (vsInsertAll p L).2.map (vsF p)} := by
  have hI := vsInsertAll_inv hp hL
  rw [← hI.span]
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h
    obtain ⟨hb1, hb2⟩ := vsRelSpan_mem hb
    have ha1 : a.1 = 0 := by
      have := congrArg Prod.fst hab
      rw [Prod.fst_add, hb1, add_zero] at this
      exact this
    have ha0 := vsPairs_fst_zero hI.ech ha ha1
    rw [ha0, zero_add] at hab
    rw [hab] at hb2
    exact hb2
  · intro h
    exact Submodule.mem_sup_right (vsRelSpan_of_mem h)

/-- **The rows span the main parts of the inputs.** -/
theorem vsInsertAll_span (hp : p.Prime) {lx lt : ℕ} {L : List (List ℕ × List ℕ)}
    (hL : ∀ xt ∈ L, VsBelow p xt ∧ xt.1.length = lx ∧ xt.2.length = lt) :
    vsSpan p (vsInsertAll p L).1 =
      Submodule.span (ZMod p) {w | w ∈ L.map fun xt => vsF p xt.1} := by
  have hI := vsInsertAll_inv hp hL
  have hm := congrArg (Submodule.map (LinearMap.fst (ZMod p) (ℕ → ZMod p) (ℕ → ZMod p))) hI.span
  simp only [vsAccSpan, Submodule.map_sup, vsRowSpan, vsRelSpan, vsPairSpan,
    Submodule.map_span] at hm
  have e1 : (LinearMap.fst (ZMod p) (ℕ → ZMod p) (ℕ → ZMod p)) '' {v | v ∈ (vsInsertAll p L).1.map
      (vsR p)} = {v | v ∈ (vsInsertAll p L).1.map fun r => vsF p r.x} := by
    ext v; simp [vsR]
  have e2 : (LinearMap.fst (ZMod p) (ℕ → ZMod p) (ℕ → ZMod p)) '' {v | v ∈ (vsInsertAll p L).2.map
      (vsRelP p)} ⊆ {0} := by
    rintro v ⟨w, hw, rfl⟩
    simp only [Set.mem_setOf_eq, List.mem_map] at hw
    obtain ⟨t, -, rfl⟩ := hw
    rfl
  have e3 : (LinearMap.fst (ZMod p) (ℕ → ZMod p) (ℕ → ZMod p)) '' {v | v ∈ L.map (vsP p)} =
      {w | w ∈ L.map fun xt => vsF p xt.1} := by
    ext v; simp [vsP]
  rw [e1, e3] at hm
  have e4 : Submodule.span (ZMod p) ((LinearMap.fst (ZMod p) (ℕ → ZMod p) (ℕ → ZMod p)) ''
      {v | v ∈ (vsInsertAll p L).2.map (vsRelP p)}) = ⊥ := by
    rw [eq_bot_iff, Submodule.span_le]
    exact e2.trans (by simp)
  rw [e4, sup_bot_eq] at hm
  exact hm

/-- **Solving.** Sift `(u, z)` through the rows, with `z` a tag that reads as `0`. The sifted
main part is `0` exactly when `u` is in the span of the rows. In that case
`(u, -sifted tag)` lies in the span of the inputs. -/
theorem vsSolve (hp : p.Prime) {lx lt : ℕ} {L : List (List ℕ × List ℕ)}
    (hL : ∀ xt ∈ L, VsBelow p xt ∧ xt.1.length = lx ∧ xt.2.length = lt)
    {u z : List ℕ} (hu : ∀ y ∈ u, y < p) (hul : u.length = lx) (hzl : z.length = lt)
    (hz : vsF p z = 0) :
    (vsF p (vsSift p (vsInsertAll p L).1 (u, z)).1 = 0 ↔
      vsF p u ∈ vsSpan p (vsInsertAll p L).1) ∧
    (vsF p (vsSift p (vsInsertAll p L).1 (u, z)).1 = 0 →
      (vsF p u, -vsF p (vsSift p (vsInsertAll p L).1 (u, z)).2) ∈ vsPairSpan p L) := by
  have hI := vsInsertAll_inv hp hL
  have hs : VsShort (u, z) (vsInsertAll p L).1 := fun r hr => by
    rw [(hI.len r hr).1, (hI.len r hr).2]; exact ⟨hul.ge, hzl.ge⟩
  refine ⟨vsSift_eq_zero_iff hp.pos hI.ech hu hs, fun h0 => ?_⟩
  have hd := vsSift_psub_mem hp.pos (vsInsertAll p L).1 (xt := (u, z)) hu hs
  rw [← hI.span]
  refine Submodule.mem_sup_left ?_
  convert hd using 1
  simp [vsP, hz, h0]

end GI.Proved
