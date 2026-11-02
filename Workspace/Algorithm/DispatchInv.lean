import Workspace.Algorithm.Expose

/-!
# The dispatcher keeps the hierarchy invariant

The children of a dispatcher step run under the child group `K` on the same domain, with the
hierarchy `I.hier'` (`DispatchStep.K_hier'_eq`):

* enumeration: the block kernel, with the exposed hierarchy of the primitive quotient. The
  exposed hierarchy satisfies the invariant for `G` (`PrimitiveQuotient.tower`), so it does for
  the subgroup `K`.
* product refinement (Section 3.3: "Product actions refine the actual hierarchy"): the
  coordinate subgroup, with the interval of the quotient split into the coordinate intervals
  `coordHier`. Interval `i` goes from "the coordinates `j ≥ i` agree" to "the coordinates
  `j ≥ i + 1` agree". The coordinate subgroup keeps every coordinate in place, so these
  partitions are invariant (`coordPart_inv`); in one class of the coarse end, a fine class is
  fixed by its coordinate `i`, so there are at most `binom(m,k)` of them (`classCount_coordPart`).

The result is `DispatchStep.hierInv`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type} {S : State Ω C}

namespace PrimitiveQuotient

variable (Q : PrimitiveQuotient S) {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k))

/-- The coordinate subgroup keeps every coordinate partition (it fixes every coordinate and
permutes the `k`-subsets inside each coordinate). -/
theorem coordPart_inv (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k) (i : ℕ) :
    ∀ g ∈ Q.coordinateGroup e hS hb, ∀ v ∈ S.dom, ∀ w ∈ S.dom,
      (Q.coordPart e i).r (g v) (g w) ↔ (Q.coordPart e i).r v w := by
  rintro _ ⟨x, hx, rfl⟩ v hv w hw
  obtain ⟨h, hh⟩ := (Product.coordHom_eq_one_iff e Q.ρ.range hS.1 hb _).1 hx
  have hgv := (S.dom_inv x.1 x.2 v).2 hv
  have hgw := (S.dom_inv x.1 x.2 w).2 hw
  have ev : e (Q.blk (x.1 v)) = fun j => GI.Cited.kSetPerm (h j) (e (Q.blk v) j) := by
    rw [Q.equivariant x v hv]
    exact hh (Q.blk v)
  have ew : e (Q.blk (x.1 w)) = fun j => GI.Cited.kSetPerm (h j) (e (Q.blk w) j) := by
    rw [Q.equivariant x w hw]
    exact hh (Q.blk w)
  change ((x.1 v ∈ S.dom ∧ x.1 w ∈ S.dom ∧ ∀ j : Fin r, i ≤ j.val →
      e (Q.blk (x.1 v)) j = e (Q.blk (x.1 w)) j) ∨ _) ↔
    ((v ∈ S.dom ∧ w ∈ S.dom ∧ ∀ j : Fin r, i ≤ j.val → e (Q.blk v) j = e (Q.blk w) j) ∨ _)
  rw [ev, ew]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro (⟨-, -, h'⟩ | ⟨h', -⟩)
    exacts [Or.inl ⟨hv, hw, h'⟩, absurd hgv h']
  · rintro (⟨-, -, h'⟩ | ⟨h', -⟩)
    exacts [Or.inl ⟨hgv, hgw, h'⟩, absurd hv h']

/-- In one class of "the coordinates `j ≥ i + 1` agree", the classes of "the coordinates
`j ≥ i` agree" differ only in coordinate `i`, so there are at most `binom(m,k)` of them. -/
theorem classCount_coordPart [Finite Ω] {i : ℕ} (hi : i < r) (X : Set Ω) (a : Ω)
    (hX : ∀ w ∈ X, w ∈ S.dom ∧ (Q.coordPart e (i + 1)).r a w) :
    classCount (Q.coordPart e i) X ≤ m.choose k := by
  classical
  have hmem : ∀ v ∈ X, ∀ w ∈ X, e (Q.blk v) ⟨i, hi⟩ = e (Q.blk w) ⟨i, hi⟩ →
      (Q.coordPart e i).r v w := by
    intro v hv w hw hvw
    obtain ⟨hvD, hav⟩ := hX v hv
    obtain ⟨hwD, haw⟩ := hX w hw
    have ha : a ∈ S.dom := by
      rcases hav with ⟨h1, -, -⟩ | ⟨h1, h2⟩
      exacts [h1, absurd hvD h2]
    have hav' : ∀ j : Fin r, i + 1 ≤ j.val → e (Q.blk a) j = e (Q.blk v) j := by
      rcases hav with ⟨-, -, h⟩ | ⟨h1, -⟩
      exacts [h, absurd ha h1]
    have haw' : ∀ j : Fin r, i + 1 ≤ j.val → e (Q.blk a) j = e (Q.blk w) j := by
      rcases haw with ⟨-, -, h⟩ | ⟨h1, -⟩
      exacts [h, absurd ha h1]
    refine Or.inl ⟨hvD, hwD, fun j hj => ?_⟩
    rcases Nat.lt_or_ge i j.val with hlt | hge
    · exact (hav' j hlt).symm.trans (haw' j hlt)
    · have : j = ⟨i, hi⟩ := Fin.ext (show j.val = i by omega)
      rw [this]
      exact hvw
  have hcard : Nat.card (Product.KSet m k) = m.choose k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]
  unfold classCount
  rw [← hcard]
  refine Nat.card_le_card_of_injective
    (Quotient.lift (fun w : X => e (Q.blk w.1) ⟨i, hi⟩) fun v w hvw => ?_) ?_
  · have hvw' : (Q.coordPart e i).r v.1 w.1 := hvw
    rcases hvw' with ⟨-, -, h⟩ | ⟨h1, -⟩
    · exact h ⟨i, hi⟩ le_rfl
    · exact absurd (hX v.1 v.2).1 h1
  · intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn
    induction q₂ using Quotient.inductionOn
    exact Quotient.sound (hmem _ (Subtype.prop _) _ (Subtype.prop _) h)

/-- The coordinate intervals from `s` on: interval `i` goes from coordinates `j ≥ i` to
coordinates `j ≥ i + 1`. -/
def coordFrom (s n : ℕ) : List (Interval Ω) :=
  (List.range' s n).map fun i =>
    ⟨Q.coordPart e (i + 1), m.choose k, min Q.top.cap (m.choose k), Q.top.origin⟩

theorem coordHier_eq : Q.coordHier e = Q.coordFrom e 0 r := by
  rw [coordHier, coordFrom, List.range_eq_range']

theorem fineEnd_coordFrom (f : Setoid Ω) (s : ℕ) :
    ∀ n, 1 ≤ n → fineEnd f (Q.coordFrom e s n) = Q.coordPart e (s + n)
  | 0, h => absurd h (by norm_num)
  | 1, _ => rfl
  | n + 2, _ => by
    rw [coordFrom, List.range'_succ, List.map_cons, fineEnd_cons, ← coordFrom,
      fineEnd_coordFrom _ (s + 1) (n + 1) (by omega)]
    congr 1
    omega

theorem chain_coordFrom [Finite Ω] (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k) :
    ∀ (s n : ℕ), s + n ≤ r →
      Chain (Q.coordinateGroup e hS hb) S.dom (Q.coordPart e s) (Q.coordFrom e s n)
  | _, 0, _ => trivial
  | s, n + 1, h => by
    rw [coordFrom, List.range'_succ, List.map_cons, ← coordFrom]
    refine ⟨Q.coordPart_inv e hS hb (s + 1), fun v hv w hw hvw => ?_, fun a _ => ?_,
      min_le_right _ _, chain_coordFrom hS hb (s + 1) n (by omega)⟩
    · rcases hvw with ⟨h1, h2, h3⟩ | ⟨h1, -⟩
      exacts [Or.inl ⟨h1, h2, fun j hj => h3 j (by omega)⟩, absurd hv h1]
    · exact Q.classCount_coordPart e (by omega) _ a fun w hw => ⟨hw.1, hw.2.2⟩

theorem coordPart_mono {i j : ℕ} (hij : i ≤ j) {v w : Ω} (h : (Q.coordPart e i).r v w) :
    (Q.coordPart e j).r v w := by
  rcases h with ⟨h1, h2, h3⟩ | h
  exacts [Or.inl ⟨h1, h2, fun l hl => h3 l (hij.trans hl)⟩, Or.inr h]

/-- **The coordinate intervals keep the bound of the quotient interval** (Section A.5: "Refining
its product coordinates gives each resulting interval cap `q`, clamped by any already smaller
valid cap"): each coordinate interval is a sub-interval of the quotient interval, and its ratio
`binom(m,k)` bounds the classes it counts. -/
theorem caps_coordFrom [Finite Ω] (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k)
    (hcap : CapOK S.G S.dom (Q.coordPart e 0) Q.top.part Q.top.cap) :
    ∀ (s n : ℕ), s + n ≤ r →
      Caps (Q.coordinateGroup e hS hb) S.dom (Q.coordPart e s) (Q.coordFrom e s n)
  | _, 0, _ => trivial
  | s, n + 1, h => by
    have hKG : Q.coordinateGroup e hS hb ≤ S.G := Subgroup.map_subtype_le _
    rw [coordFrom, List.range'_succ, List.map_cons, ← coordFrom]
    refine ⟨fun a ha => ?_, caps_coordFrom hS hb hcap (s + 1) n (by omega)⟩
    refine capAt_min_count ((hcap a ha).sub hKG
      (fun u _ hu => ⟨hu.1, mem_orb_mono hKG hu.2.1, Q.top_univ a ha _ hu.1⟩)
      fun u _ _ hfix w hw => ?_) (S.dom_inv.mono hKG) (Q.coordPart_inv e hS hb s)
      (Q.coordPart_inv e hS hb (s + 1))
      (Q.classCount_coordPart e (by omega) _ a fun w hw => ⟨hw.1, hw.2.2⟩)
    exact Q.coordPart_mono e (Nat.zero_le s)
      (hfix w ⟨hw.1, mem_orb_mono hKG hw.2.1, Q.top_univ a ha w hw.1⟩)

end PrimitiveQuotient

namespace DispatchStep

variable {P : Params}

/-- **The dispatcher keeps the hierarchy invariant**: the children of a dispatcher step, under
the child group `K` on the same domain with the hierarchy `I.hier'`, satisfy `HierInv`. -/
theorem hierInv [Finite Ω] (I : DispatchStep P S) : HierInv I.K S.dom I.hier' := by
  rcases I.K_hier'_eq with ⟨Q, _, _, _, _, _, -, hK, hh⟩ | ⟨Q, _, _, _, _, -, m, k, r, e, hS, hb, hr, hK, hh⟩
  · rw [hK, hh]
    exact Q.tower.mono Q.kernel_le subset_rfl
  · rw [hK, hh]
    have hKG : Q.coordinateGroup e hS hb ≤ S.G := Subgroup.map_subtype_le _
    obtain ⟨hpre, -, -, -, -, hpost⟩ := chain_append.1 Q.tower.chain
    -- The block partition is "all coordinates agree".
    have h0 : ∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ Q.pre).r v w ↔ (Q.coordPart e 0).r v w := by
      intro v hv w hw
      rw [Q.fine_eq v hv w hw]
      constructor
      · intro h
        exact Or.inl ⟨hv, hw, fun j _ => by rw [h]⟩
      · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
        · exact e.injective (funext fun j => h j (Nat.zero_le _))
        · exact absurd hv h
    -- The last coordinate partition holds the domain, as the coarse end of `top` does.
    have hr0 : 1 ≤ r := by omega
    have hfe : fineEnd (fineEnd ⊥ Q.pre) (Q.coordHier e) = Q.coordPart e r := by
      rw [Q.coordHier_eq, Q.fineEnd_coordFrom e _ 0 r hr0, zero_add]
    have htop : ∀ v ∈ S.dom, ∀ w ∈ S.dom, Q.top.part.r v w ↔ (Q.coordPart e r).r v w := by
      intro v hv w hw
      refine ⟨fun _ => Or.inl ⟨hv, hw, fun j hj => absurd j.2 (by omega)⟩,
        fun _ => Q.top_univ v hv w hw⟩
    have hDK : Invariant (Q.coordinateGroup e hS hb) S.dom := S.dom_inv.mono hKG
    refine ⟨?_, ?_, ?_⟩
    · rw [chain_append, chain_append, fineEnd_append, hfe]
      refine ⟨⟨hpre.mono hKG subset_rfl, ?_⟩, ?_⟩
      · rw [chain_congr h0, Q.coordHier_eq]
        exact Q.chain_coordFrom e hS hb 0 r (by omega)
      · rw [← chain_congr htop]
        exact hpost.mono hKG subset_rfl
    · have ht := Q.tower.top.mono hKG subset_rfl
      rw [fineEnd_append, fineEnd_cons] at ht
      rw [fineEnd_append, fineEnd_append, hfe]
      intro a ha w hw hwa
      exact (fineEnd_congr htop Q.post a ha w hw).1 (ht a ha w hw hwa)
    · obtain ⟨hcpre, hctop, hcpost⟩ := caps_append.1 Q.tower.caps
      rw [caps_append, caps_append, fineEnd_append, hfe]
      refine ⟨⟨hcpre.mono hKG subset_rfl, ?_⟩, ?_⟩
      · rw [caps_congr hDK h0, Q.coordHier_eq]
        refine Q.caps_coordFrom e hS hb (fun a ha => ?_) 0 r (by omega)
        exact (capAt_congr S.dom_inv h0).1 (hctop a ha)
      · rw [← caps_congr hDK htop]
        exact hcpost.mono hKG subset_rfl

end DispatchStep

end GI.Algorithm
