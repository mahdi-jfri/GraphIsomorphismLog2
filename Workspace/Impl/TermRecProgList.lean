import Workspace.Impl.TermRecProgMath

/-!
# Lists of objects: pieces, counts and the object test (T5, mathematics)

The program keeps objects in lists. This file relates its list computations to the multisets of
`MulticosetPieces`.

* **Pieces from a list** (`tmRiPcs`, `tmRiPcs_eq`). For a list `L`, the program keeps, for each
  position `i` that is the first position of its orbit (the first `j` with `L_j` in the
  `A`-orbit of `L_i` is `i`), the entries of `L` in the orbit of `L_i`. The multiset of these
  lists is exactly the set `pieces A L` ("Partition `X` and `Y` into pieces"): every piece
  appears once, at the first position of its orbit.
* **Equality of multisets from counts** (`tmRi_ms_eq_iff`): `X = Y` iff `|X| = |Y|` and every
  entry of `X` occurs as often in `X` as in `Y`. This decides the case `ℓ = 0` ("the action is
  trivial, and equality of the multisets decides").
* **The object test** (`tmRi_act_eq_iff`, `tmRi_mem_conj`): for coset objects `L h` and `L h'`
  of one color, `(L h)^g = L h'` iff `g (h'⁻¹ h) ∈ h⁻¹ L h`. So orbit tests and point
  transporters are one coset intersection `G x ∩ K` with the solvable group `G` on the left
  ("`SolvableCosetIntersection`" with `x = h'⁻¹ h`, `K = h⁻¹ L h`).
-/

namespace GI.Impl

open GI.Multicoset Equiv
open GI.Cited (gens)

/-! ### Pieces from a list -/

section Pieces

variable {α : Type} {G : Type} [Group G] {Ω : Type} [RAct G Ω]

/-- The positions `j < i` that are first in their class under the test `q`, and the class of
each, as lists. -/
def tmRiPcs (q : α → α → Bool) (L : List α) (d : α) (i : ℕ) : List (List α) :=
  ((List.range i).filter (fun j => L.findIdx (q (L.getD j d)) == j)).map
    (fun j => L.filter (q (L.getD j d)))

theorem tmRiPcs_zero (q : α → α → Bool) (L : List α) (d : α) : tmRiPcs q L d 0 = [] := rfl

theorem tmRiPcs_succ (q : α → α → Bool) (L : List α) (d : α) (i : ℕ) :
    tmRiPcs q L d (i + 1) = tmRiPcs q L d i ++
      (if L.findIdx (q (L.getD i d)) = i then [L.filter (q (L.getD i d))] else []) := by
  unfold tmRiPcs
  rw [List.range_succ, List.filter_append, List.map_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil, beq_iff_eq, List.getD_eq_getElem?_getD]
  split_ifs <;> simp

theorem tmRi_findIdx_le {p : α → Bool} {L : List α} {i : ℕ} (hi : i < L.length)
    (hp : p L[i] = true) : L.findIdx p ≤ i := by
  by_contra h
  have h3 : p L[i] = false := List.not_of_lt_findIdx (show i < L.findIdx p by omega)
  rw [hp] at h3
  exact Bool.noConfusion h3

open Classical in
/-- **The pieces of a list.** If `q a b` decides that `f a` and `f b` lie in one `A`-orbit, the
classes kept by `tmRiPcs` are the pieces of the multiset `f L`, each once. -/
theorem tmRiPcs_eq (A : Subgroup G) (f : α → Ω) (q : α → α → Bool)
    (hq : ∀ a b, q a b = true ↔ SameOrb A (f a) (f b)) (L : List α) (d : α) :
    (((tmRiPcs q L d L.length).map fun S => ((S.map f : List Ω) : Multiset Ω)) :
      Multiset (Multiset Ω)) = (pieces A ((L.map f : List Ω) : Multiset Ω)).val := by
  set X : Multiset Ω := ((L.map f : List Ω) : Multiset Ω) with hX
  -- the class of an entry is its part
  have hpart : ∀ a, (((L.filter (q a)).map f : List Ω) : Multiset Ω) = partAt A X {f a} := by
    intro a
    rw [partAt, hX, Multiset.filter_coe, List.filter_map]
    congr 2
    apply List.filter_congr
    intro z _
    simp only [Function.comp_apply, Multiset.mem_singleton, exists_eq_left]
    by_cases h : SameOrb A (f a) (f z)
    · simp [h, (hq a z).2 h]
    · have : q a z = false := by
        cases hqz : q a z
        · rfl
        · exact absurd ((hq a z).1 hqz) h
      simp [h, this]
  -- two entries in one orbit test alike
  have hqeq : ∀ a b, q a b = true → q a = q b := by
    intro a b hab
    funext z
    have h1 := (hq a b).1 hab
    apply Bool.eq_iff_iff.2
    rw [hq, hq]
    exact ⟨fun h => h1.symm.trans h, fun h => h1.trans h⟩
  have hrefl : ∀ a, q a a = true := fun a => (hq a a).2 (sameOrb_refl A _)
  have hsymm : ∀ a b, q a b = true → q b a = true := fun a b h => (hq b a).2 ((hq a b).1 h).symm
  have hget : ∀ j (hj : j < L.length), L.getD j d = L[j] := fun j hj => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  unfold tmRiPcs
  rw [List.map_map]
  set I := (List.range L.length).filter (fun j => L.findIdx (q (L.getD j d)) == j) with hI
  have hImem : ∀ j, j ∈ I ↔ j < L.length ∧ L.findIdx (q (L.getD j d)) = j := by
    intro j
    simp [hI]
  apply (Multiset.Nodup.ext _ (pieces A X).nodup).2
  · intro S
    simp only [Multiset.mem_coe, List.mem_map, Function.comp_apply, Finset.mem_val]
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hjl, -⟩ := (hImem j).1 hj
      rw [hpart, mem_pieces]
      refine ⟨f (L.getD j d), ?_, rfl⟩
      rw [hget j hjl, hX, Multiset.mem_coe]
      exact List.mem_map_of_mem (List.getElem_mem hjl)
    · intro hS
      obtain ⟨x, hx, rfl⟩ := mem_pieces.mp hS
      rw [hX, Multiset.mem_coe] at hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
      have hlt : L.findIdx (q L[k]) < L.length :=
        List.findIdx_lt_length.2 ⟨L[k], List.getElem_mem hk, hrefl _⟩
      set i := L.findIdx (q L[k]) with hidef
      have hqi : q L[k] L[i] = true := List.findIdx_getElem
      have he : q L[i] = q L[k] := (hqeq _ _ hqi).symm
      refine ⟨i, (hImem i).2 ⟨hlt, ?_⟩, ?_⟩
      · rw [hget i hlt, he]
      · rw [hget i hlt, he, hpart]
  · rw [Multiset.coe_nodup]
    refine List.Nodup.map_on ?_ (List.Nodup.filter _ List.nodup_range)
    intro i hi j hj hij
    obtain ⟨hil, hfi⟩ := (hImem i).1 hi
    obtain ⟨hjl, hfj⟩ := (hImem j).1 hj
    simp only [Function.comp_apply] at hij
    rw [hget i hil] at hfi hij
    rw [hget j hjl] at hfj hij
    -- `L_j` lies in the class of `L_i`
    have hji : q L[i] L[j] = true := by
      have hm : L[j] ∈ L.filter (q L[j]) := List.mem_filter.2 ⟨List.getElem_mem hjl, hrefl _⟩
      have hm' : f L[j] ∈ (((L.filter (q L[j])).map f : List Ω) : Multiset Ω) :=
        Multiset.mem_coe.2 (List.mem_map_of_mem hm)
      rw [← hij, Multiset.mem_coe] at hm'
      obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hm'
      have h1 := (hq _ _).1 (List.mem_filter.1 hb).2
      rw [hbe] at h1
      exact (hq _ _).2 h1
    have h1 : j ≤ i := hfj ▸ tmRi_findIdx_le hil (hsymm _ _ hji)
    have h2 : i ≤ j := hfi ▸ tmRi_findIdx_le hjl hji
    omega

end Pieces

/-! ### Equality of multisets from counts -/

section Count

variable {α Ω : Type}

open Classical in
/-- **Equal multisets from counts.** If `q a b` decides `f a = f b`, then the images of `X` and
`Y` are equal as multisets iff `|X| = |Y|` and every entry of `X` has as many equal entries in
`X` as in `Y`. -/
theorem tmRi_ms_eq_iff (f : α → Ω) (q : α → α → Bool) (hq : ∀ a b, q a b = true ↔ f a = f b)
    (X Y : List α) :
    (((X.map f : List Ω) : Multiset Ω) = ((Y.map f : List Ω) : Multiset Ω)) ↔
      X.length = Y.length ∧ ∀ x ∈ X, (X.filter (q x)).length = (Y.filter (q x)).length := by
  have hcount : ∀ (Z : List α) (x : α),
      Multiset.count (f x) ((Z.map f : List Ω) : Multiset Ω) = (Z.filter (q x)).length := by
    intro Z x
    rw [Multiset.coe_count, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro z _
    apply Bool.eq_iff_iff.2
    rw [hq]
    simp only [Function.comp_apply, beq_iff_eq]
    exact eq_comm
  constructor
  · intro h
    refine ⟨?_, fun x _ => ?_⟩
    · have := congrArg Multiset.card h
      simpa using this
    · rw [← hcount, ← hcount, h]
  · rintro ⟨hl, hc⟩
    apply Multiset.eq_of_le_of_card_le
    · rw [Multiset.le_iff_count]
      intro a
      by_cases ha : a ∈ ((X.map f : List Ω) : Multiset Ω)
      · rw [Multiset.mem_coe] at ha
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        rw [hcount, hcount, hc x hx]
      · rw [Multiset.count_eq_zero.2 ha]
        exact Nat.zero_le _
    · simp [hl]

end Count

/-! ### The object test -/

section Obj

variable {n : ℕ}

/-- The generators of a conjugate: `⟨s ps s⁻¹⟩ = s ⟨ps⟩ s⁻¹`. -/
theorem tmRi_mem_conj (s : Perm (Fin n)) (ps : List (Perm (Fin n))) (y : Perm (Fin n)) :
    y ∈ gens (ps.map fun x => s * x * s⁻¹) ↔ s⁻¹ * y * s ∈ gens ps := by
  have e : gens (ps.map fun x => s * x * s⁻¹) = (gens ps).map (MulAut.conj s).toMonoidHom := by
    unfold gens
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    simp [MulAut.conj_apply]
  rw [e, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply, mul_assoc]

/-- The action on an encoded object: `(L h)^g = L (h g)`. -/
theorem tmRi_obj_act (c : ℕ) (σL : List (Perm (Fin n))) (h g : Perm (Fin n)) :
    tmGlObj c σL h ↼ g = tmGlObj c σL (h * g) := by
  apply CObj.ext
  · rfl
  · rw [cobj_act_coset]
    simp only [tmGlObj, Set.image_image, mul_assoc]

/-- Two right cosets of one subgroup are equal iff the quotient of the representatives lies in
it. -/
theorem tmRi_rcoset_eq_iff (L : Subgroup (Perm (Fin n))) (a b : Perm (Fin n)) :
    (fun l => l * a) '' (L : Set (Perm (Fin n))) = (fun l => l * b) '' (L : Set (Perm (Fin n))) ↔
      a * b⁻¹ ∈ L := by
  constructor
  · intro h
    have : a ∈ (fun l => l * b) '' (L : Set (Perm (Fin n))) := by
      rw [← h]; exact ⟨1, L.one_mem, one_mul a⟩
    obtain ⟨l, hl, rfl⟩ := this
    simpa using hl
  · intro h
    ext z
    simp only [Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l * (a * b⁻¹), L.mul_mem hl h, by group⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l * (a * b⁻¹)⁻¹, L.mul_mem hl (L.inv_mem h), by group⟩

/-- **The object test.** For objects `L h` and `L' h'` with `⟨L⟩ = ⟨L'⟩` when the colors agree,
`(L h)^g = L' h'` iff the colors agree and `g (h'⁻¹ h) ∈ h⁻¹ L h`, where `h⁻¹ L h` is generated
by the conjugates `h⁻¹ x h` of the generators. -/
theorem tmRi_act_eq_iff {c c' : ℕ} {σL σL' : List (Perm (Fin n))} (hL : c = c' → gens σL = gens σL')
    (h h' g : Perm (Fin n)) :
    tmGlObj c σL h ↼ g = tmGlObj c' σL' h' ↔
      c = c' ∧ g * (h'⁻¹ * h) ∈ gens (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹) := by
  rw [tmRi_obj_act, tmRi_mem_conj]
  constructor
  · intro he
    have hc : c = c' := congrArg CObj.tag he
    have hs := congrArg CObj.coset he
    simp only [tmGlObj] at hs
    rw [← hL hc, tmRi_rcoset_eq_iff] at hs
    refine ⟨hc, ?_⟩
    simpa [mul_assoc] using hs
  · rintro ⟨rfl, hm⟩
    apply CObj.ext
    · rfl
    · simp only [tmGlObj]
      rw [← hL rfl, tmRi_rcoset_eq_iff]
      simpa [mul_assoc] using hm

/-- The stabilizer of an object in `G`: `Aut_G(L h) = G ∩ h⁻¹ L h`. -/
theorem tmRi_mem_aut {c : ℕ} {σL : List (Perm (Fin n))} {h : Perm (Fin n)}
    {G : Subgroup (Perm (Fin n))} (g : Perm (Fin n)) :
    g ∈ Aut G (tmGlObj c σL h) ↔ g ∈ G ⊓ gens (σL.map fun x => h⁻¹ * x * h⁻¹⁻¹) := by
  rw [mem_aut, Subgroup.mem_inf, tmRi_act_eq_iff (fun _ => rfl)]
  simp

end Obj

end GI.Impl
