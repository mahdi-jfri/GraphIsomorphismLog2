module

public import Workspace.Impl.TermGlueLabPItem
public import Workspace.Impl.TermGlueLabPYLab
public import Workspace.Impl.TermGlueLabPOr
public import Workspace.Impl.TermGlueLabLift

@[expose] public section

/-!
# The two label vectors of step 6: the mathematics

Proof of Theorem A.23: the affine call of step 6 compares the label point of `x`
with the label point of the aligned target `y'`, both read in the coordinates `E` of the torsor
(`tmGL_contract_trans(')`). Here we say which vectors these are, in terms of data the label
program already has.

For a string `z` with the type multiset of `x`, the label program holds one pair `[J_k, a_k]`
per row: `J_k` is the first row of `x` of the type of `z_k`, and `x_{J_k}^{a_k} = z_k` with
`a_k ∈ N` (`TmGLSEnt`). For `z = x` these are the pairs of `tmGLPXLab_spec`
(`tmGLS_ent_x`), and for `z = y'` the search results of `tmGLPYLab_spec` (`tmGLS_ent_y`).

* `tmGLS_lab_vec`: if `zs` are coordinate vectors of `1, a_0, …, a_{q-1}`, then
  `(Σ zs) V mod d` is the vector `E(s(z))` of the label of `z` (with the first-row
  representatives `tmGLPRep`). This is the vector of `tmGLS_call'`.
* `tmGLS_or_perm`: with distinct types, `k ↦ J_k` is a permutation `ρ`, and the orientation
  of `z` is `sign ρ`. Its parity `itpNInv ρ % 2` is the orientation coordinate.
* `tmGLS_pt_vec`: with the orientation coordinate in front (`tmGLPEo`, moduli
  `Fin.cons 2 (tmGLQMod D)`), the vector of the label point `(s(z), o(z))` is the list
  `encInt (itpNInv ρ % 2) :: (Σ zs) V mod d`. This is the vector of `tmGLS_call`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens encInt)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}

/-! ### The pairs of a string -/

/-- **The pairs of `z`**: one entry `[J_k, a_k]` per row, `J_k` the first row of `x` of the type
of `z_k`, `a_k ∈ N` and `x_{J_k}^{a_k} = z_k`. -/
def TmGLSEnt (N : Subgroup (Perm (Fin n))) (X Z : Fin q → Ω) (l : List Val) : Prop :=
  l.length = q ∧ ∀ k : Fin q, ∃ J : Fin q, ∃ x ∈ N,
    l[k.1]? = some (.list [.nat J, encPerm x]) ∧ TmGLPFirst N X (Z k) J ∧ X J ↼ x = Z k

/-- The pairs of `tmGLPXLab_spec` are the pairs of `x`. -/
theorem tmGLS_ent_x {N : Subgroup (Perm (Fin n))} {X : Fin q → Ω} {l : List Val}
    (h : TmGLPXOut N X (.list l)) : TmGLSEnt N X X l := by
  obtain ⟨l', hl', hlen, hk⟩ := h
  cases hl'
  refine ⟨hlen, fun k => ?_⟩
  obtain ⟨v, hv, J, x, hx, rfl, hJ, hxk⟩ := hk k
  exact ⟨J, x, hx, hv, hJ, hxk⟩

/-- **The search results of `tmGLPYLab_spec` are the pairs of `z`**, when `z` has the type
multiset of `x`: then no search fails, since every row of `z` lies in the `N`-orbit of a row
of `x`. -/
theorem tmGLS_ent_y {N : Subgroup (Perm (Fin n))} {X Z : Fin q → Ω} {l : List Val}
    (h : TmGLPYOut N X Z (.list l)) (hz : types N Z = types N X) : TmGLSEnt N X Z l := by
  obtain ⟨l', hl', hlen, hk⟩ := h
  cases hl'
  refine ⟨hlen, fun k => ?_⟩
  obtain ⟨v, hv, hf⟩ := hk k
  rcases hf with ⟨-, hno⟩ | ⟨j, x, hx, rfl, hxZ, hmin⟩
  · -- the type of `z_k` is the type of some row `x_j`
    have hmem : orbitN N (Z k) ∈ types N X := by
      rw [← hz]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val k)
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
    have hZ : Z k ∈ orbitN N (X j) := by rw [hj]; exact tmGLP_self_mem N (Z k)
    obtain ⟨c, hc, hce⟩ := hZ
    exact absurd hce (hno j c hc)
  · exact ⟨j, x, hx, hv, tmGLP_first_of_find hx hxZ hmin, hxZ⟩

/-- The first rows and the elements of the pairs, as functions of the row. -/
theorem tmGLS_ent_choose {N : Subgroup (Perm (Fin n))} {X Z : Fin q → Ω} {l : List Val}
    (h : TmGLSEnt N X Z l) : ∃ J : Fin q → Fin q, ∃ a : Fin q → Perm (Fin n),
      (∀ k, a k ∈ N) ∧ (∀ k : Fin q, l[k.1]? = some (Val.list [.nat (J k), encPerm (a k)])) ∧
      (∀ k, TmGLPFirst N X (Z k) (J k)) ∧ ∀ k, X (J k) ↼ a k = Z k := by
  choose J a ha hl hJ haz using h.2
  exact ⟨J, a, ha, hl, hJ, haz⟩

/-! ### The label vector -/

variable {A : Type*} [CommGroup A]

/-- **The label vector.** Let `E` be coordinates of `A/B(x)` with `E(class of w) = w V mod D`
(`tmGLPE_g`). If row `z_k` is `x_{J_k}^{a_k}` with `J_k` the first row of its type and `zs` are
coordinate vectors of `1, a_0, …, a_{q-1}`, then `(Σ zs) V mod D` is the vector of `E(s(z))`,
the label of `z` with the first-row representatives. -/
theorem tmGLS_lab_vec {N : Subgroup (Perm (Fin n))} {φ : N →* A} {X Z : Fin q → Ω}
    (j0 : Fin q) {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (E : Additive (tmGLV N φ X) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ w, E (tmGLPg N φ X (fun i => σN[i.val]) w) = tmGLQMap V D w)
    (hz : types N Z = types N X) {J : Fin q → Fin q} {a : Fin q → Perm (Fin n)}
    (ha : ∀ k, a k ∈ N) (hJ : ∀ k, TmGLPFirst N X (Z k) (J k)) (haz : ∀ k, X (J k) ↼ a k = Z k)
    {zs : List (Fin σN.length → ℤ)} (hzs : List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs) :
    (fun i => Matrix.vecMul zs.sum V i % D i i) =
      tmGLVecZ (E (Additive.ofMul (tmGLLab N φ X (tmGLPRep N X j0) Z))) := by
  have hx : ∀ y ∈ List.ofFn a, y ∈ gens σN := by
    intro y hy
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
    rw [hN]; exact ha k
  have hp : (∏ k, tmGLc N φ X (a k)) = ((List.ofFn a).map (tmGLc N φ X)).prod := by
    rw [List.map_ofFn, List.prod_ofFn]; rfl
  rw [tmGLP_lab_of_first j0 hz ha hJ haz, hp, ← tmGLP_csum_class' hN hx hzs, hE, tmGLP_vecZ hpos]

/-! ### The orientation -/

/-- **The orientation from the pairs.** With distinct types, `k ↦ J_k` is a permutation `ρ`
(two rows with the same first row have the same type, hence are equal), and the orientation
of `z` is `sign ρ`: the matching `π = ρ⁻¹` has `type(z_{π i}) = type(x_i)`, and
`sign ρ⁻¹ = sign ρ`. -/
theorem tmGLS_or_perm {N : Subgroup (Perm (Fin n))} {X Z : Fin q → Ω}
    (hT : (types N X).Nodup) (hz : types N Z = types N X) {J : Fin q → Fin q}
    (hJ : ∀ k, TmGLPFirst N X (Z k) (J k)) :
    ∃ ρ : Perm (Fin q), (∀ k, ρ k = J k) ∧ tmGLOr N X Z = sign ρ := by
  have ho : ∀ k, orbitN N (Z k) = orbitN N (X (J k)) := fun k => tmGLP_orbit_eq (hJ k).1
  have hinj : Function.Injective J := by
    intro k k' he
    refine tmGL_types_inj hz hT ?_
    rw [ho, ho, he]
  set ρ := Equiv.ofBijective J (Finite.injective_iff_bijective.mp hinj)
  have hρ : ∀ k, ρ k = J k := fun _ => rfl
  refine ⟨ρ, hρ, ?_⟩
  have hπ : ∀ i, orbitN N (Z (ρ⁻¹ i)) = orbitN N (X i) := by
    intro i
    rw [ho, ← hρ, Perm.apply_inv_self]
  rw [tmGLOr_eq hz hT hπ, sign_inv]

/-- The orientation coordinate: the parity of `ρ`, as an integer, is the value of
`tmGLPUnits (sign ρ)` (from `tmGLP_par_units`). -/
theorem tmGLS_par_val (ρ : Perm (Fin q)) :
    (((tmGLPUnits (Additive.ofMul (sign ρ))).val : ℕ) : ℤ) = ((itpNInv ρ % 2 : ℕ) : ℤ) := by
  rw [← tmGLP_par_units, ZMod.val_natCast, Nat.mod_mod]

/-! ### Vectors with one more coordinate in front -/

/-- The reduced coordinates of `tmGLPCons k m (b, v)` are `b` followed by those of `v`. -/
theorem tmGLS_vecZ_cons {d : ℕ} (k : ℕ) (m : Fin d → ℕ) (b : ZMod k) (v : tmGLVec m) :
    tmGLVecZ (tmGLPCons k m (b, v)) = Fin.cons ((b.val : ℕ) : ℤ) (tmGLVecZ v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [tmGLVecZ, tmGLPCons, ZMod.ringEquivCongr_val]
  · simp [tmGLVecZ, tmGLPCons, ZMod.ringEquivCongr_val]

/-- `linVecVal` of a vector with one more coordinate in front. -/
theorem tmGLS_linVecVal_cons {d : ℕ} (a : ℤ) (f : Fin d → ℤ) :
    linVecVal (Fin.cons a f : Fin (d + 1) → ℤ) =
      .list (encInt a :: (List.finRange d).map fun i => encInt (f i)) := by
  simp only [linVecVal, List.finRange_succ, List.map_cons, List.map_map]
  congr 2

/-- The two bits as integers: `[0, []]` and `[0, [1]]`. -/
theorem tmGLS_bit_enc {b : ℕ} (hb : b < 2) :
    Val.list [.nat 0, if b = 0 then .list [] else .list [.nat 1]] = encInt (b : ℤ) := by
  interval_cases b <;> rfl

/-- The coordinates `tmGLPEo` are `tmGLPCons 2` of the orientation in `ℤ/2` and `E` of the
label. -/
theorem tmGLS_Eo_apply {P : Type*} [Group P] {Ω : Type} [RAct P Ω] {q : ℕ}
    {N : Subgroup P} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}
    {t s : ℕ} {a : Fin t → P} (ha : ∀ i, a i ∈ N) (hgen : N ≤ Subgroup.closure (Set.range a))
    {M : Matrix (Fin t) (Fin t) ℤ}
    (hM : ∀ z, linCoordMap (fun i => phiT N φ (a i)) z = 0 ↔ ∃ y, Matrix.vecMul y M = z)
    {Z : Matrix (Fin s) (Fin t) ℤ}
    (hB : labelGroup N φ x = Subgroup.closure (Set.range fun j =>
        Additive.toMul (linCoordMap (fun i => phiT N φ (a i)) (Z j))))
    {V D : Matrix (Fin t) (Fin t) ℤ} (hV : IsUnit V.det) (hpos : ∀ i, 0 < D i i)
    (hrel : ∀ w, (∃ y, Matrix.vecMul y (tmGLQStack M Z) = w) ↔
      ∀ i, D i i ∣ (Matrix.vecMul w V) i) (p : tmGLV N φ x × ℤˣ) :
    tmGLPEo ha hgen hM hB hV hpos hrel (Additive.ofMul p) =
      tmGLPCons 2 (tmGLQMod D) (tmGLPUnits (Additive.ofMul p.2),
        tmGLPE ha hgen hM hB hV hpos hrel (Additive.ofMul p.1)) := rfl

/-- **The vector of a label point.** Let `Ev` put the orientation coordinate (in `ℤ/2`) in front
of `E` (as `tmGLPEo` does, `tmGLS_Eo_apply`). With distinct types, let `ρ` be the permutation
`k ↦ J_k` of `tmGLS_or_perm`. Then the vector of the label point `(s(z), o(z))` is
`encInt (itpNInv ρ % 2)` followed by the vector `(Σ zs) V mod D` of the label. -/
theorem tmGLS_pt_vec {N : Subgroup (Perm (Fin n))} {φ : N →* A} {X Z : Fin q → Ω}
    (j0 : Fin q) {σN : List (Perm (Fin n))} (hN : gens σN = N)
    {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ} (hpos : ∀ i, 0 < D i i)
    (E : Additive (tmGLV N φ X) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ w, E (tmGLPg N φ X (fun i => σN[i.val]) w) = tmGLQMap V D w)
    (Ev : Additive (tmGLV N φ X × ℤˣ) ≃+ tmGLVec (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ))
    (hEv : ∀ p : tmGLV N φ X × ℤˣ, Ev (Additive.ofMul p) =
      tmGLPCons 2 (tmGLQMod D) (tmGLPUnits (Additive.ofMul p.2), E (Additive.ofMul p.1)))
    (hT : (types N X).Nodup) (hz : types N Z = types N X) {J : Fin q → Fin q}
    {a : Fin q → Perm (Fin n)} (ha : ∀ k, a k ∈ N) (hJ : ∀ k, TmGLPFirst N X (Z k) (J k))
    (haz : ∀ k, X (J k) ↼ a k = Z k)
    {zs : List (Fin σN.length → ℤ)} (hzs : List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs)
    {ρ : Perm (Fin q)} (hρ : ∀ k, ρ k = J k) :
    Val.list (encInt ((itpNInv ρ % 2 : ℕ) : ℤ) ::
        (List.finRange σN.length).map fun i => encInt (Matrix.vecMul zs.sum V i % D i i)) =
      linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLPt N φ X (tmGLPRep N X j0) Z)))) := by
  obtain ⟨ρ', hρ', hor⟩ := tmGLS_or_perm hT hz hJ
  have e : ρ' = ρ := Equiv.ext fun k => by rw [hρ', hρ]
  subst e
  rw [hEv, tmGLS_vecZ_cons, tmGLS_linVecVal_cons, tmGLPt, hor, tmGLS_par_val,
    ← tmGLS_lab_vec j0 hN hpos E hE hz ha hJ haz hzs]

end GI.Impl
