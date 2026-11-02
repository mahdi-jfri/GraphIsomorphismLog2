import Workspace.Impl.TermGlue
import Workspace.Impl.TermRecSpec

/-!
# One radical coset of the row terminal: the mathematics (T5 inside `TermCosetSpec`)

Corollary A.22 solves the type multisets of the two strings inside one coset `R r` of the
radical preimage `R`, by Theorem A.20 on a solvable supplement `S` of `N` in `R` (Lemma A.19).
Theorem A.20 works on coset objects (`CObj`), so the types (the `N`-orbits of the rows) must
first be written as coset objects. This file proves that the objects a program builds from the
coset table `Iso_H(x_i, y_j)` have the same transporters as the types, and that the transporter
inside `R r` is read off from the transporter in `S`.

**Types as coset objects.** Fix a class representative `z` (a row of `y`). A type `t` in the
`H`-orbit of `[z]_N` is sent to the set `{g ∈ H : z^g ∈ t}` (`tmCsCarry`). This map is
`H`-equivariant (`tmCs_carry_act`) and injective on these types (`tmCs_carry_inj`), and the set
is the right coset `(Aut_H(z) N) h` for any `h ∈ H` with `z^h ∈ t` (`tmCs_carry_orbit`). The
color of a type is the least index `j` with `y_j` in its `H`-class (`tmCsStar`); different
classes get different colors. So the map `tmCsF` on all types is equivariant and injective on
the types that occur, and transporters are kept (`tmCs_iso_map`). The program needs only the
table `Iso_H(x_i, y_j)`: the colors come from which entries are empty, the group `Aut_H(y_j)`
from the generators of an entry (`tmCs_gens_aut`), and the coset representative from its
element. A row with no partner on the other side makes the transporter empty
(`tmCs_partner_x`, `tmCs_partner_y`).

**The radical coset** (`tmCs_res_eq`). With `R ⊴ H` (`tmCs_rad_normalizes`), `R = N S` and `N`
fixing the objects: `Iso_H(X, Y) ∩ R r = r · Iso_S(X^r, Y) · N`. When `Iso_S(X^r, Y)` is the
coset `x ⟨gs⟩`, this is the coset `(r x) ⟨gs, N⟩` (`tmCs_res_coset`). This is the paper's
"restrict to `S` ... at the end, adjoining `N` recovers the full transporter".
-/

namespace GI.Impl

open GI.Multicoset Equiv
open GI.Cited (gens)

/-! ### Types as coset objects -/

section Carry

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω]

/-- The elements of `H` that carry `z` into the set `t`. -/
def tmCsCarry (H : Subgroup G) (z : Ω) (t : Set Ω) : Set G := {g | g ∈ H ∧ z ↼ g ∈ t}

/-- **Equivariance**: for `k ∈ H`, the carriers into `t^k` are the carriers into `t`, times `k`. -/
theorem tmCs_carry_act {H : Subgroup G} {z : Ω} {t : Set Ω} {k : G} (hk : k ∈ H) :
    tmCsCarry H z (t ↼ k) = (fun g => g * k) '' tmCsCarry H z t := by
  ext g
  simp only [tmCsCarry, set_act_def, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hg, w, hw, he⟩
    refine ⟨g * k⁻¹, ⟨H.mul_mem hg (H.inv_mem hk), ?_⟩, by group⟩
    have : z ↼ (g * k⁻¹) = w := by
      rw [← act_act, ← he, act_act, mul_inv_cancel, act_one]
    rw [this]; exact hw
  · rintro ⟨g', ⟨hg', hw⟩, rfl⟩
    exact ⟨H.mul_mem hg' hk, _, hw, by rw [act_act]⟩

/-- **The carrier set is a coset**: if every element of `L` is `a n` with `a ∈ Aut_H(z)`,
`n ∈ N`, and conversely, then the carriers of `z` into `[w]_N` are `L h` for any `h ∈ H` with
`z^h = w`. -/
theorem tmCs_carry_orbit {H N L : Subgroup G} (hNH : N ≤ H) (hn : Normalizes H N)
    {z w : Ω} {h : G} (hh : h ∈ H) (hzw : z ↼ h = w)
    (hL : ∀ x, x ∈ L ↔ ∃ a ∈ Aut H z, ∃ n ∈ N, x = a * n) :
    tmCsCarry H z (orbitN N w) = (fun l => l * h) '' (L : Set G) := by
  ext g
  simp only [tmCsCarry, orbitN, Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨hg, n, hnN, he⟩
    have hgH : g * (h * n)⁻¹ ∈ H := H.mul_mem hg (H.inv_mem (H.mul_mem hh (hNH hnN)))
    have hgA : g * (h * n)⁻¹ ∈ Aut H z := by
      refine ⟨hgH, ?_⟩
      rw [← act_act, ← he, ← hzw, act_act, act_act]
      have : h * (n * (h * n)⁻¹) = 1 := by group
      rw [this, act_one]
    refine ⟨g * h⁻¹, (hL _).2 ⟨_, hgA, h * n * h⁻¹, hn h hh n hnN, by group⟩, by group⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨a, ha, n, hnN, rfl⟩ := (hL l).1 hl
    refine ⟨H.mul_mem (H.mul_mem ha.1 (hNH hnN)) hh, h⁻¹ * n * h, hn.inv hh hnN, ?_⟩
    rw [← hzw, act_act, show a * n * h = a * (n * h) by group, ← act_act z a, ha.2]
    congr 1
    group

/-- **Injectivity on the types of one class.** -/
theorem tmCs_carry_inj {H N : Subgroup G} {z w w' : Ω} {h : G} (hh : h ∈ H) (hzw : z ↼ h = w)
    (he : tmCsCarry H z (orbitN N w) = tmCsCarry H z (orbitN N w')) :
    orbitN N w = orbitN N w' := by
  have hm : h ∈ tmCsCarry H z (orbitN N w) := ⟨hh, 1, N.one_mem, by rw [act_one, hzw]⟩
  rw [he] at hm
  obtain ⟨-, n, hn, hw⟩ := hm
  rw [← hzw, ← hw, orbitN_kernel hn]

end Carry

/-! ### Equivariant maps keep transporters -/

section Map

variable {G : Type*} [Group G] {Ω₁ Ω₂ : Type*} [RAct G Ω₁] [RAct G Ω₂]

/-- **An equivariant map, injective on an invariant set holding all objects, keeps
transporters.** -/
theorem tmCs_iso_map [Nonempty Ω₁] {H : Subgroup G} {F : Ω₁ → Ω₂} {D : Set Ω₁}
    (hD : ∀ t ∈ D, ∀ k ∈ H, t ↼ k ∈ D) (hF : ∀ t ∈ D, ∀ k ∈ H, F (t ↼ k) = F t ↼ k)
    (hinj : Set.InjOn F D) {X Y : Multiset Ω₁} (hX : ∀ t ∈ X, t ∈ D) (hY : ∀ t ∈ Y, t ∈ D) :
    Iso H (X.map F) (Y.map F) = Iso H X Y := by
  ext h
  simp only [mem_iso]
  refine and_congr_right fun hh => ?_
  have hmap : X.map F ↼ h = (X ↼ h).map F := by
    rw [multiset_act_def, multiset_act_def, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun t ht => (hF t (hX t ht) h hh).symm
  rw [hmap]
  constructor
  · intro he
    have hXh : ∀ t ∈ X ↼ h, t ∈ D := by
      intro t ht
      rw [multiset_act_def, Multiset.mem_map] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact hD s (hX s hs) h hh
    have back : ∀ Z : Multiset Ω₁, (∀ t ∈ Z, t ∈ D) →
        (Z.map F).map (Function.invFunOn F D) = Z := by
      intro Z hZ
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id Z]
      exact Multiset.map_congr rfl fun t ht => hinj.leftInvOn_invFunOn (hZ t ht)
    rw [← back _ hXh, ← back _ hY, he]
  · intro he; rw [he]

end Map

/-! ### Colors: the least row of `y` in the class -/

section Class

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω] (H N : Subgroup G) {q : ℕ}
  (y : Fin q → Ω)

/-- `t` is the type of an `H`-image of the row `y_j`. -/
def tmCsIn (j : ℕ) (t : Set Ω) : Prop := ∃ hj : j < q, ∃ h ∈ H, t = orbitN N (y ⟨j, hj⟩ ↼ h)

open Classical in
/-- The color of a type: the least `j` with `t` in the class of `y_j` (`q` if there is none). -/
noncomputable def tmCsStar (t : Set Ω) : ℕ :=
  if hx : ∃ j, tmCsIn H N y j t then Nat.find hx else q

open Classical in
/-- **A type as a coset object**: the color `j = tmCsStar t` and the carriers of `y_j` into `t`. -/
noncomputable def tmCsF (t : Set Ω) : CObj ℕ G :=
  ⟨tmCsStar H N y t, if hj : tmCsStar H N y t < q then tmCsCarry H (y ⟨_, hj⟩) t else ∅⟩

/-- The types of the `H`-images of the rows of `y`. -/
def tmCsD : Set (Set Ω) := {t | ∃ j, tmCsIn H N y j t}

variable {H N y}

theorem tmCsIn_act (hn : Normalizes H N) {k : G} (hk : k ∈ H) {j : ℕ} {t : Set Ω} :
    tmCsIn H N y j (t ↼ k) ↔ tmCsIn H N y j t := by
  have one : ∀ {t : Set Ω} {k : G}, k ∈ H → tmCsIn H N y j t → tmCsIn H N y j (t ↼ k) := by
    rintro t k hk ⟨hj, h, hh, rfl⟩
    exact ⟨hj, h * k, H.mul_mem hh hk, by rw [orbitN_act hn hk, act_act]⟩
  refine ⟨fun h => ?_, one hk⟩
  have := one (H.inv_mem hk) h
  rwa [act_act, mul_inv_cancel, act_one] at this

theorem tmCsStar_act (hn : Normalizes H N) {k : G} (hk : k ∈ H) (t : Set Ω) :
    tmCsStar H N y (t ↼ k) = tmCsStar H N y t := by
  classical
  have he : ∀ j, tmCsIn H N y j (t ↼ k) ↔ tmCsIn H N y j t := fun j => tmCsIn_act hn hk
  unfold tmCsStar
  by_cases hx : ∃ j, tmCsIn H N y j t
  · have hx' : ∃ j, tmCsIn H N y j (t ↼ k) := by
      obtain ⟨j, hj⟩ := hx; exact ⟨j, (he j).2 hj⟩
    rw [dif_pos hx, dif_pos hx']
    exact (Nat.find_congr' fun {j} => he j)
  · have hx' : ¬ ∃ j, tmCsIn H N y j (t ↼ k) := fun ⟨j, hj⟩ => hx ⟨j, (he j).1 hj⟩
    rw [dif_neg hx, dif_neg hx']

theorem tmCsStar_spec {j : ℕ} {t : Set Ω} (h : tmCsIn H N y j t) :
    tmCsIn H N y (tmCsStar H N y t) t ∧ tmCsStar H N y t ≤ j := by
  classical
  have hx : ∃ j, tmCsIn H N y j t := ⟨j, h⟩
  unfold tmCsStar
  rw [dif_pos hx]
  exact ⟨Nat.find_spec hx, Nat.find_min' hx h⟩

/-- **The color is the least index of the class.** -/
theorem tmCsStar_eq {j : ℕ} {t : Set Ω} (h : tmCsIn H N y j t)
    (hmin : ∀ j' < j, ¬ tmCsIn H N y j' t) : tmCsStar H N y t = j := by
  obtain ⟨h1, h2⟩ := tmCsStar_spec h
  by_contra hne
  exact hmin _ (lt_of_le_of_ne h2 hne) h1

theorem tmCsD_act (hn : Normalizes H N) : ∀ t ∈ tmCsD H N y, ∀ k ∈ H, t ↼ k ∈ tmCsD H N y := by
  rintro t ⟨j, hj⟩ k hk
  exact ⟨j, (tmCsIn_act hn hk).2 hj⟩

theorem tmCsF_act (hn : Normalizes H N) :
    ∀ t ∈ tmCsD H N y, ∀ k ∈ H, tmCsF H N y (t ↼ k) = tmCsF H N y t ↼ k := by
  intro t _ k hk
  have hs := tmCsStar_act (y := y) hn hk t
  apply CObj.ext
  · exact hs
  · simp only [tmCsF, cobj_act_coset]
    by_cases hq : tmCsStar H N y t < q
    · have hq' : tmCsStar H N y (t ↼ k) < q := hs ▸ hq
      rw [dif_pos hq, dif_pos hq']
      have e : (⟨tmCsStar H N y (t ↼ k), hq'⟩ : Fin q) = ⟨tmCsStar H N y t, hq⟩ := Fin.ext hs
      rw [e, tmCs_carry_act hk]
    · have hq' : ¬ tmCsStar H N y (t ↼ k) < q := hs ▸ hq
      rw [dif_neg hq, dif_neg hq', Set.image_empty]

theorem tmCsF_inj : Set.InjOn (tmCsF H N y) (tmCsD H N y) := by
  rintro t ⟨j, hj⟩ t' ⟨j', hj'⟩ he
  have htag : tmCsStar H N y t = tmCsStar H N y t' := congrArg CObj.tag he
  obtain ⟨⟨hc, h, hh, ht⟩, -⟩ := tmCsStar_spec hj
  obtain ⟨⟨hc', h', hh', ht'⟩, -⟩ := tmCsStar_spec hj'
  have hco := congrArg CObj.coset he
  simp only [tmCsF] at hco
  rw [dif_pos hc, dif_pos hc'] at hco
  have e : (⟨tmCsStar H N y t', hc'⟩ : Fin q) = ⟨tmCsStar H N y t, hc⟩ := Fin.ext htag.symm
  rw [e] at hco ht'
  set yc := y ⟨tmCsStar H N y t, hc⟩
  clear_value yc
  rw [ht, ht'] at hco ⊢
  exact tmCs_carry_inj hh rfl hco

/-- **Membership in a class from the coset table**: the type of `w` is in the class of `y_j`
exactly when `Iso_H(w, y_j)` is nonempty. -/
theorem tmCs_in_iff (hNH : N ≤ H) (w : Ω) (j : Fin q) :
    tmCsIn H N y j (orbitN N w) ↔ (Iso H w (y j)).Nonempty := by
  constructor
  · rintro ⟨_, h, hh, he⟩
    have hw : w ∈ orbitN N w := ⟨1, N.one_mem, act_one w⟩
    rw [he] at hw
    obtain ⟨n, hn, hw⟩ := hw
    refine ⟨(h * n)⁻¹, H.inv_mem (H.mul_mem hh (hNH hn)), ?_⟩
    rw [← hw, act_act, act_act, show h * (n * (h * n)⁻¹) = 1 by group, act_one]
  · rintro ⟨g, hg, hgw⟩
    refine ⟨j.2, g⁻¹, H.inv_mem hg, ?_⟩
    rw [← hgw, act_act, mul_inv_cancel, act_one]

/-- Two rows of `y` linked to one row `x_i` are in one class. -/
theorem tmCs_in_iff_y (hNH : N ≤ H) {w : Ω} {j j' : Fin q} {g : G}
    (hg : g ∈ Iso H w (y j)) :
    tmCsIn H N y j' (orbitN N (y j)) ↔ (Iso H w (y j')).Nonempty := by
  rw [tmCs_in_iff hNH]
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g * g', iso_comp hg hg'⟩
  · rintro ⟨g', hg'⟩
    exact ⟨g⁻¹ * g', iso_comp (iso_inv hg) hg'⟩

end Class

/-! ### Rows without partner -/

section Partner

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω] {H N : Subgroup G} {q : ℕ}
  {x y : Fin q → Ω}

/-- **A transporter of the types links every row of `x` to a row of `y`.** -/
theorem tmCs_partner_x (hNH : N ≤ H) (hn : Normalizes H N) {h : G}
    (hh : h ∈ Iso H (types N x) (types N y)) (i : Fin q) : ∃ j, (Iso H (x i) (y j)).Nonempty := by
  have hm : orbitN N (x i) ↼ h ∈ types N y := by
    rw [← hh.2]; exact act_mem_act h (Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩)
  rw [orbitN_act hn hh.1] at hm
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hm
  have hy : y j ∈ orbitN N (y j) := ⟨1, N.one_mem, act_one _⟩
  rw [hj] at hy
  obtain ⟨n, hn', he⟩ := hy
  exact ⟨j, h * n, H.mul_mem hh.1 (hNH hn'), by rw [← act_act, he]⟩

/-- **A transporter of the types links every row of `y` to a row of `x`.** -/
theorem tmCs_partner_y (hNH : N ≤ H) (hn : Normalizes H N) {h : G}
    (hh : h ∈ Iso H (types N x) (types N y)) (j : Fin q) : ∃ i, (Iso H (x i) (y j)).Nonempty := by
  have hm : orbitN N (y j) ∈ types N x ↼ h := by
    rw [hh.2]; exact Multiset.mem_map.2 ⟨j, Finset.mem_univ_val _, rfl⟩
  rw [mem_act, orbitN_act hn (H.inv_mem hh.1)] at hm
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hm
  have hx : x i ∈ orbitN N (x i) := ⟨1, N.one_mem, act_one _⟩
  rw [hi] at hx
  obtain ⟨n, hn', he⟩ := hx
  refine ⟨i, (h⁻¹ * n)⁻¹, H.inv_mem (H.mul_mem (H.inv_mem hh.1) (hNH hn')), ?_⟩
  rw [← he, act_act, act_act, show h⁻¹ * (n * (h⁻¹ * n)⁻¹) = 1 by group, act_one]

end Partner

/-! ### Groups from the coset table -/

section Groups

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω]

/-- **The group of a canonical answer is the stabilizer of the target**: if
`Iso_H(z, w) = x K`, then `K = Aut_H(w)`. -/
theorem tmCs_gens_aut {H K : Subgroup G} {z w : Ω} {x : G}
    (hI : Iso H z w = (fun g => x * g) '' (K : Set G)) (g : G) : g ∈ K ↔ g ∈ Aut H w := by
  have hx : x ∈ Iso H z w := by rw [hI]; exact ⟨1, K.one_mem, mul_one x⟩
  have key : x * g ∈ Iso H z w ↔ g ∈ K := by
    rw [hI]
    constructor
    · rintro ⟨k, hk, he⟩
      rwa [mul_left_cancel he] at hk
    · intro hg; exact ⟨g, hg, rfl⟩
  rw [← key, mem_iso, mem_aut]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using H.mul_mem (H.inv_mem hx.1) h1, ?_⟩
    rw [← act_act, hx.2] at h2; exact h2
  · rintro ⟨h1, h2⟩
    exact ⟨H.mul_mem hx.1 h1, by rw [← act_act, hx.2, h2]⟩

end Groups

section PermGroups

variable {n : ℕ}

/-- **The group `Aut_H(z) N` of an object**: generators of `Aut_H(z)` followed by generators of
`N` generate exactly the products `a n`. -/
theorem tmCs_mem_gens_append {H N : Subgroup (Perm (Fin n))} {Ω : Type*}
    [RAct (Perm (Fin n)) Ω] {z : Ω} (hn : Normalizes H N) {σA σN : List (Perm (Fin n))}
    (hA : gens σA = Aut H z) (hN : gens σN = N) (x : Perm (Fin n)) :
    x ∈ gens (σA ++ σN) ↔ ∃ a ∈ Aut H z, ∃ m ∈ N, x = a * m := by
  constructor
  · intro hx
    refine closure_mem_mul (hn.mono (aut_le H z)) ?_ x hx
    intro γ hγ
    rcases List.mem_append.1 hγ with h | h
    · refine ⟨γ, ?_, 1, N.one_mem, by simp⟩
      rw [← hA]; exact Subgroup.subset_closure h
    · refine ⟨1, (Aut H z).one_mem, γ, ?_, by simp⟩
      rw [← hN]; exact Subgroup.subset_closure h
  · rintro ⟨a, ha, m, hm, rfl⟩
    have h1 : gens σA ≤ gens (σA ++ σN) :=
      Subgroup.closure_mono fun g hg => List.mem_append_left _ hg
    have h2 : gens σN ≤ gens (σA ++ σN) :=
      Subgroup.closure_mono fun g hg => List.mem_append_right _ hg
    rw [← hA] at ha; rw [← hN] at hm
    exact Subgroup.mul_mem _ (h1 ha) (h2 hm)

/-- **The coset of the residual answer**: `r · x⟨σ⟩ · N = (r x) ⟨σ, σN⟩`. -/
theorem tmCs_res_coset {S N : Subgroup (Perm (Fin n))} {σ σN : List (Perm (Fin n))}
    (hσS : gens σ ≤ S) (hSN : Normalizes S N) (hN : gens σN = N) {I : Set (Perm (Fin n))}
    {x0 r : Perm (Fin n)} (hI : I = (fun g => x0 * g) '' (gens σ : Set (Perm (Fin n)))) :
    {h | ∃ s ∈ I, ∃ m ∈ N, h = r * s * m} =
      (fun g => r * x0 * g) '' (gens (σ ++ σN) : Set (Perm (Fin n))) := by
  subst hI
  have h1 : gens σ ≤ gens (σ ++ σN) :=
    Subgroup.closure_mono fun g hg => List.mem_append_left _ hg
  have h2 : gens σN ≤ gens (σ ++ σN) :=
    Subgroup.closure_mono fun g hg => List.mem_append_right _ hg
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, m, hm, rfl⟩
    rw [← hN] at hm
    exact ⟨g * m, Subgroup.mul_mem _ (h1 hg) (h2 hm), by group⟩
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨k, hk, a, ha, rfl⟩ := closure_mem_mul (K := gens σ) (A := N) (hSN.mono hσS)
      (fun γ hγ => by
        rcases List.mem_append.1 hγ with h | h
        · exact ⟨γ, Subgroup.subset_closure h, 1, N.one_mem, by simp⟩
        · exact ⟨1, (gens σ).one_mem, γ, by rw [← hN]; exact Subgroup.subset_closure h,
            by simp⟩) g' hg'
    exact ⟨x0 * k, ⟨k, hk, rfl⟩, a, ha, by group⟩

end PermGroups

/-! ### The radical coset -/

section Res

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω]

/-- **The radical preimage is normal in `H`.** -/
theorem tmCs_rad_normalizes [Finite G] {H N : Subgroup G} (hn : Normalizes H N) :
    Normalizes H (radicalPreimage H N) := by
  haveI hN := normal_of_normalizes hn
  rw [radicalPreimage, dif_pos hN]
  rintro h hh _ ⟨y, hy, rfl⟩
  refine ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap] at hy ⊢
  simpa using (GI.RadicalSocle.solvableRadical_normal).conj_mem _ hy
    (QuotientGroup.mk' (N.subgroupOf H) ⟨h, hh⟩)

/-- **Corollary A.22 in one radical coset, through a supplement**: the transporters in `R r`
are `r · Iso_S(X^r, Y) · N`. -/
theorem tmCs_res_eq {H N R S : Subgroup G} (hRH : R ≤ H) (hRn : Normalizes H R) (hSR : S ≤ R)
    (hNR : N ≤ R) (hcov : ∀ x ∈ R, ∃ n ∈ N, ∃ s ∈ S, x = n * s) (hSN : Normalizes S N)
    {X Y : Multiset Ω} {r : G} (hr : r ∈ H) (hfX : Fixes N (X ↼ r)) (hfY : Fixes N Y) :
    {h | h ∈ Iso H X Y ∧ ∃ x ∈ R, h = x * r} =
      {h | ∃ s ∈ Iso S (X ↼ r) Y, ∃ m ∈ N, h = r * s * m} := by
  have hiso := iso_eq_kernel_mul_supplement (Y := Y) hNR hSR hcov hfX
  ext h
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hh, x, hx, rfl⟩
    have hy : r⁻¹ * x * r ∈ Iso R (X ↼ r) Y := by
      refine ⟨by simpa using hRn.inv hr hx, ?_⟩
      rw [act_act, show r * (r⁻¹ * x * r) = x * r by group]
      exact hh.2
    rw [hiso] at hy
    obtain ⟨m, hm, s, hs, he⟩ := hy
    refine ⟨s, hs, s⁻¹ * m * s, hSN.inv hs.1 hm, ?_⟩
    have : x = r * (m * s) * r⁻¹ := by rw [← he]; group
    rw [this]; group
  · rintro ⟨s, hs, m, hm, rfl⟩
    have hsR := hSR hs.1
    refine ⟨⟨H.mul_mem (H.mul_mem hr (hRH hsR)) (hRH (hNR hm)), ?_⟩,
      r * (s * m) * r⁻¹, hRn r hr _ (R.mul_mem hsR (hNR hm)), by group⟩
    rw [← act_act, ← act_act, hs.2, hfY.act_eq hm]

end Res

/-! ### The listed objects -/

section Objs

variable {n : ℕ} {Ω : Type*} [RAct (Perm (Fin n)) Ω]

/-- **A listed object is the coset object of its type**: color `c` the class index, group
`Aut_H(y_c) N`, representative `h` with `y_c^h = w`. -/
theorem tmCs_obj_eq {H N : Subgroup (Perm (Fin n))} (hNH : N ≤ H) (hn : Normalizes H N) {q : ℕ}
    {y : Fin q → Ω} {w : Ω} {c : ℕ} (hc : c < q) (hstar : tmCsStar H N y (orbitN N w) = c)
    {σL : List (Perm (Fin n))}
    (hL : ∀ x, x ∈ gens σL ↔ ∃ a ∈ Aut H (y ⟨c, hc⟩), ∃ m ∈ N, x = a * m)
    {h : Perm (Fin n)} (hh : h ∈ H) (hzw : y ⟨c, hc⟩ ↼ h = w) :
    tmGlObj c σL h = tmCsF H N y (orbitN N w) := by
  subst hstar
  apply CObj.ext
  · rfl
  · simp only [tmCsF, tmGlObj]
    rw [dif_pos hc, tmCs_carry_orbit hNH hn hh hzw hL]

/-- The multiset of a list of objects indexed by the rows. -/
theorem tmCs_ms_rows {q : ℕ} (f : Fin q → ℕ × List (Perm (Fin n)) × Perm (Fin n))
    {F : Set Ω → CObj ℕ (Perm (Fin n))} {x : Fin q → Ω} {N : Subgroup (Perm (Fin n))}
    (hf : ∀ i, tmGlObj (f i).1 (f i).2.1 (f i).2.2 = F (orbitN N (x i))) :
    tmGlMs ((List.finRange q).map f) = (types N x).map F := by
  unfold tmGlMs types
  rw [Multiset.map_map, List.map_map]
  rw [show (Finset.univ : Finset (Fin q)).val = ((List.finRange q : List (Fin q)) : Multiset (Fin q))
    from rfl]
  rw [Multiset.map_coe]
  congr 1
  exact List.map_congr_left fun i _ => hf i

/-- Shifting every representative by `r` acts by `r` on the multiset. -/
theorem tmCs_ms_shift (X : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))) (r : Perm (Fin n)) :
    tmGlMs (X.map fun o => (o.1, o.2.1, o.2.2 * r)) = tmGlMs X ↼ r := by
  unfold tmGlMs
  rw [multiset_act_def, Multiset.map_coe, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun o _ => ?_
  apply CObj.ext
  · rfl
  · simp only [Function.comp_apply, tmGlObj, cobj_act_coset, Set.image_image, mul_assoc]

/-- **The residual transporter in one radical coset from the listed objects** (Corollary A.22
through Lemma A.19): if the listed objects are the coset objects of the types and every row of
`x` has a partner in `y`, the transporters of the types inside `R r` are
`r · Iso_S(X^r, Y) · N`. -/
theorem tmCs_res_main {q : ℕ} {H N R S : Subgroup (Perm (Fin n))} (hNH : N ≤ H)
    (hn : Normalizes H N) (hRH : R ≤ H) (hRn : Normalizes H R) (hSR : S ≤ R) (hNR : N ≤ R)
    (hcov : ∀ z ∈ R, ∃ m ∈ N, ∃ s ∈ S, z = m * s) (hSN : Normalizes S N)
    {x y : Fin q → Ω} {OX OY : List (ℕ × List (Perm (Fin n)) × Perm (Fin n))}
    (hOX : tmGlMs OX = (types N x).map (tmCsF H N y))
    (hOY : tmGlMs OY = (types N y).map (tmCsF H N y))
    (hpart : ∀ i, ∃ j, (Iso H (x i) (y j)).Nonempty) {r : Perm (Fin n)} (hr : r ∈ H) :
    {h | h ∈ Iso H (types N x) (types N y) ∧ ∃ z ∈ R, h = z * r} =
      {h | ∃ s ∈ Iso S (tmGlMs OX ↼ r) (tmGlMs OY), ∃ m ∈ N, h = r * s * m} := by
  have hDx : ∀ t ∈ types N x, t ∈ tmCsD H N y := by
    intro t ht
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ht
    obtain ⟨j, hj⟩ := hpart i
    exact ⟨j, (tmCs_in_iff hNH (x i) j).2 hj⟩
  have hDy : ∀ t ∈ types N y, t ∈ tmCsD H N y := by
    intro t ht
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ht
    exact ⟨j, (tmCs_in_iff hNH (y j) j).2 ⟨1, H.one_mem, act_one _⟩⟩
  have hfix : ∀ {Z : Multiset (Set Ω)}, (∀ t ∈ Z, t ∈ tmCsD H N y) → Fixes N Z →
      Fixes N (Z.map (tmCsF H N y)) := by
    intro Z hZ hfZ m hm o ho
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 ho
    rw [← tmCsF_act hn t (hZ t ht) m (hNH hm), hfZ m hm t ht]
  have hiso := tmCs_iso_map (H := H) (tmCsD_act hn) (tmCsF_act hn) tmCsF_inj hDx hDy
  rw [← hiso, ← hOX, ← hOY]
  refine tmCs_res_eq hRH hRn hSR hNR hcov hSN hr ?_ ?_
  · rw [hOX]; exact (hfix hDx (fixes_types N x)).act hn hr
  · rw [hOY]; exact hfix hDy (fixes_types N y)

end Objs

end GI.Impl
