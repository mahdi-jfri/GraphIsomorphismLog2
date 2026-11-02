import Workspace.CertificateEndpoint
import Workspace.AlternatingSimple

/-!
# The local permutation families `Q_T`, `P_T`, `J_T`

Paper, Appendix A, Section "The local permutation families" (`sec:local-groups`).

Let `G ≤ Sym(Ω)` and let `π : G → Alt(Γ)` be a surjection. For `T ⊆ Γ`:

* `Q_T = {g ∈ G : T^{π(g)} = T}` (`Qgrp`),
* `P_T = {g ∈ Q_T : sgn(π(g)|_T) = 1}` (`Pgrp`),
* `J_T = G_{(T)} = {g ∈ G : π(g) fixes T pointwise}` (`Jgrp`).

"If `k ≥ 3` and `m - k ≥ 2`, restriction gives a surjection
`φ_T : P_T → Alt(T)`, with kernel `J_T`, and `[Q_T : P_T] = 2`."
Here `φ_T` is `phiT`. Surjectivity and the kernel need no size hypothesis
(`phiT_surjective`, `phiT_ker`); the index needs `|T| ≥ 2` and `|Γ \ T| ≥ 2`
(`index_P_in_Q`).

Since `π` is only defined on `G`, we extend it by `1` off `G` (`lab`); every
statement only evaluates it on `G`.

The conjugation lemmas at the end say that `g ∈ G` carries `(P_T, φ_T)` to
`(P_{T'}, φ_{T'})` for `T' = T^{π(g)}`, along the isomorphism
`Alt(T) ≅ Alt(T')` induced by `π(g)|_T` (`compat`). This is the paper's "the even
set-stabilizer `P_T` is conjugacy-equivariant, including for odd bijections
between the ordered test sets".
-/

namespace GI.LocalGroups

open Equiv Equiv.Perm GI.Endpoint

variable {Ω Γ : Type*} [Fintype Γ] [DecidableEq Γ]
variable (G : Subgroup (Perm Ω)) (π : G →* alternatingGroup Γ)

open Classical in
/-- The label permutation `π(g)`, extended by `1` outside `G`. -/
noncomputable def lab (g : Perm Ω) : Perm Γ :=
  if hg : g ∈ G then (π ⟨g, hg⟩ : Perm Γ) else 1

variable {G π}

theorem lab_of_mem {g : Perm Ω} (hg : g ∈ G) : lab G π g = π ⟨g, hg⟩ := by
  classical
  simp [lab, hg]

theorem lab_coe (g : G) : lab G π g = π g := lab_of_mem g.2

theorem lab_one : lab G π 1 = 1 := by
  rw [lab_of_mem G.one_mem]
  have : (⟨1, G.one_mem⟩ : G) = 1 := rfl
  rw [this, map_one]; rfl

theorem lab_mul {g h : Perm Ω} (hg : g ∈ G) (hh : h ∈ G) :
    lab G π (g * h) = lab G π g * lab G π h := by
  rw [lab_of_mem (G.mul_mem hg hh), lab_of_mem hg, lab_of_mem hh]
  have : (⟨g * h, G.mul_mem hg hh⟩ : G) = ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
  rw [this, map_mul]; rfl

theorem lab_inv {g : Perm Ω} (hg : g ∈ G) : lab G π g⁻¹ = (lab G π g)⁻¹ := by
  rw [lab_of_mem (G.inv_mem hg), lab_of_mem hg]
  have : (⟨g⁻¹, G.inv_mem hg⟩ : G) = (⟨g, hg⟩ : G)⁻¹ := rfl
  rw [this, map_inv]; rfl

variable (G π) (T : Finset Γ)

/-- `Q_T = {g ∈ G : T^{π(g)} = T}`. -/
def Qgrp : Subgroup (Perm Ω) where
  carrier := {g | g ∈ G ∧ ∀ c, lab G π g c ∈ T ↔ c ∈ T}
  one_mem' := ⟨G.one_mem, fun c => by rw [lab_one]; rfl⟩
  mul_mem' := fun {g h} hg hh =>
    ⟨G.mul_mem hg.1 hh.1, fun c => by rw [lab_mul hg.1 hh.1, Perm.mul_apply, hg.2, hh.2]⟩
  inv_mem' := fun {g} hg => ⟨G.inv_mem hg.1, fun c => by
    rw [lab_inv hg.1]
    have := hg.2 ((lab G π g)⁻¹ c)
    simp only [Perm.apply_inv_self] at this
    exact this.symm⟩

variable {G π T}

theorem mem_Qgrp {g : Perm Ω} : g ∈ Qgrp G π T ↔ g ∈ G ∧ ∀ c, lab G π g c ∈ T ↔ c ∈ T :=
  Iff.rfl

variable (G π T)

/-- Restriction `g ↦ π(g)|_T` on `Q_T`. -/
noncomputable def restrictQ : Qgrp G π T →* Perm T where
  toFun a := (lab G π a).subtypePerm a.2.2
  map_one' := by
    ext c
    simp [lab_one]
  map_mul' a b := by
    ext c
    simp [lab_mul a.2.1 b.2.1]

/-- `P_T = {g ∈ Q_T : sgn(π(g)|_T) = 1}`. -/
noncomputable def Pgrp : Subgroup (Perm Ω) :=
  (sign.comp (restrictQ G π T)).ker.map (Qgrp G π T).subtype

/-- `J_T = {g ∈ G : π(g) fixes T pointwise}`. -/
def Jgrp : Subgroup (Perm Ω) where
  carrier := {g | g ∈ G ∧ ∀ c ∈ T, lab G π g c = c}
  one_mem' := ⟨G.one_mem, fun c _ => by rw [lab_one]; rfl⟩
  mul_mem' := fun {g h} hg hh =>
    ⟨G.mul_mem hg.1 hh.1, fun c hc => by
      rw [lab_mul hg.1 hh.1, Perm.mul_apply, hh.2 c hc, hg.2 c hc]⟩
  inv_mem' := fun {g} hg => ⟨G.inv_mem hg.1, fun c hc => by
    rw [lab_inv hg.1]
    conv_lhs => rw [← hg.2 c hc]
    simp⟩

variable {G π T}

theorem restrictQ_apply (a : Qgrp G π T) (c : T) :
    (restrictQ G π T a c : Γ) = lab G π a c := rfl

theorem mem_Pgrp {g : Perm Ω} :
    g ∈ Pgrp G π T ↔ ∃ h : g ∈ Qgrp G π T, sign (restrictQ G π T ⟨g, h⟩) = 1 := by
  simp only [Pgrp, Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.comp_apply,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨h, hs⟩
    exact ⟨⟨g, h⟩, hs, rfl⟩

theorem mem_Jgrp {g : Perm Ω} : g ∈ Jgrp G π T ↔ g ∈ G ∧ ∀ c ∈ T, lab G π g c = c := Iff.rfl

theorem Pgrp_le_Qgrp : Pgrp G π T ≤ Qgrp G π T := fun _ hg => (mem_Pgrp.1 hg).1

theorem Qgrp_le : Qgrp G π T ≤ G := fun _ hg => hg.1

theorem Jgrp_le_Qgrp : Jgrp G π T ≤ Qgrp G π T := by
  intro g hg
  refine ⟨hg.1, fun c => ?_⟩
  by_cases hc : c ∈ T
  · rw [hg.2 c hc]
  · constructor
    · intro h
      have := hg.2 _ h
      rw [(lab G π g).injective this] at h
      exact absurd h hc
    · exact fun h => absurd h hc

theorem restrictQ_eq_one_of_Jgrp {g : Perm Ω} (hg : g ∈ Jgrp G π T) :
    restrictQ G π T ⟨g, Jgrp_le_Qgrp hg⟩ = 1 := by
  ext c
  rw [restrictQ_apply, hg.2 c c.2]
  rfl

theorem Jgrp_le_Pgrp : Jgrp G π T ≤ Pgrp G π T := fun _ hg =>
  mem_Pgrp.2 ⟨Jgrp_le_Qgrp hg, by rw [restrictQ_eq_one_of_Jgrp hg, map_one]⟩

theorem Pgrp_le : Pgrp G π T ≤ G := Pgrp_le_Qgrp.trans Qgrp_le

variable (G π T)

/-- `φ_T : P_T → Alt(T)`, restriction of `π(g)` to `T`. -/
noncomputable def phiT : Pgrp G π T →* alternatingGroup T where
  toFun a := ⟨restrictQ G π T ⟨a, Pgrp_le_Qgrp a.2⟩, by
    obtain ⟨_, hs⟩ := mem_Pgrp.1 a.2
    exact mem_alternatingGroup.2 hs⟩
  map_one' := by
    apply Subtype.ext
    exact (restrictQ G π T).map_one
  map_mul' a b := by
    apply Subtype.ext
    exact (restrictQ G π T).map_mul ⟨a, Pgrp_le_Qgrp a.2⟩ ⟨b, Pgrp_le_Qgrp b.2⟩

variable {G π T}

theorem phiT_apply (a : Pgrp G π T) (c : T) : ((phiT G π T a : Perm T) c : Γ) = lab G π a c :=
  rfl

/-- `φ_T` is onto `Alt(T)` (the paper states it for `k ≥ 3`, `m - k ≥ 2`; it holds
for every `T`). -/
theorem phiT_surjective (hπ : Function.Surjective π) : Function.Surjective (phiT G π T) := by
  intro σ
  let σ' : Perm Γ := ofSubtype (σ : Perm T)
  have hσ' : σ' ∈ alternatingGroup Γ := by
    rw [mem_alternatingGroup, sign_ofSubtype]
    exact mem_alternatingGroup.1 σ.2
  obtain ⟨g, hg⟩ := hπ ⟨σ', hσ'⟩
  have hlab : lab G π g = σ' := by rw [lab_coe, hg]
  have hQ : (g : Perm Ω) ∈ Qgrp G π T := ⟨g.2, fun c => by
    rw [hlab]; exact ofSubtype_apply_mem_iff_mem (σ : Perm T) c⟩
  have hres : restrictQ G π T ⟨g, hQ⟩ = σ := by
    ext c
    rw [restrictQ_apply]
    change lab G π g c = _
    rw [hlab, ofSubtype_apply_of_mem _ c.2]
  have hP : (g : Perm Ω) ∈ Pgrp G π T :=
    mem_Pgrp.2 ⟨hQ, by rw [hres]; exact mem_alternatingGroup.1 σ.2⟩
  refine ⟨⟨g, hP⟩, Subtype.ext ?_⟩
  exact hres

/-- `ker φ_T = J_T`. -/
theorem phiT_ker : (phiT G π T).ker.map (Pgrp G π T).subtype = Jgrp G π T := by
  ext g
  simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Pgrp_le a.2, fun c hc => ?_⟩
    have := congrArg (fun p : alternatingGroup T => ((p : Perm T) ⟨c, hc⟩ : Γ)) ha
    simpa [phiT_apply] using this
  · intro hg
    refine ⟨⟨g, Jgrp_le_Pgrp hg⟩, ?_, rfl⟩
    apply Subtype.ext
    exact restrictQ_eq_one_of_Jgrp hg

theorem mem_ker_phiT_iff (a : Pgrp G π T) : phiT G π T a = 1 ↔ (a : Perm Ω) ∈ Jgrp G π T := by
  rw [← phiT_ker, Subgroup.mem_map]
  constructor
  · intro h; exact ⟨a, h, rfl⟩
  · rintro ⟨b, hb, he⟩
    rw [Subtype.ext he] at hb
    exact hb

/-- `[Q_T : P_T] = 2` when `|T| ≥ 2` and `|Γ \ T| ≥ 2` (the paper has `k ≥ 3`,
`m - k ≥ 2`). A paired transposition, one in each part, lies in `Alt(Γ)`, preserves
`T`, and is odd on `T`. -/
theorem index_P_in_Q (hπ : Function.Surjective π) (hT : 2 ≤ T.card)
    (hTc : 2 ≤ (Finset.univ \ T).card) :
    (Pgrp G π T).relIndex (Qgrp G π T) = 2 := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (show 1 < T.card by omega)
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 (show 1 < (Finset.univ \ T).card by omega)
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hc hd
  let τ : Perm Γ := swap a b * swap c d
  have hτA : τ ∈ alternatingGroup Γ := by
    rw [mem_alternatingGroup, sign_mul, sign_swap hab, sign_swap hcd]; rfl
  obtain ⟨g, hg⟩ := hπ ⟨τ, hτA⟩
  have hlab : lab G π g = τ := by rw [lab_coe, hg]
  have hpres : ∀ x, τ x ∈ T ↔ x ∈ T := by
    intro x
    simp only [τ, Perm.mul_apply]
    by_cases hx1 : x = c
    · subst hx1
      rw [swap_apply_left, swap_apply_of_ne_of_ne (by rintro rfl; exact hd ha)
        (by rintro rfl; exact hd hb)]
      exact ⟨fun h => absurd h hd, fun h => absurd h hc⟩
    by_cases hx2 : x = d
    · subst hx2
      rw [swap_apply_right, swap_apply_of_ne_of_ne (by rintro rfl; exact hc ha)
        (by rintro rfl; exact hc hb)]
      exact ⟨fun h => absurd h hc, fun h => absurd h hd⟩
    rw [swap_apply_of_ne_of_ne hx1 hx2]
    by_cases hx3 : x = a
    · subst hx3; simp [swap_apply_left, hb, ha]
    by_cases hx4 : x = b
    · subst hx4; simp [swap_apply_right, ha, hb]
    rw [swap_apply_of_ne_of_ne hx3 hx4]
  have hQ : (g : Perm Ω) ∈ Qgrp G π T := ⟨g.2, fun x => by rw [hlab]; exact hpres x⟩
  -- The restriction of `τ` to `T` is the transposition `(a b)` of `T`.
  have hres : restrictQ G π T ⟨g, hQ⟩ = swap ⟨a, ha⟩ ⟨b, hb⟩ := by
    ext ⟨x, hx⟩
    rw [restrictQ_apply]
    change lab G π g x = _
    rw [hlab]
    have hxc : x ≠ c := fun h => hc (h ▸ hx)
    have hxd : x ≠ d := fun h => hd (h ▸ hx)
    simp only [τ, Perm.mul_apply, swap_apply_of_ne_of_ne hxc hxd]
    by_cases hx3 : x = a
    · subst hx3; simp
    by_cases hx4 : x = b
    · subst hx4; simp
    rw [swap_apply_of_ne_of_ne hx3 hx4, swap_apply_of_ne_of_ne
      (fun h => hx3 (congrArg Subtype.val h)) (fun h => hx4 (congrArg Subtype.val h))]
  have hodd : sign (restrictQ G π T ⟨g, hQ⟩) = -1 := by
    rw [hres, sign_swap (fun h => hab (congrArg Subtype.val h))]
  have hsub : (Pgrp G π T).subgroupOf (Qgrp G π T) = (sign.comp (restrictQ G π T)).ker := by
    ext q
    rw [Subgroup.mem_subgroupOf, mem_Pgrp, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨q.2, h⟩⟩
  have hsurj : Function.Surjective (sign.comp (restrictQ G π T)) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨⟨g, hQ⟩, hodd⟩
  rw [Subgroup.relIndex, hsub, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  rfl

/-- `Q_T = P_T ∪ P_T τ` for any `τ ∈ Q_T \ P_T` (the coset supplied by a paired
transposition in the proof of Proposition A.1). -/
theorem Qgrp_eq_union {τ g : Perm Ω} (hτ : τ ∈ Qgrp G π T) (hτP : τ ∉ Pgrp G π T)
    (hg : g ∈ Qgrp G π T) : g ∈ Pgrp G π T ∨ g * τ⁻¹ ∈ Pgrp G π T := by
  by_cases hgP : g ∈ Pgrp G π T
  · exact Or.inl hgP
  right
  have hodd : ∀ {h : Perm Ω} (hh : h ∈ Qgrp G π T), h ∉ Pgrp G π T →
      sign (restrictQ G π T ⟨h, hh⟩) = -1 := by
    intro h hh hn
    rcases Int.units_eq_one_or (sign (restrictQ G π T ⟨h, hh⟩)) with e | e
    · exact absurd (mem_Pgrp.2 ⟨hh, e⟩) hn
    · exact e
  have hm : g * τ⁻¹ ∈ Qgrp G π T := (Qgrp G π T).mul_mem hg ((Qgrp G π T).inv_mem hτ)
  refine mem_Pgrp.2 ⟨hm, ?_⟩
  have : (⟨g * τ⁻¹, hm⟩ : Qgrp G π T) = ⟨g, hg⟩ * (⟨τ, hτ⟩ : Qgrp G π T)⁻¹ := rfl
  rw [this, map_mul, map_inv, map_mul, map_inv, hodd hg hgP, hodd hτ hτP]
  rfl

/-! ### The preimage description behind Proposition A.1 -/

/-- `ker π ≤ J_T`. -/
theorem ker_le_Jgrp : π.ker.map G.subtype ≤ Jgrp G π T := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g.2, fun c _ => ?_⟩
  change lab G π g c = c
  rw [lab_coe, MonoidHom.mem_ker.1 hg]
  rfl

/-- The proof of Proposition A.1: `P_T` is the full preimage of
`Alt(T) × Alt(Γ \ T)`. An element `g ∈ G` lies in `P_T` exactly when `π(g)`
preserves `T` and is even on both `T` and its complement. (Evenness on one part
forces it on the other, since `π(g)` is even.) -/
theorem mem_Pgrp_iff_preimage {g : Perm Ω} :
    g ∈ Pgrp G π T ↔ g ∈ G ∧ ∃ h : (∀ c, lab G π g c ∈ T ↔ c ∈ T),
      sign ((lab G π g).subtypePerm h) = 1 ∧
      sign ((lab G π g).subtypePerm (p := fun c => c ∉ T) (fun c => not_congr (h c))) = 1 := by
  rw [mem_Pgrp]
  constructor
  · rintro ⟨hQ, hs⟩
    refine ⟨hQ.1, hQ.2, hs, ?_⟩
    have hdec : lab G π g = ((lab G π g).subtypePerm hQ.2).subtypeCongr
        ((lab G π g).subtypePerm (p := fun c => c ∉ T) (fun c => not_congr (hQ.2 c))) := by
      ext c
      by_cases hc : c ∈ T
      · rw [Perm.subtypeCongr.left_apply _ _ hc]; rfl
      · rw [Perm.subtypeCongr.right_apply _ _ hc]; rfl
    have heven : sign (lab G π g) = 1 := by
      rw [lab_of_mem hQ.1]; exact mem_alternatingGroup.1 (π ⟨g, hQ.1⟩).2
    rw [hdec, sign_subtypeCongr] at heven
    have hs' : sign ((lab G π g).subtypePerm hQ.2) = 1 := hs
    have h3 : sign ((lab G π g).subtypePerm hQ.2) *
        sign ((lab G π g).subtypePerm (p := fun c => c ∉ T) (fun c => not_congr (hQ.2 c))) = 1 := by
      convert heven
    rw [hs', one_mul] at h3
    exact h3
  · rintro ⟨hG, h, hs, _⟩
    exact ⟨⟨hG, h⟩, hs⟩

/-! ### Conjugation by elements of `G` -/

/-- The bijection `π(g)|_T : T → T^{π(g)}`. -/
def labEquiv (p : Perm Γ) (T : Finset Γ) : T ≃ (wmap p T : Finset Γ) :=
  p.subtypeEquiv (fun _ => apply_mem_wmap.symm)

theorem conj_mem_Qgrp {g a : Perm Ω} (hg : g ∈ G) :
    a ∈ Qgrp G π T ↔ g * a * g⁻¹ ∈ Qgrp G π (wmap (lab G π g) T) := by
  constructor
  · intro ha
    refine ⟨G.mul_mem (G.mul_mem hg ha.1) (G.inv_mem hg), fun c => ?_⟩
    rw [lab_mul (G.mul_mem hg ha.1) (G.inv_mem hg), lab_mul hg ha.1, lab_inv hg]
    simp only [Perm.mul_apply, mem_wmap, Perm.inv_apply_self]
    exact ha.2 _
  · intro ha
    have haG : a ∈ G := by
      have := G.mul_mem (G.mul_mem (G.inv_mem hg) ha.1) hg
      simpa [mul_assoc] using this
    refine ⟨haG, fun c => ?_⟩
    have h := ha.2 (lab G π g c)
    rw [lab_mul (G.mul_mem hg haG) (G.inv_mem hg), lab_mul hg haG, lab_inv hg] at h
    simpa [Perm.mul_apply, mem_wmap] using h

theorem restrictQ_conj {g a : Perm Ω} (hg : g ∈ G) (ha : a ∈ Qgrp G π T) :
    restrictQ G π (wmap (lab G π g) T) ⟨g * a * g⁻¹, (conj_mem_Qgrp hg).1 ha⟩ =
      (labEquiv (lab G π g) T).permCongr (restrictQ G π T ⟨a, ha⟩) := by
  ext c
  rw [restrictQ_apply, permCongr_apply]
  simp only [labEquiv, subtypeEquiv_symm, subtypeEquiv_apply, restrictQ_apply]
  rw [lab_mul (G.mul_mem hg ha.1) (G.inv_mem hg), lab_mul hg ha.1, lab_inv hg]
  rfl

theorem conj_mem_Pgrp {g a : Perm Ω} (hg : g ∈ G) :
    a ∈ Pgrp G π T ↔ g * a * g⁻¹ ∈ Pgrp G π (wmap (lab G π g) T) := by
  rw [mem_Pgrp, mem_Pgrp]
  constructor
  · rintro ⟨ha, hs⟩
    exact ⟨(conj_mem_Qgrp hg).1 ha, by rw [restrictQ_conj hg ha, sign_permCongr, hs]⟩
  · rintro ⟨ha, hs⟩
    have ha' := (conj_mem_Qgrp hg).2 ha
    exact ⟨ha', by rw [restrictQ_conj hg ha', sign_permCongr] at hs; exact hs⟩

theorem conj_mem_Jgrp {g a : Perm Ω} (hg : g ∈ G) :
    a ∈ Jgrp G π T ↔ g * a * g⁻¹ ∈ Jgrp G π (wmap (lab G π g) T) := by
  constructor
  · intro ha
    refine ⟨G.mul_mem (G.mul_mem hg ha.1) (G.inv_mem hg), fun c hc => ?_⟩
    rw [lab_mul (G.mul_mem hg ha.1) (G.inv_mem hg), lab_mul hg ha.1, lab_inv hg]
    rw [mem_wmap] at hc
    simp only [Perm.mul_apply, ha.2 _ hc, Perm.apply_inv_self]
  · intro ha
    have haG : a ∈ G := by
      have := G.mul_mem (G.mul_mem (G.inv_mem hg) ha.1) hg
      simpa [mul_assoc] using this
    refine ⟨haG, fun c hc => ?_⟩
    have h := ha.2 (lab G π g c) (apply_mem_wmap.2 hc)
    rw [lab_mul (G.mul_mem hg haG) (G.inv_mem hg), lab_mul hg haG, lab_inv hg] at h
    simpa [Perm.mul_apply] using h

/-- **Conjugacy equivariance of `(P_T, φ_T)`.** Every `g ∈ G` carries
`(P_T, φ_T)` to `(P_{T'}, φ_{T'})`, `T' = T^{π(g)}`, along the isomorphism
`Alt(T) ≅ Alt(T')` induced by `π(g)|_T`; no parity condition on `π(g)|_T` is
needed. -/
theorem compat {g : Perm Ω} (hg : g ∈ G) :
    Compat (phiT G π T) (phiT G π (wmap (lab G π g) T)) g
      (GI.AlternatingSimple.relabel (labEquiv (lab G π g) T)) where
  mem a := conj_mem_Pgrp hg
  map a := by
    apply Subtype.ext
    change restrictQ G π _ ⟨g * a * g⁻¹, _⟩ = (labEquiv (lab G π g) T).permCongr _
    exact restrictQ_conj hg (Pgrp_le_Qgrp a.2)

end GI.LocalGroups
