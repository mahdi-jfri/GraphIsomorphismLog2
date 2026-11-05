module

public import Workspace.Impl.TermGlueLabTorsor

@[expose] public section

/-!
# The affine action of `D` on the label torsor

Proof of Theorem A.23: "An element `h ∈ D`, the subgroup preserving this type
multiset, is lifted through `K` to a blockwise permutation `k(h)`. Its coordinate actions differ
from the common `h` by elements of `N`; their images in `A` give a computable affine offset.
Conjugation by `h` permutes the groups `B_a`, so it induces the linear part on `A/B(x)`."
Explicitly,
`s ↦ s^h + Σ_a m_a [t_a(h)] + Σ_i [d_i(h)] (mod B(x))`, where `z_a^h = z_{a^h}^{t_a(h)}` and
`k_i(h) = h d_i(h)`. "When the orientation coordinate occurs, its translation is the sign of
the induced permutation of the distinct types."

Setting: as in `TermGlueLabTorsor`, plus a group `H` normalizing `N` whose conjugation keeps the
kernel of `φ` (`TmGLKer`; in the terminal, `ker φ = N*` is normal in `H`). `D = Aut_H(T)` is the
stabilizer of the type multiset `T` of `x`.

* `tmGLκ h`: the linear part, `[n] ↦ [h⁻¹ n h]` (`tmGLκ_c`). It is well defined because
  conjugation by `h ∈ D` maps `B(x)` into itself (`tmGL_conj_ker`).
* `tmGLε h`: the orientation translation, the sign of the permutation `ρ` of the rows of `x` with
  `type(x_{ρ i}) = type(x_i)^h` when every type is distinct (`tmGLε_eq`), else `1`.
* `tmGL_equivariant`: for any `t` with `z_a^h = z_{a^h}^{t a}` and any tuple `d` with
  `h⁻¹ d_i ∈ N`, the string `z^d` has label `κ_h(s(z)) · Π_i [t(type x_i)] · Π_i [h⁻¹ d_i]` and
  orientation `o(z) ε(h)`. This is the paper's displayed formula (written multiplicatively).
-/

namespace GI.Impl

open GI.Multicoset Equiv Equiv.Perm

section Affine

variable {P : Type*} [Group P] {Ω : Type} [RAct P Ω] {q : ℕ}
variable {N H : Subgroup P} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}

/-- The total label of a list product (`phiT` is multiplicative on `N`). -/
theorem tmGL_phiT_lprod (l : List P) (hl : ∀ a ∈ l, a ∈ N) :
    l.prod ∈ N ∧ phiT N φ l.prod = (l.map (phiT N φ)).prod := by
  induction l with
  | nil => exact ⟨N.one_mem, phiT_one⟩
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih fun b hb => hl b (List.mem_cons_of_mem a hb)
    have ha := hl a List.mem_cons_self
    refine ⟨by simpa using N.mul_mem ha h1, ?_⟩
    rw [List.prod_cons, phiT_mul ha h1, h2, List.map_cons, List.prod_cons]

theorem tmGL_phiT_ofFn {s : Fin q → P} (hs : ∀ i, s i ∈ N) :
    (List.ofFn s).prod ∈ N ∧ phiT N φ (List.ofFn s).prod = ∏ i, phiT N φ (s i) := by
  have h := tmGL_phiT_lprod (φ := φ) (List.ofFn s) (by simpa [List.mem_ofFn] using hs)
  refine ⟨h.1, ?_⟩
  rw [h.2, List.map_ofFn, List.prod_ofFn]
  rfl

variable (N H φ) in

/-- **Conjugation by `H` keeps the kernel of `φ`.** -/
def TmGLKer : Prop := ∀ h ∈ H, ∀ n ∈ N, phiT N φ n = 1 → phiT N φ (h⁻¹ * n * h) = 1


/-- The rows of `x` moved by `h ∈ D` are rows of types of `x`. -/
theorem tmGL_D_row (hn : Normalizes H N) {h : P}
    (hD : h ∈ Aut H (types N x)) (i : Fin q) : ∃ j, ∃ c ∈ N, x i ↼ h = x j ↼ c := by
  have hmem : orbitN N (x i ↼ h) ∈ types N x := by
    rw [← orbitN_act hn hD.1, ← hD.2]
    exact act_mem_act h (Multiset.mem_map_of_mem _ (Finset.mem_univ_val i))
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
  have : x i ↼ h ∈ orbitN N (x j) := by rw [hj]; exact ⟨1, N.one_mem, act_one _⟩
  obtain ⟨c, hc, hce⟩ := this
  exact ⟨j, c, hc, hce.symm⟩

/-- **Conjugation by `h ∈ D` maps `B(x)` into itself** ("Conjugation by `h` permutes the groups
`B_a`"), so it maps the kernel of `N → A/B(x)` into itself. -/
theorem tmGL_conj_lab (hn : Normalizes H N) (hker : TmGLKer N H φ) {h : P}
    (hD : h ∈ Aut H (types N x)) {n : P} (hnN : n ∈ N) (hB : phiT N φ n ∈ labelGroup N φ x) :
    phiT N φ (h⁻¹ * n * h) ∈ labelGroup N φ x := by
  have hh : h ∈ H := hD.1
  obtain ⟨s, hs, hsn⟩ := hB
  have hsN : ∀ i, s i ∈ N := fun i => aut_le _ _ (hs i)
  obtain ⟨hS, hSφ⟩ := tmGL_phiT_ofFn (φ := φ) hsN
  set S := (List.ofFn s).prod
  -- `n S⁻¹` lies in the kernel of `φ`
  have hk : phiT N φ (n * S⁻¹) = 1 := by
    rw [phiT_mul hnN (N.inv_mem hS), phiT_inv hS, hSφ, hsn, mul_inv_cancel]
  have hk' := hker h hh _ (N.mul_mem hnN (N.inv_mem hS)) hk
  -- the conjugate of `S` is the product of the conjugates
  have hconj : h⁻¹ * S * h = (List.ofFn fun i => h⁻¹ * s i * h).prod := by
    have := map_list_prod (MulAut.conj h⁻¹).toMonoidHom (List.ofFn s)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, List.map_ofFn] at this
    rw [this]
    congr 2
    funext i
    simp
  obtain ⟨hS', hSφ'⟩ := tmGL_phiT_ofFn (φ := φ) (fun i => hn.inv hh (hsN i))
  have e : h⁻¹ * n * h = (h⁻¹ * (n * S⁻¹) * h) * (h⁻¹ * S * h) := by group
  rw [e, phiT_mul (hn.inv hh (N.mul_mem hnN (N.inv_mem hS))) (hn.inv hh hS), hk', one_mul, hconj,
    hSφ']
  refine Subgroup.prod_mem _ fun i _ => ?_
  obtain ⟨j, c, hc, hjc⟩ := tmGL_D_row hn hD i
  refine tmGL_aut_label (x := x) (j := j) hc ?_
  rw [← hjc]
  refine mem_aut.mpr ⟨hn.inv hh (hsN i), ?_⟩
  rw [act_act, show h * (h⁻¹ * s i * h) = s i * h by group, ← act_act, (mem_aut.mp (hs i)).2]

variable (hn : Normalizes H N)

/-- Conjugation `n ↦ h⁻¹ n h` as an endomorphism of `N`. -/
def tmGLconj {h : P} (hh : h ∈ H) : N →* N where
  toFun n := ⟨h⁻¹ * n * h, hn.inv hh n.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem tmGL_conj_ker (hker : TmGLKer N H φ) {h : P} (hD : h ∈ Aut H (types N x)) :
    (tmGLf N φ x).ker ≤ (tmGLf N φ x).ker.comap (tmGLconj hn hD.1) := by
  intro n hk
  rw [MonoidHom.mem_ker, tmGLf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hk
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, tmGLf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  have h1 : φ n = phiT N φ n := by simp [phiT]
  have := tmGL_conj_lab hn hker hD n.2 (h1 ▸ hk)
  simpa [phiT, tmGLconj, dif_pos (hn.inv hD.1 n.2)] using this

open Classical in
/-- **The linear part** `κ_h : [n] ↦ [h⁻¹ n h]` on `A/B(x)` for `h ∈ D` (the identity off
`D`). -/
noncomputable def tmGLκ (hker : TmGLKer N H φ) (h : P) : tmGLV N φ x →* tmGLV N φ x :=
  if hD : h ∈ Aut H (types N x) then
    QuotientGroup.map _ _ (tmGLconj hn hD.1) (tmGL_conj_ker hn hker hD)
  else MonoidHom.id _

variable {hn}

theorem tmGLκ_c (hker : TmGLKer N H φ) {h : P} (hD : h ∈ Aut H (types N x)) {n : P}
    (hnN : n ∈ N) : tmGLκ hn hker h (tmGLc N φ x n) = tmGLc N φ x (h⁻¹ * n * h) := by
  simp only [tmGLκ, dif_pos hD, tmGLc, dif_pos hnN, dif_pos (hn.inv hD.1 hnN)]
  rfl

theorem tmGLc_surj (v : tmGLV N φ x) : ∃ n ∈ N, tmGLc N φ x n = v := by
  obtain ⟨⟨n, hnN⟩, rfl⟩ := QuotientGroup.mk_surjective v
  exact ⟨n, hnN, by simp only [tmGLc, dif_pos hnN]⟩

/-- **The linear parts compose** as a right action: `κ_{gh} = κ_h ∘ κ_g`. -/
theorem tmGLκ_mul (hker : TmGLKer N H φ) {g h : P} (hg : g ∈ Aut H (types N x))
    (hh : h ∈ Aut H (types N x)) (v : tmGLV N φ x) :
    tmGLκ hn hker (g * h) v = tmGLκ hn hker h (tmGLκ hn hker g v) := by
  obtain ⟨n, hnN, rfl⟩ := tmGLc_surj v
  rw [tmGLκ_c hker ((Aut H _).mul_mem hg hh) hnN, tmGLκ_c hker hg hnN,
    tmGLκ_c hker hh (hn.inv hg.1 hnN)]
  congr 1
  group

/-- **`N` acts trivially on the linear part**, since `A/B(x)` is abelian. -/
theorem tmGLκ_N (hker : TmGLKer N H φ) {n : P} (hnN : n ∈ N) (hD : n ∈ Aut H (types N x))
    (v : tmGLV N φ x) : tmGLκ hn hker n v = v := by
  obtain ⟨m, hmN, rfl⟩ := tmGLc_surj v
  rw [tmGLκ_c hker hD hmN, tmGLc_mul (N.mul_mem (N.inv_mem hnN) hmN) hnN,
    tmGLc_mul (N.inv_mem hnN) hmN, tmGLc_inv hnN, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

/-! ### The orientation translation -/

variable (N x)

open Classical in
/-- **The orientation translation**: the sign of the permutation `ρ` of the rows of `x` with
`type(x_{ρ i}) = type(x_i)^h`, when every type is distinct; otherwise `1`. -/
noncomputable def tmGLε (h : P) : ℤˣ :=
  if hT : (types N x).Nodup ∧ ∃ ρ : Perm (Fin q), ∀ i, orbitN N (x (ρ i)) = orbitN N (x i) ↼ h
  then sign hT.2.choose else 1

variable {N x}

theorem tmGLε_eq (hT : (types N x).Nodup) {h : P} {ρ : Perm (Fin q)}
    (hρ : ∀ i, orbitN N (x (ρ i)) = orbitN N (x i) ↼ h) : tmGLε N x h = sign ρ := by
  have h' : (types N x).Nodup ∧ ∃ ρ : Perm (Fin q), ∀ i, orbitN N (x (ρ i)) = orbitN N (x i) ↼ h :=
    ⟨hT, ρ, hρ⟩
  simp only [tmGLε, dif_pos h']
  congr 1
  refine Equiv.ext fun i => tmGL_types_inj rfl hT ?_
  rw [h'.2.choose_spec i, hρ i]

theorem tmGLε_of_not_nodup (hT : ¬ (types N x).Nodup) (h : P) : tmGLε N x h = 1 := by
  simp only [tmGLε]
  rw [dif_neg (fun h' => hT h'.1)]

/-- The induced permutation of the types exists for `h ∈ D`. -/
theorem tmGL_ρ_exists {h : P} (hD : h ∈ Aut H (types N x)) :
    ∃ ρ : Perm (Fin q), ∀ i, orbitN N (x (ρ i)) = orbitN N (x i) ↼ h := by
  have hT : Finset.univ.val.map (fun i => orbitN N (x i) ↼ h) =
      Finset.univ.val.map (fun i => orbitN N (x i)) := by
    have := hD.2
    rw [types, multiset_act_def, Multiset.map_map] at this
    exact this
  exact tmGL_exists_perm hT

/-! ### Equivariance: the paper's formula -/

/-- Valid transporters between representatives: `(rep a)^h = (rep (a^h))^{t a}` with
`t a ∈ N`, for every type `a` of `x`. -/
def TmGLT (N : Subgroup P) (x : Fin q → Ω) (rep : Set Ω → Ω) (h : P) (t : Set Ω → P) : Prop :=
  ∀ a ∈ types N x, t a ∈ N ∧ rep a ↼ h = rep (a ↼ h) ↼ t a

/-- Valid transporters exist for `h ∈ D`. -/
theorem tmGLT_exists {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) {h : P}
    (hD : h ∈ Aut H (types N x)) (hn : Normalizes H N) : ∃ t, TmGLT N x rep h t := by
  classical
  have key : ∀ a ∈ types N x, ∃ t ∈ N, rep a ↼ h = rep (a ↼ h) ↼ t := by
    intro a ha
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
    obtain ⟨c, hc, hce⟩ := hrep i
    have hah : orbitN N (x i) ↼ h = orbitN N (x i ↼ h) := orbitN_act hn hD.1 _
    have hmem : orbitN N (x i) ↼ h ∈ types N x := hD.2 ▸ act_mem_act h ha
    obtain ⟨j, -, hj⟩ := Multiset.mem_map.mp hmem
    have hr : rep (orbitN N (x i) ↼ h) ∈ orbitN N (x i ↼ h) := by
      rw [← hah, ← hj]; exact hrep j
    obtain ⟨c'', hc'', hce''⟩ := hr
    refine ⟨c''⁻¹ * (h⁻¹ * c * h), N.mul_mem (N.inv_mem hc'') (hn.inv hD.1 hc), ?_⟩
    rw [← hce'', ← hce, act_act, act_act, act_act]
    congr 1
    group
  choose! t ht using key
  exact ⟨t, fun a ha => ht a ha⟩

/-- The new rows after a tuple of class `h` have the types moved by `h`. -/
theorem tmGL_orbit_d (hn : Normalizes H N) {h : P} (hh : h ∈ H) {d : Fin q → P}
    (hd : ∀ i, h⁻¹ * d i ∈ N) (z : Fin q → Ω) (i : Fin q) :
    orbitN N (rowAct d 1 z i) = orbitN N (z i) ↼ h := by
  simp only [rowAct, Perm.one_symm, Perm.one_apply]
  rw [show d i = h * (h⁻¹ * d i) by group, ← act_act, orbitN_kernel (hd i), orbitN_act hn hh]

theorem tmGL_types_d' (hn : Normalizes H N) {h : P} (hh : h ∈ H) {d : Fin q → P}
    (hd : ∀ i, h⁻¹ * d i ∈ N) (z : Fin q → Ω) : types N (rowAct d 1 z) = types N z ↼ h := by
  rw [types, types, multiset_act_def, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ => tmGL_orbit_d hn hh hd z i

theorem tmGL_types_d (hn : Normalizes H N) {h : P} (hD : h ∈ Aut H (types N x))
    {d : Fin q → P} (hd : ∀ i, h⁻¹ * d i ∈ N) {z : Fin q → Ω} (hz : types N z = types N x) :
    types N (rowAct d 1 z) = types N x := by
  have : types N (rowAct d 1 z) = types N z ↼ h := by
    rw [types, types, multiset_act_def, Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ => tmGL_orbit_d hn hD.1 hd z i
  rw [this, hz, hD.2]

/-- Sums over the rows of a string with type multiset `T` are sums over the rows of `x`. -/
theorem tmGL_prod_types {M : Type*} [CommMonoid M] (F : Set Ω → M) {z : Fin q → Ω}
    (hz : types N z = types N x) : ∏ i, F (orbitN N (z i)) = ∏ i, F (orbitN N (x i)) := by
  have := congrArg (fun T : Multiset (Set Ω) => (T.map F).prod) hz
  simpa [types, Multiset.map_map, Finset.prod_eq_multiset_prod, Function.comp_def] using this

/-- **The label is equivariant** (the paper's formula). For `h ∈ D`, valid `t`, and a tuple `d`
of class `h`, the label of `z^d` is `κ_h(s(z)) · Π_i [t(type x_i)] · Π_i [h⁻¹ d_i]`. -/
theorem tmGL_equivariant (hker : TmGLKer N H φ) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep)
    {h : P} (hD : h ∈ Aut H (types N x)) {t : Set Ω → P} (ht : TmGLT N x rep h t)
    {d : Fin q → P} (hd : ∀ i, h⁻¹ * d i ∈ N) {z : Fin q → Ω} (hz : types N z = types N x) :
    tmGLLab N φ x rep (rowAct d 1 z) =
      tmGLκ hn hker h (tmGLLab N φ x rep z) * (∏ i, tmGLc N φ x (t (orbitN N (x i)))) *
        ∏ i, tmGLc N φ x (h⁻¹ * d i) := by
  have hh : h ∈ H := hD.1
  have hA := tmGLn_spec hrep hz
  set n := tmGLn N rep z
  have hmem : ∀ i, orbitN N (z i) ∈ types N x := fun i => by
    rw [← hz]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  have hz' := tmGL_types_d hn hD hd hz
  -- the new row `i` is reached from its representative by `t(a_i) (h⁻¹ n_i h) (h⁻¹ d_i)`
  have hb : ∀ i, rep (orbitN N (rowAct d 1 z i)) ↼
      (t (orbitN N (z i)) * (h⁻¹ * n i * h) * (h⁻¹ * d i)) = rowAct d 1 z i := by
    intro i
    rw [tmGL_orbit_d hn hh hd z i, show t (orbitN N (z i)) * (h⁻¹ * n i * h) * (h⁻¹ * d i) =
      t (orbitN N (z i)) * (h⁻¹ * (n i * d i)) by group, ← act_act, ← (ht _ (hmem i)).2, act_act,
      show h * (h⁻¹ * (n i * d i)) = n i * d i by group, ← act_act, (hA i).2]
    simp [rowAct, Perm.one_symm]
  have hbN : ∀ i, t (orbitN N (z i)) * (h⁻¹ * n i * h) * (h⁻¹ * d i) ∈ N := fun i =>
    N.mul_mem (N.mul_mem (ht _ (hmem i)).1 (hn.inv hh (hA i).1)) (hd i)
  rw [tmGLLab_eq hrep hz' hbN hb]
  simp_rw [tmGLc_mul (N.mul_mem (ht _ (hmem _)).1 (hn.inv hh (hA _).1)) (hd _),
    tmGLc_mul (ht _ (hmem _)).1 (hn.inv hh (hA _).1)]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    tmGL_prod_types (fun a => tmGLc N φ x (t a)) hz, tmGLLab, map_prod,
    Finset.prod_congr rfl fun i _ => tmGLκ_c hker hD (hA i).1]
  rw [mul_comm (∏ i, tmGLc N φ x (t (orbitN N (x i))))]

include hn in
/-- **The orientation is equivariant**: `o(z^d) = o(z) ε(h)`. -/
theorem tmGL_equivariant_or {h : P} (hD : h ∈ Aut H (types N x)) {d : Fin q → P}
    (hd : ∀ i, h⁻¹ * d i ∈ N) {z : Fin q → Ω} (hz : types N z = types N x) :
    tmGLOr N x (rowAct d 1 z) = tmGLOr N x z * tmGLε N x h := by
  by_cases hT : (types N x).Nodup
  · obtain ⟨πz, hπz⟩ := tmGL_match_x hz
    obtain ⟨ρ, hρ⟩ := tmGL_ρ_exists hD
    have hz' := tmGL_types_d hn hD hd hz
    rw [tmGLOr_eq hz hT hπz, tmGLε_eq hT hρ, tmGLOr_eq (π := πz * ρ⁻¹) hz' hT (fun i => by
      rw [tmGL_orbit_d hn hD.1 hd z, Perm.mul_apply, hπz, ← hρ, Perm.apply_inv_self])]
    rw [Perm.sign_mul, Perm.sign_inv]
  · rw [tmGLOr_of_not_nodup hT, tmGLOr_of_not_nodup hT, tmGLε_of_not_nodup hT, one_mul]

end Affine

end GI.Impl
