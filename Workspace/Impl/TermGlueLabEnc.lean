import Workspace.Impl.TermGlueLabAff

/-!
# The label action in finite abelian coordinates

To call the affine transporter procedure (`TmGLAffineSpec`), the label step
writes the action of the supplement `S = ⟨gs⟩` in coordinates. Given an isomorphism
`E : Y ≅ ∏_i ℤ/m_i` of the torsor group `Y` (`A/B(x) × C₂` when every type is distinct, else
`A/B(x)`), a left linear action `λ` and offsets `o` with the cocycle identity, `tmGLρE` and
`tmGLcE` are the data of the contract, and `tmGLρE_cocycle` checks its cocycle precondition.

For the label action, `λ(g) = κ_{g⁻¹}` and `o(g) = u(g⁻¹)`: the right action `F` of the paper
read as a left action (`tmGL_left_of_right`). `tmGLκe` is `κ_h` as an automorphism.
-/

namespace GI.Impl

open GI.Multicoset GI.Cited Equiv

/-! ### Generic coordinates of an affine action -/

section Gen

variable {n d : ℕ} {gs : List (Perm (Fin n))} {m : Fin d → ℕ} {Y : Type*} [CommGroup Y]

/-- The linear part in coordinates: `ρ(g) = E ∘ λ(g) ∘ E⁻¹`. -/
def tmGLρE (E : Additive Y ≃+ tmGLVec m) (lam : gens gs →* MulAut Y) :
    gens gs →* (tmGLVec m ≃+ tmGLVec m) where
  toFun g := E.symm.trans ((MulEquiv.toAdditive (lam g)).trans E)
  map_one' := by
    ext v i
    simp [map_one]
  map_mul' g h := by
    ext v i
    simp [map_mul]

/-- The offsets in coordinates. -/
def tmGLcE (E : Additive Y ≃+ tmGLVec m) (o : gens gs → Y) (g : gens gs) : tmGLVec m :=
  E (Additive.ofMul (o g))

theorem tmGLρE_apply (E : Additive Y ≃+ tmGLVec m) (lam : gens gs →* MulAut Y) (g : gens gs)
    (y : Y) : tmGLρE E lam g (E (Additive.ofMul y)) = E (Additive.ofMul (lam g y)) := by
  simp [tmGLρE]

/-- **The cocycle precondition of the contract**, from the cocycle identity of the offsets. -/
theorem tmGLρE_cocycle (E : Additive Y ≃+ tmGLVec m) (lam : gens gs →* MulAut Y)
    (o : gens gs → Y) (ho : ∀ g h, o (g * h) = lam g (o h) * o g) (g h : gens gs) :
    tmGLcE E o (g * h) = tmGLρE E lam g (tmGLcE E o h) + tmGLcE E o g := by
  rw [tmGLcE, tmGLcE, tmGLcE, tmGLρE_apply, ← map_add, ho]
  rfl

/-- The encoded affine map is the encoding of the affine map. -/
theorem tmGLρE_aff (E : Additive Y ≃+ tmGLVec m) (lam : gens gs →* MulAut Y)
    (o : gens gs → Y) (g : gens gs) (y : Y) :
    tmGLρE E lam g (E (Additive.ofMul y)) + tmGLcE E o g = E (Additive.ofMul (lam g y * o g)) := by
  rw [tmGLρE_apply, tmGLcE, ← map_add]
  rfl

end Gen

/-! ### The linear part of the label action as automorphisms -/

section Kappa

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}
  {x : Fin q → Ω}
variable (hn : Normalizes H N) (hker : TmGLKer N H φ)

theorem tmGLκ_one (hNH : N ≤ H) : ∀ v : tmGLV N φ x, tmGLκ hn hker 1 v = v :=
  tmGLκ_N hker N.one_mem (tmGL_N_D hNH N.one_mem)

/-- `κ_h` as an automorphism, for `h ∈ D`. -/
noncomputable def tmGLκe (hNH : N ≤ H) {h : Perm (Fin n)} (hD : h ∈ Aut H (types N x)) :
    MulAut (tmGLV N φ x) where
  toFun := tmGLκ hn hker h
  invFun := tmGLκ hn hker h⁻¹
  left_inv v := by
    rw [← tmGLκ_mul hker hD ((Aut H _).inv_mem hD), mul_inv_cancel, tmGLκ_one hn hker hNH]
  right_inv v := by
    rw [← tmGLκ_mul hker ((Aut H _).inv_mem hD) hD, inv_mul_cancel, tmGLκ_one hn hker hNH]
  map_mul' := map_mul _

variable {gs : List (Perm (Fin n))} (hgs : gens gs ≤ Aut H (types N x))

/-- **The left linear action** `g ↦ κ_{g⁻¹}` of `⟨gs⟩ ≤ D` on `A/B(x)`. -/
noncomputable def tmGLlam (hNH : N ≤ H) : gens gs →* MulAut (tmGLV N φ x) where
  toFun g := tmGLκe hn hker hNH (hgs ((gens gs).inv_mem g.2))
  map_one' := by
    ext v
    change tmGLκ hn hker (1 : gens gs).1⁻¹ v = v
    simp only [OneMemClass.coe_one, inv_one]
    exact tmGLκ_one hn hker hNH v
  map_mul' g h := by
    ext v
    change tmGLκ hn hker ((g * h : gens gs) : Perm (Fin n))⁻¹ v =
      tmGLκ hn hker (g : Perm (Fin n))⁻¹ (tmGLκ hn hker (h : Perm (Fin n))⁻¹ v)
    rw [Subgroup.coe_mul, mul_inv_rev, tmGLκ_mul hker (hgs ((gens gs).inv_mem h.2))
      (hgs ((gens gs).inv_mem g.2))]

/-- The same with the orientation coordinate (on which the linear part is trivial). -/
noncomputable def tmGLlamO (hNH : N ≤ H) : gens gs →* MulAut (tmGLV N φ x × ℤˣ) where
  toFun g := MulEquiv.prodCongr (tmGLlam hn hker hgs hNH g) (MulEquiv.refl ℤˣ)
  map_one' := by
    ext v
    · show tmGLlam hn hker hgs hNH 1 v.1 = v.1
      rw [map_one]; rfl
    · rfl
  map_mul' g h := by
    ext v
    · show tmGLlam hn hker hgs hNH (g * h) v.1 =
        tmGLlam hn hker hgs hNH g (tmGLlam hn hker hgs hNH h v.1)
      rw [map_mul]; rfl
    · rfl

end Kappa

/-! ### The label action in coordinates -/

section Label

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
variable {N H : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A}
  {x : Fin q → Ω}
variable {hn : Normalizes H N} {hker : TmGLKer N H φ} {hNH : N ≤ H}
variable {gs : List (Perm (Fin n))} {hgs : gens gs ≤ Aut H (types N x)}

/-- **The offsets of the left action** `g ↦ (u(g⁻¹), ε(g⁻¹))`. -/
noncomputable def tmGLoO (rep : Set Ω → Ω) (k : Perm (Fin n) → Fin q → Perm (Fin n))
    (g : gens gs) : tmGLV N φ x × ℤˣ :=
  (tmGLu N φ x rep k (g : Perm (Fin n))⁻¹, tmGLε N x (g : Perm (Fin n))⁻¹)

/-- The left offsets satisfy the cocycle identity of the contract. -/
theorem tmGLoO_cocycle {k : Perm (Fin n) → Fin q → Perm (Fin n)} (hk : TmGLLift N H φ k)
    {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) (g h : gens gs) :
    tmGLoO rep k (g * h) = tmGLlamO hn hker hgs hNH g (tmGLoO rep k h) * tmGLoO rep k g := by
  have hg := hgs ((gens gs).inv_mem g.2)
  have hh := hgs ((gens gs).inv_mem h.2)
  obtain ⟨hu, hε⟩ := tmGLu_mul (hn := hn) (hker := hker) hk hrep hh hg
  simp only [tmGLoO, Subgroup.coe_mul, mul_inv_rev, hu, hε]
  refine Prod.ext rfl ?_
  show tmGLε N x (h : Perm (Fin n))⁻¹ * tmGLε N x (g : Perm (Fin n))⁻¹ =
    tmGLε N x (h : Perm (Fin n))⁻¹ * tmGLε N x (g : Perm (Fin n))⁻¹
  rfl

/-- The left affine map of `g` is `F_{g⁻¹}`. -/
theorem tmGLoO_aff (rep : Set Ω → Ω) (k : Perm (Fin n) → Fin q → Perm (Fin n)) (g : gens gs)
    (p : tmGLV N φ x × ℤˣ) :
    tmGLlamO hn hker hgs hNH g p * tmGLoO rep k g = tmGLF hn hker rep k (g : Perm (Fin n))⁻¹ p :=
  rfl

/-- **The contract's transporter is the label transporter** (orientation case: `E` encodes
`A/B(x) × C₂`). With `v = E(p_{y'})` and `w = E(p_x)`, the transporter of the contract is
`{g ∈ ⟨gs⟩ | F_g p_x = p_{y'}}`. -/
theorem tmGL_contract_trans {d : ℕ} {m : Fin d → ℕ}
    (E : Additive (tmGLV N φ x × ℤˣ) ≃+ tmGLVec m) {k : Perm (Fin n) → Fin q → Perm (Fin n)}
    (hk : TmGLLift N H φ k) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep)
    (p p' : tmGLV N φ x × ℤˣ) :
    tmGLAffTrans gs (tmGLρE E (tmGLlamO hn hker hgs hNH)) (tmGLcE E (tmGLoO rep k))
        (E (Additive.ofMul p')) (E (Additive.ofMul p)) =
      {g | g ∈ gens gs ∧ tmGLF hn hker rep k g p = p'} := by
  refine tmGL_enc_trans gs (tmGLF hn hker rep k) (tmGL_F_one hNH hk hrep)
    (fun g hg h hh v => tmGL_F_mul hk hrep (hgs hg) (hgs hh) v) Set.univ (fun _ _ _ _ => trivial)
    (fun p => E (Additive.ofMul p)) (fun a _ b _ hab => ?_) _ _ (fun g p _ => ?_) trivial trivial
  · exact Additive.ofMul.injective (E.injective hab)
  · rw [tmGLρE_aff, tmGLoO_aff]

/-- The offsets without the orientation coordinate: `g ↦ u(g⁻¹)`. -/
noncomputable def tmGLo (rep : Set Ω → Ω) (k : Perm (Fin n) → Fin q → Perm (Fin n))
    (g : gens gs) : tmGLV N φ x :=
  tmGLu N φ x rep k (g : Perm (Fin n))⁻¹

theorem tmGLo_cocycle {k : Perm (Fin n) → Fin q → Perm (Fin n)} (hk : TmGLLift N H φ k)
    {rep : Set Ω → Ω} (hrep : TmGLRep N x rep) (g h : gens gs) :
    tmGLo rep k (g * h) = tmGLlam hn hker hgs hNH g (tmGLo rep k h) * tmGLo rep k g := by
  have hg := hgs ((gens gs).inv_mem g.2)
  have hh := hgs ((gens gs).inv_mem h.2)
  obtain ⟨hu, -⟩ := tmGLu_mul (hn := hn) (hker := hker) hk hrep hh hg
  simp only [tmGLo, Subgroup.coe_mul, mul_inv_rev, hu]
  rfl

/-- **The contract's transporter is the label transporter** (no orientation coordinate: some
type repeats, `E` encodes `A/B(x)` and the orientation is `1`). -/
theorem tmGL_contract_trans' (hT : ¬ (types N x).Nodup) {d : ℕ} {m : Fin d → ℕ}
    (E : Additive (tmGLV N φ x) ≃+ tmGLVec m) {k : Perm (Fin n) → Fin q → Perm (Fin n)}
    (hk : TmGLLift N H φ k) {rep : Set Ω → Ω} (hrep : TmGLRep N x rep)
    (s s' : tmGLV N φ x) :
    tmGLAffTrans gs (tmGLρE E (tmGLlam hn hker hgs hNH)) (tmGLcE E (tmGLo rep k))
        (E (Additive.ofMul s')) (E (Additive.ofMul s)) =
      {g | g ∈ gens gs ∧ tmGLF hn hker rep k g (s, 1) = (s', 1)} := by
  refine tmGL_enc_trans gs (tmGLF hn hker rep k) (tmGL_F_one hNH hk hrep)
    (fun g hg h hh v => tmGL_F_mul hk hrep (hgs hg) (hgs hh) v) {p | p.2 = 1}
    (fun g _ p hp => ?_) (fun p => E (Additive.ofMul p.1)) (fun a ha b hb hab => ?_) _ _
    (fun g p hp => ?_) (show ((s, 1) : tmGLV N φ x × ℤˣ).2 = 1 from rfl)
    (show ((s', 1) : tmGLV N φ x × ℤˣ).2 = 1 from rfl)
  · simp only [Set.mem_setOf_eq] at hp ⊢
    simp only [tmGLF, hp, tmGLε_of_not_nodup hT, mul_one]
  · simp only [Set.mem_setOf_eq] at ha hb
    exact Prod.ext (Additive.ofMul.injective (E.injective hab)) (ha.trans hb.symm)
  · simp only [tmGLρE_aff]
    rfl

end Label

end GI.Impl

/-! ### The characteristic bound -/

namespace GI.Impl

open Equiv GI.Multicoset

/-- Each modulus divides the order of a group with these coordinates. -/
theorem tmGL_mod_dvd_card {d : ℕ} {m : Fin d → ℕ} (hm : ∀ i, 0 < m i) {Y : Type*} [CommGroup Y]
    (E : Additive Y ≃+ tmGLVec m) (i : Fin d) : m i ∣ Nat.card Y := by
  haveI : ∀ i, NeZero (m i) := fun i => ⟨Nat.ne_of_gt (hm i)⟩
  have h1 : Nat.card Y = Nat.card (tmGLVec m) :=
    (Nat.card_congr (Additive.ofMul.trans E.toEquiv))
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [ZMod.card]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

/-- `A/B(x)` is a quotient of `N ≤ Sym(n)`, so its order divides `n!`. -/
theorem tmGLV_card_dvd {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
    {N : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] (φ : N →* A) (x : Fin q → Ω) :
    Nat.card (tmGLV N φ x) ∣ n.factorial := by
  refine (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_subgroup_dvd_card N).trans ?_)
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **The characteristic bound** ("With the possible orientation factor included, the
characteristic bound is `p ≤ max{b, 2}`"): every prime divisor of a modulus of coordinates of
`A/B(x) × C₂` is at most `max n 2`. -/
theorem tmGL_prime_le {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
    {N : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}
    {d : ℕ} {m : Fin d → ℕ} (hm : ∀ i, 0 < m i) (E : Additive (tmGLV N φ x × ℤˣ) ≃+ tmGLVec m)
    (i : Fin d) (p : ℕ) (hp : p.Prime) (hpm : p ∣ m i) : p ≤ max n 2 := by
  have h1 := (hpm.trans (tmGL_mod_dvd_card hm E i))
  have h2 : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  rw [Nat.card_prod, h2] at h1
  rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
  · exact le_max_of_le_left ((Nat.Prime.dvd_factorial hp).mp (h.trans (tmGLV_card_dvd φ x)))
  · exact le_max_of_le_right (Nat.le_of_dvd (by norm_num) h)

/-- The same without the orientation coordinate. -/
theorem tmGL_prime_le' {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω] {q : ℕ}
    {N : Subgroup (Perm (Fin n))} {A : Type*} [CommGroup A] {φ : N →* A} {x : Fin q → Ω}
    {d : ℕ} {m : Fin d → ℕ} (hm : ∀ i, 0 < m i) (E : Additive (tmGLV N φ x) ≃+ tmGLVec m)
    (i : Fin d) (p : ℕ) (hp : p.Prime) (hpm : p ∣ m i) : p ≤ max n 2 :=
  le_max_of_le_left ((Nat.Prime.dvd_factorial hp).mp
    ((hpm.trans (tmGL_mod_dvd_card hm E i)).trans (tmGLV_card_dvd φ x)))

end GI.Impl
