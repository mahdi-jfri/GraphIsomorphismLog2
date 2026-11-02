import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# The implicit object model of Section A (`sec:quotient-algorithms`)

The paper works with right actions: `x^h`, `x^{gh} = (x^g)^h`, right cosets `Lh`,
and `L^h = h⁻¹ L h`. We keep these conventions. A right action of `G` on `Ω` is
the class `RAct G Ω`, written `x ↼ g`.

* `Iso H X Y = {h ∈ H : X^h = Y}` and `Aut H X` are the transporter and the
  stabilizer for any right action, in particular for the action on multisets.
* `Fixes N X` says that `N` fixes every listed object of `X`.
* A coset object of color `c` is `cobj L c h = (c, L_c h)`. Its tag `c` keeps
  different orbit colors distinct, even if their subgroups agree.

The statements here are the claims of the subsection "The implicit object model".
-/

namespace GI.Multicoset

/-- A right action `x ↦ x^g`: `x^1 = x` and `x^{gh} = (x^g)^h`. -/
class RAct (G : Type*) [Group G] (Ω : Type*) where
  /-- The image `x^g`. -/
  act : Ω → G → Ω
  act_one : ∀ x, act x 1 = x
  act_mul : ∀ x g h, act x (g * h) = act (act x g) h

/-- The image `x^g`, with the group structure found by instance search. -/
def ract {G : Type*} [Group G] {Ω : Type*} [RAct G Ω] (x : Ω) (g : G) : Ω := RAct.act x g

/-- `x ↼ g` is `x^g`. -/
scoped infixl:75 " ↼ " => ract

section Basic

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω]

@[simp] theorem act_one (x : Ω) : x ↼ (1 : G) = x := RAct.act_one (G := G) x

theorem act_act (x : Ω) (g h : G) : x ↼ g ↼ h = x ↼ (g * h) := (RAct.act_mul x g h).symm

@[simp] theorem act_act_inv (x : Ω) (g : G) : x ↼ g ↼ g⁻¹ = x := by
  rw [act_act, mul_inv_cancel, act_one]

@[simp] theorem act_inv_act (x : Ω) (g : G) : x ↼ g⁻¹ ↼ g = x := by
  rw [act_act, inv_mul_cancel, act_one]

theorem act_injective (g : G) : Function.Injective (fun x : Ω => x ↼ g) := by
  intro x y h
  simpa using congrArg (fun z : Ω => z ↼ g⁻¹) h

theorem act_eq_iff {x y : Ω} {g : G} : x ↼ g = y ↔ x = y ↼ g⁻¹ :=
  ⟨fun h => by rw [← h, act_act_inv], fun h => by rw [h, act_inv_act]⟩

end Basic

/-! ### Multisets -/

section Multisets

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω]

/-- The action on multisets of objects: `X^g = {x^g : x ∈ X}` with multiplicities. -/
instance multisetRAct : RAct G (Multiset Ω) where
  act X g := X.map (fun x => x ↼ g)
  act_one X := by simp
  act_mul X g h := by simp [Multiset.map_map, act_act]

theorem multiset_act_def (X : Multiset Ω) (g : G) : X ↼ g = X.map (fun x => x ↼ g) := rfl

@[simp] theorem card_act (X : Multiset Ω) (g : G) : Multiset.card (X ↼ g) = Multiset.card X := by
  simp [multiset_act_def]

theorem mem_act {X : Multiset Ω} {g : G} {z : Ω} : z ∈ X ↼ g ↔ z ↼ g⁻¹ ∈ X := by
  rw [multiset_act_def, Multiset.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨_, h, by simp⟩

theorem act_mem_act {X : Multiset Ω} {x : Ω} (g : G) (hx : x ∈ X) : x ↼ g ∈ X ↼ g := by
  rw [mem_act]; simpa using hx

@[simp] theorem add_act (X Y : Multiset Ω) (g : G) : (X + Y) ↼ g = X ↼ g + Y ↼ g := by
  simp [multiset_act_def]

@[simp] theorem zero_act (g : G) : (0 : Multiset Ω) ↼ g = 0 := rfl

theorem count_act [DecidableEq Ω] (X : Multiset Ω) (g : G) (z : Ω) :
    (X ↼ g).count (z ↼ g) = X.count z := by
  rw [multiset_act_def, Multiset.count_map_eq_count' _ _ (act_injective g)]

/-- Filtering commutes with the action, with the predicate moved along. -/
theorem filter_act (p : Ω → Prop) [DecidablePred p] (X : Multiset Ω) (g : G) :
    (X ↼ g).filter p = (X.filter (fun x => p (x ↼ g))) ↼ g := by
  rw [multiset_act_def, multiset_act_def, Multiset.filter_map]
  rfl

end Multisets

/-! ### Transporters and stabilizers -/

section Transporters

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω]

/-- The transporter `Iso_H(X, Y) = {h ∈ H : X^h = Y}`. -/
def Iso (H : Subgroup G) (X Y : Ω) : Set G := {h | h ∈ H ∧ X ↼ h = Y}

/-- The stabilizer `Aut_H(X) = Iso_H(X, X)`, as a subgroup. -/
def Aut (H : Subgroup G) (X : Ω) : Subgroup G where
  carrier := {h | h ∈ H ∧ X ↼ h = X}
  one_mem' := ⟨H.one_mem, act_one X⟩
  mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, by rw [← act_act, ha.2, hb.2]⟩
  inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, by
    conv_lhs => rw [← ha.2]
    exact act_act_inv X a⟩

theorem mem_iso {H : Subgroup G} {X Y : Ω} {h : G} : h ∈ Iso H X Y ↔ h ∈ H ∧ X ↼ h = Y :=
  Iso.eq_def H X Y ▸ Iff.rfl

theorem mem_aut {H : Subgroup G} {X : Ω} {h : G} : h ∈ Aut H X ↔ h ∈ H ∧ X ↼ h = X :=
  Iff.rfl

theorem aut_le (H : Subgroup G) (X : Ω) : Aut H X ≤ H := fun _ h => h.1

theorem iso_self (H : Subgroup G) (X : Ω) : Iso H X X = (Aut H X : Set G) := rfl

theorem iso_mono {H K : Subgroup G} (hHK : H ≤ K) (X Y : Ω) : Iso H X Y ⊆ Iso K X Y :=
  fun _ h => ⟨hHK h.1, h.2⟩

/-- A nonempty transporter is a right coset of the source stabilizer:
`Iso_H(X,Y) = Aut_H(X) t` for every `t ∈ Iso_H(X,Y)`. -/
theorem mem_iso_iff_of_mem {H : Subgroup G} {X Y : Ω} {t h : G} (ht : t ∈ Iso H X Y) :
    h ∈ Iso H X Y ↔ h * t⁻¹ ∈ Aut H X := by
  rw [mem_iso] at ht ⊢
  constructor
  · rintro ⟨hH, hX⟩
    refine ⟨H.mul_mem hH (H.inv_mem ht.1), ?_⟩
    rw [← act_act, hX, ← ht.2, act_act_inv]
  · rintro ⟨hH, hX⟩
    refine ⟨by simpa using H.mul_mem hH ht.1, ?_⟩
    have := congrArg (fun z => z ↼ t) hX
    simp only [act_act, inv_mul_cancel_right] at this
    rw [this, ht.2]

theorem iso_eq_aut_mul {H : Subgroup G} {X Y : Ω} {t : G} (ht : t ∈ Iso H X Y) :
    Iso H X Y = (fun a => a * t) '' (Aut H X : Set G) := by
  ext h
  rw [mem_iso_iff_of_mem ht]
  constructor
  · intro hh; exact ⟨h * t⁻¹, hh, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

/-- Moving the target: `h ∈ Iso_H(X, Y)` iff `h τ⁻¹ ∈ Iso_H(X, Y^{τ⁻¹})`, for `τ ∈ H`. -/
theorem mem_iso_shift {H : Subgroup G} {X Y : Ω} {τ h : G} (hτ : τ ∈ H) :
    h ∈ Iso H X Y ↔ h * τ⁻¹ ∈ Iso H X (Y ↼ τ⁻¹) := by
  simp only [mem_iso]
  constructor
  · rintro ⟨hh, rfl⟩
    exact ⟨H.mul_mem hh (H.inv_mem hτ), by rw [act_act]⟩
  · rintro ⟨hh, he⟩
    refine ⟨by simpa using H.mul_mem hh hτ, ?_⟩
    have := congrArg (fun z => z ↼ τ) he
    simpa [act_act] using this

theorem iso_comp {H : Subgroup G} {X Y Z : Ω} {g h : G} (hg : g ∈ Iso H X Y)
    (hh : h ∈ Iso H Y Z) : g * h ∈ Iso H X Z :=
  ⟨H.mul_mem hg.1 hh.1, by rw [← act_act, hg.2, hh.2]⟩

theorem iso_inv {H : Subgroup G} {X Y : Ω} {g : G} (hg : g ∈ Iso H X Y) : g⁻¹ ∈ Iso H Y X :=
  ⟨H.inv_mem hg.1, by rw [← hg.2, act_act_inv]⟩

/-- The transporter of a translated source: `Iso_H(X^g, Y) = g⁻¹ Iso_H(X, Y)` for `g ∈ H`. -/
theorem mem_iso_act_left {H : Subgroup G} {X Y : Ω} {g h : G} (hg : g ∈ H) :
    h ∈ Iso H (X ↼ g) Y ↔ g * h ∈ Iso H X Y := by
  simp only [mem_iso, act_act]
  constructor
  · rintro ⟨hh, he⟩; exact ⟨H.mul_mem hg hh, he⟩
  · rintro ⟨hh, he⟩; exact ⟨by simpa using H.mul_mem (H.inv_mem hg) hh, he⟩

end Transporters

/-! ### Normal kernels -/

section Kernels

variable {G : Type*} [Group G] {Ω : Type*} [RAct G Ω]

/-- `H` normalizes `N`: `h n h⁻¹ ∈ N` for `h ∈ H`, `n ∈ N`. With `N ≤ H` this is `N ◁ H`. -/
def Normalizes (H N : Subgroup G) : Prop := ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N

theorem Normalizes.inv {H N : Subgroup G} (hn : Normalizes H N) {h n : G} (hh : h ∈ H)
    (hN : n ∈ N) : h⁻¹ * n * h ∈ N := by
  simpa using hn h⁻¹ (H.inv_mem hh) n hN

theorem Normalizes.mono {H K N : Subgroup G} (hn : Normalizes H N) (hK : K ≤ H) :
    Normalizes K N := fun h hh => hn h (hK hh)

theorem normalizes_self (H : Subgroup G) : Normalizes H H :=
  fun _ hh _ hn => H.mul_mem (H.mul_mem hh hn) (H.inv_mem hh)

theorem Normalizes.inf {H N M : Subgroup G} (hN : Normalizes H N) (hM : Normalizes H M) :
    Normalizes H (N ⊓ M) := fun h hh n hn => ⟨hN h hh n hn.1, hM h hh n hn.2⟩

/-- `N` fixes every listed object of `X`. -/
def Fixes (N : Subgroup G) (X : Multiset Ω) : Prop := ∀ n ∈ N, ∀ x ∈ X, x ↼ n = x

theorem Fixes.act_eq {N : Subgroup G} {X : Multiset Ω} (hf : Fixes N X) {n : G} (hn : n ∈ N) :
    X ↼ n = X := by
  rw [multiset_act_def]
  conv_rhs => rw [← Multiset.map_id X]
  exact Multiset.map_congr rfl (fun x hx => hf n hn x hx)

theorem Fixes.mono {N M : Subgroup G} {X : Multiset Ω} (hf : Fixes N X) (hM : M ≤ N) :
    Fixes M X := fun n hn => hf n (hM hn)

theorem Fixes.of_le {N : Subgroup G} {X Y : Multiset Ω} (hf : Fixes N X) (hYX : Y ≤ X) :
    Fixes N Y := fun n hn y hy => hf n hn y (Multiset.mem_of_le hYX hy)

/-- The fixed objects of a normalized kernel are permuted by `H`. -/
theorem Fixes.act {H N : Subgroup G} {X : Multiset Ω} (hf : Fixes N X) (hn : Normalizes H N)
    {h : G} (hh : h ∈ H) : Fixes N (X ↼ h) := by
  intro n hN z hz
  rw [mem_act] at hz
  have key := hf _ (hn.inv (H.inv_mem hh) hN) _ hz
  simp only [inv_inv] at key
  have := congrArg (fun w => w ↼ h) key
  simp only [act_act] at this
  rw [show z = z ↼ h⁻¹ ↼ h by simp, act_act, act_act]
  simpa [mul_assoc] using this

/-- Elementwise version: a normalized kernel fixing `x` fixes its whole `H`-orbit. -/
theorem fixes_point_act {H N : Subgroup G} {x : Ω} (hx : ∀ n ∈ N, x ↼ n = x)
    (hn : Normalizes H N) {h : G} (hh : h ∈ H) : ∀ n ∈ N, x ↼ h ↼ n = x ↼ h := by
  have := (show Fixes N ({x} : Multiset Ω) from fun n hN z hz => by
    rw [Multiset.mem_singleton] at hz; subst hz; exact hx n hN).act hn hh
  intro n hN
  exact this n hN _ (by simp [multiset_act_def])

/-- "Restriction to `S` loses no object permutation ... At the end, adjoining `N`
recovers the full transporter in `H`": if `H = NS` and `N` fixes the listed source
objects, then `Iso_H(X, Y) = N · Iso_S(X, Y)`. -/
theorem iso_eq_kernel_mul_supplement {H N S : Subgroup G} {X Y : Multiset Ω}
    (hNH : N ≤ H) (hSH : S ≤ H) (hcover : ∀ h ∈ H, ∃ n ∈ N, ∃ s ∈ S, h = n * s)
    (hfix : Fixes N X) :
    Iso H X Y = {h | ∃ n ∈ N, ∃ s ∈ Iso S X Y, h = n * s} := by
  ext h
  constructor
  · rintro ⟨hh, he⟩
    obtain ⟨n, hn, s, hs, rfl⟩ := hcover h hh
    refine ⟨n, hn, s, ⟨hs, ?_⟩, rfl⟩
    rw [← act_act, hfix.act_eq hn] at he
    exact he
  · rintro ⟨n, hn, s, ⟨hs, he⟩, rfl⟩
    exact ⟨H.mul_mem (hNH hn) (hSH hs), by rw [← act_act, hfix.act_eq hn, he]⟩

/-- A subgroup `K ≤ T` that contains `T ∩ A` and covers `T` modulo `A` is all of `T`.
This is the argument "these generators contain the entire kernel and map onto the
quotient" used in the paper several times. -/
theorem le_of_cover {T K A : Subgroup G} (hKT : K ≤ T) (hker : T ⊓ A ≤ K)
    (hcover : ∀ t ∈ T, ∃ k ∈ K, ∃ a ∈ A, t = k * a) : T ≤ K := by
  intro t ht
  obtain ⟨k, hk, a, ha, rfl⟩ := hcover t ht
  have haT : a ∈ T := by simpa using T.mul_mem (T.inv_mem (hKT hk)) ht
  exact K.mul_mem hk (hker ⟨haT, ha⟩)

/-- If `K` normalizes `A` and every element of `Γ` lies in `K A`, then so does every
element of the subgroup generated by `Γ`. -/
theorem closure_mem_mul {K A : Subgroup G} (hn : Normalizes K A) {Γ : Set G}
    (hΓ : ∀ γ ∈ Γ, ∃ k ∈ K, ∃ a ∈ A, γ = k * a) :
    ∀ t ∈ Subgroup.closure Γ, ∃ k ∈ K, ∃ a ∈ A, t = k * a := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem x hx => exact hΓ x hx
  | one => exact ⟨1, K.one_mem, 1, A.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk, a, ha, rfl⟩ := hx
    obtain ⟨k', hk', a', ha', rfl⟩ := hy
    refine ⟨k * k', K.mul_mem hk hk', k'⁻¹ * a * k' * a', A.mul_mem (hn.inv hk' ha) ha', ?_⟩
    group
  | inv x _ hx =>
    obtain ⟨k, hk, a, ha, rfl⟩ := hx
    refine ⟨k⁻¹, K.inv_mem hk, k * a⁻¹ * k⁻¹, hn k hk _ (A.inv_mem ha), ?_⟩
    group

end Kernels

/-! ### Coset objects -/

section Cosets

variable {G : Type*} [Group G]

/-- An object with an orbit-color tag `tag` and an underlying set `coset ⊆ G`.
For a coset object the set is a right coset `L_c h`. -/
@[ext] structure CObj (κ : Type*) (G : Type*) where
  tag : κ
  coset : Set G

variable {κ : Type*}

/-- The right `G`-action on tagged sets: `(c, C)^g = (c, Cg)`. -/
instance cobjRAct : RAct G (CObj κ G) where
  act o g := ⟨o.tag, (fun x => x * g) '' o.coset⟩
  act_one o := by cases o; simp
  act_mul o g h := by
    cases o
    simp only [Set.image_image, mul_assoc]

@[simp] theorem cobj_act_tag (o : CObj κ G) (g : G) : ((o ↼ g : CObj κ G)).tag = o.tag := rfl

theorem cobj_act_coset (o : CObj κ G) (g : G) : ((o ↼ g : CObj κ G)).coset = (fun x => x * g) '' o.coset :=
  rfl

/-- The right conjugate `L^h = h⁻¹ L h`. -/
def conjR (L : Subgroup G) (h : G) : Subgroup G where
  carrier := {g | h * g * h⁻¹ ∈ L}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have := L.mul_mem ha hb
    simpa [mul_assoc] using this
  inv_mem' := fun {a} ha => by
    have := L.inv_mem ha
    simpa [mul_assoc] using this

theorem mem_conjR {L : Subgroup G} {h g : G} : g ∈ conjR L h ↔ h * g * h⁻¹ ∈ L := Iff.rfl

/-- The coset object `L_c h` of orbit color `c`. -/
def cobj (L : κ → Subgroup G) (c : κ) (h : G) : CObj κ G :=
  ⟨c, (fun l => l * h) '' (L c : Set G)⟩

theorem mem_cobj_coset {L : κ → Subgroup G} {c : κ} {h x : G} :
    x ∈ (cobj L c h).coset ↔ x * h⁻¹ ∈ L c := by
  simp only [cobj, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨l, hl, rfl⟩; simpa using hl
  · intro hx; exact ⟨x * h⁻¹, hx, by simp⟩

@[simp] theorem cobj_act (L : κ → Subgroup G) (c : κ) (h g : G) :
    cobj L c h ↼ g = cobj L c (h * g) := by
  apply CObj.ext
  · rfl
  · ext x
    simp only [cobj_act_coset, cobj, Set.image_image, mul_assoc]

/-- Equality of coset objects: same color, and `h k⁻¹ ∈ L_c`. -/
theorem cobj_eq_iff {L : κ → Subgroup G} {c c' : κ} {h k : G} :
    cobj L c h = cobj L c' k ↔ c = c' ∧ h * k⁻¹ ∈ L c := by
  constructor
  · intro he
    have hc : c = c' := congrArg CObj.tag he
    subst hc
    refine ⟨rfl, ?_⟩
    have hmem : h ∈ (cobj L c h).coset := mem_cobj_coset.mpr (by simp)
    rw [he] at hmem
    exact mem_cobj_coset.mp hmem
  · rintro ⟨rfl, hk⟩
    apply CObj.ext
    · rfl
    · ext x
      simp only [mem_cobj_coset]
      constructor
      · intro hx
        have := (L c).mul_mem hx hk
        simpa [mul_assoc] using this
      · intro hx
        have := (L c).mul_mem hx ((L c).inv_mem hk)
        simpa [mul_assoc] using this

/-- "Different orbit colors remain distinct, even if their subgroups happen to agree." -/
theorem cobj_ne_of_tag_ne {L : κ → Subgroup G} {c c' : κ} (hc : c ≠ c') (h k : G) :
    cobj L c h ≠ cobj L c' k := fun he => hc (cobj_eq_iff.mp he).1

/-- The stabilizer of `Lh` in `R` is `R ∩ L^h`, with `L^h = h⁻¹ L h`. -/
theorem aut_cobj (R : Subgroup G) (L : κ → Subgroup G) (c : κ) (h : G) :
    Aut R (cobj L c h) = R ⊓ conjR (L c) h := by
  ext g
  rw [mem_aut, cobj_act, cobj_eq_iff, Subgroup.mem_inf, mem_conjR]
  simp [mul_assoc]

/-- "Since `N` fixes every object": a kernel `N ≤ L_c` normalized by `H` fixes `L_c h`
for every `h ∈ H`. -/
theorem cobj_act_kernel {H N : Subgroup G} {L : κ → Subgroup G} {c : κ} (hNL : N ≤ L c)
    (hn : Normalizes H N) {h n : G} (hh : h ∈ H) (hN : n ∈ N) :
    cobj L c h ↼ n = cobj L c h := by
  rw [cobj_act, cobj_eq_iff]
  exact ⟨rfl, by simpa [mul_assoc] using hNL (hn h hh n hN)⟩

/-- The stabilizer `R ∩ L^h` of `Lh` "still contains `N`". -/
theorem kernel_le_aut_cobj {H N R : Subgroup G} {L : κ → Subgroup G} {c : κ} (hNR : N ≤ R)
    (hNL : N ≤ L c) (hn : Normalizes H N) {h : G} (hh : h ∈ H) :
    N ≤ Aut R (cobj L c h) := fun _ hN => ⟨hNR hN, cobj_act_kernel hNL hn hh hN⟩

/-- The `R`-orbit test: for `R` normalized by `H` and `h, k ∈ H`, two objects `Lh, Lk`
of one color lie in one `R`-orbit exactly when `h k⁻¹ ∈ L R`. (Only `k ∈ H` is used.) -/
theorem cobj_same_orbit_iff {H R : Subgroup G} {L : κ → Subgroup G} {c : κ}
    (hR : Normalizes H R) {h k : G} (hk : k ∈ H) :
    (∃ r ∈ R, cobj L c h ↼ r = cobj L c k) ↔ ∃ l ∈ L c, ∃ r ∈ R, h * k⁻¹ = l * r := by
  simp only [cobj_act, cobj_eq_iff, true_and]
  constructor
  · rintro ⟨r, hr, hl⟩
    refine ⟨h * r * k⁻¹, hl, k * r⁻¹ * k⁻¹, hR k hk _ (R.inv_mem hr), by group⟩
  · rintro ⟨l, hl, r, hr, he⟩
    refine ⟨k⁻¹ * r⁻¹ * k, by simpa using hR.inv hk (R.inv_mem hr), ?_⟩
    have : h * (k⁻¹ * r⁻¹ * k) * k⁻¹ = l := by
      calc h * (k⁻¹ * r⁻¹ * k) * k⁻¹ = (h * k⁻¹) * r⁻¹ := by group
        _ = l := by rw [he]; group
    rw [this]; exact hl

/-- "Product factorization supplies a relative `R`-transporter": from `h k⁻¹ = l r`, the
element `k⁻¹ r⁻¹ k ∈ R` carries `Lh` to `Lk`. -/
theorem cobj_relative_transporter {L : κ → Subgroup G} {c : κ} {h k l r : G}
    (hl : l ∈ L c) (he : h * k⁻¹ = l * r) :
    cobj L c h ↼ (k⁻¹ * r⁻¹ * k) = cobj L c k := by
  rw [cobj_act, cobj_eq_iff]
  refine ⟨rfl, ?_⟩
  have : h * (k⁻¹ * r⁻¹ * k) * k⁻¹ = l := by
    calc h * (k⁻¹ * r⁻¹ * k) * k⁻¹ = (h * k⁻¹) * r⁻¹ := by group
      _ = l := by rw [he]; group
  rw [this]; exact hl

/-! #### Restriction to a supplement -/

/-- "Factoring an object representative `h = n s` replaces `Lh` by ... `L s`": a kernel
element on the left of the representative does not change the object. -/
theorem cobj_kernel_mul {L : κ → Subgroup G} {c : κ} {N : Subgroup G} (hNL : N ≤ L c)
    {n s : G} (hn : n ∈ N) : cobj L c (n * s) = cobj L c s := by
  rw [cobj_eq_iff]
  exact ⟨rfl, by simpa using hNL hn⟩

/-- The rebased object `(L ∩ S) s` over `S`: the correspondence `(L ∩ S)s ↦ Ls` is
injective on representatives in `S` ("This is a bijection of the corresponding coset
spaces"). -/
theorem cobj_supplement_eq_iff {L : κ → Subgroup G} {S : Subgroup G} {c : κ} {s s' : G}
    (hs : s ∈ S) (hs' : s' ∈ S) :
    cobj (fun c => L c ⊓ S) c s = cobj (fun c => L c ⊓ S) c s' ↔ cobj L c s = cobj L c s' := by
  simp only [cobj_eq_iff, true_and, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, S.mul_mem hs (S.inv_mem hs')⟩⟩

/-- Surjectivity of the rebasing: with `H = N S` and `N ≤ L`, every object `Lh`, `h ∈ H`,
is `Ls` for some `s ∈ S`. -/
theorem cobj_supplement_surj {H N S : Subgroup G} {L : κ → Subgroup G} {c : κ}
    (hNL : N ≤ L c) (hcover : ∀ h ∈ H, ∃ n ∈ N, ∃ s ∈ S, h = n * s) {h : G} (hh : h ∈ H) :
    ∃ s ∈ S, cobj L c h = cobj L c s := by
  obtain ⟨n, hn, s, hs, rfl⟩ := hcover h hh
  exact ⟨s, hs, cobj_kernel_mul hNL hn⟩

/-- The rebasing respects the `S`-action. -/
theorem cobj_supplement_act {L : κ → Subgroup G} {S : Subgroup G} {c : κ} (s g : G) :
    cobj (fun c => L c ⊓ S) c s ↼ g = cobj (fun c => L c ⊓ S) c (s * g) := cobj_act _ _ _ _

/-- "`L ∩ S = ⟨S ∩ N, s_l⟩`": if `N ≤ L ≤ H = NS`, `S` normalizes `N`, and each generator
`l ∈ Γ` of `L` factors as `l = n_l s_l` with `n_l ∈ N`, `s_l ∈ S`, then the elements `s_l`
together with `S ∩ N` generate `L ∩ S`. -/
theorem inf_supplement_eq_closure {N L S : Subgroup G} (hNL : N ≤ L) (hSN : Normalizes S N)
    {Γ : Set G} (hΓ : Subgroup.closure Γ = L) (fac : Γ → G × G)
    (hfac : ∀ γ : Γ, (fac γ).1 ∈ N ∧ (fac γ).2 ∈ S ∧ (γ : G) = (fac γ).1 * (fac γ).2) :
    L ⊓ S = Subgroup.closure (Set.range (fun γ : Γ => (fac γ).2)) ⊔ (S ⊓ N) := by
  set K := Subgroup.closure (Set.range (fun γ : Γ => (fac γ).2)) ⊔ (S ⊓ N) with hKdef
  have hsl : ∀ γ : Γ, (fac γ).2 ∈ L ⊓ S := by
    intro γ
    obtain ⟨h1, h2, h3⟩ := hfac γ
    refine ⟨?_, h2⟩
    have hγ : (γ : G) ∈ L := hΓ ▸ Subgroup.subset_closure γ.2
    have : (fac γ).2 = (fac γ).1⁻¹ * γ := by rw [h3]; group
    rw [this]; exact L.mul_mem (L.inv_mem (hNL h1)) hγ
  have hKle : K ≤ L ⊓ S := by
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨γ, rfl⟩; exact hsl γ
    · intro x hx; exact ⟨hNL hx.2, hx.1⟩
  apply le_antisymm _ hKle
  -- every element of `L` is `n k` with `n ∈ N`, `k ∈ K`; we use the form `k n'`.
  have hKS : K ≤ S := hKle.trans inf_le_right
  have hnK : Normalizes K N := hSN.mono hKS
  have hcov : ∀ t ∈ L, ∃ k ∈ K, ∃ a ∈ N, t = k * a := by
    rw [← hΓ]
    apply closure_mem_mul hnK
    intro γ hγ
    obtain ⟨h1, h2, h3⟩ := hfac ⟨γ, hγ⟩
    simp only at h3
    refine ⟨(fac ⟨γ, hγ⟩).2, Subgroup.mem_sup_left (Subgroup.subset_closure ⟨⟨γ, hγ⟩, rfl⟩),
      (fac ⟨γ, hγ⟩).2⁻¹ * (fac ⟨γ, hγ⟩).1 * (fac ⟨γ, hγ⟩).2, ?_, ?_⟩
    · simpa using hSN.inv h2 h1
    · conv_lhs => rw [h3]
      group
  apply le_of_cover hKle
  · rintro x ⟨⟨_, hxS⟩, hxN⟩
    exact Subgroup.mem_sup_right ⟨hxS, hxN⟩
  · rintro t ⟨htL, _⟩
    obtain ⟨k, hk, a, ha, rfl⟩ := hcov t htL
    exact ⟨k, hk, a, ha, rfl⟩

end Cosets

end GI.Multicoset
