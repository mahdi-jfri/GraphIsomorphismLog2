module

public import Workspace.Proved.VsMHardA

@[expose] public section

/-!
# The commutator pairing as a bilinear form

In a group `G`, let `N` be a subgroup whose commutators lie in a set `Z` of elements that commute
with `N`, and suppose every commutator of `N` is a power `ζ^t` of an element `ζ` of order `r`.
Then `dl(x, y) ∈ ZMod r` with `⁅x, y⁆ = ζ^dl(x, y)` is additive in `x` (`vsPDl_mul`), so the key
`x ↦ (dl(x, g_j))_j` is a homomorphism from `N` to `(ZMod r)^k`. An element has key `0` iff it
commutes with every `g_j` (`vsPDl_eq_zero_iff`).
-/

namespace GI.Proved

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The hypotheses: commutators of `N` commute with `N` and are powers of `ζ`, of order `r`. -/
structure VsPPairHyp (N : Subgroup G) (r : ℕ) (ζ : G) : Prop where
  ord : orderOf ζ = r
  comm : ∀ x ∈ N, ∀ y ∈ N, ∀ z ∈ N, Commute ⁅x, y⁆ z
  pow : ∀ x ∈ N, ∀ y ∈ N, ∃ a : ZMod r, ⁅x, y⁆ = ζ ^ a.val

/-- The discrete logarithm of `⁅x, y⁆`. -/
noncomputable def vsPDl (r : ℕ) (ζ x y : G) : ZMod r := vsMDl r ζ ⁅x, y⁆

variable {N : Subgroup G} {r : ℕ} {ζ : G}

theorem VsPPairHyp.spec (h : VsPPairHyp N r ζ) {x y : G} (hx : x ∈ N) (hy : y ∈ N) :
    ⁅x, y⁆ = ζ ^ (vsPDl r ζ x y).val :=
  vsMDl_spec (h.pow x hx y hy)

theorem VsPPairHyp.pow_r (h : VsPPairHyp N r ζ) : ζ ^ r = 1 := by
  rw [← h.ord]; exact pow_orderOf_eq_one ζ

/-- **Additivity in the first argument.** -/
theorem VsPPairHyp.dl_mul [NeZero r] (h : VsPPairHyp N r ζ) {x y z : G} (hx : x ∈ N) (hy : y ∈ N)
    (hz : z ∈ N) : vsPDl r ζ (x * y) z = vsPDl r ζ x z + vsPDl r ζ y z := by
  apply vsM_zp_inj h.ord
  rw [← h.spec (mul_mem hx hy) hz, vsM_zp_add h.pow_r, ← h.spec hx hz, ← h.spec hy hz]
  exact vsM_comm_mul_left (h.comm y hy z hz x hx) (h.comm y hy z hz z hz)

theorem VsPPairHyp.dl_one [NeZero r] (h : VsPPairHyp N r ζ) {z : G} (hz : z ∈ N) :
    vsPDl r ζ 1 z = 0 := by
  have := h.dl_mul (one_mem N) (one_mem N) hz
  rw [one_mul] at this
  exact (add_eq_left.1 this.symm)

theorem VsPPairHyp.dl_pow [NeZero r] (h : VsPPairHyp N r ζ) {x z : G} (hx : x ∈ N) (hz : z ∈ N) :
    ∀ a : ℕ, vsPDl r ζ (x ^ a) z = (a : ZMod r) * vsPDl r ζ x z
  | 0 => by rw [pow_zero, h.dl_one hz, Nat.cast_zero, zero_mul]
  | a + 1 => by
    rw [pow_succ, h.dl_mul (pow_mem hx a) hx hz, h.dl_pow hx hz a]; push_cast; ring

theorem VsPPairHyp.dl_eq_zero_iff [NeZero r] (h : VsPPairHyp N r ζ) {x y : G} (hx : x ∈ N)
    (hy : y ∈ N) : vsPDl r ζ x y = 0 ↔ x * y = y * x := by
  rw [← commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro e; rw [h.spec hx hy, e]; simp
  · intro e
    apply vsM_zp_inj h.ord
    rw [← h.spec hx hy, e]; simp

end GI.Proved

/-! ### The quotient `N̄ = N / (N ∩ S)` as a vector space over `ZMod r` -/

namespace GI.Proved

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The hypotheses on `N` and the "scalars" `S`: `S` commutes with `N`, commutators and `r`-th
powers of `N` lie in `S`. -/
structure VsPQuotHyp (N S : Subgroup G) (r : ℕ) : Prop where
  sc : ∀ s ∈ S, ∀ x ∈ N, s * x = x * s
  comm : ∀ x ∈ N, ∀ y ∈ N, ⁅x, y⁆ ∈ S
  pow : ∀ x ∈ N, x ^ r ∈ S

variable {N S : Subgroup G} {r : ℕ}

theorem VsPQuotHyp.normal (h : VsPQuotHyp N S r) : (S.subgroupOf N).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have : ((g * n * g⁻¹ : N) : G) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← h.sc _ hn _ g.2, mul_inv_cancel_right]
    rw [this]; exact hn⟩

/-- The quotient is commutative. -/
abbrev VsPQuotHyp.commGroup (h : VsPQuotHyp N S r) :
    @CommGroup (N ⧸ S.subgroupOf N) :=
  haveI := h.normal
  { (inferInstance : Group (N ⧸ S.subgroupOf N)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hc := h.comm _ (N.inv_mem b.2) _ (N.inv_mem a.2)
      have : (((a * b)⁻¹ * (b * a) : N) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]; group
      rw [this]; exact hc }

end GI.Proved

namespace GI.Proved

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The product `∏ g_i ^ e_i` (in list order; missing exponents count as `0`). -/
def vsPW (gs : List G) (e : List ℕ) : G :=
  (List.zipWith (fun g a => g ^ a) gs e).prod

theorem vsPW_nil (e : List ℕ) : vsPW ([] : List G) e = 1 := by simp [vsPW]

theorem vsPW_cons (g : G) (gs : List G) (a : ℕ) (e : List ℕ) :
    vsPW (g :: gs) (a :: e) = g ^ a * vsPW gs e := by simp [vsPW]

variable {N : Subgroup G} {r : ℕ} {ζ : G}

theorem vsPW_mem {gs : List G} (hgs : ∀ g ∈ gs, g ∈ N) : ∀ e, vsPW gs e ∈ N := by
  induction gs with
  | nil => intro e; rw [vsPW_nil]; exact one_mem N
  | cons g gs ih =>
    intro e
    cases e with
    | nil => simp [vsPW]
    | cons a e =>
      rw [vsPW_cons]
      exact mul_mem (pow_mem (hgs g (by simp)) a) (ih (fun x hx => hgs x (by simp [hx])) e)

/-- **The key of a product.** -/
theorem VsPPairHyp.dl_W [NeZero r] (h : VsPPairHyp N r ζ) {gs : List G} (hgs : ∀ g ∈ gs, g ∈ N)
    {z : G} (hz : z ∈ N) : ∀ e : List ℕ, e.length = gs.length →
      vsPDl r ζ (vsPW gs e) z =
        ((List.zipWith (fun g (a : ℕ) => (a : ZMod r) * vsPDl r ζ g z) gs e).sum) := by
  induction gs with
  | nil => intro e _; rw [vsPW_nil, h.dl_one hz]; simp
  | cons g gs ih =>
    intro e he
    cases e with
    | nil => simp at he
    | cons a e =>
      have hg := hgs g (by simp)
      have hgs' : ∀ x ∈ gs, x ∈ N := fun x hx => hgs x (by simp [hx])
      rw [vsPW_cons, h.dl_mul (pow_mem hg a) (vsPW_mem hgs' e) hz, h.dl_pow hg hz,
        ih hgs' e (by simpa using he)]
      simp

end GI.Proved

namespace GI.Proved

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem vsP_zipWith_ofFn {α β γ : Type*} (f : α → β → γ) (l : List α) (m : List β)
    (h : m.length = l.length) :
    List.zipWith f l m = List.ofFn (fun i : Fin l.length => f l[i] (m[i]'(by rw [h]; exact i.2))) := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp

/-- The exponent list of a vector over `ZMod r`. -/
def vsPExp {k r : ℕ} (a : Fin k → ZMod r) : List ℕ := (List.finRange k).map fun i => (a i).val

theorem vsPExp_length {k r : ℕ} (a : Fin k → ZMod r) : (vsPExp a).length = k := by simp [vsPExp]

variable {N S : Subgroup G} {r : ℕ} {ζ : G}

/-- **The radical is in `S`.** Suppose `N = ⟨gs⟩`, the kernel of the Gram matrix
`(dl(g_i, g_j))` is spanned by vectors `A` whose words lie in `S`. Then every `x ∈ N` commuting
with all `g_j` lies in `S`. -/
theorem vsP_radical [Fact r.Prime] (hQ : VsPQuotHyp N S r) (hP : VsPPairHyp N r ζ) {gs : List G}
    (hN : N = Subgroup.closure {g | g ∈ gs}) {A : List (Fin gs.length → ZMod r)}
    (hker : ∀ e : Fin gs.length → ZMod r,
      (∀ j : Fin gs.length, ∑ i, e i * vsPDl r ζ gs[i] gs[j] = 0) →
        e ∈ Submodule.span (ZMod r) {a | a ∈ A})
    (hA : ∀ a ∈ A, vsPW gs (vsPExp a) ∈ S) :
    ∀ x ∈ N, (∀ g ∈ gs, x * g = g * x) → x ∈ S := by
  classical
  haveI : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  letI : AddCommGroup (ZMod r) := (ZMod.commRing r).toAddCommGroup
  have hgN : ∀ g ∈ gs, g ∈ N := fun g hg => hN ▸ Subgroup.subset_closure hg
  haveI := hQ.normal
  letI : CommGroup (N ⧸ S.subgroupOf N) := hQ.commGroup
  have hQr : ∀ q : N ⧸ S.subgroupOf N, q ^ r = 1 := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    erw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      SubgroupClass.coe_pow]
    exact hQ.pow y y.2
  let mk : G → N ⧸ S.subgroupOf N := fun x =>
    if hx : x ∈ N then ((⟨x, hx⟩ : N) : N ⧸ S.subgroupOf N) else 1
  have hmk : ∀ x (hx : x ∈ N), mk x = ((⟨x, hx⟩ : N) : N ⧸ S.subgroupOf N) := fun x hx => by
    simp only [mk, dif_pos hx]
  have hmk_mul : ∀ x ∈ N, ∀ y ∈ N, mk (x * y) = mk x * mk y := by
    intro x hx y hy
    rw [hmk _ (mul_mem hx hy), hmk x hx, hmk y hy]; rfl
  have hmk_pow : ∀ x ∈ N, ∀ a : ℕ, mk (x ^ a) = mk x ^ a := by
    intro x hx a
    induction a with
    | zero => rw [pow_zero, pow_zero, hmk 1 (one_mem N)]; rfl
    | succ a ih => rw [pow_succ, pow_succ, hmk_mul _ (pow_mem hx a) _ hx, ih]
  have hmk_one : ∀ x (hx : x ∈ N), mk x = 1 ↔ x ∈ S := by
    intro x hx
    rw [hmk x hx, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hgs' : ∀ i : Fin gs.length, gs[i] ∈ N := fun i => hgN _ (List.getElem_mem _)
  let Ψ : (Fin gs.length → ZMod r) → N ⧸ S.subgroupOf N := fun e => ∏ i, mk gs[i] ^ (e i).val
  have hpowval : ∀ (q : N ⧸ S.subgroupOf N) (a b : ZMod r), q ^ (a + b).val = q ^ a.val * q ^ b.val :=
    fun q a b => vsM_zp_add (hQr q) a b
  have hpowmul : ∀ (q : N ⧸ S.subgroupOf N) (a b : ZMod r), q ^ (a * b).val = (q ^ b.val) ^ a.val :=
    fun q a b => vsM_zp_mul (hQr q) a b
  have hΨadd : ∀ e e', Ψ (e + e') = Ψ e * Ψ e' := by
    intro e e'
    simp only [Ψ, Pi.add_apply, hpowval, Finset.prod_mul_distrib]
  have hΨsmul : ∀ (c : ZMod r) e, Ψ (c • e) = Ψ e ^ c.val := by
    intro c e
    simp only [Ψ, Pi.smul_apply, smul_eq_mul, hpowmul, Finset.prod_pow]
  have hΨzero : Ψ 0 = 1 := by simp [Ψ]
  -- the word of a vector
  have hW : ∀ a : Fin gs.length → ZMod r, Ψ a = mk (vsPW gs (vsPExp a)) := by
    intro a
    have hlen : (vsPExp a).length = gs.length := vsPExp_length a
    have hz : vsPW gs (vsPExp a) = (List.ofFn fun i : Fin gs.length => gs[i] ^ (a i).val).prod := by
      unfold vsPW
      rw [vsP_zipWith_ofFn _ _ _ hlen]
      congr 1
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp [vsPExp]
    have hprod : ∀ l : List G, (∀ x ∈ l, x ∈ N) → mk l.prod = (l.map mk).prod := by
      intro l hl
      induction l with
      | nil => simp only [List.prod_nil, List.map_nil]; rw [hmk 1 (one_mem N)]; rfl
      | cons x l ih =>
        have hx : x ∈ N := hl x (by simp)
        have hl' : ∀ z ∈ l, z ∈ N := fun z hz => hl z (by simp [hz])
        rw [List.prod_cons, hmk_mul x hx _ (Subgroup.list_prod_mem N hl'), List.map_cons,
          List.prod_cons, ih hl']
    rw [hz, hprod _ (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact pow_mem (hgs' i) _), List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => (hmk_pow _ (hgs' i) _).symm
  have hr1 : (1 : ZMod r).val = 1 := ZMod.val_one r
  -- every class is a value of `Ψ`
  have hsurj : ∀ x ∈ N, ∃ e, Ψ e = mk x := by
    intro x hx
    rw [hN] at hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      refine ⟨Pi.single ⟨i, hi⟩ 1, ?_⟩
      simp only [Ψ]
      rw [Finset.prod_eq_single (⟨i, hi⟩ : Fin gs.length)]
      · rw [Pi.single_eq_same, hr1, pow_one]; rfl
      · intro j _ hj; rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
      · simp
    | one => exact ⟨0, by rw [hΨzero, hmk 1 (one_mem N)]; rfl⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨e, he⟩ := ihx
      obtain ⟨e', he'⟩ := ihy
      exact ⟨e + e', by rw [hΨadd, he, he', hmk_mul x (hN ▸ hx) y (hN ▸ hy)]⟩
    | inv x hx ihx =>
      obtain ⟨e, he⟩ := ihx
      refine ⟨-e, ?_⟩
      have h1 : Ψ (-e) * Ψ e = 1 := by rw [← hΨadd, neg_add_cancel, hΨzero]
      have h2 : mk x⁻¹ * mk x = 1 := by
        rw [← hmk_mul _ (inv_mem (hN ▸ hx)) _ (hN ▸ hx), inv_mul_cancel, hmk 1 (one_mem N)]; rfl
      rw [he] at h1
      exact mul_right_cancel (h1.trans h2.symm)
  -- the main argument
  intro x hx hxc
  obtain ⟨e, he⟩ := hsurj x hx
  have hwN := vsPW_mem hgN (vsPExp e)
  have hxw : x⁻¹ * vsPW gs (vsPExp e) ∈ S := by
    have h1 : mk (x⁻¹ * vsPW gs (vsPExp e)) = 1 := by
      rw [hmk_mul _ (inv_mem hx) _ hwN, ← hW, he, ← hmk_mul _ (inv_mem hx) _ hx, inv_mul_cancel,
        hmk 1 (one_mem N)]; rfl
    exact (hmk_one _ (mul_mem (inv_mem hx) hwN)).1 h1
  have hkey : ∀ j : Fin gs.length, ∑ i, e i * vsPDl r ζ gs[i] gs[j] = 0 := by
    intro j
    have hgj := hgs' j
    have h0 : vsPDl r ζ x gs[j] = 0 := (hP.dl_eq_zero_iff hx hgj).2 (hxc _ (List.getElem_mem _))
    have hsN : x⁻¹ * vsPW gs (vsPExp e) ∈ N := mul_mem (inv_mem hx) hwN
    have hs0 : vsPDl r ζ (x⁻¹ * vsPW gs (vsPExp e)) gs[j] = 0 :=
      (hP.dl_eq_zero_iff hsN hgj).2 (hQ.sc _ hxw _ hgj)
    have hsplit : vsPW gs (vsPExp e) = x * (x⁻¹ * vsPW gs (vsPExp e)) := by group
    have hd := hP.dl_mul hx hsN hgj
    rw [← hsplit, h0, hs0, add_zero] at hd
    have hz := vsP_zipWith_ofFn (fun g (a : ℕ) => (a : ZMod r) * vsPDl r ζ g gs[j]) gs (vsPExp e)
      (vsPExp_length e)
    rw [hP.dl_W hgN hgj (vsPExp e) (vsPExp_length e), hz, List.sum_ofFn] at hd
    refine (Finset.sum_congr rfl fun i _ => ?_).trans hd
    simp [vsPExp, ZMod.natCast_zmod_val]
  have hspanP : ∀ v ∈ Submodule.span (ZMod r) {a | a ∈ A}, Ψ v = 1 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem a ha =>
      rw [hW]
      exact (hmk_one _ (vsPW_mem hgN _)).2 (hA a ha)
    | zero => exact hΨzero
    | add a b _ _ ha hb => rw [hΨadd, ha, hb, mul_one]
    | smul c a _ ha => rw [hΨsmul, ha, one_pow]
  have hΨ1 := hspanP e (hker e hkey)
  rw [hΨ1] at he
  exact (hmk_one x hx).1 he.symm

end GI.Proved

namespace GI.Proved

open scoped commutatorElement

variable {G : Type*} [Group G] {N S : Subgroup G} {r : ℕ} {ζ : G}

theorem VsPPairHyp.dl_inv [NeZero r] (h : VsPPairHyp N r ζ) {x z : G} (hx : x ∈ N) (hz : z ∈ N) :
    vsPDl r ζ x⁻¹ z = - vsPDl r ζ x z := by
  have := h.dl_mul (inv_mem hx) hx hz
  rw [inv_mul_cancel, h.dl_one hz] at this
  exact eq_neg_of_add_eq_zero_left this.symm

/-- **Keys are injective modulo `S`** when the radical lies in `S`. -/
theorem vsP_key_inj [NeZero r] (hP : VsPPairHyp N r ζ) {gs : List G}
    (hN : N = Subgroup.closure {g | g ∈ gs})
    (hrad : ∀ x ∈ N, (∀ g ∈ gs, x * g = g * x) → x ∈ S) {x y : G} (hx : x ∈ N) (hy : y ∈ N)
    (hk : ∀ g ∈ gs, vsPDl r ζ x g = vsPDl r ζ y g) : x⁻¹ * y ∈ S := by
  have hgN : ∀ g ∈ gs, g ∈ N := fun g hg => hN ▸ Subgroup.subset_closure hg
  refine hrad _ (mul_mem (inv_mem hx) hy) fun g hg => ?_
  rw [← hP.dl_eq_zero_iff (mul_mem (inv_mem hx) hy) (hgN g hg), hP.dl_mul (inv_mem hx) hy (hgN g hg),
    hP.dl_inv hx (hgN g hg), hk g hg, neg_add_cancel]

end GI.Proved

namespace GI.Proved

variable {G : Type*} [Group G]

/-- **Invariance under the generated group.** If a set `Cl` is closed under right multiplication
by `S` (which is normalized by the generators) and under conjugation by the generators, it is
closed under conjugation by the generated group (in a finite group). -/
theorem vsP_conj_closed [Finite G] {S : Subgroup G} {hs : Set G} {Cl : Set G}
    (hS : ∀ h ∈ hs, ∀ s ∈ S, h * s * h⁻¹ ∈ S)
    (hCl : ∀ x ∈ Cl, ∀ s ∈ S, x * s ∈ Cl) (hgen : ∀ h ∈ hs, ∀ x ∈ Cl, h * x * h⁻¹ ∈ Cl) :
    ∀ g ∈ Subgroup.closure hs, ∀ x ∈ Cl, g * x * g⁻¹ ∈ Cl := by
  -- the conjugations that keep `Cl` and normalize `S`
  let K : Submonoid G :=
    { carrier := {g | (∀ x ∈ Cl, g * x * g⁻¹ ∈ Cl) ∧ ∀ s ∈ S, g * s * g⁻¹ ∈ S}
      mul_mem' := by
        rintro a b ⟨ha, has⟩ ⟨hb, hbs⟩
        refine ⟨fun x hx => ?_, fun s hs' => ?_⟩
        · have := ha _ (hb x hx)
          have e : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
          rw [e]; exact this
        · have e : a * b * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
          rw [e]; exact has _ (hbs s hs')
      one_mem' := ⟨fun x hx => by simpa using hx, fun s hs' => by simpa using hs'⟩ }
  have hK : ∀ g ∈ K, g⁻¹ ∈ K := by
    intro g hg
    have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
    have e : g⁻¹ = g ^ (orderOf g - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hfin.orderOf_pos,
        pow_orderOf_eq_one]
    rw [e]; exact pow_mem hg _
  let K' : Subgroup G := { K with inv_mem' := fun {g} hg => hK g hg }
  have hgK : hs ⊆ K' := fun h hh => ⟨hgen h hh, hS h hh⟩
  intro g hg x hx
  exact ((Subgroup.closure_le K').2 hgK hg).1 x hx

end GI.Proved

namespace GI.Proved

open scoped commutatorElement

variable {G : Type*} [Group G] {N : Subgroup G} {r : ℕ} {ζ : G}

/-- The key of `x` with respect to the generators `gs`. -/
noncomputable def vsPK (r : ℕ) (ζ : G) (gs : List G) (x : G) : Fin gs.length → ZMod r :=
  fun j => vsPDl r ζ x gs[j]

theorem VsPPairHyp.key_mul [NeZero r] (h : VsPPairHyp N r ζ) {gs : List G}
    (hgs : ∀ g ∈ gs, g ∈ N) {x y : G} (hx : x ∈ N) (hy : y ∈ N) :
    vsPK r ζ gs (x * y) = vsPK r ζ gs x + vsPK r ζ gs y := by
  funext j; exact h.dl_mul hx hy (hgs _ (List.getElem_mem _))

theorem VsPPairHyp.key_inv [NeZero r] (h : VsPPairHyp N r ζ) {gs : List G}
    (hgs : ∀ g ∈ gs, g ∈ N) {x : G} (hx : x ∈ N) : vsPK r ζ gs x⁻¹ = - vsPK r ζ gs x := by
  funext j; exact h.dl_inv hx (hgs _ (List.getElem_mem _))

theorem VsPPairHyp.key_one [NeZero r] (h : VsPPairHyp N r ζ) {gs : List G}
    (hgs : ∀ g ∈ gs, g ∈ N) : vsPK r ζ gs 1 = 0 := by
  funext j; exact h.dl_one (hgs _ (List.getElem_mem _))

theorem VsPPairHyp.key_pow [NeZero r] (h : VsPPairHyp N r ζ) {gs : List G}
    (hgs : ∀ g ∈ gs, g ∈ N) {x : G} (hx : x ∈ N) (a : ℕ) :
    vsPK r ζ gs (x ^ a) = (a : ZMod r) • vsPK r ζ gs x := by
  funext j; simp only [Pi.smul_apply, smul_eq_mul]; exact h.dl_pow hx (hgs _ (List.getElem_mem _)) a

/-- Keys of the generated subgroup lie in the span of the keys. -/
theorem VsPPairHyp.key_closure [NeZero r] (h : VsPPairHyp N r ζ) {gs : List G}
    (hgs : ∀ g ∈ gs, g ∈ N) {T : Set G} (hT : T ⊆ N) :
    ∀ x ∈ Subgroup.closure T, vsPK r ζ gs x ∈ Submodule.span (ZMod r) (vsPK r ζ gs '' T) := by
  intro x hx
  have hTN : Subgroup.closure T ≤ N := (Subgroup.closure_le _).2 hT
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | one => rw [h.key_one hgs]; exact Submodule.zero_mem _
  | mul x y hx hy ihx ihy =>
    rw [h.key_mul hgs (hTN hx) (hTN hy)]; exact Submodule.add_mem _ ihx ihy
  | inv x hx ihx => rw [h.key_inv hgs (hTN hx)]; exact Submodule.neg_mem _ ihx

/-- Every vector of the span is the key of an element of the generated subgroup. -/
theorem VsPPairHyp.key_span [NeZero r] (h : VsPPairHyp N r ζ) {gs : List G}
    (hgs : ∀ g ∈ gs, g ∈ N) {T : Set G} (hT : T ⊆ N) :
    ∀ v ∈ Submodule.span (ZMod r) (vsPK r ζ gs '' T), ∃ x ∈ Subgroup.closure T, vsPK r ζ gs x = v := by
  intro v hv
  have hTN : Subgroup.closure T ≤ N := (Subgroup.closure_le _).2 hT
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨x, Subgroup.subset_closure hx, rfl⟩
  | zero => exact ⟨1, one_mem _, h.key_one hgs⟩
  | add v w _ _ hv hw =>
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨y, hy, rfl⟩ := hw
    exact ⟨x * y, mul_mem hx hy, h.key_mul hgs (hTN hx) (hTN hy)⟩
  | smul c v _ hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    refine ⟨x ^ c.val, pow_mem hx _, ?_⟩
    rw [h.key_pow hgs (hTN hx), ZMod.natCast_zmod_val]

end GI.Proved
