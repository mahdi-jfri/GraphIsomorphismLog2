module

public import Workspace.Impl.TermRecStepW
public import Workspace.MulticosetTransport

@[expose] public section

/-!
# T5, rebasing into `H_x`-objects (`b + 96`)

When `ℓ > 0` in the pairwise step (`tmRiYE`), the recursive call on `(ℓ, H_x, A_x, S', T)` needs
its input objects to have stabilizers inside `H_x` (`TmRiListIn (gens hs)`), whereas the objects of
`S' = S^{τ⁻¹}` and `T` only have stabilizers inside `H` (in fact inside `B = A ⊔ H_x`).

The function `b + 96` (`tmRiRebMainE`) rebases `S'` and `T` into `H_x`-objects before calling `b`:
1. Partition `S'` and `T` into `⊥`-orbits `PX` and `PY` (`Ps = PX ++ PY`), which are also their
   `A_x`-orbits because `A_x = A ∩ H_x` fixes `S'` and `T`.
2. Form `B = A ⊔ H_x` (`gens σB`).
3. For each pair of pieces `(Q, Q')` in `Ps`, compute `Iso_{H_x}(Q, Q')` (`tmRiRebPairE`, `b + 98`)
   by calling `gObj` (`TermGlueObjSpec`) on `(B, A_x, A, [x_0, q_1], [x_0, q'_1], B, 1)`, where
   `x_0` is `ox` recolored to `0` (forcing the transporter in `B` to fix `ox` and hence lie in
   `H_x`) and `q_1, q'_1` are `Q[0], Q'[0]` recolored to `1`.
4. Form the `H_x`-profiles `obsS` and `obsT` (`b + 78`) with respect to `A_x` and the table. By
   `tmRi_profs_in` their stabilizers lie in `H_x`, and since `A_x` fixes `S'` and `T`,
   `Iso_{H_x}(obsS, obsT) = Iso_{H_x}(S', T)`.
5. Call `b` at fuel `ℓ` on `(ℓ, H_x, A_x, obsS, obsT)`.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Machine (BinOp)
open scoped Pointwise commutatorElement
open GI.Cited (Val encPerm encGroup gens SolvableCosetIntersection DerivedSubgroup Membership)

variable {n : ℕ}

/-- **The recursion at fuel `ℓ`, as a hypothesis**: `TermRecSpec` at one fuel, with the
answer as a coset of `Perm (Fin n)` and a cost bound `T`. -/
def TmRiIH (P : Program) (b n M ℓ T : ℕ) : Prop :=
  ∀ (σH σN : List (Perm (Fin n))) (X Y : List (TmRiO n)),
    (0 < ℓ → TmRiListIn (gens σH) (X ++ Y)) →
    gens σN ≤ gens σH → GI.Multicoset.Normalizes (gens σH) (gens σN) →
    relDerived (gens σH) (gens σN) ℓ ≤ gens σN → ℓ ≤ n ^ 2 + 5 →
    Fixes (gens σN) (tmGlMs X) → Fixes (gens σN) (tmGlMs Y) →
    σH.length ≤ n ^ 2 → σN.length ≤ n ^ 2 → X.length ≤ M → Y.length ≤ M →
    TmRecObjOK M (X ++ Y) →
    FunAll P b (tmRecIn ℓ σH σN X Y) (fun u cost =>
      CosetC n u (Iso (gens σH) (tmGlMs X) (tmGlMs Y)) ∧ cost ≤ T)

/-- `letE` with additive cost bounds. -/
theorem tmRi_letE {P : Program} {env : List Val} {e body : Expr} {Ra : Val → ℕ → Prop}
    {R : Val → Prop} {Ka Wo B : ℕ} (ha : EvalAll P env e Ra) (hKa : ∀ v ca, Ra v ca → ca ≤ Ka)
    (hb : ∀ v ca, Ra v ca →
      EvalAll P (env ++ [v]) body (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ B)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Ka + B + Wo + 1) :=
  EvalAll.letE ha fun v ca h => (hb v ca h).mono fun w cb hw =>
    ⟨hw.1, hw.2.1, by have := hKa v ca h; omega⟩

theorem tmRi_letD {P : Program} {env : List Val} {e body : Expr} {v : Val} {ca : ℕ}
    {R : Val → Prop} {Wo B : ℕ} (ha : Det P env e v ca)
    (hb : EvalAll P (env ++ [v]) body (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ B)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ ca + B + Wo + 1) :=
  tmRi_letE ha (fun _ _ h => h.2) fun v' ca' h => by obtain ⟨rfl, -⟩ := h; exact hb

/-- `letE` with a cost budget. -/
theorem tmRi_letB {P : Program} {env : List Val} {e body : Expr} {Ra : Val → ℕ → Prop}
    {R : Val → Prop} {Ka Wo Bud : ℕ} (ha : EvalAll P env e Ra)
    (hKa : ∀ v ca, Ra v ca → ca ≤ Ka) (hB : Ka + Wo + 1 ≤ Bud)
    (hb : ∀ v ca, Ra v ca →
      EvalAll P (env ++ [v]) body (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ Bud - Ka - Wo - 1)) :
    EvalAll P env (.letE e body) (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) :=
  EvalAll.letE ha fun v ca h => (hb v ca h).mono fun w cb hw =>
    ⟨hw.1, hw.2.1, by have := hKa v ca h; omega⟩

/-- `ite` with a cost budget. -/
theorem tmRi_iteB {P : Program} {env : List Val} {c t e : Expr} {x cc : ℕ}
    {R : Val → Prop} {Wo Bud : ℕ} (hc : Det P env c (.nat x) cc) (hB : cc + Wo + 1 ≤ Bud)
    (ht : x ≠ 0 → EvalAll P env t (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ Bud - cc - Wo - 1))
    (he : x = 0 → EvalAll P env e (fun w cb => R w ∧ w.wt ≤ Wo ∧ cb ≤ Bud - cc - Wo - 1)) :
    EvalAll P env (.ite c t e) (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) :=
  (sup_ite hc ht he).mono fun w c' ⟨ce, ⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, by omega⟩

/-- A final deterministic step with a cost budget. -/
theorem tmRi_detB {P : Program} {env : List Val} {e : Expr} {v : Val} {cv : ℕ}
    {R : Val → Prop} {Wo Bud : ℕ} (h : Det P env e v cv) (hR : R v) (hw : v.wt ≤ Wo)
    (hc : cv ≤ Bud) : EvalAll P env e (fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) :=
  h.post fun c' hc' => ⟨hR, hw, by omega⟩

theorem TmRecObjOK.of_same {M : ℕ} {L L' : List (TmRiO n)} (h : TmRecObjOK M L)
    (h' : ∀ o ∈ L', ∃ o₀ ∈ L, o.1 = o₀.1 ∧ o.2.1 = o₀.2.1) : TmRecObjOK M L' := by
  intro o ho
  obtain ⟨o₀, ho₀, e1, e2⟩ := h' o ho
  obtain ⟨h1, h2, h3⟩ := h o₀ ho₀
  refine ⟨e2 ▸ h1, e1 ▸ h2, fun o' ho' hc => ?_⟩
  obtain ⟨o₁, ho₁, e1', e2'⟩ := h' o' ho'
  rw [e2, e2']
  exact h3 o₁ ho₁ (by rw [← e1, ← e1', hc])

theorem tmRi_wt_ansC {u : Val} {C : Set (Perm (Fin n))} (h : CosetC n u C) :
    u.wt ≤ 700 * (n + 1) ^ 6 := by
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  rcases h with ⟨rfl, -⟩ | ⟨x, hs, rfl, hl, -⟩
  · have : (Val.list []).wt ≤ 5 := by decide
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega
  · have := wt_list2_le (encPerm x) (encGroup hs)
    have := wt_encPerm_le x
    have := wt_encGroup_le_sq hl
    have : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    omega

/-- The generic bound of the small steps of one level. -/
def tmRiSQ (n M : ℕ) : ℕ := 10 ^ 5 * (tmRiVs n M + 1) ^ 2

/-- The cost of the profiles of one side, besides the small steps. -/
noncomputable def tmRiPrC (hmem : Membership) (n M : ℕ) : ℕ :=
  2 * M * tmRiProfC hmem n (3 * tmRiVs n M) + mapK * (2 * M + 1) * (tmRiVs n M + 2000 * tmRiB n M + 5) +
    8000 * (2 * M + 1) ^ 3

/-! ### Mathematical helpers for rebasing -/

theorem normal_subgroupOf_of_normalizes {G : Type*} [Group G] {H N : Subgroup G}
    (hn : GI.Multicoset.Normalizes H N) : (N.subgroupOf H).Normal :=
  ⟨fun n hn' h => hn h.1 h.2 n.1 hn'⟩

theorem derivedSeries_quot_le_relDerived {G : Type*} [Group G] (H N : Subgroup G)
    [(N.subgroupOf H).Normal] :
    ∀ i, derivedSeries (H ⧸ N.subgroupOf H) i ≤
      ((relDerived H N i).subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))
  | 0 => by
    intro x _
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf H) x
    exact ⟨h, h.2, rfl⟩
  | i + 1 => by
    have ih := derivedSeries_quot_le_relDerived H N i
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono ih ih).trans ?_
    rw [← Subgroup.map_commutator]
    refine Subgroup.map_mono fun x hx => ?_
    rw [Subgroup.mem_subgroupOf, relDerived_succ]
    have hle : ((relDerived H N i).subgroupOf H).map H.subtype ≤ relDerived H N i :=
      Subgroup.map_comap_le H.subtype (relDerived H N i)
    have hx' : (x : G) ∈ ⁅((relDerived H N i).subgroupOf H).map H.subtype,
        ((relDerived H N i).subgroupOf H).map H.subtype⁆ := by
      rw [← Subgroup.map_commutator]
      exact Subgroup.mem_map_of_mem _ hx
    exact (le_sup_left : ⁅relDerived H N i, relDerived H N i⁆ ≤
      ⁅relDerived H N i, relDerived H N i⁆ ⊔ N) (Subgroup.commutator_mono hle hle hx')

theorem isSolvable_quot_of_relDerived {G : Type*} [Group G] {H N : Subgroup G}
    [(N.subgroupOf H).Normal] {d : ℕ} (h : relDerived H N d ≤ N) :
    Group.IsSolvable (H ⧸ N.subgroupOf H) := by
  refine ⟨⟨d, eq_bot_iff.2 ?_⟩⟩
  refine (derivedSeries_quot_le_relDerived H N d).trans ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  exact h hx

theorem isSolvable_quot_of_le {G : Type*} [Group G] {H N B K : Subgroup G}
    [hN : (N.subgroupOf H).Normal] [hKB : (K.subgroupOf B).Normal]
    (hsol : Group.IsSolvable (H ⧸ N.subgroupOf H)) (hBH : B ≤ H) (hNK : N ≤ K) :
    Group.IsSolvable (B ⧸ K.subgroupOf B) := by
  let f : B →* H ⧸ N.subgroupOf H := (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion hBH)
  have hker : f.ker ≤ K.subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, QuotientGroup.ker_mk',
      Subgroup.mem_subgroupOf] at hb
    exact hNK hb
  have : Group.IsSolvable (B ⧸ f.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.quotientKerEquivRange f).injective
  refine Group.isSolvable_of_surjective (f := QuotientGroup.map f.ker (K.subgroupOf B)
    (MonoidHom.id B) hker) ?_
  intro x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk b, rfl⟩

theorem tmRi_color_of_sameOrb {A : Subgroup (Perm (Fin n))} {o o' : TmRiO n}
    (h : SameOrb A (tmRiObj o) (tmRiObj o')) : o.1 = o'.1 := by
  obtain ⟨a, _, ha⟩ := h
  exact (congrArg CObj.tag ha).symm.trans rfl |>.symm

theorem tmRi_recolor_act_eq {c : ℕ} {o o' : TmRiO n} (hc : o.1 = o'.1) {g : Perm (Fin n)} :
    tmRiObj (c, o.2.1, o.2.2) ↼ g = tmRiObj (c, o'.2.1, o'.2.2) ↔ tmRiObj o ↼ g = tmRiObj o' := by
  simp only [tmRiObj, tmGlObj, CObj.ext_iff, cobj_act_tag, cobj_act_coset, hc, true_and]

theorem tmRi_recolor_sameOrb {A : Subgroup (Perm (Fin n))} (c : ℕ) {o o' : TmRiO n}
    (h : SameOrb A (tmRiObj o) (tmRiObj o')) :
    SameOrb A (tmRiObj (c, o.2.1, o.2.2)) (tmRiObj (c, o'.2.1, o'.2.2)) := by
  have hc := tmRi_color_of_sameOrb h
  obtain ⟨a, ha, hact⟩ := h
  exact ⟨a, ha, (tmRi_recolor_act_eq hc).2 hact⟩

theorem tmRi_recolor_sameOrb_act {A : Subgroup (Perm (Fin n))} (c : ℕ) {o o' : TmRiO n}
    {g : Perm (Fin n)} (h : SameOrb A (tmRiObj o) (tmRiObj o' ↼ g)) :
    SameOrb A (tmRiObj (c, o.2.1, o.2.2)) (tmRiObj (c, o'.2.1, o'.2.2) ↼ g) := by
  obtain ⟨a, ha, hact⟩ := h
  refine ⟨a, ha, CObj.ext (by simp [tmRiObj, tmGlObj, cobj_act_tag]) ?_⟩
  have hcos := congrArg CObj.coset hact
  simpa [tmRiObj, tmGlObj, cobj_act_coset] using hcos

theorem tmRi_two_eq_iff {a0 a1 b0 b1 : CObj ℕ (Perm (Fin n))}
    (ha0 : a0.tag = 0) (_ha1 : a1.tag = 1) (hb0 : b0.tag = 0) (hb1 : b1.tag = 1) :
    ({a0, a1} : Multiset (CObj ℕ (Perm (Fin n)))) = {b0, b1} ↔ a0 = b0 ∧ a1 = b1 := by
  constructor
  · intro h
    have hm : a0 ∈ ({b0, b1} : Multiset (CObj ℕ (Perm (Fin n)))) := by
      rw [← h, Multiset.insert_eq_cons]; exact Multiset.mem_cons_self a0 {a1}
    rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · refine ⟨rfl, ?_⟩
      rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons] at h
      exact Multiset.singleton_inj.1 ((Multiset.cons_inj_right a0).1 h)
    · exfalso; omega
  · rintro ⟨rfl, rfl⟩; rfl

open Classical in
theorem tmRi_partAt_single_of_sameOrb {A : Subgroup (Perm (Fin n))} {x z : CObj ℕ (Perm (Fin n))}
    (h : SameOrb A x z) : partAt A ({z} : Multiset _) {x} = {z} := by
  rw [partAt, Multiset.filter_eq_self]
  intro y hy
  rw [Multiset.mem_singleton.1 hy]
  exact ⟨x, Multiset.mem_singleton_self x, h⟩

open Classical in
theorem tmRi_partAt_single_of_tag_ne {A : Subgroup (Perm (Fin n))} {x z : CObj ℕ (Perm (Fin n))}
    (h : x.tag ≠ z.tag) : partAt A ({z} : Multiset _) {x} = 0 := by
  rw [partAt, Multiset.filter_eq_nil]
  intro y hy
  rw [Multiset.mem_singleton.1 hy]
  rintro ⟨t, ht, ⟨a, _, ha⟩⟩
  rw [Multiset.mem_singleton.1 ht] at ha
  have htag := congrArg CObj.tag ha
  rw [cobj_act_tag] at htag
  exact h htag

open Classical in
theorem tmRi_conf_two {A : Subgroup (Perm (Fin n))} {a0 a1 b0 b1 : CObj ℕ (Perm (Fin n))}
    (ha0 : a0.tag = 0) (ha1 : a1.tag = 1)
    (h0 : SameOrb A a0 b0) (h1 : SameOrb A a1 b1) :
    Conf A ({a0, a1} : Multiset (CObj ℕ (Perm (Fin n)))) {b0, b1} := by
  have hb0 : b0.tag = 0 := by obtain ⟨a, _, ha⟩ := h0; rw [← ha, cobj_act_tag, ha0]
  have hb1 : b1.tag = 1 := by obtain ⟨a, _, ha⟩ := h1; rw [← ha, cobj_act_tag, ha1]
  have eY : ({a0, a1} : Multiset (CObj ℕ (Perm (Fin n)))) = {a0} + {a1} := by
    rw [Multiset.insert_eq_cons, ← Multiset.singleton_add]
  have eZ : ({b0, b1} : Multiset (CObj ℕ (Perm (Fin n)))) = {b0} + {b1} := by
    rw [Multiset.insert_eq_cons, ← Multiset.singleton_add]
  have pY0 : partAt A ({a0, a1} : Multiset _) {a0} = {a0} := by
    rw [eY, partAt_add, tmRi_partAt_single_of_sameOrb (sameOrb_refl A a0),
      tmRi_partAt_single_of_tag_ne (by omega), add_zero]
  have pY1 : partAt A ({a0, a1} : Multiset _) {a1} = {a1} := by
    rw [eY, partAt_add, tmRi_partAt_single_of_tag_ne (by omega),
      tmRi_partAt_single_of_sameOrb (sameOrb_refl A a1), zero_add]
  have pZ0 : partAt A ({b0, b1} : Multiset _) {a0} = {b0} := by
    rw [eZ, partAt_add, tmRi_partAt_single_of_sameOrb h0,
      tmRi_partAt_single_of_tag_ne (by omega), add_zero]
  have pZ1 : partAt A ({b0, b1} : Multiset _) {a1} = {b1} := by
    rw [eZ, partAt_add, tmRi_partAt_single_of_tag_ne (by omega),
      tmRi_partAt_single_of_sameOrb h1, zero_add]
  apply conf_of_parts
  · intro z hz
    rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨a0, by rw [Multiset.insert_eq_cons]; exact Multiset.mem_cons_self _ _, h0⟩
    · exact ⟨a1, by rw [Multiset.insert_eq_cons]; simp, h1⟩
  · intro T hT
    obtain ⟨y, hy, rfl⟩ := mem_pieces.1 hT
    rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · obtain ⟨c0, hc0, hact0⟩ := h0
      refine ⟨c0, hc0, ?_⟩
      rw [pY0, pZ0, ← hact0]; simp [multiset_act_def]
    · obtain ⟨c1, hc1, hact1⟩ := h1
      refine ⟨c1, hc1, ?_⟩
      rw [pY1, pZ1, ← hact1]; simp [multiset_act_def]

theorem tmRi_sameOrb_sup {H A : Subgroup (Perm (Fin n))} (hAH : A ≤ H)
    (hAn : GI.Multicoset.Normalizes H A) (x : CObj ℕ (Perm (Fin n))) :
    ∀ g ∈ A ⊔ Aut H x, g ∈ H ∧ SameOrb A x (x ↼ g) := by
  let U : Subgroup (Perm (Fin n)) :=
    { carrier := {g | g ∈ H ∧ SameOrb A x (x ↼ g)}
      one_mem' := ⟨H.one_mem, by rw [act_one]; exact sameOrb_refl A x⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨h1, o1⟩ ⟨h2, o2⟩
        refine ⟨H.mul_mem h1 h2, o2.trans ?_⟩
        rw [← act_act]
        exact (sameOrb_act_iff hAn h2).2 o1
      inv_mem' := by
        rintro g ⟨hg, og⟩
        refine ⟨H.inv_mem hg, ?_⟩
        have h := (sameOrb_act_iff hAn (H.inv_mem hg)).2 og.symm
        rwa [act_act_inv] at h }
  have hle : A ⊔ Aut H x ≤ U := sup_le
    (fun a ha => ⟨hAH ha, ⟨a, ha, rfl⟩⟩)
    (fun h hh => ⟨hh.1, by rw [hh.2]; exact sameOrb_refl A x⟩)
  exact fun g hg => hle hg

theorem tmRi_normalizes_reb {H N A : Subgroup (Perm (Fin n))}
    (hAH : A ≤ H) (hAn : GI.Multicoset.Normalizes H A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ N) {x : CObj ℕ (Perm (Fin n))}
    (hNx : ∀ n ∈ N, x ↼ n = x) :
    GI.Multicoset.Normalizes (A ⊔ Aut H x) (A ⊓ Aut H x) := by
  let U : Subgroup (Perm (Fin n)) :=
    { carrier := {g | ∀ k ∈ A ⊓ Aut H x, g * k * g⁻¹ ∈ A ⊓ Aut H x ∧ g⁻¹ * k * g ∈ A ⊓ Aut H x}
      one_mem' := fun k hk => by simp [hk]
      mul_mem' := fun {g₁ g₂} h1 h2 k hk => by
        refine ⟨?_, ?_⟩
        · have := (h1 (g₂ * k * g₂⁻¹) (h2 k hk).1).1
          simpa [mul_assoc] using this
        · have := (h2 (g₁⁻¹ * k * g₁) (h1 k hk).2).2
          simpa [mul_assoc] using this
      inv_mem' := fun {g} hg k hk => by simpa using ⟨(hg k hk).2, (hg k hk).1⟩ }
  have hle : A ⊔ Aut H x ≤ U := by
    refine sup_le (fun a ha k hk => ?_) (fun h hh k hk => ?_)
    · have hconj : ∀ b ∈ A, b * k * b⁻¹ ∈ A ⊓ Aut H x := fun b hb => by
        refine ⟨A.mul_mem (A.mul_mem hb hk.1) (A.inv_mem hb),
          H.mul_mem (H.mul_mem (hAH hb) hk.2.1) (H.inv_mem (hAH hb)), ?_⟩
        have he : b * k * b⁻¹ = k * (k⁻¹ * b * k * b⁻¹) := by group
        rw [he, ← act_act, hk.2.2]
        exact hNx _ (hcomm _ (A.inv_mem hk.1) b hb)
      exact ⟨hconj a ha, by simpa using hconj a⁻¹ (A.inv_mem ha)⟩
    · have hconj : ∀ u ∈ Aut H x, u * k * u⁻¹ ∈ A ⊓ Aut H x := fun u hu =>
        ⟨hAn u hu.1 k hk.1, (Aut H x).mul_mem ((Aut H x).mul_mem hu hk.2) ((Aut H x).inv_mem hu)⟩
      exact ⟨hconj h hh, by simpa using hconj h⁻¹ ((Aut H x).inv_mem hh)⟩
  exact fun g hg k hk => (hle hg k hk).1

theorem tmRi_pc_nil_eq_replicate {σN : List (Perm (Fin n))} {M : ℕ} {Q : List (TmRiO n)}
    (hQ : TmRiPc ([] : List (Perm (Fin n))) σN M Q) {q : TmRiO n} (hq : Q[0]? = some q) :
    tmGlMs Q = Multiset.replicate Q.length (tmRiObj q) := by
  have hqm : tmRiObj q ∈ tmGlMs Q := by
    simp only [tmGlMs, Multiset.mem_coe, List.mem_map]
    exact ⟨q, List.mem_of_getElem? hq, rfl⟩
  refine Multiset.eq_replicate.2 ⟨by simp [tmGlMs], fun s hs => ?_⟩
  exact (tmRi_sameOrb_nil.1 (hQ.2.2.1 s hs (tmRiObj q) hqm))

theorem tmRi_reb_iso_pair {H B : Subgroup (Perm (Fin n))} {ox q q' : TmRiO n}
    {σN : List (Perm (Fin n))} {M : ℕ} {Q Q' : List (TmRiO n)}
    (hBH : B ≤ H) (hoxB : Aut H (tmRiObj ox) ≤ B) (hc : q.1 = q'.1)
    (hQ : TmRiPc ([] : List (Perm (Fin n))) σN M Q) (hq : Q[0]? = some q)
    (hQ' : TmRiPc ([] : List (Perm (Fin n))) σN M Q') (hq' : Q'[0]? = some q')
    (hlen : Q.length = Q'.length) :
    Iso B (tmGlMs [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)])
      (tmGlMs [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)]) =
      Iso (Aut H (tmRiObj ox)) (tmGlMs Q) (tmGlMs Q') := by
  have hQrep := tmRi_pc_nil_eq_replicate hQ hq
  have hQ'rep := tmRi_pc_nil_eq_replicate hQ' hq'
  have hQpos : 0 < Q.length := List.length_pos_of_ne_nil hQ.1
  ext g
  simp only [mem_iso]
  have htwo : tmGlMs [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)] ↼ g =
      tmGlMs [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)] ↔
      tmRiObj ox ↼ g = tmRiObj ox ∧ tmRiObj q ↼ g = tmRiObj q' := by
    change ({tmRiObj (0, ox.2.1, ox.2.2) ↼ g, tmRiObj (1, q.2.1, q.2.2) ↼ g} : Multiset _) =
      {tmRiObj (0, ox.2.1, ox.2.2), tmRiObj (1, q'.2.1, q'.2.2)} ↔ _
    rw [tmRi_two_eq_iff rfl rfl rfl rfl, tmRi_recolor_act_eq rfl, tmRi_recolor_act_eq hc]
  have hrep : tmGlMs Q ↼ g = tmGlMs Q' ↔ tmRiObj q ↼ g = tmRiObj q' := by
    rw [hQrep, hQ'rep, ← hlen]
    constructor
    · intro h
      have hm : tmRiObj q ↼ g ∈ (Multiset.replicate Q.length (tmRiObj q)) ↼ g :=
        act_mem_act g (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)
      rw [h] at hm
      exact (Multiset.mem_replicate.1 hm).2
    · intro h
      rw [multiset_act_def, Multiset.map_replicate, h]
  rw [htwo, hrep]
  exact ⟨fun ⟨hgB, hox, hqq'⟩ => ⟨⟨hBH hgB, hox⟩, hqq'⟩,
    fun ⟨hgx, hqq'⟩ => ⟨hoxB hgx, hgx.2, hqq'⟩⟩

theorem tmRi_eq_of_conf_fixes {K : Subgroup (Perm (Fin n))} {Y Z : Multiset (CObj ℕ (Perm (Fin n)))}
    (hfix : Fixes K Y) (hconf : Conf K Y Z) : Z = Y := by
  obtain ⟨w, hw, rfl⟩ := hconf
  have hsum : ∑ T ∈ pieces K Y, T ↼ w T = ∑ T ∈ pieces K Y, T :=
    Finset.sum_congr rfl fun T hT => (hfix.of_le (piece_le hT)).act_eq (hw T hT)
  rw [hsum, sum_pieces]

open Classical in
theorem tmRi_pieces_eq_of_fixes {K : Subgroup (Perm (Fin n))} {Y : Multiset (CObj ℕ (Perm (Fin n)))}
    (hfix : Fixes K Y) : pieces K Y = pieces (gens ([] : List (Perm (Fin n)))) Y := by
  have hp : ∀ x ∈ Y, partAt K Y {x} = partAt (gens ([] : List (Perm (Fin n)))) Y {x} := by
    intro x hx
    unfold partAt
    apply Multiset.filter_congr
    intro z hz
    simp only [Multiset.mem_singleton, exists_eq_left, tmRi_sameOrb_nil]
    refine ⟨fun ⟨k, hk, hact⟩ => ?_, fun h => ⟨1, K.one_mem, by rw [act_one, h]⟩⟩
    have h1 := congrArg (· ↼ k⁻¹) hact
    rw [act_act_inv] at h1
    exact h1.trans (hfix k⁻¹ (K.inv_mem hk) z hz)
  unfold pieces
  exact Finset.image_congr fun x hx => hp x (Multiset.mem_toFinset.1 hx)

theorem tmRiHat_iso_eq_of_fixes {H A : Subgroup (Perm (Fin n))}
    {P : Finset (Multiset (CObj ℕ (Perm (Fin n))))}
    {col : Multiset (CObj ℕ (Perm (Fin n))) → ℕ}
    {rep : Multiset (CObj ℕ (Perm (Fin n))) → Multiset (CObj ℕ (Perm (Fin n)))}
    (hr : TmRiRep H P col rep) (hAn : GI.Multicoset.Normalizes H A)
    {U V : Multiset (CObj ℕ (Perm (Fin n)))}
    (hU : pieces A U ⊆ P) (hV : pieces A V ⊆ P) (hfixV : Fixes A V) :
    Iso H (tmRiHat H A col rep U) (tmRiHat H A col rep V) = Iso H U V := by
  ext h
  exact ⟨fun hh => ⟨hh.1, tmRi_eq_of_conf_fixes hfixV (tmRiHat_conf hr hAn hU hV hh.1 hh.2)⟩,
    fun hh => tmRiHat_carry hr hAn hU hV hh⟩

/-! ### Placement of the rebasing functions -/

theorem tmRiReb_mods {P : Program} {b gObj : ℕ} (h : P.HasAt (b + 96) (tmRiRebFuns b gObj)) :
    P.funs[b + 96]? = some (tmRiRebMainE b) ∧
    P.funs[b + 97]? = some (tmRiRebRowE b) ∧
    P.funs[b + 98]? = some (tmRiRebPairE gObj) ∧
    P.HasAt (b + 99) (mapFuns (b + 99) (b + 97)) ∧
    P.HasAt (b + 102) (mapFuns (b + 102) (b + 98)) := by
  have h' : P.HasAt (b + 96) ([tmRiRebMainE b, tmRiRebRowE b, tmRiRebPairE gObj] ++
      (mapFuns (b + 99) (b + 97) ++ mapFuns (b + 102) (b + 98))) := by
    simpa [List.append_assoc] using (show P.HasAt (b + 96)
      (([tmRiRebMainE b, tmRiRebRowE b, tmRiRebPairE gObj] ++
        mapFuns (b + 99) (b + 97) ++ mapFuns (b + 102) (b + 98)) ++ [tmRiNormStepE b]) from h).left
  have h0 := tmRi_hasAt_right h' (b' := b + 99) rfl
  have h1 := tmRi_hasAt_right h0 (b' := b + 102) rfl
  refine ⟨?_, ?_, ?_, h0.left, h1⟩
  · simpa using h'.left 0 (by simp)
  · have := h'.left 1 (by simp)
    rwa [show b + 96 + 1 = b + 97 by omega] at this
  · have := h'.left 2 (by simp)
    rwa [show b + 96 + 2 = b + 98 by omega] at this

theorem tmRiReb_normStep {P : Program} {b gObj : ℕ} (h : P.HasAt (b + 96) (tmRiRebFuns b gObj)) :
    P.funs[b + 105]? = some (tmRiNormStepE b) := by
  have h1 : P.HasAt (b + 105) [tmRiNormStepE b] := tmRi_hasAt_right h (b' := b + 105) rfl
  simpa using h1 0 (by simp)

/-! ### Specification of `tmRiRebPairE` (`b + 98`) and `tmRiRebRowE` (`b + 99`) -/

theorem tmRi_rebPair_glue {P : Program} {gObj Kg Dg M ℓ : ℕ}
    (hglue : Iface.TermGlueObjSpec P Kg Dg gObj)
    {σH σN σA σB hs hk : List (Perm (Fin n))} {ox q q' : TmRiO n} {Ql Q'l : List (TmRiO n)}
    (hIn : TmRiListIn (gens σB) (Ql ++ Q'l)) (hoxIn : tmRiStab ox ≤ gens σB)
    (hBH : gens σB ≤ gens σH) (hAB : gens σA ≤ gens σB)
    (hB : gens σB = gens σA ⊔ gens hs)
    (hsx : gens hs = Aut (gens σH) (tmRiObj ox))
    (hkx : gens hk = gens σA ⊓ Aut (gens σH) (tmRiObj ox))
    (hNH : gens σN ≤ gens σH) (hNA : gens σN ≤ gens σA)
    (hNn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hAn : GI.Multicoset.Normalizes (gens σH) (gens σA))
    (hfuel : relDerived (gens σH) (gens σN) (ℓ + 1) ≤ gens σN)
    (hcomm : ∀ a ∈ gens σA, ∀ b ∈ gens σA, a * b * a⁻¹ * b⁻¹ ∈ gens σN)
    (hNox : ∀ g ∈ gens σN, tmRiObj ox ↼ g = tmRiObj ox)
    (hQ : TmRiPc ([] : List (Perm (Fin n))) hk M Ql) (hq : Ql[0]? = some q)
    (hQ' : TmRiPc ([] : List (Perm (Fin n))) hk M Q'l) (hq' : Q'l[0]? = some q')
    (hoxq : SameOrb (gens σA) (tmRiObj ox) (tmRiObj q))
    (hoxq' : SameOrb (gens σA) (tmRiObj ox) (tmRiObj q'))
    (hc : q.1 = q'.1) (hlen : Ql.length = Q'l.length) :
    FunAll P gObj (tmGlIn σB hk σA [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)]
        [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)] σB 1)
      (fun u cost => CosetC n u (Iso (gens hs) (tmGlMs Ql) (tmGlMs Q'l)) ∧
        cost ≤ Kg * ((tmGlIn σB hk σA [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)]
          [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)] σB 1).wt + 1) ^ Dg) := by
  have hqm : q ∈ Ql := List.mem_of_getElem? hq
  have hq'm : q' ∈ Q'l := List.mem_of_getElem? hq'
  set X₀ : List (TmRiO n) := [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)] with hX₀
  set Y₀ : List (TmRiO n) := [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)] with hY₀
  have hNk : gens σN ≤ gens hk := by
    rw [hkx]
    exact le_inf hNA (fun g hg => ⟨hNH hg, hNox g hg⟩)
  have hsolB : ∀ [((gens hk).subgroupOf (gens σB)).Normal],
      IsSolvable ((gens σB) ⧸ (gens hk).subgroupOf (gens σB)) := by
    intro _
    haveI := normal_subgroupOf_of_normalizes hNn
    exact isSolvable_quot_of_le (isSolvable_quot_of_relDerived hfuel) hBH hNk
  have hIn₀ : ∀ o ∈ X₀ ++ Y₀, gens (o.2.1.map fun x => o.2.2⁻¹ * x * o.2.2⁻¹⁻¹) ≤ gens σB := by
    intro o ho
    simp only [hX₀, hY₀, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with (rfl | rfl) | (rfl | rfl)
    · exact hoxIn
    · exact hIn q (List.mem_append_left _ hqm)
    · exact hoxIn
    · exact hIn q' (List.mem_append_right _ hq'm)
  have hkA : gens hk ≤ gens σA := by rw [hkx]; exact inf_le_left
  have hBn_k : GI.Multicoset.Normalizes (gens σB) (gens hk) := by
    rw [hB, hsx, hkx]
    exact tmRi_normalizes_reb (hAB.trans hBH) hAn hcomm hNox
  have hBn_A : GI.Multicoset.Normalizes (gens σB) (gens σA) := fun g hg a ha => hAn g (hBH hg) a ha
  have hcomm_k : ∀ a ∈ gens σA, ∀ b ∈ gens σA, a * b * a⁻¹ * b⁻¹ ∈ gens hk :=
    fun a ha b hb => hNk (hcomm a ha b hb)
  have hfixX₀ : Fixes (gens hk) (tmGlMs X₀) := by
    intro g hg z hz
    simp only [hX₀, tmGlMs, List.map, Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · have hg' : g ∈ Aut (gens σH) (tmRiObj ox) := by rw [hkx] at hg; exact hg.2
      exact (tmRi_recolor_act_eq rfl).2 hg'.2
    · have hqg : tmRiObj q ↼ g = tmRiObj q :=
        hQ.2.2.2 g hg (tmRiObj q) (by simp only [tmGlMs, Multiset.mem_coe, List.mem_map]; exact ⟨q, hqm, rfl⟩)
      exact (tmRi_recolor_act_eq rfl).2 hqg
  have hfixY₀ : Fixes (gens hk) (tmGlMs Y₀) := by
    intro g hg z hz
    simp only [hY₀, tmGlMs, List.map, Multiset.mem_coe, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · have hg' : g ∈ Aut (gens σH) (tmRiObj ox) := by rw [hkx] at hg; exact hg.2
      exact (tmRi_recolor_act_eq rfl).2 hg'.2
    · have hq'g : tmRiObj q' ↼ g = tmRiObj q' :=
        hQ'.2.2.2 g hg (tmRiObj q') (by simp only [tmGlMs, Multiset.mem_coe, List.mem_map]; exact ⟨q', hq'm, rfl⟩)
      exact (tmRi_recolor_act_eq rfl).2 hq'g
  have horbB : ∀ g ∈ gens σB,
      SameOrb (gens σA) (tmRiObj (0, ox.2.1, ox.2.2)) (tmRiObj (0, ox.2.1, ox.2.2) ↼ g) ∧
      SameOrb (gens σA) (tmRiObj (1, q.2.1, q.2.2)) (tmRiObj (1, q.2.1, q.2.2) ↼ g) ∧
      SameOrb (gens σA) (tmRiObj (1, q'.2.1, q'.2.2)) (tmRiObj (1, q.2.1, q.2.2) ↼ g) ∧
      SameOrb (gens σA) (tmRiObj (1, q'.2.1, q'.2.2)) (tmRiObj (1, q'.2.1, q'.2.2) ↼ g) := by
    intro g hg
    have hoxg : SameOrb (gens σA) (tmRiObj ox) (tmRiObj ox ↼ g) := by
      have hg' : g ∈ gens σA ⊔ Aut (gens σH) (tmRiObj ox) := by rwa [← hsx, ← hB]
      exact (tmRi_sameOrb_sup (hAB.trans hBH) hAn (tmRiObj ox) g hg').2
    have hqg : SameOrb (gens σA) (tmRiObj ox ↼ g) (tmRiObj q ↼ g) :=
      (sameOrb_act_iff hAn (hBH hg)).2 hoxq
    have hq'g : SameOrb (gens σA) (tmRiObj ox ↼ g) (tmRiObj q' ↼ g) :=
      (sameOrb_act_iff hAn (hBH hg)).2 hoxq'
    refine ⟨tmRi_recolor_sameOrb_act 0 hoxg,
      tmRi_recolor_sameOrb_act 1 (hoxq.symm.trans (hoxg.trans hqg)),
      tmRi_recolor_sameOrb_act 1 (hoxq'.symm.trans (hoxg.trans hqg)),
      tmRi_recolor_sameOrb_act 1 (hoxq'.symm.trans (hoxg.trans hq'g))⟩
  have hP1 : ∀ g ∈ gens σB, Conf (gens σA) (tmGlMs X₀) (tmGlMs X₀ ↼ g) := by
    intro g hg; obtain ⟨o1, o2, -, -⟩ := horbB g hg; exact tmRi_conf_two rfl rfl o1 o2
  have hP2 : ∀ g ∈ gens σB, Conf (gens σA) (tmGlMs Y₀) (tmGlMs X₀ ↼ (g * 1)) := by
    intro g hg; rw [mul_one]; obtain ⟨o1, -, o3, -⟩ := horbB g hg; exact tmRi_conf_two rfl rfl o1 o3
  have hP3 : ∀ g ∈ gens σB, Conf (gens σA) (tmGlMs Y₀) (tmGlMs Y₀ ↼ ((1 : Perm (Fin n))⁻¹ * g * 1)) := by
    intro g hg; rw [inv_one, one_mul, mul_one]; obtain ⟨o1, -, -, o4⟩ := horbB g hg
    exact tmRi_conf_two rfl rfl o1 o4
  have hP4 : ∀ h ∈ Iso (gens σB) (tmGlMs X₀) (tmGlMs Y₀), h * (1 : Perm (Fin n))⁻¹ ∈ gens σB :=
    fun _ hh => by simpa using hh.1
  have hP5 : Aut (gens σB) (tmGlMs X₀) ≤ gens σB := fun _ hh => hh.1
  have hoxB : Aut (gens σH) (tmRiObj ox) ≤ gens σB := by rw [hB, hsx]; exact le_sup_right
  have hiso_eq : Iso (gens σB) (tmGlMs X₀) (tmGlMs Y₀) = Iso (gens hs) (tmGlMs Ql) (tmGlMs Q'l) := by
    rw [hsx]; exact tmRi_reb_iso_pair hBH hoxB hc hQ hq hQ' hq' hlen
  refine (hglue σB hk σA X₀ Y₀ σB 1 hsolB hIn₀ hkA hAB hBn_k hBn_A hcomm_k hfixX₀ hfixY₀
    hAB le_rfl (gens σB).one_mem hP1 hP2 hP3 hP4 hP5).mono fun u cu h => ?_
  rw [tmRi_ansC_iff, hiso_eq] at h
  exact h

private theorem wt_get_lt {vs : List Val} {v : Val} {i W : ℕ}
    (hi : vs[i]? = some v) (hw : (Val.list vs).wt ≤ W) : v.wt < W :=
  Nat.lt_of_lt_of_le (wt_le_wt_list (List.mem_of_getElem? hi)) hw

private theorem det_get_lt {P : Program} {env : List Val} {e : Expr} {vs : List Val} {v : Val}
    {i c W : ℕ} (h : Det P env e (.list vs) c) (hi : vs[i]? = some v)
    (hw : (Val.list vs).wt ≤ W) (hi_le : i ≤ 10) :
    Det P env (.get e (.nat i)) v (c + 2 * W + 20) := by
  have h1 := wt_nat_le i
  have h2 := length_lt_wt_list vs
  have h3 := wt_get_lt hi hw
  exact (Det.get' h (Det.nat i) hi).mono (by omega)

private theorem det_mk2_le {P : Program} {env : List Val} {e1 e2 : Expr} {v1 v2 : Val}
    {c1 c2 W1 W2 : ℕ} (h1 : Det P env e1 v1 c1) (h2 : Det P env e2 v2 c2)
    (hw1 : v1.wt ≤ W1) (hw2 : v2.wt ≤ W2) :
    Det P env (mk2 e1 e2) (.list [v1, v2]) (c1 + c2 + 4 * W1 + 4 * W2 + 20) ∧
      (Val.list [v1, v2]).wt ≤ 2 * W1 + 2 * W2 + 6 := by
  have := wt_list2_le v1 v2
  exact ⟨(Det.mk2 h1 h2).mono (by omega), by omega⟩

private theorem det_mk3_le {P : Program} {env : List Val} {e1 e2 e3 : Expr} {v1 v2 v3 : Val}
    {c1 c2 c3 W1 W2 W3 : ℕ} (h1 : Det P env e1 v1 c1) (h2 : Det P env e2 v2 c2)
    (h3 : Det P env e3 v3 c3) (hw1 : v1.wt ≤ W1) (hw2 : v2.wt ≤ W2) (hw3 : v3.wt ≤ W3) :
    Det P env (mk3 e1 e2 e3) (.list [v1, v2, v3]) (c1 + c2 + c3 + 6 * W1 + 6 * W2 + 6 * W3 + 30) ∧
      (Val.list [v1, v2, v3]).wt ≤ 2 * W1 + 2 * W2 + 2 * W3 + 8 := by
  have := wt_list3_le v1 v2 v3
  exact ⟨(Det.mk3 h1 h2 h3).mono (by omega), by omega⟩

private theorem det_mkList7_le {P : Program} {env : List Val}
    {e1 e2 e3 e4 e5 e6 e7 : Expr} {v1 v2 v3 v4 v5 v6 v7 : Val} {c W : ℕ}
    (h1 : Det P env e1 v1 c) (h2 : Det P env e2 v2 c) (h3 : Det P env e3 v3 c)
    (h4 : Det P env e4 v4 c) (h5 : Det P env e5 v5 c) (h6 : Det P env e6 v6 c)
    (h7 : Det P env e7 v7 c)
    (hw : v1.wt + v2.wt + v3.wt + v4.wt + v5.wt + v6.wt + v7.wt ≤ W) :
    Det P env (Expr.mkList [e1, e2, e3, e4, e5, e6, e7])
      (.list [v1, v2, v3, v4, v5, v6, v7]) (7 * c + 20 * W + 200) ∧
    (Val.list [v1, v2, v3, v4, v5, v6, v7]).wt ≤ 2 * W + 16 := by
  have hwl : (Val.list [v1, v2, v3, v4, v5, v6, v7]).wt ≤ 2 * W + 16 := by
    have := wt_list_le [v1, v2, v3, v4, v5, v6, v7]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  refine ⟨(Det.mkList (P := P) (env := env) (c := c)
    [(e1, v1), (e2, v2), (e3, v3), (e4, v4), (e5, v5), (e6, v6), (e7, v7)] (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7)).mono (by
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      omega), hwl⟩

theorem tmRi_rebPair_dml {P : Program} {W : ℕ}
    {σB hk σA : List (Perm (Fin n))} {ox q q' : TmRiO n} {Ql Q'l : List (TmRiO n)} {c0 : Val}
    (hc0 : c0 = .list [encGroup σB, encGroup hk, encGroup σA,
      tmGlObjVal (0, ox.2.1, ox.2.2), encPerm (1 : Perm (Fin n))])
    (hq : Ql[0]? = some q) (hq' : Q'l[0]? = some q')
    (hW : (Val.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l]).wt ≤ W) :
    Det P [.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l]] (Expr.mkList [
        .get (.get (arg 0) (.nat 0)) (.nat 0),
        .get (.get (arg 0) (.nat 0)) (.nat 1),
        .get (.get (arg 0) (.nat 0)) (.nat 2),
        mk2 (.get (.get (arg 0) (.nat 0)) (.nat 3))
          (mk3 (.nat 1) (.get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 1))
            (.get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 2))),
        mk2 (.get (.get (arg 0) (.nat 0)) (.nat 3))
          (mk3 (.nat 1) (.get (.get (arg 1) (.nat 0)) (.nat 1))
            (.get (.get (arg 1) (.nat 0)) (.nat 2))),
        .get (.get (arg 0) (.nat 0)) (.nat 0),
        .get (.get (arg 0) (.nat 0)) (.nat 4)])
      (tmGlIn σB hk σA [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)]
        [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)] σB 1) (2000 * W + 15000) ∧
    (tmGlIn σB hk σA [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)]
      [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)] σB 1).wt ≤ 50 * W + 200 := by
  have hc0Q_w : (Val.list [c0, tmGlObjsVal Ql]).wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (i := 0) rfl hW)
  have hQ'w : (tmGlObjsVal Q'l).wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (i := 1) rfl hW)
  have hc0w : c0.wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 0) rfl hc0Q_w)
  have hQw : (tmGlObjsVal Ql).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 1) rfl hc0Q_w)
  have hqw : (tmGlObjVal q).wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (v := tmGlObjVal q) (i := 0) (by simp [hq]) hQw)
  have hq'w : (tmGlObjVal q').wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (v := tmGlObjVal q') (i := 0) (by simp [hq']) hQ'w)
  have hc0w' : (Val.list [encGroup σB, encGroup hk, encGroup σA,
      tmGlObjVal (0, ox.2.1, ox.2.2), encPerm (1 : Perm (Fin n))]).wt ≤ W := hc0 ▸ hc0w
  have hBw : (encGroup σB).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 0) rfl hc0w')
  have hkw : (encGroup hk).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 1) rfl hc0w')
  have hAw : (encGroup σA).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 2) rfl hc0w')
  have hox0w : (tmGlObjVal (0, ox.2.1, ox.2.2)).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 3) rfl hc0w')
  have h1pw : (encPerm (1 : Perm (Fin n))).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 4) rfl hc0w')
  have hq1w : (encGroup q.2.1).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 1) rfl hqw)
  have hq2w : (encPerm q.2.2).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 2) rfl hqw)
  have hq'1w : (encGroup q'.2.1).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 1) rfl hq'w)
  have hq'2w : (encPerm q'.2.2).wt ≤ W := Nat.le_of_lt (wt_get_lt (i := 2) rfl hq'w)
  have droot := (Det.var' (P := P) (env := [.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l]])
    (i := 0) rfl).mono (c' := W + 2) (by omega)
  have da0 := det_get_lt droot (i := 0) rfl hW (by decide)
  have da1 := det_get_lt droot (i := 1) rfl hW (by decide)
  have dc0 := det_get_lt da0 (i := 0) rfl hc0Q_w (by decide)
  have dQl := det_get_lt da0 (i := 1) rfl hc0Q_w (by decide)
  have dq := det_get_lt dQl (v := tmGlObjVal q) (i := 0) (by simp [hq]) hQw (by decide)
  have dq' := det_get_lt da1 (v := tmGlObjVal q') (i := 0) (by simp [hq']) hQ'w (by decide)
  have dc0' : Det P [.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l]] (.get (arg 0) (.nat 0))
      (.list [encGroup σB, encGroup hk, encGroup σA, tmGlObjVal (0, ox.2.1, ox.2.2), encPerm (1 : Perm (Fin n))])
      (W + 2 + 2 * W + 20 + 2 * W + 20) := hc0 ▸ dc0
  have dc0_0 := (det_get_lt dc0' (i := 0) rfl hc0w' (by decide)).mono (c' := 100 * W + 1000) (by omega)
  have dc0_1 := (det_get_lt dc0' (i := 1) rfl hc0w' (by decide)).mono (c' := 100 * W + 1000) (by omega)
  have dc0_2 := (det_get_lt dc0' (i := 2) rfl hc0w' (by decide)).mono (c' := 100 * W + 1000) (by omega)
  have dc0_3 := det_get_lt dc0' (i := 3) rfl hc0w' (by decide)
  have dc0_4 := (det_get_lt dc0' (i := 4) rfl hc0w' (by decide)).mono (c' := 100 * W + 1000) (by omega)
  have dq1 := det_get_lt dq (i := 1) rfl hqw (by decide)
  have dq2 := det_get_lt dq (i := 2) rfl hqw (by decide)
  have dq'1 := det_get_lt dq' (i := 1) rfl hq'w (by decide)
  have dq'2 := det_get_lt dq' (i := 2) rfl hq'w (by decide)
  obtain ⟨dqr, hqr_w⟩ := det_mk3_le (Det.nat 1) dq1 dq2 (wt_nat_le 1) hq1w hq2w
  obtain ⟨dq'r, hq'r_w⟩ := det_mk3_le (Det.nat 1) dq'1 dq'2 (wt_nat_le 1) hq'1w hq'2w
  obtain ⟨dX₀, hX₀w⟩ := det_mk2_le dc0_3 dqr hox0w hqr_w
  obtain ⟨dY₀, hY₀w⟩ := det_mk2_le dc0_3 dq'r hox0w hq'r_w
  obtain ⟨dml, hGw⟩ := det_mkList7_le (W := 25 * W + 80)
    dc0_0 dc0_1 dc0_2 (dX₀.mono (by omega)) (dY₀.mono (by omega)) dc0_0 dc0_4 (by omega)
  have eG : tmGlIn σB hk σA [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)]
      [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)] σB 1 =
      .list [encGroup σB, encGroup hk, encGroup σA,
        .list [tmGlObjVal (0, ox.2.1, ox.2.2), .list [.nat 1, encGroup q.2.1, encPerm q.2.2]],
        .list [tmGlObjVal (0, ox.2.1, ox.2.2), .list [.nat 1, encGroup q'.2.1, encPerm q'.2.2]],
        encGroup σB, encPerm (1 : Perm (Fin n))] := rfl
  exact ⟨eG ▸ dml.mono (by omega), eG ▸ hGw.trans (by omega)⟩

theorem tmRi_rebPair_spec {P : Program} {b gObj Kg Dg M ℓ W : ℕ}
    (hReb : P.HasAt (b + 96) (tmRiRebFuns b gObj))
    (hglue : Iface.TermGlueObjSpec P Kg Dg gObj)
    {σH σN σA σB hs hk : List (Perm (Fin n))} {ox : TmRiO n} {Ql Q'l : List (TmRiO n)} {c0 : Val}
    (hc0 : c0 = .list [encGroup σB, encGroup hk, encGroup σA,
      tmGlObjVal (0, ox.2.1, ox.2.2), encPerm (1 : Perm (Fin n))])
    (hIn : TmRiListIn (gens σB) (Ql ++ Q'l)) (hoxIn : tmRiStab ox ≤ gens σB)
    (hBH : gens σB ≤ gens σH) (hAB : gens σA ≤ gens σB)
    (hB : gens σB = gens σA ⊔ gens hs)
    (hsx : gens hs = Aut (gens σH) (tmRiObj ox))
    (hkx : gens hk = gens σA ⊓ Aut (gens σH) (tmRiObj ox))
    (hNH : gens σN ≤ gens σH) (hNA : gens σN ≤ gens σA)
    (hNn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hAn : GI.Multicoset.Normalizes (gens σH) (gens σA))
    (hfuel : relDerived (gens σH) (gens σN) (ℓ + 1) ≤ gens σN)
    (hcomm : ∀ a ∈ gens σA, ∀ b ∈ gens σA, a * b * a⁻¹ * b⁻¹ ∈ gens σN)
    (hNox : ∀ g ∈ gens σN, tmRiObj ox ↼ g = tmRiObj ox)
    (hQ : TmRiPc ([] : List (Perm (Fin n))) hk M Ql)
    (hQ' : TmRiPc ([] : List (Perm (Fin n))) hk M Q'l)
    (hQo : ∀ o ∈ Ql, SameOrb (gens σA) (tmRiObj ox) (tmRiObj o))
    (hQ'o : ∀ o ∈ Q'l, SameOrb (gens σA) (tmRiObj ox) (tmRiObj o))
    (hW : (Val.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l]).wt ≤ W)
    (hWV : 50 * W + 200 ≤ tmRiVs n M) :
    FunAll P (b + 98) (.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l])
      (fun w cost => CosetC n w (Iso (gens hs) (tmGlMs Ql) (tmGlMs Q'l)) ∧
        w.wt ≤ 700 * (n + 1) ^ 6 ∧
        cost ≤ Kg * (tmRiVs n M + 1) ^ Dg + 5 * 10 ^ 4 * (tmRiVs n M + 1)) := by
  obtain ⟨fB1, fB2, -, -, fB5⟩ := tmRiB_facts n M
  obtain ⟨fV1, fV2, fV3, fV4⟩ := tmRiVs_facts n M
  have hF1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  set Wo := 700 * (n + 1) ^ 6 with hWo
  have hWoV : Wo ≤ tmRiVs n M := by omega
  set Bud := Kg * (tmRiVs n M + 1) ^ Dg + 5 * 10 ^ 4 * (tmRiVs n M + 1) with hBud
  set R : Val → Prop := fun w => CosetC n w (Iso (gens hs) (tmGlMs Ql) (tmGlMs Q'l)) with hR
  have hc0Q_w : (Val.list [c0, tmGlObjsVal Ql]).wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (i := 0) rfl hW)
  have hQ'w : (tmGlObjsVal Q'l).wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (i := 1) rfl hW)
  have hQw : (tmGlObjsVal Ql).wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (i := 1) rfl hc0Q_w)
  obtain ⟨q, hq⟩ : ∃ q, Ql[0]? = some q := by
    cases Ql with
    | nil => exact absurd rfl hQ.1
    | cons o _ => exact ⟨o, rfl⟩
  obtain ⟨q', hq'⟩ : ∃ q', Q'l[0]? = some q' := by
    cases Q'l with
    | nil => exact absurd rfl hQ'.1
    | cons o _ => exact ⟨o, rfl⟩
  have hqm : q ∈ Ql := List.mem_of_getElem? hq
  have hq'm : q' ∈ Q'l := List.mem_of_getElem? hq'
  have hoxq : SameOrb (gens σA) (tmRiObj ox) (tmRiObj q) := hQo q hqm
  have hoxq' : SameOrb (gens σA) (tmRiObj ox) (tmRiObj q') := hQ'o q' hq'm
  have hc : q.1 = q'.1 := (tmRi_color_of_sameOrb hoxq).symm.trans (tmRi_color_of_sameOrb hoxq')
  obtain ⟨dml, hGw⟩ := tmRi_rebPair_dml (P := P) hc0 hq hq' hW
  have hgl := tmRi_rebPair_glue hglue hIn hoxIn hBH hAB hB hsx hkx hNH hNA hNn hAn hfuel
    hcomm hNox hQ hq hQ' hq' hoxq hoxq' hc
  have droot := (Det.var' (P := P) (env := [.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l]])
    (i := 0) rfl).mono (c' := W + 2) (by omega)
  have da0 := det_get_lt droot (i := 0) rfl hW (by decide)
  have da1 := det_get_lt droot (i := 1) rfl hW (by decide)
  have dQl := det_get_lt da0 (i := 1) rfl hc0Q_w (by decide)
  have dlen1 := Det.length dQl
  have dlen2 := Det.length da1
  rw [List.length_map] at dlen1 dlen2
  have deq1 := (Det.arith' (op := .eq) dlen1 dlen2 rfl).mono (c' := 25 * W + 200) (by
    have := wt_nat_le Ql.length
    have := wt_nat_le Q'l.length
    have : Ql.length < (tmGlObjsVal Ql).wt := by
      have := length_lt_wt_list (Ql.map tmGlObjVal); rwa [List.length_map] at this
    have : Q'l.length < (tmGlObjsVal Q'l).wt := by
      have := length_lt_wt_list (Q'l.map tmGlObjVal); rwa [List.length_map] at this
    have : BinOp.eval .eq Ql.length Q'l.length ≤ 1 := by simp only [BinOp.eval]; split <;> omega
    have := wt_nat_le (BinOp.eval .eq Ql.length Q'l.length)
    omega)
  have hqw : (tmGlObjVal q).wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (v := tmGlObjVal q) (i := 0) (by simp [hq]) hQw)
  have hq'w : (tmGlObjVal q').wt ≤ W :=
    Nat.le_of_lt (wt_get_lt (v := tmGlObjVal q') (i := 0) (by simp [hq']) hQ'w)
  have dq := det_get_lt dQl (v := tmGlObjVal q) (i := 0) (by simp [hq]) hQw (by decide)
  have dq' := det_get_lt da1 (v := tmGlObjVal q') (i := 0) (by simp [hq']) hQ'w (by decide)
  have dq0 := det_get_lt dq (i := 0) rfl hqw (by decide)
  have dq'0 := det_get_lt dq' (i := 0) rfl hq'w (by decide)
  have heq2_val : BinOp.eval .eq q.1 q'.1 = 1 := by simp [BinOp.eval, hc]
  have deq2 := (Det.arith' (op := .eq) dq0 dq'0 rfl).mono (c' := 25 * W + 200) (by
    have : (Val.nat (BinOp.eval .eq q.1 q'.1)).wt = 3 := by rw [heq2_val]; rfl
    omega)
  refine FunAll.intro (tmRiReb_mods hReb).2.2.1 (EvalAll.mono (Q := fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) ?_
    fun w c h => ⟨h.1, h.2.1, h.2.2⟩)
  refine tmRi_iteB deq1 (by omega) (fun hne1 => ?_) (fun he1 => ?_)
  · have hlen : Ql.length = Q'l.length := by
      by_contra h; simp [BinOp.eval, h] at hne1
    refine tmRi_iteB deq2 (by omega) (fun _ => ?_)
      (fun he2 => absurd he2 (by rw [heq2_val]; decide))
    refine EvalAll.call_funAll (f := gObj) dml
      (Q := fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud - (25 * W + 200) - Wo - 1 - (25 * W + 200) - Wo - 1)
      fun u ca hu => ?_
    obtain ⟨hu, hca⟩ := hu
    subst hu
    refine (hgl hlen).mono fun w cw h => ?_
    have hww : w.wt ≤ Wo := tmRi_wt_ansC h.1
    have hpow : Kg * ((tmGlIn σB hk σA [(0, ox.2.1, ox.2.2), (1, q.2.1, q.2.2)]
        [(0, ox.2.1, ox.2.2), (1, q'.2.1, q'.2.2)] σB 1).wt + 1) ^ Dg ≤ Kg * (tmRiVs n M + 1) ^ Dg :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    refine ⟨h.1, hww, ?_⟩
    generalize Kg * (tmRiVs n M + 1) ^ Dg = K0 at *
    omega
  · have hlen : Ql.length ≠ Q'l.length := by
      intro h; simp [BinOp.eval, h] at he1
    have hnilw : (Val.list []).wt ≤ 5 := by decide
    refine tmRi_detB (Det.nil (P := P) (env := [.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l]]))
      (Or.inl ⟨rfl, ?_⟩) ?_ ?_
    · ext g
      simp only [mem_iso, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hact⟩
      have hcard := congrArg Multiset.card hact
      simp only [tmGlMs, card_act, Multiset.coe_card, List.length_map] at hcard
      exact hlen hcard
    · omega
    · omega

/-- The cost of the rebasing table for `m` pieces. -/
noncomputable def tmRiRebTabC (Kg Dg n M m W : ℕ) : ℕ :=
  m * (m * (Kg * (tmRiVs n M + 1) ^ Dg + 5 * 10 ^ 4 * (tmRiVs n M + 1)) +
    mapK * (m + 1) * (10 * W + 20 + m * (1400 * (n + 1) ^ 6 + 1) + 5) + 150 * W + 300 +
      m * (1400 * (n + 1) ^ 6 + 1)) +
    mapK * (m + 1) * (W + m * (2 * (m * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) + 5)

theorem tmRiRebTabC_mono (Kg Dg n M : ℕ) {m m' : ℕ} (h : m ≤ m') (W : ℕ) :
    tmRiRebTabC Kg Dg n M m W ≤ tmRiRebTabC Kg Dg n M m' W := by
  unfold tmRiRebTabC
  gcongr

/-- **The rebasing table (`b + 99`).** -/
theorem tmRi_rebTab_spec {P : Program} {b gObj Kg Dg M ℓ W : ℕ}
    (hReb : P.HasAt (b + 96) (tmRiRebFuns b gObj))
    (hglue : Iface.TermGlueObjSpec P Kg Dg gObj)
    {σH σN σA σB hs hk : List (Perm (Fin n))} {ox : TmRiO n}
    {Qs : List (List (TmRiO n))} {Z : List (TmRiO n)} {c0 : Val}
    (hc0 : c0 = .list [encGroup σB, encGroup hk, encGroup σA,
      tmGlObjVal (0, ox.2.1, ox.2.2), encPerm (1 : Perm (Fin n))])
    (hIn : TmRiListIn (gens σB) Z) (hoxIn : tmRiStab ox ≤ gens σB)
    (hBH : gens σB ≤ gens σH) (hAB : gens σA ≤ gens σB)
    (hB : gens σB = gens σA ⊔ gens hs)
    (hsx : gens hs = Aut (gens σH) (tmRiObj ox))
    (hkx : gens hk = gens σA ⊓ Aut (gens σH) (tmRiObj ox))
    (hNH : gens σN ≤ gens σH) (hNA : gens σN ≤ gens σA)
    (hNn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hAn : GI.Multicoset.Normalizes (gens σH) (gens σA))
    (hfuel : relDerived (gens σH) (gens σN) (ℓ + 1) ≤ gens σN)
    (hcomm : ∀ a ∈ gens σA, ∀ b ∈ gens σA, a * b * a⁻¹ * b⁻¹ ∈ gens σN)
    (hNox : ∀ g ∈ gens σN, tmRiObj ox ↼ g = tmRiObj ox)
    (hQs : ∀ Q ∈ Qs, TmRiPc ([] : List (Perm (Fin n))) hk M Q)
    (hZo : ∀ o ∈ Z, SameOrb (gens σA) (tmRiObj ox) (tmRiObj o))
    (hZ : ∀ Q ∈ Qs, ∀ o ∈ Q, o ∈ Z)
    (hW : (Val.list [.list [c0, .list (Qs.map tmGlObjsVal)],
      .list (Qs.map tmGlObjsVal)]).wt ≤ W)
    (hWV : 50 * (10 * W + 20) + 200 ≤ tmRiVs n M) :
    FunAll P (b + 99) (.list [.list [c0, .list (Qs.map tmGlObjsVal)],
        .list (Qs.map tmGlObjsVal)])
      (fun w cost => ∃ tab, w = .list tab ∧ TmRiTab (gens hs) Qs tab ∧
        w.wt ≤ Qs.length * (2 * (Qs.length * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) + 4 ∧
        cost ≤ tmRiRebTabC Kg Dg n M Qs.length W) := by
  set PV : Val := .list (Qs.map tmGlObjsVal) with hPV
  set c : Val := .list [c0, PV] with hc
  set m := Qs.length with hm
  set Cp := Kg * (tmRiVs n M + 1) ^ Dg + 5 * 10 ^ 4 * (tmRiVs n M + 1) with hCp
  have hcw : c.wt < W := Nat.lt_of_lt_of_le (wt_le_wt_list List.mem_cons_self) hW
  have hPw : PV.wt < W :=
    Nat.lt_of_lt_of_le (wt_le_wt_list (List.mem_cons_of_mem _ List.mem_cons_self)) hW
  have hc0w : c0.wt < W := Nat.lt_trans (wt_le_wt_list List.mem_cons_self) hcw
  have hSw : ∀ Q ∈ Qs, (tmGlObjsVal Q).wt < PV.wt := fun Q hQ =>
    wt_le_wt_list (List.mem_map_of_mem hQ)
  have hlenPV : (Qs.map tmGlObjsVal).length = m := by rw [List.length_map]
  have hrow : ∀ SV ∈ Qs.map tmGlObjsVal, FunAll P (b + 97) (.list [c, SV]) (fun w cost =>
      (∃ Q ∈ Qs, SV = tmGlObjsVal Q ∧ ∃ us, w = .list us ∧ List.Forall₂ (fun TV u =>
        ∃ Q' ∈ Qs, TV = tmGlObjsVal Q' ∧ CosetC n u (Iso (gens hs) (tmGlMs Q) (tmGlMs Q')))
        (Qs.map tmGlObjsVal) us) ∧ w.wt ≤ m * (1400 * (n + 1) ^ 6 + 1) + 4 ∧
      cost ≤ m * Cp + mapK * (m + 1) * (10 * W + 20 + m * (1400 * (n + 1) ^ 6 + 1) + 5) +
        150 * W + 300 + m * (1400 * (n + 1) ^ 6 + 1)) := by
    intro SV hSV
    obtain ⟨Ql, hQl, rfl⟩ := List.mem_map.1 hSV
    have hQlw := hSw Ql hQl
    have hpair : ∀ TV ∈ Qs.map tmGlObjsVal, FunAll P (b + 98) (.list [.list [c0, tmGlObjsVal Ql], TV])
        (fun w cost => (∃ Q' ∈ Qs, TV = tmGlObjsVal Q' ∧
          CosetC n w (Iso (gens hs) (tmGlMs Ql) (tmGlMs Q'))) ∧ w.wt ≤ 700 * (n + 1) ^ 6 ∧
          cost ≤ Cp) := by
      intro TV hTV
      obtain ⟨Q'l, hQ'l, rfl⟩ := List.mem_map.1 hTV
      have hQ'lw := hSw Q'l hQ'l
      have hW' : (Val.list [.list [c0, tmGlObjsVal Ql], tmGlObjsVal Q'l]).wt ≤ 10 * W + 20 := by
        have := wt_list2_le (.list [c0, tmGlObjsVal Ql]) (tmGlObjsVal Q'l)
        have := wt_list2_le c0 (tmGlObjsVal Ql)
        omega
      have hIn' : TmRiListIn (gens σB) (Ql ++ Q'l) := by
        intro o ho
        rcases List.mem_append.1 ho with ho | ho
        · exact hIn o (hZ Ql hQl o ho)
        · exact hIn o (hZ Q'l hQ'l o ho)
      refine (tmRi_rebPair_spec hReb hglue hc0 hIn' hoxIn hBH hAB hB hsx hkx hNH hNA hNn hAn hfuel
        hcomm hNox (hQs Ql hQl) (hQs Q'l hQ'l) (fun o ho => hZo o (hZ Ql hQl o ho))
        (fun o ho => hZo o (hZ Q'l hQ'l o ho)) hW' hWV).mono
        fun w cw h => ⟨⟨Q'l, hQ'l, rfl, h.1⟩, h.2.1, h.2.2⟩
    have hmap := tmRi_mapU (tmRiReb_mods hReb).2.2.2.2 (c := .list [c0, tmGlObjsVal Ql]) hpair
    have da0 := Det.arg' (P := P) (vs := [c, tmGlObjsVal Ql]) (rest := []) (j := 0) rfl
    have da1 := Det.arg' (P := P) (vs := [c, tmGlObjsVal Ql]) (rest := []) (j := 1) rfl
    have dc0 := Det.get' da0 (Det.nat 0) (v := c0) rfl
    have dPV := Det.get' da0 (Det.nat 1) (v := PV) rfl
    have dcall_arg := Det.mk2 (Det.mk2 dc0 da1) dPV
    refine FunAll.intro (tmRiReb_mods hReb).2.1 (EvalAll.call_funAll dcall_arg fun v ca hv => ?_)
    obtain ⟨rfl, hca⟩ := hv
    refine hmap.mono fun w cw ⟨ws, hw, hR, hww, hcw'⟩ => ⟨⟨Ql, hQl, rfl, ws, hw, hR.imp
      fun _ _ h => h⟩, by
        rw [hlenPV] at hww
        have e : m * (2 * (700 * (n + 1) ^ 6) + 1) = m * (1400 * (n + 1) ^ 6 + 1) := by ring
        omega, ?_⟩
    have hp1 : (Qs.map tmGlObjsVal).length * Cp = m * Cp := by rw [hlenPV]
    have hp2 : mapK * ((Qs.map tmGlObjsVal).length + 1) *
        ((Val.list [Val.list [c0, tmGlObjsVal Ql], Val.list (List.map tmGlObjsVal Qs)]).wt +
          (List.map tmGlObjsVal Qs).length * (2 * (700 * (n + 1) ^ 6) + 1) + 5) =
        mapK * (m + 1) * ((Val.list [Val.list [c0, tmGlObjsVal Ql], PV]).wt +
          m * (2 * (700 * (n + 1) ^ 6) + 1) + 5) := by rw [hlenPV]
    have hp3 : (Qs.map tmGlObjsVal).length * (2 * (700 * (n + 1) ^ 6) + 1) =
        m * (1400 * (n + 1) ^ 6 + 1) := by rw [hlenPV]; ring
    have h1 := wt_list2_le (.list [c0, tmGlObjsVal Ql]) PV
    have h2 := wt_list2_le c0 (tmGlObjsVal Ql)
    have h4 := wt_list2_le c (tmGlObjsVal Ql)
    have h5 : (Val.nat 0).wt = 2 := rfl
    have h5' : (Val.nat 1).wt = 3 := rfl
    have e : m * (2 * (700 * (n + 1) ^ 6) + 1) = m * (1400 * (n + 1) ^ 6 + 1) := by ring
    have h6 : (Val.list [Val.list [c0, tmGlObjsVal Ql], PV]).wt + m * (2 * (700 * (n + 1) ^ 6) + 1) + 5 ≤
        10 * W + 20 + m * (1400 * (n + 1) ^ 6 + 1) + 5 := by omega
    have h7 := Nat.mul_le_mul_left (mapK * (m + 1)) h6
    omega
  refine (tmRi_mapU (tmRiReb_mods hReb).2.2.2.1 (c := c) hrow).mono fun w cw ⟨ws, hw, hR, hww, hcw'⟩ =>
    ⟨ws, hw, hR.imp fun _ _ h => h, by rw [hlenPV] at hww; exact hww, ?_⟩
  have hp1 : (Qs.map tmGlObjsVal).length = m := hlenPV
  have hq1 : ∀ K : ℕ, (Qs.map tmGlObjsVal).length * K = m * K := fun K => by rw [hp1]
  have hq2 : ∀ K : ℕ, mapK * ((Qs.map tmGlObjsVal).length + 1) * K = mapK * (m + 1) * K :=
    fun K => by rw [hp1]
  simp only [hq1, hq2] at hcw'
  have e0 : (Val.list [c, Val.list (List.map tmGlObjsVal Qs)]).wt = (Val.list [c, PV]).wt := rfl
  have h2 : mapK * (m + 1) * ((Val.list [c, PV]).wt + m * (2 * (m * (1400 * (n + 1) ^ 6 + 1) + 4) +
      1) + 5) ≤ mapK * (m + 1) * (W + m * (2 * (m * (1400 * (n + 1) ^ 6 + 1) + 4) + 1) + 5) :=
    Nat.mul_le_mul_left _ (by omega)
  refine le_trans hcw' ?_
  unfold tmRiRebTabC
  rw [e0, ← hCp]
  omega

theorem tmRi_profs_hat_left_of_fixes {H A : Subgroup (Perm (Fin n))}
    (hAn : GI.Multicoset.Normalizes H A) {X Y : List (TmRiO n)} (hfixX : Fixes A (tmGlMs X))
    {obs : List (TmRiO n)} (hl : obs.length = (tmRiPcsO (gens []) X).length)
    (hP : ∀ i (hi : i < obs.length), TmRiProfOut H A (tmRiPs (gens []) X Y) (0 + i) obs[i]) :
    tmGlMs obs = tmRiHat H A (tmRiCol H (tmRiPs (gens []) X Y))
      (tmRiRepM H (tmRiPs (gens []) X Y)) (tmGlMs X) := by
  rw [tmRi_profs_ms hAn (by simp [tmRiPs]) hl hP]
  unfold tmRiHat
  rw [tmRi_pieces_eq_of_fixes hfixX, ← tmRiPcsO_ms (gens []) X]
  simp [tmRiPs]

theorem tmRi_profs_hat_right_of_fixes {H A : Subgroup (Perm (Fin n))}
    (hAn : GI.Multicoset.Normalizes H A) {X Y : List (TmRiO n)} (hfixY : Fixes A (tmGlMs Y))
    {obs : List (TmRiO n)} (hl : obs.length = (tmRiPcsO (gens []) Y).length)
    (hP : ∀ i (hi : i < obs.length),
      TmRiProfOut H A (tmRiPs (gens []) X Y) ((tmRiPcsO (gens []) X).length + i) obs[i]) :
    tmGlMs obs = tmRiHat H A (tmRiCol H (tmRiPs (gens []) X Y))
      (tmRiRepM H (tmRiPs (gens []) X Y)) (tmGlMs Y) := by
  rw [tmRi_profs_ms hAn (by simp [tmRiPs]) hl hP]
  unfold tmRiHat
  rw [tmRi_pieces_eq_of_fixes hfixY, ← tmRiPcsO_ms (gens []) Y]
  simp [tmRiPs]

theorem tmRi_triv_det {P : Program} {env : List Val} {eA : Expr}
    {σA : List (Perm (Fin n))} {cA : ℕ} (hAl : σA.length ≤ n ^ 2)
    (dA : Det P env eA (encGroup σA) cA) :
    Det P env (mk2 (.get eA (.nat 0)) (mk1 (.get (.get eA (.nat 1)) (.nat 0))))
      (encGroup ([] : List (Perm (Fin n)))) (3 * cA + 10000 * (n + 1) ^ 6) := by
  have hF1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hAw : (encGroup σA).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hAl
  have h0w : (encGroup ([] : List (Perm (Fin n)))).wt ≤ 320 * (n + 1) ^ 6 :=
    wt_encGroup_le_sq (by simp)
  have dn := det_get_lt dA (i := 0) rfl hAw (by decide)
  have dL := det_get_lt dA (i := 1) (v := .list ((1 :: σA).map encPerm)) rfl hAw (by decide)
  have hLw : (Val.list ((1 :: σA).map encPerm)).wt ≤ 320 * (n + 1) ^ 6 :=
    Nat.le_of_lt (wt_get_lt (i := 1) rfl hAw)
  have d1 := det_get_lt dL (i := 0) (v := encPerm (1 : Perm (Fin n))) rfl hLw (by decide)
  have h1w : (encPerm (1 : Perm (Fin n))).wt ≤ 320 * (n + 1) ^ 6 :=
    Nat.le_of_lt (wt_get_lt (i := 0) rfl hLw)
  have hn_w : (Val.nat n).wt ≤ 320 * (n + 1) ^ 6 :=
    Nat.le_of_lt (wt_get_lt (i := 0) rfl hAw)
  have dmk1 := Det.mk1 d1
  have hmk1w : (Val.list [encPerm (1 : Perm (Fin n))]).wt ≤ 640 * (n + 1) ^ 6 + 5 := by
    have := wt_list1_le (encPerm (1 : Perm (Fin n))); omega
  obtain ⟨dmk2, _⟩ := det_mk2_le dn dmk1 hn_w hmk1w
  have e : Val.list [.nat n, .list [encPerm (1 : Perm (Fin n))]] =
      encGroup ([] : List (Perm (Fin n))) := rfl
  exact e ▸ dmk2.mono (by omega)

theorem tmRi_sup_det {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem)
    {env : List Val} {eA eh : Expr} {σA hs : List (Perm (Fin n))} {cA ch : ℕ}
    (hAl : σA.length ≤ n ^ 2) (hsl : hs.length ≤ n ^ 2)
    (dA : Det P env eA (encGroup σA) cA) (dh : Det P env eh (encGroup hs) ch) :
    Det P env (.call (b + 43) (mk2 (.get eA (.nat 0))
        (.call (b + 48) (mk2 (.get eA (.nat 1)) (.get eh (.nat 1))))))
      (encGroup (keepList (σA ++ 1 :: hs)))
      (2 * cA + ch + reduceCost hmem n (2 * n ^ 2 + 1) + 10 ^ 7 * (n + 1) ^ 8) := by
  have dn := Det.get' dA (Det.nat 0) (v := .nat n) rfl
  have dgA := Det.get' dA (Det.nat 1) (v := .list ((1 :: σA).map encPerm)) rfl
  have dgs := Det.get' dh (Det.nat 1) (v := .list ((1 :: hs).map encPerm)) rfl
  have dapp := Det.call (Det.mk2 dgA dgs) (tmRi_append_det hP.app _ _)
  have happ : Val.list (List.map encPerm (1 :: σA) ++ List.map encPerm (1 :: hs)) =
      .list ((1 :: (σA ++ 1 :: hs)).map encPerm) := by simp
  rw [happ] at dapp
  have dgrp := Det.mk2 dn dapp
  have hgrp : Val.list [.nat n, .list ((1 :: (σA ++ 1 :: hs)).map encPerm)] =
      encGroup (σA ++ 1 :: hs) := by simp [encGroup, GI.Cited.encPerms]
  rw [hgrp] at dgrp
  have dred := Det.call dgrp (reduce_spec hmem hP.red hP.mem (σA ++ 1 :: hs))
  refine dred.mono ?_
  have h1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have e2 : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hwA := wt_encGroup_le_sq hAl
  have hwh := wt_encGroup_le_sq hsl
  have hwK := wt_encGroup_le_sq (length_keepList_le (σA ++ 1 :: hs))
  have hnn : (Val.nat n).wt < (encGroup σA).wt := wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hxs : (Val.list ((1 :: σA).map encPerm)).wt < (encGroup σA).wt :=
    wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hys : (Val.list ((1 :: hs).map encPerm)).wt < (encGroup hs).wt :=
    wt_le_wt_list (vs := [.nat n, _]) (by simp)
  have hl : (σA ++ 1 :: hs).length ≤ 2 * n ^ 2 + 1 := by simp; omega
  have hT : ((σA ++ 1 :: hs).length + 2) * (n + 1) ≤ 3 * (n + 1) ^ 3 := by
    calc _ ≤ 3 * (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = 3 * (n + 1) ^ 3 := by ring
  have hT2 : (((σA ++ 1 :: hs).length + 2) * (n + 1)) ^ 2 ≤ 9 * (n + 1) ^ 6 := by
    calc _ ≤ (3 * (n + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left hT 2
      _ = 9 * (n + 1) ^ 6 := by ring
  have hG2 := wt_encGroup_le (σA ++ 1 :: hs)
  have hL2 := wt_list_encPerms_le (1 :: (σA ++ 1 :: hs))
  simp only [List.length_cons] at hL2
  have hL2' : (Val.list ((1 :: (σA ++ 1 :: hs)).map encPerm)).wt ≤ 117 * (n + 1) ^ 6 := by
    have : ((σA ++ 1 :: hs).length + 1 + 1) = (σA ++ 1 :: hs).length + 2 := rfl
    rw [this] at hL2; omega
  have hw2 := wt_list2_le (.list ((1 :: σA).map encPerm)) (.list ((1 :: hs).map encPerm))
  have hlm : loopModK * ((List.map encPerm (1 :: hs)).length + 1) *
      ((Val.list [Val.list (List.map encPerm (1 :: σA)), Val.list (List.map encPerm (1 :: hs))]).wt +
        (List.map encPerm (1 :: hs)).length +
        (Val.list (List.map encPerm (1 :: (σA ++ 1 :: hs)))).wt + 1) ≤ 4 * 10 ^ 6 * (n + 1) ^ 8 := by
    rw [mul_assoc, List.length_map, List.length_cons]
    calc _ ≤ loopModK * (2 * (n + 1) ^ 2 * (2000 * (n + 1) ^ 6)) := by
          refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _ = 4 * 10 ^ 6 * (n + 1) ^ 8 := by simp only [loopModK]; ring
  have hrc := reduceCost_mono hmem n hl
  have hw4 := wt_list2_le (.nat n) (.list ((1 :: (σA ++ 1 :: hs)).map encPerm))
  have h50 : (Val.nat 0).wt = 2 := rfl
  have h51 : (Val.nat 1).wt = 3 := rfl
  omega

private theorem det_mkList5_le {P : Program} {env : List Val}
    {e1 e2 e3 e4 e5 : Expr} {v1 v2 v3 v4 v5 : Val} {c W : ℕ}
    (h1 : Det P env e1 v1 c) (h2 : Det P env e2 v2 c) (h3 : Det P env e3 v3 c)
    (h4 : Det P env e4 v4 c) (h5 : Det P env e5 v5 c)
    (hw : v1.wt + v2.wt + v3.wt + v4.wt + v5.wt ≤ W) :
    Det P env (Expr.mkList [e1, e2, e3, e4, e5])
      (.list [v1, v2, v3, v4, v5]) (5 * c + 12 * W + 100) ∧
    (Val.list [v1, v2, v3, v4, v5]).wt ≤ 2 * W + 12 := by
  have hwl : (Val.list [v1, v2, v3, v4, v5]).wt ≤ 2 * W + 12 := by
    have := wt_list_le [v1, v2, v3, v4, v5]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    omega
  refine ⟨(Det.mkList (P := P) (env := env) (c := c)
    [(e1, v1), (e2, v2), (e3, v3), (e4, v4), (e5, v5)] (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5)).mono (by
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      omega), hwl⟩

theorem tmRi_reb_tabArg_det {P : Program} {M : ℕ}
    {v0 v1 v2 v3 PV : Val} {σB σA hs hk : List (Perm (Fin n))}
    {S' Tl : List (TmRiO n)} {ox : TmRiO n}
    (hox : Tl[0]? = some ox)
    (hBl : σB.length ≤ n ^ 2) (hAl : σA.length ≤ n ^ 2) (hkl : hk.length ≤ n ^ 2)
    (haw : (Val.list [v0, encGroup σA, encGroup hs, encGroup hk,
      tmGlObjsVal S', tmGlObjsVal Tl]).wt ≤ 15000 * tmRiB n M)
    (hTw : (tmGlObjsVal Tl).wt ≤ 2020 * tmRiB n M)
    (hPw : PV.wt ≤ 9000 * ((M + 1) * tmRiB n M)) :
    let e5 : List Val := [.list [v0, encGroup σA, encGroup hs, encGroup hk,
      tmGlObjsVal S', tmGlObjsVal Tl], v1, v2, v3, PV, encGroup σB]
    let c0 : Val := .list [encGroup σB, encGroup hk, encGroup σA,
      tmGlObjVal (0, ox.2.1, ox.2.2), encPerm (1 : Perm (Fin n))]
    Det P e5 (mk2 (mk2 (Expr.mkList [.var 5, arg 3, arg 1,
        mk3 (.nat 0) (.get (.get (arg 5) (.nat 0)) (.nat 1)) (.get (.get (arg 5) (.nat 0)) (.nat 2)),
        .get (.get (arg 1) (.nat 1)) (.nat 0)]) (.var 4)) (.var 4))
      (.list [.list [c0, PV], PV]) (tmRiSQ n M) ∧
    (Val.list [.list [c0, PV], PV]).wt ≤ 150000 * ((M + 1) * tmRiB n M) := by
  intro e5 c0
  obtain ⟨fB1, fB2, -, -, fB5⟩ := tmRiB_facts n M
  obtain ⟨fV1, fV2, fV3, fV4⟩ := tmRiVs_facts n M
  have hF1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hSQ : 10 ^ 5 * (tmRiVs n M + 1) ≤ tmRiSQ n M := by
    unfold tmRiSQ; exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have hBw : (encGroup σB).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hBl
  have hAw : (encGroup σA).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hAl
  have hkw : (encGroup hk).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hkl
  have h1pw : (encPerm (1 : Perm (Fin n))).wt ≤ 320 * (n + 1) ^ 6 := by
    have := wt_encPerm_le (1 : Perm (Fin n))
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hoxw : (tmGlObjVal ox).wt ≤ 2020 * tmRiB n M :=
    Nat.le_of_lt (wt_get_lt (v := tmGlObjVal ox) (i := 0) (by simp [hox]) hTw)
  have hox1w : (encGroup ox.2.1).wt ≤ 2020 * tmRiB n M :=
    Nat.le_of_lt (wt_get_lt (i := 1) rfl hoxw)
  have hox2w : (encPerm ox.2.2).wt ≤ 2020 * tmRiB n M :=
    Nat.le_of_lt (wt_get_lt (i := 2) rfl hoxw)
  have droot := (Det.var' (P := P) (env := e5) (i := 0) rfl).mono
    (c' := 15000 * tmRiB n M + 1) (by omega)
  have da1 := det_get_lt droot (i := 1) (v := encGroup σA) rfl haw (by decide)
  have da3 := det_get_lt droot (i := 3) (v := encGroup hk) rfl haw (by decide)
  have da5 := det_get_lt droot (i := 5) (v := tmGlObjsVal Tl) rfl haw (by decide)
  have dv4 := (Det.var' (P := P) (env := e5) (i := 4) (v := PV) rfl).mono
    (c' := 9000 * ((M + 1) * tmRiB n M) + 5) (by omega)
  have dv5 := (Det.var' (P := P) (env := e5) (i := 5) (v := encGroup σB) rfl).mono
    (c' := 320 * (n + 1) ^ 6 + 5) (by omega)
  have da1_1 := det_get_lt da1 (i := 1) (v := .list ((1 :: σA).map encPerm)) rfl hAw (by decide)
  have hL1w : (Val.list ((1 :: σA).map encPerm)).wt ≤ 320 * (n + 1) ^ 6 :=
    Nat.le_of_lt (wt_get_lt (i := 1) rfl hAw)
  have d1p := det_get_lt da1_1 (i := 0) (v := encPerm (1 : Perm (Fin n))) rfl hL1w (by decide)
  have dox := det_get_lt da5 (v := tmGlObjVal ox) (i := 0) (by simp [hox]) hTw (by decide)
  have dox1 := det_get_lt dox (i := 1) (v := encGroup ox.2.1) rfl hoxw (by decide)
  have dox2 := det_get_lt dox (i := 2) (v := encPerm ox.2.2) rfl hoxw (by decide)
  obtain ⟨dox0, hox0w⟩ := det_mk3_le (Det.nat 0) dox1 dox2 (wt_nat_le 0) hox1w hox2w
  have eox0 : Val.list [.nat 0, encGroup ox.2.1, encPerm ox.2.2] = tmGlObjVal (0, ox.2.1, ox.2.2) := rfl
  have dox0' : Det P e5 (mk3 (.nat 0) (.get (.get (arg 5) (.nat 0)) (.nat 1))
      (.get (.get (arg 5) (.nat 0)) (.nat 2))) (tmGlObjVal (0, ox.2.1, ox.2.2))
      (200000 * tmRiB n M) := eox0 ▸ dox0.mono (by omega)
  have hox0w' : (tmGlObjVal (0, ox.2.1, ox.2.2)).wt ≤ 8100 * tmRiB n M := eox0 ▸ hox0w.trans (by omega)
  obtain ⟨dc0, hc0w⟩ := det_mkList5_le (c := 200000 * tmRiB n M) (W := 10000 * tmRiB n M)
    (dv5.mono (by omega)) (da3.mono (by omega)) (da1.mono (by omega)) dox0' (d1p.mono (by omega))
    (by omega)
  have ec0 : Val.list [encGroup σB, encGroup hk, encGroup σA,
      tmGlObjVal (0, ox.2.1, ox.2.2), encPerm (1 : Perm (Fin n))] = c0 := rfl
  have dc0' : Det P e5 (Expr.mkList [.var 5, arg 3, arg 1,
      mk3 (.nat 0) (.get (.get (arg 5) (.nat 0)) (.nat 1)) (.get (.get (arg 5) (.nat 0)) (.nat 2)),
      .get (.get (arg 1) (.nat 1)) (.nat 0)]) c0 (2000000 * tmRiB n M) :=
    ec0 ▸ dc0.mono (by omega)
  have hc0w' : c0.wt ≤ 20020 * ((M + 1) * tmRiB n M) := ec0 ▸ hc0w.trans (by omega)
  obtain ⟨dc0P, hc0Pw⟩ := det_mk2_le dc0' dv4 hc0w' hPw
  obtain ⟨dall, hallw⟩ := det_mk2_le dc0P dv4 hc0Pw hPw
  exact ⟨dall.mono (by omega), hallw.trans (by omega)⟩

/-- The cost of rebasing `S'` and `T` into `H_x`-objects (`b + 96`) besides `T`. -/
noncomputable def tmRiRebC (psci : Prim) (hmem : Membership) (Kg Dg n M : ℕ) : ℕ :=
  2 * tmRiPcsC (tmRiObjPC psci n (2 * M)) (tmRiVs n M) +
    reduceCost hmem n (2 * n ^ 2 + 1) +
    tmRiRebTabC Kg Dg n M (2 * M) (tmRiVs n M) +
    2 * tmRiPrC hmem n M + 15 * tmRiSQ n M + 10 * (700 * (n + 1) ^ 6 + 1)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **Rebasing `S'` and `T` into `H_x`-objects and calling `b` (`b + 96`).** -/
theorem tmRi_reb_spec {P : Program} {b jsci jder jmem gObj : ℕ}
    {hsci : SolvableCosetIntersection} {hder : DerivedSubgroup} {hmem : Membership}
    (hP : TmRiAt P b jsci jder jmem gObj hsci hder hmem) {Kg Dg M ℓ T : ℕ}
    (hReb : P.HasAt (b + 96) (tmRiRebFuns b gObj))
    (hglue : Iface.TermGlueObjSpec P Kg Dg gObj) (ih : TmRiIH P b n M ℓ T)
    {σH σN σA hs hk : List (Perm (Fin n))} {ox : TmRiO n} {S' Tl : List (TmRiO n)}
    (_hIn : TmRiListIn (gens σH) (S' ++ Tl)) (hoxIn : tmRiStab ox ≤ gens σH)
    (_hHl : σH.length ≤ n ^ 2) (hAl : σA.length ≤ n ^ 2)
    (hsl : hs.length ≤ n ^ 2) (hkl : hk.length ≤ n ^ 2)
    (hNH : gens σN ≤ gens σH) (hNn : GI.Multicoset.Normalizes (gens σH) (gens σN))
    (hA : gens σA = relDerived (gens σH) (gens σN) ℓ)
    (hfuel : relDerived (gens σH) (gens σN) (ℓ + 1) ≤ gens σN) (hℓ : ℓ ≤ n ^ 2 + 5)
    (hsx : gens hs = Aut (gens σH) (tmRiObj ox))
    (hkx : gens hk = gens σA ⊓ Aut (gens σH) (tmRiObj ox))
    (hfixS' : Fixes (gens hk) (tmGlMs S')) (hfixT : Fixes (gens hk) (tmGlMs Tl))
    (hS'o : ∀ o ∈ S', SameOrb (gens σA) (tmRiObj ox) (tmRiObj o))
    (hTo : ∀ o ∈ Tl, SameOrb (gens σA) (tmRiObj ox) (tmRiObj o))
    (hNT : Fixes (gens σN) (tmGlMs Tl)) (hox : Tl[0]? = some ox)
    (hS'l : S'.length ≤ M) (hTl : Tl.length ≤ M) (hok : TmRecObjOK M (S' ++ Tl)) :
    FunAll P (b + 96) (.list [.nat ℓ, encGroup σA, encGroup hs, encGroup hk,
        tmGlObjsVal S', tmGlObjsVal Tl])
      (fun u cost => CosetC n u (Iso (gens hs) (tmGlMs S') (tmGlMs Tl)) ∧
        cost ≤ T + tmRiRebC (solvableCosetIntersectionPrim hsci) hmem Kg Dg n M) := by
  obtain ⟨fB1, fB2, fB3, fB4, fB5⟩ := tmRiB_facts n M
  obtain ⟨fV1, fV2, fV3, fV4⟩ := tmRiVs_facts n M
  have hF1 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hn2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn4 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hnn : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hSQ : 10 ^ 5 * (tmRiVs n M + 1) ≤ tmRiSQ n M := by
    unfold tmRiSQ; exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
  have hWoV : 700 * (n + 1) ^ 6 ≤ tmRiVs n M := by omega
  set S'v := S'.map tmGlObjVal with hS'v
  set Tlv := Tl.map tmGlObjVal with hTlv
  set vs : List Val := [.nat ℓ, encGroup σA, encGroup hs, encGroup hk, .list S'v, .list Tlv] with hvs
  have hain : Val.list [.nat ℓ, encGroup σA, encGroup hs, encGroup hk,
      tmGlObjsVal S', tmGlObjsVal Tl] = .list vs := rfl
  rw [hain]
  have hokS' : TmRiOK (2 * M) S' := fun o ho =>
    ⟨(hok o (by simp [ho])).1, by have := (hok o (by simp [ho])).2.1; omega,
      fun o' ho' he => (hok o (by simp [ho])).2.2 o' (by simp [ho']) he⟩
  have hokT : TmRiOK (2 * M) Tl := fun o ho =>
    ⟨(hok o (by simp [ho])).1, by have := (hok o (by simp [ho])).2.1; omega,
      fun o' ho' he => (hok o (by simp [ho])).2.2 o' (by simp [ho']) he⟩
  have hS'w : (Val.list S'v).wt ≤ 2020 * tmRiB n M := tmRi_wt_side hS'l hokS'
  have hTw : (Val.list Tlv).wt ≤ 2020 * tmRiB n M := tmRi_wt_side hTl hokT
  have hAw : (encGroup σA).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hAl
  have hsw : (encGroup hs).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hsl
  have hkw : (encGroup hk).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hkl
  have hlw : (Val.nat ℓ).wt ≤ (n + 1) ^ 6 + 8 := by have := wt_nat_le ℓ; omega
  have haw : (Val.list vs).wt ≤ 15000 * tmRiB n M := by
    have := wt_list_le [.nat ℓ, encGroup σA, encGroup hs, encGroup hk, .list S'v, .list Tlv]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at this
    show (Val.list [.nat ℓ, encGroup σA, encGroup hs, encGroup hk, .list S'v, .list Tlv]).wt ≤ _
    omega
  set R : Val → Prop := fun w => CosetC n w (Iso (gens hs) (tmGlMs S') (tmGlMs Tl)) with hR
  obtain ⟨Wo, hWo⟩ : ∃ w, w = 700 * (n + 1) ^ 6 := ⟨_, rfl⟩
  obtain ⟨Bud, hBud⟩ : ∃ B, B = T + tmRiRebC (solvableCosetIntersectionPrim hsci) hmem Kg Dg n M := ⟨_, rfl⟩
  rw [← hBud]
  have hBud' : Bud = T +
      2 * tmRiPcsC (tmRiObjPC (solvableCosetIntersectionPrim hsci) n (2 * M)) (tmRiVs n M) +
      reduceCost hmem n (2 * n ^ 2 + 1) +
      tmRiRebTabC Kg Dg n M (2 * M) (tmRiVs n M) +
      2 * tmRiPrC hmem n M + 15 * tmRiSQ n M + 10 * (Wo + 1) := by
    rw [hBud, hWo]; unfold tmRiRebC; ring
  refine FunAll.intro (tmRiReb_mods hReb).1 (EvalAll.mono (Q := fun w c => R w ∧ w.wt ≤ Wo ∧ c ≤ Bud) ?_
    fun w c h => ⟨h.1, h.2.2⟩)
  -- let 1: `encGroup []`
  set σA₀ : List (Perm (Fin n)) := [] with hσA₀
  have h0l : σA₀.length ≤ n ^ 2 := by simp [hσA₀]
  have h0w : (encGroup σA₀).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq h0l
  have hnorm0 : ∀ Z : List (TmRiO n), TmRiListNorm (gens σA₀) Z := by
    intro Z o _ h _ g hg
    have hg1 : g = 1 := Subgroup.mem_bot.1 (by simpa [hσA₀, gens] using hg)
    subst hg1
    simp
  have d1 := (tmRi_triv_det hAl (Det.arg' (P := P) (vs := vs) (rest := []) (j := 1)
    (v := encGroup σA) rfl)).mono (c' := tmRiSQ n M) (by omega)
  refine tmRi_letB d1 (fun _ _ h => h.2) (by omega) fun v1 c1 h1 => ?_
  obtain ⟨rfl, -⟩ := h1
  -- pieces of S' and Tl under `gens []`
  set PX := tmRiPcsO (gens σA₀) S' with hPX
  set PY := tmRiPcsO (gens σA₀) Tl with hPY
  set Qs := tmRiPs (gens σA₀) S' Tl with hQs
  have hQsl : Qs.length ≤ 2 * M := by
    have := tmRiPs_length_le (gens σA₀) S' Tl; rw [← hQs] at this; omega
  have hPXl : PX.length ≤ M := (tmRiPcsO_length_le _ _).trans hS'l
  have hPYl : PY.length ≤ M := (tmRiPcsO_length_le _ _).trans hTl
  have hPc : ∀ Q ∈ Qs, TmRiPc σA₀ hk M Q ∧ ∀ o ∈ Q, o ∈ S' ++ Tl := by
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ | hQ
    · obtain ⟨h1, h2⟩ := tmRiPcsO_pc (σA := σA₀) hS'l hfixS' hQ
      exact ⟨h1, fun o ho => List.mem_append_left _ (h2 o ho)⟩
    · obtain ⟨h1, h2⟩ := tmRiPcsO_pc (σA := σA₀) hTl hfixT hQ
      exact ⟨h1, fun o ho => List.mem_append_right _ (h2 o ho)⟩
  have hSw : ∀ Q ∈ Qs, (tmGlObjsVal Q).wt ≤ 2020 * tmRiB n M := by
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ | hQ
    · obtain ⟨o, -, rfl⟩ := tmRiPcsO_mem hQ
      exact (tmRi_wt_objs_sub List.filter_sublist).trans hS'w
    · obtain ⟨o, -, rfl⟩ := tmRiPcsO_mem hQ
      exact (tmRi_wt_objs_sub List.filter_sublist).trans hTw
  have hPXw : (Val.list (PX.map tmGlObjsVal)).wt ≤ 9000 * ((M + 1) * tmRiB n M) :=
    tmRi_wt_pcsL (by omega) fun Q hQ => hSw Q (List.mem_append_left _ hQ)
  have hPYw : (Val.list (PY.map tmGlObjsVal)).wt ≤ 9000 * ((M + 1) * tmRiB n M) :=
    tmRi_wt_pcsL (by omega) fun Q hQ => hSw Q (List.mem_append_right _ hQ)
  have hPw : (Val.list (Qs.map tmGlObjsVal)).wt ≤ 9000 * ((M + 1) * tmRiB n M) :=
    tmRi_wt_pcsL hQsl hSw
  -- let 2: `PX`
  have hEX : (Val.list [encGroup σA₀, .list S'v]).wt ≤ tmRiVs n M := by
    have := wt_list2_le (encGroup σA₀) (.list S'v); omega
  have hpX := tmRi_pcs_spec hP (hnorm0 S') h0l hokS' (E := tmRiVs n M) hEX
  rw [← tmRiPcsO_val, ← hPX] at hpX
  have d2 := Det.call (Det.mk2 (Det.var' (P := P) (env := [.list vs, encGroup σA₀]) (i := 1) rfl)
    (Det.arg' (P := P) (vs := vs) (rest := [encGroup σA₀]) (j := 4) (v := .list S'v) rfl)) hpX
  refine tmRi_letB d2 (fun _ _ h => h.2) (by omega) fun v2 c2 h2 => ?_
  obtain ⟨rfl, -⟩ := h2
  -- let 3: `PY`
  have hEY : (Val.list [encGroup σA₀, .list Tlv]).wt ≤ tmRiVs n M := by
    have := wt_list2_le (encGroup σA₀) (.list Tlv); omega
  have hpY := tmRi_pcs_spec hP (hnorm0 Tl) h0l hokT (E := tmRiVs n M) hEY
  rw [← tmRiPcsO_val, ← hPY] at hpY
  have d3 := Det.call (Det.mk2 (Det.var' (P := P) (env := [.list vs, encGroup σA₀,
    .list (PX.map tmGlObjsVal)]) (i := 1) rfl) (Det.arg' (P := P) (vs := vs)
    (rest := [encGroup σA₀, .list (PX.map tmGlObjsVal)]) (j := 5) (v := .list Tlv) rfl)) hpY
  refine tmRi_letB d3 (fun _ _ h => h.2) (by omega) fun v3 c3 h3 => ?_
  obtain ⟨rfl, -⟩ := h3
  -- let 4: `Qs`
  have happ := tmRi_append_det hP.app (PX.map tmGlObjsVal) (PY.map tmGlObjsVal)
  have eP : PX.map tmGlObjsVal ++ PY.map tmGlObjsVal = Qs.map tmGlObjsVal := by
    simp [hQs, hPX, hPY, tmRiPs]
  rw [eP] at happ
  have d4 := Det.call (Det.mk2 (Det.var' (P := P) (env := [.list vs, encGroup σA₀,
    .list (PX.map tmGlObjsVal), .list (PY.map tmGlObjsVal)]) (i := 2) rfl)
    (Det.var' (P := P) (env := [.list vs, encGroup σA₀,
    .list (PX.map tmGlObjsVal), .list (PY.map tmGlObjsVal)]) (i := 3) rfl)) happ
  have hm4 : loopModK * ((PY.map tmGlObjsVal).length + 1) *
      ((Val.list [.list (PX.map tmGlObjsVal), .list (PY.map tmGlObjsVal)]).wt +
        (PY.map tmGlObjsVal).length + (Val.list (Qs.map tmGlObjsVal)).wt + 1) ≤
      5 * 10 ^ 4 * (tmRiVs n M + 1) ^ 2 := by
    have h1 := wt_list2_le (.list (PX.map tmGlObjsVal)) (.list (PY.map tmGlObjsVal))
    have h2 := length_lt_wt_list (PY.map tmGlObjsVal)
    rw [mul_assoc]
    calc _ ≤ loopModK * ((tmRiVs n M + 1) * (50 * (tmRiVs n M + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
      _ = 5 * 10 ^ 4 * (tmRiVs n M + 1) ^ 2 := by simp only [loopModK]; ring
  have hSQ2 : tmRiSQ n M = 2 * (5 * 10 ^ 4 * (tmRiVs n M + 1) ^ 2) := by unfold tmRiSQ; ring
  have := wt_list2_le (.list (PX.map tmGlObjsVal)) (.list (PY.map tmGlObjsVal))
  refine tmRi_letB d4 (fun _ _ h => h.2) (by omega) fun v4 c4 h4 => ?_
  obtain ⟨rfl, -⟩ := h4
  -- let 5: `σB = keepList (σA ++ 1 :: hs)`
  set e4 : List Val := [.list vs, encGroup σA₀, .list (PX.map tmGlObjsVal),
    .list (PY.map tmGlObjsVal), .list (Qs.map tmGlObjsVal)] with he4
  set σB := keepList (σA ++ 1 :: hs) with hσB
  have hBl : σB.length ≤ n ^ 2 := length_keepList_le _
  have hBw : (encGroup σB).wt ≤ 320 * (n + 1) ^ 6 := wt_encGroup_le_sq hBl
  have hB : gens σB = gens σA ⊔ gens hs := by
    rw [hσB, gens_keepList, tmRi_gens_append, tmRi_gens_one]
  have d5 := (tmRi_sup_det hP hAl hsl
    (Det.arg' (P := P) (vs := vs) (rest := e4.tail) (j := 1) (v := encGroup σA) rfl)
    (Det.arg' (P := P) (vs := vs) (rest := e4.tail) (j := 2) (v := encGroup hs) rfl)).mono
    (c' := reduceCost hmem n (2 * n ^ 2 + 1) + tmRiSQ n M) (by
      have h8_12 : (n + 1) ^ 8 ≤ (n + 1) ^ 6 * (n + 1) ^ 6 := by
        calc (n + 1) ^ 8 ≤ (n + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
          _ = (n + 1) ^ 6 * (n + 1) ^ 6 := by ring
      have h6_V : 10 ^ 7 * (n + 1) ^ 8 ≤ 10 ^ 4 * (tmRiVs n M + 1) ^ 2 := by
        calc 10 ^ 7 * (n + 1) ^ 8
            ≤ 10 ^ 7 * ((n + 1) ^ 6 * (n + 1) ^ 6) := Nat.mul_le_mul_left _ h8_12
          _ ≤ 10 ^ 4 * ((10 ^ 8 * (n + 1) ^ 6) * (10 ^ 8 * (n + 1) ^ 6)) := by nlinarith
          _ ≤ 10 ^ 4 * ((tmRiVs n M + 1) * (tmRiVs n M + 1)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
          _ = 10 ^ 4 * (tmRiVs n M + 1) ^ 2 := by ring
      have hSQ_eq : tmRiSQ n M = 10 * (10 ^ 4 * (tmRiVs n M + 1) ^ 2) := by unfold tmRiSQ; ring
      omega)
  refine tmRi_letB d5 (fun _ _ h => h.2) (by omega) fun v5 c5 h5 => ?_
  obtain ⟨rfl, -⟩ := h5
  -- let 6: rebasing table (`b + 99`)
  set e5 : List Val := e4 ++ [encGroup σB] with he5
  set c0 : Val := .list [encGroup σB, encGroup hk, encGroup σA,
    tmGlObjVal (0, ox.2.1, ox.2.2), encPerm (1 : Perm (Fin n))] with hc0
  obtain ⟨darg6, hW6⟩ := tmRi_reb_tabArg_det (P := P) (M := M)
    (v0 := .nat ℓ) (v1 := encGroup σA₀) (v2 := .list (PX.map tmGlObjsVal))
    (v3 := .list (PY.map tmGlObjsVal)) (PV := .list (Qs.map tmGlObjsVal))
    hox hBl hAl hkl haw hTw hPw
  have hAH : gens σA ≤ gens σH := hA ▸ relDerived_le hNH ℓ
  have hAn : GI.Multicoset.Normalizes (gens σH) (gens σA) := hA ▸ relDerived_normalizes hNn ℓ
  have hNA : gens σN ≤ gens σA := hA ▸ le_relDerived hNH ℓ
  have hBH : gens σB ≤ gens σH := by
    rw [hB, hsx]; exact sup_le hAH (aut_le _ _)
  have hAB : gens σA ≤ gens σB := by rw [hB]; exact le_sup_left
  have hcomm : ∀ a ∈ gens σA, ∀ b ∈ gens σA, a * b * a⁻¹ * b⁻¹ ∈ gens σN := by
    intro a ha b hb
    rw [hA] at ha hb
    simpa [commutatorElement_def] using relDerived_commutator_mem hfuel ha hb
  have hNox : ∀ g ∈ gens σN, tmRiObj ox ↼ g = tmRiObj ox := fun g hg =>
    hNT g hg (tmRiObj ox) (Multiset.mem_coe.2 (List.mem_map_of_mem (List.mem_of_getElem? hox)))
  have hZo : ∀ o ∈ S' ++ Tl, SameOrb (gens σA) (tmRiObj ox) (tmRiObj o) := by
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact hS'o o ho
    · exact hTo o ho
  have hoxInB : tmRiStab ox ≤ gens σB := by
    rw [hB, hsx]
    intro g hg
    exact (le_sup_right : Aut (gens σH) (tmRiObj ox) ≤ gens σA ⊔ Aut (gens σH) (tmRiObj ox))
      ⟨hoxIn hg, mem_tmRiStab_iff.1 hg⟩
  have hInB : TmRiListIn (gens σB) (S' ++ Tl) := by
    intro o ho
    obtain ⟨a, ha, hact⟩ := hZo o ho
    exact tmRiStab_le_of_sameOrb hoxInB (hAB ha) hact
  have hWV6 : 50 * (10 * (150000 * ((M + 1) * tmRiB n M)) + 20) + 200 ≤ tmRiVs n M := by omega
  have htab := EvalAll.call_funAll (f := b + 99) darg6 (Q := fun w c =>
      (∃ tab, w = .list tab ∧ TmRiTab (gens hs) Qs tab ∧ w.wt ≤ 12000 * ((M + 1) * tmRiB n M)) ∧
      c ≤ tmRiRebTabC Kg Dg n M (2 * M) (tmRiVs n M) + 2 * tmRiSQ n M)
      fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (tmRi_rebTab_spec hReb hglue hc0 hInB hoxInB hBH hAB hB hsx hkx hNH hNA hNn hAn
      hfuel hcomm hNox (fun Q hQ => (hPc Q hQ).1) hZo (fun Q hQ o ho => (hPc Q hQ).2 o ho)
      hW6 hWV6).mono fun w c h => ?_
    obtain ⟨tab, rfl, ht, hw, hc⟩ := h
    have hw' := le_trans hw (tmRi_wt_tab hQsl)
    refine ⟨⟨tab, rfl, ht, hw'⟩, ?_⟩
    have hW6_le : 150000 * ((M + 1) * tmRiB n M) ≤ tmRiVs n M := by omega
    have hmono1 : tmRiRebTabC Kg Dg n M Qs.length (150000 * ((M + 1) * tmRiB n M)) ≤
        tmRiRebTabC Kg Dg n M Qs.length (tmRiVs n M) := by
      unfold tmRiRebTabC; gcongr
    have hmono2 := tmRiRebTabC_mono Kg Dg n M hQsl (tmRiVs n M)
    omega
  refine tmRi_letB htab (fun _ _ h => h.2) (by omega) fun v6 c6 h6 => ?_
  obtain ⟨⟨tab, rfl, ht, htw⟩, -⟩ := h6
  have hQsXY : Qs.length = PX.length + PY.length := by simp [hQs, hPX, hPY, tmRiPs]
  have hlPX : (PX.map tmGlObjsVal).length = PX.length := List.length_map _
  have hlPY : (PY.map tmGlObjsVal).length = PY.length := List.length_map _
  have htabw : (Val.list tab).wt ≤ 12000 * ((M + 1) * tmRiB n M) := htw
  have hprofC : ∀ m o : ℕ, m ≤ M → (Val.list [.list [encGroup hk, .list tab, .nat o],
      natList (List.range m)]).wt ≤ tmRiVs n M →
      m * tmRiProfC hmem n (3 * tmRiVs n M) + mapK * (m + 1) *
        ((Val.list [.list [encGroup hk, .list tab, .nat o], natList (List.range m)]).wt +
          m * (2 * (2 * Qs.length + 700 * (n + 1) ^ 6) + 1) + 5) + 8000 * (m + 1) ^ 3 ≤
      tmRiPrC hmem n M := by
    intro m o hm hw
    have h1 : m * tmRiProfC hmem n (3 * tmRiVs n M) ≤ 2 * M * tmRiProfC hmem n (3 * tmRiVs n M) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 := tmRi_wt_profs (n := n) hm hQsl
    have h3 : mapK * (m + 1) * ((Val.list [.list [encGroup hk, .list tab, .nat o],
        natList (List.range m)]).wt + m * (2 * (2 * Qs.length + 700 * (n + 1) ^ 6) + 1) + 5) ≤
        mapK * (2 * M + 1) * (tmRiVs n M + 2000 * tmRiB n M + 5) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h4 : 8000 * (m + 1) ^ 3 ≤ 8000 * (2 * M + 1) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    unfold tmRiPrC; omega
  have hrng : ∀ m : ℕ, m ≤ M → (natList (List.range m)).wt ≤ 4 * tmRiB n M + 4 := by
    intro m hm
    rw [range_eq_encPerm_one]
    have := wt_encPerm_le (1 : Perm (Fin m))
    have h : (m + 1) ^ 2 ≤ tmRiB n M + 1 := by
      have : (m + 1) ^ 2 ≤ (M + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have e : (M + 1) ^ 2 = (M + 1) * (M + 1) := by ring
      have : (M + 1) * (M + 1) ≤ tmRiB n M := Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  -- let 7: profiles of S'
  set e6 : List Val := e5 ++ [.list tab] with he6
  have dlen7 := Det.length (Det.var' (P := P) (env := e6) (i := 2) (v := .list (PX.map tmGlObjsVal)) rfl)
  rw [hlPX] at dlen7
  have drng7 := Det.call dlen7 (range_det hP.range PX.length)
  have darg7 := Det.mk2 (Det.mk3 (Det.arg' (P := P) (vs := vs) (rest := e6.tail) (j := 3)
    (v := encGroup hk) rfl)
    (Det.var' (P := P) (env := e6) (i := 6) (v := .list tab) rfl) (Det.nat 0)) drng7
  have hw7 : (Val.list [.list [encGroup hk, .list tab, .nat 0], natList (List.range PX.length)]).wt ≤
      tmRiVs n M := by
    have := wt_list3_le (encGroup hk) (.list tab) (.nat 0)
    have := wt_list2_le (.list [encGroup hk, .list tab, .nat 0]) (natList (List.range PX.length))
    have := hrng PX.length hPXl
    have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    omega
  have hprofX := EvalAll.call_funAll (f := b + 78) darg7 (Q := fun w c =>
      (∃ obs : List (TmRiO n), w = .list (obs.map tmGlObjVal) ∧ obs.length = PX.length ∧
        (∀ i (hi : i < obs.length), TmRiProfOut (gens hs) (gens hk) Qs (0 + i) obs[i]) ∧
        w.wt ≤ 2000 * tmRiB n M) ∧ c ≤ tmRiPrC hmem n M + tmRiSQ n M) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (tmRi_profs_spec hP hkl ht (o := 0) (m := PX.length) (by omega) (Wa := tmRiVs n M)
      (by have := wt_list3_le (encGroup hk) (.list tab) (.nat 0); have : (Val.nat 0).wt ≤ 2 :=
        wt_nat_le 0; omega)).mono fun w c h => ?_
    obtain ⟨obs, rfl, hl, hpo, hww, hc⟩ := h
    have hww' := le_trans hww (tmRi_wt_profs (n := n) hPXl hQsl)
    refine ⟨⟨obs, rfl, hl, hpo, hww'⟩, ?_⟩
    have := hprofC PX.length 0 hPXl hw7
    have := wt_list3_le (encGroup hk) (.list tab) (.nat 0)
    have : (Val.nat 0).wt ≤ 2 := wt_nat_le 0
    have := hrng PX.length hPXl
    have := wt_nat_le PX.length
    have := wt_encPerm_le (1 : Perm (Fin PX.length))
    omega
  refine tmRi_letB hprofX (fun _ _ h => h.2) (by omega) fun v7 c7 h7 => ?_
  obtain ⟨⟨obsS, rfl, hlS, hpoS, hwS⟩, -⟩ := h7
  -- let 8: profiles of Tl
  set e7 : List Val := e6 ++ [.list (obsS.map tmGlObjVal)] with he7
  have dlen8 := Det.length (Det.var' (P := P) (env := e7) (i := 3) (v := .list (PY.map tmGlObjsVal)) rfl)
  rw [hlPY] at dlen8
  have drng8 := Det.call dlen8 (range_det hP.range PY.length)
  have dlen8' := Det.length (Det.var' (P := P) (env := e7) (i := 2) (v := .list (PX.map tmGlObjsVal)) rfl)
  rw [hlPX] at dlen8'
  have darg8 := Det.mk2 (Det.mk3 (Det.arg' (P := P) (vs := vs) (rest := e7.tail) (j := 3)
    (v := encGroup hk) rfl)
    (Det.var' (P := P) (env := e7) (i := 6) (v := .list tab) rfl) dlen8') drng8
  have hPXw' : (Val.nat PX.length).wt ≤ M + 2 := by have := wt_nat_le PX.length; omega
  have hw8 : (Val.list [.list [encGroup hk, .list tab, .nat PX.length],
      natList (List.range PY.length)]).wt ≤ tmRiVs n M := by
    have := wt_list3_le (encGroup hk) (.list tab) (.nat PX.length)
    have := wt_list2_le (.list [encGroup hk, .list tab, .nat PX.length]) (natList (List.range PY.length))
    have := hrng PY.length hPYl
    omega
  have hprofY := EvalAll.call_funAll (f := b + 78) darg8 (Q := fun w c =>
      (∃ obs : List (TmRiO n), w = .list (obs.map tmGlObjVal) ∧ obs.length = PY.length ∧
        (∀ i (hi : i < obs.length), TmRiProfOut (gens hs) (gens hk) Qs (PX.length + i) obs[i]) ∧
        w.wt ≤ 2000 * tmRiB n M) ∧ c ≤ tmRiPrC hmem n M + tmRiSQ n M) fun v ca hv => by
    obtain ⟨rfl, hca⟩ := hv
    refine (tmRi_profs_spec hP hkl ht (o := PX.length) (m := PY.length) (by omega)
      (Wa := tmRiVs n M)
      (by have := wt_list3_le (encGroup hk) (.list tab) (.nat PX.length); omega)).mono
      fun w c h => ?_
    obtain ⟨obs, rfl, hl, hpo, hww, hc⟩ := h
    have hww' := le_trans hww (tmRi_wt_profs (n := n) hPYl hQsl)
    refine ⟨⟨obs, rfl, hl, hpo, hww'⟩, ?_⟩
    have := hprofC PY.length PX.length hPYl hw8
    have := wt_list3_le (encGroup hk) (.list tab) (.nat PX.length)
    have := hrng PY.length hPYl
    have := wt_nat_le PY.length
    have := wt_encPerm_le (1 : Perm (Fin PY.length))
    omega
  refine tmRi_letB hprofY (fun _ _ h => h.2) (by omega) fun v8 c8 h8 => ?_
  obtain ⟨⟨obsT, rfl, hlT, hpoT, hwT⟩, -⟩ := h8
  -- tail call `b` on `[ℓ, hs, hk, obsS, obsT]`
  have hkh : gens hk ≤ gens hs := by rw [hkx, hsx]; exact inf_le_right
  have hnk : GI.Multicoset.Normalizes (gens hs) (gens hk) := by
    rw [hsx, hkx]
    intro h hh k hk_mem
    exact ⟨hAn h (aut_le (gens σH) (tmRiObj ox) hh) k hk_mem.1,
      (Aut (gens σH) (tmRiObj ox)).mul_mem ((Aut (gens σH) (tmRiObj ox)).mul_mem hh hk_mem.2)
        ((Aut (gens σH) (tmRiObj ox)).inv_mem hh)⟩
  have hhatS : tmGlMs obsS = tmRiHat (gens hs) (gens hk) (tmRiCol (gens hs) Qs)
      (tmRiRepM (gens hs) Qs) (tmGlMs S') :=
    tmRi_profs_hat_left_of_fixes hnk hfixS' hlS hpoS
  have hhatT : tmGlMs obsT = tmRiHat (gens hs) (gens hk) (tmRiCol (gens hs) Qs)
      (tmRiRepM (gens hs) Qs) (tmGlMs Tl) :=
    tmRi_profs_hat_right_of_fixes hnk hfixT hlT hpoT
  have hSP : pieces (gens hk) (tmGlMs S') ⊆ tmRiPF Qs := by
    rw [tmRi_pieces_eq_of_fixes hfixS']; exact tmRiPs_sub_left (gens σA₀) S' Tl
  have hTP : pieces (gens hk) (tmGlMs Tl) ⊆ tmRiPF Qs := by
    rw [tmRi_pieces_eq_of_fixes hfixT]; exact tmRiPs_sub_right (gens σA₀) S' Tl
  have hiso_hat : Iso (gens hs) (tmGlMs obsS) (tmGlMs obsT) =
      Iso (gens hs) (tmGlMs S') (tmGlMs Tl) := by
    rw [hhatS, hhatT]
    exact tmRiHat_iso_eq_of_fixes (tmRi_rep (H := gens hs) (Ps := Qs)) hnk hSP hTP hfixT
  have hokR : TmRecObjOK M (obsS ++ obsT) := tmRi_profs_ok hQsl fun ob hob => by
    rcases List.mem_append.1 hob with h | h
    · exact tmRi_profs_mem hpoS ob h
    · exact tmRi_profs_mem hpoT ob h
  have hInR : TmRiListIn (gens hs) (obsS ++ obsT) := tmRi_profs_in hkh fun ob hob => by
    rcases List.mem_append.1 hob with h | h
    · exact tmRi_profs_mem hpoS ob h
    · exact tmRi_profs_mem hpoT ob h
  have hfixOS : Fixes (gens hk) (tmGlMs obsS) := by rw [hhatS]; exact tmRiHat_fix hnk _
  have hfixOT : Fixes (gens hk) (tmGlMs obsT) := by rw [hhatT]; exact tmRiHat_fix hnk _
  have hfuel_hk : relDerived (gens hs) (gens hk) ℓ ≤ gens hk := by
    rw [hsx, hkx, hA]
    have h1 := relDerived_mono hNH (aut_le (gens σH) (tmRiObj ox))
      (M := relDerived (gens σH) (gens σN) ℓ ⊓ Aut (gens σH) (tmRiObj ox))
      (ℓ := ℓ) inf_le_left ℓ le_rfl
    have h2 := relDerived_le (H := Aut (gens σH) (tmRiObj ox))
      (N := relDerived (gens σH) (gens σN) ℓ ⊓ Aut (gens σH) (tmRiObj ox)) inf_le_right ℓ
    exact le_inf h1 h2
  have hrec := ih hs hk obsS obsT (fun _ => hInR) hkh hnk hfuel_hk hℓ hfixOS hfixOT hsl hkl
    (by omega) (by omega) hokR
  set e8 : List Val := e7 ++ [.list (obsT.map tmGlObjVal)] with he8
  obtain ⟨dml9, _⟩ := det_mkList5_le (P := P) (env := e8) (c := 3 * tmRiVs n M + 20) (W := tmRiVs n M)
    ((Det.arg' (P := P) (vs := vs) (rest := e8.tail) (j := 0) (v := .nat ℓ) rfl).mono (by omega))
    ((Det.arg' (P := P) (vs := vs) (rest := e8.tail) (j := 2) (v := encGroup hs) rfl).mono (by omega))
    ((Det.arg' (P := P) (vs := vs) (rest := e8.tail) (j := 3) (v := encGroup hk) rfl).mono (by omega))
    ((Det.var' (P := P) (env := e8) (i := 7) rfl).mono (by
      show (Val.list (obsS.map tmGlObjVal)).wt + 1 ≤ _; omega))
    ((Det.var' (P := P) (env := e8) (i := 8) rfl).mono (by
      show (Val.list (obsT.map tmGlObjVal)).wt + 1 ≤ _; omega))
    (by
      have e1 : (tmGlObjsVal obsS).wt = (Val.list (obsS.map tmGlObjVal)).wt := rfl
      have e2 : (tmGlObjsVal obsT).wt = (Val.list (obsT.map tmGlObjVal)).wt := rfl
      omega)
  refine EvalAll.call_funAll dml9 fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine hrec.mono fun u cu h => ?_
  have hw := tmRi_wt_ansC h.1
  rw [hiso_hat] at h
  exact ⟨h.1, by omega, by omega⟩

end GI.Impl
