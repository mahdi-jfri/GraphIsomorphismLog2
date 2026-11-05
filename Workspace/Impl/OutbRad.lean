module

public import Workspace.Impl.TermRad
public import Workspace.Impl.SocPre
public import Workspace.Impl.OutbSupp

@[expose] public section

/-!
# Stage 2 radical subgroup program (`OutbRad`)

Given `[encGroup σH, encGroup σN]` with `N = gens σN ≤ H = gens σH`, `N` normalized by `H`, and
`N` transitive on `Fin n`, `outbRadEntry` computes generators of a subgroup `R'` satisfying
Lemma A.21′ (`radical_free_order_of_quotient`):
- `N ≤ R' ≤ H`,
- `R' / N` is solvable (`∃ ℓ, relDerived R' N ℓ ≤ N`),
- `[H : R'] ≤ b(H / N)²`.

The program proceeds in ten steps:
1. Compute `v1` (`GensOf R v1`, `R = radicalPreimage H N`) via `radEntry` on `[encGroup σH, encGroup σN]`.
2. Wrap `v1` into `encGroup rs'` (`gens rs' = R`) via `mkGroupFuns`.
3. Compute a nonabelian-chief chain `cs = radCsVal L` from `H` to `R` via `tcChainEntry` on
   `[encGroup σH, encGroup rs']` (using that `R` contains the transitive subgroup `N` and is
   therefore transitive on `Fin n`).
4. Map `appendFuns` with `v1` over `cs` via `mapFuns` to obtain `ws = socCsVal (L.map (rs ++ ·))`,
   which satisfies `SocChain H R` by `soc_chain_of_nonabelianChiefChain`.
5. Compute `v5` (`GensOf E_H v5`, `E_H = soclePreimage H R`) via `socPreEntry` on
   `[encGroup σH, encGroup rs', ws]` (using `[E_H : R] ≤ b(H / N) ≤ radQ n`).
6. Wrap `v5` into `encGroup es'` (`gens es' = E_H`) via `mkGroupFuns`.
7. Compute `v7` (`GensOf K*_H v7`, `K*_H = radicalPreimage H E_H`) via `radEntry` on
   `[encGroup σH, encGroup es']` (using that `E_H` contains `N` and is therefore transitive on `Fin n`).
8. Wrap `v7` into `encGroup ks'` (`gens ks' = K*_H`) via `mkGroupFuns`.
9. Enumerate right coset representatives `v9 = .list (reps.map encPerm)` of `R` in `E_H` via
   `gmpRepsEntryF` on `[encGroup rs', v5]`.
10. Compute generators of the solvable-quotient subgroup `R'` via `outbSuppEntry` on
    `[encGroup ks', encGroup es', encGroup rs', v9]`.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang GI.Cited GI.RadicalSocle GI.RadicalFreeOrder GI.Composition Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

set_option maxRecDepth 100000

/-! ### Mathematical helpers: transitivity, index of `soclePreimage`, and `map` of `append` -/

/-- Any subgroup `B` containing a pretransitive subgroup `A` is itself pretransitive. -/
theorem outb_isPretransitive_of_le {α : Type*} {G : Type*} [Group G] [MulAction G α]
    {A B : Subgroup G} (hAB : A ≤ B) [htr : MulAction.IsPretransitive A α] :
    MulAction.IsPretransitive B α := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := htr.exists_smul_eq x y
  exact ⟨⟨g.1, hAB g.2⟩, hg⟩

/-- For `N ⊴ H ≤ Sym(n)` with `N` transitive on `Fin n`, `bFac (H ⧸ N.subgroupOf H) ≤ radQ n`. -/
theorem outb_bFac_quotient_le_radQ {H N : Subgroup (Perm (Fin n))}
    (hNH : N ≤ H) [(N.subgroupOf H).Normal] [htr : MulAction.IsPretransitive N (Fin n)] :
    bFac (H ⧸ N.subgroupOf H) ≤ radQ n := by
  have h : (bFac (H ⧸ N.subgroupOf H) : ℝ) ≤ (n : ℝ) ^ Real.logb 2 n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have : Subsingleton (Perm (Fin 0)) := inferInstance
      have : Subsingleton (H ⧸ N.subgroupOf H) := by
        refine ⟨fun x y => ?_⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
        congr 1
        exact Subsingleton.elim x y
      have hb : bFac (H ⧸ N.subgroupOf H) = 1 := by
        have h := aFac_mul_bFac (X := H ⧸ N.subgroupOf H)
        rw [Nat.card_unique] at h
        exact Nat.eq_one_of_mul_eq_one_left h
      rw [hb]; simp
    · exact GI.Proved.gmpTransitiveNonabelian n hn0 H N hNH htr _ _ (GI.Composition.spec _)
  exact Nat.cast_le.mp (h.trans (Nat.le_ceil _))

/-- For `N ⊴ H ≤ Sym(n)` with `N` transitive on `Fin n` and `R = radicalPreimage H N`,
the index `[soclePreimage H R : R]` is at most `radQ n`. -/
theorem outb_index_soclePreimage_le_radQ {H N R : Subgroup (Perm (Fin n))}
    (hNH : N ≤ H) (hnN : GI.Multicoset.Normalizes H N)
    [htr : MulAction.IsPretransitive N (Fin n)]
    (hR : R = GI.Multicoset.radicalPreimage H N) :
    (R.subgroupOf (soclePreimage H R)).index ≤ radQ n := by
  subst hR
  have : (N.subgroupOf H).Normal := GI.Multicoset.normal_of_normalizes hnN
  obtain ⟨hRH, -, -⟩ := GI.Multicoset.radicalPreimage_spec hNH hnN
  have hnR : GI.Multicoset.Normalizes H (GI.Multicoset.radicalPreimage H N) :=
    GI.Multicoset.normalizes_of_normal hRH
  have : ((GI.Multicoset.radicalPreimage H N).subgroupOf H).Normal :=
    GI.Multicoset.normal_of_normalizes hnR
  have hEH : soclePreimage H (GI.Multicoset.radicalPreimage H N) ≤ H := soclePreimage_le H _
  rw [soc_index_eq_card_quot hEH, soc_quot_soclePreimage]
  have hcard : Nat.card (socle (H ⧸ (GI.Multicoset.radicalPreimage H N).subgroupOf H)) ≤
      bFac (H ⧸ N.subgroupOf H) := by
    rw [← bFac_quotient_radicalPreimage]
    exact card_socle_le_bFac radicalPreimage_quotient_radicalFree
  exact hcard.trans (outb_bFac_quotient_le_radQ hNH)

/-- Any `GmpCosetReps E R reps` covers `E` in the sense of `TmRpCov R reps`. -/
theorem outb_tmRpCov_of_gmpCosetReps {E R : Subgroup (Perm (Fin n))} {reps : List (Perm (Fin n))}
    (hrs : GmpCosetReps E R reps) : ∀ x ∈ E, TmRpCov R reps x := by
  intro x hx
  obtain ⟨r, hr, v, hv, rfl⟩ := hrs.cover x hx
  exact ⟨r, hr, by simpa [mul_assoc] using hv⟩

/-- Relating `map` of `append` on `radCsVal L` to `socCsVal (L.map (rs ++ ·))`. -/
theorem outb_forall2_map_append {rs : List (Perm (Fin n))}
    (L : List (List (Perm (Fin n)))) (ws : List Val)
    (h : List.Forall₂ (fun (x w : Val) => ∃ ys, x = Val.list ys ∧ w = Val.list (rs.map encPerm ++ ys))
      (L.map fun hs => Val.list (hs.map encPerm)) ws) :
    Val.list ws = socCsVal (L.map fun hs => rs ++ hs) := by
  induction L generalizing ws with
  | nil => cases h; rfl
  | cons hs L ih =>
    cases h with
    | cons hhd htl =>
      rcases hhd with ⟨_, h1, rfl⟩
      cases Val.list.inj h1
      have ih' := Val.list.inj (ih _ htl)
      simp [socCsVal, List.map_append, ih']

/-- If `IsNonabelianChiefChain H R (L.map gens)` and `gens rs = R`, then
`Ws = L.map (fun hs => rs ++ hs)` satisfies `SocChain H R (Ws.map gens)`. -/
theorem outb_socChain_of_map_append {H R : Subgroup (Perm (Fin n))} {rs : List (Perm (Fin n))}
    {L : List (List (Perm (Fin n)))} (hRH : R ≤ H) (hnR : GI.Multicoset.Normalizes H R)
    (hrs : gens rs = R) (hc : IsNonabelianChiefChain H R (L.map gens)) :
    SocChain H R ((L.map fun hs => rs ++ hs).map gens) := by
  have hmap : (L.map fun hs => rs ++ hs).map gens = (L.map gens).map (fun C => R ⊔ C) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun hs _ => ?_
    simp [outb_gens_append, hrs]
  rw [hmap]
  exact soc_chain_of_nonabelianChiefChain hRH hnR hc

/-- Weight bound for `Val.list (ws.map encPerm)` when `ws.length ≤ 2 * n ^ 2`. -/
theorem outb_wt_list_encPerms_le_two_sq {ws : List (Perm (Fin n))} (hwl : ws.length ≤ 2 * n ^ 2) :
    (Val.list (ws.map encPerm)).wt ≤ 52 * (n + 1) ^ 6 := by
  have h1 := wt_list_encPerms_le ws
  have hlen : ws.length + 1 ≤ 2 * (n + 1) ^ 2 := by
    have e : 2 * (n + 1) ^ 2 = 2 * n ^ 2 + 4 * n + 2 := by ring
    omega
  have hm : (ws.length + 1) * (n + 1) ≤ 2 * (n + 1) ^ 3 :=
    calc (ws.length + 1) * (n + 1) ≤ 2 * (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_right _ hlen
      _ = 2 * (n + 1) ^ 3 := by ring
  have h2 : ((ws.length + 1) * (n + 1)) ^ 2 ≤ 4 * (n + 1) ^ 6 :=
    calc ((ws.length + 1) * (n + 1)) ^ 2 ≤ (2 * (n + 1) ^ 3) ^ 2 := Nat.pow_le_pow_left hm 2
      _ = 4 * (n + 1) ^ 6 := by ring
  omega

/-- Weight bound for any `v` satisfying `GensOf H v`. -/
theorem outb_wt_of_gensOf {H : Subgroup (Perm (Fin n))} {v : Val} (h : GensOf H v) :
    v.wt ≤ 13 * (n + 1) ^ 6 := by
  obtain ⟨hs, rfl, hl, -⟩ := h
  exact wt_list_encPerms_le_sq hl

/-- Weight bound for `socCsVal (L.map (fun hs => rs ++ hs))` when `rs.length ≤ n ^ 2`,
`L.length ≤ n ^ 2 + 1`, and `∀ hs ∈ L, hs.length ≤ n ^ 2`. -/
theorem outb_wt_socCsVal_map_append {rs : List (Perm (Fin n))} {L : List (List (Perm (Fin n)))}
    (hrl : rs.length ≤ n ^ 2) (hLl : L.length ≤ n ^ 2 + 1)
    (hl : ∀ hs ∈ L, hs.length ≤ n ^ 2) :
    (socCsVal (L.map fun hs => rs ++ hs)).wt ≤ 200 * (n + 1) ^ 8 := by
  set Ws := L.map fun hs => rs ++ hs
  have h1 := wt_list_le (Ws.map fun ws => Val.list (ws.map encPerm))
  have h2 := List.sum_le_length_nsmul ((Ws.map fun ws => Val.list (ws.map encPerm)).map Val.wt)
    (52 * (n + 1) ^ 6) (by
      simp only [Ws, List.map_map, List.mem_map, Function.comp_apply, forall_exists_index, and_imp]
      rintro _ hs hhs rfl
      have hhsl := hl hs hhs
      exact outb_wt_list_encPerms_le_two_sq (by simp [List.length_append]; omega))
  simp only [List.length_map, smul_eq_mul] at h1 h2
  have hWsl : Ws.length ≤ (n + 1) ^ 2 := by
    simp only [Ws, List.length_map]
    have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have h3 : Ws.length * (52 * (n + 1) ^ 6) ≤ (n + 1) ^ 2 * (52 * (n + 1) ^ 6) :=
    Nat.mul_le_mul_right _ hWsl
  have h4 : (n + 1) ^ 2 * (52 * (n + 1) ^ 6) = 52 * (n + 1) ^ 8 := by ring
  have h5 : (n + 1) ^ 2 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  change (Val.list (Ws.map fun ws => Val.list (ws.map encPerm))).wt ≤ 200 * (n + 1) ^ 8
  omega

/-- Specification of `mapFuns` with `appendFuns` to prepend `rs.map encPerm` to every generator
list in `radCsVal L`. -/
theorem outb_map_append_spec {P : Program} {f_map ap : ℕ}
    (hmap : P.HasAt f_map (mapFuns f_map ap)) (hap : P.HasAt ap (appendFuns ap))
    (rs : List (Perm (Fin n))) (L : List (List (Perm (Fin n))))
    (hrl : rs.length ≤ n ^ 2) (hLl : L.length ≤ n ^ 2 + 1)
    (hl : ∀ hs ∈ L, hs.length ≤ n ^ 2) :
    FunAll P f_map (.list [.list (rs.map encPerm), radCsVal L]) (fun w cost =>
      w = socCsVal (L.map fun hs => rs ++ hs) ∧
      cost ≤ 10 ^ 8 * (n + 1) ^ 10) := by
  set xs := L.map fun hs => Val.list (hs.map encPerm) with hxs
  set c := Val.list (rs.map encPerm) with hc
  set B : Val → ℕ := fun _ => 10 ^ 6 * (n + 1) ^ 8
  have hcw : c.wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hrl
  have hcsw : (radCsVal L).wt ≤ 100 * (n + 1) ^ 8 := SeriesVal.wt_le ⟨L, rfl, hLl, hl, rfl⟩
  have hstep : ∀ x ∈ xs, FunAll P ap (.list [c, x]) (fun w cost =>
      (∃ ys, x = .list ys ∧ w = .list (rs.map encPerm ++ ys)) ∧ cost ≤ B x) := by
    intro x hx
    obtain ⟨hs, hhs, rfl⟩ := List.mem_map.mp hx
    have hhsl : hs.length ≤ n ^ 2 := hl hs hhs
    have hx_wt : (Val.list (hs.map encPerm)).wt ≤ 13 * (n + 1) ^ 6 := wt_list_encPerms_le_sq hhsl
    have hw_wt : (Val.list (rs.map encPerm ++ hs.map encPerm)).wt ≤ 52 * (n + 1) ^ 6 := by
      rw [← List.map_append]
      exact outb_wt_list_encPerms_le_two_sq (by simp [List.length_append]; omega)
    refine (append_spec hap (rs.map encPerm) (hs.map encPerm)).mono fun w cost ⟨hw, hcost⟩ =>
      ⟨⟨hs.map encPerm, rfl, hw⟩, ?_⟩
    subst hw
    have h2 := wt_list2_le (.list (rs.map encPerm)) (.list (hs.map encPerm))
    have hcw' : (Val.list (rs.map encPerm)).wt ≤ 13 * (n + 1) ^ 6 := hcw
    have hlen : (hs.map encPerm).length ≤ (n + 1) ^ 6 := by
      simp only [List.length_map]
      have : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ n) 2
      exact (hhsl.trans this).trans (Nat.pow_le_pow_right (Nat.succ_pos n) (by decide))
    have h06 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow 6 (n + 1) (Nat.succ_pos n)
    have hcost' : cost ≤ loopModK * ((n + 1) ^ 2) * (150 * (n + 1) ^ 6) := by
      refine hcost.trans (Nat.mul_le_mul ?_ (by omega))
      refine Nat.mul_le_mul_left _ ?_
      simp only [List.length_map]
      have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have heq : loopModK * ((n + 1) ^ 2) * (150 * (n + 1) ^ 6) ≤ 10 ^ 6 * (n + 1) ^ 8 := by
      calc loopModK * ((n + 1) ^ 2) * (150 * (n + 1) ^ 6) = 150000 * (n + 1) ^ 8 := by
            simp only [loopModK]; ring
        _ ≤ 10 ^ 6 * (n + 1) ^ 8 := Nat.mul_le_mul_right _ (by decide)
    exact hcost'.trans heq
  refine (map_spec hmap hstep).mono fun w cost ⟨ws, hw, hrel, hcost⟩ => ?_
  have hweq := hw.trans (outb_forall2_map_append L ws hrel)
  refine ⟨hweq, ?_⟩
  rw [hweq] at hcost
  have hww : (socCsVal (L.map fun hs => rs ++ hs)).wt ≤ 200 * (n + 1) ^ 8 :=
    outb_wt_socCsVal_map_append hrl hLl hl
  have hsum : (xs.map B).sum = xs.length * (10 ^ 6 * (n + 1) ^ 8) := by
    simp [B]
  have hxl : xs.length ≤ 2 * (n + 1) ^ 2 := by
    simp only [xs, List.length_map]
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  have ha_wt := wt_list2_le c (radCsVal L)
  have h68 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := Nat.pow_le_pow_right (Nat.succ_pos n) (by decide)
  have h08 : 1 ≤ (n + 1) ^ 8 := Nat.one_le_pow 8 (n + 1) (Nat.succ_pos n)
  have h1 : (xs.map B).sum ≤ 2 * 10 ^ 6 * (n + 1) ^ 10 := by
    rw [hsum]
    calc xs.length * (10 ^ 6 * (n + 1) ^ 8)
        ≤ (2 * (n + 1) ^ 2) * (10 ^ 6 * (n + 1) ^ 8) := Nat.mul_le_mul_right _ hxl
      _ = 2 * 10 ^ 6 * (n + 1) ^ 10 := by ring
  have h2 : mapK * (xs.length + 1) * ((Val.list [c, .list xs]).wt +
      (socCsVal (L.map fun hs => rs ++ hs)).wt + 1) ≤
      3 * 10 ^ 6 * (n + 1) ^ 10 := by
    have hxl1 : xs.length + 1 ≤ 3 * (n + 1) ^ 2 := by
      have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n)
      omega
    have hwt_sum : (Val.list [c, .list xs]).wt +
        (socCsVal (L.map fun hs => rs ++ hs)).wt + 1 ≤ 500 * (n + 1) ^ 8 := by
      change (Val.list [c, radCsVal L]).wt + _ + 1 ≤ _
      omega
    calc mapK * (xs.length + 1) * ((Val.list [c, .list xs]).wt +
          (socCsVal (L.map fun hs => rs ++ hs)).wt + 1)
        ≤ (mapK * (3 * (n + 1) ^ 2)) * (500 * (n + 1) ^ 8) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hxl1) hwt_sum
      _ = 1500000 * (n + 1) ^ 10 := by simp only [mapK]; ring
      _ ≤ 3 * 10 ^ 6 * (n + 1) ^ 10 := Nat.mul_le_mul_right _ (by decide)
  omega

/-! ### Synthetic `Prim` for `gmpRepsCost` -/

/-- A synthetic `Prim` whose `boundSize` bounds `gmpRepsCost hm W q` at `W + q`. -/
noncomputable def gmpRepsPrim (hm : Membership) : Prim where
  Pre := fun _ => False
  Post := fun _ _ => True
  c := (gmpRepsCost_le hm).choose
  k := (gmpRepsCost_le hm).choose_spec.choose
  prog := (membershipPrim hm).prog
  spec := fun x => x.2.elim

theorem gmpRepsCost_le_boundSize (hm : Membership) (W q : ℕ) :
    gmpRepsCost hm W q ≤ (gmpRepsPrim hm).boundSize (W + q) :=
  (gmpRepsCost_le hm).choose_spec.choose_spec W q

/-! ### Entry point and module layout of `OutbRad` -/

/-- **The Stage 2 radical subgroup program** on `[encGroup σH, encGroup σN]`:
1. `.var 1 = .list (rs.map encPerm)` (`GensOf R`) via `f_rad` on `.var 0`
2. `.var 2 = encGroup rs'` via `mg` on `[n, .var 1]`
3. `.var 3 = radCsVal L` via `f_tc` on `[arg 0, .var 2]`
4. `.var 4 = socCsVal (L.map (rs ++ ·))` via `f_map` on `[.var 1, .var 3]`
5. `.var 5 = .list (es.map encPerm)` (`GensOf E_H`) via `f_soc` on `[arg 0, .var 2, .var 4]`
6. `.var 6 = encGroup es'` via `mg` on `[n, .var 5]`
7. `.var 7 = .list (ks.map encPerm)` (`GensOf K*_H`) via `f_rad` on `[arg 0, .var 6]`
8. `.var 8 = encGroup ks'` via `mg` on `[n, .var 7]`
9. `.var 9 = .list (reps.map encPerm)` via `f_reps` on `[.var 2, .var 5]`
10. returns `.call f_supp (mk4 (.var 8) (.var 6) (.var 2) (.var 9))`. -/
def outbRadEntry (f_rad mg f_tc f_map f_soc f_reps f_supp : ℕ) : Expr :=
  .letE (.call f_rad (.var 0))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
  (.letE (.call f_tc (mk2 (arg 0) (.var 2)))
  (.letE (.call f_map (mk2 (.var 1) (.var 3)))
  (.letE (.call f_soc (mk3 (arg 0) (.var 2) (.var 4)))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 5)))
  (.letE (.call f_rad (mk2 (arg 0) (.var 6)))
  (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 7)))
  (.letE (.call f_reps (mk2 (.var 2) (.var 5)))
    (.call f_supp (mk4 (.var 8) (.var 6) (.var 2) (.var 9)))))))))))

/-- The first 97 functions of T2 at base `b`. -/
def flRadHead (b jder jni jmem jpre : ℕ) : List Expr :=
  [radEntry (b + 2) (b + 97) jni, radStepBody (b + 5) (b + 8) (b + 15) jder jni (b + 20)] ++
  iterFuns (b + 2) (b + 1) ++ appendFuns (b + 5) ++ mkGroupFuns (b + 8) ++ leFuns (b + 15) jmem ++
  gmpFactorKernelFuns (b + 20) jmem jpre

theorem length_flRadHead (b jder jni jmem jpre : ℕ) :
    (flRadHead b jder jni jmem jpre).length = 97 := rfl

/-- **The code of T2** at base `b` (331 functions). -/
def flRadFuns (b jmb jpre jmem jnc jni jder : ℕ) : List Expr :=
  flRadHead b jder jni jmem jpre ++ tcChainFuns (b + 97) jmb jpre jmem jnc jni jder

theorem length_flRadFuns (b jmb jpre jmem jnc jni jder : ℕ) :
    (flRadFuns b jmb jpre jmem jnc jni jder).length = 331 := by
  rw [flRadFuns, List.length_append, length_flRadHead, length_tcChainFuns]

/-- **The layout of T2** from the position of `flRadFuns` and the primitive entries. -/
theorem flRadAt_of {P : Program} {b jmb jpre jmem jnc jni jder : ℕ}
    {hmb : MinimalBlocks} {hpre : Preimage} {hmem : Membership}
    {hnc : NormalClosure} {hni : NormalizedIntersection} {hder : DerivedSubgroup}
    (h : P.HasAt b (flRadFuns b jmb jpre jmem jnc jni jder))
    (pmb : P.prims[jmb]? = some (minimalBlocksPrim hmb))
    (pp : P.prims[jpre]? = some (preimagePrim hpre))
    (pm : P.prims[jmem]? = some (membershipPrim hmem))
    (pnc : P.prims[jnc]? = some (normalClosurePrim hnc))
    (pi : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (pd : P.prims[jder]? = some (derivedSubgroupPrim hder)) :
    RadAt P b (b + 2) (b + 1) (b + 5) (b + 8) (b + 15) (b + 97) (b + 20)
      jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder := by
  unfold flRadFuns at h
  have h1 : P.HasAt b (flRadHead b jder jni jmem jpre) := h.left
  have h2 : P.HasAt (b + 97) (tcChainFuns (b + 97) jmb jpre jmem jnc jni jder) := by
    have hr := h.right
    rwa [length_flRadHead] at hr
  exact
  { entry := by simpa using (h1.block (gs := [radEntry (b + 2) (b + 97) jni]) 0 rfl).single
    iter := h1.block 2 rfl
    step :=
      { step := (h1.block (gs := [radStepBody (b + 5) (b + 8) (b + 15) jder jni (b + 20)]) 1 rfl).single
        ap := h1.block 5 rfl
        mg := h1.block 8 rfl
        le := h1.block 15 rfl
        fk := gmpFactorKernelAt_of (h1.block 20 rfl) pm pp
        jd := pd
        ji := pi
        jm := pm }
    tc := tcChainAt_of h2 pmb pp pm pnc pi pd }

/-- Standard bundle for `SocPreAt` at base `b`. -/
abbrev SocPreBundleAt (P : Program) (b jni jm jpre : ℕ)
    (hni : NormalizedIntersection) (hmem : Membership) (hpre : Preimage) : Prop :=
  SocPreAt P b (b + 5) (b + 1) (b + 2) (b + 8) (b + 3) (b + 4) (b + 11) (b + 18) (b + 23)
    jni jm jpre hni hmem hpre

/-- Standard bundle for `OutbSuppAt` at base `b`. -/
abbrev OutbSuppBundleAt (P : Program) (b jni jnc jord jm : ℕ)
    (hni : NormalizedIntersection) (hnc : NormalClosure) (hord : GroupOrder)
    (hmem : Membership) : Prop :=
  OutbSuppAt P b (b + 12) (b + 1) (b + 2) (b + 18) jni (b + 3) (b + 25) (b + 4) (b + 5)
    (b + 6) (b + 33) (b + 7) (b + 36) (b + 8) (b + 28) jnc jord jm (b + 15) (b + 9)
    (b + 39) (b + 10) (b + 42) (b + 46) (b + 58) (b + 11) (b + 28)
    hni hnc hord hmem

/-- Standard bundle for `RadAt` at base `b`. -/
abbrev FlRadBundleAt (P : Program) (b jmb jpre jmem jnc jni jder : ℕ)
    (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup) : Prop :=
  RadAt P b (b + 2) (b + 1) (b + 5) (b + 8) (b + 15) (b + 97) (b + 20)
    jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder

/-- Where the complete `OutbRad` program sits at base `b`. -/
structure OutbRadAt (P : Program) (b jmb jpre jmem jnc jni jder jord : ℕ)
    (hmb : MinimalBlocks) (hpre : Preimage) (hmem : Membership)
    (hnc : NormalClosure) (hni : NormalizedIntersection) (hder : DerivedSubgroup)
    (hord : GroupOrder) : Prop where
  entry : P.funs[b]? = some
    (outbRadEntry (b + 4) (b + 12) (b + 101) (b + 1) (b + 335) (b + 25) (b + 435))
  map : P.HasAt (b + 1) (mapFuns (b + 1) (b + 9))
  rad : FlRadBundleAt P (b + 4) jmb jpre jmem jnc jni jder hmb hpre hmem hnc hni hder
  soc : SocPreBundleAt P (b + 335) jni jmem jpre hni hmem hpre
  supp : OutbSuppBundleAt P (b + 435) jni jnc jord jmem hni hnc hord hmem

/-- **The complete function block of `OutbRad`** at base `b` (496 functions). -/
def outbRadFuns (b jmb jpre jmem jnc jni jder jord : ℕ) : List Expr :=
  [outbRadEntry (b + 4) (b + 12) (b + 101) (b + 1) (b + 335) (b + 25) (b + 435)] ++
  mapFuns (b + 1) (b + 9) ++
  flRadFuns (b + 4) jmb jpre jmem jnc jni jder ++
  socPreFuns (b + 335) jni jmem jpre ++
  outbSuppFuns (b + 435) jni jnc jord jmem

theorem length_outbRadFuns (b jmb jpre jmem jnc jni jder jord : ℕ) :
    (outbRadFuns b jmb jpre jmem jnc jni jder jord).length = 496 := by
  simp only [outbRadFuns, List.length_append, length_flRadFuns, length_socPreFuns,
    length_outbSuppFuns]
  rfl

/-- **The layout `OutbRadAt`** from `P.HasAt b (outbRadFuns b ...)`. -/
theorem outbRadAt_of {P : Program} {b jmb jpre jmem jnc jni jder jord : ℕ}
    {hmb : MinimalBlocks} {hpre : Preimage} {hmem : Membership}
    {hnc : NormalClosure} {hni : NormalizedIntersection} {hder : DerivedSubgroup}
    {hord : GroupOrder}
    (h : P.HasAt b (outbRadFuns b jmb jpre jmem jnc jni jder jord))
    (pmb : P.prims[jmb]? = some (minimalBlocksPrim hmb))
    (pp : P.prims[jpre]? = some (preimagePrim hpre))
    (pm : P.prims[jmem]? = some (membershipPrim hmem))
    (pnc : P.prims[jnc]? = some (normalClosurePrim hnc))
    (pi : P.prims[jni]? = some (normalizedIntersectionPrim hni))
    (pd : P.prims[jder]? = some (derivedSubgroupPrim hder))
    (pord : P.prims[jord]? = some (groupOrderPrim hord)) :
    OutbRadAt P b jmb jpre jmem jnc jni jder jord hmb hpre hmem hnc hni hder hord := by
  have hhead : P.HasAt b ([outbRadEntry (b + 4) (b + 12) (b + 101) (b + 1) (b + 335) (b + 25)
      (b + 435)] ++ mapFuns (b + 1) (b + 9)) := h.left.left.left
  have hrad : P.HasAt (b + 4) (flRadFuns (b + 4) jmb jpre jmem jnc jni jder) := by
    have hr := h.left.left.right
    rwa [show ([outbRadEntry (b + 4) (b + 12) (b + 101) (b + 1) (b + 335) (b + 25) (b + 435)] ++
      mapFuns (b + 1) (b + 9)).length = 4 from rfl] at hr
  have hsoc : P.HasAt (b + 335) (socPreFuns (b + 335) jni jmem jpre) := by
    have hr := h.left.right
    have hl : ([outbRadEntry (b + 4) (b + 12) (b + 101) (b + 1) (b + 335) (b + 25) (b + 435)] ++
      mapFuns (b + 1) (b + 9) ++ flRadFuns (b + 4) jmb jpre jmem jnc jni jder).length = 335 := by
      rw [List.length_append, length_flRadFuns]; rfl
    rwa [hl] at hr
  have hsupp : P.HasAt (b + 435) (outbSuppFuns (b + 435) jni jnc jord jmem) := by
    have hr := h.right
    have hl : ([outbRadEntry (b + 4) (b + 12) (b + 101) (b + 1) (b + 335) (b + 25) (b + 435)] ++
      mapFuns (b + 1) (b + 9) ++ flRadFuns (b + 4) jmb jpre jmem jnc jni jder ++
      socPreFuns (b + 335) jni jmem jpre).length = 435 := by
      rw [List.length_append, List.length_append, length_flRadFuns, length_socPreFuns]; rfl
    rwa [hl] at hr
  exact
  { entry := by
      rw [← Nat.add_zero b]
      exact (hhead.block (gs := [outbRadEntry (b + 4) (b + 12) (b + 101) (b + 1) (b + 335) (b + 25)
        (b + 435)]) 0 rfl).single
    map := hhead.block 1 rfl
    rad := flRadAt_of hrad pmb pp pm pnc pi pd
    soc := socPreAt_of hsoc pi pm pp
    supp := outbSuppAt_of hsupp pi pnc pord pm }

/-! ### Polynomial cost bound and specification of `OutbRad` -/

/-- The exponent of `T + 1` in the polynomial bound of `OutbRad`. -/
def outbRadD (pc pd pq pi pm pr pnc pord : Prim) : ℕ :=
  16 + 6 * pc.k + 6 * pr.k + 6 * radD pc pd pq pi pm +
    8 * socPreD pi pm pq + 6 * outbSuppD pi pnc pord pm

/-- The constant of the polynomial bound of `OutbRad`. -/
def outbRadK (pc pd pq pi pm pr pnc pord : Prim) : ℕ :=
  radK pc pd pq pi pm + pc.c * 802 ^ pc.k +
    3 * socPreK pi pm pq * 1202 ^ socPreD pi pm pq +
    radK pc pd pq pi pm * 801 ^ radD pc pd pq pi pm +
    pr.c * 802 ^ pr.k +
    outbSuppK pi pnc pord pm * 2001 ^ outbSuppD pi pnc pord pm + 10 ^ 10

private theorem outbRad_step1_le (pc pd pq pi pm pr pnc pord : Prim) (T : ℕ) :
    radCost pc pd pq pi pm T ≤
      radK pc pd pq pi pm * (T + 1) ^ outbRadD pc pd pq pi pm pr pnc pord := by
  refine (radCost_le pc pd pq pi pm T).trans (Nat.mul_le_mul_left _ ?_)
  exact rad_pow_le (Nat.succ_pos T) (by simp only [outbRadD]; omega)

private theorem outbRad_step3_le (pc pd pq pi pm pr pnc pord : Prim) {B T : ℕ}
    (hB : B ≤ 800 * (T + 1) ^ 6) :
    pc.boundSize B ≤
      pc.c * 802 ^ pc.k * (T + 1) ^ outbRadD pc pd pq pi pm pr pnc pord := by
  have h1 := rad_bS_le pc (Nat.succ_pos T) hB
  refine h1.trans (Nat.mul_le_mul_left _ ?_)
  exact rad_pow_le (Nat.succ_pos T) (by simp only [outbRadD]; omega)

private theorem outbRad_step5_le (pc pd pq pi pm pr pnc pord : Prim) {T_soc L q T : ℕ}
    (hTsoc : T_soc ≤ 1200 * (T + 1) ^ 8) (hL : L ≤ 2 * (T + 1) ^ 2) (hq : q ≤ T) :
    socPreCost pi pm pq T_soc L q ≤
      (3 * socPreK pi pm pq * 1202 ^ socPreD pi pm pq) *
        (T + 1) ^ outbRadD pc pd pq pi pm pr pnc pord := by
  set X := T + 1 with hXdef
  have hX : 1 ≤ X := Nat.succ_pos T
  have hX8 : 1 ≤ X ^ 8 := Nat.one_le_pow 8 X hX
  have hX2 : 1 ≤ X ^ 2 := Nat.one_le_pow 2 X hX
  have h18 : X ≤ X ^ 8 := Nat.le_self_pow (by decide) X
  have hL1 : L + 1 ≤ 3 * X ^ 2 := by omega
  have hTq1 : T_soc + q + 1 ≤ 1202 * X ^ 8 := by omega
  set Ds := socPreD pi pm pq
  set Ks := socPreK pi pm pq
  have hpow : (T_soc + q + 1) ^ Ds ≤ 1202 ^ Ds * X ^ (8 * Ds) := by
    calc (T_soc + q + 1) ^ Ds ≤ (1202 * X ^ 8) ^ Ds := Nat.pow_le_pow_left hTq1 Ds
      _ = 1202 ^ Ds * X ^ (8 * Ds) := by rw [mul_pow, ← pow_mul]
  have h0 := socPreCost_le pi pm pq T_soc L q
  have h1 : Ks * ((L + 1) * (T_soc + q + 1) ^ Ds) ≤
      (3 * Ks * 1202 ^ Ds) * X ^ (2 + 8 * Ds) := by
    calc Ks * ((L + 1) * (T_soc + q + 1) ^ Ds)
        ≤ Ks * ((3 * X ^ 2) * (1202 ^ Ds * X ^ (8 * Ds))) :=
          Nat.mul_le_mul_left Ks (Nat.mul_le_mul hL1 hpow)
      _ = (3 * Ks * 1202 ^ Ds) * (X ^ 2 * X ^ (8 * Ds)) := by ring
      _ = (3 * Ks * 1202 ^ Ds) * X ^ (2 + 8 * Ds) := by rw [← pow_add]
  refine h0.trans (h1.trans (Nat.mul_le_mul_left _ ?_))
  exact rad_pow_le hX (by simp only [outbRadD, Ds]; omega)

private theorem outbRad_step7_le (pc pd pq pi pm pr pnc pord : Prim) {T2 T : ℕ}
    (hT2 : T2 ≤ 800 * (T + 1) ^ 6) :
    radCost pc pd pq pi pm T2 ≤
      (radK pc pd pq pi pm * 801 ^ radD pc pd pq pi pm) *
        (T + 1) ^ outbRadD pc pd pq pi pm pr pnc pord := by
  set X := T + 1
  have hX : 1 ≤ X := Nat.succ_pos T
  have hX6 : 1 ≤ X ^ 6 := Nat.one_le_pow 6 X hX
  have hT2' : T2 + 1 ≤ 801 * X ^ 6 := by omega
  set Dr := radD pc pd pq pi pm
  set Kr := radK pc pd pq pi pm
  have h0 := radCost_le pc pd pq pi pm T2
  have h1 : Kr * (T2 + 1) ^ Dr ≤ (Kr * 801 ^ Dr) * X ^ (6 * Dr) := by
    calc Kr * (T2 + 1) ^ Dr ≤ Kr * (801 * X ^ 6) ^ Dr :=
          Nat.mul_le_mul_left Kr (Nat.pow_le_pow_left hT2' Dr)
      _ = (Kr * 801 ^ Dr) * X ^ (6 * Dr) := by rw [mul_pow, ← pow_mul]; ring
  refine h0.trans (h1.trans (Nat.mul_le_mul_left _ ?_))
  exact rad_pow_le hX (by simp only [outbRadD, Dr]; omega)

private theorem outbRad_step9_le (pc pd pq pi pm pr pnc pord : Prim) {B T : ℕ}
    (hB : B ≤ 800 * (T + 1) ^ 6) :
    pr.boundSize B ≤
      pr.c * 802 ^ pr.k * (T + 1) ^ outbRadD pc pd pq pi pm pr pnc pord := by
  have h1 := rad_bS_le pr (Nat.succ_pos T) hB
  refine h1.trans (Nat.mul_le_mul_left _ ?_)
  exact rad_pow_le (Nat.succ_pos T) (by simp only [outbRadD]; omega)

private theorem outbRad_step10_le (pc pd pq pi pm pr pnc pord : Prim) {n m T_supp T : ℕ}
    (hn : n ≤ T_supp) (hm : m ≤ T) (hTs : T_supp ≤ 2000 * (T + 1) ^ 6) :
    outbSuppCost pi pnc pord pm n m T_supp ≤
      (outbSuppK pi pnc pord pm * 2001 ^ outbSuppD pi pnc pord pm) *
        (T + 1) ^ outbRadD pc pd pq pi pm pr pnc pord := by
  set X := T + 1
  have hX : 1 ≤ X := Nat.succ_pos T
  have hX6 : 1 ≤ X ^ 6 := Nat.one_le_pow 6 X hX
  have hm1 : m + 1 ≤ X := Nat.succ_le_succ hm
  have hTs1 : T_supp + 1 ≤ 2001 * X ^ 6 := by omega
  set Dp := outbSuppD pi pnc pord pm
  set Kp := outbSuppK pi pnc pord pm
  have h0 := outbSuppCost_le pi pnc pord pm hn (m := m)
  have h1 : Kp * ((m + 1) ^ 3 * (T_supp + 1) ^ Dp) ≤
      (Kp * 2001 ^ Dp) * X ^ (3 + 6 * Dp) := by
    calc Kp * ((m + 1) ^ 3 * (T_supp + 1) ^ Dp)
        ≤ Kp * (X ^ 3 * (2001 * X ^ 6) ^ Dp) :=
          Nat.mul_le_mul_left Kp (Nat.mul_le_mul (Nat.pow_le_pow_left hm1 3)
            (Nat.pow_le_pow_left hTs1 Dp))
      _ = (Kp * 2001 ^ Dp) * (X ^ 3 * X ^ (6 * Dp)) := by rw [mul_pow, ← pow_mul]; ring
      _ = (Kp * 2001 ^ Dp) * X ^ (3 + 6 * Dp) := by rw [← pow_add]
  refine h0.trans (h1.trans (Nat.mul_le_mul_left _ ?_))
  exact rad_pow_le hX (by simp only [outbRadD, Dp]; omega)

set_option maxHeartbeats 800000 in
/-- **Specification of `outbRadEntry` (Lemma A.21′ program)**: on `[encGroup gs, encGroup ns]`
with `gens ns ≤ gens gs` normalized by `gens gs` and `gens ns` transitive on `Fin n`, outputs `u`
generating a subgroup `R'` with `gens ns ≤ R' ≤ gens gs`, `R' / gens ns` solvable, and
`((R'.subgroupOf (gens gs))).index ≤ bFac ((gens gs) ⧸ (gens ns).subgroupOf (gens gs)) ^ 2`,
in time polynomial in `(Val.list [encGroup gs, encGroup ns]).wt + radQ n`. -/
theorem outbRad_spec (hMa : MarotiPrimitive) {hmb : MinimalBlocks} {hpre : Preimage}
    {hmem : Membership} {hnc : NormalClosure} {hni : NormalizedIntersection}
    {hder : DerivedSubgroup} {hord : GroupOrder}
    {P : Program} {b jmb jpre jmem jnc jni jder jord : ℕ}
    (hP : OutbRadAt P b jmb jpre jmem jnc jni jder jord hmb hpre hmem hnc hni hder hord)
    (gs ns : List (Perm (Fin n))) (hNH : gens ns ≤ gens gs)
    (hn : GI.Multicoset.Normalizes (gens gs) (gens ns))
    [htr : MulAction.IsPretransitive (gens ns) (Fin n)] :
    FunAll P b (.list [encGroup gs, encGroup ns]) (fun u cost =>
      ∃ R' : Subgroup (Perm (Fin n)),
        GensOf R' u ∧ R' ≤ gens gs ∧ gens ns ≤ R' ∧
        (∃ ℓ, GI.Multicoset.relDerived R' (gens ns) ℓ ≤ gens ns) ∧
        (∀ [((gens ns).subgroupOf (gens gs)).Normal],
          (R'.subgroupOf (gens gs)).index ≤
            bFac ((gens gs) ⧸ (gens ns).subgroupOf (gens gs)) ^ 2) ∧
        cost ≤ outbRadK (tcChainPrim hmb hpre hmem hnc hni hder) (derivedSubgroupPrim hder)
          (gmpFactorKernelPrim hmem hpre) (normalizedIntersectionPrim hni) (membershipPrim hmem)
          (gmpRepsPrim hmem) (normalClosurePrim hnc) (groupOrderPrim hord) *
          ((Val.list [encGroup gs, encGroup ns]).wt + radQ n + 1) ^
            outbRadD (tcChainPrim hmb hpre hmem hnc hni hder) (derivedSubgroupPrim hder)
              (gmpFactorKernelPrim hmem hpre) (normalizedIntersectionPrim hni) (membershipPrim hmem)
              (gmpRepsPrim hmem) (normalClosurePrim hnc) (groupOrderPrim hord)) := by
  set in_v := Val.list [encGroup gs, encGroup ns] with hin_v
  set T := in_v.wt + radQ n with hT
  set X := T + 1 with hXdef
  set pc := tcChainPrim hmb hpre hmem hnc hni hder
  set pd := derivedSubgroupPrim hder
  set pq := gmpFactorKernelPrim hmem hpre
  set pi := normalizedIntersectionPrim hni
  set pm := membershipPrim hmem
  set pr := gmpRepsPrim hmem
  set pnc := normalClosurePrim hnc
  set pord := groupOrderPrim hord
  set D := outbRadD pc pd pq pi pm pr pnc pord with hD
  have hX : 1 ≤ X := Nat.succ_pos T
  have hTX : T < X := Nat.lt_succ_self T
  have hgT : (encGroup gs).wt < T := (wt_le_wt_list (by simp)).trans_le (Nat.le_add_right _ _)
  have hnT : (encGroup ns).wt < T := (wt_le_wt_list (by simp)).trans_le (Nat.le_add_right _ _)
  have hnW : n + 1 ≤ T := by
    have := S_le_wt_encGroup gs
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hqT : radQ n ≤ T := Nat.le_add_left _ _
  have hin_T : in_v.wt ≤ T := Nat.le_add_right _ _
  have hnX : n + 1 ≤ X := by omega
  have hnX2 : (n + 1) ^ 2 ≤ X ^ 6 :=
    (Nat.pow_le_pow_left hnX 2).trans (rad_pow_le hX (by decide))
  have hnX6 : (n + 1) ^ 6 ≤ X ^ 6 := Nat.pow_le_pow_left hnX 6
  have hnX8 : (n + 1) ^ 8 ≤ X ^ 8 := Nat.pow_le_pow_left hnX 8
  have hnX9 : (n + 1) ^ 9 ≤ X ^ 9 := Nat.pow_le_pow_left hnX 9
  have hnX10 : (n + 1) ^ 10 ≤ X ^ 10 := Nat.pow_le_pow_left hnX 10
  have hX16 : X ≤ X ^ 6 := Nat.le_self_pow (by decide) X
  have hTX6 : T < X ^ 6 := hTX.trans_le hX16
  have hgX6 : (encGroup gs).wt < X ^ 6 := hgT.trans hTX6
  have hqX6 : radQ n < X ^ 6 := hqT.trans_lt hTX6
  have hin_X6 : in_v.wt < X ^ 6 := hin_T.trans_lt hTX6
  have hX68 : X ^ 6 ≤ X ^ 8 := rad_pow_le hX (by decide)
  have hX810 : X ^ 8 ≤ X ^ 10 := rad_pow_le hX (by decide)
  have hX910 : X ^ 9 ≤ X ^ 10 := rad_pow_le hX (by decide)
  have hX1016 : X ^ 10 ≤ X ^ 16 := rad_pow_le hX (by decide)
  have hX16D : X ^ 16 ≤ X ^ D := rad_pow_le hX (by simp only [hD, outbRadD]; omega)
  have hX6_pos : 1 ≤ X ^ 6 := Nat.one_le_pow 6 X hX
  have hnw : (Val.nat n).wt ≤ 2 * X ^ 6 := (wt_nat_le n).trans (by omega)
  have h0w := wt_nat_le 0
  have hmk_X9 : 8 * mkGroupK * (n + 1) ^ 9 ≤ 10 ^ 6 * X ^ 9 := by
    simp only [mkGroupK]; clear * - hnX9; omega
  have : ((gens ns).subgroupOf (gens gs)).Normal := GI.Multicoset.normal_of_normalizes hn
  obtain ⟨hR0H, hNR0, -⟩ := GI.Multicoset.radicalPreimage_spec hNH hn
  -- step 1: `v1 = .call (b + 4) (.var 0)` (`rad_spec` on `[encGroup gs, encGroup ns]`)
  have dinp := Det.var' (P := P) (env := [in_v]) (i := 0) (v := in_v) rfl
  refine FunAll.intro hP.entry (EvalAll.letE
    (Ra := fun v1 c1 => GensOf (GI.Multicoset.radicalPreimage (gens gs) (gens ns)) v1 ∧
      c1 ≤ radK pc pd pq pi pm * X ^ D + 20 * X ^ 6)
    (EvalAll.call_funAll dinp fun v ca hv => ?_) fun v1 c1 h1 => ?_)
  · obtain ⟨rfl, hca⟩ := hv
    refine (rad_spec hMa hP.rad gs ns hNH hn).mono fun v1 cb ⟨hv1, hcb⟩ => ⟨hv1, ?_⟩
    have hb1 : cb ≤ radK pc pd pq pi pm * X ^ D :=
      hcb.trans (outbRad_step1_le pc pd pq pi pm pr pnc pord T)
    have hw1 : v1.wt ≤ 13 * X ^ 6 := (outb_wt_of_gensOf hv1).trans (by omega)
    clear * - hca hb1 hw1 hin_X6 hX6_pos
    omega
  clear dinp
  obtain ⟨⟨rs, rfl, hrl, hrs⟩, hc1⟩ := h1
  have hrw : (outbSv rs).wt ≤ 13 * X ^ 6 := (wt_list_encPerms_le_sq hrl).trans (by omega)
  -- step 2: `v2 = encGroup rs'` via `mg`
  have dn1 := Det.get' (Det.arg' (P := P) (vs := [encGroup gs, encGroup ns])
    (rest := [outbSv rs]) (j := 0) (v := encGroup gs) rfl) (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn1
  have dv1 := Det.var' (P := P) (env := [in_v, outbSv rs]) (i := 1) (v := outbSv rs) rfl
  obtain ⟨rs', hrl', hrs', d2, hRw⟩ := outb_mk_det hP.rad.step.mg dn1 dv1
    (⟨rs, rfl, hrl, rfl⟩ : GensVal n (outbSv rs) (gens rs))
  rw [hrs] at hrs'
  clear dn1 dv1
  refine EvalAll.letE d2 fun v2 c2 h2 => ?_
  obtain ⟨rfl, hc2⟩ := h2
  clear d2
  have hRw_X6 : (encGroup rs').wt ≤ 320 * X ^ 6 := by clear * - hRw hnX6; omega
  have hnr_w := wt_list2_le (.nat n) (outbSv rs)
  -- step 3: `v3 = .call (b + 101) (mk2 (arg 0) (.var 2))` (`tcChain_spec` on `[encGroup gs, encGroup rs']`)
  have hRH' : gens rs' ≤ gens gs := hrs'.symm ▸ hR0H
  have hnR' : GI.Multicoset.Normalizes (gens gs) (gens rs') := by
    rw [hrs']; exact GI.Multicoset.normalizes_of_normal hR0H
  have hNR' : gens ns ≤ gens rs' := hrs'.symm ▸ hNR0
  have : MulAction.IsPretransitive (gens rs') (Fin n) := outb_isPretransitive_of_le hNR'
  set env2 := [in_v, outbSv rs, encGroup rs']
  have dgs2 := Det.arg' (P := P) (vs := [encGroup gs, encGroup ns])
    (rest := [outbSv rs, encGroup rs']) (j := 0) (v := encGroup gs) rfl
  rw [← hin_v] at dgs2
  have drs2 := Det.var' (P := P) (env := env2) (i := 2) (v := encGroup rs') rfl
  have dtc_arg := Det.mk2 dgs2 drs2
  have htc_wt0 := wt_list2_le (encGroup gs) (encGroup rs')
  have htc_wt : (Val.list [encGroup gs, encGroup rs']).wt ≤ 700 * X ^ 6 := by
    clear * - htc_wt0 hgX6 hRw_X6 hX6_pos; omega
  have hn_tc : n ≤ (Val.list [encGroup gs, encGroup rs']).wt := by
    have := S_le_wt_encGroup gs
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have : (encGroup gs).wt < (Val.list [encGroup gs, encGroup rs']).wt := wt_le_wt_list (by simp)
    omega
  refine EvalAll.letE
    (Ra := fun v3 c3 => (∃ Hs, SeriesVal n v3 Hs ∧ IsNonabelianChiefChain (gens gs) (gens rs') Hs) ∧
      c3 ≤ pc.c * 802 ^ pc.k * X ^ D + 2000 * X ^ 8)
    (EvalAll.call_funAll dtc_arg fun v ca hv => ?_) fun v3 c3 h3 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (tcChain_spec hMa hP.rad.tc gs rs' hRH' hnR' (fun _ => inferInstance)).mono
      fun v3 cb ⟨⟨Hs, hSv, hs⟩, hcb⟩ => ⟨⟨Hs, hSv, hs⟩, ?_⟩
    have hb0 : cb ≤ pc.boundSize ((Val.list [encGroup gs, encGroup rs']).wt + radQ n) :=
      hcb.trans (tcChainCost_le_boundSize hmb hpre hmem hnc hni hder hn_tc)
    have htc_B : (Val.list [encGroup gs, encGroup rs']).wt + radQ n ≤ 800 * (T + 1) ^ 6 := by
      rw [← hXdef]; clear * - htc_wt hqX6 hX6_pos; omega
    have hb1 : cb ≤ pc.c * 802 ^ pc.k * X ^ D :=
      hb0.trans (outbRad_step3_le pc pd pq pi pm pr pnc pord htc_B)
    have hw3 : v3.wt ≤ 100 * X ^ 8 := (SeriesVal.wt_le hSv).trans (by omega)
    clear * - hca hb1 hw3 hin_X6 hgX6 hRw_X6 htc_wt hX68 hX6_pos
    omega
  clear dgs2 drs2 dtc_arg
  obtain ⟨⟨Hs, ⟨L, rfl, hLl, hl, rfl⟩, hs⟩, hc3⟩ := h3
  have hcsw : (radCsVal L).wt ≤ 100 * X ^ 8 :=
    (SeriesVal.wt_le ⟨L, rfl, hLl, hl, rfl⟩).trans (by omega)
  -- step 4: `v4 = .call (b + 1) (mk2 (.var 1) (.var 3))` (`outb_map_append_spec`)
  set env3 := [in_v, outbSv rs, encGroup rs', radCsVal L]
  have dv1_3 := Det.var' (P := P) (env := env3) (i := 1) (v := outbSv rs) rfl
  have dv3_3 := Det.var' (P := P) (env := env3) (i := 3) (v := radCsVal L) rfl
  have dmap_arg := Det.mk2 dv1_3 dv3_3
  have hmap_in_w := wt_list2_le (outbSv rs) (radCsVal L)
  set Ws := L.map fun hs => rs ++ hs with hWs
  have hWsw : (socCsVal Ws).wt ≤ 200 * X ^ 8 :=
    (outb_wt_socCsVal_map_append hrl hLl hl).trans (by omega)
  refine EvalAll.letE
    (Ra := fun v4 c4 => v4 = socCsVal Ws ∧ c4 ≤ 2 * 10 ^ 8 * X ^ 10)
    (EvalAll.call_funAll dmap_arg fun v ca hv => ?_) fun v4 c4 h4 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (outb_map_append_spec hP.map hP.rad.step.ap rs L hrl hLl hl).mono
      fun v4 cb ⟨hv4, hcb⟩ => ⟨hv4.trans (by rw [hWs]), ?_⟩
    rw [hv4, ← hWs]
    clear * - hca hcb hrw hcsw hmap_in_w hWsw hnX10 hX68 hX810 hX6_pos
    omega
  clear dv1_3 dv3_3 dmap_arg
  obtain ⟨rfl, hc4⟩ := h4
  -- step 5: `v5 = .call (b + 335) (mk3 (arg 0) (.var 2) (.var 4))` (`socPre_spec_of_radicalPreimage`)
  have hchain : SocChain (gens gs) (gens rs') (Ws.map gens) :=
    outb_socChain_of_map_append hRH' hnR' (hrs.trans hrs'.symm) hs
  have hq_idx : ((gens rs').subgroupOf (soclePreimage (gens gs) (gens rs'))).index ≤ radQ n :=
    outb_index_soclePreimage_le_radQ hNH hn hrs'
  set env4 := [in_v, outbSv rs, encGroup rs', radCsVal L, socCsVal Ws]
  have dgs4 := Det.arg' (P := P) (vs := [encGroup gs, encGroup ns])
    (rest := [outbSv rs, encGroup rs', radCsVal L, socCsVal Ws]) (j := 0) (v := encGroup gs) rfl
  rw [← hin_v] at dgs4
  have drs4 := Det.var' (P := P) (env := env4) (i := 2) (v := encGroup rs') rfl
  have dws4 := Det.var' (P := P) (env := env4) (i := 4) (v := socCsVal Ws) rfl
  have dsoc_arg := Det.mk3 dgs4 drs4 dws4
  have hsoc_wt0 := wt_list3_le (encGroup gs) (encGroup rs') (socCsVal Ws)
  have hsoc_wt : (Val.list [encGroup gs, encGroup rs', socCsVal Ws]).wt ≤ 1200 * (T + 1) ^ 8 := by
    rw [← hXdef]; clear * - hsoc_wt0 hgX6 hRw_X6 hWsw hX68 hX6_pos; omega
  have hWsl_X2 : Ws.length ≤ 2 * (T + 1) ^ 2 := by
    rw [← hXdef]
    simp only [Ws, List.length_map]
    have : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hnX 2
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega
  refine EvalAll.letE
    (Ra := fun v5 c5 => GensOf (soclePreimage (gens gs) (gens rs')) v5 ∧
      c5 ≤ (3 * socPreK pi pm pq * 1202 ^ socPreD pi pm pq) * X ^ D + 5000 * X ^ 8)
    (EvalAll.call_funAll dsoc_arg fun v ca hv => ?_) fun v5 c5 h5 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (socPre_spec_of_radicalPreimage hP.soc gs rs' Ws hNH hn hrs' hchain hq_idx).mono
      fun v5 cb ⟨hv5, hcb⟩ => ⟨hv5, ?_⟩
    have hb5 : cb ≤ (3 * socPreK pi pm pq * 1202 ^ socPreD pi pm pq) * X ^ D :=
      hcb.trans (outbRad_step5_le pc pd pq pi pm pr pnc pord hsoc_wt hWsl_X2 hqT)
    have hw5 : v5.wt ≤ 13 * X ^ 6 := (outb_wt_of_gensOf hv5).trans (by omega)
    rw [← hXdef] at hsoc_wt
    clear * - hca hb5 hw5 hin_X6 hgX6 hRw_X6 hWsw hsoc_wt hX68 hX6_pos
    omega
  clear dgs4 drs4 dws4 dsoc_arg
  obtain ⟨⟨es, rfl, hel, hes⟩, hc5⟩ := h5
  have hew : (outbSv es).wt ≤ 13 * X ^ 6 := (wt_list_encPerms_le_sq hel).trans (by omega)
  -- step 6: `v6 = encGroup es'` via `mg`
  set env5 := [in_v, outbSv rs, encGroup rs', radCsVal L, socCsVal Ws, outbSv es]
  have dn5 := Det.get' (Det.arg' (P := P) (vs := [encGroup gs, encGroup ns])
    (rest := [outbSv rs, encGroup rs', radCsVal L, socCsVal Ws, outbSv es])
    (j := 0) (v := encGroup gs) rfl) (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn5
  have dv5 := Det.var' (P := P) (env := env5) (i := 5) (v := outbSv es) rfl
  obtain ⟨es', hel', hes', d6, hEw⟩ := outb_mk_det hP.rad.step.mg dn5 dv5
    (⟨es, rfl, hel, rfl⟩ : GensVal n (outbSv es) (gens es))
  rw [hes] at hes'
  clear dn5 dv5
  refine EvalAll.letE d6 fun v6 c6 h6 => ?_
  obtain ⟨rfl, hc6⟩ := h6
  clear d6
  have hEw_X6 : (encGroup es').wt ≤ 320 * X ^ 6 := by clear * - hEw hnX6; omega
  have hne_w := wt_list2_le (.nat n) (outbSv es)
  -- step 7: `v7 = .call (b + 4) (mk2 (arg 0) (.var 6))` (`rad_spec` on `[encGroup gs, encGroup es']`)
  have hRE' : gens rs' ≤ gens es' := by rw [hes']; exact le_soclePreimage hRH'
  have hEH' : gens es' ≤ gens gs := by rw [hes']; exact soclePreimage_le (gens gs) (gens rs')
  have : ((gens rs').subgroupOf (gens gs)).Normal := GI.Multicoset.normal_of_normalizes hnR'
  have hnE' : GI.Multicoset.Normalizes (gens gs) (gens es') := by
    rw [hes']; exact GI.Multicoset.normalizes_of_normal (soclePreimage_le (gens gs) (gens rs'))
  have : MulAction.IsPretransitive (gens es') (Fin n) := outb_isPretransitive_of_le hRE'
  set env6 := [in_v, outbSv rs, encGroup rs', radCsVal L, socCsVal Ws, outbSv es, encGroup es']
  have dgs6 := Det.arg' (P := P) (vs := [encGroup gs, encGroup ns])
    (rest := [outbSv rs, encGroup rs', radCsVal L, socCsVal Ws, outbSv es, encGroup es'])
    (j := 0) (v := encGroup gs) rfl
  rw [← hin_v] at dgs6
  have des6 := Det.var' (P := P) (env := env6) (i := 6) (v := encGroup es') rfl
  have drad2_arg := Det.mk2 dgs6 des6
  have hrad2_wt0 := wt_list2_le (encGroup gs) (encGroup es')
  have hrad2_T : (Val.list [encGroup gs, encGroup es']).wt + radQ n ≤ 800 * (T + 1) ^ 6 := by
    rw [← hXdef]; clear * - hrad2_wt0 hgX6 hEw_X6 hqX6 hX6_pos; omega
  refine EvalAll.letE
    (Ra := fun v7 c7 => GensOf (GI.Multicoset.radicalPreimage (gens gs) (gens es')) v7 ∧
      c7 ≤ (radK pc pd pq pi pm * 801 ^ radD pc pd pq pi pm) * X ^ D + 2000 * X ^ 6)
    (EvalAll.call_funAll drad2_arg fun v ca hv => ?_) fun v7 c7 h7 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (rad_spec hMa hP.rad gs es' hEH' hnE').mono fun v7 cb ⟨hv7, hcb⟩ => ⟨hv7, ?_⟩
    have hb7 : cb ≤ (radK pc pd pq pi pm * 801 ^ radD pc pd pq pi pm) * X ^ D :=
      hcb.trans (outbRad_step7_le pc pd pq pi pm pr pnc pord hrad2_T)
    have hw7 : v7.wt ≤ 13 * X ^ 6 := (outb_wt_of_gensOf hv7).trans (by omega)
    clear * - hca hb7 hw7 hin_X6 hgX6 hEw_X6 hrad2_wt0 hX6_pos
    omega
  clear dgs6 des6 drad2_arg
  obtain ⟨⟨ks, rfl, hkl, hks⟩, hc7⟩ := h7
  have hkw : (outbSv ks).wt ≤ 13 * X ^ 6 := (wt_list_encPerms_le_sq hkl).trans (by omega)
  -- step 8: `v8 = encGroup ks'` via `mg`
  set env7 := [in_v, outbSv rs, encGroup rs', radCsVal L, socCsVal Ws, outbSv es, encGroup es',
    outbSv ks]
  have dn7 := Det.get' (Det.arg' (P := P) (vs := [encGroup gs, encGroup ns])
    (rest := [outbSv rs, encGroup rs', radCsVal L, socCsVal Ws, outbSv es, encGroup es',
      outbSv ks])
    (j := 0) (v := encGroup gs) rfl) (Det.nat 0) (v := .nat n) rfl
  rw [← hin_v] at dn7
  have dv7 := Det.var' (P := P) (env := env7) (i := 7) (v := outbSv ks) rfl
  obtain ⟨ks', hkl', hks', d8, hKw⟩ := outb_mk_det hP.rad.step.mg dn7 dv7
    (⟨ks, rfl, hkl, rfl⟩ : GensVal n (outbSv ks) (gens ks))
  rw [hks] at hks'
  clear dn7 dv7
  refine EvalAll.letE d8 fun v8 c8 h8 => ?_
  obtain ⟨rfl, hc8⟩ := h8
  clear d8
  have hKw_X6 : (encGroup ks').wt ≤ 320 * X ^ 6 := by clear * - hKw hnX6; omega
  have hnk_w := wt_list2_le (.nat n) (outbSv ks)
  -- step 9: `v9 = .call (b + 25) (mk2 (.var 2) (.var 5))` (`gmpReps_spec` on `[encGroup rs', outbSv es]`)
  set env8 := [in_v, outbSv rs, encGroup rs', radCsVal L, socCsVal Ws, outbSv es, encGroup es',
    outbSv ks, encGroup ks']
  have drs8 := Det.var' (P := P) (env := env8) (i := 2) (v := encGroup rs') rfl
  have des8 := Det.var' (P := P) (env := env8) (i := 5) (v := outbSv es) rfl
  have dreps_arg := Det.mk2 drs8 des8
  have hreps_wt0 := wt_list2_le (encGroup rs') (outbSv es)
  have hidx_es : ((gens rs').subgroupOf (gens es)).index ≤ radQ n := by
    rw [hes]; exact hq_idx
  have hreps_Wq : (Val.list [encGroup rs', outbSv es]).wt +
      ((gens rs').subgroupOf (gens es)).index ≤ 800 * (T + 1) ^ 6 := by
    rw [← hXdef]; clear * - hreps_wt0 hRw_X6 hew hidx_es hqX6 hX6_pos; omega
  refine EvalAll.letE
    (Ra := fun v9 c9 => (∃ reps : List (Perm (Fin n)), v9 = .list (reps.map encPerm) ∧
      GmpCosetReps (gens es) (gens rs') reps) ∧
      c9 ≤ pr.c * 802 ^ pr.k * X ^ D + 2000 * X ^ 6)
    (EvalAll.call_funAll dreps_arg fun v ca hv => ?_) fun v9 c9 h9 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (gmpReps_spec hP.rad.step.fk.reps rs' es).mono fun v9 cb ⟨reps, hv9, hreps, hcb⟩ =>
      ⟨⟨reps, hv9, hreps⟩, ?_⟩
    subst hv9
    have hb0 := hcb.trans (gmpRepsCost_le_boundSize hmem _ _)
    have hb9 : cb ≤ pr.c * 802 ^ pr.k * X ^ D :=
      hb0.trans (outbRad_step9_le pc pd pq pi pm pr pnc pord hreps_Wq)
    have hrepl : reps.length ≤ T := by rw [hreps.length]; exact hidx_es.trans hqT
    have hw9 : (Val.list (reps.map encPerm)).wt ≤ 13 * X ^ 6 := by
      calc (Val.list (reps.map encPerm)).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 :=
            outb_wt_reps_le reps
        _ ≤ 13 * X ^ 2 * X ^ 2 :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left (by omega) 2))
              (Nat.pow_le_pow_left hnX 2)
        _ = 13 * X ^ 4 := by ring
        _ ≤ 13 * X ^ 6 := Nat.mul_le_mul_left 13 (rad_pow_le hX (by decide))
    clear * - hca hb9 hw9 hreps_wt0 hRw_X6 hew hX6_pos
    omega
  clear drs8 des8 dreps_arg
  obtain ⟨⟨reps, rfl, hreps⟩, hc9⟩ := h9
  have hrepl : reps.length ≤ T := by rw [hreps.length]; exact hidx_es.trans hqT
  have hrepw : (Val.list (reps.map encPerm)).wt ≤ 13 * X ^ 6 := by
    calc (Val.list (reps.map encPerm)).wt ≤ 13 * (reps.length + 1) ^ 2 * (n + 1) ^ 2 :=
          outb_wt_reps_le reps
      _ ≤ 13 * X ^ 2 * X ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left (by omega) 2))
            (Nat.pow_le_pow_left hnX 2)
      _ = 13 * X ^ 4 := by ring
      _ ≤ 13 * X ^ 6 := Nat.mul_le_mul_left 13 (rad_pow_le hX (by decide))
  -- step 10: `.call (b + 435) (mk4 (.var 8) (.var 6) (.var 2) (.var 9))` (`outbSupp_radical_free_order`)
  have hcov : ∀ x ∈ gens es', TmRpCov (gens rs') reps x := by
    rw [hes', ← hes]
    exact outb_tmRpCov_of_gmpCosetReps hreps
  have hK_eq : gens ks' = GI.Multicoset.radicalPreimage (gens gs)
      (soclePreimage (gens gs) (GI.Multicoset.radicalPreimage (gens gs) (gens ns))) := by
    rw [hks', hes', hrs']
  have hE_eq : gens es' =
      soclePreimage (gens gs) (GI.Multicoset.radicalPreimage (gens gs) (gens ns)) := by
    rw [hes', hrs']
  set env9 := env8 ++ [.list (reps.map encPerm)]
  have dks9 := Det.var' (P := P) (env := env9) (i := 8) (v := encGroup ks') rfl
  have des9 := Det.var' (P := P) (env := env9) (i := 6) (v := encGroup es') rfl
  have drs9 := Det.var' (P := P) (env := env9) (i := 2) (v := encGroup rs') rfl
  have drep9 := Det.var' (P := P) (env := env9) (i := 9) (v := .list (reps.map encPerm)) rfl
  have dsupp_arg := Det.mk4 dks9 des9 drs9 drep9
  have hsupp_in_w := wt_list4_le (encGroup ks') (encGroup es') (encGroup rs')
    (.list (reps.map encPerm))
  have hsupp_grp_w0 := wt_list3_le (encGroup ks') (encGroup es') (encGroup rs')
  have hsupp_grp_w : (Val.list [encGroup ks', encGroup es', encGroup rs']).wt ≤ 2000 * (T + 1) ^ 6 := by
    rw [← hXdef]; clear * - hsupp_grp_w0 hKw_X6 hEw_X6 hRw_X6 hX6_pos; omega
  have hn_supp : n ≤ (Val.list [encGroup ks', encGroup es', encGroup rs']).wt := by
    have := S_le_wt_encGroup ks'
    have : n + 1 ≤ (ks'.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have : (encGroup ks').wt < (Val.list [encGroup ks', encGroup es', encGroup rs']).wt :=
      wt_le_wt_list (by simp)
    omega
  refine EvalAll.call_funAll dsupp_arg fun v ca hv => ?_
  obtain ⟨rfl, hca⟩ := hv
  refine (outbSupp_radical_free_order hP.supp hNH ks' es' rs' reps hrs' hE_eq hK_eq hcov).mono
    fun u cb h => ?_
  obtain ⟨R', hR'u, hNR'_le, hR'H, _, hrel, _, hidx, hcb⟩ := h
  refine ⟨R', hR'u, hR'H, hNR'_le, hrel, hidx, ?_⟩
  have hb10 : cb ≤ (outbSuppK pi pnc pord pm * 2001 ^ outbSuppD pi pnc pord pm) * X ^ D :=
    hcb.trans (outbRad_step10_le pc pd pq pi pm pr pnc pord hn_supp hrepl hsupp_grp_w)
  have huw : u.wt ≤ 13 * X ^ 6 := (outb_wt_of_gensOf hR'u).trans (by omega)
  have hgoal : outbRadK pc pd pq pi pm pr pnc pord * X ^ D =
      radK pc pd pq pi pm * X ^ D + pc.c * 802 ^ pc.k * X ^ D +
        (3 * socPreK pi pm pq * 1202 ^ socPreD pi pm pq) * X ^ D +
        (radK pc pd pq pi pm * 801 ^ radD pc pd pq pi pm) * X ^ D +
        pr.c * 802 ^ pr.k * X ^ D +
        (outbSuppK pi pnc pord pm * 2001 ^ outbSuppD pi pnc pord pm) * X ^ D +
        10 ^ 10 * X ^ D := by
    unfold outbRadK
    ring
  rw [hgoal]
  have h10_D : 10 ^ 10 * X ^ 16 ≤ 10 ^ 10 * X ^ D := Nat.mul_le_mul_left _ hX16D
  have h6_16 : X ^ 6 ≤ X ^ 16 := hX68.trans (hX810.trans hX1016)
  have h8_16 : X ^ 8 ≤ X ^ 16 := hX810.trans hX1016
  have h9_16 : X ^ 9 ≤ X ^ 16 := hX910.trans hX1016
  clear * - hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hca hb10 huw
    hin_X6 hgX6 hnw h0w hmk_X9 hrw hRw_X6 hnr_w hew hEw_X6 hne_w hkw hKw_X6 hnk_w
    hrepw hsupp_in_w hnX6 h6_16 h8_16 h9_16 hX1016 h10_D hX6_pos
  omega

/-- **The Stage 2 radical subgroup program satisfies `Iface.TermRadSpec`.** -/
theorem outbRad_termRadSpec {hmb : MinimalBlocks} {hpre : Preimage}
    {hmem : Membership} {hnc : NormalClosure} {hni : NormalizedIntersection}
    {hder : DerivedSubgroup} {hord : GroupOrder}
    {P : Program} {b jmb jpre jmem jnc jni jder jord : ℕ}
    (hP : OutbRadAt P b jmb jpre jmem jnc jni jder jord hmb hpre hmem hnc hni hder hord) :
    Iface.TermRadSpec P
      (outbRadK (tcChainPrim hmb hpre hmem hnc hni hder) (derivedSubgroupPrim hder)
        (gmpFactorKernelPrim hmem hpre) (normalizedIntersectionPrim hni) (membershipPrim hmem)
        (gmpRepsPrim hmem) (normalClosurePrim hnc) (groupOrderPrim hord))
      (outbRadD (tcChainPrim hmb hpre hmem hnc hni hder) (derivedSubgroupPrim hder)
        (gmpFactorKernelPrim hmem hpre) (normalizedIntersectionPrim hni) (membershipPrim hmem)
        (gmpRepsPrim hmem) (normalClosurePrim hnc) (groupOrderPrim hord)) b := by
  intro m σH σN hNH hn htr
  refine (outbRad_spec GI.Cited.marotiPrimitive hP σH σN hNH hn).mono fun u cost h => ?_
  obtain ⟨R', hR'u, hR'H, hNR', hrel, hidx, hcost⟩ := h
  refine ⟨R', hR'u, hR'H, hNR', hrel, hidx, hcost.trans ?_⟩
  refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
  have := radQ_le_ceil_expLogSq m
  omega

end GI.Impl
