module

public import Workspace.Paper.RadicalFreeOrder
public import Workspace.SocPreMath
public import Workspace.OutbSuppMath

@[expose] public section

/-!
# Paper statements: computing `R'` and rebasing into `R'`

Appendix A, the paragraphs "Computing `R'`" and "Rebasing into `R'`" before Corollary A.22
(`cor:transitive-kernel-multicoset`), mathematical content:

* `GI.Paper.par_compute_socle`: the socle preimage `E_H` from the chain (first step);
* `GI.Paper.par_compute_descent`: the descent modulo `R` over the transversal (fourth step);
* `GI.Paper.par_compute_radical_subgroup`: the result `R' = S` has the form of Lemma A.21;
* `GI.Paper.par_rebase_subgroup`: the rebasing of the listed objects into `R'`.

The programs are `GI.Impl.socPre_spec` (`E_H`), `GI.Impl.outbSupp_spec` (the descent),
`GI.Impl.outbRad_termRadSpec` (all of `R'`, with its cost) and `GI.Impl.outbRebTabF`
(`Workspace/Impl/OutbReb.lean`, the rebasing).
-/

namespace GI.Paper

open GI.Cited GI.Composition GI.Multicoset

universe u

/-- **Computing `E_H`** (paragraph "Computing `R'`", first step), in the group `Q = H/R`, which
has no nontrivial solvable normal subgroup, with a chain `t` of normal subgroups whose
nonabelian factors are chief factors:
* if `I = t_j ∩ C ≠ 1` and `t_{j+1} ∩ C = 1` for a normal `C`, then `I` is a minimal normal
  subgroup ("We claim that `I/R` is a minimal normal subgroup of `H/R`");
* `I ∩ C_Q(I) = 1` for every normal `I` ("The intersection of `I/R` with its centralizer is the
  center of `I/R` ... so it is trivial");
* `C_Q(E I) = C_Q(E) ∩ C_Q(I)` (the update of `C`);
* if a normal `E ≤ soc(Q)` has `C_Q(E) = 1`, then `E = soc(Q)` ("At that point `E = E_H`"). -/
theorem par_compute_socle {Q : Type u} [Group Q] [Finite Q]
    (hrf : ∀ M : Subgroup Q, M.Normal → Group.IsSolvable M → M = ⊥)
    {L : ℕ} {t : ℕ → Subgroup Q} (ht : GI.Impl.SocQuotChain L t) :
    (∀ (C : Subgroup Q) [C.Normal] (j : ℕ), j < L → t j ⊓ C ≠ ⊥ → t (j + 1) ⊓ C = ⊥ →
      GI.RadicalSocle.MinimalNormal (t j ⊓ C)) ∧
    (∀ (I : Subgroup Q) [I.Normal], I ⊓ Subgroup.centralizer (I : Set Q) = ⊥) ∧
    (∀ E I : Subgroup Q, Subgroup.centralizer ((E ⊔ I : Subgroup Q) : Set Q) =
      Subgroup.centralizer (E : Set Q) ⊓ Subgroup.centralizer (I : Set Q)) ∧
    (∀ (E : Subgroup Q) [E.Normal], E ≤ GI.RadicalSocle.socle Q →
      Subgroup.centralizer (E : Set Q) = ⊥ → E = GI.RadicalSocle.socle Q) :=
  ⟨fun _ _ _ hj hI hnext => GI.Impl.soc_quot_minimalNormal hrf ht hj hI hnext,
    fun I _ => GI.Impl.soc_quot_inf_centralizer_eq_bot hrf I,
    GI.Impl.soc_quot_centralizer_sup,
    fun _ _ hE hC => GI.Impl.soc_quot_eq_socle_of_centralizer_eq_bot hE hC⟩

/-- **The descent modulo `R`** (paragraph "Computing `R'`", fourth step), for `R ≤ E_H ≤ K*_H`
in `Sym(n)` and a list `reps` with one element in each coset `R x`, `x ∈ E_H` (the
transversal):
* growing `P`: if `R ≤ P ≤ F ≤ E_H` and `P/R` is a `p`-subgroup of `F/R` that is not a
  Sylow subgroup, some `e ∈ reps` has `e ∈ F`, `e ∉ P` and `|⟨P, e⟩|` dividing `p^a |R|`;
* if every Sylow subgroup of `F/R` is normal (tested for the primes `p ≤ n`), then `F/R` is
  nilpotent;
* the correction: if `P/R` is a Sylow `p`-subgroup of `F/R` and `s` normalizes `F` and `R`,
  some `e ∈ reps` with `e ∈ F` makes `es` normalize `P`;
* one round: if `P` is not normalized by `F = S ∩ E_H` and every generator `s` of `S` is
  replaced by some `es` with `e ∈ F` that normalizes `P`, then `S' = ⟨R, es⟩` has
  `R ≤ S' ≤ S`, `S' E_H = K*_H`, and `2 |S' ∩ E_H| ≤ |S ∩ E_H|`;
* the end: if `(S ∩ E_H)/R` is nilpotent and `K*_H/E_H` is solvable, then `S/R` is
  solvable. -/
theorem par_compute_descent {n : ℕ} :
    (∀ {p : ℕ}, p.Prime → ∀ {R F E_H P : Subgroup (Equiv.Perm (Fin n))}
      [(R.subgroupOf F).Normal], F ≤ E_H → ∀ {reps : List (Equiv.Perm (Fin n))},
      (∀ x ∈ E_H, GI.Impl.TmRpCov R reps x) → R ≤ P → P ≤ F → ∀ {b : ℕ},
      Nat.card P = p ^ b * Nat.card R → b < (Nat.card F / Nat.card R).factorization p →
      ∃ e ∈ reps, e ∈ F ∧ e ∉ P ∧
        Nat.card (P ⊔ Subgroup.closure {e} : Subgroup (Equiv.Perm (Fin n))) ∣
          p ^ (Nat.card F / Nat.card R).factorization p * Nat.card R) ∧
    (∀ {R F : Subgroup (Equiv.Perm (Fin n))} [(R.subgroupOf F).Normal], R ≤ F →
      (∀ q, q.Prime → q ≤ n → q ∣ Nat.card F / Nat.card R →
        ∃ P, GI.Impl.OutbSylowMod q R F P ∧ GI.Impl.OutbNormIn F P) →
      Group.IsNilpotent (F ⧸ R.subgroupOf F)) ∧
    (∀ {p : ℕ}, p.Prime → ∀ {R F E_H P : Subgroup (Equiv.Perm (Fin n))}
      [(R.subgroupOf F).Normal], F ≤ E_H → ∀ {reps : List (Equiv.Perm (Fin n))},
      (∀ x ∈ E_H, GI.Impl.TmRpCov R reps x) → GI.Impl.OutbSylowMod p R F P →
      ∀ {s : Equiv.Perm (Fin n)}, (∀ r ∈ R, s⁻¹ * r * s ∈ R) → (∀ m ∈ F, s * m * s⁻¹ ∈ F) →
      ∃ e ∈ reps, e ∈ F ∧ P.map (MulAut.conj (e * s)).toMonoidHom ≤ P) ∧
    (∀ {K E_H R P : Subgroup (Equiv.Perm (Fin n))} {rs ss ts : List (Equiv.Perm (Fin n))},
      R ≤ E_H → R ≤ GI.Cited.gens ss → R ≤ P → GI.Cited.gens rs = R →
      GI.Cited.gens ss ⊔ E_H = K →
      (∀ t ∈ ts, t ∈ Subgroup.normalizer (P : Set (Equiv.Perm (Fin n))) ∧
        ∃ g ∈ GI.Cited.gens ss ⊓ E_H, ∃ s ∈ ss, t = g * s) →
      (∀ s ∈ ss, ∃ t ∈ ts, ∃ g ∈ GI.Cited.gens ss ⊓ E_H, t = g * s) →
      ¬ GI.Impl.OutbNormIn (GI.Cited.gens ss ⊓ E_H) P →
      R ≤ GI.Cited.gens (rs ++ ts) ∧ GI.Cited.gens (rs ++ ts) ≤ GI.Cited.gens ss ∧
        GI.Cited.gens (rs ++ ts) ⊔ E_H = K ∧
        2 * Nat.card (GI.Cited.gens (rs ++ ts) ⊓ E_H : Subgroup _) ≤
          Nat.card (GI.Cited.gens ss ⊓ E_H : Subgroup _)) ∧
    (∀ {K E_H R S : Subgroup (Equiv.Perm (Fin n))}, R ≤ E_H → E_H ≤ K → R ≤ S → S ≤ K →
      ∀ [(E_H.subgroupOf K).Normal] [(R.subgroupOf (S ⊓ E_H : Subgroup _)).Normal]
        [(R.subgroupOf S).Normal],
      Group.IsSolvable (K ⧸ E_H.subgroupOf K) →
      Group.IsNilpotent ((S ⊓ E_H : Subgroup _) ⧸ R.subgroupOf (S ⊓ E_H : Subgroup _)) →
      Group.IsSolvable (S ⧸ R.subgroupOf S)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp R F E_H P _ hME reps hcov hRP hPM b hc hb
    exact GI.Impl.outb_exists_rep_grow hp hME hcov hRP hPM hc hb
  · intro R F _ hRM h
    exact GI.Impl.outb_nilpotent_of_normal hRM h
  · intro p hp R F E_H P _ hME reps hcov hsyl s hsR hsM
    exact GI.Impl.outb_exists_rep_conj hp hME hcov hsyl hsR hsM
  · intro K E_H R P rs ss ts hRE hRS hRP hR hSE hts hcov hnot
    exact GI.Impl.outb_corr_step hRE hRS hRP hR hSE hts hcov hnot
  · intro K E_H R S hRE hEK hRS hSK _ _ _ hK hM
    exact GI.Impl.outb_solvable_quotient hRE hEK hRS hSK hK hM

/-- **The end of "Computing `R'`"**: a subgroup `S` with `R ≤ S ≤ K*_H`, `S/R` solvable and
`S E_H = K*_H` has the form of Lemma A.21. Lemma A.19 applied to `R ◁ S` gives a solvable
`S₁ ≤ S` with `S₁ R = S`, and then `S₁ E_H = K*_H`. So `R' = S` satisfies `N ◁ R' ≤ H`,
`R'/N` is solvable, and `[H : R'] ≤ b(Q)²`. -/
theorem par_compute_radical_subgroup {G : Type u} [Group G] [Finite G]
    {H N : Subgroup G} (hNH : N ≤ H) [(N.subgroupOf H).Normal] {S : Subgroup G}
    (hRS : radicalPreimage H N ≤ S)
    (hSK : S ≤ radicalPreimage H (soclePreimage H (radicalPreimage H N)))
    [((radicalPreimage H N).subgroupOf S).Normal]
    (hsolv : Group.IsSolvable (S ⧸ (radicalPreimage H N).subgroupOf S))
    (hsup : S ⊔ soclePreimage H (radicalPreimage H N) =
      radicalPreimage H (soclePreimage H (radicalPreimage H N))) :
    (∃ S₁ : Subgroup G, S₁ ≤ S ∧ Group.IsSolvable S₁ ∧ S₁ ⊔ radicalPreimage H N = S ∧
      S₁ ⊔ soclePreimage H (radicalPreimage H N) =
        radicalPreimage H (soclePreimage H (radicalPreimage H N))) ∧
    N ≤ S ∧ S ≤ H ∧ (N.subgroupOf S).Normal ∧ (∃ ℓ, relDerived S N ℓ ≤ N) ∧
      (∀ [(N.subgroupOf S).Normal], Group.IsSolvable (S ⧸ N.subgroupOf S)) ∧
      (S.subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2 := by
  have hRE : radicalPreimage H N ≤ soclePreimage H (radicalPreimage H N) :=
    le_soclePreimage (radicalPreimage_le H N)
  refine ⟨?_, GI.RadicalFreeOrder.radical_free_order_of_quotient hNH hRS hSK
    (fun [_] => hsolv) hsup⟩
  have := hsolv
  obtain ⟨S₁, hS₁S, hS₁solv, hS₁R⟩ := lem_solvable_supplement hRS
  refine ⟨S₁, hS₁S, hS₁solv, hS₁R, ?_⟩
  rw [← hsup, ← hS₁R, sup_assoc, sup_eq_right.mpr hRE]

/-- **Paragraph "Rebasing into `R'`"** before Corollary A.22.
* For objects `x = Lh`, `y = Lk` of one color with `h, k ∈ H` and `L ≤ H`, the element
  `g = h⁻¹ k` carries `x` to `y`, the stabilizer of `y` in `H` is `K = L^k`, and
  `Iso_H(x, y) = g K`.
* For subgroups `R'`, `K`, an element `g`, and a list `S` of elements of `K` with one element in
  each coset `R' c`, `c ∈ K`: `R' ∩ gK` is nonempty exactly when `g s⁻¹ ∈ R'` for some
  `s ∈ S`, and if `u ∈ R' ∩ gK`, then `R' ∩ gK = u (R' ∩ K)`. Schreier's lemma for the
  generators of `R' ∩ K` is `GI.Impl.outbSchreier_gens_eq`.
* The new object of `w`, for `u ∈ R'` with `z^u = w`: the set `{v ∈ R' : z^v = w}` is the
  coset `(R' ∩ H_z) u`; it determines `w`; for `t ∈ R'` the set for `w^t` is the set for `w`
  times `t`; and its group `R' ∩ H_z` contains `N` when `N ≤ R'` fixes `z`.
That such a map keeps all transporters in `R'` is `GI.Impl.tmCs_iso_map`. -/
theorem par_rebase_subgroup {G : Type*} [Group G] {κ : Type*} {Ω : Type*} [RAct G Ω] :
    (∀ (L : κ → Subgroup G) (c : κ) {H : Subgroup G}, L c ≤ H → ∀ {h k : G}, h ∈ H → k ∈ H →
      cobj L c h ↼ (h⁻¹ * k) = cobj L c k ∧ Aut H (cobj L c k) = conjR (L c) k ∧
      Iso H (cobj L c h) (cobj L c k) = (fun a => (h⁻¹ * k) * a) '' (conjR (L c) k : Set G)) ∧
    (∀ (R' K : Subgroup G) (g : G) (S : List G), (∀ s ∈ S, s ∈ K) →
      (∀ c ∈ K, ∃ s ∈ S, c * s⁻¹ ∈ R') →
      (((R' : Set G) ∩ (fun a => g * a) '' (K : Set G)).Nonempty ↔ ∃ s ∈ S, g * s⁻¹ ∈ R') ∧
      ∀ u ∈ (R' : Set G) ∩ (fun a => g * a) '' (K : Set G),
        (R' : Set G) ∩ (fun a => g * a) '' (K : Set G) =
          (fun a => u * a) '' ((R' ⊓ K : Subgroup G) : Set G)) ∧
    (∀ (R' N : Subgroup G) (z w : Ω) (u : G), u ∈ R' → z ↼ u = w →
      {v | v ∈ R' ∧ z ↼ v = w} = (fun a => a * u) '' (Aut R' z : Set G) ∧
      (∀ w' : Ω, {v | v ∈ R' ∧ z ↼ v = w} = {v | v ∈ R' ∧ z ↼ v = w'} → w = w') ∧
      (∀ t ∈ R', {v | v ∈ R' ∧ z ↼ v = w ↼ t} =
        (fun v => v * t) '' {v | v ∈ R' ∧ z ↼ v = w}) ∧
      (N ≤ R' → (∀ n ∈ N, z ↼ n = z) → N ≤ Aut R' z)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro L c H hLH h k hh hk
    have hK : conjR (L c) k ≤ H := by
      intro x hx
      have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem hk) (hLH (mem_conjR.mp hx))) hk
    refine ⟨?_, ?_, ?_⟩
    · rw [cobj_act, mul_inv_cancel_left]
    · rw [aut_cobj, inf_eq_right.mpr hK]
    · ext v
      simp only [mem_iso, cobj_act, cobj_eq_iff, true_and, Set.mem_image, SetLike.mem_coe,
        mem_conjR]
      constructor
      · rintro ⟨-, hv⟩
        refine ⟨k⁻¹ * h * v, ?_, by group⟩
        have e : k * (k⁻¹ * h * v) * k⁻¹ = h * v * k⁻¹ := by group
        rw [e]; exact hv
      · rintro ⟨a, ha, rfl⟩
        have e : h * (h⁻¹ * k * a) * k⁻¹ = k * a * k⁻¹ := by group
        refine ⟨?_, by rw [e]; exact ha⟩
        have e' : h⁻¹ * k * a = h⁻¹ * (k * a * k⁻¹) * k := by group
        rw [e']
        exact H.mul_mem (H.mul_mem (H.inv_mem hh) (hLH ha)) hk
  · intro R' K g S hSK hcov
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨u, huR, c, hc, rfl⟩
      obtain ⟨s, hs, hcs⟩ := hcov c⁻¹ (K.inv_mem hc)
      refine ⟨s, hs, ?_⟩
      have e : g * s⁻¹ = (g * c) * (c⁻¹ * s⁻¹) := by group
      rw [e]
      exact R'.mul_mem huR hcs
    · rintro ⟨s, hs, hgs⟩
      exact ⟨g * s⁻¹, hgs, s⁻¹, K.inv_mem (hSK s hs), rfl⟩
    · rintro u ⟨huR, c₀, hc₀, rfl⟩
      ext x
      simp only [Set.mem_inter_iff, Set.mem_image, SetLike.mem_coe, Subgroup.mem_inf]
      constructor
      · rintro ⟨hxR, c, hc, rfl⟩
        refine ⟨c₀⁻¹ * c, ⟨?_, K.mul_mem (K.inv_mem hc₀) hc⟩, by group⟩
        have e : c₀⁻¹ * c = (g * c₀)⁻¹ * (g * c) := by group
        rw [e]
        exact R'.mul_mem (R'.inv_mem huR) hxR
      · rintro ⟨a, ⟨haR, haK⟩, rfl⟩
        exact ⟨R'.mul_mem huR haR, c₀ * a, K.mul_mem hc₀ haK, by group⟩
  · intro R' N z w u hu hzw
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext v
      simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, mem_aut]
      constructor
      · rintro ⟨hv, hzv⟩
        refine ⟨v * u⁻¹, ⟨R'.mul_mem hv (R'.inv_mem hu), ?_⟩, by group⟩
        rw [← act_act, hzv, ← hzw, act_act_inv]
      · rintro ⟨a, ⟨ha, hza⟩, rfl⟩
        exact ⟨R'.mul_mem ha hu, by rw [← act_act, hza, hzw]⟩
    · intro w' he
      have hmem : u ∈ {v | v ∈ R' ∧ z ↼ v = w} := ⟨hu, hzw⟩
      rw [he] at hmem
      exact hzw.symm.trans hmem.2
    · intro t ht
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨hv, hzv⟩
        refine ⟨v * t⁻¹, ⟨R'.mul_mem hv (R'.inv_mem ht), ?_⟩, by group⟩
        rw [← act_act, hzv, act_act_inv]
      · rintro ⟨v', ⟨hv', hzv'⟩, rfl⟩
        exact ⟨R'.mul_mem hv' ht, by rw [← act_act, hzv']⟩
    · intro hNR hfix n hn
      exact ⟨hNR hn, hfix n hn⟩

end GI.Paper
