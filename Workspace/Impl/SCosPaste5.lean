module

public import Workspace.Impl.SCosPaste4

@[expose] public section

/-!
# The paste function

`scos_paste_spec`: on the answers of the children (one for each coset representative `t` of
`K` in `𝒢`), function `7` answers the problem `x 𝒢` on `Φ`. The filter keeps the nonempty
answers. If none is left, the subcoset is empty (`scosPaste_facts`). Otherwise the branch
`scosPaste_then` builds `[z₁, w]`, and `w` is a group value of `L(𝒢, Φ)` by `scosPaste_gens`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

section Prog

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- **The paste.** -/
theorem scos_paste_spec {𝒢 K : Subgroup (ScosPair n)} {x : ScosPair n} {Φ : Finset (Fin n)}
    {ts : List (ScosPair n)} {as : List Val}
    (hinv : ScosInv 𝒢 Φ) (hK : K ≤ 𝒢) (hts : ∀ t ∈ ts, t ∈ 𝒢)
    (hcov : ∀ g ∈ 𝒢, ∃ t ∈ ts, t⁻¹ * g ∈ K)
    (has : List.Forall₂ (fun t a => ScosAns n a (x * t) K Φ) ts as)
    (hlen : ts.length ≤ (n + n + 1) ^ c) :
    FunAll 𝒫 7 (.list as) (fun w cost => ScosAns n w x 𝒢 Φ ∧ cost ≤ scosOwnP hps n c) := by
  obtain ⟨zs, hgood, hin, hcz⟩ := scosPaste_collect has
  obtain ⟨hzs, hcov', hemp⟩ := scosPaste_facts hinv hK hts hcov hin hcz
  obtain ⟨hQ1, hQ2, hQ3, hQ4, hQ5⟩ := scosPaste_Q n
  have hlas : as.length ≤ (n + n + 1) ^ c := has.length_eq ▸ hlen
  obtain ⟨hM1, hM2, hM3, hM4⟩ := scosPaste_M n c hlas
  obtain ⟨hMp1, hMp2, hMp3, hMp4, hMp5⟩ := scosPaste_Mpow hM4
  have hLQ : as.length * (n + n + 1) ^ 6 + (n + n + 1) ^ 6 ≤ scosPasteM n c := by
    rw [Nat.add_mul, Nat.one_mul] at hM2; exact hM2
  -- the answers are lists of weight at most `700 Q`
  have hal : ∀ a ∈ as, (∃ l, a = .list l) ∧ a.wt ≤ 700 * (n + n + 1) ^ 6 := by
    intro a ha
    obtain ⟨t, -, h⟩ := scosPaste_mem_right has ha
    refine ⟨?_, scosPaste_wt_ans h⟩
    rcases h with ⟨rfl, -⟩ | ⟨z, -, lv, rfl, -⟩
    exacts [⟨_, rfl⟩, ⟨_, rfl⟩]
  -- the filter
  have hp : ∀ a ∈ as, FunDet 𝒫 8 (.list [.nat 0, a]) (boolVal (scosPasteGood a))
      ((fun _ => 6000 * (n + n + 1) ^ 6) a) := by
    intro a ha
    obtain ⟨⟨l, rfl⟩, hw⟩ := hal a ha
    refine FunDet.mono (scosPaste_goodTest l) ?_
    show _ ≤ 6000 * (n + n + 1) ^ 6
    have := wt_list2_le (.nat 0) (.list l)
    have := wt_nat_le 0
    omega
  have hfilD : FunAll 𝒫 244 (.list [.nat 0, .list as]) (fun w cost =>
      w = .list (as.filter scosPasteGood) ∧ cost ≤ as.length * (6000 * (n + n + 1) ^ 6) +
        loopModK * (as.length + 1) * ((Val.list [.nat 0, .list as]).wt + as.length +
          (Val.list (as.filter scosPasteGood)).wt + 1)) :=
    (filter_spec scos_filter hp).mono fun w cost h => by
      obtain ⟨rfl, hc⟩ := h
      simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hc
      exact ⟨rfl, hc⟩
  have d1 := Det.call (Det.mk2 (Det.nat (P := 𝒫) (env := [.list as]) 0)
    (Det.var' (i := 0) (v := .list as) rfl)) hfilD
  -- weights of the lists
  have was := GI.Lang.wt_list_le_of as fun a ha => (hal a ha).2
  have wfs := GI.Lang.wt_list_le_of (as.filter scosPasteGood) fun a ha =>
    (hal a (List.mem_of_mem_filter ha)).2
  have hfl : (as.filter scosPasteGood).length ≤ as.length := List.length_filter_le _ _
  have hfl' := Nat.mul_le_mul_right (2 * (700 * (n + n + 1) ^ 6) + 1) hfl
  have e1 : as.length * (2 * (700 * (n + n + 1) ^ 6) + 1) =
      1400 * (as.length * (n + n + 1) ^ 6) + as.length := by ring
  have e2 : as.length * (6000 * (n + n + 1) ^ 6) = 6000 * (as.length * (n + n + 1) ^ 6) := by
    ring
  rw [e1] at was hfl'
  refine FunAll.intro scos_paste ?_
  unfold scosPasteF
  refine EvalAll.letE d1 fun v1 c1 h1 => ?_
  obtain ⟨rfl, hc1⟩ := h1
  have hc1' : c1 ≤ 10000000 * scosPasteM n c ^ 6 := by
    have w2 := wt_list2_le (.nat 0) (.list as)
    have w0 := wt_nat_le 0
    have w3 := wt_list2_le (.nat 0) (.list (as.filter scosPasteGood))
    have hin : (Val.list [.nat 0, .list as]).wt + as.length +
        (Val.list (as.filter scosPasteGood)).wt + 1 ≤ 5000 * scosPasteM n c := by omega
    have hov := Nat.mul_le_mul (Nat.mul_le_mul_left loopModK hM3) hin
    have e : loopModK * scosPasteM n c * (5000 * scosPasteM n c) =
        5000000 * scosPasteM n c ^ 2 := by unfold loopModK; ring
    omega
  clear hc1 hfilD d1 hp
  cases zs with
  | nil =>
    have hf0 : as.filter scosPasteGood = [] := List.forall₂_nil_left_iff.mp hgood
    rw [hf0]
    refine EvalAll.mono (Det.ite_zero (Det.length (vs := []) (Det.var' (P := 𝒫)
      (env := [.list as, .list []]) (i := 1) rfl)) Det.nil) fun w cost h => ?_
    obtain ⟨rfl, hc⟩ := h
    refine ⟨Or.inl ⟨rfl, hemp rfl⟩, ?_⟩
    unfold scosOwnP
    simp only [wt_list_nil, List.length_nil] at hc ⊢
    omega
  | cons z₁ zr =>
    obtain ⟨a₁, fr, hga, hgr, hfe⟩ := List.forall₂_cons_left_iff.mp hgood
    obtain ⟨lv₁, rfl, ⟨gs₁, rfl, hgs₁⟩, hlv⟩ := hga
    have hlenfr : fr.length + 1 ≤ (n + n + 1) ^ c := by
      have := hfe ▸ hfl
      simp only [List.length_cons] at this
      omega
    rw [hfe] at hgood wfs hfl hfl' ⊢
    simp only [List.length_cons] at hfl hfl' wfs
    refine EvalAll.ite (Det.length (Det.var' (P := 𝒫)
      (env := [.list as, .list (.list [encPerm (nintSum z₁), encGroup gs₁] :: fr)])
      (i := 1) rfl)) (fun vc cc h => ⟨_, h.1⟩) fun k cc h => ?_
    obtain ⟨hk, hcc⟩ := h
    simp only [Val.nat.injEq, List.length_cons] at hk
    subst hk
    rw [if_neg (by omega)]
    refine (scosPaste_then (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) (v0 := .list as)
      hgood hlv hlenfr).mono fun w cost h => ?_
    obtain ⟨w', rfl, hgv, hww, hcost⟩ := h
    refine ⟨Or.inr ⟨z₁, hzs z₁ (List.mem_cons_self ..), w', rfl, ?_, hww⟩, ?_⟩
    · rw [← scosPaste_gens hinv hK (List.mem_cons_self ..) hzs hcov' hgs₁]
      exact hgv
    · have ww := wt_list2_le (encPerm (nintSum z₁)) w'
      have wz := scosPaste_wt_perm (nintSum z₁)
      have hw' : w'.wt ≤ 320 * (n + n + 1) ^ 6 := hww
      simp only [List.length_cons] at hcc
      unfold scosOwnP
      omega

end Prog

end GI.Impl
