import Workspace.Impl.SCosBig3

/-!
# Function 5 (`bigF`), the children and the paste

The body after the nine `let`s is `.call 7 (.call 241 [[kv, xv, ind], L])`. The coset pairs `L`
of step 9 give the representatives `t ∈ ts` of the cosets of `K = scosBMKer 𝒢 Φ lab`
(`scosBM_cover`); every child `[kv, x t, ind]` is a problem for `K`, whose orbits on `Φ` are
smaller than `Φ` (`scosBM_mo_lt`), so the hypothesis `hrec` solves it. The map over the children
is `scos_children_spec`, the paste `scos_paste_spec`. The numbers `m` (blocks) and `s` (block
size) of the postcondition come from `scosBM_blocks`, and `ℓ = |L| ≤ (m + 1)^c` from
`scosBM_length_le`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved GI.Algorithm GI.Assembly Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The weight of the list of coset pairs. -/
theorem scosBig_wtPairs (c : ℕ) {L : List ((Fin (n + n) → ℕ) × Perm (Fin (n + n)))}
    (hf : ∀ p ∈ L, ∀ i, p.1 i ≤ n + n) (hlen : L.length ≤ (n + n + 1) ^ c) :
    (encPairs labKey L).wt ≤ 50 * scosBigS n c := by
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  have hM := scosPaste_M n c hlen
  have h := GI.Lang.wt_list_le_of (L.map (GI.Lang.encPair labKey)) (c := 22 * (n + n + 1) ^ 6)
    (by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      have h1 := wt_list2_le (natList (labKey p.1)) (encPerm p.2)
      have h2 := scosPaste_wt_lab p.1 (hf p hp)
      have h3 := scosPaste_wt_perm p.2
      show (Val.list [natList (labKey p.1), encPerm p.2]).wt ≤ _
      omega)
  rw [List.length_map] at h
  have e : L.length * (2 * (22 * (n + n + 1) ^ 6) + 1) =
      44 * (L.length * (n + n + 1) ^ 6) + L.length := by ring
  have h2 : (L.length + 1) * (n + n + 1) ^ 6 = L.length * (n + n + 1) ^ 6 + (n + n + 1) ^ 6 := by
    ring
  show (Val.list (L.map (GI.Lang.encPair labKey))).wt ≤ _
  omega

/-- The weight of the list of the child answers. -/
theorem scosBig_wtAs (c : ℕ) {ts : List (ScosPair n)} {as : List Val} {x : ScosPair n}
    {K : Subgroup (ScosPair n)} {Φ : Finset (Fin n)}
    (has : List.Forall₂ (fun t a => ScosAns n a (x * t) K Φ) ts as)
    (hlen : ts.length ≤ (n + n + 1) ^ c) : (Val.list as).wt ≤ 1500 * scosBigS n c := by
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  have hl : as.length ≤ (n + n + 1) ^ c := has.length_eq ▸ hlen
  have hM := scosPaste_M n c hl
  have h := GI.Lang.wt_list_le_of as (c := 700 * (n + n + 1) ^ 6) fun a ha => by
    obtain ⟨t, -, hta⟩ := scosPaste_mem_right has ha
    exact scosPaste_wt_ans hta
  have e : as.length * (2 * (700 * (n + n + 1) ^ 6) + 1) =
      1400 * (as.length * (n + n + 1) ^ 6) + as.length := by ring
  have h2 : (as.length + 1) * (n + n + 1) ^ 6 = as.length * (n + n + 1) ^ 6 + (n + n + 1) ^ 6 :=
    by ring
  omega

section Prog

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-- **The children and the paste.** -/
theorem scosBig_tail (hc : ScosPalfyC c) {𝒢 : Subgroup (ScosPair n)} {x : ScosPair n}
    {Φ : Finset (Fin n)} (hinv : ScosInv 𝒢 Φ) (htr : ScosTrans 𝒢 Φ) (h2 : 2 ≤ Φ.card)
    (hsol : IsSolvable (𝒢.map (MonoidHom.fst (Perm (Fin n)) (Perm (Fin n)))))
    {gs : List (Perm (Fin (n + n)))} (hgs : gens gs = 𝒢.map nintSum)
    (hw : (encGroup gs).wt ≤ scosW n)
    {lab : Fin (scosBMk Φ) → ℕ} (hlt : ∀ j, lab j < scosBMk Φ)
    (hmbl : IsMinimalBlocks (restrK (Equiv.refl _) (𝒢.map nintSum) (scosPhiF Φ)
      (scosBM_invariant 𝒢 Φ hinv)).range lab)
    {kv : Val} (hkv : ScosBigKer 𝒢 Φ lab kv) {w9 : Val} (hcos : ScosBigCos Φ lab gs w9)
    (T : Subgroup (ScosPair n) → Finset (Fin n) → ℕ)
    (hrec : ∀ (K : Subgroup (ScosPair n)) (v' : Val) (x' : ScosPair n), K ≤ 𝒢 →
      ScosProb n v' K x' Φ → scosMo K Φ < Φ.card →
        FunAll 𝒫 0 v' (fun w c' => ScosAns n w x' K Φ ∧ c' ≤ T K Φ))
    (rest : List Val) (h8 : rest[7]? = some kv) (h9 : rest[8]? = some w9) :
    EvalAll 𝒫 (.list [encGroup gs, encPerm (nintSum x), scosInd Φ] :: rest)
      (.call 7 (.call 241 (mk2 (mk3 (.var 8) (arg 1) (arg 2)) (.var 9))))
      (ScosBigPost n c T 𝒢 x Φ (scosOwnC n c + scosOwnP hps n c + scosBigD n c)) := by
  obtain ⟨L, rfl, hnd, horb, hgood⟩ := hcos
  have hgen : genGroup (1 :: gs) = 𝒢.map nintSum := (scosBig_genGroup gs).trans hgs
  obtain ⟨ts, hts, htsG, hcov⟩ := scosBM_cover 𝒢 Φ lab (1 :: gs) hgen L horb hgood
  have hlenm := scosBM_length_le 𝒢 Φ hinv lab hc htr hsol hmbl (1 :: gs) hgen L hnd horb
  have hlen : L.length ≤ (n + n + 1) ^ c := hlenm.trans (scosBM_pow_le Φ lab c)
  have hlts : ts.length = L.length := by
    have := congrArg List.length hts
    simp only [List.length_map] at this
    exact this.symm
  have hf : ∀ p ∈ L, ∀ i, p.1 i ≤ n + n := by
    intro p hp i
    rw [← (hgood p hp).2]
    exact scosBMLab_le Φ lab hlt _
  obtain ⟨hm2, s, hs1, hms, hmo⟩ := scosBM_blocks 𝒢 Φ hinv lab htr h2 hmbl
  have hch : ∀ t ∈ ts, FunAll 𝒫 0 (.list [kv, encPerm (nintSum (x * t)), scosInd Φ])
      (fun w c' => ScosAns n w (x * t) (scosBMKer 𝒢 Φ lab) Φ ∧ c' ≤ T (scosBMKer 𝒢 Φ lab) Φ) :=
    fun t _ => hrec _ _ (x * t) (scosBMKer_le 𝒢 Φ lab)
      ⟨⟨kv, rfl, hkv.1, hkv.2⟩, scosBMKer_inv 𝒢 Φ hinv lab, scosBMKer_solvable 𝒢 Φ lab hsol⟩
      (scosBM_mo_lt 𝒢 Φ hinv lab htr h2 hmbl)
  have hchild := scos_children_spec (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) hts hf hlen
    hkv.2 hch
  -- the argument of the map
  have d8 := Det.var' (P := 𝒫) (env := .list [encGroup gs, encPerm (nintSum x), scosInd Φ] :: rest)
    (i := 8) (v := kv) h8
  have d9 := Det.var' (P := 𝒫) (env := .list [encGroup gs, encPerm (nintSum x), scosInd Φ] :: rest)
    (i := 9) (v := encPairs labKey L) h9
  have da1 := Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ]) (rest := rest)
    (j := 1) (v := encPerm (nintSum x)) rfl
  have da2 := Det.arg' (P := 𝒫) (vs := [encGroup gs, encPerm (nintSum x), scosInd Φ]) (rest := rest)
    (j := 2) (v := scosInd Φ) rfl
  have dA := Det.mk2 (Det.mk3 d8 da1 da2) d9
  have hQ := scosPaste_Q n
  have hS := scosBigS_facts n c
  have w0 := scosBig_wt0 gs x Φ hw
  have w9 := scosBig_wtPairs c hf hlen
  have wk := hkv.2
  have wx := scosPaste_wt_perm (nintSum x)
  have wi := scosPaste_wt_ind Φ
  have wC := wt_list3_le kv (encPerm (nintSum x)) (scosInd Φ)
  have wA := wt_list2_le (.list [kv, encPerm (nintSum x), scosInd Φ]) (encPairs labKey L)
  unfold scosW at wk
  have dA' := dA.mono (c' := 10000 * scosBigS n c) (by omega)
  have hin : EvalAll 𝒫 (.list [encGroup gs, encPerm (nintSum x), scosInd Φ] :: rest)
      (.call 241 (mk2 (mk3 (.var 8) (arg 1) (arg 2)) (.var 9)))
      (fun v cv => ∃ as : List Val, v = .list as ∧
        List.Forall₂ (fun t a => ScosAns n a (x * t) (scosBMKer 𝒢 Φ lab) Φ) ts as ∧
        cv ≤ 10000 * scosBigS n c + (scosOwnC n c + L.length *
          (scosOwnC n c + T (scosBMKer 𝒢 Φ lab) Φ)) + v.wt + 1) :=
    EvalAll.call_funAll dA' fun v ca h => by
      obtain ⟨rfl, hca⟩ := h
      exact hchild.mono fun w cb ⟨as, h1, h2, h3⟩ => ⟨as, h1, h2, by omega⟩
  refine EvalAll.call_funAll hin fun v cv hv => ?_
  obtain ⟨as, rfl, has, hcv⟩ := hv
  have hpaste := scos_paste_spec (c := c) (hps := hps) (hpre := hpre) (hmb := hmb) hinv
    (scosBMKer_le 𝒢 Φ lab) htsG hcov has (hlts ▸ hlen)
  have was := scosBig_wtAs c has (hlts ▸ hlen)
  have hD : 100000 * scosBigS n c ≤ scosBigD n c :=
    scosBigD_of (A := 100000) (j := 1) (by rw [pow_one]) (by norm_num) (by norm_num)
  refine hpaste.mono fun w cb ⟨hans, hcb⟩ => ⟨hans, scosBMKer 𝒢 Φ lab,
    (Finset.univ.image lab).card, s, L.length, scosBMKer_le 𝒢 Φ lab, hm2, hs1, hms, hlenm, hmo, ?_⟩
  have ww := scosPaste_wt_ans hans
  generalize L.length * (scosOwnC n c + T (scosBMKer 𝒢 Φ lab) Φ) = Y at *
  omega

end Prog

end GI.Impl
