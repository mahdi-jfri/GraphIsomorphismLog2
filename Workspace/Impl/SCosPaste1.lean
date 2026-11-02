import Workspace.Impl.SCosSpec

/-!
# The children of the transitive case

Function `5` (`scosBigF`) ends with `.call 7 (.call 241 (mk2 (mk3 kv xv ind) pairs))`. Function
`241` maps the child function `6` over the coset pairs `[f, t]`: the child solves the problem
`[kv, x t, ind]`. This file proves the specification of that map (`scos_children_spec`).

The weights are bounded through two quantities: `Q = (N + 1)^6` with `N = n + n`, which bounds
the weight of every group value and every answer up to a constant (`scosAns_wt_le`), and
`M = Q ((N + 1)^c + 1)`, which also bounds the number of children times `Q`.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

variable {n : ℕ}

/-- The quantity `Q ((N + 1)^c + 1)` with `Q = (N + 1)^6`, `N = n + n`. -/
def scosPasteM (n c : ℕ) : ℕ := (n + n + 1) ^ 6 * ((n + n + 1) ^ c + 1)

/-- The own cost of the map over the children. -/
def scosOwnC (n c : ℕ) : ℕ := 100000000 * scosPasteM n c ^ 2

/-- Elementary facts on `Q = (N + 1)^6`. -/
theorem scosPaste_Q (n : ℕ) : 1 ≤ (n + n + 1) ^ 6 ∧ n + n + 1 ≤ (n + n + 1) ^ 6 ∧
    (n + n + 1) ^ 2 ≤ (n + n + 1) ^ 6 ∧ (n + n + 1) ^ 3 ≤ (n + n + 1) ^ 6 ∧
    (n + n + 1) ^ 4 ≤ (n + n + 1) ^ 6 := by
  have h1 : 1 ≤ n + n + 1 := by omega
  refine ⟨Nat.one_le_pow _ _ (by omega), ?_, ?_, ?_, ?_⟩
  · simpa using Nat.pow_le_pow_right h1 (show 1 ≤ 6 by omega)
  all_goals exact Nat.pow_le_pow_right h1 (by omega)

/-- Elementary facts on `M`. -/
theorem scosPaste_M (n c : ℕ) {len : ℕ} (hlen : len ≤ (n + n + 1) ^ c) :
    (n + n + 1) ^ 6 ≤ scosPasteM n c ∧ (len + 1) * (n + n + 1) ^ 6 ≤ scosPasteM n c ∧
    len + 1 ≤ scosPasteM n c ∧ 1 ≤ scosPasteM n c := by
  have hQ := (scosPaste_Q n).1
  have h2 : (len + 1) * (n + n + 1) ^ 6 ≤ scosPasteM n c := by
    unfold scosPasteM
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (by omega)
  have h3 : len + 1 ≤ (len + 1) * (n + n + 1) ^ 6 := Nat.le_mul_of_pos_right _ hQ
  have h4 : (n + n + 1) ^ 6 ≤ (len + 1) * (n + n + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem scosPasteM_le (n c : ℕ) : scosPasteM n c ≤ 2 ^ (c + 7) * (n + 1) ^ (c + 6) := by
  have h1 : n + n + 1 ≤ 2 * (n + 1) := by omega
  have hB : (n + n + 1) ^ c + 1 ≤ 2 * (2 * (n + 1)) ^ c := by
    have := Nat.pow_le_pow_left h1 c
    have := Nat.one_le_pow c (2 * (n + 1)) (by omega)
    omega
  have hQ : (n + n + 1) ^ 6 ≤ (2 * (n + 1)) ^ 6 := Nat.pow_le_pow_left h1 6
  calc scosPasteM n c ≤ (2 * (n + 1)) ^ 6 * (2 * (2 * (n + 1)) ^ c) :=
        Nat.mul_le_mul hQ hB
    _ = 2 ^ (c + 7) * (n + 1) ^ (c + 6) := by rw [mul_pow, mul_pow]; ring

theorem scosOwnC_le (n c : ℕ) :
    scosOwnC n c ≤ (100000000 * 4 ^ (c + 7)) * (n + 1) ^ (2 * c + 12) := by
  have h := Nat.pow_le_pow_left (scosPasteM_le n c) 2
  unfold scosOwnC
  calc 100000000 * scosPasteM n c ^ 2 ≤ 100000000 * (2 ^ (c + 7) * (n + 1) ^ (c + 6)) ^ 2 :=
        Nat.mul_le_mul_left _ h
    _ = (100000000 * 4 ^ (c + 7)) * (n + 1) ^ (2 * c + 12) := by
        rw [show (4 : ℕ) = 2 ^ 2 by rfl, ← pow_mul]; ring

/-! ### Weights -/

theorem scosPaste_wt_ind (Φ : Finset (Fin n)) : (scosInd Φ).wt ≤ 7 * (n + n + 1) ^ 6 := by
  have h := wt_encFun_le (indF (Equiv.refl (Fin (n + n))) (scosPhiF Φ)) (B := 1)
    (indF_le_one _ _)
  have := (scosPaste_Q n).2.1
  unfold scosInd indVal
  omega

theorem scosPaste_wt_perm (σ : Perm (Fin (n + n))) : (encPerm σ).wt ≤ 4 * (n + n + 1) ^ 6 := by
  have h := wt_encPerm_le σ
  have := (scosPaste_Q n).2.2.1
  omega

theorem scosPaste_wt_lab (f : Fin (n + n) → ℕ) (hf : ∀ i, f i ≤ n + n) :
    (natList (labKey f)).wt ≤ 4 * (n + n + 1) ^ 6 := by
  rw [natList_labKey]
  have h := wt_encFun_le_sq f hf
  have := (scosPaste_Q n).2.2.1
  omega

/-- **The weight of an answer.** -/
theorem scosAns_wt_le {w : Val} {x : ScosPair n} {𝒢 : Subgroup (ScosPair n)}
    {Φ : Finset (Fin n)} (h : ScosAns n w x 𝒢 Φ) :
    w.wt ≤ 2 * (4 * (n + n + 1) ^ 2 + scosW n) + 6 := by
  rcases h with ⟨rfl, -⟩ | ⟨z, -, lv, rfl, -, hlv⟩
  · simp
  · have h1 := wt_list2_le (encPerm (nintSum z)) lv
    have h2 := wt_encPerm_le (nintSum z)
    omega

/-- The weight of an answer, in terms of `Q`. -/
theorem scosPaste_wt_ans {w : Val} {x : ScosPair n} {𝒢 : Subgroup (ScosPair n)}
    {Φ : Finset (Fin n)} (h : ScosAns n w x 𝒢 Φ) : w.wt ≤ 700 * (n + n + 1) ^ 6 := by
  have h1 := scosAns_wt_le h
  have := (scosPaste_Q n).2.2.1
  have := (scosPaste_Q n).1
  unfold scosW at h1
  omega

section Prog

variable {c : ℕ} {hps : PointwiseStab} {hpre : Preimage} {hmb : MinimalBlocks}

local notation "𝒫" => scosProgram c hps hpre hmb

/-! ### One child -/

/-- **One child.** On `[[kv, x, ind], [f, t]]` with `t = nintSum t'`, the answer of the problem
`[kv, x t', ind]`. -/
theorem scosPaste_child {K : Subgroup (ScosPair n)} {kv : Val} {x t : ScosPair n}
    {Φ : Finset (Fin n)} {p : (Fin (n + n) → ℕ) × Perm (Fin (n + n))} (hp : p.2 = nintSum t)
    (hf : ∀ i, p.1 i ≤ n + n) (hkv : kv.wt ≤ scosW n) {TK : ℕ}
    (hch : FunAll 𝒫 0 (.list [kv, encPerm (nintSum (x * t)), scosInd Φ])
      (fun w c' => ScosAns n w (x * t) K Φ ∧ c' ≤ TK)) :
    FunAll 𝒫 6 (.list [.list [kv, encPerm (nintSum x), scosInd Φ], GI.Lang.encPair labKey p])
      (fun w cost => ScosAns n w (x * t) K Φ ∧ cost ≤ 100000 * (n + n + 1) ^ 6 + TK) := by
  obtain ⟨f, s⟩ := p
  simp only at hp hf
  subst hp
  have d0 := Det.arg' (P := 𝒫) (vs := [.list [kv, encPerm (nintSum x), scosInd Φ],
    .list [natList (labKey f), encPerm (nintSum t)]]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := 𝒫) (vs := [.list [kv, encPerm (nintSum x), scosInd Φ],
    .list [natList (labKey f), encPerm (nintSum t)]]) (rest := []) (j := 1) rfl
  have dk := Det.get' d0 (Det.nat 0) (v := kv) rfl
  have dx := Det.get' d0 (Det.nat 1) (v := encPerm (nintSum x)) rfl
  have di := Det.get' d0 (Det.nat 2) (v := scosInd Φ) rfl
  have dt := Det.get' d1 (Det.nat 1) (v := encPerm (nintSum t)) rfl
  have dc := Det.call (Det.mk2 dx dt) (compose_spec scos_compose (nintSum x) (nintSum t))
  rw [← map_mul] at dc
  have da := Det.mk3 dk dc di
  refine FunAll.intro scos_child (EvalAll.call_funAll da fun v ca h => ?_)
  obtain ⟨rfl, hca⟩ := h
  refine hch.mono fun w c' hw => ⟨hw.1, ?_⟩
  have hw' := scosPaste_wt_ans hw.1
  -- weights
  have hQ := scosPaste_Q n
  have wk : kv.wt ≤ 320 * (n + n + 1) ^ 6 := hkv
  have wx := scosPaste_wt_perm (nintSum x)
  have wt' := scosPaste_wt_perm (nintSum t)
  have wr := scosPaste_wt_perm (nintSum (x * t))
  have wi := scosPaste_wt_ind Φ
  have wf := scosPaste_wt_lab f hf
  have wC := wt_list3_le kv (encPerm (nintSum x)) (scosInd Φ)
  have wX := wt_list2_le (natList (labKey f)) (encPerm (nintSum t))
  have wA := wt_list2_le (.list [kv, encPerm (nintSum x), scosInd Φ])
    (.list [natList (labKey f), encPerm (nintSum t)])
  have wY := wt_list2_le (encPerm (nintSum x)) (encPerm (nintSum t))
  have wZ := wt_list3_le kv (encPerm (nintSum (x * t))) (scosInd Φ)
  have lk : kv.wt < (Val.list [kv, encPerm (nintSum x), scosInd Φ]).wt :=
    wt_le_wt_list (by simp)
  have lx : (encPerm (nintSum x)).wt < (Val.list [kv, encPerm (nintSum x), scosInd Φ]).wt :=
    wt_le_wt_list (by simp)
  have li : (scosInd Φ).wt < (Val.list [kv, encPerm (nintSum x), scosInd Φ]).wt :=
    wt_le_wt_list (by simp)
  have lC : (Val.list [kv, encPerm (nintSum x), scosInd Φ]).wt < (Val.list
      [.list [kv, encPerm (nintSum x), scosInd Φ],
        .list [natList (labKey f), encPerm (nintSum t)]]).wt := wt_le_wt_list (by simp)
  have lt : (encPerm (nintSum t)).wt < (Val.list [natList (labKey f), encPerm (nintSum t)]).wt :=
    wt_le_wt_list (by simp)
  have lX : (Val.list [natList (labKey f), encPerm (nintSum t)]).wt < (Val.list
      [.list [kv, encPerm (nintSum x), scosInd Φ],
        .list [natList (labKey f), encPerm (nintSum t)]]).wt := wt_le_wt_list (by simp)
  have hp3 : permK * (n + n + 1) ^ 3 ≤ 30000 * (n + n + 1) ^ 6 :=
    Nat.mul_le_mul_left _ hQ.2.2.2.1
  generalize (Val.list [.list [kv, encPerm (nintSum x), scosInd Φ],
    .list [natList (labKey f), encPerm (nintSum t)]]).wt = A at *
  generalize permK * (n + n + 1) ^ 3 = P3 at *
  generalize (n + n + 1) ^ 6 = Q at *
  have := hw.2
  omega

theorem scosPaste_mem_right {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons h1 _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., h1⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-- The entrywise relation of the map, turned into a relation on the pairs `t`. -/
theorem scosPaste_forall₂ {Pr : ScosPair n → Val → Prop}
    {L : List ((Fin (n + n) → ℕ) × Perm (Fin (n + n)))} {ts : List (ScosPair n)}
    (hts : L.map Prod.snd = ts.map nintSum) {ws : List Val}
    (h : List.Forall₂ (fun v w => ∀ (y : Val) (t : ScosPair n),
      v = .list [y, encPerm (nintSum t)] → Pr t w) (L.map (GI.Lang.encPair labKey)) ws) :
    List.Forall₂ Pr ts ws := by
  induction L generalizing ts ws with
  | nil =>
    cases ts with
    | nil => cases h; exact .nil
    | cons _ _ => simp at hts
  | cons p L ih =>
    cases ts with
    | nil => simp at hts
    | cons t ts =>
      simp only [List.map_cons, List.cons.injEq] at hts
      cases h with
      | cons h1 h2 =>
        refine .cons (h1 (natList (labKey p.1)) t ?_) (ih hts.2 h2)
        simp only [GI.Lang.encPair, hts.1]

/-- **The children.** -/
theorem scos_children_spec {K : Subgroup (ScosPair n)} {kv : Val} {x : ScosPair n}
    {Φ : Finset (Fin n)}
    {L : List ((Fin (n + n) → ℕ) × Perm (Fin (n + n)))} {ts : List (ScosPair n)}
    (hts : L.map Prod.snd = ts.map nintSum) (hf : ∀ p ∈ L, ∀ i, p.1 i ≤ n + n)
    (hlen : L.length ≤ (n + n + 1) ^ c) (hkv : kv.wt ≤ scosW n) {TK : ℕ}
    (hch : ∀ t ∈ ts, FunAll 𝒫 0 (.list [kv, encPerm (nintSum (x * t)), scosInd Φ])
      (fun w c' => ScosAns n w (x * t) K Φ ∧ c' ≤ TK)) :
    FunAll 𝒫 241 (.list [.list [kv, encPerm (nintSum x), scosInd Φ], encPairs labKey L])
      (fun w cost => ∃ as : List Val, w = .list as ∧
        List.Forall₂ (fun t a => ScosAns n a (x * t) K Φ) ts as ∧
        cost ≤ scosOwnC n c + L.length * (scosOwnC n c + TK)) := by
  have hxs : ∀ v ∈ L.map (GI.Lang.encPair labKey),
      FunAll 𝒫 6 (.list [.list [kv, encPerm (nintSum x), scosInd Φ], v])
        (fun w cost => (fun v w => ∀ (y : Val) (t : ScosPair n),
          v = .list [y, encPerm (nintSum t)] → ScosAns n w (x * t) K Φ) v w ∧
          cost ≤ (fun _ => 100000 * (n + n + 1) ^ 6 + TK) v) := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    have hp2 : p.2 ∈ ts.map nintSum := hts ▸ List.mem_map_of_mem (f := Prod.snd) hp
    obtain ⟨t, ht, hpt⟩ := List.mem_map.mp hp2
    refine (scosPaste_child hpt.symm (hf p hp) hkv (hch t ht)).mono fun w cost h => ⟨?_, h.2⟩
    intro y t' heq
    simp only [GI.Lang.encPair, Val.list.injEq, List.cons.injEq] at heq
    have e : t' = t := nintSum_injective ((encPerm_injective heq.2.1).symm.trans hpt.symm)
    subst e
    exact h.1
  have hm := map_spec scos_childMap hxs
  show FunAll 𝒫 241 (.list [_, .list (L.map (GI.Lang.encPair labKey))]) _
  refine hm.mono ?_
  rintro w cost ⟨ws, rfl, h2, hc⟩
  have h2' := scosPaste_forall₂ hts h2
  refine ⟨ws, rfl, h2', ?_⟩
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hc
  -- weights
  have hQ := scosPaste_Q n
  have hM := scosPaste_M n c hlen
  have hlw : ws.length = L.length := by
    rw [← h2'.length_eq]
    simpa using congrArg List.length hts.symm
  have wws : (Val.list ws).wt ≤ ws.length * (2 * (700 * (n + n + 1) ^ 6) + 1) + 4 :=
    GI.Lang.wt_list_le_of ws fun a ha => by
      obtain ⟨t, -, hta⟩ := scosPaste_mem_right h2' ha
      exact scosPaste_wt_ans hta
  have wxs : (Val.list (L.map (GI.Lang.encPair labKey))).wt ≤
      (L.map (GI.Lang.encPair labKey)).length * (2 * (22 * (n + n + 1) ^ 6) + 1) + 4 :=
    GI.Lang.wt_list_le_of _ fun v hv => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
      have h1 := wt_list2_le (natList (labKey p.1)) (encPerm p.2)
      have h2 := scosPaste_wt_lab p.1 (hf p hp)
      have h3 := scosPaste_wt_perm p.2
      show (Val.list [natList (labKey p.1), encPerm p.2]).wt ≤ _
      omega
  rw [List.length_map] at wxs
  rw [hlw] at wws
  have wk : kv.wt ≤ 320 * (n + n + 1) ^ 6 := hkv
  have wx := scosPaste_wt_perm (nintSum x)
  have wi := scosPaste_wt_ind Φ
  have wC := wt_list3_le kv (encPerm (nintSum x)) (scosInd Φ)
  have wA := wt_list2_le (.list [kv, encPerm (nintSum x), scosInd Φ])
    (.list (L.map (GI.Lang.encPair labKey)))
  -- the overhead of the map
  have hLQ : L.length * (n + n + 1) ^ 6 + (n + n + 1) ^ 6 ≤ scosPasteM n c := by
    have := hM.2.1; rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have e1 : L.length * (2 * (700 * (n + n + 1) ^ 6) + 1) =
      1400 * (L.length * (n + n + 1) ^ 6) + L.length := by ring
  have e2 : L.length * (2 * (22 * (n + n + 1) ^ 6) + 1) =
      44 * (L.length * (n + n + 1) ^ 6) + L.length := by ring
  have hin : (Val.list [.list [kv, encPerm (nintSum x), scosInd Φ],
      .list (L.map (GI.Lang.encPair labKey))]).wt + (Val.list ws).wt + 1 ≤
      3000 * scosPasteM n c := by
    have := hM.2.2.1
    omega
  have hov : mapK * (L.length + 1) * ((Val.list [.list [kv, encPerm (nintSum x), scosInd Φ],
      .list (L.map (GI.Lang.encPair labKey))]).wt + (Val.list ws).wt + 1) ≤ scosOwnC n c := by
    calc _ ≤ mapK * scosPasteM n c * (3000 * scosPasteM n c) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hM.2.2.1) hin
      _ ≤ scosOwnC n c := by unfold scosOwnC mapK; nlinarith
  have hch1 : 100000 * (n + n + 1) ^ 6 ≤ scosOwnC n c := by
    unfold scosOwnC
    have := Nat.le_self_pow (n := 2) (by omega) (scosPasteM n c)
    nlinarith [hM.1]
  have hsum : L.length * (100000 * (n + n + 1) ^ 6 + TK) ≤ L.length * (scosOwnC n c + TK) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end Prog

end GI.Impl
