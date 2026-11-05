module

public import Workspace.Impl.VsQTSplitM

@[expose] public section

/-!
# The split program for a tuple of local subspaces

On `[lc, Ps, B]` (local bases `P_1, …, P_b` of subspaces, and an orbit bound `B`): the context of
the action, the key of the tuple of spans, the small orbit transporter, the transporters, and the
lows of the partial sums. The value is `vsQSplitV (L.map snd) ks (vsQTLows s (vsQTQs Ps))`;
`vsQT_splitOK` turns the outputs of the transporter into a correct split.

* `vsQTSplE`, `vsQTSplit_spec`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- On `[c, [key, t]]`: the transporter `t`. -/
def vsQTSndE : Expr := .get (arg 1) (.nat 1)

/-- Entries of the local context. -/
def vsQTlcΓ : Expr := .get (.get (arg 0) (.nat 0)) (.nat 0)
def vsQTlcFr : Expr := .get (arg 0) (.nat 1)
def vsQTlcP : Expr := .get (.get (.get (arg 0) (.nat 1)) (.nat 0)) (.nat 0)
def vsQTlcD : Expr := .get (arg 0) (.nat 2)
def vsQTlcHs : Expr := .get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 1)
def vsQTlcN : Expr := .get (.get (.get (arg 0) (.nat 0)) (.nat 1)) (.nat 0)
def vsQTlcW' : Expr := .get (.get (arg 0) (.nat 0)) (.nat 2)

/-- The split program, on `[lc, Ps, B]`. -/
def vsQTSplE (kmp cat appd tl so smp lmp rng : ℕ) : Expr :=
  .letE (mk3 (mk2 vsQTlcΓ vsQTlcFr) vsQTlcP vsQTlcD)
  (.letE (.call appd (mk2 (mk1 (.nat 0)) (.call cat (.call kmp (mk2 (mk2 vsQTlcP vsQTlcD) (arg 1))))))
  (.letE (.call (so + 22) (vsBmk5 (.var 1) (.call tl vsQTlcHs) (.var 2) (arg 2) vsQTlcN))
  (mk4 (.nat 1) (.call smp (mk2 (.nat 0) (.get (.var 3) (.nat 0)))) (.get (.var 3) (.nat 1))
    (.call appd (mk2 (.call lmp (mk2 (mk4 vsQTlcFr vsQTlcP (arg 1) (.length (arg 1)))
        (.call rng (.arith .sub (.length (arg 1)) (.nat 1)))))
      (mk1 vsQTlcW'))))))

/-- The layout of the split program. -/
structure VsQTSplitAt (P : Program) (f kmp kI cat appd tl so fa smp sI lmp lI rng jp jm : ℕ) : Prop where
  hf : P.funs[f]? = some (vsQTSplE kmp cat appd tl so smp lmp rng)
  hkmp : P.HasAt kmp (mapFuns kmp kI)
  hcat : P.HasAt cat (vsWFlatFuns cat)
  happd : P.HasAt appd (appendFuns appd)
  htl : P.HasAt tl (linTailFuns tl)
  hso : P.HasAt so (vsQSotFuns so fa jp jm)
  hsmp : P.HasAt smp (mapFuns smp sI)
  hsI : P.funs[sI]? = some vsQTSndE
  hlmp : P.HasAt lmp (mapFuns lmp lI)
  hrng : P.HasAt rng (rangeFuns rng)

theorem vsQT_wt_gens {S Tm : ℕ} (hS : VsQDSz I S Tm) {gs : List (Perm (Fin I.n))}
    (hl : gs.length ≤ I.n ^ 2 + 4) : (Val.list (gs.map encPerm)).wt ≤ 500 * S ^ 6 := by
  have h1 := wt_list_encPerms_le gs
  have hS1 := hS.one_le
  have hn := hS.n
  have h2 : I.n ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hS2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS1
  have h3 : (gs.length + 1) * (I.n + 1) ≤ (6 * S ^ 2) * S :=
    Nat.mul_le_mul (by omega) (by omega)
  have h4 := Nat.pow_le_pow_left h3 2
  have e : ((6 * S ^ 2) * S) ^ 2 = 36 * S ^ 6 := by ring
  omega

/-- What the split program returns. -/
def VsQTSplOut {s : VsQSt I} (hs : VsQStOK s) (Ps : List (List (List ℕ))) (w : Val) : Prop :=
  ∃ (L : List (VsQTup s × Perm (Fin I.n))) (ks : List (Perm (Fin I.n))),
    w = vsQSplitV (L.map Prod.snd) ks (vsQTLows s (vsQTQs Ps)) ∧
    VsQOrbL (vsQTAct s) s.hs (Ps.map (vsWSp I.p (vsQD s))) L ∧
    gens ks = vsQStabG (vsQTAct_act hs) le_rfl (Ps.map (vsWSp I.p (vsQD s))) ∧ ks.length ≤ I.n ^ 2

set_option maxHeartbeats 16000000 in
/-- **The split program.** -/
theorem vsQTSplit_spec (hps : PointwiseStab) (hm : Membership) {P : Program}
    {f kmp kI cat appd tl so fa smp sI lmp lI rng jp jm key' cat' appd' tk cat'' lift bas
      itm loc phi tl₁ chk mp fI tl' chk' ker img key cat₂ appd₂ Cφ S Tm B : ℕ}
    (H : VsQTSplitAt P f kmp kI cat appd tl so fa smp sI lmp lI rng jp jm)
    (HK : VsQTKeyItemAt P kI key' cat' appd') (HL : VsQTLowAt P lI tk cat'' lift bas)
    (HA : VsQTActAt P fa itm loc phi tl₁ chk mp fI tl' chk' ker img key cat₂ appd₂)
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hps)) (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s) {Ps : List (List (List ℕ))}
    (hPs : ∀ P' ∈ Ps, VsWFit I.p (vsQD s) P') (hbS : Ps.length ≤ S) (hsum : (Ps.map List.length).sum ≤ S)
    (hB : (vsQOrb (vsQTAct s) s.hs (Ps.map (vsWSp I.p (vsQD s)))).ncard ≤ B) :
    FunAll P f (.list [vsQLCV s, vsQTPsV Ps, .nat B]) (fun w c => VsQTSplOut hs Ps w ∧
      c ≤ vsQSotCost hps hm I.n (vsQTS S B) (Cφ + 10 ^ 15 * (S ^ 3 + 1) ^ 7) + 10 ^ 20 * (S ^ 3 + 1) ^ 12 +
        10 ^ 8 * vsQTS S B ^ 4 + 10 ^ 30 * (S ^ 3 + 1) ^ 13) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hS1 := hS.one_le
  have hDd := vsQD_le hs
  have hdS := hS.d
  have hpS := hS.p
  have hnS := hS.n
  set lc := vsQLCV s
  set PsV := vsQTPsV Ps
  set A := Val.list [lc, PsV, .nat B]
  set stV := vsQStV I s
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s)
  set fr0 := Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQD s))]
  have rd : ∀ rest k v, [lc, PsV, Val.nat B][k]? = some v → Det P (A :: rest) (arg k) v (2 * A.wt + k + 5) :=
    fun rest k v hv => Det.arg' (vs := [lc, PsV, Val.nat B]) (rest := rest) hv
  have rl : ∀ rest k v, [stV, frV, .nat (vsQD s), vsFMatsVal (vsQMs s)][k]? = some v →
      Det P (A :: rest) (.get (arg 0) (.nat k)) v _ := fun rest k v hv =>
    Det.get' (rd rest 0 lc rfl) (Det.nat k) hv
  have rs : ∀ rest k v, [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y][k]? =
      some v → Det P (A :: rest) (.get (.get (arg 0) (.nat 0)) (.nat k)) v _ := fun rest k v hv =>
    Det.get' (rl rest 0 stV rfl) (Det.nat k) hv
  have dΓ := fun rest => rs rest 0 _ rfl
  have dfr := fun rest => rl rest 1 frV rfl
  have dD := fun rest => rl rest 2 _ rfl
  have dp : ∀ rest, Det P (A :: rest) vsQTlcP (.nat I.p) _ := fun rest =>
    Det.get' (Det.get' (rl rest 1 frV rfl) (Det.nat 0)
      (show [fr0, vsWVs s.ws', vsWVs (vsQCs s), .list ((vsWFrRows I.p s.ws' (vsQCs s)).map VsRow.val)][0]? =
        some fr0 from rfl)) (Det.nat 0) (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d),
          natList (vsWZ (vsQD s))][0]? = some (.nat I.p) from rfl)
  have dhs : ∀ rest, Det P (A :: rest) vsQTlcHs (.list ((1 :: s.hs).map encPerm)) _ := fun rest =>
    Det.get' (rs rest 1 _ rfl) (Det.nat 1)
      (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? = some (.list ((1 :: s.hs).map encPerm)) from rfl)
  have dn : ∀ rest, Det P (A :: rest) vsQTlcN (.nat I.n) _ := fun rest =>
    Det.get' (rs rest 1 _ rfl) (Det.nat 0)
      (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][0]? = some (.nat I.n) from rfl)
  have dw' := fun rest => rs rest 2 _ rfl
  -- the context of the action
  have dctx := Det.mk3 (Det.mk2 (dΓ []) (dfr [])) (dp []) (dD [])
  have ectx : Val.list [.list [vsQGam I, frV], .nat I.p, .nat (vsQD s)] = vsQTCtx s := rfl
  rw [ectx] at dctx
  set N := S ^ 3
  have hS3 : S ≤ N := Nat.le_self_pow (by norm_num) _
  have hS23 : S ^ 2 ≤ N := Nat.pow_le_pow_right hS1 (by norm_num)
  have hDD : vsQD s * vsQD s + 1 ≤ N := by
    have h1 : vsQD s + 1 ≤ S := by omega
    have h2 := Nat.mul_le_mul h1 h1
    have e : (vsQD s + 1) * (vsQD s + 1) = vsQD s * vsQD s + 2 * vsQD s + 1 := by ring
    have h3 : S * S ≤ N := by rw [← sq]; exact hS23
    omega
  set ys₀ := Ps.map (vsWSp I.p (vsQD s))
  -- the key of the tuple
  set C1 := vsQTCtx s
  set E1 := [A, C1]
  have hkI : ∀ P' ∈ Ps, FunDet P kI (.list [.list [.nat I.p, .nat (vsQD s)], vsWVs P'])
      (natList (vsQTKeyM (vsWSp I.p (vsQD s) P'))) (10 ^ 9 * (N + 1) ^ 6) := fun P' hP' =>
    vsQTKeyItem_spec HK (hpS.trans hS3) hDD (hPs P' hP') (by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hP'); omega)
  have dmk := Det.call (Det.mk2 (Det.mk2 (dp [C1]) (dD [C1])) (rd [C1] 1 PsV rfl))
    (vsQ_map H.hkmp Ps vsWVs (fun P' => natList (vsQTKeyM (vsWSp I.p (vsQD s) P'))) vsWVs_injective hkI)
  set xss := Ps.map fun P' => (vsQTKeyM (vsWSp I.p (vsQD s) P')).map Val.nat
  have ex1 : Val.list (Ps.map fun P' => natList (vsQTKeyM (vsWSp I.p (vsQD s) P'))) =
      Val.list (xss.map Val.list) := by simp [xss, List.map_map]; intro _ _; rfl
  rw [ex1] at dmk
  have ex2 : Val.list xss.flatten = natList (vsQTKey ys₀) := by
    simp [xss, ys₀, natList, vsQTKey, List.flatMap, List.map_flatten, List.map_map]; rfl
  -- weights of keys
  have hk0 := vsQTKey_wt hS hs (ys := ys₀) (by simp [ys₀]; exact hbS)
  have hk0' : (natList (0 :: vsQTKey ys₀)).wt ≤ 20 * (N + 1) ^ 2 := hk0
  have hkl := vsQTKey_length ys₀
  have hkb : (vsQTKey ys₀).length ≤ N := by
    rw [hkl]
    have h1 : vsQD s + 1 ≤ S := by omega
    have h2 := Nat.mul_le_mul h1 h1
    have e : (vsQD s + 1) * (vsQD s + 1) = vsQD s * vsQD s + 2 * vsQD s + 1 := by ring
    have : ys₀.length * (vsQD s * vsQD s + 1) ≤ S * (S * S) := Nat.mul_le_mul (by simp [ys₀]; omega) (by omega)
    have e2 : S * (S * S) = N := by simp only [N]; ring
    omega
  have hkbd : ∀ y ∈ vsQTKey ys₀, y ≤ N := by
    intro y hy
    simp only [vsQTKey, List.mem_flatMap, vsQTKeyM, List.mem_cons] at hy
    obtain ⟨U, -, hy⟩ := hy
    rcases hy with rfl | hy
    · omega
    · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
      have := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas U)
      exact (((this r hr).1 y hy).le.trans hpS).trans hS3
  have wk1 := wt_natList_le_sq hkbd hkb
  have hxi : ∀ v ∈ xss.map Val.list, v.wt ≤ 5 * (N + 1) ^ 2 := by
    intro v hv
    obtain ⟨xs, hxs, rfl⟩ := List.mem_map.mp hv
    obtain ⟨P', -, rfl⟩ := List.mem_map.mp hxs
    exact wt_natList_le_sq (B := N) (xs := vsQTKeyM (vsWSp I.p (vsQD s) P')) (fun y hy => by
      simp only [vsQTKeyM, List.mem_cons] at hy
      rcases hy with rfl | hy
      · omega
      · obtain ⟨r, hr, hy⟩ := List.mem_flatten.mp hy
        have := vsWKey_fit I.prime.one_lt (d := vsQD s) (vsQTBas (vsWSp I.p (vsQD s) P'))
        exact (((this r hr).1 y hy).le.trans hpS).trans hS3) (by rw [vsQTKeyM_len]; omega)
  have wxl := wt_list_le_of (xss.map Val.list) hxi
  have hxl : (xss.map Val.list).length ≤ N := by simp [xss]; omega
  have q13 : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have q34 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q24 : (N + 1) ^ 2 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have wxs : (Val.list (xss.map Val.list)).wt ≤ 20 * (N + 1) ^ 3 := by
    have := Nat.one_le_pow 2 (N + 1) (by omega)
    have h2 : (xss.map Val.list).length * (2 * (5 * (N + 1) ^ 2) + 1) ≤ (N + 1) * (11 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (N + 1) * (11 * (N + 1) ^ 2) = 11 * (N + 1) ^ 3 := by ring
    omega
  have dcat := Det.call dmk (vsWConcat_spec H.hcat (N := N) xss (by simp [xss]; omega)
    (fun xs hxs => by
      obtain ⟨P', -, rfl⟩ := List.mem_map.mp hxs
      rw [List.length_map, vsQTKeyM_len]; omega)
    (by rw [ex2]; omega) (by omega))
  rw [ex2] at dcat
  have kap0 : FunDet P appd (.list [.list [.nat 0], natList (vsQTKey ys₀)]) (natList (0 :: vsQTKey ys₀))
      (10 ^ 6 * (N + 1) ^ 3) := by
    refine (append_spec H.happd [.nat 0] ((vsQTKey ys₀).map Val.nat)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have w2 := wt_list2_le (.list [.nat 0]) (natList (vsQTKey ys₀))
    have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
    have e2' : (Val.list ([Val.nat 0] ++ (vsQTKey ys₀).map Val.nat)).wt = (natList (0 :: vsQTKey ys₀)).wt := rfl
    have e3 : (Val.list [Val.list [Val.nat 0], Val.list ((vsQTKey ys₀).map Val.nat)]).wt =
      (Val.list [.list [.nat 0], natList (vsQTKey ys₀)]).wt := rfl
    have hll : ((vsQTKey ys₀).map Val.nat).length ≤ N := by rw [List.length_map]; exact hkb
    have h4 : (((vsQTKey ys₀).map Val.nat).length + 1) *
        ((Val.list [Val.list [Val.nat 0], Val.list ((vsQTKey ys₀).map Val.nat)]).wt +
          ((vsQTKey ys₀).map Val.nat).length + (Val.list ([Val.nat 0] ++ (vsQTKey ys₀).map Val.nat)).wt + 1) ≤
        (N + 1) * (100 * (N + 1) ^ 2) := Nat.mul_le_mul (by omega) (by
          have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
          omega)
    have e : (N + 1) * (100 * (N + 1) ^ 2) = 100 * (N + 1) ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (((vsQTKey ys₀).map Val.nat).length + 1) * _ = 1000 * ((((vsQTKey ys₀).map Val.nat).length + 1) *
          ((Val.list [Val.list [Val.nat 0], Val.list ((vsQTKey ys₀).map Val.nat)]).wt +
          ((vsQTKey ys₀).map Val.nat).length + (Val.list ([Val.nat 0] ++ (vsQTKey ys₀).map Val.nat)).wt + 1)) := by
            ring
      _ ≤ _ := by omega
  have hb0 : ys₀.length ≤ S := by simp [ys₀]; exact hbS
  set S' := vsQTS S B
  -- weights of the inputs
  have wlc : lc.wt ≤ 10 ^ 6 * S ^ 6 := vsQ_wt_LC hS hs
  have hP1 : ∀ P' ∈ Ps, (vsWVs P').wt ≤ 11 * (N + 1) ^ 3 + 4 := fun P' hP' =>
    wt_vsWVs_le (VsWFit.bnd (hPs P' hP') (hpS.trans hS3) (by omega)) (by
      have := List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hP'); omega)
  have hq3 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have wPs : PsV.wt ≤ 40 * (N + 1) ^ 4 := by
    have := wt_list_le_of (Ps.map vsWVs) (c := 11 * (N + 1) ^ 3 + 4) (by
      intro v hv; obtain ⟨P', hP', rfl⟩ := List.mem_map.mp hv; exact hP1 P' hP')
    rw [List.length_map] at this
    have h2 : Ps.length * (2 * (11 * (N + 1) ^ 3 + 4) + 1) ≤ (N + 1) * (31 * (N + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (N + 1) * (31 * (N + 1) ^ 3) = 31 * (N + 1) ^ 4 := by ring
    have : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    show (Val.list _).wt ≤ _
    omega
  have wBv := wt_nat_le B
  have wA : A.wt ≤ 2 * (lc.wt + PsV.wt + (Val.nat B).wt) + 9 := by
    have := wt_list3_le lc PsV (.nat B); show (Val.list _).wt ≤ _; omega
  have wC1 : C1.wt ≤ 10 ^ 6 * S ^ 3 := by
    have w1 := wt_list2_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s))
    have w2 := wt_list3_le (.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s)]) (.nat I.p) (.nat (vsQD s))
    have := wt_nat_le I.p; have := wt_nat_le (vsQD s)
    have := vsQ_wt_fr hS hs; have := hS.g
    have : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
    show (Val.list _).wt ≤ _
    omega
  have whs := vsQT_wt_gens hS (gs := s.hs) (by have := hs.hsl; omega)
  have hS6N : S ^ 6 ≤ (N + 1) ^ 2 := by
    have : S ^ 6 = N ^ 2 := by simp only [N]; ring
    rw [this]; exact Nat.pow_le_pow_left (by omega) 2
  have hS'N : 10 ^ 7 * (N + 1) ^ 2 ≤ S' := by simp only [S', vsQTS, N]; omega
  have hS'B : B ≤ S' := by simp only [S', vsQTS]; omega
  have q24' : (N + 1) ^ 4 = (N + 1) ^ 2 * (N + 1) ^ 2 := by ring
  have hS'4 : (N + 1) ^ 4 ≤ S' ^ 2 := by
    have := Nat.mul_le_mul (show (N + 1) ^ 2 ≤ S' by omega) (show (N + 1) ^ 2 ≤ S' by omega)
    rw [← q24', ← sq] at this; exact this
  have hS'pos : 1 ≤ S' := by have := Nat.one_le_pow 2 (N + 1) (by omega); omega
  have hS'12 : S' ≤ S' ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS'23 : S' ^ 2 ≤ S' ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hS'34 : S' ^ 3 ≤ S' ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hS'7 : 10 ^ 7 ≤ S' := by have := Nat.one_le_pow 2 (N + 1) (by omega); omega
  have hS'g2 : 10 ^ 7 * S' ≤ S' ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hS'7
  have hS'g3 : 10 ^ 7 * S' ^ 2 ≤ S' ^ 3 :=
    calc 10 ^ 7 * S' ^ 2 ≤ S' * S' ^ 2 := Nat.mul_le_mul_right _ hS'7
      _ = S' ^ 3 := by ring
  have hS'g4 : 10 ^ 7 * S' ^ 3 ≤ S' ^ 4 :=
    calc 10 ^ 7 * S' ^ 3 ≤ S' * S' ^ 3 := Nat.mul_le_mul_right _ hS'7
      _ = S' ^ 4 := by ring
  have HS := vsQT_sotHyp HA hphi hS hs hb0 hB
  have hsot := vsQSot_spec hps hm H.hso hjp hjm (vsQTAct_act hs) HS
  refine FunAll.intro H.hf (EvalAll.letE dctx fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  have dk0 := Det.call (Det.mk2 (Det.mk1 (Det.nat (P := P) (env := E1) 0)) dcat) kap0
  refine EvalAll.letE dk0 fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  set E2 := [A, C1, natList (0 :: vsQTKey ys₀)]
  have dhs' := Det.call (dhs [C1, natList (0 :: vsQTKey ys₀)]) (linTail_spec H.htl ((1 :: s.hs).map encPerm))
  have ehs : Val.list (List.drop 1 ((1 :: s.hs).map encPerm)) = .list (s.hs.map encPerm) := rfl
  rw [ehs] at dhs'
  have din := Det.vsBmk5 (Det.var' (P := P) (env := E2) (i := 1) rfl) dhs'
    (Det.var' (P := P) (env := E2) (i := 2) rfl) (rd [C1, natList (0 :: vsQTKey ys₀)] 2 _ rfl)
    (dn [C1, natList (0 :: vsQTKey ys₀)])
  have edin : Val.list [C1, .list (s.hs.map encPerm), natList (0 :: vsQTKey ys₀), .nat B, .nat I.n] =
    vsQSotIn C1 s.hs vsQTKey ys₀ B := rfl
  rw [edin] at din
  refine EvalAll.letE (Ra := fun w c => ∃ (L : List (VsQTup s × Perm (Fin I.n))) (ks : List (Perm (Fin I.n))),
      w = .list [vsQPairs vsQTKey L, encGroup ks] ∧ VsQOrbL (vsQTAct s) s.hs ys₀ L ∧
      gens ks = vsQStabG (vsQTAct_act hs) le_rfl ys₀ ∧ ks.length ≤ I.n ^ 2 ∧
      c ≤ vsQSotCost hps hm I.n (vsQTS S B) (Cφ + 10 ^ 15 * (S ^ 3 + 1) ^ 7) + 10 ^ 4 * vsQTS S B ^ 4)
    (EvalAll.call_funAll din fun v ca hv => ?_) fun v3 c3 hv3 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine hsot.mono fun w c hw => ?_
    obtain ⟨L, ks, rfl, hL, hks, hksl, hc⟩ := hw
    refine ⟨L, ks, rfl, hL, hks, hksl, ?_⟩
    obtain ⟨hLl, hLp, hLw⟩ := HS.wt_pairs hL
    have wks := wt_encGroup_le_sq (n := I.n) hksl
    have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hnS 6
    have w2 := wt_list2_le (vsQPairs vsQTKey L) (encGroup ks)
    have w5 := wt_list_le [C1, .list (s.hs.map encPerm), natList (0 :: vsQTKey ys₀), .nat B, .nat I.n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at w5
    have := wt_nat_le I.n
    have ein : (vsQSotIn C1 s.hs vsQTKey ys₀ B).wt =
      (Val.list [C1, .list (s.hs.map encPerm), natList (0 :: vsQTKey ys₀), .nat B, .nat I.n]).wt := rfl
    have whs2 : (Val.list (List.drop 1 ((1 :: s.hs).map encPerm))).wt ≤ 500 * S ^ 6 := whs
    have whs1 := vsQT_wt_gens hS (gs := 1 :: s.hs) (by simp; have := hs.hsl; omega)
    have hN6 : (N + 1) ^ 6 = ((N + 1) ^ 2) ^ 3 := by ring
    have hS'3 : 10 ^ 21 * (N + 1) ^ 6 ≤ S' ^ 3 := by
      have := Nat.pow_le_pow_left hS'N 3
      have e : (10 ^ 7 * (N + 1) ^ 2) ^ 3 = 10 ^ 21 * (N + 1) ^ 6 := by ring
      omega
    have hN21 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hlt : linTailCost (Val.list ((1 :: s.hs).map encPerm)).wt ≤ S' ^ 3 := by
      unfold linTailCost
      have h1 : (Val.list ((1 :: s.hs).map encPerm)).wt + 1 ≤ 501 * (N + 1) ^ 2 := by omega
      have h2 := Nat.pow_le_pow_left h1 3
      have e : (501 * (N + 1) ^ 2) ^ 3 = 501 ^ 3 * (N + 1) ^ 6 := by ring
      omega
    have wkey0 : (natList (0 :: vsQTKey ys₀)).wt ≤ 20 * (N + 1) ^ 2 := hk0'
    have hS'4' : S' ≤ S' ^ 4 := hS'12.trans (hS'23.trans hS'34)
    have hS6' : S ^ 6 ≤ S' := by omega
    have hS3' : S ^ 3 ≤ S' := by
      have : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
      omega
    have wsI : (vsQSotIn C1 s.hs vsQTKey ys₀ B).wt ≤ 10 ^ 8 * S' := by
      have := wt_nat_le I.n
      omega
    have wE2 : (Val.list [A, C1, natList (0 :: vsQTKey ys₀)]).wt ≤ 10 ^ 9 * S' ^ 2 := by
      have := wt_list3_le A C1 (natList (0 :: vsQTKey ys₀))
      omega
    have eS2 : S' ^ 2 = vsQTS S B ^ 2 := rfl
    have eS3 : S' ^ 3 = vsQTS S B ^ 3 := rfl
    have eS4 : S' ^ 4 = vsQTS S B ^ 4 := rfl
    have eS1 : S' = vsQTS S B := rfl
    have hn6' : (I.n + 1) ^ 6 ≤ S' := by omega
    have wst : stV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, stV])
    have wGs : (encGroup s.hs).wt < stV.wt := wt_le_wt_list (by simp [stV, vsQStV])
    have eG : (Val.list [Val.nat I.n, Val.list (List.map encPerm (1 :: s.hs))]).wt = (encGroup s.hs).wt := rfl
    omega
  obtain ⟨L, ks, rfl, hL, hks, hksl, hc3⟩ := hv3
  set E3 := [A, C1, natList (0 :: vsQTKey ys₀), Val.list [vsQPairs vsQTKey L, encGroup ks]]
  obtain ⟨hLl, hLp, hLw⟩ := HS.wt_pairs hL
  have dsv : Det P E3 (.var 3) (.list [vsQPairs vsQTKey L, encGroup ks]) _ :=
    Det.var' (P := P) (env := E3) (i := 3) rfl
  have dpairs := Det.get' dsv (Det.nat 0)
    (show [vsQPairs vsQTKey L, encGroup ks][0]? = some (vsQPairs vsQTKey L) from rfl)
  have dks := Det.get' dsv (Det.nat 1) (show [vsQPairs vsQTKey L, encGroup ks][1]? = some (encGroup ks) from rfl)
  -- the transporters
  set enc : VsQTup s × Perm (Fin I.n) → Val := fun q => .list [natList (0 :: vsQTKey q.1), encPerm q.2]
  have hinj : Function.Injective enc := by
    intro q q' he
    simp only [enc, Val.list.injEq, List.cons.injEq, and_true] at he
    obtain ⟨h1, h2⟩ := he
    have h1' := vsQ_natList_injective h1
    exact Prod.ext (vsQTKey_injective (List.cons.inj h1').2) (encPerm_injective h2)
  have hsI : ∀ q ∈ L, FunDet P sI (.list [.nat 0, enc q]) (encPerm q.2) (100 * S' ^ 2) := by
    intro q hq
    refine FunDet.intro H.hsI ((Det.get' (Det.arg' (P := P) (rest := []) (vs := [.nat 0, enc q]) (j := 1) rfl)
      (Det.nat 1) (show [natList (0 :: vsQTKey q.1), encPerm q.2][1]? = some (encPerm q.2) from rfl)).mono ?_)
    have hq2 : (Val.list [natList (0 :: vsQTKey q.1), encPerm q.2]).wt ≤ 16 * S' ^ 2 := hLp q hq
    have w2 := wt_list2_le (.nat 0) (enc q)
    have := wt_le_wt_list (show encPerm q.2 ∈ [natList (0 :: vsQTKey q.1), encPerm q.2] by simp)
    have := wt_nat_le 0; have := wt_nat_le 1
    have ee : (enc q).wt = (Val.list [natList (0 :: vsQTKey q.1), encPerm q.2]).wt := rfl
    have hS'1 : 100 ≤ S' := by simp only [S', vsQTS]; have := Nat.one_le_pow 2 (S ^ 3 + 1) (by omega); omega
    have : S' ≤ S' ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have dts := Det.call (Det.mk2 (Det.nat (P := P) (env := E3) 0) dpairs)
    (vsQ_map H.hsmp L enc (fun q => encPerm q.2) hinj hsI)
  have ets : Val.list (L.map fun q => encPerm q.2) = .list ((L.map Prod.snd).map encPerm) := by
    rw [List.map_map]; rfl
  rw [ets] at dts
  -- the lows
  obtain ⟨hp1, hpN4, hdN4, h'f, hcf, hlf⟩ := vsQ_frOK hS hs
  set N4 := 4 * N
  have hF : VsWFrOK I.p N4 I.d s.ws' (vsQCs s) := ⟨hp1, by omega, by omega, h'f, hcf, by omega⟩
  have hsum' : s.ws'.length + (Ps.map List.length).sum ≤ N4 := by have := hs.wl'; omega
  have hlow : ∀ k ∈ List.range (Ps.length - 1), FunDet P lI (.list [vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps, .nat k])
      (vsWVs (vsQTLowL I.p I.d s.ws' (vsQCs s) Ps k)) (10 ^ 12 * (N4 + 1) ^ 12) := fun k hk =>
    vsQTLow_spec HL I.prime hF hPs hsum' (by omega) (by have := List.mem_range.mp hk; omega)
  set E3' := [C1, natList (0 :: vsQTKey ys₀), Val.list [vsQPairs vsQTKey L, encGroup ks]]
  have dlen := Det.length (rd E3' 1 PsV rfl)
  simp only [List.length_map] at dlen
  have dlc := Det.mk4 (dfr E3') (dp E3') (rd E3' 1 PsV rfl) dlen
  have elc : Val.list [frV, .nat I.p, PsV, .nat Ps.length] = vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps := rfl
  rw [elc] at dlc
  have dk := Det.arith (op := .sub) dlen (Det.nat 1)
  simp only [GI.Machine.BinOp.eval] at dk
  have hrange : FunDet P rng (.nat (Ps.length - 1)) (natList (List.range (Ps.length - 1))) (10 ^ 5 * (N + 1) ^ 3) := by
    refine (range_spec H.hrng (Ps.length - 1)).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have wr : (natList (List.range (Ps.length - 1))).wt ≤ 5 * (N + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => (List.mem_range.mp hy).le.trans (by omega)) (by simp; omega)
    have wk := wt_nat_le (Ps.length - 1)
    have h2 : (Ps.length - 1 + 1) * ((Val.nat (Ps.length - 1)).wt + (Ps.length - 1) +
        (natList (List.range (Ps.length - 1))).wt + 1) ≤ (N + 1) * (10 * (N + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _; omega)
    have e : (N + 1) * (10 * (N + 1) ^ 2) = 10 * (N + 1) ^ 3 := by ring
    simp only [loopModK]
    calc 1000 * (Ps.length - 1 + 1) * _ = 1000 * ((Ps.length - 1 + 1) * ((Val.nat (Ps.length - 1)).wt +
          (Ps.length - 1) + (natList (List.range (Ps.length - 1))).wt + 1)) := by ring
      _ ≤ _ := by omega
  have drng := Det.call dk hrange
  have dlm := Det.call (Det.mk2 dlc drng)
    (vsQ_map H.hlmp (List.range (Ps.length - 1)) Val.nat (fun k => vsWVs (vsQTLowL I.p I.d s.ws' (vsQCs s) Ps k))
      (fun a b h => Val.nat.inj h) hlow)
  set lw := (List.range (Ps.length - 1)).map fun k => vsWVs (vsQTLowL I.p I.d s.ws' (vsQCs s) Ps k)
  have hlwi : ∀ v ∈ lw, v.wt ≤ 11 * (N4 + 1) ^ 3 + 4 := by
    intro v hv
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hv
    have hLf := vsWLift_fit (d := I.d) I.prime.pos h'f (vsQCs s) (Ps.take (Ps.length - 1 - k)).flatten
    have hBf := vsWBas_fit I.prime.pos hLf
    refine wt_vsWVs_le (VsWFit.bnd hBf (by omega) (by omega)) ?_
    haveI : Fact I.p.Prime := ⟨I.prime⟩
    rw [vsQTLowL, vsWBas_length I.prime hLf]
    have := Submodule.finrank_le (R := ZMod I.p) (vsWSp I.p I.d (vsWLift I.p I.d s.ws' (vsQCs s)
      (Ps.take (Ps.length - 1 - k)).flatten))
    simp only [Module.finrank_fin_fun] at this
    omega
  have wlw := wt_list_le_of lw hlwi
  have hlwl : lw.length ≤ N4 := by simp [lw]; omega
  have ww' := wt_vsWVs_le (VsWFit.bnd hs.fit' (show I.p ≤ N4 by omega) (show I.d ≤ N4 by omega))
    (show s.ws'.length ≤ N4 + 1 by have := hs.wl'; omega)
  have q4 : (N4 + 1) ^ 3 ≤ (N4 + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q14 : 1 ≤ (N4 + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have wlw' : (Val.list lw).wt ≤ 40 * (N4 + 1) ^ 4 := by
    have h2 : lw.length * (2 * (11 * (N4 + 1) ^ 3 + 4) + 1) ≤ (N4 + 1) * (31 * (N4 + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (N4 + 1) * (31 * (N4 + 1) ^ 3) = 31 * (N4 + 1) ^ 4 := by ring
    have : 1 ≤ (N4 + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have kapl : FunDet P appd (.list [.list lw, .list [vsWVs s.ws']]) (.list (lw ++ [vsWVs s.ws']))
      (10 ^ 6 * (N4 + 1) ^ 4) := by
    refine (append_spec H.happd lw [vsWVs s.ws']).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
    obtain ⟨rfl, -⟩ := hw
    have w2 := wt_list2_le (.list lw) (.list [vsWVs s.ws'])
    have w1 := wt_list1_le (vsWVs s.ws')
    have wapp : (Val.list (lw ++ [vsWVs s.ws'])).wt ≤ (Val.list lw).wt + 2 * (vsWVs s.ws').wt + 2 :=
      wt_list_snoc_le lw (vsWVs s.ws')
    simp only [loopModK, List.length_cons, List.length_nil]
    omega
  have dap := Det.call (Det.mk2 dlm (Det.mk1 (dw' E3'))) kapl
  have elows : Val.list (lw ++ [vsWVs s.ws']) = vsQLowsV (vsQTLows s (vsQTQs Ps)) := by
    simp only [lw, vsQLowsV, vsQTLows, vsQTQs, vsQTLowL, List.map_append, List.map_map, List.map_cons,
      List.map_nil]
    rfl
  rw [elows] at dap
  have dout := Det.mk4 (Det.nat (P := P) (env := E3) 1) dts dks dap
  refine dout.post fun c hc => ⟨⟨L, ks, rfl, hL, hks, hksl⟩, ?_⟩
  -- the cost
  have eS1 : S' = vsQTS S B := rfl
  have eS2 : S' ^ 2 = vsQTS S B ^ 2 := rfl
  have eS3 : S' ^ 3 = vsQTS S B ^ 3 := rfl
  have eS4 : S' ^ 4 = vsQTS S B ^ 4 := rfl
  have hS'4' : S' ≤ S' ^ 4 := hS'12.trans (hS'23.trans hS'34)
  have hS6' : S ^ 6 ≤ S' := by omega
  have hS3' : S ^ 3 ≤ S' := by
    have : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    omega
  have hN21 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  -- the map of the transporters
  have wts : (Val.list ((L.map Prod.snd).map encPerm)).wt ≤ 10 * S' ^ 2 := by
    have := wt_list_le_of ((L.map Prod.snd).map encPerm) (c := 4 * S ^ 2) (by
      intro v hv
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp hv
      exact hS.wt_perm t)
    simp only [List.length_map] at this
    have hS2' : S ^ 2 ≤ S' := by have : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num); omega
    have h2 : L.length * (2 * (4 * S ^ 2) + 1) ≤ S' * (9 * S') := Nat.mul_le_mul (by omega) (by omega)
    have e : S' * (9 * S') = 9 * S' ^ 2 := by ring
    omega
  have k1 := vsW_mapCost (N := S') (n := L.length) (B := 100 * S' ^ 2) (c := 300) (k := 3)
    (W := (Val.list [.nat 0, vsQPairs vsQTKey L]).wt + (Val.list ((L.map Prod.snd).map encPerm)).wt)
    (by omega) (by
      have : S' ^ 2 ≤ (S' + 1) ^ 3 := (Nat.pow_le_pow_left (by omega) 2).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
      omega) (by
      have w2 := wt_list2_le (.nat 0) (vsQPairs vsQTKey L)
      have := wt_nat_le 0
      have : S' ^ 3 ≤ (S' + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have hLw' : (vsQPairs vsQTKey L).wt ≤ 40 * S' ^ 3 := hLw
      omega)
  have hS'14 : (S' + 1) ^ 4 ≤ 16 * S' ^ 4 := by
    have h1 : (S' + 1) ^ 4 ≤ (2 * S') ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e : (2 * S') ^ 4 = 16 * S' ^ 4 := by ring
    omega
  have e31 : (S' + 1) ^ (3 + 1) = (S' + 1) ^ 4 := rfl
  rw [e31] at k1
  have ets2 : Val.list (L.map fun q => encPerm q.2) = .list ((L.map Prod.snd).map encPerm) := ets
  -- the map of the lows
  have hN4 : (N4 + 1) ^ 13 ≤ 4 ^ 13 * (N + 1) ^ 13 := by
    have h1 : N4 + 1 ≤ 4 * (N + 1) := by omega
    have := Nat.pow_le_pow_left h1 13
    have e : (4 * (N + 1)) ^ 13 = 4 ^ 13 * (N + 1) ^ 13 := by ring
    omega
  have k2 := vsW_mapCost (N := N4) (n := (List.range (Ps.length - 1)).length) (B := 10 ^ 12 * (N4 + 1) ^ 12)
    (c := 10 ^ 12) (k := 12)
    (W := (Val.list [vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps, .list ((List.range (Ps.length - 1)).map Val.nat)]).wt +
      (Val.list lw).wt) (by simp; omega) le_rfl (by
      have wctx : (vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps).wt ≤ 10 ^ 4 * (N4 + 1) ^ 4 := by
        have := wt_list4_le (vsWFrVal I.p I.d s.ws' (vsQCs s)) (.nat I.p) (vsQTPsV Ps) (.nat Ps.length)
        have ePs : PsV.wt = (vsQTPsV Ps).wt := rfl
        have := wt_vsWFrVal_le hF
        have := wt_nat_le I.p; have := wt_nat_le Ps.length
        have : (N + 1) ^ 4 ≤ (N4 + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
        have : (N4 + 1) ^ 3 ≤ (N4 + 1) ^ 4 := q4
        have efr : frV.wt = (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt := rfl
        show (Val.list _).wt ≤ _
        omega
      have wr : (Val.list ((List.range (Ps.length - 1)).map Val.nat)).wt ≤ 5 * (N4 + 1) ^ 2 :=
        wt_natList_le_sq (xs := List.range (Ps.length - 1)) (fun y hy => (List.mem_range.mp hy).le.trans (by omega))
          (by simp; omega)
      have w2 := wt_list2_le (vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps) (.list ((List.range (Ps.length - 1)).map Val.nat))
      have : (N4 + 1) ^ 2 ≤ (N4 + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
      have : (N4 + 1) ^ 4 ≤ (N4 + 1) ^ 12 := Nat.pow_le_pow_right (by omega) (by omega)
      omega)
  have e121 : (N4 + 1) ^ (12 + 1) = (N4 + 1) ^ 13 := rfl
  rw [e121] at k2
  have hN13 : (N + 1) ^ 12 ≤ (N + 1) ^ 13 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN413 : (N4 + 1) ^ 4 ≤ (N4 + 1) ^ 13 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN43 : (N + 1) ^ 3 ≤ (N + 1) ^ 13 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN63 : (N + 1) ^ 6 ≤ (N + 1) ^ 13 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN23 : (N + 1) ^ 2 ≤ (N + 1) ^ 13 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN4_13 : (N4 + 1) ^ 13 ≤ 4 ^ 13 * (N + 1) ^ 13 := hN4
  have eN : (S ^ 3 + 1) ^ 13 = (N + 1) ^ 13 := rfl
  have eN12 : (S ^ 3 + 1) ^ 12 = (N + 1) ^ 12 := rfl
  have wlows : (vsQLowsV (vsQTLows s (vsQTQs Ps))).wt ≤ 100 * (N4 + 1) ^ 4 := by
    rw [← elows]
    have := wt_list_snoc_le lw (vsWVs s.ws')
    omega
  have wks := wt_encGroup_le_sq (n := I.n) hksl
  have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hnS 6
  have wout := wt_list4_le (.nat 1) (.list ((L.map Prod.snd).map encPerm)) (encGroup ks)
    (vsQLowsV (vsQTLows s (vsQTQs Ps)))
  have eout : (vsQSplitV (L.map Prod.snd) ks (vsQTLows s (vsQTQs Ps))).wt =
      (Val.list [.nat 1, .list ((L.map Prod.snd).map encPerm), encGroup ks,
        vsQLowsV (vsQTLows s (vsQTQs Ps))]).wt := rfl
  have hc3' : c3 ≤ vsQSotCost hps hm I.n S' (Cφ + 10 ^ 15 * (N + 1) ^ 7) + 10 ^ 4 * S' ^ 4 := hc3
  have wst : stV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, stV])
  have wfrl : frV.wt < lc.wt := wt_le_wt_list (by simp [lc, vsQLCV, frV])
  have wGs : (encGroup s.hs).wt < stV.wt := wt_le_wt_list (by simp [stV, vsQStV])
  have wΓs : (vsQGam I).wt < stV.wt := wt_le_wt_list (by simp [stV, vsQStV])
  have wfr0 : fr0.wt < frV.wt := wt_le_wt_list (by simp [frV, vsWFrVal, fr0])
  have eG : (Val.list [Val.nat I.n, Val.list (List.map encPerm (1 :: s.hs))]).wt = (encGroup s.hs).wt := rfl
  have ews' : (vsWVs s.ws').wt < stV.wt := wt_le_wt_list (by simp [stV, vsQStV])
  have efr0 : (Val.list [Val.nat I.p, Val.nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQD s))]).wt = fr0.wt := rfl
  have wΓfr := wt_list2_le (vsQGam I) frV
  have wpd := wt_list2_le (Val.nat I.p) (Val.nat (vsQD s))
  have wpdP := wt_list2_le (Val.list [Val.nat I.p, Val.nat (vsQD s)]) PsV
  have := wt_nat_le I.p; have := wt_nat_le (vsQD s); have := wt_nat_le Ps.length
  have := wt_nat_le (Ps.length - 1); have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have w0l : (Val.list [Val.nat 0]).wt ≤ 10 := by decide
  have w0k := wt_list2_le (Val.list [Val.nat 0]) (natList (vsQTKey ys₀))
  have wctx : (vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps).wt ≤ 10 ^ 4 * (N4 + 1) ^ 4 := by
    have := wt_list4_le (vsWFrVal I.p I.d s.ws' (vsQCs s)) (.nat I.p) (vsQTPsV Ps) (.nat Ps.length)
    have ePs : PsV.wt = (vsQTPsV Ps).wt := rfl
    have := wt_vsWFrVal_le hF
    have : (N + 1) ^ 4 ≤ (N4 + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have : (N4 + 1) ^ 3 ≤ (N4 + 1) ^ 4 := q4
    have efr : frV.wt = (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt := rfl
    show (Val.list _).wt ≤ _
    omega
  have wr : (natList (List.range (Ps.length - 1))).wt ≤ 5 * (N4 + 1) ^ 2 :=
    wt_natList_le_sq (xs := List.range (Ps.length - 1)) (fun y hy => (List.mem_range.mp hy).le.trans (by omega))
      (by simp; omega)
  have wcr := wt_list2_le (vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps) (natList (List.range (Ps.length - 1)))
  have er : (Val.list ((List.range (Ps.length - 1)).map Val.nat)).wt = (natList (List.range (Ps.length - 1))).wt := rfl
  have ek1 : (Val.list [Val.nat 0, Val.list (List.map enc L)]).wt = (Val.list [.nat 0, vsQPairs vsQTKey L]).wt := rfl
  have wp0 := wt_list2_le (.nat 0) (vsQPairs vsQTKey L)
  have wpk := wt_list2_le (vsQPairs vsQTKey L) (encGroup ks)
  have wxsl : (Val.list (xss.map Val.list)).wt ≤ 20 * (N + 1) ^ 3 := wxs
  have k0 := vsW_mapCost (N := N) (n := Ps.length) (B := 10 ^ 9 * (N + 1) ^ 6) (c := 10 ^ 9) (k := 6)
    (W := (Val.list [Val.list [Val.nat I.p, Val.nat (vsQD s)], Val.list (List.map vsWVs Ps)]).wt +
      (Val.list (xss.map Val.list)).wt) (by omega) le_rfl (by
      have ePs : PsV.wt = (Val.list (List.map vsWVs Ps)).wt := rfl
      have : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      have : (N + 1) ^ 3 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      have := wt_list2_le (Val.list [Val.nat I.p, Val.nat (vsQD s)]) (Val.list (List.map vsWVs Ps))
      omega)
  have e61 : (N + 1) ^ (6 + 1) = (N + 1) ^ 7 := rfl
  rw [e61] at k0
  have hN7 : (N + 1) ^ 7 ≤ (N + 1) ^ 13 := Nat.pow_le_pow_right (by omega) (by omega)
  have wA' : A.wt ≤ 10 ^ 8 * S' ^ 2 := by
    clear * - wA wlc wPs wBv hS'B hS6' hS'4 hS'12 hS'pos
    omega
  have wlc' : lc.wt ≤ 10 ^ 6 * S' := by clear * - wlc hS6'; omega
  have tA : stV.wt ≤ 10 ^ 6 * S' := by clear * - wst wlc'; omega
  have tB : frV.wt ≤ 10 ^ 6 * S' := by clear * - wfrl wlc'; omega
  have tC : C1.wt ≤ 10 ^ 6 * S' := by clear * - wC1 hS3'; omega
  have tD : (Val.list [vsQGam I, frV]).wt ≤ 10 ^ 7 * S' := by clear * - wΓfr wΓs tA tB; omega
  have tE : fr0.wt ≤ 10 ^ 6 * S' := by clear * - wfr0 tB; omega
  have tF : (Val.nat I.p).wt ≤ S' + 2 := by
    have h1 := wt_nat_le I.p
    have h2 : I.p ≤ S := hpS
    have h3 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
    have h4 : S ^ 3 ≤ S' := hS3'
    clear * - h1 h2 h3 h4
    omega
  have tG : (Val.nat (vsQD s)).wt ≤ S' + 2 := by
    have h1 := wt_nat_le (vsQD s)
    have h2 : vsQD s ≤ S := by omega
    have h3 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
    have h4 : S ^ 3 ≤ S' := hS3'
    clear * - h1 h2 h3 h4
    omega
  have t1 : c1 ≤ 10 ^ 10 * S' ^ 2 := by
    clear * - hc1 wA' tA tB tC tD tE tF tG wΓs efr0 hS'12 hS'pos
    omega
  have hN67 : (N + 1) ^ 6 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN37 : (N + 1) ^ 3 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN27 : (N + 1) ^ 2 ≤ (N + 1) ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  have ePs2 : PsV.wt = (Val.list (List.map vsWVs Ps)).wt := rfl
  have ewk : (natList (vsQTKey ys₀)).wt ≤ 5 * (N + 1) ^ 2 := wk1
  have t2 : c2 ≤ 10 ^ 10 * S' ^ 2 + 10 ^ 13 * (N + 1) ^ 7 := by
    clear * - hc2 wA' tB tE tF tG wpd wpdP k0 wxs hN67 hN37 hN27 ewk w0k hk0' w0l efr0 ePs2 wPs hS'4 hS'12 hS'pos
    omega
  have k1' : L.length * (100 * S' ^ 2) + mapK * (L.length + 1) *
      ((Val.list [Val.nat 0, Val.list (List.map enc L)]).wt +
        (Val.list (List.map encPerm (List.map Prod.snd L))).wt + 1) ≤ 1001 * 300 * (S' + 1) ^ 4 := k1
  have hLw' : (vsQPairs vsQTKey L).wt ≤ 40 * S' ^ 3 := hLw
  have hc3'' := hc3'
  clear_value S'
  have wks' : (encGroup ks).wt ≤ 320 * S' := by
    have := wt_encGroup_le_sq (n := I.n) hksl
    have hn6 : (I.n + 1) ^ 6 ≤ S ^ 6 := Nat.pow_le_pow_left hnS 6
    omega
  have w1w := wt_list1_le (vsWVs s.ws')
  have wlww := wt_list2_le (Val.list lw) (Val.list [vsWVs s.ws'])
  have ww'2 : (vsWVs s.ws').wt ≤ lc.wt := le_of_lt (lt_trans ews' wst)
  have q4S : (N4 + 1) ^ 4 ≤ (N4 + 1) ^ 13 := hN413
  have hN4b : (N4 + 1) ^ 13 ≤ 4 ^ 13 * (N + 1) ^ 13 := hN4
  have wlow2 : (vsQLowsV (vsQTLows s (vsQTQs Ps))).wt ≤ 100 * (N4 + 1) ^ 4 := wlows
  have hbS' : Ps.length ≤ S' := by
    have : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have q24N4 : (N4 + 1) ^ 2 ≤ (N4 + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have wv := wt_nat_le (Ps.length - 1)
  have hk13 : 1 ≤ (N + 1) ^ 13 := Nat.one_le_pow _ _ (by omega)
  have u1 : L.length * (100 * S' ^ 2) + mapK * (L.length + 1) *
      ((Val.list [Val.nat 0, Val.list (List.map enc L)]).wt +
        (Val.list (List.map encPerm (List.map Prod.snd L))).wt + 1) ≤ 5 * 10 ^ 6 * S' ^ 4 := by
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 k1' hS'14; omega
  have u2 : (Val.list [vsQPairs vsQTKey L, encGroup ks]).wt ≤ 100 * S' ^ 3 := by
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wpk hLw' wks' hS'12 hS'23 hS'pos; omega
  have u3 : (Val.list [Val.nat 0, vsQPairs vsQTKey L]).wt ≤ 100 * S' ^ 3 := by
    have := wt_nat_le 0
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wp0 hLw' this hS'23 hS'12 hS'pos; omega
  have u3' : (Val.list [Val.nat 0, Val.list (List.map enc L)]).wt ≤ 100 * S' ^ 3 := u3
  have u4 : (List.range (Ps.length - 1)).length * (10 ^ 12 * (N4 + 1) ^ 12) + mapK * ((List.range (Ps.length - 1)).length + 1) *
      ((Val.list [vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps, Val.list (List.map Val.nat (List.range (Ps.length - 1)))]).wt +
        (Val.list lw).wt + 1) ≤ 10 ^ 23 * (N + 1) ^ 13 := by
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 k2 hN4b; omega
  have u5 : (vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps).wt ≤ 10 ^ 12 * (N + 1) ^ 13 := by
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wctx q4S hN4b; omega
  have u14 : (natList (List.range (Ps.length - 1))).wt ≤ 10 ^ 9 * (N + 1) ^ 13 := by clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wr q24N4 q4S hN4b; omega
  have u6 : (Val.list [vsQTLowCtx I.p I.d s.ws' (vsQCs s) Ps, natList (List.range (Ps.length - 1))]).wt ≤
      10 ^ 15 * (N + 1) ^ 13 := by
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wcr u5 u14; omega
  have u7 : (Val.list lw).wt ≤ 10 ^ 10 * (N + 1) ^ 13 := by clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wlw' q4S hN4b; omega
  have u8 : (Val.list [Val.list lw, Val.list [vsWVs s.ws']]).wt ≤ 10 ^ 11 * (N + 1) ^ 13 + 10 * lc.wt + 100 := by
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wlww u7 w1w ww'2; omega
  have u9 : (vsQLowsV (vsQTLows s (vsQTQs Ps))).wt ≤ 10 ^ 10 * (N + 1) ^ 13 := by
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wlow2 q4S hN4b; omega
  have u10 : (Val.list [Val.nat 1, Val.list (List.map encPerm (List.map Prod.snd L)), encGroup ks,
      vsQLowsV (vsQTLows s (vsQTQs Ps))]).wt ≤ 10 ^ 11 * (N + 1) ^ 13 + 10 ^ 4 * S' ^ 2 := by
    have := wt_nat_le 1
    clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 wout u9 wts wks' this hS'12; omega
  have u11 : 10 ^ 6 * (N4 + 1) ^ 4 ≤ 10 ^ 21 * (N + 1) ^ 13 := by clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 q4S hN4b; omega
  have u12 : stV.wt ≤ 10 ^ 6 * S' := tA
  have u13 : lc.wt ≤ 10 ^ 6 * S' := wlc'
  have u15 : 10 ^ 5 * (N + 1) ^ 3 ≤ 10 ^ 5 * (N + 1) ^ 13 := by clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 hN43; omega
  have u16 : (Val.list [vsWVs s.ws']).wt ≤ 10 * lc.wt + 10 := by clear * - hk13 hS'g2 hS'g3 hS'g4 hS'7 w1w ww'2; omega
  have u17 : fr0.wt ≤ 10 ^ 6 * S' := tE
  have u18 : S' ^ 3 ≤ S' ^ 4 := hS'34
  have u19 : S' ^ 2 ≤ S' ^ 4 := hS'23.trans hS'34
  have t4 : c ≤ 10 ^ 7 * S' ^ 4 + 10 ^ 28 * (N + 1) ^ 13 := by
    clear * - hk13 hc u1 u2 u3 u3' u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 wA' tB tF hbS' wv
      wts wks' hS'4' hS'g2 hS'g3 hS'g4 hS'pos ww'2 hLw' efr0
    omega
  have hN713 : (N + 1) ^ 7 ≤ (N + 1) ^ 13 := Nat.pow_le_pow_right (by omega) (by omega)
  have hv2 : S' ^ 2 ≤ S' ^ 4 := hS'23.trans hS'34
  clear * - t1 t2 hc3' t4 u10 hN713 hv2 hS'g2 hS'g3 hS'g4 hN13 hk13 eS4
  omega

end GI.Impl
