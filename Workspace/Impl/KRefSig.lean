import Workspace.Impl.KRefRound

/-!
# The signature code of one tuple

On `[[A, B, VAll, range M], nb]`, the body `krefSigF` computes, for the tuple `x` of `nb`:
1. its vector codes (the module `vcs` on the update indices `nb[3]`);
2. their ranks among all vector codes `VAll` (`ranks`);
3. for each `u < M`, how many points `z` have rank `u` (`cnts`);
4. the Horner code of the signature `[col x] ++ pat x ++ (colors of x ∘ τ) ++ counts`, in three
   steps of `hor`.
The result is `krefHorner B (krefSig col β x)` (`kref_sigF`).
-/

namespace GI.Impl

open GI.Lang GI.Cited
open GI.Machine (len)

variable {n k : ℕ}

/-- The signature body. -/
def krefSigF (look hor ranks cnts vcs : ℕ) : Expr :=
  .letE (.call vcs (mk2 (mk2 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))) (.get (arg 1) (.nat 3))))
   (.letE (.call ranks (mk2 (.get (arg 0) (.nat 2)) (.var 1)))
    (.letE (.call cnts (mk2 (.var 2) (.get (arg 0) (.nat 3))))
     (.letE (.call hor (mk3 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1))
        (.get (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0)))))
      (.letE (.call hor (mk3 (.get (arg 0) (.nat 1))
          (.call look (mk2 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 2)))) (.var 4)))
        (.call hor (mk3 (.get (arg 0) (.nat 1)) (.var 3) (.var 5)))))))

/-- Where the modules used by the signature body sit. -/
structure KrefSigAt (P : Program) (look hor ranks cnts vcs : ℕ) : Prop where
  hlook : P.HasAt look (krefLookFuns look)
  hhor : P.HasAt hor (krefHorFuns hor)
  hranks : P.HasAt ranks (krefRanksFuns ranks)
  hcnts : P.HasAt cnts (krefCntsFuns cnts)
  hvcs : P.HasAt vcs (krefVcsFuns vcs look hor)

def krefSigK : ℕ := 30 * (krefVcsK + krefRanksK + krefCntsK + 3 * krefHorK + krefLookK) + 100000

/-- The context of the signature body. -/
def krefSigCtx (col : KCol n k) (β : Bool) : Val :=
  .list [natList (krefAv col β), .nat (krefB n k), natList (krefVAll col),
    natList (List.range (krefM n k))]

section Sig

variable {col : KCol n k} (hs : KrefSmall col)

include hs

theorem kref_wt_sigCtx (β : Bool) : (krefSigCtx col β).wt ≤ 150 * krefX n k ^ 4 := by
  have h := wt_list4_le (natList (krefAv col β)) (.nat (krefB n k)) (natList (krefVAll col))
    (natList (List.range (krefM n k)))
  have := kref_wt_Av hs β; have := kref_wt_B hs; have := kref_wt_VAll hs
  have := kref_wt_range (n := n) (k := k) (kref_M_le hs)
  obtain ⟨hX2, hX12, hX23, hX34, -⟩ := kref_X4 (n := n) (k := k)
  unfold krefSigCtx
  omega

theorem kref_wt_tauCols (β : Bool) (x : Fin k → Fin n) :
    (natList (krefTauCols col β x)).wt ≤ 10 * krefX n k ^ 2 := by
  have h := kref_wt_natList_C (xs := krefTauCols col β x) (C := 3 * krefX n k) (fun a ha => by
    obtain ⟨τ, -, rfl⟩ := List.mem_map.mp ha; exact kref_wt_col hs β _)
  have hl : (krefTauCols col β x).length = k ^ k := by simp [krefTauCols, length_krefTups]
  rw [hl] at h
  obtain ⟨hX2, hX12, -, -, -⟩ := kref_X4 (n := n) (k := k)
  have := @kk_le_krefX n k
  have : k ^ k * (3 * krefX n k) ≤ 3 * krefX n k ^ 2 := by rw [sq]; nlinarith
  omega

omit hs in
theorem kref_hornerFrom_le_self {B : ℕ} (hB : 1 ≤ B) (a : ℕ) (l : List ℕ) :
    a ≤ krefHornerFrom B a l := kref_hornerFrom_le_append hB a [] l

/-- **The signature code of one tuple.** -/
theorem kref_sigF {P : Program} {g look hor ranks cnts vcs : ℕ}
    (hg : P.funs[g]? = some (krefSigF look hor ranks cnts vcs))
    (hat : KrefSigAt P look hor ranks cnts vcs) (β : Bool) (x : Fin k → Fin n) :
    FunDet P g (.list [krefSigCtx col β, krefNbVal x])
      (.nat (krefHorner (krefB n k) (krefSig col β x))) (krefSigK * (krefZ n k + 1) ^ 5) := by
  obtain ⟨hX2, hX12, hX23, hX34, hZ⟩ := kref_X4 (n := n) (k := k)
  have hB1 : 1 ≤ krefB n k := by unfold krefB; omega
  have hM := kref_M_le hs
  -- weights
  have wAB := kref_wt_ctxAB hs β
  have wA := kref_wt_Av hs β
  have wB := kref_wt_B hs
  have wVA := kref_wt_VAll hs
  have wR := kref_wt_range (n := n) (k := k) hM
  have wvc := kref_wt_vcs hs β x
  have wrl := kref_wt_rl hs β x
  have wcn := kref_wt_counts hs β x
  have wpat := kref_wt_pat x
  have wtid := kref_wt_tidx x
  have wtau := kref_wt_tauCols hs β x
  have wupd := kref_wt_upd x
  have wsc := kref_wt_scode hs β x
  have wctx := kref_wt_sigCtx hs β
  have wnb := kref_wt_nbVal x
  have hlenVA : (krefVAll col).length + 2 ≤ krefZ n k := by rw [length_krefVAll]; omega
  have hnZ : n ≤ krefZ n k := n_le_krefX.trans X_le_Z
  -- the codes
  set B := krefB n k with hBdef
  set c0 := col β x with hc0
  set h1 := krefHornerFrom B c0 (krefPat x) with hh1
  set h2 := krefHornerFrom B h1 (krefTauCols col β x) with hh2
  have hfin : krefHornerFrom B h2 (krefCounts col β x) = krefHorner B (krefSig col β x) :=
    kref_sig_horner col β x
  have l1 : h1 ≤ h2 := kref_hornerFrom_le_self hB1 _ _
  have l2 : h2 ≤ krefHorner B (krefSig col β x) := hfin ▸ kref_hornerFrom_le_self hB1 _ _
  have w1 : (Val.nat h1).wt ≤ 9 * krefX n k ^ 3 := (kref_wt_nat_mono (l1.trans l2)).trans wsc
  have w2 : (Val.nat h2).wt ≤ 9 * krefX n k ^ 3 := (kref_wt_nat_mono l2).trans wsc
  have wc0 : (Val.nat c0).wt ≤ 3 * krefX n k := kref_wt_col hs β x
  -- the module calls
  have cvc := kref_vcs hat.hvcs hat.hlook hat.hhor (Us := krefUpd x) (Y := krefZ n k) hB1
    (by omega) (kref_vcOK hs β x) (by omega)
  rw [kref_vcs_eq] at cvc
  have crl := kref_ranks hat.hranks (L := krefVAll col) (qs := krefVcs col β x) (Y := krefZ n k)
    (by omega) (by omega) hlenVA
  rw [kref_rl_eq] at crl
  have ccn := kref_cnts hat.hcnts (rl := krefRl col β x) (M := krefM n k) (Y := krefZ n k)
    (fun a ha => by
      obtain ⟨z, rfl⟩ := List.mem_ofFn.mp ha
      have := krefRl_lt col β x z; omega)
    (by simp [krefRl]; omega) (by omega) (by omega) (by omega)
  have ccn' : FunDet P cnts (.list [natList (krefRl col β x), natList (List.range (krefM n k))])
      (natList (krefCounts col β x)) (krefCntsK * (krefZ n k + 1) ^ 5) := ccn
  have hw1Z : (Val.nat h1).wt ≤ krefZ n k := by omega
  have hw2Z : (Val.nat h2).wt ≤ krefZ n k := by omega
  have hwsZ : (Val.nat (krefHorner B (krefSig col β x))).wt ≤ krefZ n k := by omega
  have ch1 : FunDet P hor (.list [.nat B, natList (krefPat x), .nat c0]) (.nat h1)
      (krefHorK * (krefZ n k + 1) ^ 3) :=
    kref_hor hat.hhor (B := B) (a := c0) (ds := krefPat x) (Y := krefZ n k) hB1
      (by omega) hw1Z (by omega)
  have clk := kref_look hat.hlook (T := krefAv col β) (is := krefTidx x) (Y := krefZ n k)
    (fun i hi => by
      obtain ⟨τ, -, rfl⟩ := List.mem_map.mp hi
      rw [length_krefAv]; exact krefIdx_lt _) (by omega) (by omega)
  rw [kref_look_tidx] at clk
  have ch2 : FunDet P hor (.list [.nat B, natList (krefTauCols col β x), .nat h1]) (.nat h2)
      (krefHorK * (krefZ n k + 1) ^ 3) :=
    kref_hor hat.hhor (B := B) (a := h1) (ds := krefTauCols col β x) (Y := krefZ n k)
      hB1 (by omega) hw2Z (by omega)
  have ch3 := kref_hor hat.hhor (B := B) (a := h2) (ds := krefCounts col β x) (Y := krefZ n k)
    hB1 (by omega) (by rw [hfin]; exact hwsZ) (by omega)
  rw [hfin] at ch3
  -- the environment
  have hWV : (Val.list [krefSigCtx col β, krefNbVal x]).wt ≤ krefZ n k := by
    have := wt_list2_le (krefSigCtx col β) (krefNbVal x); omega
  set V : List Val := [krefSigCtx col β, krefNbVal x] with hV
  have gA : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 0) (.nat 0))
      (natList (krefAv col β)) (3 * (Val.list V).wt + 0 + 0 + 9) := fun _ => Det.arg2 rfl rfl
  have gB : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 0) (.nat 1))
      (.nat B) (3 * (Val.list V).wt + 0 + 1 + 9) := fun _ => Det.arg2 rfl rfl
  have gVA : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 0) (.nat 2))
      (natList (krefVAll col)) (3 * (Val.list V).wt + 0 + 2 + 9) := fun _ => Det.arg2 rfl rfl
  have gR : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 0) (.nat 3))
      (natList (List.range (krefM n k))) (3 * (Val.list V).wt + 0 + 3 + 9) :=
    fun _ => Det.arg2 rfl rfl
  have gI : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 1) (.nat 0))
      (.nat (krefIdx x)) (3 * (Val.list V).wt + 1 + 0 + 9) := fun _ => Det.arg2 rfl rfl
  have gP : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 1) (.nat 1))
      (natList (krefPat x)) (3 * (Val.list V).wt + 1 + 1 + 9) := fun _ => Det.arg2 rfl rfl
  have gT : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 1) (.nat 2))
      (natList (krefTidx x)) (3 * (Val.list V).wt + 1 + 2 + 9) := fun _ => Det.arg2 rfl rfl
  have gU : ∀ (rest : List Val), Det P (.list V :: rest) (.get (arg 1) (.nat 3))
      (.list ((krefUpd x).map natList)) (3 * (Val.list V).wt + 1 + 3 + 9) :=
    fun _ => Det.arg2 rfl rfl
  -- step 1: vector codes
  have s1 := Det.call (Det.mk2 (Det.mk2 (gA []) (gB [])) (gU [])) cvc
  -- step 2: ranks
  set E2 : List Val := [.list V, natList (krefVcs col β x)] with hE2
  have v1 : Det P E2 (.var 1) (natList (krefVcs col β x)) ((natList (krefVcs col β x)).wt + 1) :=
    Det.var' rfl
  have s2 := Det.call (Det.mk2 (gVA _) v1) crl
  -- step 3: counts
  set E3 : List Val := E2 ++ [natList (krefRl col β x)] with hE3
  have v2 : Det P E3 (.var 2) (natList (krefRl col β x)) ((natList (krefRl col β x)).wt + 1) :=
    Det.var' rfl
  have s3 := Det.call (Det.mk2 v2 (gR _)) ccn'
  -- step 4: the first code
  set E4 : List Val := E3 ++ [natList (krefCounts col β x)] with hE4
  have hidx := kref_natList_get (l := krefAv col β) (r := krefIdx x)
    (by rw [length_krefAv]; exact krefIdx_lt x)
  rw [kref_Av_getD] at hidx
  have s4a := Det.get' (gA (rest := [natList (krefVcs col β x), natList (krefRl col β x),
    natList (krefCounts col β x)])) (gI _) hidx
  have s4 := Det.call (Det.mk3 (gB _) (gP _) s4a) ch1
  -- step 5: the second code
  set E5 : List Val := E4 ++ [.nat h1] with hE5
  have s5a := Det.call (Det.mk2 (gA (rest := [natList (krefVcs col β x),
    natList (krefRl col β x), natList (krefCounts col β x), .nat h1])) (gT _)) clk
  have v4 : Det P E5 (.var 4) (.nat h1) ((Val.nat h1).wt + 1) := Det.var' rfl
  have s5 := Det.call (Det.mk3 (gB _) s5a v4) ch2
  -- step 6: the last code
  set E6 : List Val := E5 ++ [.nat h2] with hE6
  have v3 : Det P E6 (.var 3) (natList (krefCounts col β x))
      ((natList (krefCounts col β x)).wt + 1) := Det.var' rfl
  have v5 : Det P E6 (.var 5) (.nat h2) ((Val.nat h2).wt + 1) := Det.var' rfl
  have s6 := Det.call (Det.mk3 (gB (rest := [natList (krefVcs col β x),
    natList (krefRl col β x), natList (krefCounts col β x), .nat h1, .nat h2])) v3 v5) ch3
  have hall := Det.letE s1 (Det.letE s2 (Det.letE s3 (Det.letE s4 (Det.letE s5 s6))))
  refine FunDet.intro hg (hall.mono ?_)
  -- the cost
  have := wt_list2_le (.list [natList (krefAv col β), .nat B]) (.list ((krefUpd x).map natList))
  have := wt_list2_le (natList (krefVAll col)) (natList (krefVcs col β x))
  have := wt_list2_le (natList (krefRl col β x)) (natList (List.range (krefM n k)))
  have := wt_list3_le (.nat B) (natList (krefPat x)) (.nat c0)
  have := wt_list2_le (natList (krefAv col β)) (natList (krefTidx x))
  have := wt_list3_le (.nat B) (natList (krefTauCols col β x)) (.nat h1)
  have := wt_list3_le (.nat B) (natList (krefCounts col β x)) (.nat h2)
  have := wt_nat_le (krefIdx x)
  have := (krefIdx_lt x).le.trans (@N_le_krefX n k)
  have ec1 : (Val.nat (col β x)).wt = (Val.nat c0).wt := rfl
  have ec2 : (Val.list [Val.nat B, natList (krefPat x), Val.nat (col β x)]).wt =
      (Val.list [Val.nat B, natList (krefPat x), Val.nat c0]).wt := rfl
  have hT : krefZ n k + 1 ≤ (krefZ n k + 1) ^ 5 := kref_le_pow (by norm_num)
  have p3 : (krefZ n k + 1) ^ 3 ≤ (krefZ n k + 1) ^ 5 := kref_pow_mono (by norm_num)
  have q1 : krefHorK * (krefZ n k + 1) ^ 3 ≤ krefHorK * (krefZ n k + 1) ^ 5 :=
    Nat.mul_le_mul_left _ p3
  have q2 : krefLookK * (krefZ n k + 1) ^ 3 ≤ krefLookK * (krefZ n k + 1) ^ 5 :=
    Nat.mul_le_mul_left _ p3
  have e : krefSigK * (krefZ n k + 1) ^ 5 = 30 * (krefVcsK * (krefZ n k + 1) ^ 5) +
      30 * (krefRanksK * (krefZ n k + 1) ^ 5) + 30 * (krefCntsK * (krefZ n k + 1) ^ 5) +
      90 * (krefHorK * (krefZ n k + 1) ^ 5) + 30 * (krefLookK * (krefZ n k + 1) ^ 5) +
      100000 * (krefZ n k + 1) ^ 5 := by
    unfold krefSigK; ring
  rw [e]
  omega

end Sig

end GI.Impl
