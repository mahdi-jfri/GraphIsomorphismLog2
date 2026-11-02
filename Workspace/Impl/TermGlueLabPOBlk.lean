import Workspace.Impl.TermGlueLabPOM

/-!
# The block matrix and the extra coordinate (step 5, programs)

Step 5 of the label program, the case where all types are distinct. The items of
the affine procedure then carry the orientation coordinate in front (`TermGlueLabPOM.lean`).
Two small programs build them from the items without it:

* `tmGLPConsF app` on `[x, l]` returns `x :: l` (one `append`; `tmGLPCons_spec`);
* `tmGLPBlkFuns b` on `encIntMatrix B` returns `encIntMatrix [[1, 0], [0, B]]`
  (`replicate` for the zero row, `map` of `cons 0` over the rows; `tmGLPBlk_spec`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encInt encIntMatrix encPerm encGroup gens)

/-- The expression of `encInt 0`. -/
def tmGLPZeroE : Expr := mk2 (.nat 0) .nil

/-- The expression of `encInt 1`. -/
def tmGLPOneE : Expr := mk2 (.nat 0) (.snoc .nil (.nat 1))

theorem tmGLP_encInt0 : encInt 0 = .list [.nat 0, .list []] := by simp [encInt]

theorem tmGLP_encInt1 : encInt 1 = .list [.nat 0, .list [.nat 1]] := by
  simp [encInt, Nat.bits]

theorem tmGLP_zeroE {P : Program} {env : List Val} : Det P env tmGLPZeroE (encInt 0) 200 := by
  rw [tmGLP_encInt0]
  exact (Det.mk2 (Det.nat 0) Det.nil).mono (by decide)

theorem tmGLP_oneE {P : Program} {env : List Val} : Det P env tmGLPOneE (encInt 1) 300 := by
  rw [tmGLP_encInt1]
  exact (Det.mk2 (Det.nat 0) (Det.snoc Det.nil (Det.nat 1))).mono (by decide)

theorem tmGLP_encInt01_wt : (encInt 0).wt ≤ 100 ∧ (encInt 1).wt ≤ 100 := by
  rw [tmGLP_encInt0, tmGLP_encInt1]; decide

/-! ### `cons` -/

/-- On `[x, l]`: the list `x :: l`. -/
def tmGLPConsF (app : ℕ) : Expr := .call app (mk2 (.snoc .nil (arg 0)) (arg 1))

def tmGLPConsC (W : ℕ) : ℕ := 10 ^ 5 * (W + 1) ^ 2

theorem tmGLPConsC_mono {W W' : ℕ} (h : W ≤ W') : tmGLPConsC W ≤ tmGLPConsC W' := by
  unfold tmGLPConsC; gcongr

private theorem tmGLP_cons_ar {L W Y : ℕ} (hL : L < W) (hY : Y ≤ 11 * W + 20) :
    1000 * (L + 1) * Y ≤ 20000 * (W + 1) ^ 2 := by
  have h1 : (L + 1) * Y ≤ (W + 1) * (20 * (W + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (W + 1) * (20 * (W + 1)) = 20 * (W + 1) ^ 2 := by ring
  rw [Nat.mul_assoc]
  omega

/-- **`cons`.** -/
theorem tmGLPCons_spec {P : Program} {f app : ℕ} (hf : P.funs[f]? = some (tmGLPConsF app))
    (happ : P.HasAt app (appendFuns app)) (x : Val) (l : List Val) :
    FunDet P f (.list [x, .list l]) (.list (x :: l)) (tmGLPConsC (Val.list [x, .list l]).wt) := by
  set a := Val.list [x, .list l] with ha
  set W := a.wt with hW
  apply FunDet.intro hf
  have d0 := Det.arg' (P := P) (vs := [x, .list l]) (rest := []) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [x, .list l]) (rest := []) (j := 1) rfl
  have ds : Det P [a] (.snoc .nil (arg 0)) (.list [x]) _ := Det.snoc Det.nil d0
  have dm := Det.mk2 ds d1
  have hap := append_spec happ [x] l
  have hap' : FunAll P app (.list [.list [x], .list l]) (fun w c =>
      w = .list (x :: l) ∧ c ≤ 20000 * (W + 1) ^ 2) := by
    refine FunAll.mono hap fun w c ⟨hw, hc⟩ => ⟨hw, hc.trans ?_⟩
    subst hw
    have wx : x.wt < W := wt_le_wt_list (by simp)
    have wl : (Val.list l).wt < W := wt_le_wt_list (by simp)
    have ll := length_lt_wt_list l
    have w1 := wt_list_cons_le x []
    have w2 := wt_list2_le (.list [x]) (.list l)
    have w3 := wt_list_cons_le x l
    have : ([x] ++ l) = x :: l := rfl
    rw [this]
    simp only [wt_list_nil] at w1
    exact tmGLP_cons_ar (by omega) (by omega)
  refine (Det.call dm hap').mono ?_
  have ea : (Val.list [x, Val.list l]).wt = W := rfl
  have wx : x.wt < W := wt_le_wt_list (by simp)
  have wl : (Val.list l).wt < W := wt_le_wt_list (by simp)
  have w1 := wt_list_cons_le x []
  have w2 := wt_list2_le (.list [x]) (.list l)
  have w3 := wt_list_cons_le x l
  have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have e1 : (Val.list ([] ++ [x])).wt = (Val.list [x]).wt := rfl
  simp only [wt_list_nil] at w1
  unfold tmGLPConsC
  generalize (W + 1) ^ 2 = S at *
  omega

/-! ### The block matrix -/

/-- The map body: `0 :: row`, on `[c, row]`. -/
def tmGLPCons0F (cons : ℕ) : Expr := .call cons (mk2 tmGLPZeroE (arg 1))

/-- **The block matrix** `[[1, 0], [0, B]]`, on `encIntMatrix B`. -/
def tmGLPBlkF (rep cons mp : ℕ) : Expr :=
  .letE (.call rep (mk2 (.length (.var 0)) tmGLPZeroE))
    (.letE (.call cons (mk2 tmGLPOneE (.var 1)))
      (.letE (.call mp (mk2 .nil (.var 0)))
        (.call cons (mk2 (.var 2) (.var 3)))))

/-- The module (12 functions). -/
def tmGLPBlkFuns (b : ℕ) : List Expr :=
  [tmGLPBlkF (b + 1) (b + 4) (b + 5)] ++ replicateFuns (b + 1) ++ [tmGLPConsF (b + 9)] ++
    mapFuns (b + 5) (b + 8) ++ [tmGLPCons0F (b + 4)] ++ appendFuns (b + 9)

theorem length_tmGLPBlkFuns (b : ℕ) : (tmGLPBlkFuns b).length = 12 := rfl

def tmGLPBlkC (W : ℕ) : ℕ := 10 ^ 12 * (W + 1) ^ 4

private theorem tmGLP_forall2_map {xs ws : List Val} {f : Val → Val}
    (h : List.Forall₂ (fun x w => w = f x) xs ws) : ws = xs.map f := by
  induction h with
  | nil => rfl
  | cons h _ ih => rw [List.map_cons, ih, h]

/-- One row of `encIntMatrix B`. -/
def tmGLPRow {t : ℕ} (B : Matrix (Fin t) (Fin t) ℤ) (i : Fin t) : List Val :=
  (List.finRange t).map fun j => encInt (B i j)

private theorem tmGLP_blk_rows {t : ℕ} (B : Matrix (Fin t) (Fin t) ℤ) :
    encIntMatrix B = .list ((List.finRange t).map fun i => .list (tmGLPRow B i)) := rfl

private theorem tmGLP_blk_ar2 {W L Y : ℕ} (hL : L ≤ W) (hY : Y ≤ 1000 * (W + 1) ^ 2) :
    loopModK * (L + 1) * Y ≤ 10 ^ 6 * (W + 1) ^ 3 := by
  unfold loopModK
  rw [Nat.mul_assoc]
  calc 1000 * ((L + 1) * Y) ≤ 1000 * ((W + 1) * (1000 * (W + 1) ^ 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hY)
    _ = 10 ^ 6 * (W + 1) ^ 3 := by ring

private theorem tmGLP_blk_ar3 {S X : ℕ} (hS : 1 ≤ S) (hX : X ≤ 1500 * S) :
    tmGLPConsC X ≤ 3 * 10 ^ 11 * S ^ 2 := by
  unfold tmGLPConsC
  have h1 : (X + 1) ^ 2 ≤ (1501 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (1501 * S) ^ 2 = 2253001 * S ^ 2 := by ring
  rw [h2] at h1
  generalize (X + 1) ^ 2 = A at *
  generalize S ^ 2 = S2 at *
  omega

private theorem tmGLP_blk_ar1 {W c : ℕ} (hc : c ≤ tmGLPConsC (2 * W + 250) + 20 * W + 2000) :
    c ≤ 10 ^ 10 * (W + 1) ^ 2 := by
  unfold tmGLPConsC at hc
  have h1 : (2 * W + 250 + 1) ^ 2 ≤ (251 * (W + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : (251 * (W + 1)) ^ 2 = 63001 * (W + 1) ^ 2 := by ring
  have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [h2] at h1
  generalize (2 * W + 250 + 1) ^ 2 = A at *
  generalize (W + 1) ^ 2 = S at *
  omega

/-- **The block matrix.** -/
theorem tmGLPBlk_spec {P : Program} {b : ℕ} (h : P.HasAt b (tmGLPBlkFuns b)) {t : ℕ}
    (B : Matrix (Fin t) (Fin t) ℤ) :
    FunDet P b (encIntMatrix B) (encIntMatrix (tmGLPBlk B)) (tmGLPBlkC (encIntMatrix B).wt) := by
  have hf : P.funs[b]? = some (tmGLPBlkF (b + 1) (b + 4) (b + 5)) := by
    simpa using (h.block (gs := [tmGLPBlkF (b + 1) (b + 4) (b + 5)]) 0 rfl).single
  have hrep : P.HasAt (b + 1) (replicateFuns (b + 1)) := h.block 1 rfl
  have hcons : P.funs[b + 4]? = some (tmGLPConsF (b + 9)) :=
    (h.block (gs := [tmGLPConsF (b + 9)]) 4 rfl).single
  have hmp : P.HasAt (b + 5) (mapFuns (b + 5) (b + 8)) := h.block 5 rfl
  have hc0 : P.funs[b + 8]? = some (tmGLPCons0F (b + 4)) :=
    (h.block (gs := [tmGLPCons0F (b + 4)]) 8 rfl).single
  have happ : P.HasAt (b + 9) (appendFuns (b + 9)) := h.block 9 rfl
  set rows : List Val := (List.finRange t).map fun i => .list (tmGLPRow B i) with hrows
  have hB : encIntMatrix B = .list rows := tmGLP_blk_rows B
  set W := (encIntMatrix B).wt with hW
  have wr : (Val.list rows).wt = W := by rw [hW, hB]
  have lr : rows.length = t := by simp [hrows]
  have ltW : t < W := by have := length_lt_wt_list rows; omega
  have ⟨w0, w1⟩ := tmGLP_encInt01_wt
  have hS1 : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS2 : (W + 1) ^ 2 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  -- the zero row
  set z : Val := .list (List.replicate t (encInt 0)) with hz
  have ez : z.wt = (Val.list (List.replicate t (encInt 0))).wt := rfl
  have wz : z.wt ≤ 201 * W + 4 := by
    have := wt_list_le_of (l := List.replicate t (encInt 0)) (A := 100) (by
      intro v hv; rw [(List.mem_replicate.1 hv).2]; exact w0)
    simp only [List.length_replicate] at this
    exact this.trans (by omega)
  -- the rows `0 :: row`
  have hrow : ∀ x ∈ rows, FunAll P (b + 8) (.list [.list [], x]) (fun w c =>
      w = tmGLPConsV (encInt 0) x ∧ c ≤ 10 ^ 10 * (W + 1) ^ 2) := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    have wx : (Val.list (tmGLPRow B i)).wt < W := by
      rw [← wr]; exact wt_le_wt_list hx
    set a0 : Val := .list [.list [], .list (tmGLPRow B i)] with ha0
    have w2 := wt_list2_le (.list []) (.list (tmGLPRow B i))
    simp only [wt_list_nil] at w2
    apply FunAll.intro hc0
    have d1 := Det.arg' (P := P) (vs := [.list [], .list (tmGLPRow B i)]) (rest := []) (j := 1) rfl
    have dm := Det.mk2 (tmGLP_zeroE (P := P) (env := [a0])) d1
    have hcs := tmGLPCons_spec hcons happ (encInt 0) (tmGLPRow B i)
    have w3 := wt_list2_le (encInt 0) (.list (tmGLPRow B i))
    have w4 := wt_list_cons_le (encInt 0) (tmGLPRow B i)
    refine ((Det.call dm hcs).mono le_rfl).post fun c hc => ⟨rfl, tmGLP_blk_ar1 ?_⟩
    have := tmGLPConsC_mono (show (Val.list [encInt 0, .list (tmGLPRow B i)]).wt ≤ 2 * W + 250 by
      omega)
    have ea : a0.wt = (Val.list [.list [], .list (tmGLPRow B i)]).wt := rfl
    omega
  apply FunDet.intro hf
  have dv0 : Det P [encIntMatrix B] (.var 0) (.list rows) _ :=
    Det.var' (env := [encIntMatrix B]) (i := 0) (v := .list rows) (by rw [hB]; rfl)
  -- stage 1: the zero row
  have dl : Det P [encIntMatrix B] (.length (.var 0)) (.nat t) ((Val.list rows).wt + 1 + t + 3) := by
    have := Det.length dv0
    rw [lr] at this
    exact this
  have d1a := Det.mk2 dl (tmGLP_zeroE (P := P) (env := [encIntMatrix B]))
  have hrepD : FunDet P (b + 1) (.list [.nat t, encInt 0]) z (10 ^ 6 * (W + 1) ^ 3) := by
    refine FunAll.mono (replicate_spec hrep t (encInt 0)) fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
    subst hw
    refine hc.trans (tmGLP_blk_ar2 ltW.le ?_)
    have := wt_list2_le (.nat t) (encInt 0)
    have := wt_nat_le t
    omega
  have d1 := Det.call d1a hrepD
  -- stage 2: the first row
  set r0 : Val := .list (encInt 1 :: List.replicate t (encInt 0)) with hr0
  have er0 : r0.wt = (Val.list (encInt 1 :: List.replicate t (encInt 0))).wt := rfl
  have wr0 : r0.wt ≤ 201 * W + 206 := by
    have := wt_list_cons_le (encInt 1) (List.replicate t (encInt 0)); omega
  have d2a := Det.mk2 (tmGLP_oneE (P := P) (env := [encIntMatrix B, z]))
    (Det.var' (P := P) (env := [encIntMatrix B, z]) (i := 1) (v := z) rfl)
  have d2 := Det.call d2a (tmGLPCons_spec hcons happ (encInt 1) (List.replicate t (encInt 0)))
  -- stage 3: the other rows
  set rs : Val := .list (rows.map (tmGLPConsV (encInt 0))) with hrs
  have ers : rs.wt = (Val.list (rows.map (tmGLPConsV (encInt 0)))).wt := rfl
  have wrs : rs.wt ≤ 406 * (W + 1) ^ 2 := by
    rw [ers]
    have h1 := wt_list_le_of (l := rows.map (tmGLPConsV (encInt 0))) (A := W + 202) (by
      intro v hv
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      have := wt_list_cons_le (encInt 0) (tmGLPRow B i)
      have : (Val.list (tmGLPRow B i)).wt < W := by
        rw [← wr]; exact wt_le_wt_list hx
      show (Val.list (encInt 0 :: tmGLPRow B i)).wt ≤ _
      omega)
    rw [List.length_map, lr] at h1
    have h2 : t * (2 * (W + 202) + 1) ≤ (W + 1) * (405 * (W + 1)) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : (W + 1) * (405 * (W + 1)) = 405 * (W + 1) ^ 2 := by ring
    rw [h3] at h2
    exact h1.trans (Nat.add_le_add_right h2 4 |>.trans (by
      have : 4 ≤ (W + 1) ^ 2 := by nlinarith
      generalize (W + 1) ^ 2 = S at *
      omega))
  have hmap := map_spec hmp (c := .list []) (xs := rows)
    (R := fun x w => w = tmGLPConsV (encInt 0) x) (B := fun _ => 10 ^ 10 * (W + 1) ^ 2) hrow
  have hmapD : FunDet P (b + 5) (.list [.list [], .list rows]) rs
      (10 ^ 10 * (W + 1) ^ 3 + 10 ^ 6 * (W + 1) ^ 3) := by
    refine FunAll.mono hmap fun w c ⟨ws, hw, hws, hc⟩ => ?_
    have hws' := tmGLP_forall2_map hws
    subst hws'
    subst hw
    refine ⟨rfl, hc.trans (Nat.add_le_add ?_ ?_)⟩
    · rw [List.map_const', List.sum_replicate, lr, smul_eq_mul]
      have : t * (10 ^ 10 * (W + 1) ^ 2) ≤ (W + 1) * (10 ^ 10 * (W + 1) ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      have e : (W + 1) * (10 ^ 10 * (W + 1) ^ 2) = 10 ^ 10 * (W + 1) ^ 3 := by ring
      omega
    · rw [lr, show mapK = loopModK from rfl]
      refine tmGLP_blk_ar2 ltW.le ?_
      have := wt_list2_le (.list []) (.list rows)
      simp only [wt_list_nil] at this
      have : W + 1 ≤ (W + 1) ^ 2 := hS1
      show _ + rs.wt + 1 ≤ _
      omega
  have d3a := Det.mk2 (Det.nil (P := P) (env := [encIntMatrix B, z, r0]))
    (Det.var' (P := P) (env := [encIntMatrix B, z, r0]) (i := 0) (v := .list rows) (by rw [hB]; rfl))
  have d3 := Det.call d3a hmapD
  -- stage 4: the matrix
  have d4a := Det.mk2 (Det.var' (P := P) (env := [encIntMatrix B, z, r0, rs]) (i := 2) (v := r0) rfl)
    (Det.var' (P := P) (env := [encIntMatrix B, z, r0, rs]) (i := 3) (v := rs) rfl)
  have d4 := Det.call d4a (tmGLPCons_spec hcons happ r0 (rows.map (tmGLPConsV (encInt 0))))
  have hval : Val.list (r0 :: rows.map (tmGLPConsV (encInt 0))) = encIntMatrix (tmGLPBlk B) := by
    rw [tmGLP_enc_blk, hr0, hrows, List.map_map]
    rfl
  rw [hval] at d4
  refine (Det.letE d1 (Det.letE d2 (Det.letE d3 d4))).mono ?_
  -- the cost
  have wout : (encIntMatrix (tmGLPBlk B)).wt ≤ 1000 * (W + 1) ^ 2 := by
    rw [← hval]
    have := wt_list_cons_le r0 (rows.map (tmGLPConsV (encInt 0)))
    omega
  have k2 := tmGLPConsC_mono (show (Val.list [encInt 1, z]).wt ≤ 1500 * (W + 1) ^ 2 by
    have := wt_list2_le (encInt 1) z; omega)
  have k4 := tmGLPConsC_mono (show (Val.list [r0, rs]).wt ≤ 1500 * (W + 1) ^ 2 by
    have := wt_list2_le r0 rs; omega)
  have k2' := tmGLP_blk_ar3 (S := (W + 1) ^ 2) (Nat.one_le_pow 2 (W + 1) (Nat.succ_pos W)) le_rfl
  have e4 : ((W + 1) ^ 2) ^ 2 = (W + 1) ^ 4 := by ring
  have e3 : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [e4] at k2'
  have wa1 := wt_list2_le (.nat t) (encInt 0)
  have wa2 := wt_list2_le (encInt 1) z
  have wa3 := wt_list2_le (.list []) (.list rows)
  have wa4 := wt_list2_le r0 rs
  have wt' := wt_nat_le t
  have ew : (encIntMatrix B).wt = W := rfl
  have ewz : (Val.list [encIntMatrix B, z]).wt = (Val.list [encIntMatrix B, z]).wt := rfl
  have ex : tmGLPConsC (Val.list [encInt 1, Val.list (List.replicate t (encInt 0))]).wt =
      tmGLPConsC (Val.list [encInt 1, z]).wt := rfl
  have ey : tmGLPConsC (Val.list [r0, Val.list (List.map (tmGLPConsV (encInt 0)) rows)]).wt =
      tmGLPConsC (Val.list [r0, rs]).wt := rfl
  have wE : ∀ v : Val, v = encInt 0 ∨ v = encInt 1 → v.wt ≤ 100 := by
    rintro v (rfl | rfl) <;> omega
  simp only [wt_list_nil] at wa3
  unfold tmGLPBlkC
  generalize tmGLPConsC (1500 * (W + 1) ^ 2) = K at *
  generalize (W + 1) ^ 4 = S4 at *
  generalize (W + 1) ^ 3 = S3 at *
  generalize (W + 1) ^ 2 = S2 at *
  omega

end GI.Impl
