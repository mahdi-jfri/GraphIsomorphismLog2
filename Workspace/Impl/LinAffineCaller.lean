module

public import Workspace.Impl.TermGlueLabAff
public import Workspace.Impl.LinRecenterContextSpec
public import Workspace.Impl.LinFiniteDifference
public import Workspace.Impl.LinZeroIntVector
public import Workspace.Impl.LinAffineLeftSpec
public import Workspace.Impl.LinMixedLoopSpec
public import Workspace.Lang.Prims.Reduce

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang

theorem linTmGLMat_eq {d : ℕ} (m : Fin d → ℕ) (f : linFiniteVec m →+ linFiniteVec m) :
    tmGLMat m f = linFiniteIntMatrix m f := rfl

theorem linTmGLAffItem_eq {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m) (g : gens gs) :
    tmGLAffItem gs m ρ c g = linPlainAffineVal m ρ c g := rfl

theorem linTmGLAffIn_eq {n d : ℕ} (gs : List (Equiv.Perm (Fin n))) (m : Fin d → ℕ)
    (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m)) (c : gens gs → linFiniteVec m)
    (v w : linFiniteVec m) :
    tmGLAffIn gs m ρ c v w = .list [encGroup gs, linVecVal (fun i => (m i : ℤ)),
      .list ((linActionGens gs).map (linPlainAffineVal m ρ c)),
      linVecVal (fun i => ((v i).val : ℤ)), linVecVal (fun i => ((w i).val : ℤ))] := by
  have he := linPrimaryGeneratorList_eq gs
  unfold linPrimaryGeneratorList at he
  have hm := congrArg (fun xs => xs.map (linPlainAffineVal m ρ c)) he
  simp only [List.map_map, Function.comp_def] at hm
  have hv := congrArg (fun x => Val.list [encGroup gs, linVecVal (fun i => (m i : ℤ)), .list x,
      linVecVal (fun i => ((v i).val : ℤ)), linVecVal (fun i => ((w i).val : ℤ))]) hm
  change tmGLAffIn gs m ρ c v w = _ at hv
  exact hv

def linAffineCallerIdentityE : Expr := .get (.get (arg 0) (.nat 1)) (.nat 0)

def linAffineCallerSmallF (difference zero : ℕ) : Expr :=
  .letE (.call difference (mk3 (arg 1) (arg 3) (arg 4)))
    (.letE (.call zero (.var 1))
      (.ite (.var 2) (mk2 linAffineCallerIdentityE
        (mk2 (.get (arg 0) (.nat 0)) (mk1 linAffineCallerIdentityE))) .nil))

def linAffineCallerPrepF (context difference reduce tail restrict : ℕ) : Expr :=
  .letE (.call context (.var 0))
    (.letE (.call difference (mk3 (arg 1) (arg 3) (arg 4)))
      (.letE (.call reduce (arg 0))
        (.letE (.call tail (.get (.var 3) (.nat 1)))
          (.letE (.call restrict (mk2 (.var 1) (.var 4)))
            (.snoc (mk3 (.var 5) (.snoc (.var 2) linIntOneE) linAffineCallerIdentityE) (arg 1))))))

def linAffineCallerMainF (prepare loop left : ℕ) : Expr :=
  .letE (.call prepare (.var 0))
    (.letE (.call loop (.var 1))
      (.ite (.length (.var 2)) (.call left (mk2 (.get (.get (.var 2) (.nat 0)) (.nat 0))
        (.get (.var 2) (.nat 2)))) .nil))

def linAffineCallerTopF (main small : ℕ) : Expr :=
  .ite (.arith .lt (.nat 1) (.get (arg 0) (.nat 0)))
    (.ite (.arith .lt (.nat 1) (.length (.get (arg 0) (.nat 1))))
      (.call main (.var 0)) (.call small (.var 0)))
    (.call small (.var 0))

def linAffineTransportAllFuns (b jmem jm jv : ℕ) : List Expr :=
  [linAffineCallerTopF (b + 1) (b + 2),
    linAffineCallerMainF (b + 1010) (b + 244) (b + 979),
    linAffineCallerSmallF (b + 128) (b + 153)] ++
    linRecenterContextFuns (b + 3) ++ linFiniteDifferenceFuns (b + 128) ++ linZeroIntVectorFuns (b + 153) ++
    reduceFuns (b + 158) jmem ++ tailFuns (b + 163) ++ linAffineRestrictFuns (b + 166) jm ++
    linMixedLoopFuns (b + 244) jm jv ++ linAffineLeftFuns (b + 979) ++
    [linAffineCallerPrepF (b + 3) (b + 128) (b + 158) (b + 163) (b + 166)]

theorem linAffineTransportAllFuns_length (b jmem jm jv : ℕ) :
    (linAffineTransportAllFuns b jmem jm jv).length = 1011 := by
  simp only [linAffineTransportAllFuns, List.length_append, linRecenterContextFuns_length,
    linFiniteDifferenceFuns_length, linZeroIntVectorFuns_length, linAffineRestrictFuns_length,
    linMixedLoopFuns_length, linAffineLeftFuns_length]
  rfl

end GI.Impl
