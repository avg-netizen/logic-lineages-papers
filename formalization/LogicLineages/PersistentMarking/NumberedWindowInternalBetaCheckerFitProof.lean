module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaSubDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowTransparentBetaBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerFitProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalEqualityTest (equalityTest)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowBinderRootAlgorithm (beta betaRows)
open NumberedWindowTransparentBetaBranchProof (instanceOutput row_iff)
open NumberedWindowInternalBetaSub

/-- Physical coordinates selected by the original nested parses. No
substitution, target comparison or endpoint rewrite occurs here. -/
def fields (src : Nat) : Option ((Nat × List Nat) × (Nat × List Nat)) := do
  let p ← unpackNode src
  let fn ← unpackNode (p.2.getD 2 0)
  pure (p,fn)

def binderBits (p fn : Nat × List Nat) : Bool :=
  (p.1 == 6) && (fn.1 == 2) && (p.2.getD 0 0 == fn.2.getD 0 0)

def guardSpec (src dst : Nat) : Nat :=
  (guarded src dst ((fields src).any fun f => binderBits f.1 f.2)).toNat

def argSpec (src : Nat) : Nat :=
  ((fields src).map fun f => f.1.2.getD 3 0).getD 0

def bodySpec (src : Nat) : Nat :=
  ((fields src).map fun f => f.2.2.getD 1 0).getD 0

private theorem evaluateCompose2 {n : Nat} (top : Program 2) (a b : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition top ![a,b]) v =
      run2 top (evaluate a v) (evaluate b v) := by
  unfold run2
  rw [evaluate,vectorTwo]
  rfl

private theorem evaluateTarget (src dst : Nat) :
    run2 (.composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2))) src dst
      = dst + 1 := by
  unfold run2
  rw [evaluate,vectorOne]
  rfl

theorem checkerEvaluation (guard arg body sub : Program 2) (src dst : Nat) :
    run2 (betaChecker guard arg body sub) src dst =
      if run2 guard src dst = 0 then 0
      else if run2 sub (run2 arg src dst) (run2 body src dst) = dst + 1 then 1 else 0 := by
  unfold betaChecker
  unfold run2 at *
  rw [evalBranch]
  split
  · rfl
  · rw [evaluateCompose2,evaluateCompose2]
    change run2 equalityTest (run2 sub (run2 arg src dst) (run2 body src dst))
      (run2 (.composition .succ (fun _ : Fin 1 => .projection (1 : Fin 2))) src dst) = _
    rw [evaluateTarget]
    exact exactEqualityEvaluation _ _

private theorem codeMatches (arg body dst : Nat) :
    code arg body = dst + 1 ↔ (NumberedWindowSingletonAlgorithm.output arg 0 body).1 = some dst := by
  unfold code
  cases (NumberedWindowSingletonAlgorithm.output arg 0 body).1 <;> simp

/-- An all-input fit for the transparent checker. These three numeric selector
fits are for actual original fields and guards; not assumptions about the
result of substitution or about the enclosing positive path checker. -/
theorem exactOriginal (guard arg body sub : Program 2) (subFit : Fits sub)
    (guardFit : ∀ src dst, run2 guard src dst = guardSpec src dst)
    (argFit : ∀ src dst, run2 arg src dst = argSpec src)
    (bodyFit : ∀ src dst, run2 body src dst = bodySpec src)
    (src dst : Nat) :
    run2 (betaChecker guard arg body sub) src dst = (beta src dst).toNat := by
  rw [checkerEvaluation,guardFit,argFit,bodyFit,subFit]
  simp only [codeMatches]
  unfold guardSpec argSpec bodySpec fields beta
  cases hp : unpackNode src with
  | none => simp [guarded]
  | some p =>
    simp only [Option.bind_some,Option.any_some]
    cases hf : unpackNode (p.2.getD 2 0) with
    | none =>
      simp only [List.getD_eq_getElem?_getD] at hf
      simp [guarded,hf]
    | some fn =>
      simp only [Option.bind_some,Option.any_some,Option.map_some,Option.getD_some]
      have same := row_iff dst p fn
      have binders : binderBits p fn = true ↔
          p.1 = 6 ∧ fn.1 = 2 ∧ p.2.getD 0 0 = fn.2.getD 0 0 := by
        simp [binderBits,Bool.and_eq_true,beq_iff_eq,and_assoc]
      cases hs : (syntaxBits src).1 <;> cases hd : (syntaxBits dst).1 <;>
        cases hb : binderBits p fn <;> cases hr : betaRows dst p fn <;>
        simp_all [guarded,instanceOutput]

#print axioms checkerEvaluation
#print axioms exactOriginal
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerFitProof
