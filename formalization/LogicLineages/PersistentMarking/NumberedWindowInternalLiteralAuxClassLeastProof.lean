module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNumericAuxClassesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction constantZero)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalLessThan (constantOne)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration packedLeast encodeState)
open NumberedWindowInternalSparsePathEnvelope (run field nodeGood)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termFields termOne)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers predOne)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (compositeOne compositeTwo compositeThree compareEvaluation predEvaluation)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalLiteralNumericAuxClassesProof (auxClasses exact_LiteralPackedLeastAuxClasses)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)

def atRaw (p : Program 1) : Program 2 := .composition p (Fin.cons (.projection 1) Fin.elim0)

def childArrow : Program 2 := consOf (atRaw (field 0)) (atRaw (field 1))

/-- The same explicitly selected underlying least callback computes
both child class codes, with their actual independent types. -/
def functionClass (L : Program 3) : Program 2 := .composition L
  (Fin.cons (.projection 0) (Fin.cons childArrow (Fin.cons (atRaw (field 2)) Fin.elim0)))

def argumentClass (L : Program 3) : Program 2 := .composition L
  (Fin.cons (.projection 0) (Fin.cons (atRaw (field 0)) (Fin.cons (atRaw (field 3)) Fin.elim0)))

def resultRaw : Program 3 := .composition predOne (Fin.cons (.projection 2) Fin.elim0)
def onSource (p : Program 2) : Program 3 := .composition p (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0))
def onResult (p : Program 2) : Program 3 := .composition p (Fin.cons (.projection 0) (Fin.cons resultRaw Fin.elim0))
def compareChildClass (p : Program 2) : Program 3 :=
  .composition compareNumbers (Fin.cons (onSource p) (Fin.cons (onResult p) Fin.elim0))
def selectedAuxiliary : Program 3 := .composition termShape (Fin.cons (.projection 1) Fin.elim0)
def childClassesAgree (L : Program 3) : Program 3 :=
  conjunction (compareChildClass (functionClass L)) (compareChildClass (argumentClass L))
def checkAuxiliaryClasses (L : Program 3) : Program 3 :=
  branch selectedAuxiliary (constantOne 3) (childClassesAgree L)
def retainClasses (L : Program 3) : Program 3 := branch (checkAuxiliaryClasses L) (constantZero 3) (.projection 2)

/-- The same physical least query, with a conjunction of its two
auxiliary child-class comparisons. The old least remains the only
producer of the selected result. -/
def auxClassLeast (L : Program 3) : Program 3 :=
  .composition (retainClasses L) (Fin.cons (.projection 0) (Fin.cons (.projection 2) (Fin.cons L Fin.elim0)))

private theorem atRawValue (p : Program 1) (ctx q : Nat) :
    evaluate (atRaw p) (ctx ::ᵥ q ::ᵥ nil) = run p q := by
  rw [atRaw,compositeOne]
  rfl

theorem childArrowValue (ctx q d c f a : Nat) (h : unpackNode q = some (6,[d,c,f,a])) :
    evaluate childArrow (ctx ::ᵥ q ::ᵥ nil) = arrow d c := by
  rw [childArrow,consOf,compositeTwo,atRawValue,atRawValue]
  obtain ⟨hd,hc,_,_⟩ := termFields h
  rw [hd,hc,consValue]
  rfl

theorem functionClassValue (L : Program 3) (ctx q d c f a : Nat) (h : unpackNode q = some (6,[d,c,f,a])) :
    evaluate (functionClass L) (ctx ::ᵥ q ::ᵥ nil) = evaluate L (ctx ::ᵥ arrow d c ::ᵥ f ::ᵥ nil) := by
  rw [functionClass,compositeThree,childArrowValue ctx q d c f a h,atRawValue,(termFields h).2.2.1]
  rfl

theorem argumentClassValue (L : Program 3) (ctx q d c f a : Nat) (h : unpackNode q = some (6,[d,c,f,a])) :
    evaluate (argumentClass L) (ctx ::ᵥ q ::ᵥ nil) = evaluate L (ctx ::ᵥ d ::ᵥ a ::ᵥ nil) := by
  rw [argumentClass,compositeThree,atRawValue,atRawValue,(termFields h).1,(termFields h).2.2.2]
  rfl

private theorem compareChildValue (p : Program 2) (ctx q t : Nat) :
    evaluate (compareChildClass p) (ctx ::ᵥ q ::ᵥ (t+1) ::ᵥ nil) =
      if evaluate p (ctx ::ᵥ q ::ᵥ nil) = evaluate p (ctx ::ᵥ t ::ᵥ nil) then 1 else 0 := by
  rw [compareChildClass,compositeTwo,onSource,onResult,compositeTwo,compositeTwo,resultRaw,compositeOne]
  change evaluate compareNumbers (evaluate p (ctx ::ᵥ q ::ᵥ nil) ::ᵥ
    evaluate p (ctx ::ᵥ evaluate predOne ((t+1) ::ᵥ nil) ::ᵥ nil) ::ᵥ nil) = _
  simp only [predEvaluation,Nat.pred_succ]
  exact compareEvaluation _ _

private theorem actualChildEquality (s : Settings) (covered : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (L : Program 3) (cal : ActualLeastCalibration s L)
    (ctx ty q k d c fn arg : Nat)
    (hq : unpackNode q = some (6,[d,c,fn,arg])) (ans : packedLeast s ctx ty q = some k) :
    evaluate (functionClass L) (ctx ::ᵥ q ::ᵥ nil) = evaluate (functionClass L) (ctx ::ᵥ k ::ᵥ nil) ∧
    evaluate (argumentClass L) (ctx ::ᵥ q ::ᵥ nil) = evaluate (argumentClass L) (ctx ::ᵥ k ::ᵥ nil) := by
  cases hc : unpack ctx with
  | none => simp [packedLeast,hc] at ans
  | some Γ =>
    have same := exact_LiteralPackedLeastAuxClasses s covered symmetric ctx ty q k ans Γ hc
    cases hk : unpackNode k with
    | none => simp [auxClasses,hq,hk] at same
    | some pair =>
      obtain ⟨tag,fields⟩ := pair
      have form : tag = 6 := by
        by_contra h
        -- On a successful least all matched raw heads, including tag six, agree.
        have tags := NumberedWindowInternalLiteralLeastHeaderInvarianceProof.exact_LiteralPackedLeastHeader
          s ctx ty q k ans
        simp [NumberedWindowInternalLiteralLeastHeaderInvarianceProof.header,hq,hk] at tags
        exact h tags.symm
      subst tag
      rcases fields with _ | ⟨d',_ | ⟨c',_ | ⟨fn',_ | ⟨arg',_ | ⟨e,es⟩⟩⟩⟩⟩ <;>
        simp [auxClasses,hq,hk] at same
      obtain ⟨dd,cc,ff,aa⟩ := same
      subst d'
      subst c'
      refine ⟨?_,?_⟩
      · rw [functionClassValue L ctx q d c fn arg hq,functionClassValue L ctx k d c fn' arg' hk]
        rw [cal ctx (arrow d c) fn,cal ctx (arrow d c) fn']
        simp [packedLeast,hc,ff]
      · rw [argumentClassValue L ctx q d c fn arg hq,argumentClassValue L ctx k d c fn' arg' hk]
        rw [cal ctx d arg,cal ctx d arg']
        simp [packedLeast,hc,aa]

theorem exact_LiteralAuxClassLeast (s : Settings) (covered : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) (L : Program 3)
    (cal : ActualLeastCalibration s L) : ActualLeastCalibration s (auxClassLeast L) := by
  intro ctx ty q
  rw [auxClassLeast,compositeThree,cal ctx ty q]
  change evaluate (retainClasses L) (ctx ::ᵥ q ::ᵥ encodeState (packedLeast s ctx ty q) ::ᵥ nil) = _
  cases ans : packedLeast s ctx ty q with
  | none =>
    change evaluate (retainClasses L) (ctx ::ᵥ q ::ᵥ 0 ::ᵥ nil) = 0
    rw [retainClasses,evalBranch]
    split <;> rfl
  | some k =>
    change evaluate (retainClasses L) (ctx ::ᵥ q ::ᵥ (k+1) ::ᵥ nil) = k+1
    let xs := ctx ::ᵥ q ::ᵥ (k+1) ::ᵥ nil
    have shape : evaluate selectedAuxiliary xs = run termShape q := by
      rw [selectedAuxiliary,compositeOne]
      rfl
    have check : evaluate (checkAuxiliaryClasses L) xs = 1 := by
      rw [checkAuxiliaryClasses,evalBranch,shape]
      have bit : run termShape q = 0 ∨ run termShape q = 1 := by
        unfold termShape nodeGood run
        rw [actualConjunctionEvaluation]
        split <;> simp
      rcases bit with h | h
      · rw [if_pos h]
        rfl
      · rw [if_neg (by rw [h]; decide)]
        obtain ⟨d,c,f,a,hq⟩ := (termOne q).mp h
        obtain ⟨hf,ha⟩ := actualChildEquality s covered symmetric L cal ctx ty q k d c f a hq ans
        change evaluate (childClassesAgree L) xs = 1
        rw [childClassesAgree,actualConjunctionEvaluation,compareChildValue,compareChildValue,if_pos hf,if_pos ha]
        rfl
    rw [retainClasses,evalBranch,check]
    rfl

#print axioms exact_LiteralAuxClassLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassLeastProof
