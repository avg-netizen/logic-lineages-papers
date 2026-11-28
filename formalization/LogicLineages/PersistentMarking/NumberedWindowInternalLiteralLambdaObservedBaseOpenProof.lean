module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaObservedBaseDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaObservedBaseOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchIntro zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons suc z)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalPush)
open NumberedWindowInternalCoverLambdaLexicalShapeProof (actualLambdaLexicalShape)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D)
open NumberedWindowInternalLiteralLambdaObservedBase

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem guardReport (guard base : Program 2) (result : OTerm α) (xs : Fin 2 → OTerm α)
    (held : D B Γ (programGraph (branch (normalize guard) (constantZero 2) base) (suc result) xs)) :
    D B Γ (programGraph guard (suc z) xs) := by
  let P := programGraph guard (suc z) xs
  obtain ⟨h⟩ := held
  have yes : Derivation B (P :: Γ) P := Derivation.hypothesis List.mem_cons_self
  have no : D B (P.not :: Γ) P := by
    have deny : D B (P.not :: Γ) P.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have bad := zeroBranchElim (normalize guard) (constantZero 2) base (suc result) xs
      (normalizeReject guard xs deny) ⟨addHyp h P.not⟩
    obtain ⟨eq⟩ := valueUnique (constantZero 2) (suc result) z xs bad (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  obtain ⟨no⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction no)⟩

/-- A successful literal lambda in the observed callback supplies both child
reports at the same pushed context, along with the original base result. -/
theorem exact_OpenObservedLambdaBase (C : Program 3) (s : Settings) (Va : Program 1) (base : Program 2)
    (ctx dom q result : OTerm α)
    (held : D B Γ (programGraph (observedLambdaBase C s Va base)
      (suc result) ![ctx,lambdaTerm dom q])) :
    D B Γ (programGraph base (suc result) ![ctx,lambdaTerm dom q]) ∧
      D B Γ (coverageReport C s (rawCons dom ctx) q) ∧ D B Γ (unary Va (suc z) q) := by
  let raw := lambdaTerm dom q
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let guard := lambdaChildObservations C s Va
  have shape := actualLambdaLexicalShape (body := B) (Γ := Γ) dom q
  have tagged := liftRawReport (header 2 2) ctx raw (suc z) shape.lambdaYes
  have checked := successorBranchElim (onRaw (header 2 2)) base
    (branch (normalize guard) (constantZero 2) base) (suc result) z xs tagged held
  have accepted := guardReport guard base result xs checked
  have computed := successorBranchElim (normalize guard) (constantZero 2) base
    (suc result) z xs (normalizeAccept guard xs accepted) checked
  obtain ⟨both⟩ := conjunctionRecover (lambdaChildCoverage C s) (lambdaChildSyntax Va) xs accepted
  have atDom := liftRawReport (field 0) ctx raw dom shape.domainRead
  have atBody := liftRawReport (field 1) ctx raw q shape.childRead
  have pushed : D B Γ (programGraph lambdaLexicalPush (rawCons dom ctx) xs) := by
    apply compositionValue fieldCons (Fin.cons (onRaw (field 0)) (Fin.cons (.projection 0) Fin.elim0))
      (rawCons dom ctx) xs ![dom,ctx] (consGraph dom ctx)
    intro i
    exact Fin.cases atDom (Fin.cases (projectionValue 0 xs) (fun j => Fin.elim0 j)) i
  refine ⟨computed,?_,?_⟩
  · apply compositionRecover (conjunction contextPresent (ownSeed C s))
      ![lambdaLexicalPush,constantZero 2,onRaw (field 1)]
      (suc z) xs ![rawCons dom ctx,z,q] ⟨Derivation.conjunctionLeft both⟩
    intro i
    exact Fin.cases pushed (Fin.cases (constantZeroValue xs)
      (Fin.cases atBody (fun j => Fin.elim0 j))) i
  · apply compositionRecover Va (fun _ : Fin 1 => onRaw (field 1))
      (suc z) xs ![q] ⟨Derivation.conjunctionRight both⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact atBody

/-- Off the lambda branch the same callback computes the unwrapped result. -/
theorem exact_OpenObservedBaseOfNonLambda (C : Program 3) (s : Settings) (Va : Program 1)
    (base : Program 2) (ctx raw result : OTerm α)
    (notLambda : D B Γ (unary (header 2 2) z raw))
    (computed : D B Γ (programGraph base (suc result) ![ctx,raw])) :
    D B Γ (programGraph (observedLambdaBase C s Va base) (suc result) ![ctx,raw]) := by
  exact zeroBranchIntro (onRaw (header 2 2)) base
    (branch (normalize (lambdaChildObservations C s Va)) (constantZero 2) base)
    (suc result) ![ctx,raw] (liftRawReport (header 2 2) ctx raw z notLambda) computed

#print axioms exact_OpenObservedLambdaBase
#print axioms exact_OpenObservedBaseOfNonLambda
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaObservedBaseOpenProof
