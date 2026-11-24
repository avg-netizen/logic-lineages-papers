module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue valueUnique)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue conjunctionRecover)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept normalizeReject)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxWindowOpenTargets (contextStep)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxUpdate)
open NumberedWindowInternalLiteralSyntaxMemoWindow (update)
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (stepFacts)
open NumberedWindowInternalLiteralCoveredMemo

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def coverageReport {α : Type} (C : Program 3) (s : Settings) (ctx raw : OTerm α) : Formula α :=
  programGraph (conjunction contextPresent (ownSeed C s)) (suc z) ![ctx,z,raw]

theorem coverStepFacts (C : Program 3) (s : Settings) (base : Program 2) (T V : Program 1)
    (key old ctx result : OTerm α)
    (held : D B Γ (contextStep (coveredUpdate C s base T V) (suc result) key old ctx)) :
    D B Γ (coverageReport C s ctx (suc key) ⊓
      (unary V (suc z) (suc key) ⊓ contextStep (strictAuxUpdate base T) (suc result) key old ctx)) := by
  let xs : Fin 4 → OTerm α := ![key,old,ctx,z]
  let h := coverageAtKey C s
  let P := programGraph h (suc z) xs
  let G := coverageReport C s ctx (suc key) ⊓
    (unary V (suc z) (suc key) ⊓ contextStep (strictAuxUpdate base T) (suc result) key old ctx)
  obtain ⟨d⟩ := held
  have yes : D B (P :: Γ) G := by
    have unit : D B (P :: Γ) P := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have rest := successorBranchElim (normalize h) (constantZero 4) (update base T V)
      (suc result) z xs (normalizeAccept h xs unit) ⟨addHyp d _⟩
    obtain ⟨inside⟩ := stepFacts base T V key old ctx result rest
    have atKey : D B (P :: Γ) (programGraph currentKey (suc key) xs) :=
      unaryGraph .succ (.projection 0) (suc key) key xs (successorValue ![key]) (projectionValue 0 xs)
    have report : D B (P :: Γ) (coverageReport C s ctx (suc key)) := by
      unfold coverageReport
      apply compositionRecover (conjunction contextPresent (ownSeed C s))
        ![.projection 2,constantZero 4,currentKey] (suc z) xs ![ctx,z,suc key] unit
      intro i
      exact Fin.cases (projectionValue 2 xs) (Fin.cases (constantZeroValue xs)
        (Fin.cases atKey (fun k => Fin.elim0 k))) i
    obtain ⟨outer⟩ := report
    exact ⟨Derivation.conjunctionIntroduction outer inside⟩
  have no : D B (P.not :: Γ) G := by
    have denied : D B (P.not :: Γ) P.not := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have bad := zeroBranchElim (normalize h) (constantZero 4) (update base T V)
      (suc result) xs (normalizeReject h xs denied) ⟨addHyp d _⟩
    obtain ⟨eq⟩ := valueUnique (constantZero 4) (suc result) z xs bad (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  obtain ⟨a⟩ := yes
  obtain ⟨b⟩ := no
  exact ⟨disjunctionElimination (excludedMiddle P)
    (Derivation.implicationIntroduction a) (Derivation.implicationIntroduction b)⟩

#print axioms coverStepFacts
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
