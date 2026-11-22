module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoTailProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeKeyChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoConsDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalAuxExchangeKeyChecks (exact_OpenRawConsBounds)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter binaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (readRow tableAt)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalCoverArgumentMemoTailProof (actualArgumentTailLookup)
open NumberedWindowInternalCoverArgumentMemoTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualArgumentCombine (F : Program 1) (h a old out mh mt : OTerm α)
    (table : Nonempty (Derivation body Γ (tableAt (argumentUpdate F) old (pairTerm h a))))
    (update : Nonempty (Derivation body Γ
      (programGraph (argumentUpdate F) out ![pairTerm h a,old,z,z])))
    (hd : Nonempty (Derivation body Γ (unary F mh h)))
    (tl : Nonempty (Derivation body Γ (readRow (argumentUpdate F) mt a))) :
    Nonempty (Derivation body Γ (programGraph chosenCombine out ![mh,mt])) := by
  let prior := pairTerm h a
  let raw := rawCons h a
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) h a
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have good : Nonempty (Derivation body Γ (programGraph argumentCell (suc z) xs)) :=
    unaryGraph cellGood currentKey (suc z) raw xs ⟨Derivation.conjunctionLeft cell⟩ key
  have header : Nonempty (Derivation body Γ (programGraph argumentHead h xs)) :=
    unaryGraph cellHead currentKey h raw xs
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩ key
  have tail : Nonempty (Derivation body Γ (programGraph argumentTail a xs)) :=
    unaryGraph cellTail currentKey a raw xs
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩ key
  have ph : Nonempty (Derivation body Γ (programGraph (headMeasure F) mh xs)) :=
    unaryGraph F argumentHead mh h xs hd header
  have pt := actualArgumentTailLookup (argumentUpdate F) a mt prior old tail
    (exact_OpenRawConsBounds body α Γ h a).2 tl table
  have positive := successorBranchElim argumentCell (constantZero 4)
    (binaryAfter chosenCombine (headMeasure F) tailMeasure) out z xs good update
  apply compositionRecover chosenCombine ![headMeasure F,tailMeasure] out xs ![mh,mt] positive
  intro i
  exact Fin.cases ph (Fin.cases pt (fun j => Fin.elim0 j)) i

#print axioms actualArgumentCombine

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoConsDataProof
