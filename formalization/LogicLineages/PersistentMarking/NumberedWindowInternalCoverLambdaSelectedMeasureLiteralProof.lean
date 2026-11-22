module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaMeasureRowOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchMemoThinSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureLiteralProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaDivisionSyntaxProof (mulRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBodyRename unaryRename)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename tripleInputsRename quadInputsRename)
open NumberedWindowInternalAuxMeasureOpenDataProof (projection)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalScratchMemoThinSuccessorProof (exact_OpenSelectedMemoSuccessor)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaPrior lambdaTape)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverLambdaMeasureRowTargets
open NumberedWindowInternalCoverLambdaMeasureRowOpenProof (exact_OpenCoverLambdaMeasureRow)
open NumberedWindowInternalCoverLambdaSelectedMeasureTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem priorRename {β : Type} (ty q : OTerm α) (j : α → β) :
    (lambdaPrior ty q).relabel j = lambdaPrior (ty.relabel j) (q.relabel j) := by
  have pairRename (a b : OTerm α) :
      (pairTerm a b).relabel j = pairTerm (a.relabel j) (b.relabel j) := by
    simp only [pairTerm,addRelabel,mulRelabel]
  simp only [lambdaPrior,pairRename,packedBodyRename,numeralRename,List.map_cons,List.map_nil]

private theorem atUpdate (M : Program 1) (ty q old value mc p d w : OTerm α)
    (parent : Nonempty (Derivation body Γ (unary (lambdaMeasure M) p (lambdaTerm ty q))))
    (table : Nonempty (Derivation body Γ (tableAt (lambdaMeasureUpdate M) old (lambdaPrior ty q))))
    (update : Nonempty (Derivation body Γ (programGraph (lambdaMeasureUpdate M) value (lambdaTape ty q old))))
    (child : Nonempty (Derivation body Γ (unary (lambdaMeasure M) mc q)))
    (code : Nonempty (Derivation body Γ (codePair mc d w))) :
    LambdaMeasureEvidence M body Γ ty q old mc p d w := by
  let R := lambdaMeasureUpdate M
  let prior := lambdaPrior ty q
  let n := lambdaTerm ty q
  let xs := lambdaTape ty q old
  have parentRow := (projection R p n).mp parent
  have observed := exact_OpenSelectedMemoSuccessor R body α Γ value prior old table update
  have same := valueUnique (scratchRow (constantZero 2) R) value p ![n,z,z] observed parentRow
  have actual := outputTransport R value p xs same update
  exact ⟨table,actual,child,code,exact_OpenCoverLambdaMeasureRow M body α Γ ty q old mc p d w table actual child code⟩

private theorem withTable (M : Program 1) (ty q old mc p d w : OTerm α) (goal : Formula α)
    (parent : Nonempty (Derivation body Γ (unary (lambdaMeasure M) p (lambdaTerm ty q))))
    (table : Nonempty (Derivation body Γ (tableAt (lambdaMeasureUpdate M) old (lambdaPrior ty q))))
    (child : Nonempty (Derivation body Γ (unary (lambdaMeasure M) mc q)))
    (code : Nonempty (Derivation body Γ (codePair mc d w)))
    (next : MeasuredCoordinatesCase M body Γ ty q mc p d w goal) :
    Nonempty (Derivation body Γ goal) := by
  apply programCases (lambdaMeasureUpdate M) (lambdaTape ty q old) goal
  intro β j Δ value keep update
  simp only [lambdaTape,quadInputsRename,priorRename,zRelabel] at update
  have parent' := renameInto parent j Δ keep
  have table' := renameInto table j Δ keep
  have child' := renameInto child j Δ keep
  have code' := renameInto code j Δ keep
  simp only [unaryRename,lambdaTerm,namedRename] at parent'
  simp only [tableAt,programRename,tripleInputsRename,priorRename,zRelabel] at table'
  simp only [unaryRename] at child'
  simp only [codePair,programRename,binaryInputsRename] at code'
  exact next β j Δ (old.relabel j) keep
    (atUpdate M (ty.relabel j) (q.relabel j) (old.relabel j) value (mc.relabel j)
      (p.relabel j) (d.relabel j) (w.relabel j) parent' table' update child' code')

theorem exact_OpenCoverLambdaSelectedMeasureAtCoordinates : ExactOpenCoverLambdaSelectedMeasureAtCoordinates := by
  intro M body α Γ ty q mc p d w goal parent child code next
  let R := lambdaMeasureUpdate M
  apply programCases (scratchTable (constantZero 2) R) ![lambdaPrior ty q,z,z] goal
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  have parent' := renameInto parent j Δ keep
  have child' := renameInto child j Δ keep
  have code' := renameInto code j Δ keep
  simp only [unaryRename,lambdaTerm,namedRename] at parent'
  simp only [unaryRename] at child'
  simp only [codePair,programRename,binaryInputsRename] at code'
  apply withTable M (ty.relabel j) (q.relabel j) old (mc.relabel j) (p.relabel j)
    (d.relabel j) (w.relabel j) (goal.relabel j) parent' table child' code'
  intro γ k Ξ old' retain row
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k f]
    exact retain (f.relabel j) (keep f hf)
  simp only [Term.relabel_relabel] at row
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ old' both row

#print axioms exact_OpenCoverLambdaSelectedMeasureAtCoordinates

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureLiteralProof
