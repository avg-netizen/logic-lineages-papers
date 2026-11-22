module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafGrammarWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafStrictWindowProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchLeavesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (renameIdentity)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedMeasureBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarBase)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase)
open NumberedWindowInternalCoverNamedResultTargets (namedResultBase)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverNamedLeafSharedMeasureProof (exact_OpenCoverNamedLeafSharedMeasure)
open NumberedWindowInternalCoverTypeLeafSharedMeasureProof (exact_OpenCoverTypeLeafSharedMeasure)
open NumberedWindowInternalCoverNamedLeafGrammarWindowProof (exact_OpenCoverNamedLeafGrammarWindowK)
open NumberedWindowInternalCoverTypeLeafStrictWindowProof (exact_OpenCoverTypeLeafStrictWindowK)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets
open NumberedWindowInternalCoverFittedInductionDispatchTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem unchanged (f : Formula α) (h : f ∈ Γ) : f.relabel id ∈ Γ := by
  simpa only [renameIdentity] using h

theorem exact_OpenFittedNamedFacts (V TV M : Program 1) (B : Program 2) (TW : Program 1)
    (s : Settings) (b : Bool) (raw p vertices ctx result ty i : OTerm α) (goal : Formula α)
    (row : PackedRow (fittedPrograms s V TV M B TW) s body Γ raw (namedTerm b.toNat ty i)
      p vertices ctx result b.toNat [ty,i]) :
    Supplies body Γ goal (fun β j Δ => NamedFacts s body Δ (p.relabel j) (ty.relabel j) (i.relabel j)) := by
  intro next
  have exactBounds := exact_OpenCoverNamedLeafSharedMeasure b M body α Γ ty i p row.data.parent.measured
  have actualK := exact_OpenCoverNamedLeafGrammarWindowK b s (lexicalBoundBase (namedResultBase B))
    (refitGuard s TW) body α Γ ctx ty i result row.data.typed
  have evidence : NamedFacts s body Γ p ty i := ⟨z,i,exactBounds.1,actualK,exactBounds.2⟩
  have moved : NamedFacts s body Γ (p.relabel id) (ty.relabel id) (i.relabel id) := by
    simpa only [Term.relabel_id] using evidence
  simpa only [renameIdentity] using next α id Γ unchanged moved

theorem exact_OpenFittedTypeOnlyFacts (V TV M : Program 1) (B : Program 2) (TW : Program 1)
    (s : Settings) (raw p vertices ctx result ty : OTerm α) (goal : Formula α)
    (row : PackedRow (fittedPrograms s V TV M B TW) s body Γ raw (typeLeafTerm ty)
      p vertices ctx result 3 [ty]) :
    Supplies body Γ goal (fun β j Δ => TypeFacts s body Δ (p.relabel j) (ty.relabel j)) := by
  intro next
  have exactPair := exact_OpenCoverTypeLeafSharedMeasure (namedMeasureBase M) body α Γ ty p row.data.parent.measured
  have actualK := exact_OpenCoverTypeLeafStrictWindowK s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))
    (refitGuard s TW) body α Γ ctx ty result row.data.typed
  have evidence : TypeFacts s body Γ p ty := ⟨z,z,exactPair,actualK⟩
  have moved : TypeFacts s body Γ (p.relabel id) (ty.relabel id) := by
    simpa only [Term.relabel_id] using evidence
  simpa only [renameIdentity] using next α id Γ unchanged moved

#print axioms exact_OpenFittedNamedFacts
#print axioms exact_OpenFittedTypeOnlyFacts

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchLeavesProof
