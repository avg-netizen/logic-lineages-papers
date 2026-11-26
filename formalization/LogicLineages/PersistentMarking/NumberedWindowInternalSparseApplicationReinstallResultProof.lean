module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallResultProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm trans cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicApplicationShape (addressEmitter)
open NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof (addressGraph)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (reportBody)

attribute [local irreducible] programGraph addressEmitter

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem addressEqual (c e k l : OTerm α)
    (aligned : Nonempty (Derivation body Γ (eqn k l))) :
    Nonempty (Derivation body Γ (eqn (addressTerm c e k) (addressTerm c e l))) := by
  let before : Fin 3 → OTerm α := ![c,e,k]
  let after : Fin 3 → OTerm α := ![c,e,l]
  have input (i : Fin 3) :
      Nonempty (Derivation body Γ (arithmeticEmbedding.onFormula ((before i).equal (after i)))) := by
    rw [onEquality]
    exact Fin.cases ⟨refl c⟩ (Fin.cases ⟨refl e⟩ (Fin.cases aligned (fun u => Fin.elim0 u))) i
  have old : Nonempty (Derivation body Γ (programGraph addressEmitter (addressTerm c e k) before)) :=
    addressGraph c e k
  unfold programGraph at old
  have moved : Nonempty (Derivation body Γ (programGraph addressEmitter (addressTerm c e k) after)) := by
    unfold programGraph
    exact graphInputTransport body α 3 Γ (OrdinaryArithmetic.graphFormula addressEmitter)
      (addressTerm c e k) before after input old
  exact valueUnique addressEmitter (addressTerm c e k) (addressTerm c e l) after moved (addressGraph c e l)

/-- The same physical least call, at the same original packed context,
codomain and raw seed, fixes both reported output addresses. -/
theorem sameResult (least : Program 3) (c e raw y w k l : OTerm α)
    (left : Nonempty (Derivation body Γ (reportBody least c e raw y k)))
    (right : Nonempty (Derivation body Γ (reportBody least c e raw w l))) :
    Nonempty (Derivation body Γ (eqn y w)) := by
  obtain ⟨a⟩ := left
  obtain ⟨b⟩ := right
  obtain ⟨codes⟩ := valueUnique least (suc k) (suc l) ![c,e,raw]
    ⟨Derivation.conjunctionLeft a⟩ ⟨Derivation.conjunctionLeft b⟩
  obtain ⟨addr⟩ := addressEqual c e k l ⟨cancelSuc codes⟩
  exact ⟨trans (Derivation.conjunctionRight a) (trans addr (symm (Derivation.conjunctionRight b)))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallResultProof
