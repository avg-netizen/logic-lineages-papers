module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationScratchTransportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph)

theorem moveCurrent {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (state current result : OTerm α) (e : Nonempty (Derivation body Γ (eqn current result)))
    (old : Nonempty (Derivation body Γ (scratchGraph state z current))) :
    Nonempty (Derivation body Γ (scratchGraph state z result)) := by
  let earlier : Fin 2 → OTerm α := ![z,current]
  let later : Fin 2 → OTerm α := ![z,result]
  apply graphInputTransport body α 2 Γ (OrdinaryArithmetic.graphFormula consCode) state earlier later _ old
  intro i
  rw [onEquality]
  exact Fin.cases ⟨refl z⟩ (Fin.cases e (fun u => Fin.elim0 u)) i

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOpenCharacterizationScratchTransportProof
