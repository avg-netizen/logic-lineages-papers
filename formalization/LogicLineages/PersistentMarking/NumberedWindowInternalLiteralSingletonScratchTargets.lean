module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalScalarSingletonInductionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)

def ExactParsedSingletonScratch : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (head decoded : OTerm α),
    Nonempty (Derivation B Γ (unary parser (suc decoded) (singletonCode head))) →
    Nonempty (Derivation B Γ (consGraph decoded head z))

def ExactLiteralSingletonCount : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code head : OTerm α),
    Nonempty (Derivation B Γ (consGraph code head z)) →
    Nonempty (Derivation B Γ (counted code head (suc z)))

def ExactLiteralSingletonMember : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code head key : OTerm α),
    Nonempty (Derivation B Γ (consGraph code head z)) →
    Nonempty (Derivation B Γ (memberGraph code key)) →
    Nonempty (Derivation B Γ (eqn head key))

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchTargets
