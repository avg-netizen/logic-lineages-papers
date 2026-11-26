module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ModeChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalAcceptance
open InternalApplicationStepPeelSupportProof (andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambdaChildren (H : Program 1) (raw payload domain child typ requestedDomain codomain gamma extended : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 1) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload domain child)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (h3 : Nonempty (Derivation body Gamma (StepCons extended domain gamma)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (TermAccepted H codomain child extended)) := by
  obtain ⟨hi⟩ := OriginalTypedDecoderInternalAcceptanceUnaryProof.lambdaIff H raw payload domain child typ requestedDomain codomain gamma extended h0 h1 h2 h3
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight (andRight (⟨hf⟩))

theorem ordinaryChildren (H : Program 1) (raw payload head base headData result types typ gamma : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 4) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload head base)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H types base gamma)) := by
  obtain ⟨hi⟩ := OriginalTypedDecoderInternalAcceptanceUnaryProof.ordinaryIff H raw payload head base headData result types typ gamma h0 h1 h2 h3
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight (andRight (⟨hf⟩))

theorem applicationChildren (H : Program 1) (raw payload domain fn arg typ arrow gamma : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (TermAccepted H arrow fn gamma ⊓ TermAccepted H domain arg gamma)) := by
  obtain ⟨hi⟩ := OriginalTypedDecoderInternalAcceptanceBinaryProof.applicationIff H raw payload domain fn arg typ arrow gamma h0 h1 h2
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact ⟨hf⟩

theorem numberedChildren (H : Program 1) (raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H baseTypes base gamma ⊓ ArgumentsAccepted H extraTypes extras gamma)) := by
  obtain ⟨hi⟩ := OriginalTypedDecoderInternalAcceptanceBinaryProof.numberedIff H raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma h0 h1 h2 h3
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight (andRight (⟨hf⟩))

theorem consChildren (H : Program 1) (raw payload domain head tail typ requestedDomain tailTypes gamma : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H typ raw gamma))) :
    Nonempty (Derivation body Gamma (TermAccepted H domain head gamma ⊓ ArgumentsAccepted H tailTypes tail gamma)) := by
  obtain ⟨hi⟩ := OriginalTypedDecoderInternalAcceptanceBinaryProof.consIff H raw payload domain head tail typ requestedDomain tailTypes gamma h0 h1 h2
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight (andRight (⟨hf⟩))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ModeChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ModeChildrenProof
