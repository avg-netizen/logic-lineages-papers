module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ModeChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalAcceptance
open InternalApplicationStepPeelSupportProof (andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambdaChildren (H : Program 1) (M W : Program 2) (raw payload domain child typ requestedDomain codomain gamma extended c : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 1) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload domain child)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain codomain)))
    (h3 : Nonempty (Derivation body Gamma (StepCons extended domain gamma)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (TermAccepted H M W codomain child extended c)) := by
  obtain ⟨hi⟩ := OriginalUniverseDecoderInternalAcceptanceUnaryProof.lambdaIff H M W raw payload domain child typ requestedDomain codomain gamma extended c h0 h1 h2 h3
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight (andRight (andRight (andRight (⟨hf⟩))))

theorem ordinaryChildren (H : Program 1) (M W : Program 2) (raw payload head base headData result types typ gamma c : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 4) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepPair payload head base)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H M W types base gamma c)) := by
  obtain ⟨hi⟩ := OriginalUniverseDecoderInternalAcceptanceUnaryProof.ordinaryIff H M W raw payload head base headData result types typ gamma c h0 h1 h2 h3
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight (andRight (andRight (andRight (⟨hf⟩))))

theorem applicationChildren (H : Program 1) (M W : Program 2) (raw payload domain fn arg typ arrow gamma c : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain fn arg)))
    (h2 : Nonempty (Derivation body Gamma (StepCons arrow domain typ)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (TermAccepted H M W arrow fn gamma c ⊓ TermAccepted H M W domain arg gamma c)) := by
  obtain ⟨hi⟩ := OriginalUniverseDecoderInternalAcceptanceBinaryProof.applicationIff H M W raw payload domain fn arg typ arrow gamma c h0 h1 h2
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight ⟨hf⟩

theorem numberedChildren (H : Program 1) (M W : Program 2) (raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 5) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepNumberedPayload payload label head recorded base extraTypes extras)))
    (h2 : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (h3 : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes)))
    (ha : Nonempty (Derivation body Gamma (TermAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (ArgumentsAccepted H M W baseTypes base gamma c ⊓ ArgumentsAccepted H M W extraTypes extras gamma c)) := by
  obtain ⟨hi⟩ := OriginalUniverseDecoderInternalAcceptanceBinaryProof.numberedIff H M W raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c h0 h1 h2 h3
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight (andRight (andRight (andRight (⟨hf⟩))))

theorem consChildren (H : Program 1) (M W : Program 2) (raw payload domain head tail typ requestedDomain tailTypes gamma c : OTerm alpha)
    (h0 : Nonempty (Derivation body Gamma (StepPair raw (numeral 7) payload)))
    (h1 : Nonempty (Derivation body Gamma (StepBinaryPayload payload domain head tail)))
    (h2 : Nonempty (Derivation body Gamma (StepArrowFields typ requestedDomain tailTypes)))
    (ha : Nonempty (Derivation body Gamma (ArgumentsAccepted H M W typ raw gamma c))) :
    Nonempty (Derivation body Gamma (TermAccepted H M W domain head gamma c ⊓ ArgumentsAccepted H M W tailTypes tail gamma c)) := by
  obtain ⟨hi⟩ := OriginalUniverseDecoderInternalAcceptanceBinaryProof.consIff H M W raw payload domain head tail typ requestedDomain tailTypes gamma c h0 h1 h2
  obtain ⟨ha⟩ := ha
  have hf := Derivation.implicationElimination (Derivation.conjunctionLeft hi) ha
  exact andRight (andRight (⟨hf⟩))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ModeChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.ModeChildrenProof
