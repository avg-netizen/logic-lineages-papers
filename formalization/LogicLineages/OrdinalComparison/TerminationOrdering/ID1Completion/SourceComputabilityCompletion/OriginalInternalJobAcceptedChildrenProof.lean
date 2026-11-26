module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAcceptedChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleSyntaxProof
open OriginalUniverseDecoderInternalAcceptance OriginalTypedDecoderStepSpecification
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem termAdmissible (H : Program 1) (M W : Program 2) (typ raw gamma c : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
 Nonempty (Derivation body Delta (Admissible H M W (numeral 0) typ raw gamma c)) := by
 obtain ⟨ha⟩ := ha
 exact ⟨orLeft (Derivation.conjunctionIntroduction
  (by simpa only [equalEqn] using (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 0))) ha)⟩
theorem listAdmissible (H : Program 1) (M W : Program 2) (types raw gamma c : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H M W types raw gamma c))) :
 Nonempty (Derivation body Delta (Admissible H M W (numeral 1) (numeral 0) raw gamma c)) := by
 obtain ⟨ha⟩ := argumentsIntro H M W raw gamma c types ha
 have h1 : Derivation body Delta (equal (numeral 1) (numeral 1)) := by
  simpa only [equalEqn] using (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 1))
 have h0 : Derivation body Delta (equal (numeral 0) (numeral 0)) := by
  simpa only [equalEqn] using (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) (numeral 0))
 exact ⟨orRight (Derivation.conjunctionIntroduction h1 (Derivation.conjunctionIntroduction h0 ha))⟩
theorem lambdaChild (H : Program 1) (M W : Program 2)
 (raw payload domain child typ requestedDomain codomain gamma extended c : OTerm alpha)
 (h0 : Nonempty (Derivation body Delta (StepPair raw (numeral 1) payload)))
 (h1 : Nonempty (Derivation body Delta (StepPair payload domain child)))
 (h2 : Nonempty (Derivation body Delta (StepArrowFields typ requestedDomain codomain)))
 (h3 : Nonempty (Derivation body Delta (StepCons extended domain gamma)))
 (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
 Nonempty (Derivation body Delta (Admissible H M W (numeral 0) codomain child extended c)) := by
 obtain ⟨law⟩ := OriginalUniverseDecoderInternalAcceptanceUnaryProof.lambdaIff H M W raw payload domain child typ requestedDomain codomain gamma extended c h0 h1 h2 h3
 have facts := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft law) (Classical.choice ha))
 exact termAdmissible H M W codomain child extended c (andRight (andRight (andRight (andRight facts))))
theorem applicationChildren (H : Program 1) (M W : Program 2)
 (raw payload domain fn arg typ arrow gamma c : OTerm alpha)
 (h0 : Nonempty (Derivation body Delta (StepPair raw (numeral 2) payload)))
 (h1 : Nonempty (Derivation body Delta (StepBinaryPayload payload domain fn arg)))
 (h2 : Nonempty (Derivation body Delta (StepCons arrow domain typ)))
 (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
 Nonempty (Derivation body Delta
  (Admissible H M W (numeral 0) arrow fn gamma c ⊓ Admissible H M W (numeral 0) domain arg gamma c)) := by
 obtain ⟨law⟩ := OriginalUniverseDecoderInternalAcceptanceBinaryProof.applicationIff H M W raw payload domain fn arg typ arrow gamma c h0 h1 h2
 have facts := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft law) (Classical.choice ha))
 exact andIntro (termAdmissible H M W arrow fn gamma c (andLeft (andRight facts)))
  (termAdmissible H M W domain arg gamma c (andRight (andRight facts)))
theorem ordinaryChild (H : Program 1) (M W : Program 2)
 (raw payload head base headData result types typ gamma c : OTerm alpha)
 (h0 : Nonempty (Derivation body Delta (StepPair raw (numeral 4) payload)))
 (h1 : Nonempty (Derivation body Delta (StepPair payload head base)))
 (h2 : Nonempty (Derivation body Delta (programGraph H headData ![head])))
 (h3 : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
 (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
 Nonempty (Derivation body Delta (Admissible H M W (numeral 1) (numeral 0) base gamma c)) := by
 obtain ⟨law⟩ := OriginalUniverseDecoderInternalAcceptanceUnaryProof.ordinaryIff H M W raw payload head base headData result types typ gamma c h0 h1 h2 h3
 have facts := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft law) (Classical.choice ha))
 exact listAdmissible H M W types base gamma c (andRight (andRight (andRight (andRight facts))))
theorem numberedChildren (H : Program 1) (M W : Program 2)
 (raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c : OTerm alpha)
 (h0 : Nonempty (Derivation body Delta (StepPair raw (numeral 5) payload)))
 (h1 : Nonempty (Derivation body Delta (StepNumberedPayload payload label head recorded base extraTypes extras)))
 (h2 : Nonempty (Derivation body Delta (programGraph H headData ![head])))
 (h3 : Nonempty (Derivation body Delta (StepArrowFields headData headResult baseTypes)))
 (ha : Nonempty (Derivation body Delta (TermAccepted H M W typ raw gamma c))) :
 Nonempty (Derivation body Delta
  (Admissible H M W (numeral 1) (numeral 0) base gamma c ⊓ Admissible H M W (numeral 1) (numeral 0) extras gamma c)) := by
 obtain ⟨law⟩ := OriginalUniverseDecoderInternalAcceptanceBinaryProof.numberedIff H M W raw payload label head recorded base extraTypes extras headData headResult baseTypes typ gamma c h0 h1 h2 h3
 have facts := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft law) (Classical.choice ha))
 have children := andRight (andRight (andRight (andRight facts)))
 exact andIntro (listAdmissible H M W baseTypes base gamma c (andLeft children))
  (listAdmissible H M W extraTypes extras gamma c (andRight children))
theorem consChildren (H : Program 1) (M W : Program 2)
 (raw payload domain head tail types requestedDomain tailTypes gamma c : OTerm alpha)
 (h0 : Nonempty (Derivation body Delta (StepPair raw (numeral 7) payload)))
 (h1 : Nonempty (Derivation body Delta (StepBinaryPayload payload domain head tail)))
 (h2 : Nonempty (Derivation body Delta (StepArrowFields types requestedDomain tailTypes)))
 (ha : Nonempty (Derivation body Delta (ArgumentsAccepted H M W types raw gamma c))) :
 Nonempty (Derivation body Delta
  (Admissible H M W (numeral 0) domain head gamma c ⊓ Admissible H M W (numeral 1) (numeral 0) tail gamma c)) := by
 obtain ⟨law⟩ := OriginalUniverseDecoderInternalAcceptanceBinaryProof.consIff H M W raw payload domain head tail types requestedDomain tailTypes gamma c h0 h1 h2
 have facts := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionLeft law) (Classical.choice ha))
 have children := andRight (andRight facts)
 exact andIntro (termAdmissible H M W domain head gamma c (andLeft children))
  (listAdmissible H M W tailTypes tail gamma c (andRight children))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAcceptedChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAcceptedChildrenProof
