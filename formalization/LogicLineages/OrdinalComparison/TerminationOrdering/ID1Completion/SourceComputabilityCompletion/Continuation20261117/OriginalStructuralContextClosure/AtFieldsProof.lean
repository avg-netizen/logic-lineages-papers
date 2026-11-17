module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportUnaryAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportBinaryAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.AtFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Definitions BindingProof
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambda (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed typ gamma context requested codomain bodyGamma : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 lambdaConstructor left domain child)))
    (hrc : Nonempty (Derivation body Delta (graph2 lambdaConstructor right domain changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requested codomain)))
    (hg : Nonempty (Derivation body Delta (StepCons bodyGamma domain gamma)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.lambdaIff (signature n arity) M W left domain child typ requested codomain gamma bodyGamma context hlc hf hg) ha
  have ht := transferApply n arity M W false child changed codomain bodyGamma context ih (andRight (andRight (andRight (andRight h))))
  exact iffBackward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.lambdaIff (signature n arity) M W right domain changed typ requested codomain gamma bodyGamma context hrc hf hg)
    (andIntro (andLeft h) (andIntro (andLeft (andRight h)) (andIntro (andLeft (andRight (andRight h))) (andIntro (andLeft (andRight (andRight (andRight h)))) ht))))

theorem applicationFunction (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed sibling typ gamma context arrow : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 applicationConstructor left domain child sibling)))
    (hrc : Nonempty (Derivation body Delta (graph3 applicationConstructor right domain changed sibling)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed)))
    (hf : Nonempty (Derivation body Delta (StepCons arrow domain typ)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.applicationIff (signature n arity) M W left domain child sibling typ arrow gamma context hlc hf) ha
  have ht := transferApply n arity M W false child changed arrow gamma context ih (andLeft (andRight h))
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.applicationIff (signature n arity) M W right domain changed sibling typ arrow gamma context hrc hf)
    (andIntro (andLeft h) (andIntro ht (andRight (andRight h))))

theorem applicationArgument (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain sibling child changed typ gamma context arrow : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 applicationConstructor left domain sibling child)))
    (hrc : Nonempty (Derivation body Delta (graph3 applicationConstructor right domain sibling changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed)))
    (hf : Nonempty (Derivation body Delta (StepCons arrow domain typ)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.applicationIff (signature n arity) M W left domain sibling child typ arrow gamma context hlc hf) ha
  have ht := transferApply n arity M W false child changed domain gamma context ih (andRight (andRight h))
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.applicationIff (signature n arity) M W right domain sibling changed typ arrow gamma context hrc hf)
    (andIntro (andLeft h) (andIntro (andLeft (andRight h)) ht))

theorem ordinaryBase (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right head child changed typ gamma context headData result types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left head child)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right head changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed)))
    (hh : Nonempty (Derivation body Delta (graph1 (signature n arity) headData head)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff (signature n arity) M W left head child headData result types typ gamma context hlc hh hf) ha
  have ht := transferApply n arity M W true child changed types gamma context ih (andRight (andRight (andRight (andRight h))))
  exact iffBackward (OriginalUniverseDecoderTransportUnaryAcceptanceProof.ordinaryIff (signature n arity) M W right head changed headData result types typ gamma context hrc hh hf)
    (andIntro (andLeft h) (andIntro (andLeft (andRight h)) (andIntro (andLeft (andRight (andRight h))) (andIntro (andLeft (andRight (andRight (andRight h)))) ht))))

theorem numberedBase (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label head recorded child changed extraTypes extras typ gamma context headData result types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,child,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,changed,extraTypes,extras])))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed)))
    (hh : Nonempty (Derivation body Delta (graph1 (signature n arity) headData head)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff (signature n arity) M W left label head recorded child extraTypes extras headData result types typ gamma context hlc hh hf) ha
  have ht := transferApply n arity M W true child changed types gamma context ih (andLeft (andRight (andRight (andRight (andRight h)))))
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff (signature n arity) M W right label head recorded changed extraTypes extras headData result types typ gamma context hrc hh hf)
    (andIntro (andLeft h) (andIntro (andLeft (andRight h)) (andIntro (andLeft (andRight (andRight h))) (andIntro (andLeft (andRight (andRight (andRight h)))) (andIntro ht (andRight (andRight (andRight (andRight (andRight h))))))))))

theorem numberedExtras (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right label head recorded base extraTypes child changed typ gamma context headData result types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,head,recorded,base,extraTypes,child])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,head,recorded,base,extraTypes,changed])))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed)))
    (hh : Nonempty (Derivation body Delta (graph1 (signature n arity) headData head)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields headData result types)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W false typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W false typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff (signature n arity) M W left label head recorded base extraTypes child headData result types typ gamma context hlc hh hf) ha
  have ht := transferApply n arity M W true child changed extraTypes gamma context ih (andRight (andRight (andRight (andRight (andRight h)))))
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.numberedIff (signature n arity) M W right label head recorded base extraTypes changed headData result types typ gamma context hrc hh hf)
    (andIntro (andLeft h) (andIntro (andLeft (andRight h)) (andIntro (andLeft (andRight (andRight h))) (andIntro (andLeft (andRight (andRight (andRight h)))) (andIntro (andLeft (andRight (andRight (andRight (andRight h))))) ht)))))

theorem argumentsHead (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain child changed tail typ gamma context requested tailTypes : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left domain child tail)))
    (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right domain changed tail)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W false child changed)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W true typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W true typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff (signature n arity) M W left domain child tail typ requested tailTypes gamma context hlc hf) ha
  have ht := transferApply n arity M W false child changed domain gamma context ih (andLeft (andRight (andRight h)))
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff (signature n arity) M W right domain changed tail typ requested tailTypes gamma context hrc hf)
    (andIntro (andLeft h) (andIntro (andLeft (andRight h)) (andIntro ht (andRight (andRight (andRight h))))))

theorem argumentsTail (n : Nat) (arity : Fin n → Nat) (M W : Program 2)
    (left right domain head child changed typ gamma context requested tailTypes : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 consConstructor left domain head child)))
    (hrc : Nonempty (Derivation body Delta (graph3 consConstructor right domain head changed)))
    (ih : Nonempty (Derivation body Delta (Transfer n arity M W true child changed)))
    (hf : Nonempty (Derivation body Delta (StepArrowFields typ requested tailTypes)))
    (ha : Nonempty (Derivation body Delta (Checked n arity M W true typ left gamma context))) :
    Nonempty (Derivation body Delta (Checked n arity M W true typ right gamma context)) := by
  have h := iffForward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff (signature n arity) M W left domain head child typ requested tailTypes gamma context hlc hf) ha
  have ht := transferApply n arity M W true child changed tailTypes gamma context ih (andRight (andRight (andRight h)))
  exact iffBackward (OriginalUniverseDecoderTransportBinaryAcceptanceProof.consIff (signature n arity) M W right domain head changed typ requested tailTypes gamma context hrc hf)
    (andIntro (andLeft h) (andIntro (andLeft (andRight h)) (andIntro (andLeft (andRight (andRight h))) ht)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.AtFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalStructuralContextClosure.AtFieldsProof
