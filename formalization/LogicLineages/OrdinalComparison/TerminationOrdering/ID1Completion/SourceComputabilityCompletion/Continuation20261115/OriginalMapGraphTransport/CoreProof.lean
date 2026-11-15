module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.StepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.CoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalListCodecDecompositionSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 ExchangeMapGraph
open Targets AgreementSyntaxProof AgreementBindingProof
open InductionDefinitions InductionSyntaxProof BindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atLookup (raw head tail left right out rest value : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (lookupAgreement raw left right)))
    (hr : Nonempty (Derivation body Delta (graph2 mapGraph rest tail left)))
    (hs : Nonempty (Derivation body Delta (graph3 mapStep out head rest left)))
    (hl : Nonempty (Derivation body Delta (graph2 lookup value left head)))
    : Nonempty (Derivation body Delta (graph2 mapGraph out raw right)) := by
  have hright := agreementApply raw left right head value ha (RestrictionProof.headMember raw head tail hc) hl
  have hstep := StepProof.atValue head rest left right out value hl hright hs
  have htail := belowRawApply raw tail left right rest ih (consTailDescent raw head tail hc)
    (andIntro (RestrictionProof.tailAgreement raw head tail left right hc ha) hr)
  exact InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) mapStep
    raw head tail rest out (Fin.cons right Fin.elim0) hc htail hstep

theorem atStep (raw head tail left right out rest : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (lookupAgreement raw left right)))
    (hr : Nonempty (Derivation body Delta (graph2 mapGraph rest tail left)))
    (hs : Nonempty (Derivation body Delta (graph3 mapStep out head rest left)))
    : Nonempty (Derivation body Delta (graph2 mapGraph out raw right)) := by
  apply programCases lookup (Fin.cons left (Fin.cons head Fin.elim0)) _
  intro beta j Theta value hj hl
  simp only [consTermRename,emptyRename] at hl
  rw [graph2Rename]
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  rw [agreementRename] at haj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hsj := InternalGraphCompositionFunctionalityProof.renameInto hs j Theta hj
  rw [graph3Rename] at hsj
  exact atLookup (raw.relabel j) (head.relabel j) (tail.relabel j) (left.relabel j) (right.relabel j) (out.relabel j) (rest.relabel j) value ihj hcj haj hrj hsj hl

theorem consCore (raw head tail left right out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (ha : Nonempty (Derivation body Delta (lookupAgreement raw left right)))
    (hv : Nonempty (Derivation body Delta (graph2 mapGraph out raw left)))
    : Nonempty (Derivation body Delta (graph2 mapGraph out raw right)) := by
  have hx := InternalRawListRecursionProof.consForward (InternalAcceptance.constantZero 1) mapStep raw head tail out (Fin.cons left Fin.elim0) hc hv
  apply InternalRawListRecursionProof.stepCases (InternalAcceptance.constantZero 1) mapStep out head tail (Fin.cons left Fin.elim0) _ hx
  intro beta j Theta rest hj hr hs
  simp only [consTermRename,emptyRename] at hr hs
  rw [graph2Rename]
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [graph2Rename] at hcj
  have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  rw [agreementRename] at haj
  exact atStep (raw.relabel j) (head.relabel j) (tail.relabel j) (left.relabel j) (right.relabel j) (out.relabel j) rest ihj hcj haj hr hs

theorem nilCore (raw left right out : OTerm alpha)
    (hz : Nonempty (Derivation body Delta (eqn raw z)))
    (hv : Nonempty (Derivation body Delta (graph2 mapGraph out raw left))) :
    Nonempty (Derivation body Delta (graph2 mapGraph out raw right)) := by
  have hl0 : Nonempty (Derivation body Delta (graph2 mapGraph z z left)) :=
    InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) mapStep z (Fin.cons left Fin.elim0)
      (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons left Fin.elim0))
  have hr0 : Nonempty (Derivation body Delta (graph2 mapGraph z z right)) :=
    InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) mapStep z (Fin.cons right Fin.elim0)
      (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons right Fin.elim0))
  have hv0 := headTransport mapGraph out raw z (Fin.cons left Fin.elim0) hz hv
  obtain ⟨he⟩ := valueUnique mapGraph out z ![z,left] hv0 hl0
  obtain ⟨hz⟩ := hz
  exact headTransport mapGraph out z raw (Fin.cons right Fin.elim0) ⟨symm hz⟩
    (outputTransport mapGraph z out ![z,right] ⟨symm he⟩ hr0)

theorem core (raw left right out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (ha : Nonempty (Derivation body Delta (lookupAgreement raw left right)))
    (hv : Nonempty (Derivation body Delta (graph2 mapGraph out raw left)))
    : Nonempty (Derivation body Delta (graph2 mapGraph out raw right)) := by
  apply OriginalContextInsertionLengthProof.listCases raw _
  · exact nilCore raw left right out ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hv (eqn raw z))
  · intro beta j Theta head tail hj hc
    rw [graph2Rename]
    have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih j Theta hj
    rw [belowRawRename] at ihj
    have haj := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
    rw [agreementRename] at haj
    have hvj := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
    rw [graph2Rename] at hvj
    exact consCore (raw.relabel j) head tail (left.relabel j) (right.relabel j) (out.relabel j) ihj hc haj hvj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalMapGraphTransport.CoreProof
