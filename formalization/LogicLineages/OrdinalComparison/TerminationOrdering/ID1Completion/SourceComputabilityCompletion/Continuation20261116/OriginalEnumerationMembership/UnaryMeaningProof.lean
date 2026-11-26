module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryDepthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaCase (n : Nat) (raw bound fuel types heads labels tupleBound typ child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw typ child))) :
    (Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) ↔
     Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.valid n raw ⊓
       ((graph2 contains (numeral 1) types typ) ⊓ Meaning.holds n child (suc bound) fuel types heads labels tupleBound)))) := by
  have he := OriginalEnumerationFields.StatementChecks.exactInternalLambda n body alpha Delta raw bound types heads labels tupleBound typ child hc
  constructor
  · intro h
    have hf := he.mp (andLeft h)
    have hv := andLeft hf
    have ht := andLeft (andRight hf)
    have hchild := andRight (andRight hf)
    have hd := UnaryDepthProof.forward false n raw typ child fuel hc hv (andRight h)
    exact andIntro hv (andIntro ht (andIntro hchild hd))
  · intro h
    have hv := andLeft h
    have ht := andLeft (andRight h)
    have hchild := andRight (andRight h)
    have hf := he.mpr (andIntro hv (andIntro ht (andLeft hchild)))
    have hd := UnaryDepthProof.backward false n raw typ child fuel hc hv (andRight hchild)
    exact andIntro hf hd

theorem ordinaryCase (n : Nat) (raw bound fuel types heads labels tupleBound head child : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child))) :
    (Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) ↔
     Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.valid n raw ⊓
       ((OriginalEnumerationFields.Targets.headAllowed n heads head) ⊓ Meaning.holds n child bound fuel types heads labels tupleBound)))) := by
  have he := OriginalEnumerationFields.StatementChecks.exactInternalOrdinary n body alpha Delta raw bound types heads labels tupleBound head child hc
  constructor
  · intro h
    have hf := he.mp (andLeft h)
    have hv := andLeft hf
    have ht := andLeft (andRight hf)
    have hchild := andRight (andRight hf)
    have hd := UnaryDepthProof.forward true n raw head child fuel hc hv (andRight h)
    exact andIntro hv (andIntro ht (andIntro hchild hd))
  · intro h
    have hv := andLeft h
    have ht := andLeft (andRight h)
    have hchild := andRight (andRight h)
    have hf := he.mpr (andIntro hv (andIntro ht (andLeft hchild)))
    have hd := UnaryDepthProof.backward true n raw head child fuel hc hv (andRight hchild)
    exact andIntro hf hd
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.UnaryMeaningProof
