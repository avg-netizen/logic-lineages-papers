module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryDepthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryMeaningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem application (n : Nat) (raw bound fuel types heads labels tupleBound typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw typ left right))) :
    (Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) ↔
     Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.valid n raw ⊓
       (graph2 contains (numeral 1) types typ ⊓ Meaning.holds n left bound fuel types heads labels tupleBound ⊓
        Meaning.holds n right bound fuel types heads labels tupleBound)))) := by
  have he := OriginalEnumerationFields.StatementChecks.exactInternalApplication n body alpha Delta raw bound types heads labels tupleBound typ left right hc
  constructor
  · intro h
    have hf := he.mp (andLeft h)
    have hv := andLeft hf
    have ht := andLeft (andLeft (andRight hf))
    have hl := andRight (andLeft (andRight hf))
    have hr := andRight (andRight hf)
    have hd := BinaryDepthProof.forward false n raw typ left right fuel hc hv (andRight h)
    exact andIntro hv (andIntro (andIntro ht (andIntro hl (andLeft hd))) (andIntro hr (andRight hd)))
  · intro h
    have hv := andLeft h
    have ht := andLeft (andLeft (andRight h))
    have hl := andRight (andLeft (andRight h))
    have hr := andRight (andRight h)
    have hf := he.mpr (andIntro hv (andIntro (andIntro ht (andLeft hl)) (andLeft hr)))
    have hd := BinaryDepthProof.backward false n raw typ left right fuel hc hv (andIntro (andRight hl) (andRight hr))
    exact andIntro hf hd

theorem cons (n : Nat) (raw bound fuel types heads labels tupleBound typ left right : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ left right))) :
    (Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) ↔
     Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.valid n raw ⊓
       (graph2 contains (numeral 1) types typ ⊓ Meaning.holds n left bound fuel types heads labels tupleBound ⊓
        Meaning.holds n right bound fuel types heads labels tupleBound)))) := by
  have he := OriginalEnumerationFields.StatementChecks.exactInternalCons n body alpha Delta raw bound types heads labels tupleBound typ left right hc
  constructor
  · intro h
    have hf := he.mp (andLeft h)
    have hv := andLeft hf
    have ht := andLeft (andLeft (andRight hf))
    have hl := andRight (andLeft (andRight hf))
    have hr := andRight (andRight hf)
    have hd := BinaryDepthProof.forward true n raw typ left right fuel hc hv (andRight h)
    exact andIntro hv (andIntro (andIntro ht (andIntro hl (andLeft hd))) (andIntro hr (andRight hd)))
  · intro h
    have hv := andLeft h
    have ht := andLeft (andLeft (andRight h))
    have hl := andRight (andLeft (andRight h))
    have hr := andRight (andRight h)
    have hf := he.mpr (andIntro hv (andIntro (andIntro ht (andLeft hl)) (andLeft hr)))
    have hd := BinaryDepthProof.backward true n raw typ left right fuel hc hv (andIntro (andRight hl) (andRight hr))
    exact andIntro hf hd

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryMeaningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.BinaryMeaningProof
