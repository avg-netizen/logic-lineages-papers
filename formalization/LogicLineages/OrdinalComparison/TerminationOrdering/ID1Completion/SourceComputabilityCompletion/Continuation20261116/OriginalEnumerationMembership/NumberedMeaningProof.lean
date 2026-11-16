module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MeaningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NumberedDepthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NumberedMeaningProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem numbered (n : Nat) (raw bound fuel types heads labels tupleBound label head typ base typeList extra : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,typ,base,typeList,extra]))) :
    (Nonempty (Derivation body Delta (Meaning.holds n raw bound (suc fuel) types heads labels tupleBound)) ↔
     Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.valid n raw ⊓
       (InternalLessThan.strictLess label (suc labels) ⊓
        OriginalEnumerationFields.Targets.headAllowed n heads head ⊓ graph2 contains (numeral 1) types typ ⊓
        Meaning.holds n base bound fuel types heads labels tupleBound ⊓
        OriginalEnumerationFields.Targets.typesAllowed typeList types tupleBound ⊓
        Meaning.holds n extra bound fuel types heads labels tupleBound)))) := by
  have he := OriginalEnumerationFields.StatementChecks.exactInternalNumbered n body alpha Delta raw bound types heads labels tupleBound label head typ base typeList extra hc
  constructor
  · intro h
    have hf := he.mp (andLeft h)
    have hv := andLeft hf
    have rest := andRight hf
    have hmetadata := andLeft (andLeft (andLeft rest))
    have hb := andRight (andLeft (andLeft rest))
    have ht := andRight (andLeft rest)
    have hx := andRight rest
    have hd := NumberedDepthProof.forward n raw label head typ base typeList extra fuel hc hv (andRight h)
    exact andIntro hv (andIntro (andIntro (andIntro hmetadata (andIntro hb (andLeft hd))) ht) (andIntro hx (andRight hd)))
  · intro h
    have hv := andLeft h
    have rest := andRight h
    have hmetadata := andLeft (andLeft (andLeft rest))
    have hb := andRight (andLeft (andLeft rest))
    have ht := andRight (andLeft rest)
    have hx := andRight rest
    have hf := he.mpr (andIntro hv (andIntro (andIntro (andIntro hmetadata (andLeft hb)) ht) (andLeft hx)))
    have hd := NumberedDepthProof.backward n raw label head typ base typeList extra fuel hc hv (andIntro (andRight hb) (andRight hx))
    exact andIntro hf hd
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NumberedMeaningProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.NumberedMeaningProof
