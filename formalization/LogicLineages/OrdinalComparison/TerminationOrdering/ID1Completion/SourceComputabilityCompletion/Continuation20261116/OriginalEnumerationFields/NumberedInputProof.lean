module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ParameterDeepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedInputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open InputProof SelectorInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem tagAt (xs : Fin 6 → OTerm alpha) (key answers param label head typ base types extra : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,types,extra]))) :
    Nonempty (Derivation body Delta (graph3 tag (numeral 5) key answers param)) :=
  OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedTag raw (xs 0) label head typ base types extra
    ![key,answers,param] (SelectorInputProof.rawAt xs key answers param hk) hc

theorem labelAt (xs : Fin 6 → OTerm alpha) (key answers param label head typ base types extra : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,types,extra]))) :
    Nonempty (Derivation body Delta (graph3 numberedLabel label key answers param)) :=
  OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedLabel raw (xs 0) label head typ base types extra
    ![key,answers,param] (SelectorInputProof.rawAt xs key answers param hk) hc

theorem headAt (xs : Fin 6 → OTerm alpha) (key answers param label head typ base types extra : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,types,extra]))) :
    Nonempty (Derivation body Delta (graph3 numberedHead head key answers param)) :=
  OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedHead raw (xs 0) label head typ base types extra
    ![key,answers,param] (SelectorInputProof.rawAt xs key answers param hk) hc

theorem typeAt (xs : Fin 6 → OTerm alpha) (key answers param label head typ base types extra : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,types,extra]))) :
    Nonempty (Derivation body Delta (graph3 numberedType typ key answers param)) :=
  OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedType raw (xs 0) label head typ base types extra
    ![key,answers,param] (SelectorInputProof.rawAt xs key answers param hk) hc

theorem typesAt (xs : Fin 6 → OTerm alpha) (key answers param label head typ base types extra : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor (xs 0) ![label,head,typ,base,types,extra]))) :
    Nonempty (Derivation body Delta (graph3 numberedTypes types key answers param)) :=
  OriginalRawSyntaxTransportInternalConstructorFieldsProof.numberedTypes raw (xs 0) label head typ base types extra
    ![key,answers,param] (SelectorInputProof.rawAt xs key answers param hk) hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NumberedInputProof
