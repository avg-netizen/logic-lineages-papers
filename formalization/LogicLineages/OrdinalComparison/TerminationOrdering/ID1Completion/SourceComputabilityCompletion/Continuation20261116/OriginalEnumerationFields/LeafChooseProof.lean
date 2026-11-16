module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafChooseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open InputProof SelectorInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem variableForward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param index : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor (xs 0) index)))
    (ho : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess index (xs 1))) := by
  have hr := rawAt xs key answers param hk
  have ht := variableTag raw (xs 0) index ![key,answers,param] hr hc
  have hi := variableIndex raw (xs 0) index ![key,answers,param] hr hc
  have hb := boundAt xs key answers param hk
  have hv := ChooseInternalProof.tag0Elim n ![key,answers,param] (suc z) ht ho
  have hlt := binaryRecover InternalLessThan.ltTest payload bound (suc z) index (xs 1) ![key,answers,param] hv hi hb
  exact InternalLessThanProof.lessOfAcceptance index (xs 1) hlt

theorem variableBackward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param index : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor (xs 0) index)))
    (ho : Nonempty (Derivation body Delta (InternalLessThan.strictLess index (xs 1)))) :
    Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param)) := by
  have hr := rawAt xs key answers param hk
  have ht := variableTag raw (xs 0) index ![key,answers,param] hr hc
  have hi := variableIndex raw (xs 0) index ![key,answers,param] hr hc
  have hb := boundAt xs key answers param hk
  have hlt := InternalLessThanSupportProof.acceptOfLess index (xs 1) ho
  have hv := binaryValue InternalLessThan.ltTest payload bound (suc z) index (xs 1) ![key,answers,param] hlt hi hb
  exact ChooseInternalProof.tag0Intro n ![key,answers,param] (suc z) ht hv

theorem bottomForward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param typ : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor (xs 0) typ)))
    (ho : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)) := by
  have hr := rawAt xs key answers param hk
  have ht := bottomTag raw (xs 0) typ ![key,answers,param] hr hc
  have hty := bottomType raw (xs 0) typ ![key,answers,param] hr hc
  have hS := typesAt xs key answers param hp
  have hv := ChooseInternalProof.tag3Elim n ![key,answers,param] (suc z) ht ho
  exact binaryRecover contains types payload (suc z) (xs 2) typ ![key,answers,param] hv hS hty

theorem bottomBackward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param typ : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor (xs 0) typ)))
    (ho : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ))) :
    Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param)) := by
  have hr := rawAt xs key answers param hk
  have ht := bottomTag raw (xs 0) typ ![key,answers,param] hr hc
  have hty := bottomType raw (xs 0) typ ![key,answers,param] hr hc
  have hS := typesAt xs key answers param hp
  have hv := binaryValue contains types payload (suc z) (xs 2) typ ![key,answers,param] ho hS hty
  exact ChooseInternalProof.tag3Intro n ![key,answers,param] (suc z) ht hv

theorem nilValue (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.nilConstructor (xs 0) Fin.elim0))) :
    Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param)) := by
  have hr := rawAt xs key answers param hk
  have ht := nilTag raw (xs 0) ![key,answers,param] hr hc
  exact ChooseInternalProof.tag6Intro n ![key,answers,param] (suc z) ht (constantValue 1 ![key,answers,param])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafChooseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LeafChooseProof
