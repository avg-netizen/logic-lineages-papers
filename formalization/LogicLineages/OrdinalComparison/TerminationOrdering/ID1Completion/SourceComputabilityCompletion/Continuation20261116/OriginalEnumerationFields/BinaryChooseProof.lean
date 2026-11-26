module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryChooseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open InputProof SelectorInputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem applicationForward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param typ left right : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor (xs 0) typ left right)))
    (hrange : Nonempty (Derivation body Delta (Boolean.PointRange.At firstAnswer ![key,answers,param])))
    (hv : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ ⊓
      (graph3 firstAnswer (suc z) key answers param ⊓ graph3 secondAnswer (suc z) key answers param))) := by
  have hr := rawAt xs key answers param hk
  have ht := applicationTag raw (xs 0) typ left right ![key,answers,param] hr hc
  have hty := applicationDomain raw (xs 0) typ left right ![key,answers,param] hr hc
  exact BinaryBranchProof.forward xs key answers param typ hp hty hrange
    (ChooseInternalProof.tag2Elim n ![key,answers,param] (suc z) ht hv)

theorem applicationBackward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param typ left right : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor (xs 0) typ left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)))
    (hf : Nonempty (Derivation body Delta (graph3 firstAnswer (suc z) key answers param)))
    (hs : Nonempty (Derivation body Delta (graph3 secondAnswer (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param)) := by
  have hr := rawAt xs key answers param hk
  have ht := applicationTag raw (xs 0) typ left right ![key,answers,param] hr hc
  have hty := applicationDomain raw (xs 0) typ left right ![key,answers,param] hr hc
  exact ChooseInternalProof.tag2Intro n ![key,answers,param] (suc z) ht
    (BinaryBranchProof.backward xs key answers param typ hp hty hm hf hs)

theorem consForward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param typ left right : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor (xs 0) typ left right)))
    (hrange : Nonempty (Derivation body Delta (Boolean.PointRange.At firstAnswer ![key,answers,param])))
    (hv : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ ⊓
      (graph3 firstAnswer (suc z) key answers param ⊓ graph3 secondAnswer (suc z) key answers param))) := by
  have hr := rawAt xs key answers param hk
  have ht := consTag raw (xs 0) typ left right ![key,answers,param] hr hc
  have hty := consType raw (xs 0) typ left right ![key,answers,param] hr hc
  exact BinaryBranchProof.forward xs key answers param typ hp hty hrange
    (ChooseInternalProof.tag7Elim n ![key,answers,param] (suc z) ht hv)

theorem consBackward (n : Nat) (xs : Fin 6 → OTerm alpha) (key answers param typ left right : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor (xs 0) typ left right)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) (xs 2) typ)))
    (hf : Nonempty (Derivation body Delta (graph3 firstAnswer (suc z) key answers param)))
    (hs : Nonempty (Derivation body Delta (graph3 secondAnswer (suc z) key answers param))) :
    Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param)) := by
  have hr := rawAt xs key answers param hk
  have ht := consTag raw (xs 0) typ left right ![key,answers,param] hr hc
  have hty := consType raw (xs 0) typ left right ![key,answers,param] hr hc
  exact ChooseInternalProof.tag7Intro n ![key,answers,param] (suc z) ht
    (BinaryBranchProof.backward xs key answers param typ hp hty hm hf hs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryChooseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.BinaryChooseProof
