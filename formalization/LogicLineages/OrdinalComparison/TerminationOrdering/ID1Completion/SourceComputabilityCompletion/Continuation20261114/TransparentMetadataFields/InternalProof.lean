module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem guardAt (V q : Program 3) (out node code param : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 q out node code param))) :
    Nonempty (Derivation body Delta (graph3 (guarded V q) out node code param)) :=
  successorBranchIntro V (constant 3 0) q out z ![node,code,param] hv hq

theorem lambdaFields (V : Program 3) (target : Bool)
    (node code param raw domain child : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child))) :
    Targets.FieldsAt body Delta V target node code param (domain) (numeral 0) (numeral 0) (numeral 0) := by
  let query := TransparentChildFields.rawCode target
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht := lambdaTag query raw domain child xs hq hc
  refine ⟨?_,?_,?_,?_⟩
  · apply guardAt V (annotationRaw target) (domain) node code param hV
    apply branchNumeralIntro 1 1 (leftOf query) _ _ (domain) xs ht
    exact lambdaDomain query raw domain child xs hq hc
  · apply guardAt V (headRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 1 4 (leftOf query) _ _ (numeral 0) xs ht
    apply branchNumeralIntro 1 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs
  · apply guardAt V (labelRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 1 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs
  · apply guardAt V (typesRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 1 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs

theorem ordinaryFields (V : Program 3) (target : Bool)
    (node code param raw hd child : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw hd child))) :
    Targets.FieldsAt body Delta V target node code param (numeral 0) (hd) (numeral 0) (numeral 0) := by
  let query := TransparentChildFields.rawCode target
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht := ordinaryTag query raw hd child xs hq hc
  refine ⟨?_,?_,?_,?_⟩
  · apply guardAt V (annotationRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 4 1 (leftOf query) _ _ (numeral 0) xs ht
    apply branchNumeralIntro 4 2 (leftOf query) _ _ (numeral 0) xs ht
    apply branchNumeralIntro 4 3 (leftOf query) _ _ (numeral 0) xs ht
    apply branchNumeralIntro 4 5 (leftOf query) _ _ (numeral 0) xs ht
    apply branchNumeralIntro 4 7 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs
  · apply guardAt V (headRaw target) (hd) node code param hV
    apply branchNumeralIntro 4 4 (leftOf query) _ _ (hd) xs ht
    exact ordinaryHead query raw hd child xs hq hc
  · apply guardAt V (labelRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 4 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs
  · apply guardAt V (typesRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 4 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs

theorem applicationFields (V : Program 3) (target : Bool)
    (node code param raw domain left right : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain left right))) :
    Targets.FieldsAt body Delta V target node code param (domain) (numeral 0) (numeral 0) (numeral 0) := by
  let query := TransparentChildFields.rawCode target
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht := applicationTag query raw domain left right xs hq hc
  refine ⟨?_,?_,?_,?_⟩
  · apply guardAt V (annotationRaw target) (domain) node code param hV
    apply branchNumeralIntro 2 1 (leftOf query) _ _ (domain) xs ht
    apply branchNumeralIntro 2 2 (leftOf query) _ _ (domain) xs ht
    exact applicationDomain query raw domain left right xs hq hc
  · apply guardAt V (headRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 2 4 (leftOf query) _ _ (numeral 0) xs ht
    apply branchNumeralIntro 2 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs
  · apply guardAt V (labelRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 2 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs
  · apply guardAt V (typesRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 2 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs

theorem consFields (V : Program 3) (target : Bool)
    (node code param raw domain left right : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw domain left right))) :
    Targets.FieldsAt body Delta V target node code param (domain) (numeral 0) (numeral 0) (numeral 0) := by
  let query := TransparentChildFields.rawCode target
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht := consTag query raw domain left right xs hq hc
  refine ⟨?_,?_,?_,?_⟩
  · apply guardAt V (annotationRaw target) (domain) node code param hV
    apply branchNumeralIntro 7 1 (leftOf query) _ _ (domain) xs ht
    apply branchNumeralIntro 7 2 (leftOf query) _ _ (domain) xs ht
    apply branchNumeralIntro 7 3 (leftOf query) _ _ (domain) xs ht
    apply branchNumeralIntro 7 5 (leftOf query) _ _ (domain) xs ht
    apply branchNumeralIntro 7 7 (leftOf query) _ _ (domain) xs ht
    exact consType query raw domain left right xs hq hc
  · apply guardAt V (headRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 7 4 (leftOf query) _ _ (numeral 0) xs ht
    apply branchNumeralIntro 7 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs
  · apply guardAt V (labelRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 7 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs
  · apply guardAt V (typesRaw target) (numeral 0) node code param hV
    apply branchNumeralIntro 7 5 (leftOf query) _ _ (numeral 0) xs ht
    exact constantValue 0 xs

theorem numberedFields (V : Program 3) (target : Bool)
    (node code param raw rank hd tau base ts extras : OTerm alpha)
    (hV : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hq : Nonempty (Derivation body Delta (graph3 (TransparentChildFields.rawCode target) raw node code param)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![rank,hd,tau,base,ts,extras]))) :
    Targets.FieldsAt body Delta V target node code param (tau) (hd) (rank) (ts) := by
  let query := TransparentChildFields.rawCode target
  let xs : Fin 3 → OTerm alpha := ![node,code,param]
  have ht := numberedTag query raw rank hd tau base ts extras xs hq hc
  refine ⟨?_,?_,?_,?_⟩
  · apply guardAt V (annotationRaw target) (tau) node code param hV
    apply branchNumeralIntro 5 1 (leftOf query) _ _ (tau) xs ht
    apply branchNumeralIntro 5 2 (leftOf query) _ _ (tau) xs ht
    apply branchNumeralIntro 5 3 (leftOf query) _ _ (tau) xs ht
    apply branchNumeralIntro 5 5 (leftOf query) _ _ (tau) xs ht
    exact numberedType query raw rank hd tau base ts extras xs hq hc
  · apply guardAt V (headRaw target) (hd) node code param hV
    apply branchNumeralIntro 5 4 (leftOf query) _ _ (hd) xs ht
    apply branchNumeralIntro 5 5 (leftOf query) _ _ (hd) xs ht
    exact numberedHead query raw rank hd tau base ts extras xs hq hc
  · apply guardAt V (labelRaw target) (rank) node code param hV
    apply branchNumeralIntro 5 5 (leftOf query) _ _ (rank) xs ht
    exact numberedLabel query raw rank hd tau base ts extras xs hq hc
  · apply guardAt V (typesRaw target) (ts) node code param hV
    apply branchNumeralIntro 5 5 (leftOf query) _ _ (ts) xs ht
    exact numberedTypes query raw rank hd tau base ts extras xs hq hc

theorem internalUnary : Targets.InternalUnary := by
  intro body alpha Delta V target ordinary node code param raw metadata child hV hq hc
  cases ordinary with
  | false => exact lambdaFields V target node code param raw metadata child hV hq hc
  | true => exact ordinaryFields V target node code param raw metadata child hV hq hc

theorem internalApplication : Targets.InternalApplication := by
  intro body alpha Delta V target cons node code param raw domain left right hV hq hc
  cases cons with
  | false => exact applicationFields V target node code param raw domain left right hV hq hc
  | true => exact consFields V target node code param raw domain left right hV hq hc

theorem internalNumbered : Targets.InternalNumbered := by
  intro body alpha Delta V target node code param raw rank hd tau base ts extras hV hq hc
  exact numberedFields V target node code param raw rank hd tau base ts extras hV hq hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentMetadataFields.InternalProof
