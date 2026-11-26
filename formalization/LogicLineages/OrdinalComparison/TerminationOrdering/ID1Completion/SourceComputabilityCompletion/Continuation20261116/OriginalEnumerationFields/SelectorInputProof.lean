module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChooseInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.InputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorInputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open InputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem rawAt (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs))) :
    Nonempty (Derivation body Delta (graph3 raw (xs 0) key answers param)) := by
  have h := pairOfLeft (.projection 0) (.projection 1) key (xs 0) xs hk (projectionValue 0 xs)
  exact unaryValue InternalUnpair.left (.projection 0) (xs 0) key ![key,answers,param] h
    (projectionValue 0 ![key,answers,param])

theorem boundAt (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs))) :
    Nonempty (Derivation body Delta (graph3 bound (xs 1) key answers param)) := by
  have h := pairOfRight (.projection 0) (.projection 1) key (xs 1) xs hk (projectionValue 1 xs)
  exact unaryValue InternalUnpair.right (.projection 0) (xs 1) key ![key,answers,param] h
    (projectionValue 0 ![key,answers,param])

theorem typesAt (xs : Fin 6 → OTerm alpha) (key answers param : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs))) :
    Nonempty (Derivation body Delta (graph3 types (xs 2) key answers param)) := by
  have h := pairOfLeft (.projection 2) (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))
    param (xs 2) xs hp (projectionValue 2 xs)
  exact unaryValue InternalUnpair.left (.projection 2) (xs 2) param ![key,answers,param] h
    (projectionValue 2 ![key,answers,param])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.SelectorInputProof
