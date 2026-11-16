module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.InputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def keyQuery : Program 6 := pairOf (.projection 0) (.projection 1)
def parameterQuery : Program 6 := pairOf (.projection 2) (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))

theorem keyValue (xs : Fin 6 → OTerm alpha) (key : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key (xs 0) (xs 1)))) :
    Nonempty (Derivation body Delta (programGraph keyQuery key xs)) :=
  binaryValue InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)

theorem parameterValue (xs : Fin 6 → OTerm alpha) (inner middle param : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner (xs 4) (xs 5))))
    (hm : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing middle (xs 3) inner)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param (xs 2) middle))) :
    Nonempty (Derivation body Delta (programGraph parameterQuery param xs)) := by
  have hi' := binaryValue InternalPairing.pairing (.projection 4) (.projection 5) inner (xs 4) (xs 5) xs hi
    (projectionValue 4 xs) (projectionValue 5 xs)
  have hm' := binaryValue InternalPairing.pairing (.projection 3) (pairOf (.projection 4) (.projection 5))
    middle (xs 3) inner xs hm (projectionValue 3 xs) hi'
  exact binaryValue InternalPairing.pairing (.projection 2) (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))
    param (xs 2) middle xs hp (projectionValue 2 xs) hm'

theorem fieldsFromExtract (n : Nat) (xs : Fin 6 → OTerm alpha) (key param value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (he : Nonempty (Derivation body Delta (graph2 (extract n) value key param))) :
    Nonempty (Derivation body Delta (programGraph (fields n) value xs)) :=
  binaryValue (extract n) keyQuery parameterQuery value key param xs he hk hp

theorem extractFromFields (n : Nat) (xs : Fin 6 → OTerm alpha) (key param value : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (he : Nonempty (Derivation body Delta (programGraph (fields n) value xs))) :
    Nonempty (Derivation body Delta (graph2 (extract n) value key param)) :=
  binaryRecover (extract n) keyQuery parameterQuery value key param xs he hk hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.InputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.InputProof
