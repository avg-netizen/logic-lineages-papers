module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.InputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def metadataTail (n : Nat) : Program 2 := pairOf (labels n) (size n)
def metadataMiddle (n : Nat) (arity : Fin n → Nat) : Program 2 := pairOf (heads n arity) (metadataTail n)

theorem nodeRecover (n : Nat) (seed param key b f : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 (node n) key seed param)))
    (hb : Nonempty (Derivation body Delta (graph2 bound b seed param)))
    (hf : Nonempty (Derivation body Delta (graph2 (fuel n) f seed param))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key b f)) :=
  binaryRecover InternalPairing.pairing bound (fuel n) key b f ![seed,param] hk hb hf

theorem tailRecover (n : Nat) (seed param tail ls sz : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 (metadataTail n) tail seed param)))
    (hl : Nonempty (Derivation body Delta (graph2 (labels n) ls seed param)))
    (hs : Nonempty (Derivation body Delta (graph2 (size n) sz seed param))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail ls sz)) :=
  binaryRecover InternalPairing.pairing (labels n) (size n) tail ls sz ![seed,param] ht hl hs

theorem middleRecover (n : Nat) (arity : Fin n → Nat) (seed param mid hs tail : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 (metadataMiddle n arity) mid seed param)))
    (hh : Nonempty (Derivation body Delta (graph2 (heads n arity) hs seed param)))
    (ht : Nonempty (Derivation body Delta (graph2 (metadataTail n) tail seed param))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mid hs tail)) :=
  binaryRecover InternalPairing.pairing (heads n arity) (metadataTail n) mid hs tail ![seed,param] hm hh ht

theorem parameterRecover (n : Nat) (arity : Fin n → Nat) (seed param meta ts mid : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 (parameter n arity) meta seed param)))
    (ht : Nonempty (Derivation body Delta (graph2 types ts seed param)))
    (hp : Nonempty (Derivation body Delta (graph2 (metadataMiddle n arity) mid seed param))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing meta ts mid)) :=
  binaryRecover InternalPairing.pairing types (metadataMiddle n arity) meta ts mid ![seed,param] hm ht hp

theorem enumerationRecover (n : Nat) (arity : Fin n → Nat) (seed param key meta out : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph2 (enumerated n arity) out seed param)))
    (hk : Nonempty (Derivation body Delta (graph2 (node n) key seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 (parameter n arity) meta seed param))) :
    Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out key meta)) :=
  binaryRecover (OriginalEnumerationRecursion.enumeration n) (node n) (parameter n arity)
    out key meta ![seed,param] he hk hm

theorem frontendRecover (n : Nat) (arity : Fin n → Nat) (seed param out en root : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 (frontend n arity) out seed param)))
    (he : Nonempty (Derivation body Delta (graph2 (enumerated n arity) en seed param)))
    (hr : Nonempty (Derivation body Delta (graph2 rootType root seed param))) :
    Nonempty (Derivation body Delta (graph2 pairRoots out en root)) :=
  binaryRecover pairRoots (enumerated n arity) rootType out en root ![seed,param] hf he hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.InputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.InputProof
