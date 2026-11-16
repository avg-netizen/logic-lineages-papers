module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem unaryVectorValue {k : Nat} (p : Program 1) (q : Program k)
    (out arg : OTerm alpha) (xs : Fin k → OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 p out arg)))
    (hq : Nonempty (Derivation body Delta (programGraph q arg xs))) :
    Nonempty (Derivation body Delta (programGraph (.composition p ![q]) out xs)) := by
  have h : (![q] : Fin 1 → Program k) = fun _ => q := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [h]
  exact unaryValue p q out arg xs hp hq

theorem guardAt (n : Nat) (key code bound answers param out : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) out code))) :
    Nonempty (Derivation body Delta (graph3 (.composition (OriginalCodeValidityGuard.check n) ![raw]) out key answers param)) := by
  have hr : Nonempty (Derivation body Delta (graph3 raw code key answers param)) :=
    unaryValue InternalUnpair.left (.projection 0) code key ![key,answers,param]
      (pairLeft key code bound hk) (projectionValue 0 ![key,answers,param])
  exact unaryVectorValue (OriginalCodeValidityGuard.check n) raw out code ![key,answers,param] hg hr

theorem zeroValue (n : Nat) (key code bound answers param : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z code))) :
    Nonempty (Derivation body Delta (graph3 (layer n) (suc z) key answers param)) := by
  apply LayerInternalProof.atPayload n key answers param z
  exact zeroBranchIntro _ _ _ z ![key,answers,param]
    (guardAt n key code bound answers param z hk hg) (constantValue 0 ![key,answers,param])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
