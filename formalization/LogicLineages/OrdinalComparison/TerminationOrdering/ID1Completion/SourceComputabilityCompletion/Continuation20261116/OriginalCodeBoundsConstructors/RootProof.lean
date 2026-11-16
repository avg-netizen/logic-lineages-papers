module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open Continuation20261115 OriginalBoundsRecombination
open Continuation20261114.OriginalHeadEncodingBridge
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem acceptedRoot (n : Nat) (raw out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (hv : Nonempty (Derivation body Delta (graph1
      (choose 6 (constant 1 0) (choose 7 (constant 1 0)
        (choose 5 (pairOf (constant 1 1) (leftOf InternalUnpair.right))
          (pairOf (constant 1 1) (constant 1 0))))) out raw))) :
    Nonempty (Derivation body Delta (graph1 (root n) out raw)) :=
  successorBranchIntro (OriginalCodeValidityGuard.check n) (constant 1 0) _ out z ![raw] hg hv

theorem termRoot (n tag : Nat) (h6 : tag ≠ 6) (h7 : tag ≠ 7) (h5 : tag ≠ 5)
    (raw out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral tag) raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) z))) :
    Nonempty (Derivation body Delta (graph1 (root n) out raw)) := by
  apply acceptedRoot n raw out hg
  apply branchNumeralIntro tag 6 InternalUnpair.left _ _ out ![raw] ht
  simp only [if_neg h6]
  apply branchNumeralIntro tag 7 InternalUnpair.left _ _ out ![raw] ht
  simp only [if_neg h7]
  apply branchNumeralIntro tag 5 InternalUnpair.left _ _ out ![raw] ht
  simp only [if_neg h5]
  exact binaryValue InternalPairing.pairing (constant 1 1) (constant 1 0)
    out (suc z) z ![raw] hp (constantValue 1 ![raw]) (constantValue 0 ![raw])

theorem nilRoot (n : Nat) (raw : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 6) raw))) :
    Nonempty (Derivation body Delta (graph1 (root n) z raw)) := by
  apply acceptedRoot n raw z hg
  apply branchNumeralIntro 6 6 InternalUnpair.left _ _ z ![raw] ht
  exact constantValue 0 ![raw]

theorem consRoot (n : Nat) (raw : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 7) raw))) :
    Nonempty (Derivation body Delta (graph1 (root n) z raw)) := by
  apply acceptedRoot n raw z hg
  apply branchNumeralIntro 7 6 InternalUnpair.left _ _ z ![raw] ht
  simp only [show (7 : Nat) ≠ 6 by decide,if_false]
  apply branchNumeralIntro 7 7 InternalUnpair.left _ _ z ![raw] ht
  exact constantValue 0 ![raw]

theorem numberedRoot (n : Nat) (raw label out : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral 5) raw)))
    (hl : Nonempty (Derivation body Delta (graph1 (leftOf InternalUnpair.right) label raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out (suc z) label))) :
    Nonempty (Derivation body Delta (graph1 (root n) out raw)) := by
  apply acceptedRoot n raw out hg
  apply branchNumeralIntro 5 6 InternalUnpair.left _ _ out ![raw] ht
  simp only [show (5 : Nat) ≠ 6 by decide,if_false]
  apply branchNumeralIntro 5 7 InternalUnpair.left _ _ out ![raw] ht
  simp only [show (5 : Nat) ≠ 7 by decide,if_false]
  apply branchNumeralIntro 5 5 InternalUnpair.left _ _ out ![raw] ht
  exact binaryValue InternalPairing.pairing (constant 1 1) (leftOf InternalUnpair.right)
    out (suc z) label ![raw] hp (constantValue 1 ![raw]) hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCodeBoundsConstructors.RootProof
