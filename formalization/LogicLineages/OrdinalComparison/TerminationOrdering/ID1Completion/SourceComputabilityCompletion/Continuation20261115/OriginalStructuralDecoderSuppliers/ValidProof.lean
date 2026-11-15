module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.ValidProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem contextFactor (n : Nat) (xs : Fin 3 → OTerm alpha) (ctx rest : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (xs 2) ctx rest))) :
    (Nonempty (Derivation body Delta (programGraph (contextAt n) (numeral 1) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) ctx))) := by
  have hl := unaryValue InternalUnpair.left (.projection 2) ctx (xs 2) xs
    (pairLeft (xs 2) ctx rest hp) (projectionValue 2 xs)
  constructor
  · intro h
    exact unaryRecover (OriginalDecodedContextValidity.contextGuard n)
      (InternalApplicationCertificateConstructors.leftOf (.projection 2)) (numeral 1) ctx xs h hl
  · intro h
    exact unaryValue (OriginalDecodedContextValidity.contextGuard n)
      (InternalApplicationCertificateConstructors.leftOf (.projection 2)) (numeral 1) ctx xs h hl

theorem packedFactor (n : Nat) (i : Fin 3) (xs : Fin 3 → OTerm alpha) (ty code : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (xs i) ty code))) :
    (Nonempty (Derivation body Delta (programGraph (packedAt n i) (numeral 1) xs)) ↔
     Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) code))) := by
  have hr := unaryValue InternalUnpair.right (.projection i) code (xs i) xs
    (pairRight (xs i) ty code hp) (projectionValue i xs)
  constructor
  · intro h
    exact unaryRecover (OriginalCodeValidityGuard.check n)
      (InternalApplicationCertificateConstructors.rightOf (.projection i)) (numeral 1) code xs h hr
  · intro h
    exact unaryValue (OriginalCodeValidityGuard.check n)
      (InternalApplicationCertificateConstructors.rightOf (.projection i)) (numeral 1) code xs h hr

theorem internalValid : Targets.InternalValid := by
  intro n body alpha Delta source target param tyA codeA tyB codeB ctx rest hs ht hp
  let xs : Fin 3 → OTerm alpha := ![source,target,param]
  constructor
  · intro h
    have h0 := conjunctionRecover (contextAt n) (InternalAcceptance.conjunction (packedAt n 0) (packedAt n 1)) xs h
    have h1 := conjunctionRecover (packedAt n 0) (packedAt n 1) xs (andRight h0)
    exact andIntro ((contextFactor n xs ctx rest hp).mp (andLeft h0))
      (andIntro ((packedFactor n 0 xs tyA codeA hs).mp (andLeft h1))
        ((packedFactor n 1 xs tyB codeB ht).mp (andRight h1)))
  · intro h
    have h0 := (contextFactor n xs ctx rest hp).mpr (andLeft h)
    have h1 := (packedFactor n 0 xs tyA codeA hs).mpr (andLeft (andRight h))
    have h2 := (packedFactor n 1 xs tyB codeB ht).mpr (andRight (andRight h))
    exact conjunctionAccept (contextAt n) (InternalAcceptance.conjunction (packedAt n 0) (packedAt n 1)) xs h0
      (conjunctionAccept (packedAt n 0) (packedAt n 1) xs h1 h2)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.ValidProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.ValidProof
