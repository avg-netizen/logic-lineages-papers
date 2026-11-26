module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.SupportProof
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

open InternalAcceptanceBranchProof InternalTagArithmeticSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (eqn)

open Continuation20261114
theorem guardNecessary (n : Nat) (arity : Fin n → Nat) (source target param : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (structural n arity) (numeral 1) source target param))) :
    Nonempty (Derivation body Delta (graph3 (OriginalStructuralDecoderSuppliers.valid n) (numeral 1) source target param)) := by
  let V := OriginalStructuralDecoderSuppliers.valid n
  let A := graph3 V (numeral 1) source target param
  apply formulaCases A
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have hn : Nonempty (Derivation body (A.not :: Delta) A.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hz := OriginalTransparentLambdaValidityInternalBranchSupportProof.conjunctionReject
      (OriginalStructuralDecoderSuppliers.contextAt n)
      (InternalAcceptance.conjunction (OriginalStructuralDecoderSuppliers.packedAt n 0) (OriginalStructuralDecoderSuppliers.packedAt n 1))
      ![source,target,param] hn
    have hf := zeroBranchElim V (InternalAcceptance.constantZero 3)
      (.composition (OriginalDecodedExchangeEquation.exchange n arity)
        ![InstalledExchangeRecursor.nodeCode,InstalledExchangeRecursor.windowCode (OriginalStructuralDecoderSuppliers.window n)])
      (numeral 1) ![source,target,param] hz (withHyp h A.not)
    obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 3) (numeral 1) (numeral 0) ![source,target,param] hf
      (InternalAcceptanceConjunctionProof.constantZeroValue ![source,target,param])
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩

theorem nodeAt (source target param tyA codeA tyB codeB node : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source tyA codeA)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tyB codeB)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node codeA codeB))) :
    Nonempty (Derivation body Delta (graph3 InstalledExchangeRecursor.nodeCode node source target param)) := by
  let xs : Fin 3 → OTerm alpha := ![source,target,param]
  have ha := unaryValue InternalUnpair.right (.projection 0) codeA source xs (pairRight source tyA codeA hs) (projectionValue 0 xs)
  have hb := unaryValue InternalUnpair.right (.projection 1) codeB target xs (pairRight target tyB codeB ht) (projectionValue 1 xs)
  exact binaryValue InternalPairing.pairing (InstalledExchangeRecursor.codeField 0) (InstalledExchangeRecursor.codeField 1)
    node codeA codeB xs hn ha hb

theorem atContextFactor (n : Nat) (arity : Fin n → Nat) (codeA codeB ctx win table node out : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ctx win table)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node codeA codeB))) :
    (Nonempty (Derivation body Delta (graph3 (atContext n arity) out codeA codeB ctx)) ↔
     Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) out node win))) := by
  let xs : Fin 3 → OTerm alpha := ![codeA,codeB,ctx]
  have hp := binaryValue InternalPairing.pairing (.projection 0) (.projection 1) node codeA codeB xs hn
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hl := unaryValue InternalUnpair.left (.projection 2) win ctx xs (pairLeft ctx win table hw) (projectionValue 2 xs)
  constructor
  · intro h
    exact binaryRecover (OriginalDecodedExchangeEquation.exchange n arity)
      (InternalApplicationCertificateConstructors.pairOf (.projection 0) (.projection 1))
      (InternalApplicationCertificateConstructors.leftOf (.projection 2)) out node win xs h hp hl
  · intro h
    exact binaryValue (OriginalDecodedExchangeEquation.exchange n arity)
      (InternalApplicationCertificateConstructors.pairOf (.projection 0) (.projection 1))
      (InternalApplicationCertificateConstructors.leftOf (.projection 2)) out node win xs h hp hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.SupportProof
