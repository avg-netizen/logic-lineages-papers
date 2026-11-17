module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceConjunctionProof (constantZeroValue)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open OriginalFinalVariableWeakeningSupportProof (compositionEquation)
open OriginalTransparentLambdaFinalLogicProof (iffCompose)
open OriginalTypedDecoderTransportLogicalProof (iffRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atPair (M : Program 2) (out typ context pair : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair context z))) :
    Nonempty (Derivation body Delta
      ((graph2 (InternalOriginalUniformContextMembership.contextMember (liftMember M)) out typ context).iff
        (graph2 M out typ context))) := by
  let xs : Fin 2 → OTerm alpha := ![typ,context]
  let ys : Fin 2 → OTerm alpha := ![typ,pair]
  have hpv := binaryValue InternalPairing.pairing (.projection 1) (InternalAcceptance.constantZero 2)
    pair context z xs hp (projectionValue 1 xs) (constantZeroValue xs)
  have hlv := unaryValue InternalUnpair.left (.projection 1) context pair ys
    (pairLeft pair context z hp) (projectionValue 1 ys)
  have hfirst := compositionEquation (liftMember M)
    ![.projection 0,pairOf (.projection 1) (InternalAcceptance.constantZero 2)] out xs ys
    (fun i => Fin.cases (projectionValue 0 xs) (Fin.cases hpv (fun k => Fin.elim0 k)) i)
  have hsecond := compositionEquation M ![.projection 0,leftOf (.projection 1)] out ys xs
    (fun i => Fin.cases (projectionValue 0 ys) (Fin.cases hlv (fun k => Fin.elim0 k)) i)
  exact iffCompose hfirst hsecond

theorem contextMemberLift : Targets.InternalContextMemberLift := by
  intro M body alpha Delta out typ context
  apply programCases InternalPairing.pairing ![context,z] _
  intro beta j Theta pair hj hp
  have hv : (fun i => (![context,z] i).relabel j) = ![context.relabel j,z] := by
    funext i
    exact Fin.cases rfl (Fin.cases (zRelabel j) (fun k => Fin.elim0 k)) i
  rw [hv] at hp
  simp only [iffRename,InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename]
  exact atPair M (out.relabel j) (typ.relabel j) (context.relabel j) pair hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalContextMemberLift.Proof
