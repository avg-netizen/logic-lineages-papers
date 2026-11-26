module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeMetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeTransferProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open SyntaxProof (acceptedRename)
open InternalTagArithmeticSupportProof (trans symm)
theorem preserved (n : Nat) (arity : Fin n → Nat)
 (source target parameter sourceType sourceRaw targetType targetRaw rootTypeRef boundsRef : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceType sourceRaw)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetType targetRaw)))
 (he : Nonempty (Derivation body Delta (graph3 (OriginalConcreteStructuralEdge.edge n arity) (numeral 1) source target parameter)))
 (ha : Nonempty (Derivation body Delta (accepted n arity sourceType sourceRaw rootTypeRef boundsRef))) :
 Nonempty (Derivation body Delta (accepted n arity targetType targetRaw rootTypeRef boundsRef)) := by
 apply InternalAcceptanceSupportProof.programCases (OriginalCodeBoundsRecursion.bounds n) ![targetRaw] _
 intro beta j Theta targetBounds hj hnew
 have hx : (fun i => (![targetRaw] i).relabel j) = ![targetRaw.relabel j] := by
  funext i; fin_cases i <;> rfl
 rw [hx] at hnew
 rw [acceptedRename]
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename] at hs'
 have ht' := renameInto ht j Theta hj
 simp only [graph2Rename] at ht'
 have he' := renameInto he j Theta hj
 simp only [graph3Rename,numeral,sucRelabel,zRelabel] at he'
 have ha' := renameInto ha j Theta hj
 rw [acceptedRename] at ha'
 have hm := EdgeMetadataProof.preserved n arity
   (source.relabel j) (target.relabel j) (parameter.relabel j)
   (sourceType.relabel j) (sourceRaw.relabel j) (targetType.relabel j) (targetRaw.relabel j)
   (boundsRef.relabel j) targetBounds hs' ht' (andRight ha') hnew he'
 have htype := andLeft hm
 have hbounds := andRight hm
 have hroot := andLeft ha'
 obtain ⟨htype⟩ := htype
 obtain ⟨hroot⟩ := hroot
 obtain ⟨hbounds⟩ := hbounds
 exact andIntro ⟨trans hroot htype⟩
   (outputTransport (OriginalCodeBoundsRecursion.bounds n) targetBounds (boundsRef.relabel j)
     ![targetRaw.relabel j] ⟨symm hbounds⟩ hnew)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeTransferProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.EdgeTransferProof
