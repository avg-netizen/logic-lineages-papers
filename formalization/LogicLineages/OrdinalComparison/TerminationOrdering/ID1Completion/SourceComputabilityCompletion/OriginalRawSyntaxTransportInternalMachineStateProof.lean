module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineRunStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorStateProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalMachineRunStateProof
open InternalApplicationResultStackCompositionStateProof (liveOfValue)
open InternalApplicationResultStackComposition (liveState)
open InternalApplicationStepPeel (graph5)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

abbrev visitFrame : Program 3 := visitOf (.projection 0) (.projection 1) (.projection 2)
abbrev finishFrame : Program 1 := finishOf (.projection 0)

theorem visitOfValue {n : Nat} (d k p : Program n) (out erased cutoff raw : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph3 visitFrame out erased cutoff raw)))
    (hd : Nonempty (Derivation positive Delta (programGraph d erased xs)))
    (hk : Nonempty (Derivation positive Delta (programGraph k cutoff xs)))
    (hp : Nonempty (Derivation positive Delta (programGraph p raw xs))) :
    Nonempty (Derivation positive Delta (programGraph (visitOf d k p) out xs)) :=
  (substitutionGraph (rawVisitSubstitution (gs := ![d,k,p]) (.projection 0) (.projection 1) (.projection 2))
    ![erased,cutoff,raw] xs out
    (fun i => Fin.cases hd (Fin.cases hk (Fin.cases hp (fun j => Fin.elim0 j))) i)).mp hs

theorem finishOfValue {n : Nat} (p : Program n) (out raw : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph1 finishFrame out raw)))
    (hp : Nonempty (Derivation positive Delta (programGraph p raw xs))) :
    Nonempty (Derivation positive Delta (programGraph (finishOf p) out xs)) :=
  (substitutionGraph (pairSubstitution (gs := fun _ : Fin 1 => p)
      (oneSubstitution _) (.projection 0))
    ![raw] xs out (fun i => by obtain rfl := Fin.eq_zero i; exact hp)).mp hs

theorem visitValue (state d k raw suffix stack frame codedWork : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph3 visitFrame frame d k raw)))
    (hw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode codedWork frame suffix)))
    (hs : Nonempty (Derivation positive Delta (graph2 liveState state codedWork stack))) :
    Nonempty (Derivation positive Delta (graph5 visitState state d k raw suffix stack)) := by
  let xs : Fin 5 → OTerm alpha := ![d,k,raw,suffix,stack]
  exact liveOfValue _ _ state codedWork stack xs hs
    (binaryValue InternalListCodec.consCode _ _ codedWork frame suffix xs hw
      (visitOfValue _ _ _ frame d k raw xs hf (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue 2 xs))
      (projectionValue 3 xs)) (projectionValue 4 xs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateProof
