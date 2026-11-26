module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem consSubstitution : ArgumentsReturnSubstitutionTargets.Cons := by
  intro Q body alpha Delta raw typ child tail packed first second parameter returned hc hp hq ht hr
  let inputs : Fin 2 → OTerm alpha := Fin.cons typ (Fin.cons first Fin.elim0)
  apply programCases InternalPairing.pairing inputs _
  intro beta j Theta observed hj hObserved
  simp only [graph2Rename]
  have hi : (fun i => (inputs i).relabel j) =
      Fin.cons (typ.relabel j) (Fin.cons (first.relabel j) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hi] at hObserved
  have hc := renameInto hc j Theta hj
  have hp := renameInto hp j Theta hj
  have hq := renameInto hq j Theta hj
  have ht := renameInto ht j Theta hj
  have hr := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename] at hc hp hq ht hr
  let xs : Fin 3 → OTerm beta :=
    ![raw.relabel j,first.relabel j,second.relabel j]
  let typeQuery : Program 3 := leftOf (rightOf (.projection 0))
  let typedQuery : Program 3 := pairOf typeQuery (.projection 1)
  have hType := OriginalRawSyntaxTransportInternalConstructorFieldsProof.consType
    (.projection 0) (raw.relabel j) (typ.relabel j) (child.relabel j) (tail.relabel j)
    xs (projectionValue 0 xs) hc
  have hTyped := binaryValue InternalPairing.pairing typeQuery (.projection 1)
    observed (typ.relabel j) (first.relabel j) xs hObserved hType (projectionValue 1 xs)
  have hCons := binaryRecover InternalListCodec.consCode typedQuery (.projection 2)
    (returned.relabel j) observed (second.relabel j) xs hr hTyped (projectionValue 2 xs)
  exact OriginalTypedArgumentObservationsInternalConsProof.backward Q
    (raw.relabel j) (typ.relabel j) (child.relabel j) (tail.relabel j) (packed.relabel j)
    (first.relabel j) observed (second.relabel j) (parameter.relabel j) (returned.relabel j)
    hc hp hq hObserved ht hCons

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ArgumentsReturnSubstitutionProof.consSubstitution
