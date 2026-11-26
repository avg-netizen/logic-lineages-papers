module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AppendIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermSuffixIdentityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open SixSol20261112.Context
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem split     (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (count typ raw parameter window gamma rawJob tagged job front suffix jobs annotatedFront mapped full : OTerm alpha)
    (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tagged typ rawJob)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z tagged)))
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) count raw)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix raw parameter)))
    (happ : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs front suffix)))
    (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedFront count z typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) mapped suffix typ)))
    (hf : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion full job)))
    :
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append full annotatedFront mapped)) := by
  have hv := OriginalRawSyntaxTransportInternalConstructorArityCasesProof.arityRange raw count ha
  apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases hv
  · intro Theta inc he
    have heq : Nonempty (Derivation body Theta (InternalTagArithmeticSyntaxProof.eqn count (numeral 0))) := by
      simpa only [equalEqn] using he
    have harity := outputTransport (OriginalRawSyntaxTransport.arityOf (.projection 0)) count (numeral 0) (Fin.cons raw Fin.elim0) heq
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof ha inc)
    have hscan := headTransport OriginalHereditaryAnnotatedExpansion.scan annotatedFront count (numeral 0)
      (Fin.cons z (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))) heq
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hp inc)
    exact ExpansionProof.actualExpansionSplit 0 body alpha Theta typ raw parameter window gamma rawJob tagged job front suffix jobs annotatedFront mapped full
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hparam inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hr inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof ht inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hj inc)
      harity
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hc inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hd inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof happ inc)
      hscan
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hm inc)
      (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hf inc)
  · intro Theta inc hrest
    apply OriginalRawSyntaxTransportInternalConstructorArityCasesProof.orCases hrest
    · intro Xi inc2 he
      have incl : ∀ f ∈ Delta, f ∈ Xi := fun f hf => inc2 _ (inc f hf)
      have heq : Nonempty (Derivation body Xi (InternalTagArithmeticSyntaxProof.eqn count (numeral 1))) := by
        simpa only [equalEqn] using he
      have harity := outputTransport (OriginalRawSyntaxTransport.arityOf (.projection 0)) count (numeral 1) (Fin.cons raw Fin.elim0) heq
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof ha incl)
      have hscan := headTransport OriginalHereditaryAnnotatedExpansion.scan annotatedFront count (numeral 1)
        (Fin.cons z (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))) heq
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hp incl)
      exact ExpansionProof.actualExpansionSplit 1 body alpha Xi typ raw parameter window gamma rawJob tagged job front suffix jobs annotatedFront mapped full
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hparam incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hr incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof ht incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hj incl)
        harity
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hc incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hd incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof happ incl)
        hscan
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hm incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hf incl)
    · intro Xi inc2 he
      have incl : ∀ f ∈ Delta, f ∈ Xi := fun f hf => inc2 _ (inc f hf)
      have heq : Nonempty (Derivation body Xi (InternalTagArithmeticSyntaxProof.eqn count (numeral 2))) := by
        simpa only [equalEqn] using he
      have harity := outputTransport (OriginalRawSyntaxTransport.arityOf (.projection 0)) count (numeral 2) (Fin.cons raw Fin.elim0) heq
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof ha incl)
      have hscan := headTransport OriginalHereditaryAnnotatedExpansion.scan annotatedFront count (numeral 2)
        (Fin.cons z (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))) heq
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hp incl)
      exact ExpansionProof.actualExpansionSplit 2 body alpha Xi typ raw parameter window gamma rawJob tagged job front suffix jobs annotatedFront mapped full
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hparam incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hr incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof ht incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hj incl)
        harity
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hc incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hd incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof happ incl)
        hscan
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hm incl)
        (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hf incl)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermSuffixIdentityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermSuffixIdentityProof
