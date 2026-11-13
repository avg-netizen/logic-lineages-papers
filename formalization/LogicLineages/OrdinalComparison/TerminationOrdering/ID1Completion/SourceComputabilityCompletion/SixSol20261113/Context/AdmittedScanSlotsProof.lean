module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedMapSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedScanSlotsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem countTransport (count expected role typ raw jobs annotatedPrefix : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) count raw)))
    (he : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) expected raw)))
    (hs : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix count role typ raw jobs))) :
    Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix expected role typ raw jobs)) :=
  headTransport OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix count expected
    (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
    (valueUnique (OriginalRawSyntaxTransport.arityOf (.projection 0)) count expected (Fin.cons raw Fin.elim0) ha he) hs

theorem singleton (F : Program 1) (count role typ raw jobs annotatedPrefix row first : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) count raw)))
    (he : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (suc z) raw)))
    (hs : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix count role typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row annotatedPrefix)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row))) :
    Nonempty (Derivation body Delta (consGraph row first z)) := by
  have hc := countTransport count (suc z) role typ raw jobs annotatedPrefix ha he hs
  exact AdmittedMapSlotsProof.singleton F annotatedPrefix row first
    (SixSol20261113.Runtime.SourceFramedScanLengthProof.scanLength (suc z) role typ raw jobs annotatedPrefix hc) hm hf

theorem binaryCases (F : Program 1) (count role typ raw jobs annotatedPrefix row first second : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) count raw)))
    (he : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (suc (suc z)) raw)))
    (hs : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix count role typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) row annotatedPrefix)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hsecond : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) row)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (tailOut : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (consGraph (row.relabel j) (first.relabel j) tailOut)) →
      Nonempty (Derivation body Theta (consGraph tailOut (second.relabel j) z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  have hc := countTransport count (suc (suc z)) role typ raw jobs annotatedPrefix ha he hs
  exact AdmittedMapSlotsProof.binaryCases F annotatedPrefix row first second psi
    (SixSol20261113.Runtime.SourceFramedScanLengthProof.scanLength (suc (suc z)) role typ raw jobs annotatedPrefix hc)
    hm hf hsecond next
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedScanSlotsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedScanSlotsProof
