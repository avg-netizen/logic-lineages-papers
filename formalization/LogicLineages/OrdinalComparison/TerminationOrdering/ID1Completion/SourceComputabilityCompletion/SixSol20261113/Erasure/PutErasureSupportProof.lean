module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Reverse the accepted result exposure using exactly the same constructor AST. -/
theorem resultIntro (s t typ raw target head base label nil : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing t typ target)))
    (hn : Nonempty (Derivation body Delta (programGraph nilConstructor nil Fin.elim0)))
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor target ![label,head,typ,base,numeral 0,nil]))) :
    Nonempty (Derivation body Delta (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label)) := by
  let xs : Fin 2 → OTerm alpha := ![s,label]
  have hnil := (substitutionGraph PutValidityExposureProof.nilSubstitution
    (Fin.elim0 : Fin 0 → OTerm alpha) xs nil (fun i => Fin.elim0 i)).mp hn
  have hraw := (substitutionGraph PutValidityExposureProof.resultSubstitution
    ![label,head,typ,base,numeral 0,nil] xs target
    (PutValidityExposureProof.fieldValues s typ raw head base label nil hp ho hnil)).mp hc
  have htype := OriginalTypedDecoderInternalScalarProof.pairLeftValue
    (.projection 0) s typ raw xs (projectionValue 0 xs) hp
  exact binaryValue InternalPairing.pairing (leftOf (.projection 0))
    PutValidityExposureProof.rawResult t typ target xs ht htype hraw

/-- Bind only the raw erasure output and its ordinary child. The constructor
and packed type of the supplied erased source are derived, not assumed. -/
theorem ordinaryExposure (s typ raw head base d cutoff erasedS : OTerm alpha)
    (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erasedS d cutoff s)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (erasedRaw erasedBase : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing
        (erasedS.relabel j) (typ.relabel j) erasedRaw)) →
      Nonempty (Derivation body Theta (graph2 ordinaryConstructor erasedRaw (head.relabel j) erasedBase)) →
      Nonempty (Derivation body Theta (graph3 eraseRaw erasedBase (d.relabel j) (cutoff.relabel j) (base.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let qs : Fin 2 → Program 4 :=
    ![.composition eraseRaw ![.projection 0,.projection 1,.projection 2],
      .composition eraseRaw ![.projection 0,.projection 1,.projection 3] ]
  apply programsCases qs ![d,cutoff,raw,base] psi
  intro beta j Theta ys hj hv
  have hvec : (fun i : Fin 4 => (![d,cutoff,raw,base] i).relabel j) =
      ![d.relabel j,cutoff.relabel j,raw.relabel j,base.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
  rw [hvec] at hv
  let xs : Fin 4 → OTerm beta := ![d.relabel j,cutoff.relabel j,raw.relabel j,base.relabel j]
  have hraw := InternalOriginalUniformVertexPathSupportProof.ternaryRecover eraseRaw (.projection 0) (.projection 1) (.projection 2)
    (ys 0) (d.relabel j) (cutoff.relabel j) (raw.relabel j) xs (hv 0)
    (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue 2 xs)
  have hbase := InternalOriginalUniformVertexPathSupportProof.ternaryRecover eraseRaw (.projection 0) (.projection 1) (.projection 3)
    (ys 1) (d.relabel j) (cutoff.relabel j) (base.relabel j) xs (hv 1)
    (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue 3 xs)
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  have he' := renameInto he j Theta hj
  rw [graph2Rename] at hp' ho'
  rw [graph3Rename] at he'
  exact next beta j Theta (ys 0) (ys 1) hj
    (OriginalRawSyntaxTransportInternalPackedProof.erasePackedForward
      (s.relabel j) (erasedS.relabel j) (typ.relabel j) (raw.relabel j) (ys 0)
      (d.relabel j) (cutoff.relabel j) hp' hraw he')
    (OriginalRawSyntaxTransportInternalFoldOrdinaryProof.ordinaryForward .erase
      (raw.relabel j) (ys 0) (d.relabel j) (cutoff.relabel j) (head.relabel j)
      (base.relabel j) (ys 1) ho' hbase hraw) hbase
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureSupportProof
