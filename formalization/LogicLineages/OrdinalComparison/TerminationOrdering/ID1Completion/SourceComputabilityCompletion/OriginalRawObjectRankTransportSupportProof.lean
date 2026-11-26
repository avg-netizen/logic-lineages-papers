module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankPackedTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof
open OriginalRawObjectTransport OriginalRawObjectTransportInternalSupportProof
open OriginalRawObjectTransportInternalSyntaxProof
open OriginalRawSyntaxTransport OriginalRawVariableRank
open OriginalRawVariableRankPackedTransportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover the payload rank through the literal right-coordinate observer. -/
theorem rankObjectForward (input rank gamma packed : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma packed)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankObjectRaw rank input))) :
    Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed)) :=
  unaryRecover variableRankPackedRaw InternalUnpair.right rank packed
    (Fin.cons input Fin.elim0) hr (pairRight input gamma packed hp)

/-- Reconstruct the Object rank at the same input pairing. -/
theorem rankObjectBackward (input rank gamma packed : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma packed)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed))) :
    Nonempty (Derivation body Delta (graph1 variableRankObjectRaw rank input)) :=
  unaryValue variableRankPackedRaw InternalUnpair.right rank packed
    (Fin.cons input Fin.elim0) hr (pairRight input gamma packed hp)

/-- Total queries for the actual Object eraser. No nonempty-context predicate
is inserted: its existing total head and tail programs determine their outputs. -/
def eraseRankQueries : Fin 5 → Program 1 :=
  ![InternalUnpair.left,InternalUnpair.right,erasedContext,erasedDomain,erasedPayload]

/-- At internally supplied outputs, the original Object graph exposes the
same packed erasure graph and input/output pair coordinates. -/
theorem rankEraseObjectAt (input erased before after : OTerm alpha)
    (ys : Fin 5 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta
      (programGraph (eraseRankQueries i) (ys i) (Fin.cons input Fin.elim0))))
    (he : Nonempty (Derivation body Delta (graph1 eraseObjectRaw erased input)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankObjectRaw before input)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankObjectRaw after erased))) :
    Nonempty (Derivation body Delta (RankNonincrease after before)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
  have hp := reconstructPair input (ys 0) (ys 1) (hq 0) (hq 1)
  have ho := binaryRecover InternalPairing.pairing erasedContext erasedPayload
    erased (ys 2) (ys 4) xs he (hq 2) (hq 4)
  have ht : Nonempty (Derivation body Delta
      (graph3 erasePackedRaw (ys 4) (ys 3) (numeral 0) (ys 1))) := by
    apply compositionRecover erasePackedRaw ![erasedDomain,constant 1 0,InternalUnpair.right]
      (ys 4) xs (Fin.cons (ys 3) (Fin.cons (numeral 0) (Fin.cons (ys 1) Fin.elim0))) (hq 4)
    intro i
    exact Fin.cases (hq 3) (Fin.cases (constantValue 0 xs)
      (Fin.cases (hq 1) (fun k => Fin.elim0 k))) i
  exact rankErasePackedNonincrease (ys 1) (ys 4) before after (ys 3) (numeral 0) ht
    (rankObjectForward input before (ys 0) (ys 1) hp hb)
    (rankObjectForward erased after (ys 2) (ys 4) ho ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportSupportProof
