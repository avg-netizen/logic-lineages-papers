module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion OriginalRawObjectTransport OriginalRawVariableRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual raw Object weakening followed by the SAME final canonical
Object program preserves all variable occurrences. The original active outer
window and original input typing pay the source conditions. No typing or
transition fixedness of the raw shifted Object is assumed. The sole refined
tuple is the existing once-guarded, transparent, once-refined pipeline. -/
def WeakeningRankLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Prop :=
  let r := OriginalFinalGuardedRank.refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let comp := GlobalSourcePackage.computability f
  let K := OriginalFinalVariableObject.canonicalObjectProgram r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (typ d input shifted out rank : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 f.window (numeral 1) (numeral context) ⊓
      (graph3 comp.typed (numeral 1) (numeral context) typ input ⊓
        (graph2 shiftObjectRaw shifted d input ⊓
          graph2 K out (numeral context) shifted))).imp
      ((graph1 variableRankObjectRaw rank out).iff
        (graph1 variableRankObjectRaw rank input))))

/-- Contextual Object erasure followed by that SAME final canonical program
cannot increase variable occurrences. The genuine original context-cons
witness remains essential for source-validity transport, even though the raw
numeric erasure rank law is total. Neither raw erased typing/fixedness nor an
erased-type window premise is supplied. Erasure need not strictly lower rank. -/
def ErasureRankLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Prop :=
  let r := OriginalFinalGuardedRank.refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let comp := GlobalSourcePackage.computability f
  let K := OriginalFinalVariableObject.canonicalObjectProgram r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (typ d gamma extended input erased out before after : OTerm alpha),
  Nonempty (Derivation body Delta
    (((graph1 f.window (numeral 1) (numeral context) ⊓
      (graph3 comp.typed (numeral 1) (numeral context) typ input ⊓
        (graph1 InternalUnpair.left extended input ⊓
          (graph2 InternalListCodec.consCode extended d gamma ⊓
            (graph1 eraseObjectRaw erased input ⊓
              graph2 K out (numeral context) erased))))) ⊓
      (graph1 variableRankObjectRaw before input ⊓
        graph1 variableRankObjectRaw after out)).imp
      (RankNonincrease after before)))

/- These contracts are independent internal derivations at the actual
unchanged final tuple. They do not assert raw selectedTyped transport,
representative coherence, canonical cancellation, certificate transport,
substitution/I/C or the closed all-term accessibility endpoint. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectRankTransport
