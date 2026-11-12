module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableRegionsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalTwoDeletionInternalVariableSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem belowBoth (raw a b i j x upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (x))))
    (hxi : Nonempty (Derivation body Delta (InternalLessThan.strictLess x i)))
    (hxj : Nonempty (Derivation body Delta (InternalLessThan.strictLess x j)))
    (hxjs : Nonempty (Derivation body Delta (InternalLessThan.strictLess x (suc j))))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  exact sameVariable left right x
    (below upper left a i x (below raw upper b (suc j) x hv hxjs hu) hxi hl)
    (below lower right b j x (below raw lower a i x hv hxi hd) hxj hr)

theorem atEarlier (raw a b i j upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (i))))
    (hij : Nonempty (Derivation body Delta (InternalLessThan.strictLess i (suc j))))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  exact sameBottom left right a
    (atCutoff upper left a i (below raw upper b (suc j) i hv hij hu) hl)
    (bottomRetained lower right b j a (atCutoff raw lower a i hv hd) hr)

theorem between (raw a b i j x upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (suc x))))
    (hix : Nonempty (Derivation body Delta (InternalLessThan.strictLess i (suc x))))
    (hxjs : Nonempty (Derivation body Delta (InternalLessThan.strictLess (suc x) (suc j))))
    (hxj : Nonempty (Derivation body Delta (InternalLessThan.strictLess x j)))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  exact sameVariable left right x
    (aboveSuccessor upper left a i x (below raw upper b (suc j) (suc x) hv hxjs hu) hix hl)
    (below lower right b j x (aboveSuccessor raw lower a i x hv hix hd) hxj hr)

theorem atLater (raw a b i j upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (suc j))))
    (hij : Nonempty (Derivation body Delta (InternalLessThan.strictLess i (suc j))))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  exact sameBottom left right b
    (bottomRetained upper left a i b (atCutoff raw upper b (suc j) hv hu) hl)
    (atCutoff lower right b j (aboveSuccessor raw lower a i j hv hij hd) hr)

theorem aboveBoth (raw a b i j x upper lower left right : InternalGraphComposition.OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 variableConstructor raw (suc (suc x)))))
    (hixx : Nonempty (Derivation body Delta (InternalLessThan.strictLess i (suc (suc x)))))
    (hjxx : Nonempty (Derivation body Delta (InternalLessThan.strictLess (suc j) (suc (suc x)))))
    (hix : Nonempty (Derivation body Delta (InternalLessThan.strictLess i (suc x))))
    (hjx : Nonempty (Derivation body Delta (InternalLessThan.strictLess j (suc x))))
    (hu : Nonempty (Derivation body Delta (graph3 eraseRaw upper b (suc j) raw)))
    (hl : Nonempty (Derivation body Delta (graph3 eraseRaw left a i upper)))
    (hd : Nonempty (Derivation body Delta (graph3 eraseRaw lower a i raw)))
    (hr : Nonempty (Derivation body Delta (graph3 eraseRaw right b j lower)))
    : Nonempty (Derivation body Delta (equal left right)) := by
  exact sameVariable left right x
    (aboveSuccessor upper left a i x (aboveSuccessor raw upper b (suc j) (suc x) hv hjxx hu) hix hl)
    (aboveSuccessor lower right b j x (aboveSuccessor raw lower a i (suc x) hv hixx hd) hjx hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableRegionsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalVariableRegionsProof
