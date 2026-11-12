module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionRankTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionRankProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalArithmeticProgramsSupportProof InternalTagArithmeticSyntaxProof
open OriginalRawSyntaxTransport OriginalFinalGuardedRankConstructorProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atArgumentRank
    (input out d e fn fnOut arg before after childBefore childAfter argumentRank : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
    (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut arg)))
    (hf : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw childBefore fn)))
    (hg : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw childAfter fnOut)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw before input)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw after out)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess childAfter childBefore)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw argumentRank arg))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess after before)) := by
  have hsumBefore := applicationValue input d e fn arg childBefore argumentRank
    (add childBefore argumentRank) hi hf hr (additionValue childBefore argumentRank)
  have hsumAfter := applicationValue out d e fnOut arg childAfter argumentRank
    (add childAfter argumentRank) ho hg hr (additionValue childAfter argumentRank)
  have heBefore := valueUnique variableRankPackedRaw before (add childBefore argumentRank)
    (Fin.cons input Fin.elim0) hb hsumBefore
  have heAfter := valueUnique variableRankPackedRaw after (add childAfter argumentRank)
    (Fin.cons out Fin.elim0) ha hsumAfter
  exact InternalOriginalPairingOrderArithmeticProof.strictTransport after before
    (add childAfter argumentRank) (add childBefore argumentRank) heAfter heBefore
    (InternalOriginalPairingOrderArithmeticProof.addStrictRight childAfter childBefore argumentRank hl)

theorem liftFunction
    (input out d e fn fnOut arg before after childBefore childAfter : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
    (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut arg)))
    (hf : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw childBefore fn)))
    (hg : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw childAfter fnOut)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw before input)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw after out)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess childAfter childBefore))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess after before)) := by
  apply programCases variableRankPackedRaw (Fin.cons arg Fin.elim0) _
  intro beta j Theta argumentRank hj hr
  have hr' : Nonempty (Derivation body Theta
      (graph1 variableRankPackedRaw argumentRank (arg.relabel j))) := by
    simpa only [graph1,consTermRename,emptyRename] using hr
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have hf' := renameInto hf j Theta hj
  have hg' := renameInto hg j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  have hl' := renameInto hl j Theta hj
  rw [graph4Rename] at hi' ho'
  rw [graph1Rename] at hf' hg' hb' ha'
  simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hl' ⊢
  exact atArgumentRank (input.relabel j) (out.relabel j) (d.relabel j) (e.relabel j)
    (fn.relabel j) (fnOut.relabel j) (arg.relabel j) (before.relabel j) (after.relabel j)
    (childBefore.relabel j) (childAfter.relabel j) argumentRank hi' ho' hf' hg' hb' ha' hl' hr'

theorem actualOriginalApplicationFunctionRank :
    OriginalApplicationFunctionRankTargets.ActualOriginalApplicationFunctionRank := by
  intro body alpha Delta input out d e fn fnOut arg before after childBefore childAfter
  let A := graph4 application input d e fn arg ⊓
    (graph4 application out d e fnOut arg ⊓
    (graph1 variableRankPackedRaw childBefore fn ⊓
    (graph1 variableRankPackedRaw childAfter fnOut ⊓
    (graph1 variableRankPackedRaw before input ⊓
    (graph1 variableRankPackedRaw after out ⊓ InternalLessThan.strictLess childAfter childBefore)))))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := liftFunction input out d e fn fnOut arg before after childBefore childAfter
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h))))
    (andLeft (andRight (andRight (andRight (andRight h)))))
    (andLeft (andRight (andRight (andRight (andRight (andRight h))))))
    (andRight (andRight (andRight (andRight (andRight (andRight h))))))
  exact ⟨Derivation.implicationIntroduction hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionRankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionRankProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationFunctionRankProof.actualOriginalApplicationFunctionRank
