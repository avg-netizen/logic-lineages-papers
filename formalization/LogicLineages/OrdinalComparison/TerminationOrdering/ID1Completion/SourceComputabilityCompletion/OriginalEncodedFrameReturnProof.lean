module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalEncodedFrameReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredTermReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRestoredListReturnProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReturnFrameCoordinatesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalEncodedFrameReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
theorem termChildren0 : OriginalEncodedFrameReturnTargets.TermChildren0 := by
 intro R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out parent counts typed rawJob typ raw
  h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
 obtain ⟨coords⟩ := OriginalReturnFrameCoordinatesProof.actualCoordinates body alpha Delta
  input work results frame rest (numeral 1) payload parent counts z typed rawJob typ raw parameter z count packed
  h0
  h2
  h3
  h4
  h5
  h6
  h7
  h8
  h1
 have hrole := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hexpectedType := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hraw := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))))
 have hparameter := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))
 have hchildCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))
 have hdeletionCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))
 have hpacked := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (coords)))
 have hresults := Nonempty.intro (Derivation.conjunctionRight (coords))
 exact OriginalRestoredTermReturnProof.children0 R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out
  h0
  h1
  h2
  hrole
  hpacked
  hparameter
  hchildCount
  hdeletionCount
  h9
  h10
  h11
  h12
  h13
  h14
  h15
  h16
  h17
theorem termChildren1 : OriginalEncodedFrameReturnTargets.TermChildren1 := by
 intro R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix first parent counts typed rawJob typ raw
  h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
 obtain ⟨coords⟩ := OriginalReturnFrameCoordinatesProof.actualCoordinates body alpha Delta
  input work results frame rest (numeral 1) payload parent counts z typed rawJob typ raw parameter (suc z) count packed
  h0
  h2
  h3
  h4
  h5
  h6
  h7
  h8
  h1
 have hrole := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hexpectedType := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hraw := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))))
 have hparameter := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))
 have hchildCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))
 have hdeletionCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))
 have hpacked := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (coords)))
 have hresults := Nonempty.intro (Derivation.conjunctionRight (coords))
 exact OriginalRestoredTermReturnProof.children1 R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix first
  h0
  h1
  h2
  hrole
  hpacked
  hparameter
  hchildCount
  hdeletionCount
  h9
  h10
  h11
  h12
  h13
  h14
  h15
  h16
  h17
  h18
theorem termChildren2 : OriginalEncodedFrameReturnTargets.TermChildren2 := by
 intro R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix childTail first second parent counts typed rawJob typ raw
  h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
 obtain ⟨coords⟩ := OriginalReturnFrameCoordinatesProof.actualCoordinates body alpha Delta
  input work results frame rest (numeral 1) payload parent counts z typed rawJob typ raw parameter (suc (suc z)) count packed
  h0
  h2
  h3
  h4
  h5
  h6
  h7
  h8
  h1
 have hrole := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hexpectedType := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hraw := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))))
 have hparameter := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))
 have hchildCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))
 have hdeletionCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))
 have hpacked := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (coords)))
 have hresults := Nonempty.intro (Derivation.conjunctionRight (coords))
 exact OriginalRestoredTermReturnProof.children2 R body alpha Delta input work results frame rest payload packed parameter count row reversed old root returned tail value stack out suffix childTail first second
  h0
  h1
  h2
  hrole
  hpacked
  hparameter
  hchildCount
  hdeletionCount
  h9
  h10
  h11
  h12
  h13
  h14
  h15
  h16
  h17
  h18
  h19
theorem listNil : OriginalEncodedFrameReturnTargets.ListNil := by
 intro R body alpha Delta input work results frame rest payload raw rawPayload count row reversed old stack out parent counts typed rawJob typ packed parameter
  h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
 obtain ⟨coords⟩ := OriginalReturnFrameCoordinatesProof.actualCoordinates body alpha Delta
  input work results frame rest (numeral 1) payload parent counts (numeral 1) typed rawJob typ raw parameter z count packed
  h0
  h2
  h3
  h4
  h5
  h6
  h7
  h8
  h1
 have hrole := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hexpectedType := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hraw := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))))
 have hparameter := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))
 have hchildCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))
 have hdeletionCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))
 have hpacked := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (coords)))
 have hresults := Nonempty.intro (Derivation.conjunctionRight (coords))
 exact OriginalRestoredListReturnProof.listNil R body alpha Delta input work results frame rest payload raw rawPayload count row reversed old stack out
  h0
  h1
  h2
  hrole
  hraw
  h9
  hchildCount
  hdeletionCount
  h10
  h11
  h12
  h13
  h14
theorem listCons : OriginalEncodedFrameReturnTargets.ListCons := by
 intro R body alpha Delta input work results frame rest payload raw rawPayload count row reversed old stack out suffix childTail first second value parent counts typed rawJob typ packed parameter
  h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
 obtain ⟨coords⟩ := OriginalReturnFrameCoordinatesProof.actualCoordinates body alpha Delta
  input work results frame rest (numeral 1) payload parent counts (numeral 1) typed rawJob typ raw parameter (suc (suc z)) count packed
  h0
  h2
  h3
  h4
  h5
  h6
  h7
  h8
  h1
 have hrole := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hexpectedType := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))))
 have hraw := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))))
 have hparameter := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))))
 have hchildCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords)))))
 have hdeletionCount := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft (coords))))
 have hpacked := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft (coords)))
 have hresults := Nonempty.intro (Derivation.conjunctionRight (coords))
 exact OriginalRestoredListReturnProof.listCons R body alpha Delta input work results frame rest payload raw rawPayload count row reversed old stack out suffix childTail first second value
  h0
  h1
  h2
  hrole
  hraw
  h9
  hchildCount
  hdeletionCount
  h10
  h11
  h12
  h13
  h14
  h15
  h16
  h17
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalEncodedFrameReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalEncodedFrameReturnProof
