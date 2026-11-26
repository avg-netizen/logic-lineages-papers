module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenBaseProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue recursionZeroValue)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof

theorem base : OpenFoldBase := by
  intro body raw least α state c ty start cert
  let P := scratchGraph state cert start
  have known : Nonempty (Derivation body [P] P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h : Nonempty (Derivation body [P] (programGraph initial state ![c,ty,start,cert])) := by
    apply compositionValue consCode ![.projection 3,.projection 2] state ![c,ty,start,cert]
      ![cert,start] known
    intro i
    exact Fin.cases (projectionValue (3 : Fin 4) ![c,ty,start,cert])
      (Fin.cases (projectionValue (2 : Fin 4) ![c,ty,start,cert]) (fun k => Fin.elim0 k)) i
  obtain ⟨graph⟩ := recursionZeroValue initial (iterateStep raw least) state ![c,ty,start,cert] h
  exact ⟨Derivation.implicationIntroduction graph⟩

theorem nilStep : OpenNilRetention := by
  intro body raw least α k prior c ty start cert cur
  let P := scratchGraph prior z cur
  let xs := call6 k prior c ty start cert
  have read := (stateParts (body := body) (Γ := [P]) z cur k prior c ty start cert
    ⟨Derivation.hypothesis List.mem_cons_self⟩).1
  obtain ⟨out⟩ := zeroBranchIntro scratchCursor (.projection 1)
    (branch (onCursor cellGood) dead (updateCell raw least)) prior xs read
    (projectionValue (1 : Fin 6) xs)
  exact ⟨Derivation.implicationIntroduction out⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenBaseProof
