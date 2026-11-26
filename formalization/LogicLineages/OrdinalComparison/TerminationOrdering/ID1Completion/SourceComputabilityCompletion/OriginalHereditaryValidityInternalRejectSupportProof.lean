module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalNodeSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalStateSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRejectSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternalNodeSupportProof OriginalHereditaryValidityInternalStateSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem exactReject {n : Nat} (p : Program n) (xs : Fin n → OTerm α)
    (hn : Nonempty (Derivation body Gamma (programGraph p (numeral 1) xs).not)) :
    Nonempty (Derivation body Gamma (programGraph (exactOne p) z xs)) := by
  apply programCases p xs _
  intro β j Delta v hj hv
  rw [programRename,zRelabel]
  have hn' := renameInto hn j Delta hj
  change Nonempty (Derivation body Delta ((programGraph p (numeral 1) xs).relabel j).not) at hn'
  simp only [programRename,OriginalLambdaConstructorGraphSyntaxProof.oneRename] at hn'
  apply equalityCases v (numeral 1) _
  · intro Theta inc he
    exact binaryValue InternalEqualityTest.equalityTest p (InternalLessThan.constantOne n)
      z v (numeral 1) (fun i => (xs i).relabel j) he
      (weakenProof hv inc) (InternalLessThanSupportProof.oneConstantValue _)
  · intro Theta inc he
    have hp := outputTransport p v (numeral 1) (fun i => (xs i).relabel j)
      (InternalEqualityTestProof.equalityOfAcceptance v (numeral 1) he) (weakenProof hv inc)
    obtain ⟨hn'⟩ := weakenProof hn' inc
    obtain ⟨hp⟩ := hp
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn' hp)⟩

theorem graphAtValue {n : Nat} (p : Program n) (out value : OTerm α)
    (xs : Fin n → OTerm α)
    (hv : Nonempty (Derivation body Gamma (programGraph p value xs))) :
    Nonempty (Derivation body Gamma ((programGraph p out xs).iff (equal out value))) := by
  let G := programGraph p out xs
  let E := equal out value
  have hvG := weakenProof hv (fun q hq => List.mem_cons_of_mem G hq)
  obtain ⟨hf⟩ := valueUnique p out value xs
    (show Nonempty (Derivation body (G :: Gamma) G) from ⟨Derivation.hypothesis List.mem_cons_self⟩) hvG
  have he : Nonempty (Derivation body (E :: Gamma) (eqn value out)) := by
    exact ⟨symm (show Derivation body (E :: Gamma) (eqn out value) from
      by simpa only [E,equalEqn] using (Derivation.hypothesis List.mem_cons_self : Derivation body (E :: Gamma) E))⟩
  obtain ⟨hb⟩ := outputTransport p value out xs he
    (weakenProof hv (fun q hq => List.mem_cons_of_mem E hq))
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (by simpa only [equalEqn] using hf))
    (Derivation.implicationIntroduction hb)⟩

theorem rejectStatus (s t m : Program 2) (state : OTerm α)
    (hn : Nonempty (Derivation body Gamma (graph1 status (numeral 1) state).not)) :
    Nonempty (Derivation body Gamma (graph1 (transition s t m) z state)) := by
  exact zeroBranchIntro _ _ _ z (Fin.cons state Fin.elim0)
    (exactReject status _ hn) (InternalLessThanSupportProof.zeroConstantValue _)

theorem rejectNode (s t m : Program 2) (state : OTerm α)
    (hl : Nonempty (Derivation body Gamma (LiveWork state)))
    (hn : Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state).not)) :
    Nonempty (Derivation body Gamma (graph1 (transition s t m) z state)) := by
  apply programCases work (Fin.cons state Fin.elim0) _
  intro β j Delta w hj hw
  rw [graph1Rename,zRelabel]
  have hl' := renameInto hl j Delta hj
  rw [liveWorkRename] at hl'
  have hn' := renameInto hn j Delta hj
  change Nonempty (Derivation body Delta ((graph1 (nodeCheck s t m) (numeral 1) state).relabel j).not) at hn'
  rw [graph1Rename,OriginalLambdaConstructorGraphSyntaxProof.oneRename] at hn'
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at hw
  let xs : Fin 1 → OTerm β := Fin.cons (state.relabel j) Fin.elim0
  apply successorBranchIntro _ _ _ z z xs (exactAccept status xs (andLeft hl'))
  apply nonzeroBranchIntro _ _ _ z w xs hw
  · simpa only [equalEqn] using nonzeroOfNotZeroGraph work w xs hw (andRight hl')
  · exact zeroBranchIntro _ _ _ z xs (exactReject (nodeCheck s t m) xs hn')
      (InternalLessThanSupportProof.zeroConstantValue xs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRejectSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRejectSupportProof
