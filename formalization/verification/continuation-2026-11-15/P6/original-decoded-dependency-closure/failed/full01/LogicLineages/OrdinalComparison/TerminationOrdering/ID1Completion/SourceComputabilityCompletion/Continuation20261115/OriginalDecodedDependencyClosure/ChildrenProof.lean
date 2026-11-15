module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ClauseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ChildrenProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)

theorem childrenClosed : Targets.InternalChildrenClosed := by
  intro n body alpha Delta raw children child hv hd hm
  apply OriginalCodeValidityGuard.FieldProof.fieldCases raw _
  intro beta j Theta tag payload first second head hj hp hf hs hh
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename]
  have hv' := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hv'
  have hd' := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph1Rename] at hd'
  have hm' := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hm'
  let f : ClauseProof.Frame n body Theta (raw.relabel j) :=
    { tag := tag, payload := payload, first := first, second := second, head := head,
      deps := children.relabel j, child := child.relabel j, pair := hp, firstGraph := hf,
      secondGraph := hs, headGraph := hh, childrenGraph := hd', member := hm' }
  have ha := (OriginalCodeValidityConstructors.Proof.guardConstructors n body beta Theta
    (raw.relabel j) tag payload first second head hp hf hs hh).mp hv'
  exact ClauseProof.fromAllowed f ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ChildrenProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencyClosure.ChildrenProof
