module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.AppendIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableAboveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.IndexProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalVariableDecoderGraphSupportProof
open OriginalContextInsertionVariableSupportProof
open InternalApplicationStepPeelSupportProof (andLeft)
open InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open InternalRecursionClosureLogicProof
open InternalOriginalOrderSyntaxProof (ltF)

theorem nilContradiction (typ index : OTerm alpha) (psi : Formula alpha)
    (h : Nonempty (Derivation body Delta (OriginalVariableDecoder.graph (suc z) typ index z))) :
    Nonempty (Derivation body Delta psi) := by
  obtain ⟨he⟩ := valueUnique OriginalVariableDecoder.check (suc z) z (inputs typ index z)
    h (OriginalVariableDecoderInternalProof.nilValue typ index)
  exact ⟨Derivation.explosion (zeroNeSuc (symm he))⟩

theorem gapContradiction (typ index gamma count gap : OTerm alpha) (psi : Formula alpha)
    (hv : Nonempty (Derivation body Delta (OriginalVariableDecoder.graph (suc z) typ index gamma)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
    (he : Nonempty (Derivation body Delta (eqn (add count gap) index))) :
    Nonempty (Derivation body Delta psi) := by
  have hi := variableInputs (suc z) typ index gamma (add count gap) gamma
    ⟨symm (Classical.choice he)⟩ ⟨refl gamma⟩ hv
  have hs := OriginalContextInsertionShiftInductionProof.appendShift gamma (suc z) typ count z gamma gap
    hl (AppendIdentityProof.identity gamma)
  have hn : Nonempty (Derivation body Delta (OriginalVariableDecoder.graph (suc z) typ gap z)) :=
    ⟨Derivation.implicationElimination (Classical.choice (InternalApplicationStepPeelSupportProof.andLeft hs)) (Classical.choice hi)⟩
  exact nilContradiction typ gap psi hn

theorem bound (typ index gamma count : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (OriginalVariableDecoder.graph (suc z) typ index gamma)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count gamma))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess index count)) := by
  let P := InternalLessThan.strictLess index count
  have hb : Nonempty (Derivation body (P.not :: Delta) P) := by
    have hn : Nonempty (Derivation body (P.not :: Delta) P.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply InternalUnpairReverseSyntaxProof.weakOrderCases (P.not :: Delta) count index P
      (InternalUnpairArithmeticProof.notLessWeak index count hn)
    intro beta j Theta gap hj he
    have hvj := renameInto (withHyp hv P.not) j Theta hj
    simp only [graphRename,sucRelabel,zRelabel] at hvj
    have hlj := renameInto (withHyp hl P.not) j Theta hj
    rw [lengthRename] at hlj
    exact gapContradiction (typ.relabel j) (index.relabel j) (gamma.relabel j) (count.relabel j)
      gap (P.relabel j) hvj hlj he
  exact ⟨InternalBetaTotalityProof.disjunctionElimination (InternalControlGraphChoiceProof.excludedMiddle P)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
    (Derivation.implicationIntroduction (Classical.choice hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.IndexProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalVariableFieldsCoverage.IndexProof
