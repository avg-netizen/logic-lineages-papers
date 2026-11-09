module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeMarkProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalVariableRepresentative InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (OTerm z suc eqn)
open InternalTagArithmeticSupportProof (symm sucNeZeroApply)
open InternalBetaTotalityProof (disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Exact-one accepted variables carry their whole original raw code. -/
theorem markedVariable (mark value : OTerm α)
    (hv : Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest (suc z) value)))
    (hm : Nonempty (Derivation body Delta (markGraph mark value))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark (suc z) value)) := by
  let xs : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  have h := successorBranchElim
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize OriginalConstructorLeaf.variableTest)
    (InternalAcceptance.constantZero 1)
    (pairOf (InternalLessThan.constantOne 1) (.projection 0)) mark z xs
    (normalizeAccept OriginalConstructorLeaf.variableTest xs hv) hm
  exact binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1) (.projection 0)
    mark (suc z) value xs h (InternalLessThanSupportProof.oneConstantValue xs) (projectionValue 0 xs)

theorem markedNonvariable (mark value : OTerm α)
    (hv : Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest (suc z) value).not))
    (hm : Nonempty (Derivation body Delta (markGraph mark value))) :
    Nonempty (Derivation body Delta (eqn mark z)) := by
  let xs : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  have h := zeroBranchElim
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize OriginalConstructorLeaf.variableTest)
    (InternalAcceptance.constantZero 1)
    (pairOf (InternalLessThan.constantOne 1) (.projection 0)) mark xs
    (normalizeReject OriginalConstructorLeaf.variableTest xs hv) hm
  exact valueUnique (InternalAcceptance.constantZero 1) mark z xs h (constantZeroValue xs)

/-- pair(1,value) cannot be raw zero. This uses the actual inverse graphs. -/
theorem pairOneNonzero (mark value : OTerm α)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark (suc z) value))) :
    Nonempty (Derivation body Delta (eqn mark z).not) := by
  let P := eqn mark z
  have hz := outputTransport InternalPairing.pairing mark z
    (Fin.cons (suc z) (Fin.cons value Fin.elim0))
    (show Nonempty (Derivation body (P :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (withHyp hp P)
  have hl := pairLeft z (suc z) value hz
  have hzero := pairLeft (body := body) (Gamma := P :: Delta) (z : OTerm α) z z
    InternalApplicationValidityStackAppendTransitionProof.pairZero
  obtain ⟨he⟩ := valueUnique InternalUnpair.left (suc z) z (Fin.cons z Fin.elim0) hl hzero
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

theorem sharedVariableMark (mark input out : OTerm α)
    (hv : Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest (suc z) input)))
    (hi : Nonempty (Derivation body Delta (markGraph mark input)))
    (ho : Nonempty (Derivation body Delta (markGraph mark out))) :
    Nonempty (Derivation body Delta (eqn out input)) := by
  have hp := markedVariable mark input hv hi
  let V := graph1 OriginalConstructorLeaf.variableTest (suc z) out
  apply formulaCases V
  · have hq := markedVariable mark out
      (show Nonempty (Derivation body (V :: Delta) V) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp ho V)
    exact valueUnique InternalUnpair.right out input (Fin.cons mark Fin.elim0)
      (pairRight mark (suc z) out hq) (pairRight mark (suc z) input (withHyp hp V))
  · have he := markedNonvariable mark out
      (show Nonempty (Derivation body (V.not :: Delta) V.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp ho V.not)
    obtain ⟨hn⟩ := pairOneNonzero mark input (withHyp hp V.not)
    obtain ⟨he⟩ := he
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn he)⟩

theorem zeroMarkRejectsVariable (value : OTerm α)
    (hm : Nonempty (Derivation body Delta (markGraph z value))) :
    Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest (suc z) value).not) := by
  let V := graph1 OriginalConstructorLeaf.variableTest (suc z) value
  obtain ⟨hn⟩ := pairOneNonzero z value (markedVariable z value
    (show Nonempty (Derivation body (V :: Delta) V) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (withHyp hm V))
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination hn (InternalTagArithmeticSupportProof.refl z))⟩

theorem eitherVariableRigid (mark input out : OTerm α)
    (hv : Nonempty (Derivation body Delta
      (graph1 OriginalConstructorLeaf.variableTest (suc z) input ⊔
        graph1 OriginalConstructorLeaf.variableTest (suc z) out)))
    (hi : Nonempty (Derivation body Delta (markGraph mark input)))
    (ho : Nonempty (Derivation body Delta (markGraph mark out))) :
    Nonempty (Derivation body Delta (eqn out input)) := by
  let Vi := graph1 OriginalConstructorLeaf.variableTest (suc z) input
  let Vo := graph1 OriginalConstructorLeaf.variableTest (suc z) out
  obtain ⟨left⟩ := sharedVariableMark mark input out
    (show Nonempty (Derivation body (Vi :: Delta) Vi) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (withHyp hi Vi) (withHyp ho Vi)
  obtain ⟨right⟩ := sharedVariableMark mark out input
    (show Nonempty (Derivation body (Vo :: Delta) Vo) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (withHyp ho Vo) (withHyp hi Vo)
  obtain ⟨hv⟩ := hv
  exact ⟨disjunctionElimination hv (Derivation.implicationIntroduction left)
    (Derivation.implicationIntroduction (symm right))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeMarkProof
