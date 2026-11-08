module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open InternalParameterizedBoundedDescentNormalizer InternalParameterizedBoundedDescentNormalizerStepSupportProof
open InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem chooseLessSplit (V : Program 2) (out candidate input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (choose V) out
        (Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0)))))) :
    Nonempty (Derivation body Gamma (eqn out input ⊔ ltF out input)) := by
  obtain ⟨hs⟩ := chooseSplit V out candidate input parameter h
  obtain ⟨hl⟩ := guardLess (body := body)
    (Gamma := programGraph (guard V) (suc z)
      (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))) :: Gamma)
    V out input parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination hs
    (Derivation.implicationIntroduction (orLeft (Derivation.hypothesis List.mem_cons_self)))
    (Derivation.implicationIntroduction (orRight hl))⟩

theorem stepSplit (R V : Program 2) (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (transitionGraph R V out input parameter))) :
    Nonempty (Derivation body Gamma (eqn out input ⊔ ltF out input)) := by
  apply transitionCases R V out input parameter _ h
  intro β j Delta candidate _ hc
  change Nonempty (Derivation body Delta
    ((eqn out input).relabel j ⊔ (ltF out input).relabel j))
  rw [eqnRelabel, orderRename]
  exact chooseLessSplit V (out.relabel j) candidate (input.relabel j) (parameter.relabel j) hc

theorem chooseValid (V : Program 2) (out candidate input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (choose V) out
        (Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))))))
    (hv : Nonempty (Derivation body Gamma (validGraph V input parameter))) :
    Nonempty (Derivation body Gamma (validGraph V out parameter)) := by
  obtain ⟨hs⟩ := chooseSplit V out candidate input parameter h
  obtain ⟨hv⟩ := hv
  have he : Nonempty (Derivation body (eqn out input :: Gamma) (validGraph V out parameter)) :=
    headTransport V (suc z) input out (Fin.cons parameter Fin.elim0)
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ ⟨addHyp hv _⟩
  obtain ⟨he⟩ := he
  obtain ⟨hg⟩ := guardValid (body := body)
    (Gamma := programGraph (guard V) (suc z)
      (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))) :: Gamma)
    V out input parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination hs
    (Derivation.implicationIntroduction he) (Derivation.implicationIntroduction hg)⟩

theorem stepValid (R V : Program 2) (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (transitionGraph R V out input parameter)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input parameter))) :
    Nonempty (Derivation body Gamma (validGraph V out parameter)) := by
  apply transitionCases R V out input parameter _ h
  intro β j Delta candidate hj hc
  have hv' := renameInto hv j Delta hj
  simp only [validGraph, binaryRename, sucRelabel, zRelabel] at hv' ⊢
  exact chooseValid V (out.relabel j) candidate (input.relabel j) (parameter.relabel j) hc hv'

/-- Recover the original source-value left tag. Neither occurrence of the
left selector is applied to the carried parameter. -/
theorem sameLeftRecover (typ out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph sameLeft (suc z)
        (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))))))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  apply programCases InternalUnpair.left (Fin.cons out Fin.elim0) _
  intro β j Delta value hj hv
  have h' := renameInto h j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [programRename, consTermRename, emptyRename, sucRelabel, zRelabel] at h'
  simp only [leftRename] at hl' ⊢
  have hv' : Nonempty (Derivation body Delta
      (InternalBoundedDescentNormalizer.unaryGraph InternalUnpair.left value (out.relabel j))) := by
    simpa only [InternalBoundedDescentNormalizer.unaryGraph, consTermRename, emptyRename] using hv
  let xs : Fin 3 → OTerm β :=
    Fin.cons (out.relabel j) (Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
  have ha := InternalBoundedDescentNormalizerStepProof.projectedUnaryValue
    InternalUnpair.left (0 : Fin 3) value xs hv'
  have hb := InternalBoundedDescentNormalizerStepProof.projectedUnaryValue
    InternalUnpair.left (1 : Fin 3) (typ.relabel j) xs hl'
  have hg := compositionRecover InternalEqualityTest.equalityTest
    (Fin.cons (.composition InternalUnpair.left (fun _ : Fin 1 => .projection (0 : Fin 3)))
      (Fin.cons (.composition InternalUnpair.left (fun _ : Fin 1 => .projection (1 : Fin 3))) Fin.elim0))
    (suc z) xs (Fin.cons value (Fin.cons (typ.relabel j) Fin.elim0)) h'
    (fun i => Fin.cases ha (Fin.cases hb (fun k => Fin.elim0 k)) i)
  have he := InternalEqualityTestProof.equalityOfAcceptance value (typ.relabel j) hg
  exact outputTransport InternalUnpair.left value (typ.relabel j) (Fin.cons (out.relabel j) Fin.elim0) he hv'

theorem guardLeft (V : Program 2) (typ out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (guard V) (suc z)
        (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))))))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  obtain ⟨hc⟩ := guardRest V out input parameter h
  exact sameLeftRecover typ out input parameter ⟨Derivation.conjunctionRight hc⟩ hl

theorem chooseLeft (V : Program 2) (out candidate input typ parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (choose V) out
        (Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))))))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  obtain ⟨hs⟩ := chooseSplit V out candidate input parameter h
  obtain ⟨hl⟩ := hl
  have he : Nonempty (Derivation body (eqn out input :: Gamma) (leftGraph typ out)) :=
    headTransport InternalUnpair.left typ input out Fin.elim0
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ ⟨addHyp hl _⟩
  obtain ⟨he⟩ := he
  obtain ⟨hg⟩ := guardLeft (body := body)
    (Gamma := programGraph (guard V) (suc z)
      (Fin.cons out (Fin.cons input (Fin.cons parameter Fin.elim0))) :: Gamma)
    V typ out input parameter ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp hl _⟩
  exact ⟨disjunctionElimination hs
    (Derivation.implicationIntroduction he) (Derivation.implicationIntroduction hg)⟩

theorem stepLeft (R V : Program 2) (out input typ parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (transitionGraph R V out input parameter)))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  apply transitionCases R V out input parameter _ h
  intro β j Delta candidate hj hc
  have hl' := renameInto hl j Delta hj
  simp only [leftRename] at hl' ⊢
  exact chooseLeft V (out.relabel j) candidate (input.relabel j) (typ.relabel j)
    (parameter.relabel j) hc hl'

/-- Zero rejects every candidate independently of the parameter. -/
theorem chooseZero (V : Program 2) (candidate parameter : OTerm α) :
    Nonempty (Derivation body Gamma
      (programGraph (choose V) z
        (Fin.cons candidate (Fin.cons z (Fin.cons parameter Fin.elim0))))) := by
  let xs : Fin 3 → OTerm α := Fin.cons candidate (Fin.cons z (Fin.cons parameter Fin.elim0))
  have hn : Nonempty (Derivation body Gamma (programGraph (guard V) (suc z) xs).not) := by
    obtain ⟨hl⟩ := guardLess (body := body)
      (Gamma := programGraph (guard V) (suc z) xs :: Gamma) V candidate z parameter
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hz⟩ := InternalBoundedDescentNormalizerStepProof.notLessZero
      (body := body) (Gamma := Gamma) candidate
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hz _) hl)⟩
  have hg := InternalBoundedDescentNormalizerStepSupportProof.conjunctionReject
    candidateLess (conjunction (candidateValid V) sameLeft) xs hn
  exact zeroBranchIntro (guard V) (.projection (1 : Fin 3)) (.projection (0 : Fin 3)) z xs hg
    (projectionValue 1 xs)

theorem zeroValue (R V : Program 2) (parameter : OTerm α) :
    Nonempty (Derivation body Gamma (transitionGraph R V z z parameter)) := by
  apply programCases R (Fin.cons z (Fin.cons parameter Fin.elim0)) _
  intro β j Delta candidate _ hc
  simp only [transitionGraph, binaryRename, zRelabel]
  let xs : Fin 2 → OTerm β := Fin.cons z (Fin.cons (parameter.relabel j) Fin.elim0)
  apply compositionValue (choose V)
    (Fin.cons R (Fin.cons (.projection (0 : Fin 2)) (Fin.cons (.projection (1 : Fin 2)) Fin.elim0))) z
    xs (Fin.cons candidate (Fin.cons z (Fin.cons (parameter.relabel j) Fin.elim0)))
    (chooseZero V candidate (parameter.relabel j))
  have hc' : Nonempty (Derivation body Delta (binaryGraph R candidate z (parameter.relabel j))) := by
    simpa only [binaryGraph, consTermRename, emptyRename, zRelabel] using hc
  intro i
  exact Fin.cases hc' (Fin.cases (projectionValue (0 : Fin 2) xs)
    (Fin.cases (projectionValue (1 : Fin 2) xs) (fun k => Fin.elim0 k))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerStepProof
