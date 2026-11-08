module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open InternalBoundedDescentNormalizer InternalBoundedDescentNormalizerStepSupportProof
open InternalAcceptance InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem chooseLessSplit (V : Program 1) (out candidate input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (choose V) out (Fin.cons candidate (Fin.cons input Fin.elim0))))) :
    Nonempty (Derivation body Gamma (eqn out input ⊔ ltF out input)) := by
  obtain ⟨hs⟩ := chooseSplit V out candidate input h
  obtain ⟨hl⟩ := guardLess (body := body)
    (Gamma := programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0)) :: Gamma)
    V out input ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination hs
    (Derivation.implicationIntroduction (orLeft (Derivation.hypothesis List.mem_cons_self)))
    (Derivation.implicationIntroduction (orRight hl))⟩

theorem stepSplit (R V : Program 1) (out input : OTerm α)
    (h : Nonempty (Derivation body Gamma (transitionGraph R V out input))) :
    Nonempty (Derivation body Gamma (eqn out input ⊔ ltF out input)) := by
  apply transitionCases R V out input _ h
  intro β j Delta candidate _ hc
  change Nonempty (Derivation body Delta
    ((eqn out input).relabel j ⊔ (ltF out input).relabel j))
  rw [eqnRelabel, orderRename]
  exact chooseLessSplit V (out.relabel j) candidate (input.relabel j) hc

theorem chooseValid (V : Program 1) (out candidate input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (choose V) out (Fin.cons candidate (Fin.cons input Fin.elim0)))))
    (hv : Nonempty (Derivation body Gamma (validGraph V input))) :
    Nonempty (Derivation body Gamma (validGraph V out)) := by
  obtain ⟨hs⟩ := chooseSplit V out candidate input h
  obtain ⟨hv⟩ := hv
  have he : Nonempty (Derivation body (eqn out input :: Gamma) (validGraph V out)) :=
    headTransport V (suc z) input out Fin.elim0
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ ⟨addHyp hv _⟩
  obtain ⟨he⟩ := he
  obtain ⟨hg⟩ := guardValid (body := body)
    (Gamma := programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0)) :: Gamma)
    V out input ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination hs
    (Derivation.implicationIntroduction he) (Derivation.implicationIntroduction hg)⟩

theorem stepValid (R V : Program 1) (out input : OTerm α)
    (h : Nonempty (Derivation body Gamma (transitionGraph R V out input)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input))) :
    Nonempty (Derivation body Gamma (validGraph V out)) := by
  apply transitionCases R V out input _ h
  intro β j Delta candidate hj hc
  have hv' := renameInto hv j Delta hj
  simp only [validGraph, unaryRename, sucRelabel, zRelabel] at hv' ⊢
  exact chooseValid V (out.relabel j) candidate (input.relabel j) hc hv'

theorem projectedUnaryValue {n : Nat} (p : Program 1) (i : Fin n)
    (out : OTerm α) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (unaryGraph p out (xs i)))) :
    Nonempty (Derivation body Gamma
      (programGraph (.composition p (fun _ : Fin 1 => .projection i)) out xs)) := by
  apply compositionValue p (fun _ : Fin 1 => .projection i) out xs (Fin.cons (xs i) Fin.elim0) hp
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

theorem sameLeftRecover (typ out input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph sameLeft (suc z) (Fin.cons out (Fin.cons input Fin.elim0)))))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  apply programCases InternalUnpair.left (Fin.cons out Fin.elim0) _
  intro β j Delta value hj hv
  have h' := renameInto h j Delta hj
  have hl' := renameInto hl j Delta hj
  simp only [programRename, consTermRename, emptyRename, sucRelabel, zRelabel] at h'
  simp only [leftGraph, unaryRename] at hl' ⊢
  have hv' : Nonempty (Derivation body Delta (unaryGraph InternalUnpair.left value (out.relabel j))) := by
    simpa only [unaryGraph, consTermRename, emptyRename] using hv
  let xs : Fin 2 → OTerm β := Fin.cons (out.relabel j) (Fin.cons (input.relabel j) Fin.elim0)
  have ha := projectedUnaryValue InternalUnpair.left (0 : Fin 2) value xs hv'
  have hb := projectedUnaryValue InternalUnpair.left (1 : Fin 2) (typ.relabel j) xs hl'
  have hg := compositionRecover InternalEqualityTest.equalityTest
    (Fin.cons (.composition InternalUnpair.left (fun _ : Fin 1 => .projection (0 : Fin 2)))
      (Fin.cons (.composition InternalUnpair.left (fun _ : Fin 1 => .projection (1 : Fin 2))) Fin.elim0))
    (suc z) xs (Fin.cons value (Fin.cons (typ.relabel j) Fin.elim0)) h'
    (fun i => Fin.cases ha (Fin.cases hb (fun k => Fin.elim0 k)) i)
  have he := InternalEqualityTestProof.equalityOfAcceptance value (typ.relabel j) hg
  exact outputTransport InternalUnpair.left value (typ.relabel j) (Fin.cons (out.relabel j) Fin.elim0) he hv'

theorem guardLeft (V : Program 1) (typ out input : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0)))))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  obtain ⟨hc⟩ := guardRest V out input h
  exact sameLeftRecover typ out input ⟨Derivation.conjunctionRight hc⟩ hl

theorem chooseLeft (V : Program 1) (out candidate input typ : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (programGraph (choose V) out (Fin.cons candidate (Fin.cons input Fin.elim0)))))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  obtain ⟨hs⟩ := chooseSplit V out candidate input h
  obtain ⟨hl⟩ := hl
  have he : Nonempty (Derivation body (eqn out input :: Gamma) (leftGraph typ out)) :=
    headTransport InternalUnpair.left typ input out Fin.elim0
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ ⟨addHyp hl _⟩
  obtain ⟨he⟩ := he
  obtain ⟨hg⟩ := guardLeft (body := body)
    (Gamma := programGraph (guard V) (suc z) (Fin.cons out (Fin.cons input Fin.elim0)) :: Gamma)
    V typ out input ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp hl _⟩
  exact ⟨disjunctionElimination hs
    (Derivation.implicationIntroduction he) (Derivation.implicationIntroduction hg)⟩

theorem stepLeft (R V : Program 1) (out input typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (transitionGraph R V out input)))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  apply transitionCases R V out input _ h
  intro β j Delta candidate hj hc
  have hl' := renameInto hl j Delta hj
  simp only [leftGraph, unaryRename] at hl' ⊢
  exact chooseLeft V (out.relabel j) candidate (input.relabel j) (typ.relabel j) hc hl'

theorem notLessZero (x : OTerm α) :
    Nonempty (Derivation body Gamma (ltF x z).not) := by
  have h : Nonempty (Derivation body (ltF x z :: Gamma) (⊥ : Formula α)) := by
    apply InternalOriginalOrderProof.orderCases _ x z _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta gap _ ⟨he⟩
    simp only [zRelabel] at he
    exact ⟨sucNeZeroApply (trans (symm (addSucc (x.relabel j) gap)) he)⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

theorem chooseZero (V : Program 1) (candidate : OTerm α) :
    Nonempty (Derivation body Gamma
      (programGraph (choose V) z (Fin.cons candidate (Fin.cons z Fin.elim0)))) := by
  let xs : Fin 2 → OTerm α := Fin.cons candidate (Fin.cons z Fin.elim0)
  have hn : Nonempty (Derivation body Gamma (programGraph (guard V) (suc z) xs).not) := by
    obtain ⟨hl⟩ := guardLess (body := body)
      (Gamma := programGraph (guard V) (suc z) xs :: Gamma) V candidate z
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hz⟩ := notLessZero (body := body) (Gamma := Gamma) candidate
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination (addHyp hz _) hl)⟩
  have hg := conjunctionReject InternalLessThan.ltTest (conjunction (candidateValid V) sameLeft) xs hn
  exact zeroBranchIntro (guard V) (.projection (1 : Fin 2)) (.projection (0 : Fin 2)) z xs hg
    (projectionValue 1 xs)

theorem zeroValue (R V : Program 1) :
    Nonempty (Derivation body Gamma (transitionGraph R V (z : OTerm α) z)) := by
  apply programCases R (Fin.cons z Fin.elim0) _
  intro β j Delta candidate _ hc
  simp only [transitionGraph, unaryRename, zRelabel]
  apply compositionValue (choose V)
    (Fin.cons R (Fin.cons (.projection (0 : Fin 1)) Fin.elim0)) z
    (Fin.cons z Fin.elim0) (Fin.cons candidate (Fin.cons z Fin.elim0)) (chooseZero V candidate)
  have hc' : Nonempty (Derivation body Delta (unaryGraph R candidate z)) := by
    simpa only [unaryGraph, consTermRename, emptyRename, zRelabel] using hc
  intro i
  exact Fin.cases hc' (Fin.cases (projectionValue (0 : Fin 1) (Fin.cons z Fin.elim0)) (fun k => Fin.elim0 k)) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepProof
