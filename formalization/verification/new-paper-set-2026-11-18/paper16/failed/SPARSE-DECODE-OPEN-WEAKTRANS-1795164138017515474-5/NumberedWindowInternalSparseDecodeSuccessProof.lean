module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeProgramProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeDifferenceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSuccessProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm trans)
open ID1Completion.InternalAdditionLawsProof (add)
open ID1Completion.InternalMultiplicationLawsProof (congAddRight)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIrreflexivity)
open ID1Completion.InternalSquareRootArithmetic (interval square)
open ID1Completion.InternalSquareRootArithmeticSupportProof (squareCongr strictWeakTrans)
open ID1Completion.InternalSquareRootProof (intervalOfRootGraph rootGraphOfInterval)
open ID1Completion.InternalUnpairArithmeticProof (leftWeakAdd notLessWeak offsetInterval intervalInputTransport)
open ID1Completion.InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open ID1Completion.InternalEqualityTestSubtractionSupportProof (subTransport)
open ID1Completion.InternalEqualityTestSubtractionProof (diagonal)
open ID1Completion.InternalSquareRoot (root)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePairGraphProof (pairEquation pairGraph)
open NumberedWindowInternalSparseDecode NumberedWindowInternalSparseDecodeTargets
open NumberedWindowInternalSparseDecodeSyntaxProof NumberedWindowInternalSparseDecodeProgramProof
open NumberedWindowInternalSparseDecodeDifferenceProof NumberedWindowInternalSparseDecodeGuardProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem notGapOfBound (s x : OTerm α)
    (hb : Nonempty (Derivation body Γ (ltF x (suc s)))) :
    Nonempty (Derivation body Γ (ltF s x).not) := by
  obtain ⟨hb⟩ := hb
  let p := ltF s x
  obtain ⟨loop⟩ := strictWeakTrans (Gamma := p :: Γ) s x s
    ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp hb p⟩
  obtain ⟨irr⟩ := actualOriginalOrderIrreflexivity body α s
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (weakenClosed irr (p :: Γ)) loop)⟩

theorem pairToSuccess (n x y : OTerm α)
    (h : Nonempty (Derivation body Γ (binary NumberedWindowInternalSparsePair.pair n x y))) :
    Nonempty (Derivation body Γ (certifiedOutputs n x y)) := by
  let s := add x y
  obtain ⟨e⟩ := pairEquation n x y h
  have hx : Nonempty (Derivation body Γ (ltF x (suc s))) := leftWeakAdd x y
  obtain ⟨here⟩ := offsetInterval s x (weakTrans x s (add s s) hx (leftWeakAdd s s))
  have hs := rootGraphOfInterval s n ⟨intervalInputTransport s (symm e) here⟩
  have left := leftGraph n s x hs
    (subTransport x (square s) (add (square s) x) (square s) n
      ⟨refl (square s)⟩ ⟨symm e⟩ (diagonal (square s) x))
  obtain ⟨right⟩ := rightGraph n s x y hs left (diagonal x y)
  obtain ⟨accepted⟩ := goodYes n s x hs left (notGapOfBound s x hx)
  obtain ⟨left⟩ := left
  exact ⟨Derivation.conjunctionIntroduction accepted (Derivation.conjunctionIntroduction left right)⟩

theorem successToPair (n x y : OTerm α)
    (h : Nonempty (Derivation body Γ (certifiedOutputs n x y))) :
    Nonempty (Derivation body Γ (binary NumberedWindowInternalSparsePair.pair n x y)) := by
  apply programCases root ![n] (binary NumberedWindowInternalSparsePair.pair n x y)
  intro β j Δ s hJ sGraph
  rw [binaryRename]
  let nn := n.relabel j
  let xx := x.relabel j
  let yy := y.relabel j
  rw [unaryInputsRename] at sGraph
  have spec := renameInto h j Δ hJ
  rw [certifiedRename] at spec
  obtain ⟨spec⟩ := spec
  have ok : Nonempty (Derivation body Δ (unary good (suc z) nn)) :=
    ⟨Derivation.conjunctionLeft spec⟩
  have a : Nonempty (Derivation body Δ (unary leftCandidate xx nn)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight spec)⟩
  have b : Nonempty (Derivation body Δ (unary rightCandidate yy nn)) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight spec)⟩
  obtain ⟨iv⟩ := intervalOfRootGraph s nn sGraph
  obtain ⟨addLeft⟩ := differenceEquation (square s) nn xx
    ⟨Derivation.conjunctionLeft iv⟩ (leftInversion nn s xx sGraph a)
  obtain ⟨addRight⟩ := differenceEquation xx s yy (notLessWeak s xx (noGapOfGood nn s xx sGraph a ok))
    (rightInversion nn s xx yy sGraph a b)
  have rebuilt : Derivation body Δ (eqn (pairTerm xx yy) nn) :=
    trans (congAddRight xx (squareCongr addRight)) addLeft
  exact outputTransport NumberedWindowInternalSparsePair.pair (pairTerm xx yy) nn ![xx,yy]
    ⟨rebuilt⟩ (pairGraph xx yy)

theorem openSuccess : OpenSuccess := by
  intro body α n x y
  let g := binary NumberedWindowInternalSparsePair.pair n x y
  let s := certifiedOutputs n x y
  obtain ⟨h₁⟩ := pairToSuccess (body := body) (Γ := [g]) n x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h₂⟩ := successToPair (body := body) (Γ := [s]) n x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction h₁)
    (Derivation.implicationIntroduction h₂)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSuccessProof
