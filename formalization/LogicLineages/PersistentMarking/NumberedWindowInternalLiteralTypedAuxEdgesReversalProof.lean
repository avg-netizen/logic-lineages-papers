module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveBooleanProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeOnCoverProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxProfileObserversProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeReversalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxClassReadProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverInterfaceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgesReversalProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralPositiveBooleanProof (exact_OpenPositiveAuxShape)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse edgeRename)
open NumberedWindowInternalLiteralTypedAuxEdgeCasesOpenProof
open NumberedWindowInternalLiteralTypedAuxEdgeIntroProof
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (typedAuxEdgeGuard)
open NumberedWindowInternalLiteralEdgeOnCoverProof (KeepsCover)
open NumberedWindowScalarAlgorithm (Settings)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralTypedAuxEdgeSlotsProof (AuxRow)
open NumberedWindowInternalLiteralTypedAuxEdgeOpenProof (childAlternatives)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralAuxClassLeastProof (functionClass argumentClass)
open NumberedWindowInternalLiteralAuxClassReadProof (exact_OpenLiteralFunctionClass exact_OpenLiteralArgumentClass)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem consEqual (x y u v : OTerm α)
    (first : Nonempty (Derivation B Γ (eqn x u)))
    (second : Nonempty (Derivation B Γ (eqn y v))) :
    Nonempty (Derivation B Γ (eqn (rawCons x y) (rawCons u v))) := by
  let before : Fin 2 → OTerm α := ![x,y]
  let after : Fin 2 → OTerm α := ![u,v]
  have input (i : Fin 2) :
      Nonempty (Derivation B Γ (arithmeticEmbedding.onFormula ((before i).equal (after i)))) := by
    rw [onEquality]
    exact Fin.cases first (Fin.cases second (fun n => Fin.elim0 n)) i
  have old : Nonempty (Derivation B Γ (programGraph fieldCons (rawCons x y) before)) :=
    consGraph x y
  unfold programGraph at old
  have moved : Nonempty (Derivation B Γ (programGraph fieldCons (rawCons x y) after)) := by
    unfold programGraph
    exact graphInputTransport B α 2 Γ (OrdinaryArithmetic.graphFormula fieldCons)
      (rawCons x y) before after input old
  exact valueUnique fieldCons (rawCons x y) (rawCons u v) after moved (consGraph u v)


private theorem changeType (E : Program 4) (ctx t t' a b : OTerm α)
    (eq : D B Γ (eqn t t')) (held : D B Γ (acceptEdge E ctx t a b)) :
    D B Γ (acceptEdge E ctx t' a b) := by
  change D B Γ (programGraph E (suc z) ![ctx,t,a,b]) at held
  change D B Γ (programGraph E (suc z) ![ctx,t',a,b])
  unfold programGraph at *
  apply graphInputTransport B α 4 Γ (OrdinaryArithmetic.graphFormula E) (suc z)
    ![ctx,t,a,b] ![ctx,t',a,b] _ held
  intro i
  rw [onEquality]
  exact Fin.cases (⟨refl ctx⟩ : D B Γ (eqn ctx ctx)) (Fin.cases eq
    (Fin.cases (⟨refl a⟩ : D B Γ (eqn a a)) (Fin.cases (⟨refl b⟩ : D B Γ (eqn b b)) (fun n => Fin.elim0 n)))) i

theorem exact_OpenReverseTypedChildCases (E : Program 4) (reverse : CanReverse E)
    (ctx : OTerm α) (a b : AuxRow α)
    (dom : D B Γ (eqn a.dom b.dom)) (cod : D B Γ (eqn a.cod b.cod))
    (held : D B Γ (childAlternatives E ctx a b)) :
    D B Γ (childAlternatives E ctx b a) := by
  let F := acceptEdge E ctx (rawCons a.dom a.cod) a.fn b.fn ⊓ eqn a.arg b.arg
  let A := eqn a.fn b.fn ⊓ acceptEdge E ctx a.dom a.arg b.arg
  obtain ⟨d⟩ := dom
  obtain ⟨arrow⟩ := consEqual a.dom a.cod b.dom b.cod ⟨d⟩ cod
  obtain ⟨sum⟩ := held
  have one : D B (F :: Γ) (childAlternatives E ctx b a) := by
    have x : Derivation B (F :: Γ) F := Derivation.hypothesis List.mem_cons_self
    have rev := reverse B α (F :: Γ) ctx (rawCons a.dom a.cod) a.fn b.fn ⟨Derivation.conjunctionLeft x⟩
    obtain ⟨moved⟩ := changeType E ctx (rawCons a.dom a.cod) (rawCons b.dom b.cod) b.fn a.fn ⟨addHyp arrow F⟩ rev
    exact ⟨orLeft (Derivation.conjunctionIntroduction moved (symm (Derivation.conjunctionRight x)))⟩
  have two : D B (A :: Γ) (childAlternatives E ctx b a) := by
    have x : Derivation B (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
    have rev := reverse B α (A :: Γ) ctx a.dom a.arg b.arg ⟨Derivation.conjunctionRight x⟩
    obtain ⟨moved⟩ := changeType E ctx a.dom b.dom b.arg a.arg ⟨addHyp d A⟩ rev
    exact ⟨orRight (Derivation.conjunctionIntroduction (symm (Derivation.conjunctionLeft x)) moved)⟩
  obtain ⟨one⟩ := one
  obtain ⟨two⟩ := two
  exact ⟨disjunctionElimination sum (Derivation.implicationIntroduction one) (Derivation.implicationIntroduction two)⟩

/-- Both actual move directions and the original same-cover reports
survive the typed child check. This concerns the physical AST. -/
theorem exact_OpenTypedAuxEdgeReverses (Base E : Program 4)
    (base : CanReverse Base) (child : CanReverse E)
    (shape : Preserves Base (unaryObserver termShape)) : CanReverse (typedAuxEdgeGuard Base E) := by
  intro B α Γ ctx ty q r held
  apply optionGraphCases termShape ![q] _
  · intro β j Δ keep zero
    rw [edgeRename]
    rw [unaryInputsRename] at zero
    have a := renameInto held j Δ keep
    rw [edgeRename] at a
    let c := ctx.relabel j
    let t := ty.relabel j
    let x := q.relabel j
    let y := r.relabel j
    have old := exact_OpenTypedAuxEdgeBase Base E c t x y a
    have hy := shape B β Δ c t x y z old (exact_OpenUnaryObserverIntro termShape c t x z zero)
    exact exact_OpenTypedAuxEdgeNonAux Base E c t y x (base B β Δ c t x y old)
      (exact_OpenUnaryObserverElim termShape c t y z hy)
  · intro β j Δ event keep positive
    rw [edgeRename]
    rw [unaryInputsRename] at positive
    have e := renameInto held j Δ keep
    rw [edgeRename] at e
    let c := ctx.relabel j
    let t := ty.relabel j
    let u := q.relabel j
    let v := r.relabel j
    have positive := exact_OpenPositiveAuxShape u event positive
    have bare := exact_OpenTypedAuxEdgeBase Base E c t u v e
    apply exact_OpenAnyTypedAuxEdgeCases Base E c t u v _ e positive
    intro γ k Θ a b stay eqA eqB known
    rw [edgeRename]
    have old := renameInto bare k Θ stay
    rw [edgeRename] at old
    let ctx' := c.relabel k
    let ty' := t.relabel k
    let l := u.relabel k
    let r := v.relabel k
    have moved := exact_OpenRetapePackedEdge Base ctx' ty' l r a.term b.term eqA eqB old
    have swap := base B γ Θ ctx' ty' a.term b.term moved
    obtain ⟨known⟩ := known
    let d := Derivation.conjunctionLeft known
    let cod := Derivation.conjunctionLeft (Derivation.conjunctionRight known)
    have facts := exact_OpenReverseTypedChildCases E child ctx' a b ⟨d⟩ ⟨cod⟩
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight known)⟩
    have full := exact_OpenTypedAuxEdgeIntro Base E ctx' ty' b a swap ⟨symm d⟩ ⟨symm cod⟩ facts
    obtain ⟨eqA⟩ := eqA
    obtain ⟨eqB⟩ := eqB
    exact exact_OpenRetapePackedEdge (typedAuxEdgeGuard Base E) ctx' ty' b.term a.term r l
      ⟨symm eqB⟩ ⟨symm eqA⟩ full

theorem exact_OpenTypedAuxKeepsCover (C : Program 3) (s : Settings) (Base E : Program 4)
    (base : KeepsCover C s Base) : KeepsCover C s (typedAuxEdgeGuard Base E) := by
  intro B α Γ ctx ty q r v w held left right
  exact base B α Γ ctx ty q r v w (exact_OpenTypedAuxEdgeBase Base E ctx ty q r held) left right

#print axioms exact_OpenReverseTypedChildCases
#print axioms exact_OpenTypedAuxEdgeReverses
#print axioms exact_OpenTypedAuxKeepsCover
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedAuxEdgesReversalProof
