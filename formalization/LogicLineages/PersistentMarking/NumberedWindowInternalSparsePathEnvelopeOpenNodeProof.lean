module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenBodyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue outputTransport successorValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof
open NumberedWindowInternalSparsePathEnvelopeOpenBodyProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem oneGraph (n : OTerm α) :
    Nonempty (Derivation body Γ (unary one (suc z) n)) :=
  oneConstantValue ![n]

theorem twoGraph (n : OTerm α) :
    Nonempty (Derivation body Γ (unary two (suc (suc z)) n)) :=
  makeUnary .succ one (suc (suc z)) n (suc z) (successorValue ![suc z]) (oneGraph n)

private theorem proveTag (tag : Program 1) (n k : OTerm α)
    (head : Nonempty (Derivation body Γ (unary cellHead k n)))
    (code : Nonempty (Derivation body Γ (unary tag k n))) :
    Nonempty (Derivation body Γ (unary (.composition equalityTest ![cellHead,tag]) (suc z) n)) := by
  apply compositionValue equalityTest ![cellHead,tag] (suc z) ![n] ![k,k] (equalitySelf k)
  intro i
  exact Fin.cases head (Fin.cases code (fun l => Fin.elim0 l)) i

private theorem recoverTag (tag : Program 1) (n k : OTerm α)
    (accepted : Nonempty (Derivation body Γ
      (unary (.composition equalityTest ![cellHead,tag]) (suc z) n)))
    (code : Nonempty (Derivation body Γ (unary tag k n))) :
    Nonempty (Derivation body Γ (unary cellHead k n)) := by
  apply programCases cellHead ![n] _
  intro β j Δ h hJ candidate
  rw [unaryRename]
  rw [inputsRename] at candidate
  let node := n.relabel j
  let tagVal := k.relabel j
  have other := moveReport j Δ hJ tag k n code
  have passed := moveReport j Δ hJ (.composition equalityTest ![cellHead,tag]) (suc z) n accepted
  simp only [sucRelabel,zRelabel] at passed
  have actual := compositionRecover equalityTest ![cellHead,tag] (suc z) ![node] ![h,tagVal] passed
    (fun i => Fin.cases candidate (Fin.cases other (fun l => Fin.elim0 l)) i)
  exact outputTransport cellHead h tagVal ![node] (equalityOfAcceptance h tagVal actual) candidate

theorem packedNode (tag : Program 1) (k : OTerm α) (xs : List (OTerm α))
    (tc : Nonempty (Derivation body Γ (unary tag k (rawCons k (packedBody xs))))) :
    let n := rawCons k (packedBody xs)
    Nonempty (Derivation body Γ (unary (nodeGood tag xs.length) (suc z) n)) ∧
      Reports body Γ n cellTail xs := by
  let t := packedBody xs
  let n := rawCons k t
  obtain ⟨hc⟩ := canonicalCell (body := body) (Γ := Γ) k t
  have head : Nonempty (Derivation body Γ (unary cellHead k n)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hc)⟩
  have tail : Nonempty (Derivation body Γ (unary cellTail t n)) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hc)⟩
  have arity := makeUnary (exactBody xs.length) cellTail (suc z) n t (packedArity xs) tail
  have tagPassed := proveTag tag n k head tc
  have checked := conjunctionAccept (.composition equalityTest ![cellHead,tag])
    (applyUnary (exactBody xs.length) cellTail) ![n] tagPassed arity
  exact ⟨conjunctionAccept cellGood
    (conjunction (.composition equalityTest ![cellHead,tag]) (applyUnary (exactBody xs.length) cellTail))
    ![n] ⟨Derivation.conjunctionLeft hc⟩ checked, packedReports n cellTail xs tail⟩

theorem readNode (tag : Program 1) (n k : OTerm α) (xs : List (OTerm α))
    (tc : Nonempty (Derivation body Γ (unary tag k n)))
    (good : Nonempty (Derivation body Γ (unary (nodeGood tag xs.length) (suc z) n)))
    (reports : Reports body Γ n cellTail xs) :
    Nonempty (Derivation body Γ (eqn n (rawCons k (packedBody xs)))) := by
  let e := Program.composition equalityTest (![cellHead,tag] : Fin 2 → Program 1)
  let a := applyUnary (exactBody xs.length) cellTail
  obtain ⟨checked⟩ := conjunctionRecover cellGood (conjunction e a) ![n] good
  obtain ⟨inner⟩ := conjunctionRecover e a ![n] ⟨Derivation.conjunctionRight checked⟩
  have head := recoverTag tag n k ⟨Derivation.conjunctionLeft inner⟩ tc
  have tail := readPackedBody body xs.length α Γ n cellTail xs rfl
    ⟨Derivation.conjunctionRight inner⟩ reports
  exact cellEquation n k (packedBody xs) ⟨Derivation.conjunctionLeft checked⟩ head tail

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
