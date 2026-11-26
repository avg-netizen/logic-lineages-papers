module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenEdgeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (oneGraph packedNode readNode)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem edgeCanonical (q w r : OTerm α) :
    Nonempty (Derivation body Γ (edgeCertified (edgeCodeTerm q w r) q w r)) := by
  let n := edgeCodeTerm q w r
  have full : Nonempty (Derivation body Γ (unary edgeGood (suc z) n)) ∧
      Reports body Γ n cellTail [q,r,w] :=
    packedNode one (suc z) [q,r,w] (oneGraph n)
  obtain ⟨ok⟩ := full.1
  obtain ⟨source⟩ := full.2.1
  obtain ⟨target⟩ := full.2.2.1
  obtain ⟨witness⟩ := full.2.2.2.1
  exact ⟨Derivation.conjunctionIntroduction ok
    (Derivation.conjunctionIntroduction source (Derivation.conjunctionIntroduction witness target))⟩

theorem edgeRead (n q w r : OTerm α)
    (e : Nonempty (Derivation body Γ (edgeCertified n q w r))) :
    Nonempty (Derivation body Γ (eqn n (edgeCodeTerm q w r))) := by
  obtain ⟨e⟩ := e
  have abc := Derivation.conjunctionRight e
  have bc := Derivation.conjunctionRight abc
  have positions : Reports body Γ n cellTail [q,r,w] :=
    ⟨⟨Derivation.conjunctionLeft abc⟩,⟨Derivation.conjunctionRight bc⟩,
     ⟨Derivation.conjunctionLeft bc⟩,trivial⟩
  exact readNode one n (suc z) [q,r,w] (oneGraph n) ⟨Derivation.conjunctionLeft e⟩ positions

private theorem transferEdge (n m q w r : OTerm α)
    (h : Nonempty (Derivation body Γ (eqn n m)))
    (e : Nonempty (Derivation body Γ (edgeCertified n q w r))) :
    Nonempty (Derivation body Γ (edgeCertified m q w r)) := by
  obtain ⟨cert⟩ := e
  have values := Derivation.conjunctionRight cert
  have wr := Derivation.conjunctionRight values
  obtain ⟨g⟩ := moveUnary edgeGood (suc z) n m h ⟨Derivation.conjunctionLeft cert⟩
  obtain ⟨a⟩ := moveUnary edgeSource q n m h ⟨Derivation.conjunctionLeft values⟩
  obtain ⟨b⟩ := moveUnary edgeWitness w n m h ⟨Derivation.conjunctionLeft wr⟩
  obtain ⟨c⟩ := moveUnary edgeTarget r n m h ⟨Derivation.conjunctionRight wr⟩
  exact ⟨Derivation.conjunctionIntroduction g
    (Derivation.conjunctionIntroduction a (Derivation.conjunctionIntroduction b c))⟩

theorem openEdge : OpenEdgeEnvelope := by
  intro body α n q w r
  let canonical := edgeCodeTerm q w r
  let equality := eqn n canonical
  let certified := edgeCertified n q w r
  have h0 : Derivation body [equality] equality := Derivation.hypothesis List.mem_cons_self
  have h1 : Derivation body [certified] certified := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward⟩ := transferEdge canonical n q w r ⟨symm h0⟩ (edgeCanonical q w r)
  obtain ⟨backward⟩ := edgeRead n q w r ⟨h1⟩
  simpa only [equalEqn] using
    (Nonempty.intro (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
      (Derivation.implicationIntroduction backward)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenEdgeProof
