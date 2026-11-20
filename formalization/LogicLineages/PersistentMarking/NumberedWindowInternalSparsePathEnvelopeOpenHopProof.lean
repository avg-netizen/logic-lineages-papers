module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenEdgeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenHopProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparsePathEnvelope
open NumberedWindowInternalSparsePathEnvelopeTargets
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (twoGraph packedNode readNode)
open NumberedWindowInternalSparsePathEnvelopeOpenEdgeProof (edgeCanonical edgeRead)

private theorem hopCodeRename {α β : Type} (t q w r : OTerm α) (j : α → β) :
    (hopCodeTerm t q w r).relabel j =
      hopCodeTerm (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j) := by
  simp only [hopCodeTerm,rawConsRename,edgeCodeRename,sucRelabel,zRelabel]

private theorem hopCertifiedRename {α β : Type} (n t q w r : OTerm α) (j : α → β) :
    (hopCertified n t q w r).relabel j = hopCertified
      (n.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j) := by
  simp only [hopCertified,conjunctionRename,unaryRename,sucRelabel,zRelabel]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem hopCanonical (t q w r : OTerm α) :
    Nonempty (Derivation body Γ (hopCertified (hopCodeTerm t q w r) t q w r)) := by
  let e := edgeCodeTerm q w r
  let n := hopCodeTerm t q w r
  have outer : Nonempty (Derivation body Γ (unary (nodeGood two 2) (suc z) n)) ∧
      Reports body Γ n cellTail [t,e] :=
    packedNode two (suc (suc z)) [t,e] (twoGraph n)
  obtain ⟨nested⟩ := edgeCanonical (body := body) (Γ := Γ) q w r
  obtain ⟨outerResult⟩ := outer.2.1
  have edgeRef : Nonempty (Derivation body Γ (unary (field 1) e n)) := outer.2.2.1
  obtain ⟨guard⟩ := conjunctionAccept (nodeGood two 2) (applyUnary edgeGood (field 1)) ![n]
    outer.1 (makeUnary edgeGood (field 1) (suc z) n e ⟨Derivation.conjunctionLeft nested⟩ edgeRef)
  have values := Derivation.conjunctionRight nested
  have wr := Derivation.conjunctionRight values
  obtain ⟨source⟩ := makeUnary edgeSource (field 1) q n e ⟨Derivation.conjunctionLeft values⟩ edgeRef
  obtain ⟨witness⟩ := makeUnary edgeWitness (field 1) w n e ⟨Derivation.conjunctionLeft wr⟩ edgeRef
  obtain ⟨target⟩ := makeUnary edgeTarget (field 1) r n e ⟨Derivation.conjunctionRight wr⟩ edgeRef
  exact ⟨Derivation.conjunctionIntroduction guard
    (Derivation.conjunctionIntroduction outerResult
      (Derivation.conjunctionIntroduction source (Derivation.conjunctionIntroduction witness target)))⟩

private theorem readWithEdge (n t q w r e : OTerm α)
    (given : Nonempty (Derivation body Γ (hopCertified n t q w r)))
    (ref : Nonempty (Derivation body Γ (unary (field 1) e n))) :
    Nonempty (Derivation body Γ (eqn n (hopCodeTerm t q w r))) := by
  obtain ⟨d⟩ := given
  obtain ⟨guards⟩ := conjunctionRecover (nodeGood two 2) (applyUnary edgeGood (field 1)) ![n]
    ⟨Derivation.conjunctionLeft d⟩
  have vs := Derivation.conjunctionRight d
  have qat := Derivation.conjunctionRight vs
  have wat := Derivation.conjunctionRight qat
  obtain ⟨good⟩ := takeUnary edgeGood (field 1) (suc z) n e ⟨Derivation.conjunctionRight guards⟩ ref
  obtain ⟨source⟩ := takeUnary edgeSource (field 1) q n e ⟨Derivation.conjunctionLeft qat⟩ ref
  obtain ⟨witness⟩ := takeUnary edgeWitness (field 1) w n e ⟨Derivation.conjunctionLeft wat⟩ ref
  obtain ⟨target⟩ := takeUnary edgeTarget (field 1) r n e ⟨Derivation.conjunctionRight wat⟩ ref
  have edge : Nonempty (Derivation body Γ (edgeCertified e q w r)) :=
    ⟨Derivation.conjunctionIntroduction good
      (Derivation.conjunctionIntroduction source (Derivation.conjunctionIntroduction witness target))⟩
  let packed := edgeCodeTerm q w r
  have edgeAt : Nonempty (Derivation body Γ (unary (field 1) packed n)) :=
    outputTransport (field 1) e packed ![n] (edgeRead e q w r edge) ref
  have reports : Reports body Γ n cellTail [t,packed] :=
    ⟨⟨Derivation.conjunctionLeft vs⟩,edgeAt,trivial⟩
  exact readNode two n (suc (suc z)) [t,packed] (twoGraph n)
    ⟨Derivation.conjunctionLeft guards⟩ reports

private theorem hopRead (n t q w r : OTerm α)
    (given : Nonempty (Derivation body Γ (hopCertified n t q w r))) :
    Nonempty (Derivation body Γ (eqn n (hopCodeTerm t q w r))) := by
  apply programCases (field 1) ![n] _
  intro β j Δ edge hJ ref
  rw [eqnRelabel,hopCodeRename]
  rw [inputsRename] at ref
  have next := renameInto given j Δ hJ
  rw [hopCertifiedRename] at next
  exact readWithEdge (n.relabel j) (t.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)
    edge next ref

private theorem transferHop (n m t q w r : OTerm α)
    (h : Nonempty (Derivation body Γ (eqn n m)))
    (e : Nonempty (Derivation body Γ (hopCertified n t q w r))) :
    Nonempty (Derivation body Γ (hopCertified m t q w r)) := by
  obtain ⟨cert⟩ := e
  have vs := Derivation.conjunctionRight cert
  have qat := Derivation.conjunctionRight vs
  have wat := Derivation.conjunctionRight qat
  obtain ⟨g⟩ := moveUnary hopGood (suc z) n m h ⟨Derivation.conjunctionLeft cert⟩
  obtain ⟨a⟩ := moveUnary hopTarget t n m h ⟨Derivation.conjunctionLeft vs⟩
  obtain ⟨b⟩ := moveUnary hopSource q n m h ⟨Derivation.conjunctionLeft qat⟩
  obtain ⟨c⟩ := moveUnary hopWitness w n m h ⟨Derivation.conjunctionLeft wat⟩
  obtain ⟨d⟩ := moveUnary hopRawTarget r n m h ⟨Derivation.conjunctionRight wat⟩
  exact ⟨Derivation.conjunctionIntroduction g
    (Derivation.conjunctionIntroduction a
      (Derivation.conjunctionIntroduction b (Derivation.conjunctionIntroduction c d)))⟩

theorem openHop : OpenHopEnvelope := by
  intro body α n t q w r
  let canonical := hopCodeTerm t q w r
  let equality := eqn n canonical
  let certified := hopCertified n t q w r
  have h0 : Derivation body [equality] equality := Derivation.hypothesis List.mem_cons_self
  have h1 : Derivation body [certified] certified := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward⟩ := transferHop canonical n t q w r ⟨symm h0⟩ (hopCanonical t q w r)
  obtain ⟨backward⟩ := hopRead n t q w r ⟨h1⟩
  simpa only [equalEqn] using
    (Nonempty.intro (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
      (Derivation.implicationIntroduction backward)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenHopProof
