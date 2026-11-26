module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixMachineProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixFrameOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro zeroBranchIntro)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (applyUnary cursor)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseRawTick (emitState stateFrame rowBody)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawTickOpenScratchProof (frameRead)
open NumberedWindowInternalSparseRawTickShapeEmitterProof (consOfGraph emitGraph)
open NumberedWindowInternalFreshProbeEmitter (consOf)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPrefixFrameEmit (p u v h k : Program 5) (xs : Fin 5 → OTerm α)
    (c t q w r : OTerm α)
    (mc : D B Γ (programGraph p c xs)) (mt : D B Γ (programGraph u t xs))
    (mq : D B Γ (programGraph v q xs)) (mw : D B Γ (programGraph h w xs))
    (mr : D B Γ (programGraph k r xs)) :
    D B Γ (programGraph (prefixFrame p u v h k) (prefixFrameTerm c t q w r) xs) := by
  let p₄ := consOf k (constantZero 5)
  let p₃ := consOf h p₄
  let p₂ := consOf v p₃
  let p₁ := consOf u p₂
  let p₀ := consOf p p₁
  let body := packedBody [c,t,q,w,r]
  have last := consOfGraph k (constantZero 5) r z xs mr (constantZeroValue xs)
  have four := consOfGraph h p₄ w (packedBody [r]) xs mw last
  have three := consOfGraph v p₃ q (packedBody [w,r]) xs mq four
  have two := consOfGraph u p₂ t (packedBody [q,w,r]) xs mt three
  have one := consOfGraph p p₁ c (packedBody [t,q,w,r]) xs mc two
  apply compositionValue .succ (fun _ : Fin 1 => p₀) (suc body) xs ![body] (successorValue ![body])
  intro j
  obtain rfl := Fin.eq_zero j
  exact one

theorem exact_OpenPrefixStart (c t q w r : OTerm α) :
    D B Γ (programGraph prefixStart (prefixStartTerm c t q w r) ![c,t,q,w,r]) := by
  let xs : Fin 5 → OTerm α := ![c,t,q,w,r]
  let frame := prefixFrameTerm c t q w r
  have row := exact_OpenPrefixFrameEmit (B := B) (Γ := Γ) (.projection 0) (.projection 1) (.projection 2) (.projection 3) (.projection 4)
    xs c t q w r (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue 2 xs) (projectionValue 3 xs)
    (projectionValue 4 xs)
  exact emitGraph _ _ (suc z) frame xs (oneConstantValue xs) row

private theorem knownBody (flag c t q w r : OTerm α) :
    D B Γ (unary rowBody (packedBody [c,t,q,w,r]) (stateTerm flag (prefixFrameTerm c t q w r))) := by
  let code := packedBody [c,t,q,w,r]
  have prev : D B Γ (unary predOne code (suc code)) := by
    rw [exact_DispatchControlAST.2.2.1]
    exact predecessorSuccessor code
  exact makeUnary predOne stateFrame code (stateTerm flag (suc code)) (suc code) prev (frameRead flag (suc code))

private theorem cellHeads (a b : OTerm α) :
    D B Γ (unary cellHead a (rawCons a b)) ∧ D B Γ (unary cellTail b (rawCons a b)) := by
  obtain ⟨row⟩ := canonicalCell (body := B) (Γ := Γ) a b
  exact ⟨⟨Derivation.conjunctionLeft (Derivation.conjunctionRight row)⟩,
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight row)⟩⟩

/-- All five previous typed frame selectors are the literal values of
that frame, including the same lexical context and remaining witness. -/
theorem exact_OpenPrefixRead (flag c t q w r : OTerm α) :
    let state := stateTerm flag (prefixFrameTerm c t q w r)
    D B Γ (unary (prefixReadSlot 0) c state) ∧ D B Γ (unary (prefixReadSlot 1) t state) ∧
      D B Γ (unary (prefixReadSlot 2) q state) ∧ D B Γ (unary (prefixReadSlot 3) w state) ∧
      D B Γ (unary (prefixReadSlot 4) r state) := by
  let s := stateTerm flag (prefixFrameTerm c t q w r)
  let x₀ := packedBody [c,t,q,w,r]
  let x₁ := packedBody [t,q,w,r]
  let x₂ := packedBody [q,w,r]
  let x₃ := packedBody [w,r]
  let x₄ := packedBody [r]
  have a := cellHeads (B := B) (Γ := Γ) c x₁
  have b := cellHeads (B := B) (Γ := Γ) t x₂
  have d := cellHeads (B := B) (Γ := Γ) q x₃
  have e := cellHeads (B := B) (Γ := Γ) w x₄
  have f := cellHeads (B := B) (Γ := Γ) r z
  have row := knownBody (B := B) (Γ := Γ) flag c t q w r
  have r₁ : D B Γ (unary (cursor 0) x₁ x₀) := a.2
  have r₂ := makeUnary cellTail (cursor 0) x₂ x₀ x₁ b.2 r₁
  have r₃ := makeUnary cellTail (cursor 1) x₃ x₀ x₂ d.2 r₂
  have r₄ := makeUnary cellTail (cursor 2) x₄ x₀ x₃ e.2 r₃
  refine ⟨makeUnary cellHead rowBody c s x₀ a.1 row,?_,?_,?_,?_⟩
  · exact makeUnary (applyUnary cellHead (cursor 0)) rowBody t s x₀
      (makeUnary cellHead (cursor 0) t x₀ x₁ b.1 r₁) row
  · exact makeUnary (applyUnary cellHead (cursor 1)) rowBody q s x₀
      (makeUnary cellHead (cursor 1) q x₀ x₂ d.1 r₂) row
  · exact makeUnary (applyUnary cellHead (cursor 2)) rowBody w s x₀
      (makeUnary cellHead (cursor 2) w x₀ x₃ e.1 r₃) row
  · exact makeUnary (applyUnary cellHead (cursor 3)) rowBody r s x₀
      (makeUnary cellHead (cursor 3) r x₀ x₄ f.1 r₄) row

theorem exact_OpenPrefixTickAtFrame (W : Program 3) (flag c t q w r out : OTerm α)
    (held : D B Γ (programGraph (prefixLive W) out ![c,t,q,w,r])) :
    D B Γ (programGraph (prefixTick W) out ![stateTerm flag (prefixFrameTerm c t q w r)]) := by
  let frame := prefixFrameTerm c t q w r
  let body := packedBody [c,t,q,w,r]
  let state := stateTerm flag frame
  obtain ⟨a,b,d,e,f⟩ := exact_OpenPrefixRead (B := B) (Γ := Γ) flag c t q w r
  have call : D B Γ (programGraph (prefixPerform W) out ![state]) := by
    apply compositionValue (prefixLive W) ![prefixReadSlot 0,prefixReadSlot 1,prefixReadSlot 2,prefixReadSlot 3,prefixReadSlot 4]
      out ![state] ![c,t,q,w,r] held
    intro i
    exact Fin.cases a (Fin.cases b (Fin.cases d (Fin.cases e (Fin.cases f (fun j => Fin.elim0 j))))) i
  exact successorBranchIntro stateFrame (.projection 0) (prefixPerform W) out body ![state]
    (frameRead flag frame) call

theorem exact_OpenPrefixTickTerminal (W : Program 3) (flag : OTerm α) :
    D B Γ (programGraph (prefixTick W) (stateTerm flag z) ![stateTerm flag z]) := by
  exact zeroBranchIntro stateFrame (.projection 0) (prefixPerform W) (stateTerm flag z)
    ![stateTerm flag z] (frameRead flag z) (projectionValue 0 ![stateTerm flag z])

#print axioms exact_OpenPrefixFrameEmit
#print axioms exact_OpenPrefixStart
#print axioms exact_OpenPrefixRead
#print axioms exact_OpenPrefixTickAtFrame
#print axioms exact_OpenPrefixTickTerminal
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixFrameOpenProof
