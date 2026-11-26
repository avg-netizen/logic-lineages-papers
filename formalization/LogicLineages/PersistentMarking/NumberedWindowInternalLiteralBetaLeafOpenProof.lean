module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue outputTransport)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseRawFunctionFrame (onRaw frameSlot)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open NumberedWindowInternalLiteralAuxRootLeafFieldsProof (sourceParts)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases moveBit)
open NumberedWindowInternalLiteralBetaLeafProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def rawLambdaTerm {α : Type} (ty body : OTerm α) : OTerm α :=
  rawCons (numeral 2) (packedBody [ty,body])

structure BetaCalls (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (U : Program 2)
    (q w r : OTerm α) : Prop where
  source : D B Γ (bit sourceIsAux ![q,w,r])
  functionShape : D B Γ (bit functionShape ![q,w,r])
  domainMatch : D B Γ (bit domainMatch ![q,w,r])
  targetMatch : D B Γ (bit (targetMatch U) ![q,w,r])

theorem exact_OpenLiteralBetaCalls (V : Program 1) (U : Program 2) (q w r : OTerm α)
    (h : D B Γ (bit (literalBetaLeaf V U) ![q,w,r])) : BetaCalls B Γ U q w r := by
  unfold literalBetaLeaf at h
  let xs : Fin 3 → OTerm α := ![q,w,r]
  obtain ⟨a⟩ := conjunctionRecover _ _ xs h
  obtain ⟨b⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight a⟩
  obtain ⟨c⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight b⟩
  obtain ⟨d⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight c⟩
  obtain ⟨e⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight d⟩
  exact ⟨⟨Derivation.conjunctionLeft c⟩,⟨Derivation.conjunctionLeft d⟩,
    ⟨Derivation.conjunctionLeft e⟩,⟨Derivation.conjunctionRight e⟩⟩

private theorem lambdaRead (q w r fn b : OTerm α) (n : Nat)
    (F : D B Γ (programGraph rawFunction fn ![q,w,r]))
    (held : D B Γ (unary (field n) b fn)) :
    D B Γ (programGraph (lambdaField n) b ![q,w,r]) := by
  apply compositionValue (field n) (fun _ : Fin 1 => rawFunction) b ![q,w,r] ![fn] held
  intro j
  obtain rfl := Fin.eq_zero j
  exact F

theorem exact_OpenBetaInstanceFromSelectors (U : Program 2) (q w r dom fn arg bind body : OTerm α)
    (held : BetaCalls B Γ U q w r)
    (d : D B Γ (unary (field 0) dom q)) (f : D B Γ (unary (field 2) fn q))
    (a : D B Γ (unary (field 3) arg q)) (t : D B Γ (unary (field 0) bind fn))
    (b : D B Γ (unary (field 1) body fn)) :
    D B Γ (eqn dom bind) ∧ D B Γ (programGraph U (suc r) ![arg,body]) := by
  let xs : Fin 3 → OTerm α := ![q,w,r]
  have F : D B Γ (programGraph rawFunction fn xs) := onTape (field 2) 0 fn xs f
  have domRead : D B Γ (programGraph (frameSlot 0 0) dom xs) := onTape (field 0) 0 dom xs d
  have aRead : D B Γ (programGraph (frameSlot 3 0) arg xs) := onTape (field 3) 0 arg xs a
  have tRead := lambdaRead q w r fn bind 0 F t
  have bRead := lambdaRead q w r fn body 1 F b
  have agree : D B Γ (eqn dom bind) := by
    apply equalityOfAcceptance
    apply compositionRecover equalityTest ![frameSlot 0 0,lambdaField 0] (suc z) xs ![dom,bind] held.domainMatch
    intro i
    exact Fin.cases domRead (Fin.cases tRead (fun e => Fin.elim0 e)) i
  refine ⟨agree,?_⟩
  apply programCases (instanceAt U) xs _
  intro β j Δ out keep call
  have known := moveBit _ q w r j Δ keep held.targetMatch
  have ar := renameInto aRead j Δ keep
  have br := renameInto bRead j Δ keep
  simp only [xs,ID1Completion.InternalControlGraphSupportProof.programRename,
    NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename] at call ar br
  let ys : Fin 3 → OTerm β := ![q.relabel j,w.relabel j,r.relabel j]
  let z₀ := r.relabel j
  have next : D B Δ (programGraph nextCode (suc z₀) ys) := by
    apply compositionValue .succ (fun _ : Fin 1 => .projection 2) (suc z₀) ys ![z₀] (successorValue ![z₀])
    intro v
    obtain rfl := Fin.eq_zero v
    exact projectionValue 2 ys
  have same : D B Δ (eqn out (suc z₀)) := by
    apply equalityOfAcceptance
    apply compositionRecover equalityTest ![instanceAt U,nextCode] (suc z) ys ![out,suc z₀] known
    intro i
    exact Fin.cases call (Fin.cases next (fun e => Fin.elim0 e)) i
  have raw := compositionRecover U ![frameSlot 3 0,lambdaField 1] out ys ![arg.relabel j,body.relabel j] call
    (fun i => Fin.cases ar (Fin.cases br (fun e => Fin.elim0 e)) i)
  rw [programRename,binaryInputsRename,sucRelabel]
  exact outputTransport U out (suc z₀) ![arg.relabel j,body.relabel j] same raw

#print axioms exact_OpenLiteralBetaCalls
#print axioms exact_OpenBetaInstanceFromSelectors
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaLeafOpenProof
