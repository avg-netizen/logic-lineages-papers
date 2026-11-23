module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalAtomicRefinementObjectTargets (sourceFields)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph unaryInput)
open NumberedWindowInternalAtomicRefinementObjectSelectorsProof (literalAddress inverseEq)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawResult rawContext rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalSparsePathEnvelope (field nodeGood)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalAuxBottomRefinement (auxCodomain auxFunction auxShell resultFits)
open NumberedWindowInternalNeutralAuxiliaryRefinement (freeAux auxHeadFree auxDom auxFnType)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm freeTerm)
open NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

section
attribute [local irreducible] programGraph

private theorem fitLiteral (x e : OTerm α)
    (h : Nonempty (Derivation B Γ (unary rawResult e x)))
    (g : Nonempty (Derivation B Γ (unary auxCodomain e x))) :
    Nonempty (Derivation B Γ (unary resultFits (suc z) x)) := by
  unfold resultFits
  rw [exact_DispatchControlAST.2.2.2.1]
  apply compositionValue equalityTest
    (Fin.cons rawResult (Fin.cons auxCodomain Fin.elim0)) (suc z) ![x] ![e,e] (equalitySelf e)
  intro j
  exact Fin.cases h (Fin.cases g (fun k => Fin.elim0 k)) j

private theorem literalFlag (c dom cod stored name arg : OTerm α) :
    let x := auxAddressTerm c dom cod (freeTerm stored name) arg
    Nonempty (Derivation B Γ (unary freeAux (suc z) x)) ∧
      Nonempty (Derivation B Γ (unary rawContext c x)) ∧
      Nonempty (Derivation B Γ (unary rawResult cod x)) ∧
      Nonempty (Derivation B Γ (unary auxDom dom x)) ∧
      Nonempty (Derivation B Γ (unary auxFnType stored x)) := by
  let fn := rawCons (numeral 0) (packedBody [stored,name])
  let raw := rawCons (numeral 6) (packedBody [dom,cod,fn,arg])
  let x := addressTerm c cod raw
  let six := literal 1 6
  let zero := literal 1 0
  obtain ⟨shell,ctx,ty,term⟩ := literalAddress (body := B) (Γ := Γ) c cod raw
  have tag6 : Nonempty (Derivation B Γ (unary six (numeral 6) raw)) := literalGraph 6 ![raw]
  have tag0 : Nonempty (Derivation B Γ (unary zero (numeral 0) fn)) := literalGraph 0 ![fn]
  have aux := packedNode six (numeral 6) [dom,cod,fn,arg] tag6
  have free := packedNode zero (numeral 0) [stored,name] tag0
  have yesAux : Nonempty (Derivation B Γ (unary auxShell (suc z) x)) :=
    makeUnary (nodeGood six 4) rawLeast (suc z) x raw aux.1 term
  have knownCod : Nonempty (Derivation B Γ (unary auxCodomain cod x)) :=
    makeUnary (field 1) rawLeast cod x raw aux.2.2.1 term
  have knownFn : Nonempty (Derivation B Γ (unary auxFunction fn x)) :=
    makeUnary (field 2) rawLeast fn x raw aux.2.2.2.1 term
  have knownDom : Nonempty (Derivation B Γ (unary auxDom dom x)) :=
    makeUnary (field 0) rawLeast dom x raw aux.2.1 term
  have knownStored : Nonempty (Derivation B Γ (unary auxFnType stored x)) :=
    makeUnary (field 0) auxFunction stored x fn free.2.1 knownFn
  have yesFree : Nonempty (Derivation B Γ (unary auxHeadFree (suc z) x)) :=
    makeUnary (nodeGood zero 2) auxFunction (suc z) x fn free.1 knownFn
  have flag : Nonempty (Derivation B Γ (unary freeAux (suc z) x)) := by
    unfold freeAux
    rw [exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2,
      exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept addressGood (conjunction auxShell (conjunction auxHeadFree resultFits)) ![x] shell
      (conjunctionAccept auxShell (conjunction auxHeadFree resultFits) ![x] yesAux
        (conjunctionAccept auxHeadFree resultFits ![x] yesFree (fitLiteral x cod ty knownCod)))
  exact ⟨flag,ctx,ty,knownDom,knownStored⟩

theorem exact_OriginalNeutralAuxiliaryRecognition : ExactOpenNeutralAuxiliaryRecognition := by
  intro B α Γ x c dom cod stored name arg shape
  let source := auxAddressTerm c dom cod (freeTerm stored name) arg
  have reverse := inverseEq x source shape
  obtain ⟨known,ctx,codomain,domain,storedType⟩ := literalFlag (B := B) (Γ := Γ) c dom cod stored name arg
  obtain ⟨flag⟩ := unaryInput freeAux (suc z) source x reverse known
  obtain ⟨c'⟩ := unaryInput rawContext c source x reverse ctx
  obtain ⟨e'⟩ := unaryInput rawResult cod source x reverse codomain
  obtain ⟨d'⟩ := unaryInput auxDom dom source x reverse domain
  obtain ⟨t'⟩ := unaryInput auxFnType stored source x reverse storedType
  exact ⟨Derivation.conjunctionIntroduction flag
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction c' e')
      (Derivation.conjunctionIntroduction d' t'))⟩

#print axioms exact_OriginalNeutralAuxiliaryRecognition

end

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryRefinementRecognitionProof
