module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectRecognitionProof
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
open NumberedWindowInternalAuxBottomRefinement NumberedWindowInternalAuxBottomRefinementObjectTargets

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

private theorem literalFlag (c dom cod stored arg : OTerm α) :
    let x := packedAuxBottomTerm c dom cod stored arg
    Nonempty (Derivation B Γ (unary sourceFlag (suc z) x)) ∧
      Nonempty (Derivation B Γ (unary rawContext c x)) ∧
      Nonempty (Derivation B Γ (unary rawResult cod x)) := by
  let fn := rawCons (numeral 3) (packedBody [stored])
  let raw := rawCons (numeral 6) (packedBody [dom,cod,fn,arg])
  let x := addressTerm c cod raw
  let six := literal 1 6
  let three := literal 1 3
  obtain ⟨shell,ctx,ty,term⟩ := literalAddress (body := B) (Γ := Γ) c cod raw
  have tag6 : Nonempty (Derivation B Γ (unary six (numeral 6) raw)) := literalGraph 6 ![raw]
  have tag3 : Nonempty (Derivation B Γ (unary three (numeral 3) fn)) := literalGraph 3 ![fn]
  have aux := packedNode six (numeral 6) [dom,cod,fn,arg] tag6
  have bot := packedNode three (numeral 3) [stored] tag3
  have yesAux : Nonempty (Derivation B Γ (unary auxShell (suc z) x)) :=
    makeUnary (nodeGood six 4) rawLeast (suc z) x raw aux.1 term
  have knownCod : Nonempty (Derivation B Γ (unary auxCodomain cod x)) :=
    makeUnary (field 1) rawLeast cod x raw aux.2.2.1 term
  have knownFn : Nonempty (Derivation B Γ (unary auxFunction fn x)) :=
    makeUnary (field 2) rawLeast fn x raw aux.2.2.2.1 term
  have yesBot : Nonempty (Derivation B Γ (unary auxHeadBottom (suc z) x)) :=
    makeUnary (nodeGood three 1) auxFunction (suc z) x fn bot.1 knownFn
  have flag : Nonempty (Derivation B Γ (unary sourceFlag (suc z) x)) := by
    unfold sourceFlag
    rw [exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2,
      exact_DispatchControlAST.2.2.2.2.2]
    exact conjunctionAccept addressGood (conjunction auxShell (conjunction auxHeadBottom resultFits)) ![x] shell
      (conjunctionAccept auxShell (conjunction auxHeadBottom resultFits) ![x] yesAux
        (conjunctionAccept auxHeadBottom resultFits ![x] yesBot (fitLiteral x cod ty knownCod)))
  exact ⟨flag,ctx,ty⟩

theorem exactRecognition : ExactOpenAuxBottomRecognition := by
  intro B α Γ x c dom cod stored arg shape
  let source := packedAuxBottomTerm c dom cod stored arg
  have reverse := inverseEq x source shape
  obtain ⟨known,ctx,codomain⟩ := literalFlag (B := B) (Γ := Γ) c dom cod stored arg
  obtain ⟨flag⟩ := unaryInput sourceFlag (suc z) source x reverse known
  obtain ⟨c'⟩ := unaryInput rawContext c source x reverse ctx
  obtain ⟨e'⟩ := unaryInput rawResult cod source x reverse codomain
  exact ⟨Derivation.conjunctionIntroduction flag (Derivation.conjunctionIntroduction c' e')⟩

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectRecognitionProof
