module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverTapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseCoverScratchOpenTargets (callbackTape callbackAt)
open NumberedWindowInternalSparseCoverScratchOpenSyntaxProof (optionFromCallback)
open NumberedWindowInternalFactoredCoverTargets (factoredCover rawCall generatorCall)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption termListAtMeasure)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem thirdReport (p : Program 1) (out a b c : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p out c))) :
    Nonempty (Derivation body Γ (programGraph (rawCall p) out ![a,b,c])) := by
  apply compositionValue p (fun _ : Fin 1 => .projection (2 : Fin 3)) out ![a,b,c] ![c] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (2 : Fin 3) ![a,b,c]

theorem selectedOptionFromActualList (H K m vertices : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph termListAtMeasure vertices ![H,K,m]))) :
    Nonempty (Derivation body Γ (programGraph selectedGrammarOption (suc vertices) ![H,K,m])) := by
  apply compositionValue .succ (fun _ : Fin 1 => termListAtMeasure) (suc vertices) ![H,K,m]
    ![vertices] (successorValue ![vertices])
  intro i
  obtain rfl := Fin.eq_zero i
  exact actual

theorem coverFromActualGenerator (V N : Program 1) (s : Settings) (vertices m seed : OTerm α)
    (valid : Nonempty (Derivation body Γ (unary V (suc z) seed)))
    (measure : Nonempty (Derivation body Γ (unary N m seed)))
    (generator : Nonempty (Derivation body Γ
      (programGraph selectedGrammarOption (suc vertices) ![headsTerm s α,typesTerm s α,m]))) :
    Nonempty (Derivation body Γ (unary (coverOption (factoredCover V N selectedGrammarOption) s) (suc vertices) seed)) := by
  let H := headsTerm s α
  let K := typesTerm s α
  let C := factoredCover V N selectedGrammarOption
  let xs := callbackTape s seed
  let parts : Fin 3 → Program 3 :=
    Fin.cons (.projection 0) (Fin.cons (.projection 1) (Fin.cons (rawCall N) Fin.elim0))
  have ready : Nonempty (Derivation body Γ (programGraph (generatorCall N selectedGrammarOption) (suc vertices) xs)) := by
    apply compositionValue selectedGrammarOption parts (suc vertices) xs ![H,K,m] generator
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (thirdReport N m H K seed measure) (fun k => Fin.elim0 k))) i
  have callback : Nonempty (Derivation body Γ (callbackAt C s (suc vertices) seed)) :=
    successorBranchIntro (rawCall V) (constantZero 3) (generatorCall N selectedGrammarOption) (suc vertices) z
      xs (thirdReport V (suc z) H K seed valid) ready
  exact optionFromCallback C s (suc vertices) seed callback

#print axioms selectedOptionFromActualList
#print axioms coverFromActualGenerator
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverTapeProof
