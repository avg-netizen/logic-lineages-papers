module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalUnpairProof (actualOriginalGeneratedCodeInverse)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalSparseCoverScratchOpenTargets (callbackTape callbackAt)
open NumberedWindowInternalSparseCoverScratchOpenBranchProof (scratchSuccessor)
open NumberedWindowInternalSparseCoverScratchOpenSyntaxProof (optionFromCallback)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open NumberedWindowInternalFactoredCoverTargets (factoredCover rawCall generatorCall)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarTargets
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem thirdReport (p : Program 1) (out a b c : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p out c))) :
    Nonempty (Derivation body Γ (programGraph
      (.composition p (fun _ : Fin 1 => .projection (2 : Fin 3))) out ![a,b,c])) := by
  apply compositionValue p (fun _ : Fin 1 => .projection (2 : Fin 3)) out ![a,b,c] ![c] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (2 : Fin 3) ![a,b,c]

/-- The exact reorder selector is indexed by Fin 1. It is propositionally
equal to the constant selector of rawCall, but these ASTs are not defeq. -/
private theorem reorderedThirdReport (p : Program 1) (out a b c : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p out c))) :
    Nonempty (Derivation body Γ (programGraph (reorder p (![2] : Fin 1 → Fin 3)) out ![a,b,c])) := by
  apply compositionValue p (fun i : Fin 1 => .projection ((![2] : Fin 1 → Fin 3) i))
    out ![a,b,c] ![c] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (2 : Fin 3) ![a,b,c]

theorem exact_ObservedSelectedTerms (d H K maxNumeral state vertices args : OTerm α)
    (actual : Nonempty (Derivation body Γ (observed d H K maxNumeral state vertices args))) :
    Nonempty (Derivation body Γ (termsReport vertices d H K maxNumeral)) := by
  obtain ⟨o⟩ := actual
  let xs := grammarTape d H K maxNumeral
  apply compositionValue ID1Completion.InternalUnpair.left (fun _ : Fin 1 => selectedGrammar)
    vertices xs ![state] ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight o)⟩
  intro i
  obtain rfl := Fin.eq_zero i
  exact ⟨Derivation.conjunctionLeft o⟩

theorem exact_OpenSelectedGrammarOption (H K m depth maxNumeral vertices : OTerm α)
    (pair : Nonempty (Derivation body Γ
      (programGraph ID1Completion.InternalPairing.pairing m ![depth,maxNumeral])))
    (terms : Nonempty (Derivation body Γ (termsReport vertices depth H K maxNumeral))) :
    Nonempty (Derivation body Γ
      (programGraph selectedGrammarOption (suc vertices) ![H,K,m])) := by
  obtain ⟨inverse⟩ := actualOriginalGeneratedCodeInverse body α m depth maxNumeral
  obtain ⟨pair⟩ := pair
  have fields := Derivation.implicationElimination (weakenClosed inverse Γ) pair
  let xs : Fin 3 → OTerm α := ![H,K,m]
  let left : Program 3 := reorder ID1Completion.InternalUnpair.left ![2]
  let right : Program 3 := reorder ID1Completion.InternalUnpair.right ![2]
  let parts : Fin 4 → Program 3 := ![left,.projection 0,.projection 1,right]
  have head : Nonempty (Derivation body Γ (programGraph left depth xs)) :=
    reorderedThirdReport ID1Completion.InternalUnpair.left depth H K m
      ⟨Derivation.conjunctionLeft fields⟩
  have last : Nonempty (Derivation body Γ (programGraph right maxNumeral xs)) :=
    reorderedThirdReport ID1Completion.InternalUnpair.right maxNumeral H K m
      ⟨Derivation.conjunctionRight fields⟩
  have core : Nonempty (Derivation body Γ
      (programGraph termListAtMeasure vertices xs)) := by
    apply compositionValue selectedTerms parts vertices xs ![depth,H,K,maxNumeral] terms
    intro i
    exact Fin.cases head (Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases last (fun j => Fin.elim0 j)))) i
  apply compositionValue (.succ : Program 1) (fun _ : Fin 1 => termListAtMeasure)
    (suc vertices) xs ![vertices] (successorValue ![vertices])
  intro i
  obtain rfl := Fin.eq_zero i
  exact core

/-- The physical original option and scratch share the same genuine
selected term report, at the original seed and literal settings. -/
theorem exact_OpenSelectedGrammarFactoredScratch (V M : Program 1) (s : Settings)
    (m depth maxNumeral vertices seed : OTerm α)
    (valid : Nonempty (Derivation body Γ (unary V (suc z) seed)))
    (measure : Nonempty (Derivation body Γ (unary M m seed)))
    (pair : Nonempty (Derivation body Γ
      (programGraph ID1Completion.InternalPairing.pairing m ![depth,maxNumeral])))
    (terms : Nonempty (Derivation body Γ
      (termsReport vertices depth (headsTerm s α) (typesTerm s α) maxNumeral))) :
    let C := factoredCover V M selectedGrammarOption
    Nonempty (Derivation body Γ (unary (coverOption C s) (suc vertices) seed)) ∧
    Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed)) := by
  let G := selectedGrammarOption
  let C := factoredCover V M G
  let H := headsTerm s α
  let K := typesTerm s α
  let xs := callbackTape s seed
  let parts : Fin 3 → Program 3 :=
    Fin.cons (.projection 0) (Fin.cons (.projection 1) (Fin.cons (rawCall M) Fin.elim0))
  have ready : Nonempty (Derivation body Γ (programGraph (generatorCall M G) (suc vertices) xs)) := by
    apply compositionValue G parts (suc vertices) xs ![H,K,m]
      (exact_OpenSelectedGrammarOption H K m depth maxNumeral vertices pair terms)
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (thirdReport M m H K seed measure) (fun j => Fin.elim0 j))) i
  have callback : Nonempty (Derivation body Γ (callbackAt C s (suc vertices) seed)) :=
    successorBranchIntro (rawCall V) (constantZero 3) (generatorCall M G) (suc vertices) z
      xs (thirdReport V (suc z) H K seed valid) ready
  have option := optionFromCallback C s (suc vertices) seed callback
  exact ⟨option,scratchSuccessor C s vertices seed option⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionOpenProof
