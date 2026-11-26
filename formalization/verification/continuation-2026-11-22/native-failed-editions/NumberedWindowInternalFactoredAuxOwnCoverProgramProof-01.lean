module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverProgramProof
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
open NumberedWindowInternalCoverGrammarStageTargets (grammarTerms stageGenerator termsGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets

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

private theorem generated (P : Program 5) (A : Program 2) (s : Settings)
    (m depth maxNumeral vertices : OTerm α)
    (pair : Nonempty (Derivation body Γ (measurePair m depth maxNumeral)))
    (terms : Nonempty (Derivation body Γ
      (termsGraph P A vertices (suc depth) (headsTerm s α) (typesTerm s α) maxNumeral))) :
    Nonempty (Derivation body Γ
      (programGraph (stageGenerator P A) (suc vertices) ![headsTerm s α,typesTerm s α,m])) := by
  obtain ⟨inverse⟩ := actualOriginalGeneratedCodeInverse body α m (suc depth) maxNumeral
  obtain ⟨pair⟩ := pair
  have fields := Derivation.implicationElimination (weakenClosed inverse Γ) pair
  let H := headsTerm s α
  let K := typesTerm s α
  let xs : Fin 3 → OTerm α := ![H,K,m]
  let left : Program 3 := reorder ID1Completion.InternalUnpair.left ![2]
  let right : Program 3 := reorder ID1Completion.InternalUnpair.right ![2]
  let parts : Fin 4 → Program 3 := ![left,.projection 0,.projection 1,right]
  have head : Nonempty (Derivation body Γ (programGraph left (suc depth) xs)) :=
    thirdReport ID1Completion.InternalUnpair.left (suc depth) H K m
      ⟨Derivation.conjunctionLeft fields⟩
  have last : Nonempty (Derivation body Γ (programGraph right maxNumeral xs)) :=
    thirdReport ID1Completion.InternalUnpair.right maxNumeral H K m
      ⟨Derivation.conjunctionRight fields⟩
  have core : Nonempty (Derivation body Γ
      (programGraph (.composition (grammarTerms P A) parts) vertices xs)) := by
    apply compositionValue (grammarTerms P A) parts vertices xs ![suc depth,H,K,maxNumeral] terms
    intro i
    exact Fin.cases head (Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 1 xs) (Fin.cases last (fun j => Fin.elim0 j)))) i
  apply compositionValue (.succ : Program 1) (fun _ : Fin 1 => .composition (grammarTerms P A) parts)
    (suc vertices) xs ![vertices] (successorValue ![vertices])
  intro i
  obtain rfl := Fin.eq_zero i
  exact core

/-- The successor term list, option payload and physical scratch output
share exactly one report; the cover does not rerun a different grammar. -/
theorem actualScratch (V M : Program 1) (P : Program 5) (A : Program 2) (s : Settings)
    (m depth maxNumeral vertices seed : OTerm α)
    (valid : Nonempty (Derivation body Γ (unary V (suc z) seed)))
    (measure : Nonempty (Derivation body Γ (unary M m seed)))
    (pair : Nonempty (Derivation body Γ (measurePair m depth maxNumeral)))
    (terms : Nonempty (Derivation body Γ
      (termsGraph P A vertices (suc depth) (headsTerm s α) (typesTerm s α) maxNumeral))) :
    Nonempty (Derivation body Γ (unary (coverOption (installedCover V M P A) s) (suc vertices) seed)) ∧
    Nonempty (Derivation body Γ (unary (scratchVertices (installedCover V M P A) s) vertices seed)) := by
  let G := stageGenerator P A
  let H := headsTerm s α
  let K := typesTerm s α
  let xs := callbackTape s seed
  let parts : Fin 3 → Program 3 :=
    Fin.cons (.projection 0) (Fin.cons (.projection 1) (Fin.cons (rawCall M) Fin.elim0))
  have ready : Nonempty (Derivation body Γ (programGraph (generatorCall M G) (suc vertices) xs)) := by
    apply compositionValue G parts (suc vertices) xs ![H,K,m]
      (generated P A s m depth maxNumeral vertices pair terms)
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (thirdReport M m H K seed measure) (fun j => Fin.elim0 j))) i
  have callback : Nonempty (Derivation body Γ (callbackAt (installedCover V M P A) s (suc vertices) seed)) :=
    successorBranchIntro (rawCall V) (constantZero 3) (generatorCall M G) (suc vertices) z
      xs (thirdReport V (suc z) H K seed valid) ready
  have option := optionFromCallback (installedCover V M P A) s (suc vertices) seed callback
  exact ⟨option,scratchSuccessor (installedCover V M P A) s vertices seed option⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverProgramProof
