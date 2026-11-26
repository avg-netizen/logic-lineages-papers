module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorSplitProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPairing (pairing)
open ID1Completion.InternalUnpair (left right)
open ID1Completion.InternalUnpairProof (actualOriginalGeneratedCodeInverse)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverSelectedSuccessorTargets
open NumberedWindowInternalCoverSelectedSuccessorOpenCoreProof

attribute [local irreducible] programGraph

private theorem atPair {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (state outTerms outArgs H K ids ts args : OTerm α) (ys : Fin 2 → OTerm α)
    (paired : Nonempty (Derivation body Γ (programGraph pairing state ys)))
    (terms : Nonempty (Derivation body Γ (stepReport termsPart (ys 0) H K ids ts args)))
    (arguments : Nonempty (Derivation body Γ (stepReport argsPart (ys 1) H K ids ts args)))
    (seenTerms : Nonempty (Derivation body Γ (termProjection outTerms state)))
    (seenArgs : Nonempty (Derivation body Γ (argsProjection outArgs state))) :
    Nonempty (Derivation body Γ
      (stepReport termsPart outTerms H K ids ts args ⊓ stepReport argsPart outArgs H K ids ts args)) := by
  have tape : ys = Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  have p : Nonempty (Derivation body Γ (programGraph pairing state
      (Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0)))) := by
    rw [← tape]
    exact paired
  obtain ⟨p⟩ := p
  obtain ⟨inverse⟩ := actualOriginalGeneratedCodeInverse body α state (ys 0) (ys 1)
  have split := Derivation.implicationElimination (weakenClosed inverse Γ) p
  have oneTape : (Fin.cons state Fin.elim0 : Fin 1 → OTerm α) = ![state] := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  have tRead := Derivation.conjunctionLeft split
  have aRead := Derivation.conjunctionRight split
  rw [oneTape] at tRead aRead
  have sameTerms := valueUnique left (ys 0) outTerms ![state] ⟨tRead⟩ seenTerms
  have sameArgs := valueUnique right (ys 1) outArgs ![state] ⟨aRead⟩ seenArgs
  let xs := stepTape H K ids ts args
  obtain ⟨t⟩ := outputTransport termsPart (ys 0) outTerms xs sameTerms terms
  obtain ⟨a⟩ := outputTransport argsPart (ys 1) outArgs xs sameArgs arguments
  exact ⟨Derivation.conjunctionIntroduction t a⟩

theorem exact_OpenSelectedCoverSuccessorSplit : ExactOpenSelectedCoverSuccessorSplit := by
  intro body α Γ state outTerms outArgs H K ids ts args packed tRead aRead
  let sels : Fin 2 → Program 5 := Fin.cons termsPart (Fin.cons argsPart Fin.elim0)
  let goal := stepReport termsPart outTerms H K ids ts args ⊓ stepReport argsPart outArgs H K ids ts args
  apply programCompositionCases pairing sels state (stepTape H K ids ts args) goal packed
  intro β j ys Δ keep terminal children
  rw [conjunctionRename,reportRename,reportRename]
  have a := renameInto aRead j Δ keep
  have t := renameInto tRead j Δ keep
  simp only [termProjection,argsProjection,unaryRename] at t a
  have partsT := children 0
  have partsA := children 1
  change Nonempty (Derivation body Δ (programGraph termsPart (ys 0)
    (fun i => (stepTape H K ids ts args i).relabel j))) at partsT
  change Nonempty (Derivation body Δ (programGraph argsPart (ys 1)
    (fun i => (stepTape H K ids ts args i).relabel j))) at partsA
  rw [tapeRename] at partsT partsA
  exact atPair (state.relabel j) (outTerms.relabel j) (outArgs.relabel j)
    (H.relabel j) (K.relabel j) (ids.relabel j) (ts.relabel j) (args.relabel j)
    ys terminal partsT partsA t a

#print axioms exact_OpenSelectedCoverSuccessorSplit

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorSplitProof
