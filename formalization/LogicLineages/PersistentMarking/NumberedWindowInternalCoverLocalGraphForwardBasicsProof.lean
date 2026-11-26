module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardBasicsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (renameIdentity)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaPositive)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalCoverLocalGraphForwardTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem tapeRefl {n : Nat} (P : Program n) (xs : Fin n → OTerm α) :
    TapeForward P P body Γ xs := fun _ _ _ _ _ actual => actual

theorem applyTape {n : Nat} (P Q : Program n) (xs : Fin n → OTerm α) (out : OTerm α)
    (ok : TapeForward P Q body Γ xs)
    (actual : Nonempty (Derivation body Γ (programGraph P out xs))) :
    Nonempty (Derivation body Γ (programGraph Q out xs)) := by
  have same : (fun i : Fin n => (xs i).relabel id) = xs := funext fun i => Term.relabel_id (xs i)
  have keep (f : Formula α) (h : f ∈ Γ) : f.relabel id ∈ Γ := by rw [renameIdentity]; exact h
  apply Eq.mp (congrArg (fun tape => Nonempty (Derivation body Γ (programGraph Q out tape))) same)
  exact ok α id Γ out keep (Eq.mpr (congrArg (fun tape =>
    Nonempty (Derivation body Γ (programGraph P out tape))) same) actual)

theorem exact_OpenCoverLambdaBaseTapeForward : ExactOpenCoverLambdaBaseTapeForward := by
  intro s B T body α Γ ctx raw rejected β j Δ out keep actual
  have guard := renameInto rejected j Δ keep
  simp only [unaryRename,zRelabel] at guard
  rw [binaryInputsRename] at actual ⊢
  let c := ctx.relabel j
  let r := raw.relabel j
  exact zeroBranchIntro (onRaw (header 2 2)) B (lambdaPositive s B T) out ![c,r]
    (liftRawReport (header 2 2) c r z guard) actual

#print axioms applyTape
#print axioms exact_OpenCoverLambdaBaseTapeForward

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardBasicsProof
