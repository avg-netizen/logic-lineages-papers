module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageOpenStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue programRename valueUnique outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases compositionRecover)
open ID1Completion.InternalUnpairProof (actualOriginalGeneratedCodeInverse)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary auxApplications)
open NumberedWindowInternalCoverAuxApplicationsChecks (exact_OpenAuxApplicationsMember)
open NumberedWindowInternalCoverGrammarStageTargets

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem binaryCases {n : Nat} (P : Program 2) (A B : Program n) (out : OTerm α) (xs : Fin n → OTerm α)
    (goal : Formula α) (run : Nonempty (Derivation body Γ (programGraph (binary P A B) out xs)))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (x y : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (programGraph A x (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Δ (programGraph B y (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Δ (programGraph P (out.relabel j) ![x,y])) →
      Nonempty (Derivation body Δ (goal.relabel j))) : Nonempty (Derivation body Γ goal) := by
  let calls : Fin 2 → Program n := Fin.cons A (Fin.cons B Fin.elim0)
  have process (β : Type) (j : α → β) (ys : Fin 2 → OTerm β) (Δ : List (Formula β)) (hJ : ∀ p ∈ Γ, p.relabel j ∈ Δ)
      (runP : Nonempty (Derivation body Δ (programGraph P (out.relabel j) ys)))
      (components : ∀ i, Nonempty (Derivation body Δ (programGraph (calls i) (ys i) (fun k => (xs k).relabel j)))) :
      Nonempty (Derivation body Δ (goal.relabel j)) := by
    have tape : ys = ![ys 0,ys 1] := by
      funext i
      refine Fin.cases rfl (fun ii => ?_) i
      obtain rfl := Fin.eq_zero ii
      rfl
    rw [tape] at runP
    exact use β j Δ (ys 0) (ys 1) hJ (components 0) (components 1) runP
  exact programCompositionCases P calls out xs goal run process

theorem completedTerms (nonAux : Program 5) (nextArgs : Program 2) (state out : OTerm α) (xs : Fin 5 → OTerm α)
    (updated : Nonempty (Derivation body Γ (programGraph (grammarStep nonAux nextArgs) state xs)))
    (projection : Nonempty (Derivation body Γ (unary ID1Completion.InternalUnpair.left out state))) :
    Nonempty (Derivation body Γ (programGraph (termsAtStep nonAux) out xs)) := by
  apply binaryCases ID1Completion.InternalPairing.pairing (termsAtStep nonAux) (binary nextArgs termsBefore argsBefore) state xs _ updated
  intro β j Δ terms args keep termsRun _ paired
  rw [programRename]
  have actual := renameInto projection j Δ keep
  rw [unaryRename] at actual
  obtain ⟨law⟩ := actualOriginalGeneratedCodeInverse body β (state.relabel j) terms args
  obtain ⟨hp⟩ := paired
  have expected := Derivation.conjunctionLeft (Derivation.implicationElimination (weakenClosed law Δ) hp)
  have same := valueUnique ID1Completion.InternalUnpair.left terms (out.relabel j) ![state.relabel j] ⟨expected⟩ actual
  exact outputTransport (termsAtStep nonAux) terms (out.relabel j) (fun i => (xs i).relabel j) same termsRun

theorem stepMember (nonAux : Program 5) (out depth old H K maxNumeral prev dom cod fn arg : OTerm α)
    (before : Nonempty (Derivation body Γ (unary ID1Completion.InternalUnpair.left prev old)))
    (step : Nonempty (Derivation body Γ (programGraph (termsAtStep nonAux) out ![depth,old,H,K,maxNumeral])))
    (domIn : Nonempty (Derivation body Γ (memberGraph K dom)))
    (codIn : Nonempty (Derivation body Γ (memberGraph K cod)))
    (fnIn : Nonempty (Derivation body Γ (memberGraph prev fn)))
    (argIn : Nonempty (Derivation body Γ (memberGraph prev arg))) :
    Nonempty (Derivation body Γ (memberGraph out (auxiliaryTerm dom cod fn arg))) := by
  let xs : Fin 5 → OTerm α := ![depth,old,H,K,maxNumeral]
  apply binaryCases append (prefixAt nonAux) applicationsAt out xs _ step
  intro β j Δ pref applications keep _ computed appended
  rw [graphRename,auxiliaryRename]
  have prior := renameInto before j Δ keep
  rw [unaryRename] at prior
  let ys : Fin 5 → OTerm β := fun i => (xs i).relabel j
  have access : Nonempty (Derivation body Δ (programGraph termsBefore (prev.relabel j) ys)) := by
    apply ID1Completion.InternalControlGraphSupportProof.compositionValue ID1Completion.InternalUnpair.left
      (fun i => .projection ((![1] : Fin 1 → Fin 5) i)) (prev.relabel j) ys ![old.relabel j] prior
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 ys
  have output : Nonempty (Derivation body Δ (programGraph auxApplications applications ![K.relabel j,prev.relabel j])) := by
    apply compositionRecover auxApplications (Fin.cons (.projection 3) (Fin.cons termsBefore Fin.elim0))
      applications ys ![K.relabel j,prev.relabel j] computed
    intro i
    exact Fin.cases (projectionValue 3 ys) (Fin.cases access (fun j => Fin.elim0 j)) i
  have d := renameInto domIn j Δ keep
  have c := renameInto codIn j Δ keep
  have f := renameInto fnIn j Δ keep
  have a := renameInto argIn j Δ keep
  simp only [graphRename] at d c f a
  have present := exact_OpenAuxApplicationsMember body β Δ (K.relabel j) (prev.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) applications d c f a output
  exact PrimaryEdgeInclusion.AppendRightProof.appendPreservation pref applications (out.relabel j)
    (auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)) appended present

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageOpenStepProof
