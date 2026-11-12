module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionStateSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight)
open OriginalHereditaryLambda (atState stateSource stateTarget stateCertificate stateParameter)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem withHyp {phi : Formula alpha}
 (h : Nonempty (Derivation body Delta phi)) (p : Formula alpha) :
 Nonempty (Derivation body (p :: Delta) phi) := by
 obtain ⟨h⟩ := h
 exact ⟨InternalBetaTotalityProof.addHyp h p⟩

/-- A literal graph implication lifts through the unchanged four state
selectors. No external interpretation of the state is used. -/
theorem atStateFactor (p q : Program 4)
 (factor : ∀ (beta : Type) (Theta : List (Formula beta)) (xs : Fin 4 → OTerm beta),
  Nonempty (Derivation body Theta (programGraph p (suc z) xs)) →
  Nonempty (Derivation body Theta (programGraph q (suc z) xs)))
 (state : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph1 (atState p) (suc z) state))) :
 Nonempty (Derivation body Delta (graph1 (atState q) (suc z) state)) := by
 apply programCompositionCases p ![stateSource,stateTarget,stateCertificate,stateParameter]
  (suc z) (Fin.cons state Fin.elim0) _ h
 intro beta rho ys Theta hrho hp hg
 simp only [graph1Rename,sucRelabel,zRelabel]
 simp only [sucRelabel,zRelabel] at hp
 simp only [consTermRename,emptyRename] at hg
 exact compositionValue q ![stateSource,stateTarget,stateCertificate,stateParameter]
  (suc z) (Fin.cons (state.relabel rho) Fin.elim0) ys (factor beta Theta ys hp) hg

/-- Both accepted factors are recovered at one actual state, sharing the
same internally queried selectors. -/
theorem atStateConjunctionRecover (p q : Program 4) (state : OTerm alpha)
 (h : Nonempty (Derivation body Delta
  (graph1 (atState (InternalAcceptance.conjunction p q)) (suc z) state))) :
 Nonempty (Derivation body Delta
  (graph1 (atState p) (suc z) state ⊓ graph1 (atState q) (suc z) state)) := by
 apply programCompositionCases (InternalAcceptance.conjunction p q)
  ![stateSource,stateTarget,stateCertificate,stateParameter]
  (suc z) (Fin.cons state Fin.elim0) _ h
 intro beta rho ys Theta hrho hp hg
 change Nonempty (Derivation body Theta
  ((graph1 (atState p) (suc z) state).relabel rho ⊓
   (graph1 (atState q) (suc z) state).relabel rho))
 simp only [graph1Rename,sucRelabel,zRelabel]
 simp only [sucRelabel,zRelabel] at hp
 simp only [consTermRename,emptyRename] at hg
 have hh := conjunctionRecover p q ys hp
 exact combine
  (compositionValue p ![stateSource,stateTarget,stateCertificate,stateParameter]
   (suc z) (Fin.cons (state.relabel rho) Fin.elim0) ys (projectLeft hh) hg)
  (compositionValue q ![stateSource,stateTarget,stateCertificate,stateParameter]
   (suc z) (Fin.cons (state.relabel rho) Fin.elim0) ys (projectRight hh) hg)

/-- The original conjunction is reconstructed using the identical selector
tuple for both original Programs. -/
theorem atStateConjunctionAccept (p q : Program 4) (state : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 (atState p) (suc z) state)))
 (hq : Nonempty (Derivation body Delta (graph1 (atState q) (suc z) state))) :
 Nonempty (Derivation body Delta
  (graph1 (atState (InternalAcceptance.conjunction p q)) (suc z) state)) := by
 apply programCompositionCases p ![stateSource,stateTarget,stateCertificate,stateParameter]
  (suc z) (Fin.cons state Fin.elim0) _ hp
 intro beta rho ys Theta hrho hp' hg
 simp only [graph1Rename,sucRelabel,zRelabel]
 simp only [sucRelabel,zRelabel] at hp'
 simp only [consTermRename,emptyRename] at hg
 have hq' := renameInto hq rho Theta hrho
 simp only [graph1Rename,sucRelabel,zRelabel] at hq'
 have hinner := compositionRecover q ![stateSource,stateTarget,stateCertificate,stateParameter]
  (suc z) (Fin.cons (state.relabel rho) Fin.elim0) ys hq' hg
 exact compositionValue (InternalAcceptance.conjunction p q)
  ![stateSource,stateTarget,stateCertificate,stateParameter]
  (suc z) (Fin.cons (state.relabel rho) Fin.elim0) ys
  (conjunctionAccept p q ys hp' hinner) hg

/-- A graph with an absorbing zero input cannot have a nonzero output at
zero. This argument uses graph functionality in the original calculus. -/
theorem nonzeroInput (p : Program 1) (out state : OTerm alpha)
 (hz : Nonempty (Derivation body Delta (graph1 p z z)))
 (hp : Nonempty (Derivation body Delta (graph1 p out state)))
 (hn : Nonempty (Derivation body Delta (eqn out z).not)) :
 Nonempty (Derivation body Delta (eqn state z).not) := by
 let E := eqn state z
 have h0 := headTransport p out state z Fin.elim0
  (show Nonempty (Derivation body (E :: Delta) E) from
   ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hp E)
 obtain ⟨he⟩ := valueUnique p out z (Fin.cons z Fin.elim0) h0 (withHyp hz E)
 obtain ⟨hn⟩ := withHyp hn E
 exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn he)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionStateSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionStateSupportProof
