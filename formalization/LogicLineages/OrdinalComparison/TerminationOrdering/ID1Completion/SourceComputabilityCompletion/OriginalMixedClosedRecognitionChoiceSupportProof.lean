module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionStateSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionChoiceSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof
open InternalControlGraphChoiceProof (excludedMiddle)
open InternalBetaTotalityProof
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight)
open OriginalHereditaryLambda (atState)
open OriginalMixedClosedRecognitionStateSupportProof
open OriginalMixedDirectBottomTraceDescentProof (choice second secondRecover)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Priority-preserving simulation of a successful choice with a shared
leaf. The second branch retains the failed first test; its accepted old
leaf then excludes the first test under the weaker leaf as well. -/
theorem choiceFactor (g1 g2 p q : Program 4) (a1 a2 : Program 1)
 (factor : ∀ (beta : Type) (Theta : List (Formula beta)) (state : OTerm beta),
  Nonempty (Derivation body Theta (graph1 (atState p) (suc z) state)) →
  Nonempty (Derivation body Theta (graph1 (atState q) (suc z) state)))
 (state next : OTerm alpha)
 (hn : Nonempty (Derivation body Delta (eqn next z).not))
 (ht : Nonempty (Derivation body Delta
  (graph1 (choice (atState (InternalAcceptance.conjunction g1 p))
   (atState (InternalAcceptance.conjunction g2 p)) a1 a2) next state))) :
 Nonempty (Derivation body Delta
  (graph1 (choice (atState (InternalAcceptance.conjunction g1 q))
   (atState (InternalAcceptance.conjunction g2 q)) a1 a2) next state)) := by
 let c1 := atState (InternalAcceptance.conjunction g1 p)
 let c2 := atState (InternalAcceptance.conjunction g2 p)
 let d1 := atState (InternalAcceptance.conjunction g1 q)
 let d2 := atState (InternalAcceptance.conjunction g2 q)
 let P := graph1 c1 (suc z) state
 let result := graph1 (choice d1 d2 a1 a2) next state
 have hy : Nonempty (Derivation body (P :: Delta) result) := by
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
   ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hparts := atStateConjunctionRecover g1 p state hp
  have hnew := atStateConjunctionAccept g1 q state (projectLeft hparts)
   (factor alpha (P :: Delta) state (projectRight hparts))
  have ha := successorBranchElim (normalize c1) (second c2 a2) a1
   next z (Fin.cons state Fin.elim0)
   (normalizeAccept c1 (Fin.cons state Fin.elim0) hp) (withHyp ht P)
  exact successorBranchIntro (normalize d1) (second d2 a2) a1
   next z (Fin.cons state Fin.elim0)
   (normalizeAccept d1 (Fin.cons state Fin.elim0) hnew) ha
 have hno : Nonempty (Derivation body (P.not :: Delta) result) := by
  have hp : Nonempty (Derivation body (P.not :: Delta) P.not) :=
   ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := zeroBranchElim (normalize c1) (second c2 a2) a1
   next (Fin.cons state Fin.elim0)
   (normalizeReject c1 (Fin.cons state Fin.elim0) hp) (withHyp ht P.not)
  have hsecond := secondRecover c2 a2 state next (withHyp hn P.not) hs
  have hparts := atStateConjunctionRecover g2 p state (projectLeft hsecond)
  have hnew := atStateConjunctionAccept g2 q state (projectLeft hparts)
   (factor alpha (P.not :: Delta) state (projectRight hparts))
  have hreject : Nonempty (Derivation body (P.not :: Delta)
    (graph1 d1 (suc z) state).not) := by
   let R := graph1 d1 (suc z) state
   have hr : Nonempty (Derivation body (R :: P.not :: Delta) R) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hguard := projectLeft (atStateConjunctionRecover g1 q state hr)
   obtain ⟨hold⟩ := atStateConjunctionAccept g1 p state hguard
    (withHyp (projectRight hparts) R)
   obtain ⟨hnot⟩ := withHyp hp R
   exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hnot hold)⟩
  have hnewSecond := successorBranchIntro (normalize d2)
   (InternalAcceptance.constantZero 1) a2 next z (Fin.cons state Fin.elim0)
   (normalizeAccept d2 (Fin.cons state Fin.elim0) hnew) (projectRight hsecond)
  exact zeroBranchIntro (normalize d1) (second d2 a2) a1
   next (Fin.cons state Fin.elim0)
   (normalizeReject d1 (Fin.cons state Fin.elim0) hreject) hnewSecond
 obtain ⟨hy⟩ := hy
 obtain ⟨hno⟩ := hno
 exact ⟨disjunctionElimination (excludedMiddle P)
  (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionChoiceSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedRecognitionChoiceSupportProof
