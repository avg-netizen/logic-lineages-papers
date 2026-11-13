module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPriorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherTypeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherTransitionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalParameterizedBoundedDescentNormalizer
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem branchSame {n : Nat} (control a b : Program n) (output : OTerm alpha) (xs : Fin n → OTerm alpha)
 (ha : Nonempty (Derivation body Delta (programGraph a output xs)))
 (hb : Nonempty (Derivation body Delta (programGraph b output xs))) :
 Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch control a b) output xs)) := by
 apply programCases control xs _
 intro beta j Theta value hj hc
 have ha' := renameInto ha j Theta hj
 have hb' := renameInto hb j Theta hj
 rw [programRename] at ha' hb' ⊢
 apply formulaCases (eqn value z)
 · exact branchValue control a b (output.relabel j) value (output.relabel j) (output.relabel j)
     (fun i => (xs i).relabel j) (withHyp hc _) (withHyp ha' _) (withHyp hb' _)
     (InternalControlGraphProof.conditionalAtZero value _ _ ⟨Derivation.hypothesis List.mem_cons_self⟩)
 · exact branchValue control a b (output.relabel j) value (output.relabel j) (output.relabel j)
     (fun i => (xs i).relabel j) (withHyp hc _) (withHyp ha' _) (withHyp hb' _)
     (InternalControlGraphProof.conditionalAtNonzero value _ _ ⟨Derivation.hypothesis List.mem_cons_self⟩)

theorem chooseCandidate (V : Program 2) (candidate input typ parameter : OTerm alpha)
 (hbound : Nonempty (Derivation body Delta (atMost candidate input)))
 (hv : Nonempty (Derivation body Delta (graph2 V (suc z) candidate parameter)))
 (hti : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (htc : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ candidate))) :
 Nonempty (Derivation body Delta (programGraph (choose V) candidate ![candidate,input,parameter])) := by
 apply InternalOriginalPairingOrderArithmeticProof.weakCases candidate input _ hbound
 · let A := InternalOriginalOrderSyntaxProof.ltF candidate input
   let xs : Fin 3 → OTerm alpha := ![candidate,input,parameter]
   have hlt : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hl := binaryValue InternalLessThan.ltTest (.projection 0) (.projection 1) (suc z) candidate input xs
     (InternalLessThanSupportProof.acceptOfLess candidate input hlt)
     (projectionValue 0 xs) (projectionValue 1 xs)
   have hvalid := binaryValue V (.projection 0) (.projection 2) (suc z) candidate parameter xs
     (withHyp hv A) (projectionValue 0 xs) (projectionValue 2 xs)
   have hleft := sameAccept (.composition InternalUnpair.left (fun _ : Fin 1 => .projection 0))
     (.composition InternalUnpair.left (fun _ : Fin 1 => .projection 1)) typ xs
     (unaryValue InternalUnpair.left (.projection 0) typ candidate xs (withHyp htc A) (projectionValue 0 xs))
     (unaryValue InternalUnpair.left (.projection 1) typ input xs (withHyp hti A) (projectionValue 1 xs))
   have hg := conjunctionAccept candidateLess (InternalAcceptance.conjunction (candidateValid V) sameLeft) xs hl
     (conjunctionAccept (candidateValid V) sameLeft xs hvalid hleft)
   exact successorBranchIntro (guard V) (.projection 1) (.projection 0) candidate z xs hg (projectionValue 0 xs)
 · let A := eqn candidate input
   let xs : Fin 3 → OTerm alpha := ![candidate,input,parameter]
   have he : Nonempty (Derivation body (A :: Delta) (eqn input candidate)) :=
     ⟨InternalTagArithmeticSupportProof.symm (Derivation.hypothesis List.mem_cons_self)⟩
   have hi := outputTransport (.projection (1 : Fin 3)) input candidate xs he (projectionValue 1 xs)
   exact branchSame (guard V) (.projection 1) (.projection 0) candidate xs hi (projectionValue 0 xs)

theorem transitionCandidate (R V : Program 2) (candidate input typ parameter : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (graph2 R candidate input parameter)))
 (hbound : Nonempty (Derivation body Delta (atMost candidate input)))
 (hv : Nonempty (Derivation body Delta (graph2 V (suc z) candidate parameter)))
 (hti : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (htc : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ candidate))) :
 Nonempty (Derivation body Delta (transitionGraph R V candidate input parameter)) := by
 have hc := chooseCandidate V candidate input typ parameter hbound hv hti htc
 apply compositionValue (choose V) (Fin.cons R (Fin.cons (.projection 0) (Fin.cons (.projection 1) Fin.elim0)))
   candidate (Fin.cons input (Fin.cons parameter Fin.elim0))
   (Fin.cons candidate (Fin.cons input (Fin.cons parameter Fin.elim0))) hc
 intro i
 refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun x => Fin.elim0 x) l) k) i
 · exact hr
 · exact projectionValue 0 (Fin.cons input (Fin.cons parameter Fin.elim0))
 · change Nonempty (Derivation body Delta (programGraph (.projection (1 : Fin 2)) parameter
     (Fin.cons input (Fin.cons parameter Fin.elim0))))
   exact projectionValue 1 (Fin.cons input (Fin.cons parameter Fin.elim0))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherTransitionProof
