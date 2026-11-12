module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsAccumulatorQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem ternaryCases (P : Program 3) (a b c : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (value : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph3 P value (a.relabel j) (b.relabel j) (c.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases P (Fin.cons a (Fin.cons b (Fin.cons c Fin.elim0))) psi
 intro beta j Theta value hj hv
 have he : (fun i : Fin 3 => ((Fin.cons a (Fin.cons b (Fin.cons c Fin.elim0)) : Fin 3 → OTerm alpha) i).relabel j) =
     Fin.cons (a.relabel j) (Fin.cons (b.relabel j) (Fin.cons (c.relabel j) Fin.elim0)) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [he] at hv
 exact next beta j Theta value hj hv

theorem pairCases (state : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (left right : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (state.relabel j) left right)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases ![InternalUnpair.left,InternalUnpair.right]
   (Fin.cons state Fin.elim0) psi
 intro beta j values Theta hj hv
 have he : (fun i : Fin 1 => ((Fin.cons state Fin.elim0 : Fin 1 → OTerm alpha) i).relabel j) =
     Fin.cons (state.relabel j) Fin.elim0 := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 have hl := hv 0
 have hr := hv 1
 rw [he] at hl hr
 simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hl hr
 exact next beta j Theta (values 0) (values 1) hj
   (reconstructPair (state.relabel j) (values 0) (values 1) hl hr)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsWalkQueryProof
