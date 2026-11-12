module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionMeasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Query the original total numeric programs inside the derivation. Their
outputs are not supplied as an external termination or source oracle. -/
theorem measuresCases (first second gamma : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
   (firstCount secondCount count : OTerm beta),
   (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 OriginalStructuralNodeSize.raw firstCount (first.relabel rho))) →
   Nonempty (Derivation body Theta (graph1 OriginalStructuralNodeSize.raw secondCount (second.relabel rho))) →
   Nonempty (Derivation body Theta (OriginalContextInsertion.lengthGraph count (gamma.relabel rho))) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let qs : Fin 3 → Program 3 :=
   ![.composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => .projection 0),
     .composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => .projection 1),
     .composition OriginalContextInsertion.length (fun _ : Fin 1 => .projection 2)]
 let xs : Fin 3 → OTerm alpha := Fin.cons first (Fin.cons second (Fin.cons gamma Fin.elim0))
 apply queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 3 → OTerm beta := Fin.cons (first.relabel rho)
   (Fin.cons (second.relabel rho) (Fin.cons (gamma.relabel rho) Fin.elim0))
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hq
 exact next beta rho Theta (ys 0) (ys 1) (ys 2) hrho
   (unaryRecover OriginalStructuralNodeSize.raw (.projection 0) (ys 0) (first.relabel rho) xx (hq 0) (projectionValue 0 xx))
   (unaryRecover OriginalStructuralNodeSize.raw (.projection 1) (ys 1) (second.relabel rho) xx (hq 1) (projectionValue 1 xx))
   (unaryRecover OriginalContextInsertion.length (.projection 2) (ys 2) (gamma.relabel rho) xx (hq 2) (projectionValue 2 xx))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionMeasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionMeasureProof
