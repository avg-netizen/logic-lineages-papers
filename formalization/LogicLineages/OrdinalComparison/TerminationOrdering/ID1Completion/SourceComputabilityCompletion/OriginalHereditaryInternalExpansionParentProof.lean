module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionDecorationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionParentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransportInternalParserSupportProof (selectorPair)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalHereditaryAnnotatedExpansion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem coordinateCases (parent input : OTerm alpha) (psi : Formula alpha)
 (hi : Nonempty (Derivation body Delta (graph1 (leftOf originalJob) input parent)))
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
   (parentRaw parameter window gamma : OTerm beta), (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 forget parentRaw (parent.relabel rho))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing parentRaw (input.relabel rho) parameter)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing parameter window gamma)) →
   Nonempty (Derivation body Theta (graph1 (rightOf originalJob) parameter (parent.relabel rho))) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let qs : Fin 4 → Program 1 := ![originalJob,rightOf originalJob,leftOf (rightOf originalJob),rightOf (rightOf originalJob)]
 let xs : Fin 1 → OTerm alpha := Fin.cons parent Fin.elim0
 apply queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 1 → OTerm beta := Fin.cons (parent.relabel rho) Fin.elim0
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hi' := renameInto hi rho Theta hrho
 rw [graph1Rename] at hi'
 exact next beta rho Theta (ys 0) (ys 1) (ys 2) (ys 3) hrho (hq 0)
   (selectorPair originalJob (ys 0) (input.relabel rho) (ys 1) xx (hq 0) hi' (hq 1))
   (selectorPair (rightOf originalJob) (ys 1) (ys 2) (ys 3) xx (hq 1) (hq 2) (hq 3)) (hq 1)

/-- Open the literal annotated expansion into its raw expansion and exact
annotation scan without decoding the job or importing a native relation. -/
theorem expansionCases (parent output : OTerm alpha) (psi : Formula alpha)
 (he : Nonempty (Derivation body Delta (graph1 expansion output parent)))
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
   (role typ parentRaw input parameter window gamma rawJobs : OTerm beta),
   (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 forget parentRaw (parent.relabel rho))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing parentRaw input parameter)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing parameter window gamma)) →
   Nonempty (Derivation body Theta (graph2 OriginalHereditaryExpansion.expansion rawJobs input parameter)) →
   Nonempty (Derivation body Theta (graph4 decorateAll (output.relabel rho) role typ input rawJobs)) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons parent Fin.elim0
 apply programCompositionCases decorateAll
   ![leftOf (.projection 0),leftOf (rightOf (.projection 0)),leftOf originalJob,
     .composition OriginalHereditaryExpansion.expansion ![leftOf originalJob,rightOf originalJob] ] output xs psi he
 intro beta rho ys Theta hrho hdec hs
 let xx : Fin 1 → OTerm beta := Fin.cons (parent.relabel rho) Fin.elim0
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hs
 have hd : Nonempty (Derivation body Theta (graph4 decorateAll (output.relabel rho) (ys 0) (ys 1) (ys 2) (ys 3))) := by
   have ht : Fin.cons (ys 0) (Fin.cons (ys 1) (Fin.cons (ys 2) (Fin.cons (ys 3) Fin.elim0))) = ys := by
     funext i
     exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
   simpa only [graph4,ht] using hdec
 apply coordinateCases (parent.relabel rho) (ys 2) (psi.relabel rho) (hs 2)
 intro gammaType sigma Xi parentRaw parameter window context hsigma hforget hraw hparam hparameter
 have hd' := renameInto hd sigma Xi hsigma
 rw [graph4Rename] at hd'
 have hj := renameInto (hs 3) sigma Xi hsigma
 have hi := renameInto (hs 2) sigma Xi hsigma
 simp only [programRename] at hj hi
 let xxx : Fin 1 → OTerm gammaType := Fin.cons ((parent.relabel rho).relabel sigma) Fin.elim0
 have hxx : (fun i => (xx i).relabel sigma) = xxx := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hxx] at hj hi
 have hrawExpansion := binaryRecover OriginalHereditaryExpansion.expansion (leftOf originalJob) (rightOf originalJob)
   ((ys 3).relabel sigma) ((ys 2).relabel sigma) parameter xxx hj hi hparameter
 have hinc : ∀ f ∈ Delta, f.relabel (sigma ∘ rho) ∈ Xi := by
   intro f hf
   simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hsigma (f.relabel rho) (hrho f hf)
 have hout := next gammaType (sigma ∘ rho) Xi ((ys 0).relabel sigma) ((ys 1).relabel sigma)
   parentRaw ((ys 2).relabel sigma) parameter window context ((ys 3).relabel sigma) hinc
   (by simpa only [Term.relabel_relabel] using hforget) hraw hparam hrawExpansion
   (by simpa only [Term.relabel_relabel] using hd')
 simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hout
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionParentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionParentProof
