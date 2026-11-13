module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionBase
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z emb eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalSourceInversionSupportProof (onEquality)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open VisitListCompletionDefinitions VisitListCompletionSyntax VisitListInductionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem completionTransport (R : Program 2) (size old new : OTerm alpha)
 (he : Nonempty (Derivation body Delta (eqn old new)))
 (hc : Nonempty (Derivation body Delta (Completion R size old))) :
 Nonempty (Derivation body Delta (Completion R size new)) := by
 let phi : Formula (Fin 2) := Completion R (.var 0) (.var 1)
 let xs : Fin 2 → OTerm alpha := ![size,old]
 let ys : Fin 2 → OTerm alpha := ![size,new]
 have hx : phi.subst (fun i => emb (xs i)) = Completion R size old := by
   simp only [phi,completionSubst,Term.subst]; rfl
 have hy : phi.subst (fun i => emb (ys i)) = Completion R size new := by
   simp only [phi,completionSubst,Term.subst]; rfl
 have eqs : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))) := by
   intro i
   refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
   · rw [equalEqn]; exact ⟨refl size⟩
   · rw [equalEqn]; exact he
 have h := InternalGraphCompositionEqualityProof.tupleCongruence body alpha 2 Delta phi
   (fun i => emb (xs i)) (fun i => emb (ys i))
   (fun i => by simpa only [InternalControlGraph.equal,onEquality,emb] using eqs i)
   (by rw [hx]; exact hc)
 rw [hy] at h
 exact h

theorem zeroCore (R : Program 2) (jobs tagged : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields R z jobs tagged))) :
 Nonempty (Derivation body Delta (Completion R z tagged)) := by
 have hj := OriginalContextInsertionLengthProof.lengthZeroRecover jobs (andLeft hf)
 have ht := headTransport OriginalHereditaryVisitScheduler.tagVisits tagged jobs z Fin.elim0 hj (andLeft (andRight hf))
 have he := valueUnique OriginalHereditaryVisitScheduler.tagVisits z tagged (Fin.cons z Fin.elim0)
   OriginalHereditaryAgendaPotentialTaggedHelpersProof.tagNil ht
 exact completionTransport R z z tagged he (VisitListCompletionConsCore.actualEmpty R body alpha Delta)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionBase
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListInductionBase
