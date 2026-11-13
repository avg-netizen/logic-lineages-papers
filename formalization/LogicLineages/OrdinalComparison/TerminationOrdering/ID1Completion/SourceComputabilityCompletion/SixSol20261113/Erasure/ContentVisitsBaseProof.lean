module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsConsCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsInductionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsBaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z emb eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalSourceInversionSupportProof (onEquality)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime ContentVisitsDefinitions ContentVisitsSyntax ContentVisitsInductionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem countedTransport (R : Program 2) (left right newLeft newRight : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (eqn left newLeft)))
 (hr : Nonempty (Derivation body Delta (eqn right newRight)))
 (hc : Nonempty (Derivation body Delta (Counted R left right))) :
 Nonempty (Derivation body Delta (Counted R newLeft newRight)) := by
 let phi : Formula (Fin 2) := Counted R (.var 0) (.var 1)
 let xs : Fin 2 → OTerm alpha := ![left,right]
 let ys : Fin 2 → OTerm alpha := ![newLeft,newRight]
 have hx : phi.subst (fun i => emb (xs i)) = Counted R left right := by
   simp only [phi,countedSubst,Term.subst]; rfl
 have hy : phi.subst (fun i => emb (ys i)) = Counted R newLeft newRight := by
   simp only [phi,countedSubst,Term.subst]; rfl
 have eqs : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))) := by
   intro i
   refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
   · rw [equalEqn]; exact hl
   · rw [equalEqn]; exact hr
 have h := InternalGraphCompositionEqualityProof.tupleCongruence body alpha 2 Delta phi
   (fun i => emb (xs i)) (fun i => emb (ys i))
   (fun i => by simpa only [InternalControlGraph.equal,onEquality,emb] using eqs i)
   (by rw [hx]; exact hc)
 rw [hy] at h
 exact h

theorem zeroCore (R : Program 2) (jobs tagged forward produced : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields R z jobs tagged forward produced))) :
 Nonempty (Derivation body Delta (Counted R tagged produced)) := by
 have hj := OriginalContextInsertionLengthProof.lengthZeroRecover jobs (andLeft hf)
 have ht := headTransport OriginalHereditaryVisitScheduler.tagVisits tagged jobs z Fin.elim0 hj (andLeft (andRight hf))
 have htag := valueUnique OriginalHereditaryVisitScheduler.tagVisits z tagged (Fin.cons z Fin.elim0)
   OriginalHereditaryAgendaPotentialTaggedHelpersProof.tagNil ht
 have hm := headTransport (InternalListMap.map (k := 0) (FramedContentDefinitions.contentProgram R))
   forward jobs z Fin.elim0 hj (andLeft (andRight (andRight (andRight (andRight hf)))))
 obtain ⟨hmap⟩ := InternalListMapProof.actualOriginalListMapZero body 0
   (FramedContentDefinitions.contentProgram R) alpha forward Fin.elim0
 have hforward : Nonempty (Derivation body Delta (eqn forward z)) := by
   have h := InternalRecursionClosureLogicProof.closedApply ⟨Derivation.conjunctionLeft hmap⟩ hm
   simpa only [equalEqn] using h
 have hr := headTransport OriginalTypedArgumentObservations.reverse produced forward z Fin.elim0 hforward
   (andRight (andRight (andRight (andRight (andRight hf)))))
 have hproduced := valueUnique OriginalTypedArgumentObservations.reverse z produced (Fin.cons z Fin.elim0)
   OriginalReverseConsProof.zero hr
 exact countedTransport R z z tagged produced htag hproduced
   (countedIntro R z z z (PrefixFrameIdentityProof.actualIdentity R body alpha Delta))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsBaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsBaseProof
