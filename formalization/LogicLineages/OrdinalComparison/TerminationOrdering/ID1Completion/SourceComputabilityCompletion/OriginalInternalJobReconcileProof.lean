module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalDecorationStoredProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobReconcileProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (refl)
open OriginalInternalJobAdmissible
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem reconcile (H : Program 1) (M W : Program 2)
 (index role typ raw rawCell child childRole childType typed stored annotation
  expectedAnnotation expectedRole expectedType expectedRaw expectedParameter expectedGamma
  childRaw childParameter childGamma c : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType)))
 (he : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing expectedAnnotation expectedRole expectedType)))
 (hv : Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.annotation expectedAnnotation index role typ raw)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCell expectedRaw expectedParameter)))
 (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing expectedParameter c expectedGamma)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing stored childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma)))
 (haccept : Nonempty (Derivation body Delta (Admissible H M W expectedRole expectedType expectedRaw expectedGamma c))) :
 Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c)) := by
 have hc := OriginalInternalDecorationStoredProof.coordinates index role typ raw rawCell child childRole childType typed stored annotation hd hp ht ha
 have hann := OriginalInternalAnnotationEqualityProof.annotationFields index role typ raw expectedAnnotation annotation expectedRole expectedType childRole childType
  hv (andRight hc) he ha
 have hraw := OriginalInternalAnnotationEqualityProof.pairFields rawCell stored expectedRaw expectedParameter childRaw childParameter hr hcr (andLeft hc)
 have hgamma := OriginalInternalAnnotationEqualityProof.pairFields expectedParameter childParameter c expectedGamma c childGamma hg hcg (andRight hraw)
 let xs : Fin 5 → OTerm alpha := ![expectedRole,expectedType,expectedRaw,expectedGamma,c]
 let ys : Fin 5 → OTerm alpha := ![childRole,childType,childRaw,childGamma,c]
 have hs : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))) := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))))) i
  · simpa only [xs,ys,Matrix.cons_val_zero,equalEqn] using andLeft hann
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using andRight hann
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using andLeft hraw
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using andRight hgamma
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using (Nonempty.intro (refl (body:=body) (Gamma:=Delta) c))
 exact OriginalInternalJobAdmissibleTransportProof.tupleTransport H M W xs ys hs haccept
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobReconcileProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobReconcileProof
