module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobContextTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (refl)
open OriginalInternalJobAdmissible
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem contexts (H : Program 1) (M W : Program 2)
 (role typ raw gamma c otherGamma otherC : OTerm alpha)
 (hg : Nonempty (Derivation body Delta (eqn gamma otherGamma)))
 (hc : Nonempty (Derivation body Delta (eqn c otherC)))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c))) :
 Nonempty (Derivation body Delta (Admissible H M W role typ raw otherGamma otherC)) := by
 let xs : Fin 5 → OTerm alpha := ![role,typ,raw,gamma,c]
 let ys : Fin 5 → OTerm alpha := ![role,typ,raw,otherGamma,otherC]
 have he : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))) := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))))) i
  · simpa only [xs,ys,Matrix.cons_val_zero,equalEqn] using (Nonempty.intro (refl (body:=body) (Gamma:=Delta) role))
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using (Nonempty.intro (refl (body:=body) (Gamma:=Delta) typ))
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using (Nonempty.intro (refl (body:=body) (Gamma:=Delta) raw))
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using hg
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using hc
 exact OriginalInternalJobAdmissibleTransportProof.tupleTransport H M W xs ys he ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobContextTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobContextTransportProof
