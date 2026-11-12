module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (emb)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem tupleTransport (H : Program 1) (M W : Program 2)
 (xs ys : Fin 5 → OTerm alpha)
 (he : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))))
 (ha : Nonempty (Derivation body Delta (Admissible H M W (xs 0) (xs 1) (xs 2) (xs 3) (xs 4)))) :
 Nonempty (Derivation body Delta (Admissible H M W (ys 0) (ys 1) (ys 2) (ys 3) (ys 4))) := by
 let phi : Formula (Fin 5) := Admissible H M W (.var 0) (.var 1) (.var 2) (.var 3) (.var 4)
 have hx : phi.subst (fun i => emb (xs i)) = Admissible H M W (xs 0) (xs 1) (xs 2) (xs 3) (xs 4) := by
  simp only [phi,admissibleSubst,Term.subst]
 have hy : phi.subst (fun i => emb (ys i)) = Admissible H M W (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) := by
  simp only [phi,admissibleSubst,Term.subst]
 have h := InternalGraphCompositionEqualityProof.tupleCongruence body alpha 5 Delta phi
  (fun i => emb (xs i)) (fun i => emb (ys i)) he (by rw [hx]; exact ha)
 rwa [hy] at h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportProof
