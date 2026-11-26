module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryWithConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDichotomyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphComposition InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalSourceInversionSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalTagArithmeticSupportProof (refl)
open OriginalLambdaErasureCaseDefinitions
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem childIHRename {beta : Type} (leaf : Program 4) (source : Program 2)
 (oldS oldT codomain erasedType cutoff context before after : OTerm alpha) (j : alpha → beta)
 (h : ChildIH body leaf source oldS oldT codomain erasedType cutoff context before after) :
 ChildIH body leaf source (oldS.relabel j) (oldT.relabel j) (codomain.relabel j)
   (erasedType.relabel j) (cutoff.relabel j) (context.relabel j) (before.relabel j) (after.relabel j) := by
 intro gamma k
 simpa only [Term.relabel_relabel] using h gamma (k ∘ j)

/-- Rewrite only the original source child of an actual four-input checker;
its target, certificate and parameter are preserved literally. -/
theorem leafSourceTransport (leaf : Program 4) (s s' t cert parameter : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal s s')))
 (h : Nonempty (Derivation body Delta (graph4 leaf (numeral 1) s t cert parameter))) :
 Nonempty (Derivation body Delta (graph4 leaf (numeral 1) s' t cert parameter)) := by
 apply graphInputTransport body alpha 4 Delta (OrdinaryArithmetic.graphFormula leaf) (numeral 1)
   (Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0))))
   (Fin.cons s' (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))) _ h
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) i
 · rw [onEquality]
   simpa only [Fin.cons_zero,equalEqn,eqn] using he
 · rw [onEquality]; exact ⟨refl t⟩
 · rw [onEquality]; exact ⟨refl cert⟩
 · rw [onEquality]; exact ⟨refl parameter⟩

theorem eraseSourceTransport (out erasedType cutoff s t : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal s t)))
 (h : Nonempty (Derivation body Delta
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw out erasedType cutoff s))) :
 Nonempty (Derivation body Delta
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw out erasedType cutoff t)) := by
 apply graphInputTransport body alpha 3 Delta
   (OrdinaryArithmetic.graphFormula OriginalRawSyntaxTransport.erasePackedRaw) out
   (Fin.cons erasedType (Fin.cons cutoff (Fin.cons s Fin.elim0)))
   (Fin.cons erasedType (Fin.cons cutoff (Fin.cons t Fin.elim0))) _ h
 intro i
 refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
 · rw [onEquality]; exact ⟨refl erasedType⟩
 · rw [onEquality]; exact ⟨refl cutoff⟩
 · rw [onEquality]
   simpa only [Fin.cons_succ,Fin.cons_zero,equalEqn,eqn] using he

/-- Query the actual erased body from the already checked square, identifying
its queried old body with the supplied original bodyCode graph. Context
witnesses are internally generated, not imposed as an IH or Frame oracle. -/
theorem namedSquare (s out domain codomain childRaw child erasedType cutoff gamma extended : OTerm alpha)
 (psi : Formula alpha)
 (hp : Nonempty (Derivation body Delta
   (graph3 OriginalLambdaConstructor.packedLambda s domain codomain childRaw)))
 (hb : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.bodyCode child codomain s)))
 (he : Nonempty (Derivation body Delta
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw out erasedType cutoff s)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)))
 (consume : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (childOut childGamma childExtended : OTerm beta),
   (∀ p ∈ Delta, p.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta
    (OriginalLambdaErasureSquareDefinitions.Result (out.relabel j) (child.relabel j) childOut
      (domain.relabel j) (codomain.relabel j) (erasedType.relabel j) (cutoff.relabel j) childGamma childExtended ⊓
     (graph2 InternalListCodec.consCode childGamma (domain.relabel j) (gamma.relabel j) ⊓
      graph2 InternalListCodec.consCode childExtended (domain.relabel j) (extended.relabel j)))) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 apply OriginalLambdaErasureSquareQueryWithConsProof.actualOriginalLambdaErasureSquareQueryWithCons
   body alpha Delta s out domain codomain childRaw erasedType cutoff gamma extended psi hp he hi
 intro beta j Theta queried childOut childGamma childExtended hj h
 have hb' := renameInto hb j Theta hj
 rw [graph2Rename] at hb'
 have hv := valueUnique OriginalLambdaConstructor.bodyCode queried (child.relabel j)
   (Fin.cons (codomain.relabel j) (Fin.cons (s.relabel j) Fin.elim0)) (andLeft (andLeft h)) hb'
 have hsquare := andRight (andLeft h)
 have htransport := eraseSourceTransport childOut (erasedType.relabel j) (suc (cutoff.relabel j))
   queried (child.relabel j) (by simpa only [equalEqn] using hv) (andLeft (andRight hsquare))
 exact consume beta j Theta childOut childGamma childExtended hj
   (andIntro (andIntro (andLeft hsquare) (andIntro htransport (andRight (andRight hsquare)))) (andRight h))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseSupportProof
