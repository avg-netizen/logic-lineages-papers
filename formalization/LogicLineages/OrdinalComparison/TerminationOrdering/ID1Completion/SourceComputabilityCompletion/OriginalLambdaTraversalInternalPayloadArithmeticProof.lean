module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalPairingSumBounds InternalPairingSumBoundsArithmeticProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof InternalUnpairArithmeticProof
open InternalUnpairReverseBoundsArithmeticProof
open InternalApplicationResultStackComposition
open InternalQuotientComparisonProof InternalApplicationCertifiedResultFoldClosure
open InternalApplicationCertifiedResultFoldClosureFuelProof (fuelCountExpansion)
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Payload fuel is literally successor of payload plus payload, as in the frozen program. -/
theorem applicationDescent (p fp ap : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (weakBound (childFuelSum fp ap) p))) :
    Nonempty (Derivation body Gamma
      (InternalLessThan.strictLess fp p ⊓ InternalLessThan.strictLess ap p)) := by
  have hf : Nonempty (Derivation body Gamma
      (InternalLessThan.strictLess fp (childFuelSum fp ap))) := by
    obtain ⟨hf⟩ := leftWeakAdd (body := body) (Gamma := Gamma) fp (suc ap)
    exact ⟨orderRight fp (symm (leftSuccessor fp (suc ap))) hf⟩
  have ha : Nonempty (Derivation body Gamma
      (InternalLessThan.strictLess ap (childFuelSum fp ap))) := by
    obtain ⟨ha⟩ := rightWeakAdd (body := body) (Gamma := Gamma) (suc fp) ap
    exact ⟨orderRight ap (symm (addSucc (suc fp) ap)) ha⟩
  obtain ⟨hf⟩ := strictWeakTrans fp (childFuelSum fp ap) p hf h
  obtain ⟨ha⟩ := strictWeakTrans ap (childFuelSum fp ap) p ha h
  exact ⟨Derivation.conjunctionIntroduction hf ha⟩

theorem lambdaDescent (p bp : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (weakBound (suc bp) p))) :
    Nonempty (Derivation body Gamma (InternalLessThan.strictLess bp p)) :=
  strictWeakTrans bp (suc bp) p ⟨equalToNext (refl bp)⟩ h

theorem doubleWeak (s t : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (weakBound s t))) :
    Nonempty (Derivation body Gamma (weakBound (add s s) (add t t))) :=
  weakTrans (add s s) (add t s) (add t t)
    (addWeakRight s t s h) (addWeakLeft t s t h)

theorem weakNext (t : OTerm alpha) :
    Nonempty (Derivation body Gamma (weakBound t (suc t))) :=
  rightSuccessor t (suc t) ⟨equalToNext (refl t)⟩

/-- Two visit completions and the opening/return steps fit the original fuel. -/
theorem applicationFuel (p fp ap : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (weakBound (childFuelSum fp ap) p))) :
    Nonempty (Derivation body Gamma (weakBound
      (suc (add (payloadFuel fp) (add (payloadFuel ap) (suc z)))) (payloadFuel p))) := by
  obtain ⟨h'⟩ := weakTrans (add (childFuelSum fp ap) (childFuelSum fp ap))
    (add p p) (suc (add p p)) (doubleWeak _ _ h) (weakNext (body := body) (Gamma := Gamma) (add p p))
  exact ⟨orderLeft (suc (payloadFuel p)) (symm (fuelCountExpansion fp ap)) h'⟩

theorem lambdaFuel (p bp : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (weakBound (suc bp) p))) :
    Nonempty (Derivation body Gamma (weakBound (suc (suc (payloadFuel bp))) (payloadFuel p))) := by
  obtain ⟨h'⟩ := successorWeak (add (suc bp) (suc bp)) (add p p) (doubleWeak _ _ h)
  have he : Derivation body Gamma
      (eqn (suc (add (suc bp) (suc bp))) (suc (suc (payloadFuel bp)))) :=
    congSuc (trans (leftSuccessor bp (suc bp)) (congSuc (addSucc bp bp)))
  exact ⟨orderLeft (suc (payloadFuel p)) he h'⟩

theorem applicationCount (p fp ap cf ca : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (weakBound (childFuelSum fp ap) p)))
    (hf : Nonempty (Derivation body Gamma (weakBound cf (payloadFuel fp))))
    (ha : Nonempty (Derivation body Gamma (weakBound ca (payloadFuel ap)))) :
    Nonempty (Derivation body Gamma (weakBound
      (suc (add cf (add ca (suc z)))) (payloadFuel p))) := by
  have ha' := addWeakRight ca (payloadFuel ap) (suc z) ha
  have h1 := addWeakLeft cf (add ca (suc z)) (add (payloadFuel ap) (suc z)) ha'
  have h2 := addWeakRight cf (payloadFuel fp) (add (payloadFuel ap) (suc z)) hf
  exact weakTrans _ _ _ (successorWeak _ _ (weakTrans _ _ _ h1 h2)) (applicationFuel p fp ap hp)

theorem lambdaCount (p bp cb : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (weakBound (suc bp) p)))
    (hb : Nonempty (Derivation body Gamma (weakBound cb (payloadFuel bp)))) :
    Nonempty (Derivation body Gamma (weakBound (suc (suc cb)) (payloadFuel p))) :=
  weakTrans _ _ _ (successorWeak _ _ (successorWeak _ _ hb)) (lambdaFuel p bp hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
