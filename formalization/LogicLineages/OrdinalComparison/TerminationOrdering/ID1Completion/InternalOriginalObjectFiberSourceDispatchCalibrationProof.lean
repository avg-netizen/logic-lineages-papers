module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchCalibrationProof
open Source InternalOriginalObjectFiberSourceDispatch
open InternalOriginalObjectFiberSourceDispatchEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local instance] Classical.propDecidable

/-- The selected raw typed checker agrees with the original object wrapper
on its exact fiber, for every raw payload and requested type code. -/
theorem typedFiberEquality (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data)
    (hc : SubtypeClosed (fun typ => typ ∈ S))
    (hdata : InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data)
    (typ object : Nat) (hf : (Nat.unpair object).1 = Encodable.encode Gamma) :
    evaluate (InternalCanonicalDescentSelection.selectedTyped data)
        (List.Vector.ofFn ![(Nat.unpair object).2,typ]) =
      JointGammaTyped.typedValue n arity (List.Vector.ofFn
        ![OrdinaryArithmeticQuotient.contextCode symbols S table,typ,object]) := by
  have hd := (objectFiberDecode Gamma object).mpr hf
  rw [InternalCanonicalDescentSelectionEvaluationProof.actualOriginalCanonicalDescentTypedCalibration
    n arity symbols S Gamma table data hc hdata]
  simp only [JointGammaTyped.typedValue,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,hd]
  simp only [OrdinaryArithmeticTypedCarrier.typedValue,InternalOriginalTypedCarrier.typedValue,
    List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons,
    OrdinaryArithmeticQuotient.contextCode,Encodable.encodek,Option.any_some]

 theorem actualOriginalObjectSourcePositiveCalibration :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualOriginalObjectSourcePositiveCalibration := by
  intro n arity symbols S Gamma table data oldPositive hc hdata hold xs
  rw [(actualOriginalObjectSourcePositiveEvaluation
    (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldPositive xs).2]
  by_cases h : xs.get 0 = OrdinaryArithmeticQuotient.contextCode symbols S table ∧
      ((Nat.unpair (xs.get 1)).1 = Encodable.encode Gamma ∧
        (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma)
  · rw [if_pos h]
    have hs := (objectFiberDecode Gamma (xs.get 1)).mpr h.2.1
    have ht := (objectFiberDecode Gamma (xs.get 2)).mpr h.2.2
    have he := (InternalCanonicalQuotientEdgeSelectionEvaluationProof.actualOriginalCanonicalEdgeDataCalibration
      n arity symbols S Gamma table data hc hdata).2.2
    have he' : InternalPathChecker.EdgeCalibrated n arity symbols S Gamma table
        (InternalCanonicalQuotientEdgeSelection.edgeChecker data) := by
      intro x y c
      rw [he]
      change (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y c).toNat =
        if NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y c then 1 else 0
      cases NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y c <;> rfl
    have hp := InternalPathCheckerEvaluationProof.actualOriginalPositivePathCheckerEvaluation
      n arity symbols S Gamma table (InternalCanonicalQuotientEdgeSelection.edgeChecker data)
      he' (Nat.unpair (xs.get 1)).2 (Nat.unpair (xs.get 2)).2 (xs.get 3)
    change evaluate (InternalPathChecker.checker
      (InternalCanonicalQuotientEdgeSelection.edgeChecker data) true)
      ((Nat.unpair (xs.get 1)).2 ::ᵥ (Nat.unpair (xs.get 2)).2 ::ᵥ xs.get 3 ::ᵥ List.Vector.nil) = _
    rw [hp]
    simp only [ContextUniform.positiveValue,hs,ht,if_true]
    simp [OrdinaryArithmeticQuotient.positiveValue,h.1,OrdinaryArithmeticQuotient.contextCode,
      Bool.toNat]
  · rw [if_neg h]
    exact hold xs

 theorem actualOriginalObjectSourceTypedCalibration :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualOriginalObjectSourceTypedCalibration := by
  intro n arity symbols S Gamma table data oldTyped hc hdata hold xs
  rw [(actualOriginalObjectSourceTypedEvaluation
    (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldTyped xs).2]
  by_cases h : xs.get 0 = OrdinaryArithmeticQuotient.contextCode symbols S table ∧
      (Nat.unpair (xs.get 2)).1 = Encodable.encode Gamma
  · rw [if_pos h]
    have hp := typedFiberEquality n arity symbols S Gamma table data hc hdata
      (xs.get 1) (xs.get 2) h.2
    have hx : List.Vector.ofFn ![xs.get 0,xs.get 1,xs.get 2] = xs := by
      apply List.Vector.ext
      intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) i <;> rfl
    rw [← h.1,hx] at hp
    exact hp
  · rw [if_neg h]
    exact hold xs

/-- Activity establishes original Option success before the object pair is
formed. In particular, a default raw zero is never mistaken for success. -/
theorem actualOriginalObjectSourceActiveResult :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualOriginalObjectSourceActiveResult := by
  intro n arity symbols S Gamma table data hc hdata context domain codomain f a h
  rcases h with ⟨hf,ha,hactive⟩
  have hdf := (objectFiberDecode Gamma f).mpr hf
  have hda := (objectFiberDecode Gamma a).mpr ha
  have hj := InternalCanonicalFixedWindowVertexDispatchEvaluationProof.actualOriginalCanonicalFixedWindowActiveVertexEquality
    n arity symbols S Gamma table data hc hdata context domain codomain
      (Nat.unpair a).2 (Nat.unpair f).2 hactive
  rcases hactive with ⟨hcontext,hfunction,hargument⟩
  have hdom : ApplicationDomain.active n arity
      (List.Vector.ofFn ![context,domain,codomain,f,a]) := by
    refine ⟨?_,?_,?_,?_⟩
    · change GuardCalibration.validWindow n context = 1
      rw [hcontext]
      exact (GuardCalibrationProof.actualOriginalWindowCalibration n symbols S table).mpr hc
    · change JointGammaTyped.typedValue n arity
        (List.Vector.ofFn ![context,ApplicationDomain.arrowCode domain codomain,f]) = 1
      rw [hcontext,← typedFiberEquality n arity symbols S Gamma table data hc hdata _ f hf]
      exact hfunction
    · change JointGammaTyped.typedValue n arity
        (List.Vector.ofFn ![context,domain,a]) = 1
      rw [hcontext,← typedFiberEquality n arity symbols S Gamma table data hc hdata _ a ha]
      exact hargument
    · change JointGammaDomain.guardValue (List.Vector.ofFn ![f,a]) = 1
      simp only [JointGammaDomain.guardValue,List.Vector.get_ofFn,
        Matrix.cons_val_zero,Matrix.cons_val_one,hdf,hda]
      rfl
  refine ⟨hdom,?_⟩
  have hsuccess := (ApplicationDomainProof.actualDomainSuccess
    n arity context domain codomain f a hdom).1
  have hoption : ApplicationResultBuilder.resultOption n arity
      (List.Vector.ofFn ![context,domain,codomain,f,a]) =
      (OrdinaryArithmeticApplication.decodedApplication n arity Gamma context domain codomain
        (Nat.unpair f).2 (Nat.unpair a).2).map (ContextUniform.objectCode Gamma) := by
    simp [ApplicationResultBuilder.resultOption,hdf,hda]
  rw [hoption] at hsuccess
  cases hd : OrdinaryArithmeticApplication.decodedApplication n arity Gamma context domain codomain
      (Nat.unpair f).2 (Nat.unpair a).2 with
  | none => simp [hd] at hsuccess
  | some raw =>
    have hjraw : evaluate (InternalCanonicalQuotientEdgeApplicationLift.actualJ data)
        (List.Vector.ofFn ![domain,codomain,(Nat.unpair f).2,(Nat.unpair a).2]) = raw := by
      simpa [ApplicationCertificateLiftPath.vertex,hd] using hj
    have hout : ApplicationResultBuilder.resultOption n arity
        (List.Vector.ofFn ![context,domain,codomain,f,a]) =
        some (Nat.pair (Encodable.encode Gamma) raw) := by
      rw [hoption,hd]
      simp only [Option.map_some,objectCodePair]
    constructor
    · simpa only [hjraw] using hout
    · change (ApplicationResultBuilder.resultOption n arity _).getD 0 = _
      rw [hout,hjraw]
      rfl

 theorem actualOriginalObjectSourceResultCalibration :
    InternalOriginalObjectFiberSourceDispatchTargets.ActualOriginalObjectSourceResultCalibration := by
  intro n arity symbols S Gamma table data oldResult hc hdata hold xs
  rw [(actualOriginalObjectSourceResultEvaluation
    (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data oldResult xs).2]
  split_ifs with h
  · have ha : resultActive (OrdinaryArithmeticQuotient.contextCode symbols S table) Gamma data
        (xs.get 0) (xs.get 1) (xs.get 2) (xs.get 3) (xs.get 4) := by
      simpa only [resultActive,InternalCanonicalFixedWindowVertexDispatch.Active,
        InternalCanonicalFixedWindowVertexDispatch.typedChecker] using h
    have hp := (actualOriginalObjectSourceActiveResult n arity symbols S Gamma table data hc hdata
      (xs.get 0) (xs.get 1) (xs.get 2) (xs.get 3) (xs.get 4) ha).2.2
    have hx : List.Vector.ofFn ![xs.get 0,xs.get 1,xs.get 2,xs.get 3,xs.get 4] = xs := by
      apply List.Vector.ext
      intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
        (Fin.cases ?_ (fun j => Fin.elim0 j))))) i <;> rfl
    rw [hx] at hp
    exact hp.symm
  · exact hold xs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceDispatchCalibrationProof
