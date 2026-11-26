module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativeEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativePositionsProof
open Source InternalOriginalUniformParameterLeaves
open UniformCertificateCompletion
open OriginalClassContextAllPositionObserver OriginalClassContextAllPositionNativeEvaluationProof
open OriginalActiveClassKernelCalibrationSupportProof
open OriginalContextExtensionCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem positionOnPrefix (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (context : Nat) (hctx : Encodable.decode context = some ((symbols,S),table))
    (hclosed : SubtypeClosed (fun tau => tau ∈ S))
    (binders Gamma : List Ty) (sigma : Ty) (seed candidate : Nat)
    (hs : InternalOriginalStepGuard.sourceValidityValue n arity symbols S (binders ++ sigma :: Gamma) seed = 1)
    (hit : rawClassValue n arity symbols S (binders ++ sigma :: Gamma) seed candidate = 1) :
    evaluate (positionTest p.base.oldRepresentative)
      (ofFn ![binders.length,seed,candidate,Nat.pair context (Encodable.encode (binders ++ sigma :: Gamma))]) = 1 := by
  have hobs := OriginalClassContextPrefixNativeProof.actualPrefixErasedClassObservers
    n arity symbols S binders Gamma sigma hclosed seed candidate hs hit
  let parameter := Nat.pair context (Encodable.encode (binders ++ Gamma))
  have hparent : Encodable.decode (Nat.unpair parameter).1 = some ((symbols,S),table) := by
    simpa only [parameter,Nat.unpair_pair] using hctx
  have hobject : ∀ value : Nat, parameterObject value parameter = some (binders ++ Gamma,value) := by
    intro value
    simp only [parameterObject,parameter,Nat.unpair_pair]
    exact Encodable.encodek (binders ++ Gamma,value)
  have hrep (value : Nat) := (BottomRepresentativeEvaluationProof.decodedLeafSlice
    n arity p.base hp.1 parameter ((symbols,S),table) hparent (binders ++ Gamma) hobject value).2.2.1
  rw [testEvaluation]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ]
  apply if_pos
  rw [observationSlice,observationSlice]
  apply congrArg₂ Nat.pair
  · exact (hrep _).trans (hobs.2.2.1.trans (hrep _).symm)
  · exact hobs.2.2.2

/-- Every in-range index determines its actual forward prefix and removed cell. -/
theorem splitAt (Gamma : List Ty) (k : Nat) (hk : k < Gamma.length) :
    ∃ binders sigma tail, Gamma = binders ++ sigma :: tail ∧ binders.length = k := by
  induction Gamma generalizing k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons sigma Gamma ih =>
    cases k with
    | zero => exact ⟨[],sigma,Gamma,rfl,rfl⟩
    | succ k =>
      obtain ⟨binders,d,tail,hGamma,hlen⟩ := ih k (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hk)
      exact ⟨sigma :: binders,d,tail,by simp only [List.cons_append,hGamma],by simp only [List.length_cons,hlen]⟩

theorem allTestsOnContext (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (context : Nat) (hctx : Encodable.decode context = some ((symbols,S),table))
    (hclosed : SubtypeClosed (fun tau => tau ∈ S)) (Gamma : List Ty) (seed candidate : Nat)
    (hs : InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma seed = 1)
    (hit : rawClassValue n arity symbols S Gamma seed candidate = 1) :
    evaluate (allTests p.base.oldRepresentative)
      (ofFn ![seed,candidate,Nat.pair context (Encodable.encode Gamma)]) = 1 := by
  rw [allTestsContext]
  apply scanAll
  intro k hk
  obtain ⟨binders,sigma,tail,hGamma,hlen⟩ := splitAt Gamma k hk
  subst Gamma
  rw [← hlen]
  exact positionOnPrefix n arity p hp symbols S table context hctx hclosed binders tail sigma seed candidate hs hit
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativePositionsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionNativePositionsProof
