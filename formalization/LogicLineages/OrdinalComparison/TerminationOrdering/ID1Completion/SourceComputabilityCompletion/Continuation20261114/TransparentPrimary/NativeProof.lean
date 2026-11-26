module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.SelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentCandidate.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.NativeProof
open Source NumberedUniformPackedDecoding InternalOriginalUniformParameterLeaves
open TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem originalEdge (n : Nat) (arity : Fin n → Nat) (E : Program 3)
    (hE : ∀ v, evaluate E v = edgeValue n arity v)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (hc : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (a b : RawPacked n) :
    evaluate E (List.Vector.ofFn ![Encodable.encode a,Encodable.encode b,parameter]) =
      (NumberedExchangeCode.packedCodeExchange arity ctx.1.1 ctx.1.2 a b).toNat := by
  rw [hE]
  simp only [edgeValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,hc,Encodable.encodek]

theorem calibration : Targets.Calibration := by
  intro n arity T C P E hT hs v
  obtain ⟨hC,hP,hE⟩ := hs
  rw [primary,InternalAcceptanceCalibrationProof.evalBranch,hT]
  change (if targetValue n arity v = 0 then 0 else
    evaluate (PrimaryIteration.run E)
      (List.Vector.ofFn ![evaluate C v,evaluate P v,v.get 0,v.get 1])) = _
  rw [hC,hP]
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma (v.get 1)
  simp only [targetValue,countValue,poolValue,Membership.listValue,decodedValue,ho (v.get 0)]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 1)).1 with
  | none => simp [hc]
  | some ctx =>
    simp only [hc]
    cases hd : rawPackedDecode n arity Gamma (v.get 0) with
    | none => simp [hd]
    | some q =>
      simp only [hd,Option.isSome_some,Bool.toNat_true,Nat.one_ne_zero,ite_false,
        Option.map_some,Option.getD_some]
      have heq : Encodable.encode q = v.get 0 := by
        have h := TransparentCandidate.NativeProof.rawReencoding n arity Gamma (v.get 0)
        simpa only [hd,Option.map_some,Option.getD_some,Option.isSome_some,
          Bool.toNat_true,ite_true] using h
      rw [← heq]
      exact PrimaryIteration.NativeProof.originalPrimaryCalibration n arity ctx.1.1 ctx.1.2 Gamma
        E (v.get 1) (originalEdge n arity E hE (v.get 1) ctx hc) q
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.NativeProof
