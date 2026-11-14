module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.SelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.TupleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.TupleProof
open Source InternalOriginalUniformParameterLeaves TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem recursorCalibration (n : Nat) (arity : Fin n → Nat) (R D : Program 2) (J : Program 3)
    (hR : ∀ v, evaluate R v = ExchangeNumericSuppliers.rankValue n v)
    (hD : ∀ v, evaluate D v = ExchangeNumericSuppliers.depsValue n v)
    (hJ : ∀ v, evaluate J v = ExchangeNumericSuppliers.layerValue n arity v) :
    ∀ v : List.Vector Nat 2, evaluate (ExchangeSelectedRecursor.exchange R D J) v =
      ExchangeNumericSuppliers.valueAt n arity (v.get 0) (v.get 1) := by
  have hr : ∀ seed param, evaluate R (List.Vector.ofFn ![seed,param]) = ExchangeNumericSuppliers.rankAt n seed param := by
    intro seed param; exact hR _
  have hd : ∀ node param, evaluate D (List.Vector.ofFn ![node,param]) = numbersNumber (ExchangeNumericSuppliers.depsAt n node param) := by
    intro node param; exact hD _
  have hj : ∀ node vals param, evaluate J (List.Vector.ofFn ![node,numbersNumber vals,param]) =
      Encodable.encode (ExchangeNumericSuppliers.layerAt n arity node vals param) := by
    intro node vals param
    rw [hJ]
    simp only [ExchangeNumericSuppliers.layerValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,numbersRoundTrip,Option.getD_some]
  have he (seed param : Nat) : evaluate (ExchangeSelectedRecursor.exchange R D J) (List.Vector.ofFn ![seed,param]) =
      ExchangeNumericSuppliers.valueAt n arity seed param :=
    ExchangeSelectedRecursor.NativeProof.nativeFinalValue R D J _ _ _ _ hr hd hj
      (ExchangeNumericSuppliers.NativeProof.nativeRankDecrease n)
      (ExchangeNumericSuppliers.NativeProof.nativeLayerLaw n arity) seed param
  intro v
  have hvec : v.get = ![v.get 0,v.get 1] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  have hv := congrArg List.Vector.ofFn hvec
  rw [List.Vector.ofFn_get] at hv
  rw [hv]
  exact he _ _

theorem selectedTuple : Targets.SelectedTuple := by
  intro n arity p H G W hp hH hG hW
  obtain ⟨Q,hQ⟩ := Proof.allPrimitiveFunctions 2 _ (SeededPrimaryPool.NativeProof.candidatesValuePrimitive n arity)
  obtain ⟨R,hR⟩ := Proof.allPrimitiveFunctions 2 _ (ExchangeNumericSuppliers.PrimitiveProof.rankPrimitive n)
  obtain ⟨D,hD⟩ := Proof.allPrimitiveFunctions 2 _ (ExchangeNumericSuppliers.PrimitiveProof.depsPrimitive n)
  obtain ⟨U,V,hU,hV,hJ⟩ := SelectionProof.supplierSelection n arity
  obtain ⟨C,K,hC,hK⟩ := InstalledExchangeRecursor.SupplierProof.supplierSelection n
  let J := TransparentExchangeLayer.optional U V
  have hLambda : Targets.LambdaAt U V := by
    intro bodyFormula alpha Delta node code param head tail xs hv hs hx hy hc
    exact TransparentExchangeLayer.InternalProof.internalLambda bodyFormula alpha Delta U V
      node code param head tail xs hv hs hx hy hc
  have hX := recursorCalibration n arity R D J hR hD hJ
  let B := InstalledExchangeRecursor.structural R D J C K
  have hB : ∀ v, evaluate B v = TypedPrimaryEdge.structuralValue n arity v :=
    InstalledExchangeRecursor.NativeProof.nativeStructural n arity R D J C K hX hC hK
  let T := OriginalTypedDecoder.target H G
  let P := SeededPrimaryPool.pool T Q
  have hT := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hP := SeededPrimaryPool.NativeProof.poolCalibration n arity T Q hT hQ
  have hs : TransparentPrimary.SuppliersCalibrated n arity (LengthAlignedPrimary.countOfPool P) P (TypedPrimaryEdge.edge B) :=
    ⟨LengthAlignedPrimary.NativeProof.countCalibration n arity P hP,hP,
      TypedPrimaryEdge.NativeProof.edgeCalibration n arity B hB⟩
  have hL := TransparentPrimary.NativeProof.calibration n arity T (LengthAlignedPrimary.countOfPool P)
    P (TypedPrimaryEdge.edge B) hT hs
  have hretain := CandidateIntegration.Proof.retainedTuple n arity p H G W
    (SeededPrimaryPool.primary T Q (TypedPrimaryEdge.edge B)) hp hH hG hW hL
  exact ⟨Q,R,D,U,V,C,K,hQ,hR,hD,hU,hV,hC,hK,hJ,hLambda,hB,hs,hL,hretain⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.TupleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.TupleProof
