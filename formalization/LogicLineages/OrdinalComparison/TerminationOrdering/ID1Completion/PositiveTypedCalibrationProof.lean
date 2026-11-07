module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.PositiveTypedCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaSemanticsCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInverseApplicationAccessibilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.PositiveTypedCalibrationProof
open Source NumberedLeastCodeRepresentative NumberedQuotientPaths

private theorem boolToNatRange (b : Bool) : b.toNat = 0 ∨ b.toNat = 1 := by
  cases b <;> simp

theorem actualPositiveRange : PositiveTypedCalibrationTargets.ActualPositiveRange := by
  intro n arity v
  have hfixed (Gamma : List Ty) (w : List.Vector Nat 4) :
      OrdinaryArithmeticQuotient.positiveValue n arity Gamma w = 0 ∨
      OrdinaryArithmeticQuotient.positiveValue n arity Gamma w = 1 := by
    exact boolToNatRange _
  cases hs : Encodable.decode (α := ContextUniform.Object) (v.get 1) with
  | none => simp [ContextUniform.positiveValue,hs]
  | some source =>
    cases ht : Encodable.decode (α := ContextUniform.Object) (v.get 2) with
    | none => simp [ContextUniform.positiveValue,hs,ht]
    | some target =>
      by_cases he : source.1 = target.1
      · simpa only [ContextUniform.positiveValue,hs,ht,if_pos he] using
          hfixed source.1 (List.Vector.ofFn ![v.get 0,source.2,target.2,v.get 3])
      · simp [ContextUniform.positiveValue,hs,ht,he]

/-- Semantic calibration only. The original numeric type and target object
are retained by carrying their existing decoder equations into encodedTyped. -/
theorem actualTypedSuccessor : PositiveTypedCalibrationTargets.ActualTypedSuccessor := by
  intro n arity context typ x y certificate hw hxTyped hpositive
  obtain ⟨Gamma,a,hx,ctx,tau,hctx,ht,ha⟩ :=
    (JointGammaTypedProof.calibration n arity context typ x).mp hxTyped
  obtain ⟨Delta,a',b,hx',hy,ctx',hctx',hp⟩ :=
    (JointGammaSemanticsCalibrationProof.positiveCalibration n arity context x y).mp
      ⟨certificate,hpositive⟩
  have hobj : (Gamma,a) = (Delta,a') := Option.some.inj (hx.symm.trans hx')
  have hGamma : Gamma = Delta := congrArg Prod.fst hobj
  have hsource : a = a' := congrArg Prod.snd hobj
  subst Delta
  subst a'
  have hcontext : ctx = ctx' := Option.some.inj (hctx.symm.trans hctx')
  subst ctx'
  obtain ⟨ctxW,hctxW,hclosed⟩ :=
    (GuardCalibrationProof.actualValidWindowCalibration n context).1.mp hw
  have hWctx : ctxW = ctx := Option.some.inj (hctxW.symm.trans hctx)
  subst ctxW
  obtain ⟨⟨rho,q⟩,hq,hqt,hrep⟩ :=
    (NumberedTypedCarrierProof.typedCanonicalCarrier n arity ctx.1.1 ctx.1.2
      hclosed Gamma tau a).mp ha
  dsimp only at hqt
  subst rho
  have hp' : PositivePath
      (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,q⟩) b := by
    simpa only [hrep] using hp
  obtain ⟨r,hr,hrrep,_htrace⟩ :=
    NumberedInverseApplicationAccessibilityProof.actualTypedSuccessorWitness
      n arity ctx.1.1 ctx.1.2 hclosed (NumberedCopyCertificate.tableAbove ctx.2)
      Gamma tau q b hq hp'
  apply (JointGammaTypedProof.calibration n arity context typ y).mpr
  refine ⟨Gamma,b,hy,ctx,tau,hctx,ht,?_⟩
  exact (NumberedTypedCarrierProof.typedCanonicalCarrier n arity ctx.1.1 ctx.1.2
    hclosed Gamma tau b).mpr ⟨⟨tau,r⟩,hr,rfl,hrrep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.PositiveTypedCalibrationProof
