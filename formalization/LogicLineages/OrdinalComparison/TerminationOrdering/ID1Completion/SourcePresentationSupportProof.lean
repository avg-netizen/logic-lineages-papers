module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationSupportProof
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open PositiveArithmeticOperatorsSupportProof SourceComputabilityFormulaSupportProof
open SourcePresentation SourceEndpoint
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem positiveSubstitutionTruth {α : Type} (body : Positive α) :
    ∀ (β : Type) (ts : α → OrdinaryArithmetic.Term β) (P : Nat → Prop) (v : β → Nat),
    realize P (substitutePositive ts body).formula v ↔
      realize P body.formula (fun a => (ts a).realize v) := by
  induction body with
  | arithmetic phi =>
    intro β ts P v
    change realize P (arithmeticEmbedding.onFormula (phi.subst ts)) v ↔
      realize P (arithmeticEmbedding.onFormula phi) _
    rw [embeddingTruth,embeddingTruth]
    simp only [FirstOrder.Language.Formula.Realize,BoundedFormula.realize_subst]
  | predicate t =>
    intro β ts P v
    change realize P (Positive.predicate (t.subst ts)).formula v ↔ _
    rw [predicateTruth,predicateTruth,FirstOrder.Language.Term.realize_subst]
  | conj p q ihp ihq =>
    intro β ts P v
    change realize P (Positive.conj (substitutePositive ts p) (substitutePositive ts q)).formula v ↔ _
    rw [conjTruth,conjTruth,ihp,ihq]
  | guarded guard p ih =>
    intro β ts P v
    change realize P (Positive.guarded (guard.subst ts) (substitutePositive ts p)).formula v ↔ _
    rw [guardedTruth,guardedTruth,ih]
    apply imp_congr
    · simp only [FirstOrder.Language.Formula.Realize,BoundedFormula.realize_subst]
    · rfl
  | all p ih =>
    intro β ts P v
    change realize P (Positive.all (substitutePositive _ p)).formula v ↔ _
    rw [allTruth,allTruth]
    apply forall_congr'
    intro xs
    rw [ih]
    have hv : (fun a =>
        (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i : Fin 1 => .var (.inr i)) a).realize
          (Sum.elim v xs)) = Sum.elim (fun a => (ts a).realize v) xs := by
      funext a
      cases a with
      | inl a =>
        rw [Sum.elim_inl,FirstOrder.Language.Term.realize_relabel]
        rfl
      | inr i => rfl
    rw [hv]

theorem actualSourcePresentationExists : SourcePresentationTargets.ActualSourcePresentationExists := by
  intro n arity Gamma
  obtain ⟨hs,hm⟩ := OrdinaryArithmeticCarrierProof.carrierCheckersPrimitive n arity Gamma
  obtain ⟨ps,hps⟩ := Proof.allPrimitiveFunctions 2 (OrdinaryArithmeticCarrier.scalarValue n arity Gamma) hs
  obtain ⟨pm,hpm⟩ := Proof.allPrimitiveFunctions 2 (OrdinaryArithmeticCarrier.listValue n arity Gamma) hm
  obtain ⟨pH,pR,hpH,hpR,hH,hR⟩ := OrdinaryArithmeticQuotientProof.encodedHAndPositiveR n arity Gamma
  obtain ⟨pD,hpD,hD⟩ := OrdinaryArithmeticDirectProof.encodedDirectFormula n arity Gamma
  exact ⟨⟨ps,pm,pR,pD⟩,hps,hpm,hpR,hpD⟩

theorem checkerTruth (p : Program 2) (context x : Nat) :
    (SourcePresentation.checkerFormula p).Realize ![context,x] ↔
      evaluate p (List.Vector.ofFn ![context,x]) = 1 := by
  rw [SourcePresentation.checkerFormula,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth]
  rfl

theorem scalarCarrierTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (hcal : Calibrated data n arity Gamma) (context x : Nat) :
    (SourcePresentation.checkerFormula data.scalar).Realize ![context,x] ↔
      OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context x := by
  rw [checkerTruth,hcal.1]
  exact OrdinaryArithmeticCarrierSupportProof.scalarCalibration n arity Gamma context x

theorem listCarrierTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (hcal : Calibrated data n arity Gamma) (context x : Nat) :
    (SourcePresentation.checkerFormula data.multiset).Realize ![context,x] ↔
      OrdinaryArithmeticCarrier.encodedList n arity Gamma context x := by
  rw [checkerTruth,hcal.2.1]
  exact OrdinaryArithmeticCarrierSupportProof.listCalibration n arity Gamma context x

theorem positiveGraphTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (hcal : Calibrated data n arity Gamma) (context x y : Nat) :
    (OrdinaryArithmeticQuotient.certificateGraph data.positive).Realize ![context,x,y] ↔
      encodedR n arity Gamma context x y := by
  rw [OrdinaryArithmeticQuotientProof.certificateGraphTruth]
  simp only [hcal.2.2.1,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact OrdinaryArithmeticQuotientProof.encodedPositiveCertificates n arity Gamma context x y

theorem directGraphTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (hcal : Calibrated data n arity Gamma) (context x y : Nat) :
    (OrdinaryArithmeticQuotient.certificateGraph data.direct).Realize ![context,x,y] ↔
      OrdinaryArithmeticDirect.encodedDirect n arity Gamma context x y := by
  rw [OrdinaryArithmeticQuotientProof.certificateGraphTruth]
  simp only [hcal.2.2.2,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact OrdinaryArithmeticDirectProof.encodedCertificates n arity Gamma context x y

theorem scalarOperatorTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (hcal : Calibrated data n arity Gamma) (context : Nat) (P : Nat → Prop) (x : Nat) :
    realize P (SourcePresentation.scalarOperator data).formula ![context,x] ↔
      OrdinaryArithmeticCarrier.encodedScalar n arity Gamma context x ∧ ∀ y, encodedR n arity Gamma context x y → P y := by
  rw [SourcePresentation.scalarOperator,PositiveArithmeticOperatorsProof.accessibilityOperatorTruth,scalarCarrierTruth data n arity Gamma hcal]
  exact and_congr Iff.rfl (forall_congr' (fun y => imp_congr (positiveGraphTruth data n arity Gamma hcal context x y) Iff.rfl))

theorem multisetOperatorTruth (data : Data) (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (hcal : Calibrated data n arity Gamma) (context : Nat) (P : Nat → Prop) (x : Nat) :
    realize P (SourcePresentation.multisetOperator data).formula ![context,x] ↔
      OrdinaryArithmeticCarrier.encodedList n arity Gamma context x ∧
        ∀ y, OrdinaryArithmeticDirect.encodedDirect n arity Gamma context x y → P y := by
  rw [SourcePresentation.multisetOperator,PositiveArithmeticOperatorsProof.accessibilityOperatorTruth,listCarrierTruth data n arity Gamma hcal]
  exact and_congr Iff.rfl (forall_congr' (fun y => imp_congr (directGraphTruth data n arity Gamma hcal context x y) Iff.rfl))

theorem closedPresentationTruth (data : Data) (context z : Nat) (P : Nat → Prop) :
    realize P (SourcePresentation.sourceBody data context).formula ![z] ↔
      realize P (TaggedArithmeticOperators.combinedOperator
        (SourcePresentation.scalarOperator data) (SourcePresentation.multisetOperator data)).formula ![context,z] := by
  rw [SourcePresentation.sourceBody,positiveSubstitutionTruth]
  have hv : (fun a : Fin 2 => (![numeral context, (.var 0 : OrdinaryArithmetic.Term (Fin 1))] a).realize ![z]) = ![context,z] := by
    funext i
    exact Fin.cases (numeralTruth context ![z])
      (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [hv]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentationSupportProof
