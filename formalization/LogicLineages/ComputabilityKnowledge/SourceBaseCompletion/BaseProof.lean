module

public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseTargets
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowNamedInternalProvabilityProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruthProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedModelProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedRevisionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedKTProof
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPACoreProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof

@[expose] public section
/-! The exact source-Base contract on the unchanged actual published-D tuple.
PA(L) closures come from the intrinsic arithmetic constructor. Positive and
negative named representations come from the actual named numeral derivations;
their converses come from actual soundness of the Base theory in its named
standard-N interpretation, matched to the source programs by the actual named
dispatch of the same augmented registry. No adequacy, soundness, consistency
or HB premise is introduced, and no finite sentence whitelist is used. -/
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowNamedNumeralCertificates GorbowSourceRegistryPadding

/-! ### Full PA(L) -/

private def closeAll {T : Sentence → Prop} : ∀ {n : Nat} {φ : Formula n}, Derivation T φ →
    Derivation T (GorbowStandardInduction.universalClosure φ)
  | 0, _, p => p
  | n + 1, phi, p => closeAll (n := n) (φ := .all phi) (.generalize p)

theorem fullPAAvailability : SourceBaseCompletion.Targets.FullPAAvailability :=
  fun _ _ w => ⟨closeAll (.arithmetic w)⟩

/-! ### Named syntax representations -/

private def dummyI : Interpretation :=
  ⟨fun _ => False, fun _ => 0, fun _ => False, fun _ => False, fun _ _ => False, fun _ => False⟩

private theorem headerValue (I : Interpretation) (name : Nat × Nat) (v : List.Vector Nat name.1) :
    (inputHeader name v).realize I Fin.elim0 = inputCode name v := by
  unfold inputHeader inputCode
  rw [GorbowRegistryTupleProof.termCalibration 0 I Fin.elim0 |>.2.2]
  simp [GorbowPRNumeralCalculation.numeralArguments, List.map_map, Function.comp_def, numeral_realize]

private theorem functionRepresentations (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) : FunctionRepresentations pF pR q := by
  have hCal := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
  intro name hn v value
  have hG := GorbowPublishedQuantifierTruth.Proof.namedFunctions pF pR q c hA name hn v.toList
    (List.Vector.toList_length v)
  constructor
  · constructor
    · rintro ⟨d⟩
      have hs := GorbowNamedDefiningTheory.Proof.theorySoundness (augmented pF q) pR _ d dummyI
      change GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
        ((inputHeader name v).realize _ Fin.elim0) = (Term.numeral value).realize _ Fin.elim0 at hs
      rw [headerValue, numeral_realize] at hs
      exact hG.symm.trans hs
    · intro h
      have e : evaluate (augmented pF q) (inputCode name v ::ᵥ List.Vector.nil) = value :=
        (hCal.1 _).trans h
      have hc := GorbowNamedNumeralCertificates.Proof.namedFunctionCalculation
        (augmented pF q) pR name hn v
      rw [e] at hc
      exact hc
  · constructor
    · rintro ⟨d⟩
      have hs := GorbowNamedDefiningTheory.Proof.theorySoundness (augmented pF q) pR _ d dummyI
      change ¬ (GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR
        ((inputHeader name v).realize _ Fin.elim0) = (Term.numeral value).realize _ Fin.elim0) at hs
      rw [headerValue, numeral_realize] at hs
      exact fun he => hs (hG.trans he)
    · intro h
      exact GorbowNamedNumeralCertificates.Proof.namedFunctionRefutation (augmented pF q) pR
        name hn v value (fun he => h ((hCal.1 _).symm.trans he))

private theorem relationRepresentations (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) : RelationRepresentations pF pR q := by
  have hCal := GorbowNamedInternalProvability.Proof.preservesCalibration 5 pF pR q hA.1
  intro name hn v
  have hG := GorbowPublishedQuantifierTruth.Proof.namedRelations pF pR q c hA name hn v.toList
    (List.Vector.toList_length v)
  obtain ⟨ht, hf⟩ := GorbowNamedNumeralCertificates.Proof.namedRelationCalculation
    (augmented pF q) pR name hn v
  constructor
  · constructor
    · rintro ⟨d⟩
      have hs := GorbowNamedDefiningTheory.Proof.theorySoundness (augmented pF q) pR _ d dummyI
      change GorbowNamedRegistryInterpretation.relationProgram (augmented pF q) pR
        ((inputHeader name v).realize _ Fin.elim0) = true at hs
      rw [headerValue] at hs
      exact hG.mp hs
    · intro h
      apply ht
      rw [hCal.2]
      simp [GorbowSourceRegistryPadding.sourceRelationValue, h]
  · constructor
    · rintro ⟨d⟩
      have hs := GorbowNamedDefiningTheory.Proof.theorySoundness (augmented pF q) pR _ d dummyI
      change ¬ (GorbowNamedRegistryInterpretation.relationProgram (augmented pF q) pR
        ((inputHeader name v).realize _ Fin.elim0) = true) at hs
      rw [headerValue] at hs
      cases hb : GorbowSortedRegistry.relationProgram (inputCode name v) with
      | false => rfl
      | true => exact absurd (hG.mpr hb) hs
    · intro h
      apply hf
      rw [hCal.2]
      simp [GorbowSourceRegistryPadding.sourceRelationValue, h]

private theorem groundRepresentations (pF pR : Program 1) (q : Program 5) (c : Code)
    (hA : Actual pF pR q c) : GroundRepresentations pF pR q :=
  ⟨GorbowPublishedQuantifierTruth.Proof.namedFunctions pF pR q c hA,
    GorbowPublishedQuantifierTruth.Proof.namedRelations pF pR q c hA⟩

theorem actualSyntaxAdequacy : SourceBaseCompletion.Targets.ActualSyntaxAdequacy :=
  fun pF pR q c hA =>
    ⟨functionRepresentations pF pR q c hA, relationRepresentations pF pR q c hA,
      groundRepresentations pF pR q c hA⟩

/-! ### Validity along the actual revision sequence -/

theorem baseRevisionValidity : SourceBaseCompletion.Targets.BaseRevisionValidity := by
  intro pF pR q c hA k
  refine ⟨fun n w => ?_, fun sigma hs => ?_⟩
  · exact (GorbowStandardInductionProof.universalClosureSemantics n _ _).mpr
      (fun v => GorbowPACoreProof.arithmeticSoundness n w _ v)
  · exact GorbowPublishedRevision.Proof.stageAxioms pF pR q c hA k sigma
      (Or.inl (List.mem_append_left _ hs))

/-! ### Self-indexed D calibration -/

theorem selfIndexedCalibration : SourceBaseCompletion.Targets.SelfIndexedCalibration :=
  fun pF pR q c hA I sigma =>
    ⟨GorbowPublishedModel.Proof.dProvabilityCalibration pF pR q c hA I sigma,
      GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA sigma⟩

/-! ### One actual tuple: Base contract, selected clauses, both KT consistencies -/

theorem completeSourcePair : SourceBaseCompletion.Targets.CompleteSourcePair := by
  obtain ⟨pF, pR, q, c, hA⟩ := GorbowPublishedDCB.Proof.actualParameters
  refine ⟨pF, pR, q, c, hA, actualSyntaxAdequacy pF pR q c hA, fun A sigma tau =>
    ⟨fun hd => ?_, GorbowPublishedDCB.Proof.selectedDistribution pF pR q c hA A sigma tau,
      GorbowPublishedDCB.Proof.selectedReflection pF pR q c hA A sigma⟩,
    GorbowPublishedKT.Proof.consistency pF pR q c hA false,
    GorbowPublishedKT.Proof.consistency pF pR q c hA true⟩
  obtain ⟨p1⟩ := GorbowPublishedDCB.Proof.dProofCertification pF pR q c hA sigma hd
  obtain ⟨p2⟩ := GorbowPublishedDCB.Proof.selectedReflection pF pR q c hA A sigma
  exact ⟨.mp p2 p1⟩

theorem fullTarget : SourceBaseCompletion.Targets.Target :=
  ⟨fullPAAvailability, actualSyntaxAdequacy, baseRevisionValidity, selfIndexedCalibration,
    completeSourcePair⟩

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.Proof
