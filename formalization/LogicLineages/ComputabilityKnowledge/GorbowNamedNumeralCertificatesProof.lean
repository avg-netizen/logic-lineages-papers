module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesTargets
public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivationProof
public import LogicLineages.ComputabilityKnowledge.GorbowUniversalInstantiationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificates.Proof
open GorbowSyntax GorbowSubstitution GorbowPRProgram GorbowSourceRegistryPadding
open GorbowNamedDefiningTheory GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open GorbowPRNumeralCalculation (numeralArguments)
open GorbowClosedEquality GorbowStandardInstances

private def numSub {n} (v : List.Vector Nat n) (i : Fin n) : Term 0 := Term.numeral (v.get i)

private theorem subHeader (name : Nat × Nat) (v : List.Vector Nat name.1) :
    substitute (numSub v) (headerVariables name) = inputHeader name v := by
  unfold headerVariables inputHeader
  rw [GorbowHeaderSubstitutionProof.headers]
  congr 1
  change ((argumentVariables name.1).map (substitute (numSub v))).toList = _
  congr 1
  apply List.Vector.ext
  intro i
  simp [argumentVariables, numeralArguments, numSub, substitute]

private theorem substituteCall {ctx out arity} tag (args : List.Vector (Term ctx) arity)
    (sigma : Fin ctx → Term out) :
    substitute sigma (call tag args) = call tag (args.map (substitute sigma)) :=
  GorbowPRCallCongruence.Proof.callSubstitution ctx out arity tag args sigma

private theorem headerCalculation (A : Sentence → Prop) name (v : List.Vector Nat name.1) :
    Nonempty (Derivation A (.equal (inputHeader name v) (Term.numeral (inputCode name v)))) := by
  have ha : ∀ t ∈ (numeralArguments v).toList, ArithmeticTerm t := by
    intro t ht
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp ht
    exact GorbowStandardInstancesProof.arithmeticNumerals 0 k
  have har := GorbowRegistryTupleProof.arithmeticConstructors.2.2 0 name.1 name.2 _ ha
  let I : Interpretation := ⟨fun _ => False, fun _ => 0, fun _ => False,
    fun _ => False, fun _ _ => False, fun _ => False⟩
  have hv : (inputHeader name v).realize I Fin.elim0 = inputCode name v := by
    unfold inputHeader inputCode
    rw [GorbowRegistryTupleProof.termCalibration 0 I Fin.elim0 |>.2.2]
    simp [numeralArguments, List.map_map, Function.comp_def, numeral_realize]
  obtain ⟨hp⟩ := GorbowArithmeticDerivationProof.closedEvaluation (inputHeader name v) har I
  rw [hv] at hp
  exact GorbowTheoryProofProof.coreEmbedding A 0 _ hp

private theorem internalCalculation (pF pR : Program 1) tag (q : Program 1)
    (ht : (GorbowPRRegistry.nodes (root pF pR))[tag]? = some ⟨1,q⟩)
    name (v : List.Vector Nat name.1) :
    Nonempty (Derivation (Theory pF pR) (.equal
      (call tag (inputHeader name v ::ᵥ List.Vector.nil))
      (Term.numeral (evaluate q (inputCode name v ::ᵥ List.Vector.nil))))) := by
  obtain ⟨hh⟩ := headerCalculation (Theory pF pR) name v
  obtain ⟨hc⟩ := GorbowPRCallCongruence.Proof.callCongruence (Theory pF pR) 1 tag
    (inputHeader name v ::ᵥ List.Vector.nil) (Term.numeral (inputCode name v) ::ᵥ List.Vector.nil)
    (fun i => by have hi : i = 0 := Fin.eq_zero i; subst i; exact ⟨hh⟩)
  obtain ⟨hn⟩ := (GorbowNamedDefiningTheory.Proof.internalNumeralCertificates
    pF pR tag 1 q ht (inputCode name v ::ᵥ List.Vector.nil)).1
  exact GorbowTheoryEqualityProof.transitivity (Theory pF pR) _ _ _ hc hn

private theorem functionInstance (pF pR : Program 1) name (hn : name ∈ functionNames)
    (v : List.Vector Nat name.1) : Nonempty (Derivation (Theory pF pR)
      (.equal (.universalFunction (inputHeader name v))
        (call functionTag (inputHeader name v ::ᵥ List.Vector.nil)))) := by
  have hm : Theory pF pR (functionAlias name) :=
    List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨name,hn,rfl⟩))
  have h := GorbowUniversalInstantiation.Proof.axiomSpecialization (Theory pF pR) name.1
    (.equal (.universalFunction (headerVariables name))
      (call functionTag (headerVariables name ::ᵥ List.Vector.nil))) (numSub v) hm
  simpa only [GorbowUniversalInstantiation.closedInstance, GorbowFormulaSubstitution.substituteFormula, substitute,
    substituteCall, subHeader, List.Vector.map_cons, List.Vector.map_nil] using h

theorem namedFunctionCalculation : Targets.NamedFunctionCalculation := by
  intro pF pR name hn v
  obtain ⟨ha⟩ := functionInstance pF pR name hn v
  obtain ⟨hb⟩ := internalCalculation pF pR functionTag pF
    (GorbowSourceRegistryPadding.Proof.functionRoot pF pR) name v
  exact GorbowTheoryEqualityProof.transitivity (Theory pF pR) _ _ _ ha hb

private theorem negativeInstance (t u : Term 0) :
    instantiate (.neg (.equal (.var 0) (liftClosedTerm 1 u))) t = .neg (.equal t u) := by
  change Formula.neg (instantiate (.equal (.var 0) (liftClosedTerm 1 u)) t) = _
  rw [GorbowClosedEqualityProof.instantiatedEqual,
    GorbowClosedEqualityProof.instantiateVariable, GorbowClosedEqualityProof.instantiateLift]

private theorem refuteValue (A : Sentence → Prop) (t : Term 0) correct value
    (hp : Derivation A (.equal t (Term.numeral correct))) (hne : correct ≠ value) :
    Nonempty (Derivation A (.neg (.equal t (Term.numeral value)))) := by
  obtain ⟨hs⟩ := GorbowTheoryEqualityProof.symmetry A _ _ hp
  obtain ⟨hn⟩ := GorbowPRNegativeNumerals.Proof.unequalNumerals A correct value hne
  let phi : Formula 1 := .neg (.equal (.var 0) (liftClosedTerm 1 (Term.numeral value)))
  obtain ⟨hi⟩ := GorbowTheoryEqualityProof.formulaImplication A phi (Term.numeral correct) t hs
  have hn' : Derivation A (instantiate phi (Term.numeral correct)) := by
    simpa only [phi, negativeInstance] using hn
  exact ⟨by simpa only [phi, negativeInstance] using Derivation.mp hi hn'⟩

theorem namedFunctionRefutation : Targets.NamedFunctionRefutation := by
  intro pF pR name hn v value hne
  obtain ⟨hp⟩ := namedFunctionCalculation pF pR name hn v
  exact refuteValue (Theory pF pR) _ _ value hp hne

private theorem relationInstance (pF pR : Program 1) name (hn : name ∈ relationNames)
    (v : List.Vector Nat name.1) : Nonempty (Derivation (Theory pF pR)
      (GorbowBooleanTruth.biconditional (relationSentence name v)
        (.equal (call (relationTag pF) (inputHeader name v ::ᵥ List.Vector.nil)) (Term.numeral 1)))) := by
  have hm : Theory pF pR (relationAlias pF name) :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_map.mpr ⟨name,hn,rfl⟩))
  have h := GorbowUniversalInstantiation.Proof.axiomSpecialization (Theory pF pR) name.1
    (GorbowBooleanTruth.biconditional (.universalRelation (headerVariables name))
      (.equal (call (relationTag pF) (headerVariables name ::ᵥ List.Vector.nil)) (Term.numeral 1)))
    (numSub v) hm
  simpa only [GorbowUniversalInstantiation.closedInstance, GorbowBooleanTruth.biconditional,
    GorbowFormulaSubstitution.substituteFormula, substitute, substituteCall, subHeader, List.Vector.map_cons,
    List.Vector.map_nil, Term.numeral, relationSentence] using h

theorem namedRelationCalculation : Targets.NamedRelationCalculation := by
  intro pF pR name hn v
  obtain ⟨ha⟩ := relationInstance pF pR name hn v
  obtain ⟨hv⟩ := internalCalculation pF pR (relationTag pF) pR
    (GorbowSourceRegistryPadding.Proof.relationRoot pF pR) name v
  constructor
  · intro he
    rw [he] at hv
    exact ⟨.mp (.mp (.logical (.andRight _ _)) ha) hv⟩
  · intro he
    obtain ⟨hneg⟩ := refuteValue (Theory pF pR) _ _ 1 hv he
    have hi := Derivation.mp (Derivation.logical (.andLeft _ _)) ha
    exact GorbowClassicalDerivation.Proof.modusTollens (Theory pF pR) _ _ hi hneg

theorem specificSourceCertificates : Targets.SpecificSourceCertificates := by
  obtain ⟨_,_,pF,pR,hpF,hpR⟩ := GorbowSourceRegistryPadding.Proof.specificPrograms
  refine ⟨pF,pR,?_,?_⟩
  · intro name hn v
    constructor
    · simpa only [hpF] using namedFunctionCalculation pF pR name hn v
    · intro value hne
      apply namedFunctionRefutation pF pR name hn v value
      simpa only [hpF] using hne
  · intro name hn v
    obtain ⟨ht,hf⟩ := namedRelationCalculation pF pR name hn v
    constructor
    · intro he
      apply ht
      rw [hpR]
      simp [sourceRelationValue, he]
    · intro he
      apply hf
      rw [hpR]
      simp [sourceRelationValue, he]

end LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificates.Proof
