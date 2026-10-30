module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryRepresentation
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDiagramProof
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticDerivationProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificateProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryRepresentationProof
open GorbowSyntax GorbowStandardInstances GorbowTheoryProof GorbowRegistryDiagram GorbowRegistryRepresentation
open GorbowClosedEquality GorbowClosedEqualityProof

private theorem subLift (σ : Fin 1 → Term 0) (w : Term 0) :
    GorbowSubstitution.substitute σ (liftClosedTerm 1 w)=w := closedTransport 1 w σ

private theorem transport (φ : Formula 1) (t u : Term 0) (p : GorbowPACore.Proof (.equal t u))
    (q : Derivation Theory (instantiate φ t)) : Nonempty (Derivation Theory (instantiate φ u)) :=
  ⟨.mp (.mp (.logical (.equalityReplace φ t u)) (GorbowTheoryProofProof.coreTree Theory p)) q⟩

theorem arithmeticInputs : Comparators.GorbowRegistryRepresentation.ArithmeticInputs := by
  intro s hs
  obtain ⟨p⟩ := GorbowArithmeticDerivationProof.closedEvaluation s hs
    (GorbowSortedRevision.interpretation GorbowAtomicRegistry.ground (fun _ => False))
  obtain ⟨ps⟩ := symmetry _ _ p
  refine ⟨?_,?_,?_⟩
  · constructor
    · rintro ⟨q⟩
      exact GorbowRegistryDiagramProof.theorySoundness (fun _ => False) 0 _ q Fin.elim0
    · intro h
      obtain ⟨q⟩ := (GorbowRegistryDiagramProof.numeralwiseRepresentation.1 (inputValue s)).mpr h
      have ht := transport (.universalRelation (.var 0)) (Term.numeral (inputValue s)) s ps q
      exact ht
  · constructor
    · rintro ⟨q⟩
      have h := GorbowRegistryDiagramProof.theorySoundness (fun _ => False) 0 _ q Fin.elim0
      change ¬ GorbowSortedRegistry.relationProgram (inputValue s)=true at h
      simpa using h
    · intro h
      obtain ⟨q⟩ := (GorbowRegistryDiagramProof.numeralwiseRepresentation.2.1 (inputValue s)).mpr h
      exact transport (.neg (.universalRelation (.var 0))) (Term.numeral (inputValue s)) s ps q
  · intro m
    constructor
    · rintro ⟨q⟩
      have h := GorbowRegistryDiagramProof.theorySoundness (fun _ => False) 0 _ q Fin.elim0
      change GorbowAtomicRegistry.functionProgram (inputValue s)=(Term.numeral m).realize _ Fin.elim0 at h
      simpa only [numeral_realize] using h
    · intro h
      obtain ⟨q⟩ := (GorbowRegistryDiagramProof.numeralwiseRepresentation.2.2 (inputValue s) m).mpr h
      let φ : Formula 1 := .equal (.universalFunction (.var 0)) (liftClosedTerm 1 (Term.numeral m))
      have qi : Derivation Theory (instantiate φ (Term.numeral (inputValue s))) := by
        simpa only [φ,instantiatedEqual,instantiateLift,instantiateTerm,GorbowSubstitution.substitute,Fin.cases_zero,subLift,functionSentence] using q
      have ht := transport φ (Term.numeral (inputValue s)) s ps qi
      simpa only [φ,instantiatedEqual,instantiateLift,instantiateTerm,GorbowSubstitution.substitute,Fin.cases_zero,subLift] using ht

theorem headerCalculation : Comparators.GorbowRegistryRepresentation.HeaderCalculation := by
  intro arity tag args
  have ha : ArithmeticTerm (headerInput arity tag args) := by
    apply GorbowRegistryTupleProof.arithmeticConstructors.2.2 0 arity tag
    intro t ht
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp ht
    exact GorbowStandardInstancesProof.arithmeticNumerals 0 n
  have hv : inputValue (headerInput arity tag args)=GorbowRegistryTuple.header arity tag args := by
    have h := (GorbowRegistryTupleProof.termCalibration 0
      (GorbowSortedRevision.interpretation GorbowAtomicRegistry.ground (fun _ => False)) Fin.elim0).2.2 arity tag (args.map Term.numeral)
    simpa [inputValue,headerInput,List.map_map,Function.comp_def,numeral_realize] using h
  refine ⟨ha,hv,?_⟩
  have hc := GorbowArithmeticDerivationProof.closedEvaluation (headerInput arity tag args) ha
    (GorbowSortedRevision.interpretation GorbowAtomicRegistry.ground (fun _ => False))
  change GorbowArithmeticDerivation.Calculation (headerInput arity tag args) (inputValue (headerInput arity tag args)) at hc
  simpa only [hv] using hc

theorem headerRepresentation : Comparators.GorbowRegistryRepresentation.HeaderRepresentation := by
  intro arity tag args
  have hh := headerCalculation arity tag args
  simpa only [hh.2.1] using arithmeticInputs (headerInput arity tag args) hh.1

theorem certificateExact : Comparators.GorbowRegistryRepresentation.CertificateExact :=
  GorbowTheoryNumericCertificateProof.proofEquivalence axiomProgram

theorem concreteCertificate : Comparators.GorbowRegistryRepresentation.ConcreteCertificate := by
  intro n φ
  rw [certificateExact]
  constructor
  · rintro ⟨ψ,he,hp⟩
    have h := GorbowSortedSyntaxCodeProof.actualInjection.1 n he
    subst ψ
    exact hp
  · intro hp; exact ⟨φ,rfl,hp⟩

theorem rejectContradiction : Comparators.GorbowRegistryRepresentation.RejectContradiction := by
  intro c
  cases h : check 0 (GorbowSortedSyntaxCode.formulaCode falseEquality) c with
  | false => rfl
  | true => exact False.elim (GorbowRegistryDiagramProof.diagramConsistency ((concreteCertificate 0 falseEquality).mp ⟨c,h⟩))

theorem uniformCheck : Comparators.GorbowRegistryRepresentation.UniformCheck :=
  GorbowTheoryNumericCertificateProof.uniformProgram axiomProgram GorbowRegistryDiagramProof.uniformPrograms.2

theorem gorbowRegistryRepresentation : Comparators.GorbowRegistryRepresentation.Target :=
  ⟨arithmeticInputs,headerCalculation,headerRepresentation,certificateExact,concreteCertificate,rejectContradiction,uniformCheck⟩
end LogicLineages.ComputabilityKnowledge.GorbowRegistryRepresentationProof
