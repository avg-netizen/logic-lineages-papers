module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.GraphProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SeedCode
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.RootEncoding
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.CodeBridge
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution PrescribedRuntimeEquality
open SixSol20261112.Fuel NamedArithmeticGraph
open FixedFormulaSubstitution PrescribedRuntimeCallCongruence
theorem code {arity k n ctx : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhsTerm : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhsTerm t old a x)
 (kind : Kind n) (J : CurrentBasicProducerProgram.Tags) (H : Installation p J) (target producerTag : Nat)
 (hp : (nodes p)[producerTag]? = some ⟨n+1,program kind⟩) (inputs : List.Vector (Term ctx) n) :
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call producerTag (Term.numeral target ::ᵥ inputs))
   (PrescribedSourceAxiomSpecialization.certificate K.mtag I.previous.previous.current.ctag
    I.previous.previous.current.atag I.previous.previous.current.constructorTag
    (rootFormula kind target) (inputs.map (LiteralNumeralPrefix.numeralCall K.numeralTag))))) := by
 dsimp only
 let C := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 let K := PrescribedRuntimeCallCongruence.tags I.previous
 let S : CurrentRecursionBaseProgram.Tags :=
  { ptag := J.ptag
    ctag := I.previous.previous.current.ctag
    atag := I.previous.previous.current.atag
    ntag := K.numeralTag
    mtag := K.mtag
    r12 := J.r12
    r13 := I.previous.previous.current.constructorTag
    baseTag := J.baseTag
    childTag := J.childTag }
 have hC : CurrentRecursionProducerCore.CodecBridge.Nodes p C := ⟨H.hc,H.ha,H.hn⟩
 have hK := CurrentRecursionProducerCore.FormulaBridge.originalNodes p installed lhs rhsTerm t old a x I
 have hnums (i : Fin n) := CurrentRecursionProducerCore.CodecBridge.numeral p C K hC hK (inputs.get i)
 obtain ⟨hnums⟩ := CurrentRecursionProducerCore.SpecializationCopy.finiteWitness n (fun i => Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralNumeralPrefix.numeralCall J.ntag (inputs.get i)) (LiteralNumeralPrefix.numeralCall K.numeralTag (inputs.get i)))) hnums
 obtain ⟨hs⟩ := SeedCode.certificate p J S H.hp H.hc H.ha H.hm H.h13 H.hn
  I.previous.previous.current.h_ctag I.previous.previous.current.h_atag
  I.previous.previous.previous.previous.previous.hmp I.previous.previous.current.h_constructor
  kind target inputs (inputs.map (LiteralNumeralPrefix.numeralCall K.numeralTag)) (fun i => by
   simp only [List.Vector.get_map]
   exact hnums i)
 obtain ⟨hg⟩ := GraphProof.exactInternal arity p n kind J producerTag H hp ctx (Term.numeral target) inputs
 exact ⟨Logic.trans _ _ _ hg hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.CodeBridge
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.CodeBridge
