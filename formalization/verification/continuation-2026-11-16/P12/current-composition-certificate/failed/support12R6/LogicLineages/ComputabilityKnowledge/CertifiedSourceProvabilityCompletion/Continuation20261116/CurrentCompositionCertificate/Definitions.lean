module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentSourceSeededSpecialization.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralCompositionProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality

/-- The literal original composition node equation, before universal closure. -/
def rootFormula {m n : Nat} (f : Program n) (g : Fin n → Program m) (tag : Nat) : Formula m :=
 .equal (call tag (argumentVariables m))
  (call (tag+1) (List.Vector.ofFn (fun i => call (tag+argumentTag f g i) (argumentVariables m))))
def numeralValues {ctx n : Nat} (ntag : Nat) (v : List.Vector (Term ctx) n) : List.Vector (Term ctx) n :=
 v.map (LiteralNumeralPrefix.numeralCall ntag)
def childValues {ctx m n : Nat} (J : PrescribedRuntimeCallCongruence.Tags)
 (f : Program n) (g : Fin n → Program m) (tag : Nat) (inputs : List.Vector (Term ctx) m) : List.Vector (Term ctx) n :=
 List.Vector.ofFn (fun i => callValue J (Term.numeral (tag+argumentTag f g i)) inputs)
/-- Original explicit recipe: root specialization, call congruence, then two
transitivities in precisely the source order. Child codes are parameters of
this constructor helper, never chosen opaque HasCertificates witnesses. -/
def number {m n : Nat} (f : Program n) (g : Fin n → Program m) (tag : Nat)
 (inputs : List.Vector Nat m) (values : List.Vector Nat n) (result : Nat)
 (codes : List.Vector Nat n) (functionCode : Nat) : Nat :=
 let a := GorbowPRNumeralCalculation.numeralArguments inputs
 let b := List.Vector.ofFn (fun i => call (tag+argumentTag f g i) a)
 let c := GorbowPRNumeralCalculation.numeralArguments values
 let parent := call tag a
 let left := call (tag+1) b
 let right := call (tag+1) c
 let seed := PrescribedRuntimeSpecialization.produce (rootFormula f g tag)
  (fun i => Term.numeral (inputs.get i)) (PrescribedSourceAxiomSpecialization.seed (rootFormula f g tag))
 transitivityNumber parent right (Term.numeral result)
  (transitivityNumber parent left right seed (callNumber (tag+1) b c codes)) functionCode
def certificate {arity k m n ctx : Nat} {p : Program arity} {installed : Formula 1}
 {lhs rhs : Term 1} {t : Term k} {old a : Program 1} {x : Program 3}
 (I : CumulativeUniformRule12Registry.JointInstallation p installed lhs rhs t old a x)
 (f : Program n) (g : Fin n → Program m) (tag : Nat)
 (inputs : List.Vector (Term ctx) m) (values : List.Vector (Term ctx) n) (result : Term ctx)
 (codes : List.Vector (Term ctx) n) (functionCode : Term ctx) : Term ctx :=
 let J := tags I
 let av := numeralValues J.numeralTag inputs
 let bv := childValues J f g tag av
 let cv := numeralValues J.numeralTag values
 let parent := callValue J (Term.numeral tag) av
 let left := callValue J (Term.numeral (tag+1)) bv
 let right := callValue J (Term.numeral (tag+1)) cv
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.current.ctag
  I.previous.current.atag I.previous.current.constructorTag (rootFormula f g tag) av
 transitivityCertificate J.mtag J.ctag J.atag J.constructorTag parent right output
  (transitivityCertificate J.mtag J.ctag J.atag J.constructorTag parent left right seed
   (callCertificate J (Term.numeral (tag+1)) bv cv codes)) functionCode
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate
