module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralCallProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open GorbowRegistryTuple GorbowClosedEquality PrescribedRuntimeEquality
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Explicit original producers, not chosen existential HasCertificates witnesses. -/
def reflexivityNumber (t : Term 0) : Nat :=
 GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.reflexive t)]
def binaryTerm {n : Nat} (multiply : Bool) (a b : Term n) : Term n :=
 if multiply then .mul a b else .add a b
/-- Original add/mul recipes: left-coordinate unary, then right-coordinate
unary, then transitivity. Dynamic closed parameters are lifted literally. -/
def binaryNumber (multiply : Bool) (a b c d : Term 0) (hac hbd : Nat) : Nat :=
 transitivityNumber (binaryTerm multiply a b) (binaryTerm multiply c b) (binaryTerm multiply c d)
  (unaryNumber (binaryTerm multiply (.var 0) (liftClosedTerm 1 b)) a c hac)
  (unaryNumber (binaryTerm multiply (liftClosedTerm 1 c) (.var 0)) b d hbd)
def pairNumber (a b c d : Term 0) (hac hbd : Nat) : Nat :=
 let hs := binaryNumber false a b c d hac hbd
 let hm := binaryNumber true (.add a b) (.add a b) (.add c d) (.add c d) hs hs
 binaryNumber false (.mul (.add a b) (.add a b)) a (.mul (.add c d) (.add c d)) c hm hac
def tupleNumber : {n : Nat} → List.Vector (Term 0) n → List.Vector (Term 0) n → List.Vector Nat n → Nat
 | 0, _, _, _ => reflexivityNumber .zero
 | n+1, args, others, codes =>
  unaryNumber (.succ (.var 0))
   (pairTerm args.head (tupleTerm args.tail.toList))
   (pairTerm others.head (tupleTerm others.tail.toList))
   (pairNumber args.head (tupleTerm args.tail.toList) others.head (tupleTerm others.tail.toList)
    codes.head (tupleNumber args.tail others.tail codes.tail))
def callNumber {n : Nat} (tag : Nat) (args others : List.Vector (Term 0) n) (codes : List.Vector Nat n) : Nat :=
 let ht := tupleNumber args others codes
 let hp := pairNumber (Term.numeral tag) (tupleTerm args.toList)
  (Term.numeral tag) (tupleTerm others.toList) (reflexivityNumber (Term.numeral tag)) ht
 let hh := pairNumber (Term.numeral n) (pairTerm (Term.numeral tag) (tupleTerm args.toList))
  (Term.numeral n) (pairTerm (Term.numeral tag) (tupleTerm others.toList)) (reflexivityNumber (Term.numeral n)) hp
 unaryNumber (.universalFunction (.var 0)) (headerTerm n tag args.toList) (headerTerm n tag others.toList) hh
/-- Only addresses already supplied by the unchanged joint installation.
No new AST or registry requirement is introduced. -/
structure Tags where
 mtag : Nat
 ctag : Nat
 atag : Nat
 constructorTag : Nat
 rctag : Nat
 reflexivityTag : Nat
 numeralTag : Nat
def tags {arity k : Nat} {p : Program arity} {f : Formula 1} {lhs rhs : Term 1} {t : Term k}
 {old arithmetic : Program 1} {x : Program 3}
 (I : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old arithmetic x) : Tags :=
 ⟨I.previous.previous.previous.previous.mpTag,I.current.ctag,I.current.atag,I.current.constructorTag,
  I.previous.previous.previous.previous.consTag,I.previous.previous.previous.previous.reflexivityTag,
  I.previous.previous.previous.previous.numeralTag⟩
def zeroValue {ctx : Nat} : Term ctx := rawNumeral .zero
def binaryValue {ctx : Nat} (J : Tags) (multiply : Bool) (a b : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.binaryValue J.ctag J.atag (if multiply then 4 else 3) a b
def pairValue {ctx : Nat} (J : Tags) (a b : Term ctx) : Term ctx :=
 binaryValue J false (binaryValue J true (binaryValue J false a b) (binaryValue J false a b)) a
def tupleValue {ctx : Nat} (J : Tags) : List (Term ctx) → Term ctx
 | [] => zeroValue
 | a::as => FixedFormulaSubstitution.unaryValue J.ctag 2 (pairValue J a (tupleValue J as))
def headerValue {ctx n : Nat} (J : Tags) (tag : Term ctx) (args : List.Vector (Term ctx) n) : Term ctx :=
 pairValue J (rawNumeral (Term.numeral n))
  (pairValue J (LiteralNumeralPrefix.numeralCall J.numeralTag tag) (tupleValue J args.toList))
def callValue {ctx n : Nat} (J : Tags) (tag : Term ctx) (args : List.Vector (Term ctx) n) : Term ctx :=
 FixedFormulaSubstitution.unaryValue J.ctag 5 (headerValue J tag args)
def reflexivityCertificate {ctx : Nat} (J : Tags) (raw : Term ctx) : Term ctx :=
 RawCumulativeLogical.certificate J.rctag J.reflexivityTag raw
def unaryCertificate {ctx : Nat} (J : Tags) (f : Term 1) (t u code : Term ctx) : Term ctx :=
 PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag
  PrescribedRuntimeEquality.boundEnvironment f nil t u code
/-- var0 is protected; var1 is one arbitrary CLOSED runtime coordinate. -/
def binaryEnvironment : FixedFormulaSubstitution.Environment 2 1 1 :=
 Fin.cases (.inl 0) (Fin.cases (.inr 0) Fin.elim0)
def binaryCertificate {ctx : Nat} (J : Tags) (multiply : Bool) (a b c d hac hbd : Term ctx) : Term ctx :=
 let hp := PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag
  binaryEnvironment (binaryTerm multiply (.var 0) (.var 1)) (b ::ᵥ nil) a c hac
 let hq := PrescribedRuntimeEquality.unaryCertificate J.mtag J.ctag J.atag J.constructorTag J.rctag J.reflexivityTag
  binaryEnvironment (binaryTerm multiply (.var 1) (.var 0)) (c ::ᵥ nil) b d hbd
 transitivityCertificate J.mtag J.ctag J.atag J.constructorTag
  (binaryValue J multiply a b) (binaryValue J multiply c b) (binaryValue J multiply c d) hp hq
/-- Literal original add/mul/add pair recipe; hs is supplied TWICE to mul. -/
def pairCertificate {ctx : Nat} (J : Tags) (a b c d hac hbd : Term ctx) : Term ctx :=
 let hs := binaryCertificate J false a b c d hac hbd
 let hm := binaryCertificate J true (binaryValue J false a b) (binaryValue J false a b)
  (binaryValue J false c d) (binaryValue J false c d) hs hs
 binaryCertificate J false (binaryValue J true (binaryValue J false a b) (binaryValue J false a b)) a
  (binaryValue J true (binaryValue J false c d) (binaryValue J false c d)) c hm hac
def tupleCertificate {ctx : Nat} (J : Tags) :
 {n : Nat} → List.Vector (Term ctx) n → List.Vector (Term ctx) n → List.Vector (Term ctx) n → Term ctx
 | 0, _, _, _ => reflexivityCertificate J zeroValue
 | n+1, args, others, codes =>
  unaryCertificate J (.succ (.var 0))
   (pairValue J args.head (tupleValue J args.tail.toList))
   (pairValue J others.head (tupleValue J others.tail.toList))
   (pairCertificate J args.head (tupleValue J args.tail.toList) others.head (tupleValue J others.tail.toList)
    codes.head (tupleCertificate J args.tail others.tail codes.tail))
def callCertificate {ctx n : Nat} (J : Tags) (tag : Term ctx)
 (args others codes : List.Vector (Term ctx) n) : Term ctx :=
 let ht := tupleCertificate J args others codes
 let tagRaw := LiteralNumeralPrefix.numeralCall J.numeralTag tag
 let arityRaw : Term ctx := rawNumeral (Term.numeral n)
 let hp := pairCertificate J tagRaw (tupleValue J args.toList)
  tagRaw (tupleValue J others.toList) (reflexivityCertificate J tagRaw) ht
 let hh := pairCertificate J arityRaw (pairValue J tagRaw (tupleValue J args.toList))
  arityRaw (pairValue J tagRaw (tupleValue J others.toList)) (reflexivityCertificate J arityRaw) hp
 unaryCertificate J (.universalFunction (.var 0)) (headerValue J tag args) (headerValue J tag others) hh
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeCallCongruence
