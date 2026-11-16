module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix

/-- Original m input binders and one LAST runtime-tag coordinate. -/
def rootTemplate {m n : Nat} (f : Program n) (g : Fin n → Program m) : Formula (m+1) :=
 let target : Term (m+1) := .var (Fin.last m)
 let xs : List.Vector (Term (m+1)) m := List.Vector.ofFn (fun i => .var i.castSucc)
 .equal (CurrentRecursionBaseProgram.openCall target xs)
  (CurrentRecursionBaseProgram.openCall (.succ target)
   (List.Vector.ofFn (fun i => CurrentRecursionBaseProgram.openCall
    (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) target) xs)))

/-- Encode the original call syntax, not execute the quoted evaluator. -/
def callCode {arity n : Nat} (tag : Program arity) (raw : List.Vector (Program arity) n) : Program arity :=
 FixedFormulaSubstitution.unary 5
  (CurrentCallCongruenceProgram.pairCode
   (constant arity (Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral n : Term 0))))
   (CurrentCallCongruenceProgram.pairCode (applyOne LiteralNumeralPrefix.numeralCode tag)
    (CurrentCallCongruenceProgram.tupleCode raw)))
/-- Actual original numeric arguments, not their encoded syntax. -/
def inputPrograms (m : Nat) : List.Vector (Program (m+1)) m := List.Vector.ofFn (fun i => .projection i.succ)
def rawPrograms (m : Nat) : List.Vector (Program (m+1)) m :=
 (inputPrograms m).map (applyOne LiteralNumeralPrefix.numeralCode)
def argumentValues {m n : Nat} (g : Fin n → Program m) : List.Vector (Program (m+1)) n :=
 List.Vector.ofFn (fun i => .composition (g i) (inputPrograms m).get)
def argumentCalls {m n : Nat} (f : Program n) (g : Fin n → Program m) : List.Vector (Program (m+1)) n :=
 List.Vector.ofFn (fun i => callCode (CurrentRecursionStepProgram.shiftProgram (argumentTag f g i) (.projection 0)) (rawPrograms m))
def argumentCodes {m n : Nat} (f : Program n) (g : Fin n → Program m) (G : Fin n → Program (m+1)) : List.Vector (Program (m+1)) n :=
 List.Vector.ofFn (fun i => .composition (G i)
  (Fin.cases (CurrentRecursionStepProgram.shiftProgram (argumentTag f g i) (.projection 0)) (inputPrograms m).get))

/-- Actual full composition producer, no supplied child certificate inputs.
Child programs are concrete AST parameters, and both evaluator and producer
calls are executed at their literal original argument vectors. -/
def program {m n : Nat} (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) : Program (m+1) :=
 let target : Program (m+1) := .projection 0
 let functionTarget := applyOne .succ target
 let values := argumentValues g
 let result := Program.composition f values.get
 let nums := rawPrograms m
 let leftArgs := argumentCalls f g
 let rightArgs := values.map (applyOne LiteralNumeralPrefix.numeralCode)
 let parent := callCode target nums
 let left := callCode functionTarget leftArgs
 let right := callCode functionTarget rightArgs
 let output := applyOne LiteralNumeralPrefix.numeralCode result
 let seed := CurrentRecursionBaseProgram.seedProgram m (rootTemplate f g) (CurrentRecursionBaseProgram.rootArguments m)
 let congruence := CurrentCallCongruenceProgram.callConstructor functionTarget leftArgs rightArgs (argumentCodes f g G)
 let functionCode := Program.composition F (Fin.cases functionTarget values.get)
 CurrentRecursionBaseProgram.transitivity parent right output
  (CurrentRecursionBaseProgram.transitivity parent left right seed congruence) functionCode

def number {m n : Nat} (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (target : Nat) (inputs : List.Vector Nat m) : Nat :=
 let values := List.Vector.ofFn (fun i => evaluate (g i) inputs)
 let codes := List.Vector.ofFn (fun i => evaluate (G i) ((target+argumentTag f g i) ::ᵥ inputs))
 CurrentCompositionCertificate.number f g target inputs values (evaluate f values) codes
  (evaluate F ((target+1) ::ᵥ values))

structure Tags (n : Nat) where
 C : CurrentCallCongruenceProgram.Tags
 ptag : Nat
 r13 : Nat
 functionTag : Nat
 argumentTags : Fin n → Nat
 functionProducerTag : Nat
 argumentProducerTags : Fin n → Nat
/-- Syntax adapter only. Its final two fields are never used by seedValue,
and no BaseProgram.Installation or dummy base/child membership is asserted. -/
def seedTags {n : Nat} (J : Tags n) : CurrentRecursionBaseProgram.Tags :=
 ⟨J.ptag,J.C.ctag,J.C.atag,J.C.numeralTag,J.C.mtag,J.C.constructorTag,J.r13,
  J.functionTag,J.functionProducerTag⟩
structure Installation {arity m n : Nat} (p : Program arity) (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : Tags n) : Prop where
 primitives : CurrentCallCongruenceProgram.Installation p J.C
 hp : (nodes p)[J.ptag]? = some ⟨2,HistoryCodec.pair⟩
 h13 : (nodes p)[J.r13]? = some ⟨2,UniformClosedRule13.lineConstructor⟩
 hf : (nodes p)[J.functionTag]? = some ⟨n,f⟩
 hg : ∀ i, (nodes p)[J.argumentTags i]? = some ⟨m,g i⟩
 hF : (nodes p)[J.functionProducerTag]? = some ⟨n+1,F⟩
 hG : ∀ i, (nodes p)[J.argumentProducerTags i]? = some ⟨m+1,G i⟩

/-- Actual symbolic child evaluation and producer calls, arbitrary runtime tag.
No quoted child call is silently identified with a differently addressed
actual evaluator. Such coherence belongs to the later fixed-source CORE proof. -/
def value {m n ctx : Nat} (f : Program n) (g : Fin n → Program m) (J : Tags n)
 (target : Term ctx) (inputs : List.Vector (Term ctx) m) : Term ctx :=
 let C := J.C
 let values := List.Vector.ofFn (fun i => call (J.argumentTags i) inputs)
 let result := call J.functionTag values
 let codes := List.Vector.ofFn (fun i => call (J.argumentProducerTags i)
  (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) target ::ᵥ inputs))
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall C.numeralTag)
 let leftArgs := List.Vector.ofFn (fun i => callValue C (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) target) nums)
 let rightArgs := values.map (LiteralNumeralPrefix.numeralCall C.numeralTag)
 let parent := callValue C target nums
 let left := callValue C (.succ target) leftArgs
 let right := callValue C (.succ target) rightArgs
 let output := LiteralNumeralPrefix.numeralCall C.numeralTag result
 let seed := CurrentRecursionBaseProgram.seedValue (seedTags J) m (rootTemplate f g)
  (CurrentRecursionBaseProgram.rawValues (seedTags J) target inputs)
 let congruence := callCertificate C (.succ target) leftArgs rightArgs codes
 let functionCode := call J.functionProducerTag (.succ target ::ᵥ values)
 transitivityCertificate C.mtag C.ctag C.atag C.constructorTag parent right output
  (transitivityCertificate C.mtag C.ctag C.atag C.constructorTag parent left right seed congruence) functionCode

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram
